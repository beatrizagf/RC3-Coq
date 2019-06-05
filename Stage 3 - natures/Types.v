Require Export Syntax.
Require Import Coq.Sets.Ensembles.

Inductive envDom :=
  | env_var : var -> envDom
  | env_loc : loc -> envDom.

Instance ID_envDom : ID envDom := {}.
  intros; repeat (decide equality).
Qed.

Definition env := partial_map envDom ty.

Inductive wfType (P : program) : ty -> Prop :=
  | WF_TClass :
      forall c,
        classLookup P c <> None ->
        wfType P (TClass c)
  | WF_TInterface :
      forall i,
        interfaceLookup P i <> None ->
        wfType P (TInterface i)
  | WF_TUnit : wfType P TUnit.

Inductive wfEnv (P : program) : env -> Prop :=
  | WF_Env :
      (forall Gamma,
        (forall x t, Gamma x = Some t -> wfType P t) ->
        (forall l t, Gamma (env_loc l) = Some t -> exists c, t = TClass c) ->
        wfEnv P Gamma).

Inductive wfFrame (Gamma Gamma1 Gamma2 : env) : Prop :=
  | WF_Frame :
      (forall x t, Gamma1 x = Some t -> Gamma x = Some t) ->
      (forall x t, Gamma2 x = Some t -> Gamma x = Some t) ->
      (forall x t, Gamma1 (env_var x) = Some t -> Gamma2 (env_var x) = None) ->
      (forall x t, Gamma2 (env_var x) = Some t -> Gamma1 (env_var x) = None) ->
      wfFrame Gamma Gamma1 Gamma2.

Inductive wfSubsumption (Gamma Gamma' : env) : Prop :=
  | WF_Subsumption :
      (forall x t, Gamma x = Some t -> Gamma' x = Some t) ->
      wfSubsumption Gamma Gamma'.

Inductive subtypeOf (P : program) : ty -> ty -> Prop :=
  | Sub_Class :
      forall c i fs ms,
        classLookup P c = Some (Cls c i fs ms) ->
        subtypeOf P (TClass c) (TInterface i)
  | Sub_InterfaceLeft :
      forall i i1 i2,
        interfaceLookup P i = Some (ExtInterface i i1 i2) ->
        subtypeOf P (TInterface i) (TInterface i1)
  | Sub_InterfaceRight :
      forall i i1 i2,
        interfaceLookup P i = Some (ExtInterface i i1 i2) ->
        subtypeOf P (TInterface i) (TInterface i2)
  | Sub_Refl :
      forall t,
        wfType P t ->
        subtypeOf P t t
  | Sub_Trans :
      forall t1 t2 t3,
        subtypeOf P t1 t2 ->
        subtypeOf P t2 t3 ->
        subtypeOf P t1 t3.
  (* | Sub_Unit : *)
  (*     forall t, *)
  (*       wfType P t -> *)
  (*       subtypeOf P t TUnit. *)

Tactic Notation "subtypeOf_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "Sub_Class"  | Case_aux c "Sub_InterfaceLeft"
  | Case_aux c "Sub_InterfaceRight" | Case_aux c "Sub_Refl"
  | Case_aux c "Sub_Trans" (*| Case_aux c "Sub_Unit"*)].

Reserved Notation " P ';' Gamma '|-' expr '\in' ty # nature '|>' NCS" (at level 40).
Inductive hasType (P : program) (Gamma : env) : expr -> ty -> nature -> (NatureConstraint -> Prop) -> Prop := (*!!*)
  | T_Var :
      forall x t,
        wfEnv P Gamma ->
        Gamma (env_var x) = Some t ->
        P ; Gamma |- (EVar x) \in t # (NVar x) |> (Empty_set NatureConstraint) (*!!*)
  | T_Loc :
      forall l t c,
        wfEnv P Gamma ->
        Gamma (env_loc l) = Some (TClass c) -> 
        subtypeOf P (TClass c) t ->
        P ; Gamma |- (EVal (VLoc l)) \in t # NatureOf(TClass c) |> (Empty_set NatureConstraint)   (*!!*)
  | T_Null :
      forall t,
        wfEnv P Gamma ->
        wfType P t ->
        P ; Gamma |- EVal VNull \in t # Undefined |> (Empty_set NatureConstraint)  (*!!*)
  | T_New :
      forall c,
        wfEnv P Gamma ->
        classLookup P c <> None ->
        let n := ConditionalNature (NatureOf (TClass c)) NAtomic NAtomic Undefined in (*!!*)
        P ; Gamma |- ENew c \in TClass c # n |> (Empty_set NatureConstraint)  (*!!*)
  | T_Call :
      forall x m e t t1 t2 n msigs y ncs,
        Gamma (env_var x) = Some t1 -> 
        methodSigs P t1 msigs ->
        methodSigLookup msigs m = Some (MethodSig m (y, t2) t) ->
        P ; Gamma |- e \in t2 # n |> ncs ->   (*!!*)
        let n1 := NatureOf(addAtomic (discardAtomic t1)) in
        let n3 := NatureOf(addAtomic (discardAtomic t)) in (*!!*)
        let n' := ConditionalNature (NVar x) NAtomic n1 (NatureOf(discardAtomic t1)) in (*!!*)
        let n'' := ConditionalNature (NVar x) NAtomic n3 (NatureOf(discardAtomic t)) in  (*!!*)
        P ; Gamma |- ECall x m e \in t # n'' |> Union NatureConstraint ncs (Singleton NatureConstraint (NN n' n'')) (*!!*)
  | T_Select :
      forall x f c t fs nclass,
        P ; Gamma |- (EVar x) \in TClass c # nclass |> (Empty_set NatureConstraint) ->(*!!*)
        fields P (TClass c) = Some fs -> 
        fieldLookup fs f = Some (Field f t) ->
        let n1 := NatureOf(addAtomic (discardAtomic (FieldsType (Field f t)))) in 
          let n2 := NatureOf(discardAtomic (FieldsType (Field f t))) in
            let n := ConditionalNature (NVar x) NAtomic n1 n2 in 
              P ; Gamma |- ESelect x f \in t# n |> (Empty_set NatureConstraint) (*!!*)
  | T_Update :
      forall c x f e t fs n ncs nclass,
        P ; Gamma |- (EVar x) \in TClass c # nclass |> (Empty_set NatureConstraint) -> 
        fields P (TClass c) = Some fs -> 
        fieldLookup fs f = Some (Field f t) ->
        P ; Gamma |- e \in t # n |> ncs ->
        let n1 := NatureOf(addAtomic (discardAtomic (FieldsType (Field f t)))) in (*!atomic!*)
        let n2 := NatureOf(discardAtomic (FieldsType (Field f t))) in(*!non-atomic!*)
        let n' := ConditionalNature (NVar x) NAtomic n1 n2 in (*!!*)
        P ; Gamma |- EUpdate x f e \in TUnit # Undefined |> Union NatureConstraint ncs (Singleton NatureConstraint (NN n' n))
  | T_Let :
      forall x e body t t' n n' ncs ncs',
        P ; Gamma |- e \in t # n |> ncs -> (*!!*)
        P ; extend Gamma (env_var (SV x)) t |- body \in t'# n' |> ncs' -> (*!!*)
         let n1 := subst_nat n' (SV x) n in (*!!*)
         let ncs1 := subst_ncs ncs' (SV x) n in (*!!*)
        no_locks body ->
        P ; Gamma |- ELet x e body \in t'# n1 |> Union NatureConstraint ncs ncs1 (*!!*)
  | T_Cast :
      forall e t1 t2 n ncs,
        P ; Gamma |- e \in t2 # n |> ncs -> (*!!*)
        subtypeOf P t2 t1 ->
        P ; Gamma |- ECast t1 e \in t1 # n |> ncs (*!!*)
  | T_Par :
      forall Gamma1 Gamma2 e1 e2 e3 t1 t2 t3 n1 n2 n3 ncs1 ncs2 ncs3,
        wfFrame Gamma Gamma1 Gamma2 ->
        P ; Gamma1 |- e1 \in t1 # n1 |> ncs1 -> (*!!*)
        P ; Gamma2 |- e2 \in t2 # n2 |> ncs2 -> (*!!*)
        P ; Gamma |- e3 \in t3 # n3 |> ncs3 -> (*!!*)
        no_locks e1 ->
        no_locks e2 ->
        no_locks e3 ->
        P ; Gamma |- EPar e1 e2 e3 \in t3 # n3 |> Union NatureConstraint (Union NatureConstraint ncs1 ncs2) ncs3 (*!!*)
  | T_Lock :
      forall x e t t2 n ncs n2 ncs2,
        P ; Gamma |- (EVar x) \in t2 # n2 |> ncs2 -> 
        P ; Gamma |- e \in t # n |> ncs ->
        no_locks e -> 
        P ; Gamma |- ELock x e \in t # n |> ncs  (*!!*)
  | T_Locked :
      forall l t2 e t n n2 ncs,
        P ; Gamma |- (EVal (VLoc l)) \in t2 # n2 |> (Empty_set NatureConstraint) ->
        P ; Gamma |- e \in t # n |> ncs ->  (*!!*)
        P ; Gamma |- ELocked l e \in t # n |> ncs (*!!*)
  where " P ';' Gamma '|-' expr '\in' ty # nature '|>' NCS" := (hasType P Gamma expr ty nature NCS). (*!!*)

Tactic Notation "hasType_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "T_Var"
  | Case_aux c "T_Loc"
  | Case_aux c "T_Null"
  | Case_aux c "T_New"
  | Case_aux c "T_Call"
  | Case_aux c "T_Select"
  | Case_aux c "T_Update"
  | Case_aux c "T_Let"
  | Case_aux c "T_Cast"
  | Case_aux c "T_Par"
  | Case_aux c "T_Lock"
  | Case_aux c "T_Locked"
  ].