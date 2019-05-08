Require Export Syntax.
Require Import Types.

Require Import Coq.Sets.Ensembles. (*!!*)
Require Import List.

(*
--------
Program
--------
*)

Inductive wfMethodSig (P : program) : methodSig -> Prop :=
  WF_Msig :
    forall m x t t',
      wfType P t ->
      wfType P t' ->
      wfMethodSig P (MethodSig m (x, t) t').

Inductive wfInterface (P : program) : interfaceDecl -> Prop :=
  | WF_Interface :
      forall i msigs,
        Forall (wfMethodSig P) msigs ->
        wfInterface P (Interface i msigs)
  | WF_ExtInterface :
      forall i i1 i2 msigs1 msigs2,
        methodSigs P (TInterface i1) msigs1 ->
        methodSigs P (TInterface i2) msigs2 ->
        (forall m msig, methodSigLookup msigs1 m = Some msig -> methodSigLookup msigs2 m = None) ->
        (forall m msig, methodSigLookup msigs2 m = Some msig -> methodSigLookup msigs1 m = None) ->
        wfInterface P (ExtInterface i i1 i2).

Inductive wfFieldDecl (P : program) : fieldDecl -> Prop :=
  | WF_Field :
      forall f t,
        wfType P t ->
        wfFieldDecl P (Field f t).

Inductive wfMethodDecl (P : program) (c : class_id) : (MethodConstraints -> Prop) -> methodDecl -> Prop := (*!!*)
  | WF_Method :
      forall m x t t' e n' ncs' Nreturn ncs, (*!!*)
      wfType P t ->
      (* This should be derivable, but this makes things simpler *)
      wfType P t' ->
      x <> this ->
      (* This should also be derivable *)
      remove id_eq_dec x
             (remove id_eq_dec this (freeVars e)) = nil ->
      exprStatic e ->
        (let Gamma := extend
                        (extend empty
                                (env_var (SV x)) t)
                        (env_var (SV this)) (TClass c) in
         P ; Gamma |- e \in t' # n' |> ncs') -> (*!!*)
        match NatureOf(t') with  (*!!*)
        | NAtomic => let ncs := Singleton NatureConstraint (NN n' NAtomic) in NatureConstraint
        | _ => let ncs := Empty_set NatureConstraint in NatureConstraint
        end ->
        wfMethodDecl P c 
          (Singleton MethodConstraints (m, 
             Union NatureConstraint (Union NatureConstraint ncs' ncs) 
              (Ensembles.Add NatureConstraint (Singleton NatureConstraint (NN (NVar (SV this)) (NatureOf (TClass c)))) (NN (NVar Nreturn) n') )
                                       )
          )
                (Method m (x, t) t' e). (*!!*)

Inductive wfClassDecl (P : program) : (MethodConstraints -> Prop) -> classDecl -> Prop := (*!!*)
  | WF_Class :
      forall c i fs ms msigs mcs_c mcs_m,
        methodSigs P (TInterface i) msigs ->
        extractSigs ms = msigs ->
        Forall (wfFieldDecl P) fs ->
        Forall (wfMethodDecl P c mcs_m) ms -> (*!!*)
        wfClassDecl P mcs_c (Cls c i fs ms).  (*!!*)

Inductive wfProgram : program -> ty -> (MethodConstraints -> Prop) -> Prop := (*!!*)
  | WF_Program :
      forall cds ids e t n ncs mcs, 
      forall m_id : method_id,
        Forall (wfClassDecl (cds, ids, e) mcs) cds -> (*!!*)
        Forall (wfInterface (cds, ids, e)) ids ->
        (cds, ids, e); empty |- e \in t # n |> ncs ->
        wfProgram (cds, ids, e) t (Union MethodConstraints mcs (Singleton MethodConstraints (m_id, ncs))). (*!!*)

(*
-------
Heap
-------
*)

Inductive wfFields (P : program) (Gamma : env) (c : class_id) (F : dyn_fields) : Prop :=
  WF_Fields :
    forall fs,
      fields P (TClass c) = Some fs ->
      (forall f t, fieldLookup fs f = Some (Field f t) ->  (*!!*)
                   exists v n ncs, F f = Some v /\ P; Gamma |- EVal v \in t # n |> ncs) ->  (*!!*)
      wfFields P Gamma c F.

Inductive wfHeap (P : program) (Gamma : env) : heap -> Prop :=
  WF_Heap :
    forall H,
      wfEnv P Gamma ->
      (forall l c, Gamma (env_loc l) = Some (TClass c) ->
                   exists F L, heapLookup H l = Some (c, F, L) /\
                               wfFields P Gamma c F) ->
      (forall l, heapLookup H l <> None -> exists c, Gamma (env_loc l) = Some (TClass c)) ->
      wfHeap P Gamma H.

(*
------
Vars
------
*)

Definition freshVars (n : nat) (V : dvar_map) :=
  (forall n', n <= n' -> fresh V (DVar n')).

Inductive wfVars (P : program) (Gamma : env) (n : nat) (V : dvar_map) : Prop := (*!!*)
  WF_Vars :
      wfEnv P Gamma ->
      (forall x t, Gamma (env_var (DV x)) = Some t -> exists v n' ncs', V x = Some v /\ P; Gamma |- (EVal v) \in t # n' |> ncs') -> (*!!*)
      (forall x, V x <> None -> Gamma (env_var (DV x)) <> None) ->
      freshVars n V ->
      wfVars P Gamma n V.

(*
------
Locks
------
*)

Inductive wfLock (H : heap) : lock -> Prop :=
  | WF_Lock :
      forall l c F,
        heapLookup H l = Some (c, F, LLocked) ->
        wfLock H l.

Inductive wfHeldLocks (H : heap) (Ls : list lock) : Prop :=
  | WF_HeldLocks :
      Forall (wfLock H) Ls ->
      wfHeldLocks H Ls.

Inductive wfLocks (Ls : list lock) (e : expr) : Prop :=
  | WF_Locks :
      (forall l, In l (locks e) -> In l Ls) ->
      NoDup (locks e) ->
      wfLocks Ls e.

Inductive disjointLocks (T1 T2 : threads) : Prop :=
  | DisjointLocks :
      (forall L, In L (heldLocks T1) -> ~ In L (heldLocks T2)) ->
      (forall L, In L (heldLocks T2) -> ~ In L (heldLocks T1)) ->
      disjointLocks T1 T2.

Inductive wfLocking (H : heap) : threads -> Prop :=
  | WF_Locking_Thread :
      forall Ls e,
        wfHeldLocks H Ls ->
        NoDup Ls ->
        wfLocks Ls e ->
        wfLocking H (T_Thread Ls e)
  | WF_Locking_Async :
      forall T1 T2 e,
        wfLocks (leftmost_locks T1) e ->
        (forall L, In L (locks e) -> ~In L (t_locks T1)) ->
        disjointLocks T1 T2 ->
        wfLocking H T1 ->
        wfLocking H T2 ->
        wfLocking H (T_Async T1 T2 e)
  | WF_Locking_EXN :
      forall Ls,
        wfHeldLocks H Ls ->
        wfLocking H (T_EXN Ls).

(*
--------
Threads
--------
*)

Inductive wfThreads (P : program) (Gamma : env) : threads -> ty -> nature -> (NatureConstraint -> Prop) -> Prop := (*!!*)
  | WF_Thread :
      forall Ls e t n ncs,  (*!!*)
        freeVars e = nil ->
        P; Gamma |- e \in t # n |> ncs -> (*!!*)
        wfThreads P Gamma (T_Thread Ls e) t n ncs (*!!*)
  | WF_Async :
      forall T1 T2 e t t1 t2 n n1 n2 ncs ncs1 ncs2, (*!!*)
        freeVars e = nil ->
        P; Gamma |- e \in t # n |> ncs -> (*!!*)
        wfThreads P Gamma T1 t1 n1 ncs1 ->  (*!!*)
        wfThreads P Gamma T2 t2 n2 ncs2 -> 
        wfThreads P Gamma (T_Async T1 T2 e) t n (Union NatureConstraint (Union NatureConstraint ncs1 ncs2) ncs) (*!!*)
  | WF_EXN :
      forall t Ls,
        wfType P t ->
        wfEnv P Gamma ->
        wfThreads P Gamma (T_EXN Ls) t Undefined (Empty_set NatureConstraint).  (*!!*)

(*
--------------
Configuration
--------------
*)

Inductive wfConfiguration (P : program) (Gamma : env) : configuration -> ty -> nature -> (NatureConstraint -> Prop) -> Prop :=
  | WF_Cfg :
      forall H V n T t n' ncs', (*!!*)
        0 < n ->
        wfHeap P Gamma H ->
        wfVars P Gamma n V ->
        wfThreads P Gamma T t n' ncs' ->  (*!!*)
        wfLocking H T ->
        wfConfiguration P Gamma (H, V, n, T) t n' ncs'. (*!!*)
