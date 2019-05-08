Require Export Types.
Require Import SyntaxProp.
Require Import WellFormedness.

Require Import Coq.Sets.Ensembles.

Ltac simpl_extend_hyp :=
  match goal with
    | H : context[extend _ ?X _ ?X] |- _ =>
      rewrite extend_eq in H

    | H : context[extend _ (env_var (SV ?X)) _ (env_var (SV ?Y))], _ : ?X <> ?Y |- _ =>
      rewrite extend_neq in H
    | H : context[extend _ (env_var (SV _)) _ (env_var (DV _))] |- _ =>
      rewrite extend_neq in H
    | H : context[extend _ (env_var (SV _)) _ (env_loc _)] |- _ =>
      rewrite extend_neq in H

    | H : context[extend _ (env_var (DV ?X)) _ (env_var (DV ?Y))], _ : ?X <> ?Y |- _ =>
      rewrite extend_neq in H
    | H : context[extend _ (env_var (DV _)) _ (env_var (SV _))] |- _ =>
      rewrite extend_neq in H
    | H : context[extend _ (env_var (DV _)) _ (env_loc _)] |- _ =>
      rewrite extend_neq in H

    | H : context[extend _ (env_loc ?X) _ (env_loc ?Y)], _ : ?X <> ?Y |- _ =>
      rewrite extend_neq in H
    | H : context[extend _ (env_loc _) _ (env_var _)] |- _ =>
      rewrite extend_neq in H

    | _ : _ |- _ => fail "No matching hypothesis found"
  end; try congruence.

Hint Extern 1 => simpl_extend_hyp : env.
Hint Extern 1 => case_extend : env.

Ltac trivial_neq :=
  match goal with
    | [_ : _|- env_loc _ <> env_var _] => congruence
    | [H : ?l1 <> ?l2 |- env_loc ?l1 <> env_loc ?l2] => congruence
    | [H : ?l2 <> ?l1 |- env_loc ?l1 <> env_loc ?l2] => congruence
    | [_ : _|- env_var _ <> env_loc _] => congruence
    | [_ : _|- env_var (SV _) <> env_var (DV _)] => congruence
    | [H : ?x <> ?y |- env_var (SV ?x) <> env_var (SV ?y)] => congruence
    | [H : ?y <> ?x |- env_var (SV ?x) <> env_var (SV ?y)] => congruence
    | [_ : _|- env_var (DV _) <> env_var (SV _)] => congruence
    | [H : ?x <> ?y |- env_var (DV ?x) <> env_var (DV ?y)] => congruence
    | [H : ?y <> ?x |- env_var (DV ?x) <> env_var (DV ?y)] => congruence
    | _ => fail 1 "Not a trivial inequality of environment domain variables"
  end.

Hint Extern 1 => trivial_neq : env.

Lemma fields_wfFieldDecl :
  forall P t' t fs mcs, (*!!*)
    wfProgram P t' mcs -> (*!!*)
    fields P t = Some fs ->
    Forall (wfFieldDecl P) fs.
Proof with auto.
  introv wfP Hfields.
  inv wfP.
  destruct t; try(solve[inv Hfields]).
  + unfold fields in Hfields.
    remember (classLookup (cds, ids, e) c) as cLookup.
    symmetry in HeqcLookup.
    destruct cLookup as [[c' i fs' ms] |]...
    inv_eq.
    solve by lookup_forall.
Qed.

Corollary fieldLookup_wfType :
  forall P t' t'' fs f t mcs, (*!!*)
    wfProgram P t' mcs -> (*!!*)
    fields P t'' = Some fs ->
    fieldLookup fs f = Some (Field f t) ->
    wfType P t.
Proof with eauto.
  introv wfP Hfields fLookup.
  eapply fields_wfFieldDecl in Hfields...
  solve by lookup_forall...
Qed.


Lemma extractSigs_wfMethodSigs :
  forall P c mtds mcs,  (*!!*)
    Forall (wfMethodDecl P c mcs) mtds -> (*!!*)
    Forall (wfMethodSig P) (extractSigs mtds).
Proof with eauto.
  introv wfMtds.
  induction mtds as [|[m [x t] t' e]]; simpl...
  inv wfMtds as [|? ? wfMtd wfMtds']. constructor...
  inv wfMtd. constructor; crush.
Qed.

Lemma methodSigs_wfMethodSig :
  forall P t' t msigs mcs,  (*!!*)
    wfProgram P t' mcs -> (*!!*)
    methodSigs P t msigs ->
    Forall (wfMethodSig P) msigs.
Proof with eauto using extractSigs_wfMethodSigs, Forall_app.
  introv [? ? ? ? wfCds wfIds wfExpr] Hsigs.
  induction Hsigs; try(lookup_forall as wfD; inv wfD)...
Qed.

Corollary methodSigLookup_wfType :
  forall P t' t msigs m x t1 t2 mcs,  (*!!*)
    wfProgram P t' mcs -> (*!!*)
    methodSigs P t msigs ->
    methodSigLookup msigs m = Some (MethodSig m (x, t1) t2) ->
    wfType P t2.
Proof with eauto using methodSigs_wfMethodSig.
  introv wfP Hsigs Hsig.
  eapply methodSigs_wfMethodSig in Hsigs...
  lookup_forall as wfMsig.
  inv wfMsig...
Qed.

(*
========================
Well-formed environment
========================
*)

Hint Constructors wfProgram.
Hint Constructors wfEnv.
Hint Constructors wfType.


Lemma wfEnv_empty :
  forall P,
    wfEnv P empty.
Proof with auto.
  constructor; introv H; inv H.
Qed.


Lemma wfEnv_equiv :
  forall P Gamma Gamma',
    (forall x, Gamma x = Gamma' x) ->
    wfEnv P Gamma ->
    wfEnv P Gamma'.
Proof with eauto.
  introv Hequiv wfGamma.
  constructor; introv;
  rewrite <- Hequiv; inv wfGamma...
Qed.

Hint Immediate wfEnv_equiv : env.

Lemma wfEnv_extend_var :
  forall P Gamma x t,
    wfEnv P Gamma ->
    wfType P t ->
    wfEnv P (extend Gamma (env_var x) t).
Proof with eauto.
  constructor; intros x' t'; case_extend; inv H...
Qed.

Hint Resolve wfEnv_extend_var : env.

Lemma wfEnv_extend_loc :
  forall P Gamma l t,
    wfEnv P Gamma ->
    wfType P t ->
    (exists c, t = TClass c) ->
    wfEnv P (extend Gamma (env_loc l) t).
Proof with eauto.
  constructor; intros x' t'; case_extend; inv H; crush...
Qed.

Hint Resolve wfEnv_extend_loc : env.

Lemma wfEnv_drop :
  forall P Gamma x,
    wfEnv P Gamma ->
    wfEnv P (drop Gamma x).
Proof with eauto with env.
  introv wfGamma.
  inv wfGamma.
  econstructor.
  + introv Henv.
    unfold drop in Henv.
    cases_if...
  + introv Henv.
    unfold drop in Henv.
    cases_if...
Qed.

Hint Resolve wfEnv_drop : env.

Lemma wfEnv_subst :
  forall P Gamma x y t,
    wfEnv P Gamma ->
    wfEnv P (extend Gamma (env_var x) t) ->
    wfEnv P (extend Gamma (env_var y) t).
Proof with eauto with env.
  introv wfGamma wfGamma'.
  inv wfGamma'...
Qed.

Hint Resolve wfEnv_subst : env.

(*
============
Subsumption
============
*)

Hint Constructors wfSubsumption.

Lemma wfSubsumption_refl :
  forall Gamma,
    wfSubsumption Gamma Gamma.
Proof with eauto.
  auto.
Qed.

Hint Immediate wfSubsumption_refl.

Lemma wfSubsumption_equiv :
  forall Gamma Gamma',
    (forall x, Gamma x = Gamma' x) ->
    wfSubsumption Gamma Gamma'.
Proof with eauto.
  constructors;
  crush.
Qed.

Hint Immediate wfSubsumption_equiv.

Lemma wfSubsumption_trans :
  forall Gamma1 Gamma2 Gamma3,
    wfSubsumption Gamma1 Gamma2 ->
    wfSubsumption Gamma2 Gamma3 ->
    wfSubsumption Gamma1 Gamma3.
Proof with eauto.
  constructors; crush.
  inv H. inv H0. crush.
Qed.

Lemma wfSubsumption_extend :
  forall Gamma Gamma' x t,
    wfSubsumption Gamma Gamma' ->
    wfSubsumption (extend Gamma x t) (extend Gamma' x t).
Proof with eauto with env.
  introv wfSub.
  inv wfSub...
Qed.

Lemma wfSubsumption_fresh :
  forall Gamma Gamma' x t,
    wfSubsumption Gamma Gamma' ->
    fresh Gamma x ->
    wfSubsumption Gamma (extend Gamma' x t).
Proof with eauto with env.
  introv wfSub Hfresh.
  inv wfSub...
Qed.

Hint Immediate wfSubsumption_fresh.

Lemma wfSubsumption_empty :
  forall Gamma,
    wfSubsumption empty Gamma.
Proof with eauto with env.
  constructor...
  introv contra.
  inv contra.
Qed.

Hint Immediate wfSubsumption_empty.

Lemma wfSubsumption_frame :
  forall Gamma Gamma1 Gamma2,
    wfFrame Gamma Gamma1 Gamma2 ->
    wfSubsumption Gamma1 Gamma /\
    wfSubsumption Gamma2 Gamma.
Proof with eauto with env.
  introv frameRule.
  inv frameRule...
Qed.

(*
==========
Subtyping
==========
*)

Lemma subtypeOf_class :
  forall P t c,
    subtypeOf P t (TClass c) ->
    t = TClass c.
Proof with eauto.
  intros. remember (TClass c) as t2.
  gen c.
  induction H; intros; try(inv Heqt2)...
  apply IHsubtypeOf2 in Heqt2 as Heq... subst. eapply IHsubtypeOf1...
Qed.

Hint Immediate subtypeOf_class.

Lemma subtypeOf_wfType :
  forall P t' t1 t2 mcs,  (*!!*)
    wfProgram P t' mcs -> (*!!*)
    subtypeOf P t1 t2 ->
    wfType P t1 /\ wfType P t2.
Proof with eauto.
  introv [? ? ? ? wfCs wfIs ?] Hsub.
  subtypeOf_cases(induction Hsub) Case;
    split;
    try(constructor; lookup_forall as wfD; inv wfD); crush;
    match goal with
      | [H: methodSigs _ _ _ |- _] =>
        solve[inv H; crush]
      | [H1: methodSigs _ _ _, H2: methodSigs _ _ _ |- _] =>
        solve[inv H1; crush
             |inv H2; crush]
    end.
Qed.

Corollary subtypeOf_wfTypeSub :
  forall P t' t1 t2 mcs,  (*!!*)
    wfProgram P t' mcs -> (*!!*)
    subtypeOf P t1 t2 ->
    wfType P t1.
Proof with eauto.
  introv wfP Hsub...
  eapply subtypeOf_wfType in Hsub; crush...
Qed.

Hint Immediate subtypeOf_wfTypeSub.

Corollary subtypeOf_wfTypeSup :
  forall P t' t1 t2 mcs,  (*!!*)
    wfProgram P t' mcs -> (*!!*)
    subtypeOf P t1 t2 ->
    wfType P t2.
Proof with eauto.
  introv wfP Hsub...
  eapply subtypeOf_wfType in Hsub; crush...
Qed.

Hint Immediate subtypeOf_wfTypeSup.

(*
========
hasType
========
*)

Hint Constructors hasType.

Lemma hasType_wfType :
  forall P Gamma e t' t n ncs mcs,  (*!!*)
    wfProgram P t' mcs -> (*!!*)
    P; Gamma |- e \in t # n |> ncs ->
    wfType P t.
Proof with eauto using subtypeOf_wfTypeSup, methodSigLookup_wfType, fieldLookup_wfType.
  intros P Gamma e. gen Gamma.
  expr_cases (induction e) Case;
    introv wfP hasType; inv hasType;
    match goal with
      | [H: wfEnv _ ?Gamma |- _] =>
        inv H
      | _ => idtac
    end...
Qed.

Hint Resolve hasType_wfType : env.

Lemma hasType_subsumption :
  forall e P t' Gamma Gamma' t mcs n ncs, (*!!*)
    wfProgram P t' mcs -> (*!!*)
    wfSubsumption Gamma Gamma' ->
    wfEnv P Gamma' ->
    P; Gamma |- e \in t # n |> ncs -> (*!!*)
    P; Gamma' |- e \in t # n |> ncs.  (*!!*)
Proof with eauto using wfSubsumption_extend.
  expr_cases (induction e) Case;
    introv [? ? ? ? ? ? ? ? wfCds wfIds wfExpr] [Hsub] wfGamma hasType; inv hasType; (*!!*)   
  try(
      solve[
          repeat
          match goal with
            | [H: hasType _ _ (EVar ?v) _ _ _|- _] => inv H (*!!*)
            | [H: hasType _ _ (EVal ?v) _ _ _|- _] => inv H (*!!*)
          end;
          constructors; eauto  (*!!*)
        ]
    )...  (*!!*)
  + Case "ECall". 
    constructors...
    simple eapply IHe. apply WF_Program with (n := n0)...
    simple apply WF_Subsumption...
    exact wfGamma. exact H8.
  + Case "EUpdate".
    constructors...
      repeat
      match goal with
        | [H: hasType _ _ (EVar ?v) _ _ _|- _] => inv H (*!!*)
        | [H: hasType _ _ (EVal ?v) _ _ _|- _] => inv H (*!!*)
      end;
      constructors; eauto.
    simple eapply IHe. apply WF_Program with (n := n0)...
    simple apply WF_Subsumption...
    exact wfGamma. exact H8.
  + Case "ELet".
    constructors...
    simple eapply IHe1. apply WF_Program with (n := n0)...
    simple apply WF_Subsumption...
    exact wfGamma. exact H2.
    eapply IHe2 with
    (Gamma := extend Gamma (env_var _) t1)...
    apply WF_Program with (n := n0)...
    simple apply wfEnv_extend_var. exact wfGamma.
    simple eapply hasType_wfType...
    apply WF_Program with (n := n0)...
  + Case "ECast".
    constructors...
    simple eapply IHe. apply WF_Program with (n := n0)...
    simple apply WF_Subsumption...
    exact wfGamma. exact H1.
  + Case "EPar".
    constructors...
    inv H2.
    constructors...
    simple eapply IHe3. apply WF_Program with (n := n0)...
    simple apply WF_Subsumption...
    exact wfGamma. exact H5.
  + Case "ELock".
    match goal with
       | [H: hasType _ _ (EVar ?v) _ _ _ |- _] => inv H
       | [H: hasType _ _ (EVal ?v) _ _ _ |- _] => inv H
    end;
    constructors; eauto. simple eapply IHe.
  apply WF_Program with (n := n0)...
  simple apply WF_Subsumption...
  exact wfGamma.
  exact H2.
  + Case "ELocked".
      repeat
      match goal with
        | [H: hasType _ _ (EVar ?v) _ _ _|- _] => inv H (*!!*)
        | [H: hasType _ _ (EVal ?v) _ _ _|- _] => inv H (*!!*)
      end;
      constructors; eauto.
    simple eapply IHe. eapply WF_Program... 
    simple apply WF_Subsumption...
    exact wfGamma. exact H5. 

  Unshelve. 
    all:eauto.
Qed.

Hint Immediate hasType_subsumption : env.

Lemma hasType_wfEnv :
  forall P t' Gamma e t mcs n ncs,  (*!!*)
    wfProgram P t' mcs->  (*!!*)
    P; Gamma |- e \in t # n |> ncs -> (*!!*)
    wfEnv P Gamma.
Proof with eauto.
  induction e; introv wfP hasType; inv hasType;
  try(eapply IHe1); try(eapply IHe); try(eassumption).
  match goal with H: hasType _ _ (EVar ?v) _ _ _|- _ => inv H end... (*!!*)
  apply wfSubsumption_frame in H2 as [Hsub1].
  eapply hasType_subsumption with (Gamma := Gamma1)...
Qed.

Hint Immediate hasType_wfEnv : env.

Corollary hasType_subsumption_extend : 
  forall P t' Gamma Gamma' e x t1 t mcs n ncs,  (*!!*)
    wfProgram P t' mcs -> (*!!*)
    wfSubsumption Gamma Gamma' ->
    wfEnv P Gamma ->
    wfEnv P Gamma' ->
    P; extend Gamma (env_var x) t1 |- e \in t # n |> ncs -> (*!!*)
    P; extend Gamma' (env_var x) t1 |- e \in t # n |> ncs. (*!!*)
Proof with eauto using wfSubsumption_extend with env.
  introv wfP wfSub wfGamma wfGamma' hasType.
  assert (wfT: wfType P t1)...
  eapply hasType_subsumption
  with (Gamma := extend Gamma (env_var x) t1)...
Qed.

Corollary hasType_flip :
  forall P t' Gamma x y e t t1 t2 mcs n ncs, (*!!*)
    wfProgram P t' mcs -> (*!!*)
    P; (extend (extend Gamma x t1) y t2) |- e \in t # n |> ncs -> (*!!*)
    x <> y ->
    P; (extend (extend Gamma y t2) x t1) |- e \in t # n |> ncs. (*!!*)
Proof with eauto using hasType_subsumption.
  introv wfP hasType Hneq.
  eapply hasType_subsumption
  with (Gamma := (extend (extend Gamma x t1) y t2))...
  + econstructor.
    introv.
    rewrite extend_order...
  + eapply hasType_wfEnv in hasType...
    apply wfEnv_equiv
    with (extend (extend Gamma x t1) y t2)...
Qed.

Corollary hasType_shadow :
  forall P t' Gamma x y e t t1 t2 mcs n ncs,  (*!!*)
    wfProgram P t' mcs -> (*!!*)
    P; (extend (extend Gamma x t1) y t2) |- e \in t # n |> ncs -> (*!!*)
    x = y ->
    P; (extend Gamma y t2) |- e \in t # n |> ncs. (*!!*)
Proof with eauto with env.
  introv wfP hasType Hneq.
  eapply hasType_subsumption
  with (Gamma' := extend Gamma y t2)
  in hasType; eauto 2 with env.
  eapply hasType_wfEnv in hasType; eauto.
  apply wfEnv_equiv
  with (extend (extend Gamma x t1) y t2)...
Qed.

Lemma hasType_extend_loc :
  forall e P Gamma t t' l c mcs n ncs,  (*!!*)
    wfProgram P t' mcs -> (*!!*)
    P; Gamma |- e \in t # n |> ncs -> (*!!*)
    Gamma (env_loc l) = None ->
    wfType P (TClass c) ->
    P; extend Gamma (env_loc l) (TClass c) |- e \in t # n |> ncs. (*!!*)
Proof with eauto 3 using hasType, hasType_flip with env.
  expr_cases(induction e) Case;
    introv wfP hasType Heq wfT; inv hasType;
  match goal with
    | [Case := "ELocked" |- _] => inv H1; econstructor
    | _ => idtac
  end;
  try(econstructor; try(case_extend)); eauto 3;
  match goal with
    | [H: _; _ |- EVar _ \in _ # _ |> _ |- _] => inv H; constructor (*!!*)
    | [H: _; _ |- EVal _ \in _ # _ |> _ |- _] => inv H; econstructor (*!!*)
    | _ => idtac
  end...
  + Case "EPar".
    inverts H2 as frame1 frame2 disj1 disj2...
    econstructor; introv envLookup...
    - case_extend...
      apply frame1 in envLookup. rewrite_and_invert.
    - case_extend...
      apply frame2 in envLookup. rewrite_and_invert.
Qed.

Lemma hasType_subst_fresh :
  forall P Gamma e t x y n ncs, (*!!*)
    P; Gamma |- e \in t # n |> ncs -> (*!!*)
    fresh Gamma (env_var (SV x)) ->
exists (n': nature) (ncs' : NatureConstraint -> Prop),
    P; Gamma |- subst x y e \in t # n' |> ncs'. (*!!*)
Proof with eauto using no_locks_subst.
  introv hasType Hfresh.
  gen Gamma. gen t n ncs.
  expr_cases (induction e) Case;
    introv hasType Hfresh; inv hasType...

  + Case "EVal".
      exists. econstructor...
  + Case "EVar".
      exists. econstructor... unfold subst_var. destruct_var. cases_if... exact H1.
  + Case "ENew".
      exists. econstructor...
  + Case "ECall". 
      edestruct IHe... inv H. exists.
      econstructor... unfold subst_var. destruct_var... cases_if... 
  + Case "ESelect".
      exists.
      econstructor... unfold subst_var. destruct_var. cases_if... 
      match goal with
      | [hasType: _; _ |- EVar _ \in _ # _ |> _ |- _] => inv hasType  (*!!*)
      end; congruence...
      exact H1.
  + Case "EUpdate".
      edestruct IHe... inv H. exists.
      econstructor... unfold subst_var. destruct_var... cases_if...
      match goal with
      | [hasType: _; _ |- EVar _ \in _ # _ |> _ |- _] => inv hasType  (*!!*)
      end; congruence...

  + Case "ELet".
      edestruct IHe1... inv H.
      simpl. cases_if. (*!!*)
        exists. econstructor...
        edestruct IHe2... (*!!*)
         unfold fresh. rewrite extend_neq... congruence. inv H1.
         exists. econstructor...

  + Case "ECast".
      edestruct IHe... inv H. exists.
      econstructor... 

  + Case "EPar". 
    edestruct IHe1... 
    inv H2. unfold fresh.
    remember (Gamma1 (env_var (SV x))) as G1.
    symmetry in HeqG1. destruct G1... apply H in HeqG1...
    congruence.
      edestruct H...

edestruct IHe2... 
    inv H2. unfold fresh.
    remember (Gamma2 (env_var (SV x))) as G2.
    symmetry in HeqG2. destruct G2... apply H7 in HeqG2...
    congruence.
 edestruct H1...

edestruct IHe3...
      edestruct H8...
exists.
     econstructor... 

  + Case "ELock".
      edestruct IHe... inv H. exists.
      econstructor... unfold subst_var. destruct_var. cases_if... 
      match goal with
      | [hasType: _; _ |- EVar _ \in _ # _ |> _ |- _] => inv hasType  (*!!*)
      end; congruence.
      exact H1.

  + Case "ELocked".
      edestruct IHe... inv H. exists.
      econstructor...
Qed.

Lemma hasType_subst :
  forall P Gamma e t t' t'' x y mcs n ncs,  (*!!*)
    wfProgram P t'' mcs ->  (*!!*)
    wfEnv P Gamma ->
    P; extend Gamma (env_var (SV x)) t' |- e \in t # n |> ncs -> (*!!*)
    fresh Gamma (env_var (DV y)) ->
exists n' ncs', (*!!*)
    P; extend Gamma (env_var (DV y)) t' |- subst x y e \in t # n' |> ncs'. (*!!*)
Proof with eauto using no_locks_subst with env.
  introv wfP wfGamma hasType Hfresh.
  gen Gamma.
  gen t n ncs. gen t'.
  gen x. gen y.
  expr_cases (induction e) Case;
    intros; simpl; try(unfold subst_var); inv hasType;
    repeat
    match goal with
      | [x : var, H : hasType _ _ (EVar ?x) _ _ _ |- _] => inv H
      | [H : hasType _ _ (EVal _) _ _ _ |- _] => inv H
      | _ => idtac
    end; repeat(destruct_var); try(cases_if); subst;
    try(simpl_extend_hyp);

    match goal with (*!!*)
      | [Case := "ELet" |- _] => edestruct IHe1 with (Gamma := Gamma); eauto 1
      | [IHe : forall _ _ _ _ _ _, _ |- _ ] => edestruct IHe with (Gamma := Gamma); eauto 1
      | _ => idtac
   end; 

    match goal with
      | [H : exists _ , _ ; _ _ |- _ \in _ # _ |> _ |- _ ] => inv H
      | _ => idtac
    end;

    match goal with (*!!*)
      | [Case := "ELet" |- _] => idtac
      | [Case := "EPar" |- _] => idtac
      | _ => exists; (*!!*)
             try(solve[try(econstructor); 
                       try(case_extend);
                       try(inv_eq); eauto 4 using no_locks_subst with env]) 
    end.

     + Case "ELet".
      exists.
      econstructor...
      eapply hasType_shadow in H6; eauto 3 with env. (*!!*)
      eapply hasType_subsumption
      with (Gamma := extend Gamma (env_var (SV s)) t0);
        eauto 4 with env.
    + Case "ELet".
      edestruct IHe2 with (Gamma := (extend Gamma (env_var (SV s)) t0))... (*!!*)
      eapply hasType_flip... inv H0. (*!!*)
      exists. (*!!*)
      econstructor... eapply hasType_flip; eauto 3 with env.
    + Case "EPar".
      remember (Gamma1 (env_var (SV x))) as G1.
      symmetry in HeqG1.
      destruct G1.


      edestruct IHe1 with (Gamma := (drop Gamma1 (env_var (SV x)))) (t' := t') (x := x)...
           { eapply hasType_subsumption
                with (Gamma := Gamma1); eauto 3 with env.
             econstructor...
             introv Henv. case_extend. rewrite_and_invert.
             inv H2. apply H in HeqG1...
             case_drop...
             apply wfEnv_extend_var...
           }
           { unfold fresh.
             remember (Gamma1 (env_var (DV y))) as G1'.
             symmetry in HeqG1'. destruct G1'... inv H2.
             apply H in HeqG1'. rewrite extend_neq in HeqG1'...
             congruence.
             case_drop...
           }
      inv H.

      - pose proof hasType_subst_fresh as Lemma. (*!!*)
        edestruct Lemma with (P) (drop Gamma2 (env_var (SV x))) (e2) (t2) (x) (y) (n2) (ncs2).
          inv H2. apply H8 in HeqG1... eapply hasType_subsumption with (Gamma := Gamma2)...
          econstructor... introv Henv. case_drop...
          unfold fresh. case_drop...
        inv H.

        exists. (*!!*)
        eapply T_Par
        with (Gamma1 := extend (drop Gamma1 (env_var (SV x))) (env_var (DV y)) t')
             (Gamma2 := drop Gamma2 (env_var (SV x)))...
        * {econstructor.
           + introv Henv. case_extend...
             rewrite extend_neq in Henv...
             inv H2.
             unfold drop in Henv. cases_if...
             apply H in Henv. rewrite extend_neq in Henv...
           + introv Henv. unfold drop in Henv. cases_if...
             inv H2. apply H9 in Henv. (*!!*)
             rewrite extend_neq in Henv...
           + introv Henv.
             destruct (id_eq_dec (env_var (DV y)) (env_var x6)). (*!!*)
             - inv_eq. simpl_extend_hyp. inv_eq.
               case_drop...
               remember (Gamma2 (env_var (DV y))) as G2.
               symmetry in HeqG2. destruct G2...
               inv H2. apply H9 in HeqG2. (*!!*)
               rewrite extend_neq in HeqG2...
               congruence.
             - rewrite extend_neq in Henv...
               case_drop...
               unfold drop in Henv.
               cases_if... inv H2. apply H13 in Henv... (*!!*)
           + introv Henv. case_extend...
             - inv_eq. unfold drop in Henv. cases_if...
               inv H2. apply H9 in Henv... (*!!*)
             - case_drop...
               unfold drop in Henv. cases_if...
               inv H2. apply H14 in Henv... (*!!*)
          }
      - remember (Gamma2 (env_var (SV x))) as G2.
        symmetry in HeqG2.
        destruct G2.


        edestruct IHe2 with (Gamma := drop Gamma2 (env_var (SV x))) (t' := t') (x := x)...
           { eapply hasType_subsumption
                with (Gamma := Gamma2); eauto 3 with env.
             econstructor...
             introv Henv. case_extend. rewrite_and_invert.
             inv H2. apply H1 in HeqG2...  (*!!*)
              case_drop...
               apply wfEnv_extend_var...
           }
           { unfold fresh.
             remember (Gamma2 (env_var (DV y))) as G2'.
             symmetry in HeqG2'. destruct G2'... inv H2.
             apply H1 in HeqG2'. rewrite extend_neq in HeqG2'... (*!!*)
             congruence.
             case_drop...
           }
        inv H.

        pose proof hasType_subst_fresh as Lemma. (*!!*)
        edestruct Lemma with (P) (drop Gamma1 (env_var (SV x))) (e1) (t1) (x) (y) (n1) (ncs1).
          inv H2. apply H9 in HeqG2... eapply hasType_subsumption with (Gamma := Gamma1)...
          econstructor... introv Henv. case_drop...
          unfold fresh. case_drop...
        inv H.
  
        * exists.
          {eapply T_Par
           with (Gamma1 := drop Gamma1 (env_var (SV x)))
                (Gamma2 := extend (drop Gamma2 (env_var (SV x))) (env_var (DV y)) t')...
           + econstructor.
             - introv Henv. unfold drop in Henv. cases_if...
               inv H2. apply H8 in Henv. (*!!*)
               rewrite extend_neq in Henv...
             - introv Henv. case_extend...
               rewrite extend_neq in Henv...
               inv H2. unfold drop in Henv. cases_if...
               apply H8 in Henv. rewrite extend_neq in Henv... (*!!*)
             - introv Henv. unfold drop in Henv.
               cases_if... case_extend...
               * inv_eq. inv H2. apply H8 in Henv... (*!!*)
               * case_drop...
                 inv H2...
             - introv Henv.
               destruct (id_eq_dec (env_var (DV y)) (env_var x6)). (*!!*)
               * inv_eq. simpl_extend_hyp. inv_eq.
                 case_drop...
                 remember (Gamma1 (env_var (DV y))) as G1'.
                 symmetry in HeqG1'. destruct G1'...
                 inv H2. apply H8 in HeqG1'.  (*!!*)
                 rewrite extend_neq in HeqG1'...
                 congruence.
               * rewrite extend_neq in Henv...
                 case_drop...
                 unfold drop in Henv.
                 cases_if... inv H2. apply H14 in Henv...  (*!!*)
          }
        * { pose proof hasType_subst_fresh as Lemma. (*!!*)
              edestruct Lemma with (P) (Gamma1) (e1) (t1) (x) (y) (n1) (ncs1).
              eapply hasType_subsumption with (Gamma := Gamma1)...
              unfold fresh...
            inv H.

              edestruct Lemma with (P) (Gamma2) (e2) (t2) (x) (y) (n2) (ncs2).
              eapply hasType_subsumption with (Gamma := Gamma2)...
              unfold fresh...
            inv H.

           exists. (*!!*)
           eapply T_Par
           with (Gamma1 := Gamma1) (Gamma2 := Gamma2)...
           + econstructor...
             - introv Henv. case_extend.
               inv H2. apply H in Henv...
               inv H2. destruct (id_eq_dec x6 (env_var (SV x))). (*!!*)
               * subst. congruence.
               * apply H in Henv...
                 rewrite extend_neq in Henv...
             - introv Henv. case_extend.
               inv H2. apply H8 in Henv... (*!!*)
               inv H2. destruct (id_eq_dec x6 (env_var (SV x))). (*!!*)
               * subst. congruence.
               * apply H8 in Henv... (*!!*)
                 rewrite extend_neq in Henv...
             - inv H2...
             - inv H2...
          }
Qed.


(*
============
Corollaries
============
*)

Corollary envModelsVars :
  forall P Gamma V n x t, (*!!*)
    wfVars P Gamma n V ->
    Gamma (env_var (DV x)) = Some t ->
    exists v n' ncs', V x = Some v /\ P; Gamma |- EVal v \in t # n' |> ncs'. (*!!*)
Proof with eauto.
  introv wfV envLookup.
  inv wfV...
Qed.

Hint Immediate envModelsVars.

Corollary wfVars_fresh :
  forall P Gamma V n m,
    wfVars P Gamma n V ->
    n <= m ->
    fresh V (DVar m).
Proof with eauto.
  introv wfV.
  inverts wfV as _ _ _ Hfresh...
Qed.

Hint Immediate wfVars_fresh.

Corollary wfVars_fresh_env :
  forall P Gamma V n m, 
    wfVars P Gamma n V ->
    n <= m ->
    fresh Gamma (env_var (DV (DVar m))).
Proof with eauto.
  introv wfV Hle.
  remember (Gamma (env_var (DV (DVar m)))) as t.
  destruct t...
  symmetry in Heqt.
  eapply envModelsVars in Heqt as (v & nature & ncs & vLookup & Val)... (*!!*)
  rewrite wfVars_fresh in vLookup...
Qed.

Hint Immediate wfVars_fresh_env.

Corollary envModelsHeap :
  forall P Gamma H l t,
    wfHeap P Gamma H ->
    Gamma (env_loc l) = Some t ->
    exists c F RL, heapLookup H l = Some (c, F, RL) /\
                wfFields P Gamma c F /\
                t = TClass c.
Proof with eauto.
  introv wfH envLookup.
  inverts wfH as wfGamma.
  assert (Hclass: exists c, t = TClass c)
    by (inv wfGamma; eauto).
  inv Hclass as [c].
  exists c.
  assert (Hlookup: exists F RL, heapLookup H l = Some (c, F, RL) /\
                                wfFields P Gamma c F)...
  inv Hlookup as [F [RL]].
  exists F RL. crush.
Qed.

Hint Immediate envModelsHeap.

Ltac wfEnvLookup :=
  match goal with
    | [wfV : wfVars ?P ?Gamma ?n ?V,
       envLookup: ?Gamma (env_var (DV ?x)) = Some ?t |- _] => 
        assert (HVex: exists v n' ncs', V x = Some v /\ P; Gamma |- EVal v \in t # n' |> ncs') (*!!*)
           by eauto using envModelsVars;
          let v := fresh "v" in
          let n' := fresh "n'" in
          let ncs' := fresh "ncs'" in
          let Vlookup := fresh "Vlookup" in
          let hasType := fresh "hasType" in
          inv HVex as [v [ n' [ ncs' [Vlookup hasType]]]];
          clear envLookup
    | [wfH : wfHeap ?P ?Gamma ?H,
             envLookup: ?Gamma (env_loc ?l) = Some ?t |- _] =>
      assert (Hex: exists c F RL,
                     heapLookup H l = Some (c, F, RL) /\
                     wfFields P Gamma c F /\
                     t = TClass c)
        by eauto using envModelsHeap;
        let c := fresh "c" in
        let F := fresh "F" in
        let RL := fresh "RL" in
        let Hlookup := fresh "Hlookup" in
        let wfF := fresh "wfF" in
        let Heq := fresh "Heq" in
        inv Hex as (c & F & RL & Hlookup & wfF & Heq);
          try(inv Heq); clear envLookup
    | _ => fail 1 "no well-formed environment lookup in context"
  end.

Corollary wfHeap_fresh_env :
  forall P Gamma H,
    wfHeap P Gamma H ->
    forall l, length H <= l -> fresh Gamma (env_loc l).
Proof with eauto.
  introv wfH Hle.
  unfold fresh.
  remember (Gamma (env_loc l)) as t.
  symmetry in Heqt.
  destruct t...
  wfEnvLookup.
  assert (contra: l < length H)
    by (apply heapLookup_lt; eauto).
  omega.
Qed.

Hint Immediate wfHeap_fresh_env.

Corollary heapMirrorsEnv :
  forall P Gamma H l c,
    wfHeap P Gamma H ->
    (exists F RL, heapLookup H l = Some (c, F, RL)) ->
    Gamma (env_loc l) = Some (TClass c).
Proof with eauto.
  introv wfH Hlookup.
  inverts wfH as wfGamma envModels heapMirrors.
  destruct Hlookup as [F [RL Hlookup]].
  assert (Hlookup' : heapLookup H l <> None) by congruence.
  apply heapMirrors in Hlookup' as [c' Hlookup'].
  assert (c = c')
    by (apply envModels in Hlookup' as [F' [RL' [Hlookup']]];
        rewrite_and_invert).
  subst...
Qed.

Hint Immediate heapMirrorsEnv.
