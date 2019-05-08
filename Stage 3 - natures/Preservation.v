Require Import Coq.Sets.Ensembles. (*!!*)

Require Import MetaProp.
Require Import SyntaxProp.
Require Import DynamicProp.
Require Import TypesProp.
Require Import WellFormednessProp.
Require Import Shared.
Require Import Locking.

Hint Constructors is_econtext.
Hint Constructors cfg_blocked.

Tactic Notation "preservation_context_tactic" integer(n) :=
  solve[
      intuition;
         match goal with
           | [IH : forall cfg', _ / ?cfg ==> cfg' -> ?P,
                Hstep : _ / ?cfg ==> _ |- _] =>
             eapply IH in Hstep as (Gamma' & n_nature' & NCS' & wfCfg' & Hsub); (*!!*)
               eauto;
               inverts wfCfg' as Hfresh' wfH' wfV' wfT';
               inversion wfT'; inversion Hsub;
               exists Gamma'; exists; split; try(eassumption)
         end;
         repeat (econstructor;
                 simpl;
                 eauto n using hasType_subsumption,
                               hasType_subsumption_extend
                          with env); try(omega);
                 try (simple eapply hasType_wfType; eauto; eapply T_Call; eauto) (*!!*)
    | exists; split; eauto with env; 
      try (simple apply WF_Cfg; eauto; (*!!*)
      simple apply WF_EXN;
        try (simple eapply hasType_wfType; eauto;
        eapply T_Call; eauto);
      simple eapply hasType_wfEnv ; eauto)].

Hint Immediate lt_0_Sn.

Lemma single_threaded_preservation :
  forall P t' Gamma H V n Ls e cfg' t mcs n_nature ncs,
    wfProgram P t' mcs -> (*!!*)
    wfConfiguration P Gamma (H, V, n, T_Thread Ls e) t n_nature ncs ->
    P / (H, V, n, T_Thread Ls e) ==> cfg' ->
    exists Gamma' n_nature' ncs',
      wfConfiguration P Gamma' cfg' t n_nature' ncs' /\
      wfSubsumption Gamma Gamma'.
Proof with eauto using subtypeOf with env.
  introv wfP wfCfg Hstep.
  inverts wfCfg as Hfresh wfH wfV wfT wfL.
  inverts wfT as Hfree hasType.
  gen cfg'.
  hasType_cases(induction hasType) Case; intros;
  (* Some trivial cases can be discarded*)
  try(inv Hstep; malformed_context);

  (* All variables must be dynamic *)
  match goal with
    | [Hfree : freeVars _ = nil |- _] =>
      simpl in Hfree;
        repeat
        match goal with
          | [Hfree : freeVars _ ++ _ ++ _ = nil |- _] =>
            simpl in Hfree;
              apply app_eq_nil in Hfree as (Hfree1 & Hfree2);
              apply app_eq_nil in Hfree2 as (Hfree2 & Hfree3)
          | [Hfree : freeVars _ ++ _ = nil |- _] =>
            simpl in Hfree;
              apply app_eq_nil in Hfree as (Hfree1 & Hfree2)
          | [x : var |- _] =>
            destruct x; try(congruence)
        end
    | _ => idtac
  end;

  (* Unfold the resulting configuation *)
  destruct cfg' as [[[H' V'] nat'] T'];

  (* Assert that the fresh symbols grow monotonically *)
  assert (Hmono: n <= nat')
    by eauto using step_n_monotonic;
 try(
  assert (wfL': wfLocking H' T')
    by (eapply wfLocking_preservation in Hstep; eauto)
    ).

  + Case "T_Var".
    inverts Hstep; try malformed_context...
    wfEnvLookup. rewrite_and_invert.
    eexists. exists... (*!!*)

  + Case "T_New".
    inv Hstep; try malformed_context.
    exists (extend Gamma (env_loc (length H)) (TClass c)).
    assert (wfEnv P (extend Gamma (env_loc (length H)) (TClass c)))...
    assert (fresh Gamma (env_loc (length H)))...
    exists. (*!!*)
    split...
    apply wfConfiguration_substitution
    with (ENew c) (n0) ((Empty_set NatureConstraint))... (*!!*)
    eapply wfConfiguration_heapExtend;
      eauto using wfFields_declsToFields. (*!!*)
      simple apply WF_Cfg...
      simple apply WF_Thread...
      simple apply T_New...

  + Case "T_Call".
    assert (wfL': wfLocking H' T').
       eapply wfLocking_preservation in Hstep; eauto.
       simple apply WF_Cfg...
       simple apply WF_Thread...
       eapply T_Call...

    assert (wfL'': wfLocking H (T_Thread Ls e))
      by eauto 3 using wfLocking_econtext.
    inv Hstep;
      try(malformed_context); try(inv_eq);
      try(preservation_context_tactic 2).

    - SCase "EvalCall". clear IHhasType.
      assert(Hsub: subtypeOf P (TClass c) t1)
      by (wfEnvLookup; rewrite_and_invert;
          inv hasType0; wfEnvLookup;
          assert (c1 = c) by crush; subst; eauto). (*!!*)

      assert (wfC: wfType P (TClass c))...
      assert (cLookup: classLookup P c <> None)
        by (inv wfC; assumption).
      apply classLookup_not_none in cLookup as (i & fs & ms & cLookup).
      inv wfP. (*!!*)


      assert (wfCls: wfClassDecl (cds, ids, e) mcs0 (Cls c i fs ms)) (*!!*)
 by (lookup_forall as wfCls; eauto)...

      assert (mtds = ms) 
        by (unfold methods in H17; destruct classLookup; eauto; inv_eq; inv_eq). (*!!*)
      subst.
      inverts wfCls as Hsigs wfFlds wfMtds.

      assert (wfT2: wfType (cds, ids, e) t2).
        simple eapply hasType_wfType. econstructor... exact hasType. (*!!*)
      assert (sigLookup: methodSigLookup (extractSigs ms) m = Some (MethodSig m (y, t2) t)).
        simple eapply methodSigs_sub...
        econstructor...  (*!!*)

      eapply extractSigs_sound in sigLookup as [e' mLookup]. (*!!*)
      rewrite_and_invert.

(****************************************)
      pose proof hasType_subst as Lemma. (*!!*)

      lookup_forall (Method m (y, t2) t e') as wfMtd. inv wfMtd. simpls. (*to have the hypothesis wfType (cds, ids, e) t2*)

      edestruct Lemma with (Gamma := (extend Gamma (env_var (SV y)) t2)) (x:=this) (y:=(DVar n)) (e:=e') (t:=t) (t':=TClass c).

           (*wfProgram*)
              eapply WF_Program...
           (*wfEnv*)
              simple apply wfEnv_extend_var.
                  simple eapply hasType_wfEnv ; trivial... eapply WF_Program... 
                  exact wfT2.
           (*e'*)
              eapply hasType_subsumption with (Gamma := (extend
                                                   (extend empty (env_var (SV y)) t2)
                                                    (env_var (SV this)) (TClass c)));
                        eauto 3 using wfSubsumption_extend with env.
                  eapply WF_Program...
                  simple apply wfEnv_extend_var.
                    simple apply wfEnv_extend_var.
                      simple eapply hasType_wfEnv ; trivial... eapply WF_Program...
                      exact H11.
                      exact wfC.
           (*fresh*)
              assert (fresh Gamma (env_var (DV (DVar n))))...

      inv H5.
      edestruct Lemma with (Gamma := (extend Gamma (env_var (DV (DVar n))) (TClass c)))
          (e:= subst this (DVar n) e')  (x:= y) (y:= DVar (S n))... 

          (*wfProgram*)
              eapply WF_Program...
          (*wfEnv*)
              simple apply wfEnv_extend_var. simple eapply hasType_wfEnv ; trivial... eapply WF_Program... 
              exact wfC.
          (*subst this (DVar n) e'*)
              eapply hasType_flip... eapply WF_Program...
          (*fresh*)
              assert (n <= S n)...
              assert (fresh Gamma (env_var (DV (DVar (S n)))))...
              unfold fresh. case_extend. inv_eq. omega.

      inv H5.
(****************************************)
      exists (extend
                (extend
                   Gamma (env_var (DV (DVar n))) (TClass c))
                (env_var (DV (DVar (S n)))) t2).
      exists.
 
      assert (n <= S n)...
      assert (fresh Gamma (env_var (DV (DVar n))))...
      assert (fresh Gamma (env_var (DV (DVar (S n)))))... 
      split...
      * { econstructor; auto.
          + eapply wfHeap_invariance
            with (Gamma := Gamma); eauto 3 with env.
            econstructor... simple apply wfEnv_extend_var.
            simple apply wfEnv_extend_var.
            simple eapply hasType_wfEnv ; trivial...
            econstructor... exact wfC. exact wfT2.
          + 
            eapply wfVars_extend; eauto 2 with env. eapply WF_Program... (*!!*)
            - eapply wfVars_extend... eapply WF_Program... (*!!*)
              apply wfVars_ge with n...
                simple eapply T_Loc... (*!!*)
                 eapply hasType_wfEnv ; trivial... (*!!*)
                eapply WF_Program... (*!!*)
            - eapply hasType_subsumption
              with (Gamma := Gamma);
              eauto 2 using wfSubsumption_fresh with env.
                 eapply WF_Program... (*!!*)
                  simple apply wfEnv_extend_var... (*!!*)
                  simple eapply hasType_wfEnv ; trivial...  (*!!*)
                 eapply WF_Program...   (*!!*)
          + lookup_forall (Method m (y, t2) t e') as wfMtd.
            inv wfMtd. simpls.
            econstructor...
            - autorewrite with freeVars. exact H30.
        }
  + Case "T_Select".
    inv hasType.
    assert (wfType P t)
      by eauto using fieldLookup_wfType.
    inv Hstep;
      try(malformed_context); try(inv_eq);
      try(preservation_context_tactic 2).
    - SCase "EvalSelect". clear IHhasType.
      wfEnvLookup. rewrite_and_invert.
      inverts hasType as Vlookup envLookup Hsub.
      assert (TClass c = TClass c1). symmetry... destruct H. (*!!*)
      assert (c0 = c)
        by (wfEnvLookup; rewrite_and_invert); subst.
      assert (wfF: exists v n ncs, F f = Some v /\
                             P; Gamma |- EVal v \in t # n |> ncs) (*!!*)
        by eauto using dyn_wfFieldLookup, wfHeap_wfFields.
      inv wfF as (v' & n & ncs & Flookup & hasType). (*!!*)
      rewrite_and_invert.
      inv wfL.
      exists. split...

  + Case "T_Update".
    assert (wfL': wfLocking H' T'). 
      eapply wfLocking_preservation in Hstep; eauto.
      simple apply WF_Cfg...
      simple apply WF_Thread...
      eapply T_Update...

    assert (wfL'': wfLocking H (T_Thread Ls e))
      by eauto 3 using wfLocking_econtext.
    inv Hstep;
      try(malformed_context); try(inv_eq);
      try(preservation_context_tactic 2).
    - SCase "EvalUpdate". clear IHhasType1. clear IHhasType2.
      inv hasType1.
      wfEnvLookup. rewrite_and_invert.
      inv hasType. wfEnvLookup.
      assert (Heq: TClass c2 = TClass c)... inv Heq. (*!!*)
      rewrite_and_invert.
      exists Gamma. exists. split... (*!!*)
      inverts wfL as ? ? wfL.
      inv wfL...
      eapply wfConfiguration_heapUpdate;
        eauto using wfFields_extend, wfHeldLocks_taken;
        crush.

  + Case "T_Let".
    assert (wfL': wfLocking H' T').
      eapply wfLocking_preservation in Hstep...
      econstructor...
      econstructor.
      simpl...
        apply T_Let with (t := t)... (*!!*)
    assert (wfLocking H (T_Thread Ls e))
      by (apply wfLocking_econtext with (ctx := ctx_let x body); eauto).
    inv Hstep;
      try(malformed_context); try(inv_eq);
      try(preservation_context_tactic 2).
    - SCase "EvalLet". clear IHhasType1. clear IHhasType2.

        pose proof hasType_subst as Lemma. (*!!*)
        edestruct Lemma with (P) (Gamma)
          (body) (t'0) (t) (t') (x) (DVar n) (mcs) (n') (ncs')...
        inv H.

      exists (extend Gamma (env_var (DV (DVar n))) t). exists.
      split...
      * { econstructor; auto.
          + eapply wfHeap_invariance
            with (Gamma := Gamma);
            eauto 2 with env.
          + eapply wfVars_extend...
            eapply wfVars_ge...
          + econstructor;
            eauto using H2 with env.
            autorewrite with freeVars...
        }
      * apply wfSubsumption_fresh...
  + Case "T_Cast".
    assert (wfL'': wfLocking H (T_Thread Ls e))
      by eauto 3 using wfLocking_econtext.
    inv Hstep;
      try(malformed_context); try(inv_eq);
      try(preservation_context_tactic 2).
    - SCase "EvalCast". clear IHhasType.
      exists Gamma. exists. split...
      econstructor...
      econstructor...
      inv hasType... eauto using subtypeOf with env.
  + Case "T_Par".
    assert (wfL': wfLocking H' T').
      eapply wfLocking_preservation in Hstep...
      econstructor...
      econstructor.
      simpl... crush.
        eapply T_Par... (*!!*)
    inv Hstep; try(malformed_context).
    exists Gamma. exists. (*!!*)
    split...
    econstructor...
    apply wfSubsumption_frame in H0 as []...
    econstructor...
    - econstructor...
      eapply hasType_subsumption with (Gamma := Gamma1)...
    - econstructor...
      eapply hasType_subsumption with (Gamma := Gamma2)...
  + Case "T_Lock".
    inv hasType1.
    wfEnvLookup.
    inv hasType.
    - SCase "V x = l".
      inv Hstep;
      try(malformed_context); try(inv_eq);
      try(preservation_context_tactic 2);
      rewrite_and_invert.
      exists Gamma. exists. split...
      econstructor...
      eapply wfHeap_update...
      eapply wfHeap_wfFields...
    - inv Hstep;
      try(malformed_context); try(inv_eq);
      try(preservation_context_tactic 2);
      rewrite_and_invert.
  + Case "T_Locked".
    inv hasType1.
    assert (wfL'': wfLocking H (T_Thread Ls e))
      by eauto 3 using wfLocking_econtext.
    inv Hstep;
      try(malformed_context); try(inv_eq);
      try(preservation_context_tactic 2). 
    - SCase "EvalLock_Release". clear IHhasType1. clear IHhasType2.
      exists Gamma. exists. split... (*!!*)
      econstructor...
      eapply wfHeap_update...
      eapply wfHeap_wfFields...
Unshelve. all: eauto.
Qed.

Theorem preservation :
  forall P t' Gamma cfg cfg' t mcs n_nature ncs,
    wfProgram P t' mcs -> (*!!*)
    wfConfiguration P Gamma cfg t n_nature ncs ->
    P / cfg ==> cfg' ->
    exists Gamma' n_nature' ncs',
      wfConfiguration P Gamma' cfg' t n_nature' ncs'/\
      wfSubsumption Gamma Gamma'.
Proof with eauto using wfConfiguration.
  introv wfP wfCfg Hstep.
  inverts wfCfg as Hfresh wfH wfV wfT wfL.
  gen t cfg' wfL wfT. gen n_nature ncs. (*!!*)
  induction T; intros...
  + Case "T = EXN".
    (* EXN does not step *)
    inv Hstep.
  + Case "T = T_Thread e".
    eapply single_threaded_preservation...
  + Case "T = T_Async T1 T2 e".
    inverts wfT as Hfree hasType wfT1 wfT2.
    inverts wfL as wfWl wfRl Hdisj wfL1 wfL2.
    destruct cfg' as [[[H' V'] n'] T'].
    assert (Hmono: n <= n')
      by eauto using step_n_monotonic.

    assert(wfLocking H' T'). (*!!*)
     simple eapply wfLocking_preservation.
     exact wfP.
     simple apply WF_Cfg.
     exact Hfresh.
     exact wfH.
     exact wfV.
     eapply WF_Async.
     exact Hfree.
     exact hasType.
     exact wfT1.
     exact wfT2.
     (*external*) (wfLocking_context_tactic 1).
     exact Hstep.

    inv Hstep;
    try(
        solve
          [
            (* When no thread steps, Gamma still types the cfg *)
            exists Gamma; exists; split; eauto with env
          |
            (* When one of the threads step, IH applies *)
            match goal with
              | [IH: forall n_nature ncs t cfg', _ / (_, _, _, ?T) ==> cfg' -> _,
                   Hstep: _ / (_, _, _, ?T) ==> _ |- _]
                => eapply IH in Hstep as [Gamma' [natureH [ncsH [wfCfg' wfSub]]]];
                  eauto; inverts wfCfg'; exists Gamma'; exists
            end;
            split; eauto;
            econstructor; eauto with arith;
            econstructor;
            eauto using hasType_subsumption,
                        wfThreads_subsumption
          ]).
Qed.
