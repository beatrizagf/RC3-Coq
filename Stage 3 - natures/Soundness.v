Require Import DynamicProp.
Require Import TypesProp.
Require Import WellFormednessProp.
Require Import Progress.
Require Import Preservation.
Require Import Shared.

Theorem type_soundness :
  forall P t' Gamma cfg t cfg' mcs n_nature ncs, (*!!*)
    wfProgram P t' mcs -> (*!!*)
    wfConfiguration P Gamma cfg t n_nature ncs -> (*!!*)
    P / cfg ==>* cfg' ->
    (exists Gamma' n_nature' ncs', (*!!*)
       wfConfiguration P Gamma' cfg' t n_nature' ncs' /\ (*!!*)
       wfSubsumption Gamma Gamma'
    ) /\
    (cfg_exn(cfg') \/ cfg_done(cfg') \/
     cfg_blocked(cfg') \/
     exists cfg'', P / cfg' ==> cfg'').
Proof with eauto with env.
  introv wfP wfCfg HstepMulti.
  split.
  + Case "Preservation".
    gen Gamma n_nature ncs. (*!!*)
    induction HstepMulti as [cfg|cfg cfg' cfg'' Hstep]; intros.
    - SCase "cfg = cfg'".
      exists Gamma...
    - SCase "cfg ==> cfg'".
      eapply preservation in Hstep
        as (Gamma' & n_nature' & ncs' & wfCfg' & HSub)... (*!!*)
      apply IHHstepMulti in wfCfg'
        as (Gamma'' & n_nature'' & ncs'' & wfCfg'' & HSub'). (*!!*)
      exists Gamma''. exists n_nature''. exists ncs''. split...  (*!!*)
      eapply wfSubsumption_trans...
  + Case "Progress".
    gen Gamma n_nature ncs. (*!!*)
    induction HstepMulti as [cfg|cfg cfg' cfg'' Hstep]; intros.
    - SCase "cfg = cfg'".
      eapply progress in wfCfg...
    - SCase "cfg ==> cfg'".
      eapply preservation in Hstep
        as (Gamma' & n_nature' & ncs' & wfCfg' & HSub)...  (*!!*)
Qed.
