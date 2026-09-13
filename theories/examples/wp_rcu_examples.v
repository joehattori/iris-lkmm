From Stdlib Require Import List.
From iris.base_logic.lib Require Import fancy_updates.
From iris.proofmode Require Import proofmode.
From iris_lkmm.lkmm Require Import rcu_matching.
From iris_lkmm.operational Require Import lkmm_machine lkmm_coupled.
From iris_lkmm.logic Require Import graph_correspondence state_interp wp wp_rcu.
Import ListNotations.

Module WpRcuExamples.
  Import LkmmMachine LkmmCoupled RcuMatching LkmmGraphCorrespondence.
  Import LkmmStateInterp LkmmWp LkmmWpRcu.

  (** Administrative continuation steps use the existing silent-step rule. *)
  Local Lemma wp_resume `{!invGS Σ, !stateG Σ} P G γ E agent next ks regs index actions Φ :
    ▷ wp P G γ E agent
      (CoupledThreadView (ThreadView (ThreadState next ks regs) index
        (actions ++ [CoreSilent agent])) None) Φ -∗
    wp P G γ E agent
      (CoupledThreadView (ThreadView (ThreadState SSkip (KSeq next :: ks) regs)
        index actions) None) Φ.
  Proof.
    apply wp_lift_silent_step.
    { intros [[_ Hempty] _]. discriminate. }
    intros prefix s a suffix final s' [_ Hview] Hagent Hstep.
    pose proof (project_coupled_thread_lookup _ _ _ Hview) as Hlookup.
    revert Hagent. inversion Hstep as [m m' b action Hmachine |]; subst. intros Hagent.
    destruct Hmachine as
      [m core' action thread Hthread Hordinary Hready Hcore |
       m owner thread [Hthread Hstmt] Hready |
       m owner thread lock rest [Hthread Hstmt] Hready Hstack |
       m owner thread [Hthread Hstmt] Hready |
       m owner thread locks [Hthread Hstmt] Hpending Hclosed];
      simpl in Hagent; subst; cbn in Hlookup;
      try rewrite Hagent in Hthread;
      rewrite Hlookup in Hthread; injection Hthread as <-; try discriminate.
    inversion Hcore; subst; simplify_eq/=.
    split; first reflexivity.
    unfold project_coupled_thread, project_thread, coupled_position_to_core in *.
    cbn in Hview. rewrite Hlookup Hready in Hview. cbn in Hview.
    injection Hview as Hindex Hactions.
    cbn. rewrite lookup_insert_eq Hready flat_map_app filter_app /=.
    rewrite filter_cons_True; last done.
    unfold next_agent_index in Hindex |- *. cbn. by rewrite Hindex Hactions.
  Qed.

  Definition nested_graph := CoreCandidate {[
    0 := EAgent 0 0 (LBarrier BarrierRcuLock);
    1 := EAgent 0 1 (LBarrier BarrierRcuLock);
    2 := EAgent 0 2 (LBarrier BarrierRcuUnlock);
    3 := EAgent 0 3 (LBarrier BarrierRcuUnlock)
  ]} ∅ ∅ ∅ ∅ ∅ ∅.

  (** The view after unfolding the sequences of ((lock; lock); unlock); unlock. *)
  Definition nested_start := CoupledThreadView
    (ThreadView (ThreadState SRcuReadLock
      [KSeq SRcuReadLock; KSeq SRcuReadUnlock; KSeq SRcuReadUnlock] ∅) 0
      [CoreSilent 0; CoreSilent 0; CoreSilent 0]) None.

  Definition nested_program := CoreProgram ∅ {[0 :=
    SSeq (SSeq (SSeq SRcuReadLock SRcuReadLock) SRcuReadUnlock) SRcuReadUnlock]}.

  Definition nested_prefix := replicate 3 (CoupledMachineAction (Execute (CoreSilent 0))).

  Definition nested_prepared := CoupledState
    (with_core (initial_state nested_program) (update_thread (core_initial_state nested_program)
      0 nested_start.(coupled_view_core).(view_thread)))
    (initial_coupled nested_program).(coupled_builder).

  Example nested_start_reachable suffix final :
    coupled_run nested_program (initial_coupled nested_program) nested_prefix nested_prepared /\
    project_coupled_thread (CoupledExecutionPosition nested_prefix nested_prepared suffix final)
      0 = Some nested_start.
  Proof.
    split; last reflexivity.
    do 3 (econstructor; first (apply CoupledStepMachine; eapply StepCore;
      [reflexivity | done | reflexivity |]; eapply StepSequence; reflexivity)).
    constructor.
  Qed.

  Example nested_readers `{!invGS Σ, !stateG Σ} γ E (R : iProp Σ) :
    R -∗ wp nested_program nested_graph γ E 0 nested_start (fun v =>
      ⌜thread_complete v.(coupled_view_core).(view_thread) /\
        v.(coupled_view_core).(view_event_index) = 4⌝ ∗ R ∗
      event_fact γ 0 (EAgent 0 0 (LBarrier BarrierRcuLock)) ∗
      event_fact γ 1 (EAgent 0 1 (LBarrier BarrierRcuLock)) ∗
      event_fact γ 2 (EAgent 0 2 (LBarrier BarrierRcuUnlock)) ∗
      event_fact γ 3 (EAgent 0 3 (LBarrier BarrierRcuUnlock))).
  Proof.
    iIntros "HR". iApply (wp_read_lock _ _ _ _ _ _ 0); try reflexivity.
    iNext. iIntros "#Hlock0 Houter".
    iApply wp_resume. iNext.
    iApply (wp_read_lock _ _ _ _ _ _ 1); try reflexivity.
    iNext. iIntros "#Hlock1 Hinner".
    iApply wp_resume. iNext.
    iApply (wp_read_unlock _ _ _ _ _ _ 1 2 with "Hinner"); try reflexivity.
    { exists 0. vm_compute. by right; left. }
    iNext. iIntros "#Hunlock2".
    iApply wp_resume. iNext.
    iApply (wp_read_unlock _ _ _ _ _ _ 0 3 with "Houter"); try reflexivity.
    { exists 0. vm_compute. by left. }
    iNext. iIntros "#Hunlock3".
    rewrite wp_unfold /wp_body /rcu_next_view /=.
    iModIntro. iFrame "HR Hlock0 Hlock1 Hunlock2 Hunlock3". done.
  Qed.
End WpRcuExamples.
