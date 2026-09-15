From Stdlib Require Import List.
From iris.base_logic.lib Require Import fancy_updates.
From iris.proofmode Require Import proofmode.
From iris_lkmm.lkmm Require Import rcu_matching.
From iris_lkmm.operational Require Import lkmm_machine lkmm_coupled.
From iris_lkmm.logic Require Import graph_correspondence rcu_ghost state_interp wp wp_rcu.
Import ListNotations.

Module WpRcuExamples.
  Import LkmmMachine LkmmCoupled RcuMatching LkmmGraphCorrespondence.
  Import RcuGhost LkmmStateInterp LkmmWp LkmmWpRcu.

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

  Definition nested_body :=
    SSeq (SSeq (SSeq SRcuReadLock SRcuReadLock) SRcuReadUnlock) SRcuReadUnlock.

  Definition nested_program := CoreProgram ∅ {[0 := nested_body]}.

  Definition nested_initial_view := CoupledThreadView
    (ThreadView (initial_thread nested_body) 0 []) None.

  Definition nested_prefix := replicate 3 (CoupledMachineAction (Execute (CoreSilent 0))).

  Definition nested_prepared := CoupledState
    (with_core (initial_state nested_program) (update_thread (core_initial_state nested_program)
      0 nested_start.(coupled_view_core).(view_thread)))
    (initial_coupled nested_program).(coupled_builder).

  Example nested_start_reachable suffix final :
    coupled_run nested_program (initial_coupled nested_program) nested_prefix nested_prepared /\
    lookup_coupled_thread_view (CoupledExecutionPosition nested_prefix nested_prepared suffix final)
      0 = Some nested_start.
  Proof.
    split; last reflexivity.
    do 3 (econstructor; first (apply CoupledStepMachine; eapply StepCore;
      [reflexivity | done | reflexivity |]; eapply StepSequence; reflexivity)).
    constructor.
  Qed.

  Example nested_readers `{!invGS Σ, !stateG Σ} γ E (R : iProp Σ) :
    R -∗ wp nested_program nested_graph γ E 0 nested_initial_view (fun v =>
      ⌜thread_complete v.(coupled_view_core).(view_thread) /\
        v.(coupled_view_core).(view_event_index) = 4 /\
        length v.(coupled_view_core).(view_actions) = 10⌝ ∗ R ∗
      event_fact γ 0 (EAgent 0 0 (LBarrier BarrierRcuLock)) ∗
      event_fact γ 1 (EAgent 0 1 (LBarrier BarrierRcuLock)) ∗
      event_fact γ 2 (EAgent 0 2 (LBarrier BarrierRcuUnlock)) ∗
      event_fact γ 3 (EAgent 0 3 (LBarrier BarrierRcuUnlock))).
  Proof.
    iIntros "HR".
    do 3 (iApply wp_seq; iNext).
    iApply (wp_read_lock _ _ _ _ _ _ 0); try reflexivity.
    iNext. iIntros "#Hlock0 Houter".
    iApply wp_skip_seq. iNext.
    iApply (wp_read_lock _ _ _ _ _ _ 1); try reflexivity.
    iNext. iIntros "#Hlock1 Hinner".
    iApply wp_skip_seq. iNext.
    iApply (wp_read_unlock _ _ _ _ _ _ 1 2 with "Hinner"); try reflexivity.
    { exists 0. vm_compute. by right; left. }
    iNext. iIntros "#Hunlock2".
    iApply wp_skip_seq. iNext.
    iApply (wp_read_unlock _ _ _ _ _ _ 0 3 with "Houter"); try reflexivity.
    { exists 0. vm_compute. by left. }
    iNext. iIntros "#Hunlock3".
    rewrite wp_unfold /wp_body /rcu_next_view /=.
    iModIntro. iFrame "HR Hlock0 Hlock1 Hunlock2 Hunlock3". done.
  Qed.

  Definition sync_start index actions regs := CoupledThreadView
    (ThreadView (ThreadState SSynchronizeRcu [] regs) index actions) None.

  (** The captured snapshot is supplied by begin and preserved by finish.
      The same proof handles empty and nonempty snapshots, arbitrary prior
      histories, and completion epochs advanced by other agents. *)
  Example synchronize_records_completion `{!invGS Σ, !stateG Σ}
      P G γ E agent index actions regs sync (R : iProp Σ) :
    lookup_event G.(candidate_events) sync =
      Some (EAgent agent index (LBarrier BarrierSyncRcu)) ->
    R -∗ wp P G γ E agent (sync_start index actions regs) (fun v =>
      ⌜v = CoupledThreadView (ThreadView (ThreadState SSkip [] regs)
        (S index) (actions ++ [CoreEmit agent])) None⌝ ∗ R ∗
      event_fact γ sync (EAgent agent index (LBarrier BarrierSyncRcu)) ∗
      ∃ locks start finish,
        gp_done γ.(rcu_name) (gp_encoding agent index) (list_to_set locks) start finish ∗
        gp_done γ.(rcu_name) (gp_encoding agent index) (list_to_set locks) start finish).
  Proof.
    intros Hevent. iIntros "HR". iApply wp_begin_gp; try reflexivity.
    iNext. iIntros (locks start) "Hpending".
    iApply (wp_finish_gp P G γ E agent (gp_wait_view (sync_start index actions regs) locks)
      locks start sync with "Hpending"); try done.
    iNext. iIntros (finish) "#Hsync #Hdone".
    rewrite wp_unfold /wp_body /rcu_next_view /gp_wait_view /sync_start /=.
    iModIntro. iSplit; first done. iFrame "HR Hsync".
    iExists locks, start, finish. iFrame "Hdone".
  Qed.
End WpRcuExamples.
