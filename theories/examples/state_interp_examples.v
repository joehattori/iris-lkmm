From Stdlib Require Import List Lia.
From stdpp Require Import gmap tactics.
From iris.base_logic.lib Require Import iprop.
From iris.proofmode Require Import proofmode.
From iris_lkmm.operational Require Import lkmm_machine lkmm_coupled.
From iris_lkmm.logic Require Import rcu_ghost state_interp.
From iris_lkmm.examples Require Import graph_domain_examples graph_correspondence_examples.
Import ListNotations.

Module StateInterpExamples.
  Import LkmmMachine LkmmCoupled RcuGhost LkmmStateInterp.
  Module GP := GraphCorrespondenceExamples.GpState.

  Module SilentAssignment.
    Definition body := SAssign 0 (EConst 42%Z).
    Definition program := CoreProgram {[3 := 7%Z]} {[0 := body; 1 := SSynchronizeRcu]}.
    Definition after_thread := ThreadState SSkip [] {[0 := RegValue 42%Z ∅]}.
    Definition after := CoupledState
      (with_core (initial_state program) (update_thread (core_initial_state program) 0 after_thread))
      (initial_coupled program).(coupled_builder).

    Lemma silent_step :
      coupled_step program (initial_coupled program)
        (CoupledMachineAction (Execute (CoreSilent 0))) after.
    Proof.
      apply CoupledStepMachine. eapply StepCore with (thread := initial_thread body).
      - reflexivity.
      - done.
      - reflexivity.
      - eapply StepAssign with (thread := initial_thread body) (dst := 0)
          (expression := EConst 42%Z) (result := RegValue 42%Z ∅); reflexivity.
    Qed.

    Example assignment_preserves_other_resources `{!stateG Σ} :
      ⊢ |==> ∃ γ, state_interp (Σ := Σ) γ after ∗ thread_token γ 0 after_thread ∗
        thread_token γ 1 (initial_thread SSynchronizeRcu) ∗
        event_fact γ 0 (EInitWrite 3 7%Z) ∗ event_fact γ 0 (EInitWrite 3 7%Z).
    Proof.
      iMod (state_interp_alloc program) as (γ) "(Hstate & Hthreads & #Hfacts)".
      iDestruct (big_sepM_delete _ _ 0 with "Hthreads") as "[H0 Hthreads]"; first reflexivity.
      iDestruct (big_sepM_delete _ _ 1 with "Hthreads") as "[H1 _]"; first reflexivity.
      iDestruct (big_sepM_lookup _ _ 0 with "Hfacts") as "#Hinit"; first reflexivity.
      iMod (state_interp_silent_step program γ (initial_coupled program) 0 after _ after_thread
        with "[$Hstate $H0]") as "[Hstate H0]".
      { apply silent_step. }
      { reflexivity. }
      iModIntro. iExists γ. iFrame "Hstate H0 H1 Hinit".
    Qed.
  End SilentAssignment.

  Module RmwEmission.
    Definition body := SXchg 0 RmwRelaxed (EConst 0) (EConst 1).
    Definition program := CoreProgram {[0 := 0%Z]} {[0 := body]}.
    Definition result_regs observed : registers := {[0 := RegValue observed {[1]}]}.
    Definition after observed := CoupledState
      (with_core (initial_state program)
        (add_rmw_events (core_initial_state program) 0 (initial_thread body)
          AccessOnce 0 observed 1%Z (result_regs observed) ∅ ∅ ∅))
      (initial_coupled program).(coupled_builder).

    Example exchange_allocates_both_event_facts `{!stateG Σ} observed :
      ⊢ |==> ∃ γ, state_interp (Σ := Σ) γ (after observed) ∗
        thread_token γ 0 (emitted_thread (initial_thread body) (result_regs observed)) ∗
        event_fact γ 0 (EInitWrite 0 0%Z) ∗
        event_fact γ 1 (EAgent 0 0 (LMemory AccessRead AccessOnce RmwMarked 0 observed)) ∗
        event_fact γ 2 (EAgent 0 1 (LMemory AccessWrite AccessOnce RmwMarked 0 1%Z)).
    Proof.
      assert (coupled_step program (initial_coupled program)
        (CoupledMachineAction (Execute (CoreObserve 0 observed))) (after observed)) as Hstep.
      { apply CoupledStepMachine. eapply StepCore; [reflexivity | done | reflexivity |].
        eapply StepXchg with (dst := 0) (mode := RmwRelaxed) (address := EConst 0)
          (expression := EConst 1) (result := RegValue 1%Z ∅); try reflexivity.
        by eexists. }
      iMod (state_interp_alloc program) as (γ) "(Hstate & Hthreads & #Hfacts)".
      iDestruct (big_sepM_lookup _ _ 0 with "Hthreads") as "Hthread"; first reflexivity.
      iDestruct (big_sepM_lookup _ _ 0 with "Hfacts") as "#Hinit"; first reflexivity.
      iMod (state_interp_execute _ _ _ _ _ _ _ Hstep with "[$Hstate $Hthread]")
        as "(Hstate & Hthread & #Hnew)".
      { apply core_initial_allocation_wf. }
      { reflexivity. }
      iDestruct (big_sepM_lookup _ _ 1 with "Hnew") as "#Hread"; first reflexivity.
      iDestruct (big_sepM_lookup _ _ 2 with "Hnew") as "#Hwrite"; first reflexivity.
      iModIntro. iExists γ. iFrame "Hstate Hthread Hinit Hread Hwrite".
    Qed.
  End RmwEmission.

  Module NestedReaders.
    Definition program := CoreProgram ∅
      {[0 := SSeq SRcuReadLock (SSeq SRcuReadLock (SSeq SRcuReadUnlock SRcuReadUnlock))]}.

    Example inner_unlock_preserves_outer_token `{!stateG Σ} :
      ⊢ |==> ∃ γ s, state_interp (Σ := Σ) γ s ∗
        thread_token γ 0 (ThreadState SSkip [KSeq SRcuReadUnlock] ∅) ∗
        reader_token γ.(rcu_name) 0 ∗
        event_fact γ 0 (EAgent 0 0 (LBarrier BarrierRcuLock)) ∗
        event_fact γ 1 (EAgent 0 1 (LBarrier BarrierRcuLock)) ∗
        event_fact γ 2 (EAgent 0 2 (LBarrier BarrierRcuUnlock)) ∗
        ⌜open_readers s.(coupled_machine) 0 = [0]⌝.
    Proof.
      iMod (state_interp_alloc program) as (γ) "(Hstate & Hthreads & _)".
      iDestruct (big_sepM_lookup _ _ 0 with "Hthreads") as "Hthread"; first reflexivity.
      iMod (state_interp_silent_step program γ _ 0 _ _ _ with "[$Hstate $Hthread]")
        as "[Hstate Hthread]".
      { apply CoupledStepMachine. eapply StepCore; [reflexivity | done | reflexivity |].
        eapply StepSequence; reflexivity. }
      { reflexivity. }
      iMod (state_interp_read_lock program γ _ 0 _ _ with "[$Hstate $Hthread]")
        as "(Hstate & Hthread & #Hlock0 & Hreader0)".
      { apply CoupledStepMachine. eapply StepReadLock; [split; reflexivity | reflexivity]. }
      { change (core_allocation_wf (core_initial_state program)). apply core_initial_allocation_wf. }
      iMod (state_interp_silent_step program γ _ 0 _ _ _ with "[$Hstate $Hthread]")
        as "[Hstate Hthread]".
      { apply CoupledStepMachine. eapply StepCore; [reflexivity | done | reflexivity |].
        eapply StepSkipSequence; reflexivity. }
      { reflexivity. }
      iMod (state_interp_silent_step program γ _ 0 _ _ _ with "[$Hstate $Hthread]")
        as "[Hstate Hthread]".
      { apply CoupledStepMachine. eapply StepCore; [reflexivity | done | reflexivity |].
        eapply StepSequence; reflexivity. }
      { reflexivity. }
      iMod (state_interp_read_lock program γ _ 0 _ _ with "[$Hstate $Hthread]")
        as "(Hstate & Hthread & #Hlock1 & Hreader1)".
      { apply CoupledStepMachine. eapply StepReadLock; [split; reflexivity | reflexivity]. }
      { change (core_allocation_wf (add_single_event (core_initial_state program) 0
          (initial_thread SRcuReadLock) (LBarrier BarrierRcuLock) ∅ ∅ ∅ ∅)).
        apply add_single_event_allocation_wf, core_initial_allocation_wf. }
      iMod (state_interp_silent_step program γ _ 0 _ _ _ with "[$Hstate $Hthread]")
        as "[Hstate Hthread]".
      { apply CoupledStepMachine. eapply StepCore; [reflexivity | done | reflexivity |].
        eapply StepSkipSequence; reflexivity. }
      { reflexivity. }
      iMod (state_interp_silent_step program γ _ 0 _ _ _ with "[$Hstate $Hthread]")
        as "[Hstate Hthread]".
      { apply CoupledStepMachine. eapply StepCore; [reflexivity | done | reflexivity |].
        eapply StepSequence; reflexivity. }
      { reflexivity. }
      iMod (state_interp_read_unlock program γ _ 0 _ _ 1 [0] with "[$Hstate $Hthread $Hreader1]")
        as "(Hstate & Hthread & #Hunlock1)".
      { apply CoupledStepMachine. eapply StepReadUnlock; [split; reflexivity | reflexivity | reflexivity]. }
      { change (core_allocation_wf (add_single_event
          (add_single_event (core_initial_state program) 0
            (initial_thread SRcuReadLock) (LBarrier BarrierRcuLock) ∅ ∅ ∅ ∅) 0
          (initial_thread SRcuReadLock) (LBarrier BarrierRcuLock) ∅ ∅ ∅ ∅)).
        apply add_single_event_allocation_wf, add_single_event_allocation_wf,
          core_initial_allocation_wf. }
      { reflexivity. }
      iModIntro. iExists γ, _. iFrame "Hstate Hthread Hreader0 Hlock0 Hlock1 Hunlock1".
      by iPureIntro.
    Qed.
  End NestedReaders.

  Local Lemma waiting_pending gid captured :
    pending_gp_at GP.waiting.(coupled_machine) gid captured <->
    gid = gp_identity 0 0 /\ captured = ∅.
  Proof.
    split.
    - intros (agent & locks & Hlookup & Hgid & Hcaptured).
      change (({[0 := []]} : gmap agent_id (list event_id)) !! agent = Some locks) in Hlookup.
      apply lookup_singleton_Some in Hlookup as [<- <-]. done.
    - intros [-> ->]. exists 0, []. split_and!; reflexivity.
  Qed.

  Local Lemma finished_completed gid captured :
    completed_gp_at GP.finished.(coupled_machine) gid captured <->
    gid = gp_identity 0 0 /\ captured = ∅.
  Proof.
    split.
    - intros (cert & agent & index & Hcert & Hlookup & Hgid & Hcaptured).
      change (In cert [GpCertificate 0 []]) in Hcert. destruct Hcert as [<- | []].
      change (Some (EAgent 0 0 (LBarrier BarrierSyncRcu)) =
        Some (EAgent agent index (LBarrier BarrierSyncRcu))) in Hlookup.
      simplify_eq. done.
    - intros [-> ->]. exists (GpCertificate 0 []), 0, 0.
      split; first by left. split_and!; reflexivity.
  Qed.

  Example waiting_protocol_matches :
    rcu_state_matches GP.waiting.(coupled_machine)
      {[gp_identity 0 0 := GpPending ∅ 0]}.
  Proof.
    split.
    - intros gid captured. rewrite waiting_pending. split.
      + intros [-> ->]. exists 0. apply lookup_singleton_eq.
      + intros (start & Hlookup). apply lookup_singleton_Some in Hlookup.
        naive_solver.
    - split.
      + intros gid captured. split.
        * intros (cert & agent & index & Hcert & _). inversion Hcert.
        * intros (start & finish & Hlookup). apply lookup_singleton_Some in Hlookup.
          naive_solver.
      + intros gid status Hlookup. apply lookup_singleton_Some in Hlookup as [_ <-].
        simpl. lia.
  Qed.

  Example finished_protocol_matches :
    rcu_state_matches GP.finished.(coupled_machine)
      {[gp_identity 0 0 := GpDone ∅ 0 1]}.
  Proof.
    split.
    - intros gid captured. split.
      + intros (agent & locks & Hlookup & _).
        change ((∅ : gmap agent_id (list event_id)) !! agent = Some locks) in Hlookup.
        by rewrite lookup_empty in Hlookup.
      + intros (start & Hlookup). apply lookup_singleton_Some in Hlookup. naive_solver.
    - split.
      + intros gid captured. rewrite finished_completed. split.
        * intros [-> ->]. exists 0, 1. apply lookup_singleton_eq.
        * intros (start & finish & Hlookup). apply lookup_singleton_Some in Hlookup.
          naive_solver.
      + intros gid status Hlookup. apply lookup_singleton_Some in Hlookup as [_ <-].
        simpl. lia.
  Qed.

  (** An unchanged Core state does not allow us to omit the begun GP. *)
  Example begin_requires_pending_entry :
    GP.before.(coupled_machine).(machine_core) = GP.waiting.(coupled_machine).(machine_core) /\
    ~ rcu_state_matches GP.waiting.(coupled_machine) ∅.
  Proof.
    split; first reflexivity. intros [Hpending _].
    destruct (proj1 (Hpending (gp_identity 0 0) ∅)) as (start & Hlookup).
    - apply waiting_pending. done.
    - by rewrite lookup_empty in Hlookup.
  Qed.

  (** A permitted future source does not yet supply an emitted-event fact. *)
  Example future_source_has_no_event_fact `{!stateG Σ} γ b :
    ⊢ state_interp (Σ := Σ) γ (CoupledState
      (State GraphDomainExamples.FutureSource.after_read ∅ []) b) -∗
    event_fact γ 2 (EAgent 0 0 (LMemory AccessWrite AccessOnce NotRmw 0 1%Z)) -∗ False.
  Proof.
    iIntros "Hstate Hevent".
    iDestruct (state_interp_event with "Hstate Hevent") as %Hlookup.
    discriminate Hlookup.
  Qed.
End StateInterpExamples.
