From Stdlib Require Import List.
From stdpp Require Import gmap tactics.
From iris_lkmm.operational Require Import core_to_machine.
Import ListNotations.

Module CoreToMachineExamples.
  Import LkmmCoreToMachine.

  Definition body := SSeq SRcuReadLock (SSeq SRcuReadLock
    (SSeq (SXchg 0 RmwRelaxed (EConst 0) (EConst 1))
      (SSeq SRcuReadUnlock (SSeq SRcuReadUnlock (SSeq SSynchronizeRcu SSynchronizeRcu))))).
  Definition program := CoreProgram {[0 := 0%Z]} {[0 := body]}.
  Definition actions := [
    CoreSilent 0; CoreEmit 0; CoreSilent 0;
    CoreSilent 0; CoreEmit 0; CoreSilent 0;
    CoreSilent 0; CoreObserve 0 0%Z; CoreSilent 0;
    CoreSilent 0; CoreEmit 0; CoreSilent 0;
    CoreSilent 0; CoreEmit 0; CoreSilent 0;
    CoreSilent 0; CoreEmit 0; CoreSilent 0; CoreEmit 0
  ].

  Local Ltac solve_core_step :=
    first [solve [eapply StepSequence; reflexivity]
      | solve [eapply StepSkipSequence; reflexivity]
      | solve [eapply StepRcuReadLock; reflexivity]
      | solve [eapply StepRcuReadUnlock; reflexivity]
      | solve [eapply StepSynchronizeRcu; reflexivity]
      | solve [eapply StepXchg with (dst := 0) (mode := RmwRelaxed)
          (result := RegValue 1%Z ∅) (address_sources := ∅);
          try reflexivity; by eexists]].

  Local Ltac solve_guards :=
    intros thread Hthread; cbn in Hthread; injection Hthread as <-;
    split; intros Hstmt; try discriminate; vm_compute; congruence.

  Local Ltac normalize_core :=
    lazymatch goal with
    | |- core_run_rcu_guards ?P ?s ?actions ?final =>
        let reduced := (eval vm_compute in s) in
        change (core_run_rcu_guards P reduced actions final)
    end.

  Local Lemma guarded_source : exists final,
    core_run_rcu_guards program (core_initial_state program) actions final /\
    core_complete final /\ rcu_matching_complete final.(core_events) /\
    final.(core_rmw) = {[(3,4)]} /\
    final.(core_threads) !! 0 = Some (ThreadState SSkip [] {[0 := RegValue 0%Z {[3]}]}).
  Proof.
    eexists. split.
    - unfold actions.
      repeat (eapply CoreRunRcuGuardsCons; [solve_core_step | solve_guards | normalize_core]).
      constructor.
    - split.
      + intros agent thread Hlookup.
        change (({[0 := ThreadState SSkip [] {[0 := RegValue 0%Z {[3]}]}]} :
          gmap agent_id thread_state) !! agent = Some thread) in Hlookup.
        apply lookup_singleton_Some in Hlookup as [-> <-]. done.
      + split_and!; vm_compute; done.
  Qed.

  (** A two-event RMW and its register provenance survive the lifting
      exactly, through nested sections and two successive synchronizations. *)
  Example nested_rmw_and_repeated_gp_lift : exists final machine_actions s,
    complete_core_run program actions final /\ complete_run program machine_actions s /\
    s.(machine_core) = final /\ project_actions machine_actions = actions /\
    s.(machine_core).(core_rmw) = {[(3,4)]} /\
    s.(machine_core).(core_threads) !! 0 =
      Some (ThreadState SSkip [] {[0 := RegValue 0%Z {[3]}]}).
  Proof.
    destruct guarded_source as (final & Hguards & Hcomplete & Hmatching & Hrmw & Hregister).
    assert (complete_core_run program actions final) as Hcore.
    { split; [by apply core_run_rcu_guards_run | done]. }
    destruct (complete_core_run_machine_lift _ _ _ Hcore Hguards Hmatching)
      as (machine_actions & s & Hrun & Hfinal & Hproject).
    exists final, machine_actions, s. split; first done. split; first done.
    split; first done. split; first done. by rewrite Hfinal.
  Qed.

  (** Guarded execution alone need not close its final reader stack. *)
  Definition open_program := CoreProgram ∅ {[0 := SRcuReadLock]}.
  Definition open_final := add_single_event (core_initial_state open_program) 0
    (initial_thread SRcuReadLock) (LBarrier BarrierRcuLock) ∅ ∅ ∅ ∅.

  Example final_matching_is_needed :
    complete_core_run open_program [CoreEmit 0] open_final /\
    core_run_rcu_guards open_program (core_initial_state open_program) [CoreEmit 0] open_final /\
    ~ rcu_matching_complete open_final.(core_events).
  Proof.
    assert (core_run_rcu_guards open_program (core_initial_state open_program)
      [CoreEmit 0] open_final) as Hguards.
    { econstructor; [by eapply StepRcuReadLock | solve_guards | constructor]. }
    split; last (split; first done; intros [Hlocks _]; discriminate Hlocks).
    split; first by apply core_run_rcu_guards_run.
    intros agent thread Hlookup. destruct (decide (agent = 0)) as [-> | Hother].
    - cbn in Hlookup. injection Hlookup as <-. done.
    - cbn in Hlookup. simplify_map_eq.
  Qed.
End CoreToMachineExamples.
