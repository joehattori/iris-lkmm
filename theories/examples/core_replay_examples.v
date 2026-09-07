From Stdlib Require Import List Lia.
From stdpp Require Import gmap tactics list.
From iris_lkmm.lang Require Import core_agent_replay core_replay.
Import ListNotations.

Module CoreReplayExamples.
  Import LkmmCoreAgentReplay.

  Module Dependencies.
    Definition writer := SStore StoreOnce (EConst 0) (EConst 1).
    Definition program := CoreProgram {[0 := 0%Z]}
      {[0 := CoreDependencyTests.body; 1 := writer]}.
    Definition actions :=
      [CoreSilent 0; CoreEmit 1; CoreObserve 0 1%Z; CoreSilent 0; CoreSilent 0;
       CoreSilent 0; CoreSilent 0; CoreSilent 0; CoreSilent 0;
       CoreSilent 0; CoreEmit 0; CoreSilent 0; CoreSilent 0;
       CoreSilent 0; CoreEmit 0].
    Definition source_events : event_structure :=
      {[0 := EInitWrite 0 0%Z;
        1 := EAgent 1 0 (LMemory AccessWrite AccessOnce NotRmw 0 1%Z);
        2 := EAgent 0 0 (LMemory AccessRead AccessOnce NotRmw 0 1%Z);
        3 := EAgent 0 1 (LMemory AccessWrite AccessOnce NotRmw 0 1%Z);
        4 := EAgent 0 2 (LMemory AccessWrite AccessOnce NotRmw 0 0%Z)]}.

    Lemma source_run : exists final,
      complete_core_run program actions final /\
      final.(core_events) = source_events /\
      final.(core_direct_addr) = {[(2,3)]} /\
      final.(core_direct_data) = {[(2,3)]} /\
      final.(core_direct_ctrl) = {[(2,3)]}.
    Proof.
      eexists. split.
      - split.
        + eapply CoreRunCons. { eapply StepSequence; reflexivity. }
          eapply CoreRunCons. { eapply StepStore; try reflexivity. by eexists. }
          eapply CoreRunCons. { eapply StepLoad; try reflexivity. by eexists. }
          eapply CoreRunCons. { eapply StepSkipSequence; reflexivity. }
          eapply CoreRunCons. { eapply StepSequence; reflexivity. }
          eapply CoreRunCons. { eapply StepAssign; reflexivity. }
          eapply CoreRunCons. { eapply StepSkipSequence; reflexivity. }
          eapply CoreRunCons. { eapply StepSequence; reflexivity. }
          eapply CoreRunCons. { eapply StepIfTrue; try reflexivity; discriminate. }
          eapply CoreRunCons. { eapply StepIfTrue; try reflexivity; discriminate. }
          eapply CoreRunCons. { eapply StepStore; try reflexivity. by eexists. }
          eapply CoreRunCons. { eapply StepSkipControl; reflexivity. }
          eapply CoreRunCons. { eapply StepSkipControl; reflexivity. }
          eapply CoreRunCons. { eapply StepSkipSequence; reflexivity. }
          eapply CoreRunCons. { eapply StepStore; try reflexivity. by eexists. }
          constructor.
        + intros agent th Hlookup. destruct (decide (agent = 0)) as [-> | Hne0].
          * simpl in Hlookup. injection Hlookup as <-. done.
          * destruct (decide (agent = 1)) as [-> | Hne1].
            -- simpl in Hlookup. injection Hlookup as <-. done.
            -- simpl in Hlookup. simplify_map_eq.
      - split_and!; vm_compute; reflexivity.
    Qed.

    (** The interleaved writer disappears from the replay, and both dependency
        endpoints move: source [2 -> 3] becomes replay [1 -> 2]. *)
    Example replay_nested_control_and_dependencies : exists replayed,
      core_run program (core_initial_state program) (agent_actions 0 actions) replayed /\
      replayed.(core_direct_addr) = {[(1,2)]} /\
      replayed.(core_direct_data) = {[(1,2)]} /\
      replayed.(core_direct_ctrl) = {[(1,2)]} /\
      replayed.(core_threads) !! 1 = Some (initial_thread writer) /\
      (forall th, replayed.(core_threads) !! 0 = Some th -> thread_complete th).
    Proof.
      destruct source_run as (final & Hrun & Hevents & Haddr & Hdata & Hctrl).
      destruct (complete_core_run_replay_agent_initial _ _ _ 0 Hrun)
        as (replayed & Hreplayed & Hmatch & Hcomplete).
      exists replayed. split; first done.
      destruct Hmatch. rewrite Hevents, Haddr, Hdata, Hctrl in *.
      split_and!.
      - rewrite replay_addr0. vm_compute. reflexivity.
      - rewrite replay_data0. vm_compute. reflexivity.
      - rewrite replay_ctrl0. vm_compute. reflexivity.
      - rewrite replay_other_threads0 by lia. reflexivity.
      - exact Hcomplete.
    Qed.
  End Dependencies.

  Module ConditionalRmw.
    Definition writer := SStore StoreOnce (EConst 0) (EConst 1).
    Definition body := SSeq
      (SCmpxchg 0 RmwFull (EConst 0) (EConst 0) (EConst 1))
      (SSeq (SCmpxchg 1 RmwAcquire (EConst 0) (EConst 0) (EConst 2))
        (SStore StoreOnce (EBin OpAdd (EReg 1) (EConst (-1))) (EReg 1))).
    Definition program := CoreProgram {[0 := 0%Z]} {[0 := body; 1 := writer]}.
    Definition actions :=
      [CoreSilent 0; CoreObserve 0 0%Z; CoreEmit 1; CoreSilent 0;
       CoreSilent 0; CoreObserve 0 1%Z; CoreSilent 0; CoreEmit 0].
    Definition source_events : event_structure :=
      {[0 := EInitWrite 0 0%Z;
        1 := EAgent 0 0 (LMemory AccessRead AccessMb RmwMarked 0 0%Z);
        2 := EAgent 0 1 (LMemory AccessWrite AccessMb RmwMarked 0 1%Z);
        3 := EAgent 1 0 (LMemory AccessWrite AccessOnce NotRmw 0 1%Z);
        4 := EAgent 0 2 (LMemory AccessRead AccessAcquire RmwMarked 0 1%Z);
        5 := EAgent 0 3 (LMemory AccessWrite AccessOnce NotRmw 0 1%Z)]}.

    Lemma source_run : exists final,
      complete_core_run program actions final /\
      final.(core_events) = source_events /\
      final.(core_rmw) = {[(1,2)]} /\
      final.(core_direct_addr) = {[(4,5)]} /\
      final.(core_direct_data) = {[(4,5)]} /\
      final.(core_direct_ctrl) = {[(1,2)]}.
    Proof.
      eexists. split.
      - split.
        + eapply CoreRunCons. { eapply StepSequence; reflexivity. }
          eapply CoreRunCons. { eapply StepCmpxchgSuccess; try reflexivity. by eexists. }
          eapply CoreRunCons. { eapply StepStore; try reflexivity. by eexists. }
          eapply CoreRunCons. { eapply StepSkipSequence; reflexivity. }
          eapply CoreRunCons. { eapply StepSequence; reflexivity. }
          eapply CoreRunCons. { eapply StepCmpxchgFailure; try reflexivity;
            try discriminate. by eexists. }
          eapply CoreRunCons. { eapply StepSkipSequence; reflexivity. }
          eapply CoreRunCons. { eapply StepStore; try reflexivity. by eexists. }
          constructor.
        + intros agent th Hlookup. destruct (decide (agent = 0)) as [-> | Hne0].
          * simpl in Hlookup. injection Hlookup as <-. done.
          * destruct (decide (agent = 1)) as [-> | Hne1].
            -- simpl in Hlookup. injection Hlookup as <-. done.
            -- simpl in Hlookup. simplify_map_eq.
      - split_and!; vm_compute; reflexivity.
    Qed.

    Definition after_writer := add_single_event (core_initial_state program) 1
      (initial_thread writer) (LMemory AccessWrite AccessOnce NotRmw 0 1%Z) ∅ ∅ ∅ ∅.

    Lemma writer_step : core_step program (core_initial_state program) (CoreEmit 1) after_writer.
    Proof.
      unfold after_writer. eapply StepStore with (mode := StoreOnce)
        (address := EConst 0) (expression := EConst 1) (result := RegValue 1%Z ∅);
        try reflexivity. by eexists.
    Qed.

    (** Replay into a reachable nonempty context.  The successful pair moves
        from [1,2] to [2,3]; the failed read stays unpaired and feeds the store. *)
    Example replay_success_and_failure_after_another_agent : exists replayed,
      core_run program (core_initial_state program)
        (CoreEmit 1 :: agent_actions 0 actions) replayed /\
      replayed.(core_rmw) = {[(2,3)]} /\
      replayed.(core_direct_addr) = {[(4,5)]} /\
      replayed.(core_direct_data) = {[(4,5)]} /\
      replayed.(core_direct_ctrl) = {[(2,3)]} /\
      core_complete replayed.
    Proof.
      destruct source_run as (final & Hrun & Hevents & Hrmw & Haddr & Hdata & Hctrl).
      pose proof (core_step_preserves_allocation _ _ _ _ writer_step
        (core_initial_allocation_wf program)) as Hbase.
      destruct (complete_core_run_replay_agent _ _ _ 0 after_writer Hrun Hbase
        eq_refl eq_refl) as (replayed & Hreplayed & Hmatch & Hcomplete).
      exists replayed. split.
      - econstructor; [exact writer_step | exact Hreplayed].
      - destruct Hmatch. rewrite Hevents, Hrmw, Haddr, Hdata, Hctrl in *.
        split_and!.
        + rewrite replay_rmw0. vm_compute. reflexivity.
        + rewrite replay_addr0. vm_compute. reflexivity.
        + rewrite replay_data0. vm_compute. reflexivity.
        + rewrite replay_ctrl0. vm_compute. reflexivity.
        + intros agent th Hlookup. destruct (decide (agent = 0)) as [-> | Hne0].
          * by apply Hcomplete.
          * rewrite replay_other_threads0 in Hlookup by done.
            destruct (decide (agent = 1)) as [-> | Hne1].
            -- simpl in Hlookup. injection Hlookup as <-. done.
            -- simpl in Hlookup. simplify_map_eq.
    Qed.
  End ConditionalRmw.

  Module WholeProgram.
    Import LkmmCoreReplay.

    Lemma dependency_agent_orders :
      program_agent_enumeration Dependencies.program [0;1] /\
      program_agent_enumeration Dependencies.program [1;0].
    Proof.
      split; split.
      - repeat constructor; set_solver.
      - intros t. unfold Dependencies.program. simpl.
        rewrite !lookup_insert_is_Some, lookup_singleton_is_Some. simpl. set_solver.
      - repeat constructor; set_solver.
      - intros t. unfold Dependencies.program. simpl.
        rewrite !lookup_insert_is_Some, lookup_singleton_is_Some. simpl. set_solver.
    Qed.

    (** Both choices of first agent terminate, including the writer that a
        single-agent replay intentionally left at its initial instruction. *)
    Example all_agents_complete_in_either_order :
      exists source,
        complete_core_run Dependencies.program Dependencies.actions source /\
        (exists final f, complete_core_run Dependencies.program
          (serial_actions [0;1] Dependencies.actions) final /\ core_state_renaming f source final) /\
        (exists final f, complete_core_run Dependencies.program
          (serial_actions [1;0] Dependencies.actions) final /\ core_state_renaming f source final).
    Proof.
      destruct Dependencies.source_run as (source & Hsource & _).
      exists source. split; first done.
      destruct dependency_agent_orders as [H01 H10]. split.
      - destruct (complete_core_run_replay_order _ _ _ _ Hsource H01)
          as (final & f & Hrun & Hcertificate & Hrename). by exists final, f.
      - destruct (complete_core_run_replay_order _ _ _ _ Hsource H10)
          as (final & f & Hrun & Hcertificate & Hrename). by exists final, f.
    Qed.

    Example all_conditional_rmw_agents_complete :
      exists source final f,
        complete_core_run ConditionalRmw.program ConditionalRmw.actions source /\
        complete_core_run ConditionalRmw.program
          (serial_actions (program_agents_list ConditionalRmw.program) ConditionalRmw.actions) final /\
        core_state_renaming f source final.
    Proof.
      destruct ConditionalRmw.source_run as (source & Hsource & _).
      destruct (complete_core_run_replay _ _ _ Hsource)
        as (final & f & Hrun & Hcertificate & Hrename).
      by exists source, final, f.
    Qed.

    Example empty_program_replays :
      exists final, complete_core_run (CoreProgram ∅ ∅)
        (serial_actions (program_agents_list (CoreProgram ∅ ∅)) []) final.
    Proof.
      assert (complete_core_run (CoreProgram ∅ ∅) [] (core_initial_state (CoreProgram ∅ ∅)))
        as Hsource.
      { split; first constructor. intros t th Hlookup. discriminate Hlookup. }
      destruct (complete_core_run_replay _ _ _ Hsource) as (final & f & Hrun & Hcertificate & Hrename).
      by exists final.
    Qed.
  End WholeProgram.
End CoreReplayExamples.
