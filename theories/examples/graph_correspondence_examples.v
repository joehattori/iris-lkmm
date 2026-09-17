From Stdlib Require Import List Lia.
From stdpp Require Import gmap tactics.
From iris.base_logic.lib Require Import iprop.
From iris.proofmode Require Import proofmode.
From iris_lkmm.lkmm Require Import event_renaming memory_relations rcu_graph.
From iris_lkmm.lang Require Import program_graph candidate_renaming.
From iris_lkmm.operational Require Import lkmm_machine lkmm_operational
  rcu_builder rcu_candidate candidate_encoding.
From iris_lkmm.logic Require Import lkmm_graph_judgment.
From iris_lkmm.examples Require Import graph_domain_examples candidate_renaming_examples.
Import ListNotations.

Module GraphCorrespondenceExamples.
  Import LkmmOperationalGraphJudgment LkmmMachine RcuBuilder RcuCandidate RcuGraph
    LkmmCandidateEncoding LkmmCandidateRenaming EventRenaming LkmmMemoryRelations.
  Module Future := GraphDomainExamples.FutureSource.
  Module Sample := LkmmProgramGraph.ProgramGraphTests.
  Module Renaming := CandidateRenamingExamples.

  (** Keep the exact read-before-write machine trace, then let the existing
      builder scheduler supply the commitment suffix. *)
  Lemma future_source_lkmm_cut : exists suffix b,
    let current := LkmmState (State Future.after_read ∅ []) initial_builder in
    let final := LkmmState (State Future.final ∅ []) b in
    lkmm_position Sample.program Future.candidate
      (LkmmExecutionPosition [LkmmMachineAction (Execute (CoreObserve 1 1%Z))]
        current (LkmmMachineAction (Execute (CoreEmit 0)) :: suffix) final).
  Proof.
    assert (LkmmMachine.step Sample.program (initial_state Sample.program)
      (Execute (CoreObserve 1 1%Z)) (State Future.after_read ∅ [])) as Hread.
    { eapply StepCore; [reflexivity | done | reflexivity |].
      eapply StepLoad with (dst := 0) (mode := LoadOnce) (address_sources := ∅);
        try reflexivity. by eexists. }
    assert (LkmmMachine.step Sample.program (State Future.after_read ∅ [])
      (Execute (CoreEmit 0)) (State Future.final ∅ [])) as Hwrite.
    { eapply StepCore; [reflexivity | done | reflexivity |].
      eapply StepStore with (mode := StoreOnce) (result := RegValue 1%Z ∅)
        (address_sources := ∅); try reflexivity. by eexists. }
    pose proof (program_graph_wf _ _ Future.graph) as Hwf.
    destruct (consistent_candidate_is_incrementally_schedulable
      (finite_candidate_of_core Future.candidate) (finite_candidate_of_core_wf _ Hwf))
      as (b & Hbuilder & Hraw & _).
    { rewrite finite_candidate_of_core_graph. exact Future.consistent. }
    assert (generated_prefix (State Future.final ∅ []) b.(bs_raw)) as Hgenerated.
    { rewrite Hraw finite_candidate_of_core_raw. unfold generated_prefix. cbn.
      split_and!; try done. intros eid ev Hlookup. done. }
    destruct (lift_builder_run Sample.program _ _ _ Hbuilder Hgenerated) as (suffix & Hsuffix).
    assert (lkmm_candidate (LkmmState (State Future.final ∅ []) b) = Future.candidate) as HG.
    { unfold lkmm_candidate. cbn. rewrite Hraw finite_candidate_of_core_raw. reflexivity. }
    exists suffix, b. split.
    - econstructor; last constructor. by apply LkmmStepMachine.
    - split.
      + econstructor; last done. by apply LkmmStepMachine.
      + split.
        * split.
          -- split.
             ++ exact (proj2 (proj1 Future.execution)).
             ++ split; first reflexivity. split; reflexivity.
          -- unfold machine_matches_raw. cbn. rewrite Hraw finite_candidate_of_core_raw.
             split_and!; reflexivity.
        * split; last done. unfold lkmm_program_graph_obligations. rewrite HG.
          destruct Hwf as (_ & Hrf & Hco & _). done.
  Qed.

  Example exact_future_source_projection : exists p,
    lkmm_position Sample.program Future.candidate p /\
    candidate_position Sample.program Future.candidate (lkmm_position_to_core p) /\
    (lkmm_position_to_core p).(position_prefix) = [CoreObserve 1 1%Z] /\
    (lkmm_position_to_core p).(position_state) = Future.after_read /\
    lookup_event (lkmm_position_to_core p).(position_state).(core_events) 2 = None /\
    rf Future.candidate.(candidate_rf) 2 1.
  Proof.
    destruct future_source_lkmm_cut as (suffix & b & Hpos).
    eexists. split; first exact Hpos. split; first by apply lkmm_position_projection.
    split; first reflexivity. split; first reflexivity. split; first reflexivity. set_solver.
  Qed.

  Example every_cut_of_that_trace_is_covered : exists suffix final,
    lkmm_run Sample.program (initial_lkmm Sample.program)
      ([LkmmMachineAction (Execute (CoreObserve 1 1%Z));
        LkmmMachineAction (Execute (CoreEmit 0))] ++ suffix) final /\
    forall prefix rest,
      prefix ++ rest = [LkmmMachineAction (Execute (CoreObserve 1 1%Z));
        LkmmMachineAction (Execute (CoreEmit 0))] ++ suffix ->
      exists current, candidate_position Sample.program (lkmm_candidate final)
        (lkmm_position_to_core (LkmmExecutionPosition prefix current rest final)).
  Proof.
    destruct future_source_lkmm_cut as (suffix & b & Hpos).
    pose proof (lkmm_position_run _ _ _ Hpos) as Hrun.
    change (lkmm_run Sample.program (initial_lkmm Sample.program)
      ([LkmmMachineAction (Execute (CoreObserve 1 1%Z));
        LkmmMachineAction (Execute (CoreEmit 0))] ++ suffix)
      (LkmmState (State Future.final ∅ []) b)) in Hrun.
    destruct Hpos as (_ & _ & Hcomplete & Hobligations & _).
    exists suffix, (LkmmState (State Future.final ∅ []) b). split; first exact Hrun.
    intros prefix rest Hsplit. rewrite <- Hsplit in Hrun.
    destruct (lkmm_run_positions _ _ _ _ Hrun Hcomplete Hobligations) as (current & _ & Hcore).
    by exists current.
  Qed.

  Example projection_retains_silent_steps :
    lkmm_core_actions [LkmmBuilderAction;
      LkmmMachineAction (Execute (CoreSilent 0));
      LkmmMachineAction (BeginGp 1);
      LkmmMachineAction (FinishGp 1)] = [CoreSilent 0; CoreEmit 1].
  Proof. reflexivity. Qed.

  Module GpState.
    Definition program := CoreProgram ∅ {[0 := SSynchronizeRcu]}.
    Definition before := initial_lkmm program.
    Definition waiting := LkmmState (begin_gp (initial_state program) 0) initial_builder.
    Definition finished := LkmmState
      (finish_gp (begin_gp (initial_state program) 0) 0 (initial_thread SSynchronizeRcu) [])
      initial_builder.

    Example begin_changes_state_without_a_core_action :
      lkmm_step program before (LkmmMachineAction (BeginGp 0)) waiting /\
      lkmm_core_action (LkmmMachineAction (BeginGp 0)) = [] /\
      before.(lkmm_machine).(machine_core) = waiting.(lkmm_machine).(machine_core) /\
      before.(lkmm_machine).(pending_gp) !! 0 = None /\
      waiting.(lkmm_machine).(pending_gp) !! 0 = Some [] /\ before <> waiting.
    Proof.
      split.
      - apply LkmmStepMachine. apply StepBeginGp with (thread := initial_thread SSynchronizeRcu);
          [split |]; reflexivity.
      - split; first reflexivity. split; first reflexivity.
        split; first reflexivity. split; first reflexivity.
        intros Heq. apply (f_equal (fun s => s.(lkmm_machine).(pending_gp) !! 0)) in Heq.
        discriminate.
    Qed.

    Example finish_retains_certificate :
      lkmm_step program waiting (LkmmMachineAction (FinishGp 0)) finished /\
      core_run program waiting.(lkmm_machine).(machine_core) [CoreEmit 0]
        finished.(lkmm_machine).(machine_core) /\
      finished.(lkmm_machine).(gp_certificates) = [GpCertificate 0 []].
    Proof.
      assert (lkmm_step program waiting (LkmmMachineAction (FinishGp 0)) finished) as Hstep.
      { apply LkmmStepMachine.
        apply StepFinishGp with (thread := initial_thread SSynchronizeRcu) (locks := []);
          try (split; reflexivity); try reflexivity. intros lock Hfalse. inversion Hfalse. }
      split; first done. split; last reflexivity.
      exact (lkmm_step_core_projection _ _ _ _ Hstep).
    Qed.
  End GpState.

  Local Lemma swap_involutive i : Renaming.swap_id (Renaming.swap_id i) = i.
  Proof. destruct i as [|[|[|i]]]; reflexivity. Qed.

  Local Lemma swap_lookup i :
    lookup_event Future.candidate.(candidate_events) (Renaming.swap_id i) =
    lookup_event Sample.candidate.(candidate_events) i.
  Proof.
    destruct i as [|[|[|i]]]; try reflexivity.
    unfold Renaming.swap_id, lookup_event, Future.candidate, Sample.candidate,
      Renaming.swapped_events, Sample.sample_events. cbn [candidate_events].
    transitivity (None : option event); [|symmetry];
      repeat (apply lookup_insert_None; split; last lia); apply lookup_empty.
  Qed.

  Lemma swapped_candidate : candidate_renaming Renaming.swap_id Sample.candidate Future.candidate.
  Proof.
    constructor.
    - constructor.
      + intros x y ex ey Hx Hy Heq.
        apply (f_equal Renaming.swap_id) in Heq. by rewrite !swap_involutive in Heq.
      + intros x ev Hlookup. by rewrite swap_lookup.
      + intros y ev Hlookup. exists (Renaming.swap_id y). split; last apply swap_involutive.
        by rewrite -swap_lookup swap_involutive.
      + intros x loc val Hlookup. destruct x as [|[|[|x]]]; try reflexivity; discriminate.
    - vm_compute. reflexivity.
    - vm_compute. reflexivity.
    - vm_compute. reflexivity.
    - vm_compute. reflexivity.
    - vm_compute. reflexivity.
    - vm_compute. reflexivity.
  Qed.

  Example renamed_origin_keeps_value_and_local_index : exists old index label,
    Renaming.swap_id old = 1 /\
    lookup_event Sample.candidate.(candidate_events) old = Some (EAgent 1 index label) /\
    is_read (EAgent 1 index label) /\ index < 1 /\ old = 2.
  Proof.
    assert (1 ∈ (RegValue 1%Z {[1]}).(reg_origins)) as Horigin by set_solver.
    destruct (renamed_thread_register_origin _ _ _ _ _ _ _ 0 (RegValue 1%Z {[1]}) 1
      swapped_candidate (proj1 Future.reader_and_writer_share_candidate) eq_refl Horigin)
      as (old & index & label & Hname & Hlookup & Hread & Hindex).
    exists old, index, label. split_and!; try done.
    destruct old as [|[|[|old]]]; cbn in Hname; congruence.
  Qed.

  Example renamed_read_retains_future_source : exists old_write old_read write,
    rf Sample.candidate.(candidate_rf) old_write old_read /\
    Renaming.swap_id old_write = write /\ Renaming.swap_id old_read = 1 /\
    rf Future.candidate.(candidate_rf) write 1 /\
    rf_edge_wf Future.candidate.(candidate_events) write 1 /\
    lookup_event Future.after_read.(core_events) write = None.
  Proof.
    destruct (renamed_position_read_source _ _ _ _ _ 1
      (EAgent 1 0 (LMemory AccessRead AccessOnce NotRmw 0 1%Z))
      swapped_candidate Future.graph Future.at_read eq_refl eq_refl)
      as (old_write & old_read & write & Hrf & Hwrite & Hread & Htarget & Hwf).
    exists old_write, old_read, write. split_and!; try done.
    assert (write = 2) as -> by
      (change ((write, 1) ∈ ({[(2, 1)]} : edge_set)) in Htarget; set_solver).
    reflexivity.
  Qed.

  Section assertions.
    Context {Σ : gFunctors}.

    Example lkmm_positions_have_core_provenance P :
      ⊢ all_lkmm_positions (Σ := Σ) P (fun G p =>
        ⌜event_structure_included p.(lkmm_position_state).(lkmm_machine).(machine_core).(core_events)
          G.(candidate_events)⌝).
    Proof.
      iApply (candidate_positions_cover_lkmm P (fun G p =>
        ⌜event_structure_included p.(position_state).(core_events)
          G.(candidate_events)⌝)%I).
      iApply GraphDomainExamples.every_position_retains_its_events.
    Qed.
  End assertions.
End GraphCorrespondenceExamples.
