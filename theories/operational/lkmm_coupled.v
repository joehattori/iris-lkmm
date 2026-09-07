From Stdlib Require Import List Lia.
From stdpp Require Import gmap sets tactics.
From iris_lkmm.lkmm Require Import memory_relations rcu_graph rcu_mono.
From iris_lkmm.lang Require Import program_graph.
From iris_lkmm.operational Require Import lkmm_machine rcu_builder rcu_candidate.
Import ListNotations.

(** Core execution coupled to the incremental graph builder.  Builder commitments
    may lag behind execution, but events, RMW pairs, and dependency provenance
    must already have been generated.  The builder chooses [rf]/[co], while
    [hb]/[pb] are derived; neither transition rule consults a completed candidate. *)
Module LkmmCoupled.
  Import LkmmMachine RcuGraph RcuMono RcuBuilder RcuCandidate.
  Import LkmmProgramGraph LkmmMemoryRelations.

  Definition generated_prefix (m : LkmmMachine.state) (r : raw_graph) : Prop :=
    event_structure_included r.(raw_events) m.(machine_core).(core_events) /\
    (list_to_set r.(raw_rmw) : edge_set) ⊆ m.(machine_core).(core_rmw) /\
    (list_to_set r.(raw_direct_addr) : edge_set) ⊆
      m.(machine_core).(core_direct_addr) /\
    (list_to_set r.(raw_direct_data) : edge_set) ⊆
      m.(machine_core).(core_direct_data) /\
    (list_to_set r.(raw_direct_ctrl) : edge_set) ⊆
      m.(machine_core).(core_direct_ctrl).

  Definition machine_matches_raw (m : LkmmMachine.state) (r : raw_graph) : Prop :=
    r.(raw_events) = m.(machine_core).(core_events) /\
    (list_to_set r.(raw_rmw) : edge_set) = m.(machine_core).(core_rmw) /\
    (list_to_set r.(raw_direct_addr) : edge_set) = m.(machine_core).(core_direct_addr) /\
    (list_to_set r.(raw_direct_data) : edge_set) = m.(machine_core).(core_direct_data) /\
    (list_to_set r.(raw_direct_ctrl) : edge_set) = m.(machine_core).(core_direct_ctrl).

  Record coupled_state := CoupledState {
    coupled_machine : LkmmMachine.state;
    coupled_builder : builder_state
  }.

  Inductive coupled_action :=
  | CoupledMachineAction (a : LkmmMachine.action)
  | CoupledBuilderAction.

  Inductive coupled_step (P : core_program) :
      coupled_state -> coupled_action -> coupled_state -> Prop :=
  | CoupledStepMachine m m' b a :
      LkmmMachine.step P m a m' ->
      coupled_step P (CoupledState m b) (CoupledMachineAction a) (CoupledState m' b)
  | CoupledStepBuilder m b b' :
      builder_step b b' ->
      generated_prefix m b'.(bs_raw) ->
      coupled_step P (CoupledState m b) CoupledBuilderAction (CoupledState m b').

  Inductive coupled_run (P : core_program) :
      coupled_state -> list coupled_action -> coupled_state -> Prop :=
  | CoupledRunNil s : coupled_run P s [] s
  | CoupledRunCons s1 s2 s3 a actions :
      coupled_step P s1 a s2 -> coupled_run P s2 actions s3 ->
      coupled_run P s1 (a :: actions) s3.

  Fixpoint machine_actions (actions : list coupled_action) : list LkmmMachine.action :=
    match actions with
    | [] => []
    | CoupledMachineAction a :: rest => a :: machine_actions rest
    | CoupledBuilderAction :: rest => machine_actions rest
    end.

  Definition initial_coupled (P : core_program) : coupled_state :=
    CoupledState (LkmmMachine.initial_state P) initial_builder.

  Definition coupled_complete (s : coupled_state) : Prop :=
    LkmmMachine.complete s.(coupled_machine) /\
    machine_matches_raw s.(coupled_machine) s.(coupled_builder).(bs_raw).

  (** Every candidate relation comes from the builder. *)
  Definition coupled_candidate (s : coupled_state) : core_candidate :=
    CoreCandidate s.(coupled_builder).(bs_raw).(raw_events)
      (list_to_set s.(coupled_builder).(bs_raw).(raw_rf))
      (list_to_set s.(coupled_builder).(bs_raw).(raw_co))
      (list_to_set s.(coupled_builder).(bs_raw).(raw_rmw))
      (list_to_set s.(coupled_builder).(bs_raw).(raw_direct_addr))
      (list_to_set s.(coupled_builder).(bs_raw).(raw_direct_data))
      (list_to_set s.(coupled_builder).(bs_raw).(raw_direct_ctrl)).

  (** These base-relation obligations are not transition guards.  Allocation,
      generated-relation well-formedness, and complete RCU matching follow
      from a completed coupled run. *)
  Definition coupled_program_graph_obligations (s : coupled_state) : Prop :=
    let C := coupled_candidate s in
    rf_wf C.(candidate_events) C.(candidate_rf) /\
    co_wf C.(candidate_events) C.(candidate_co).

  Lemma coupled_run_trans P s1 actions1 s2 actions2 s3 :
    coupled_run P s1 actions1 s2 -> coupled_run P s2 actions2 s3 ->
    coupled_run P s1 (actions1 ++ actions2) s3.
  Proof.
    intros Hrun Hrest. induction Hrun; simpl; first done.
    econstructor; [done | by apply IHHrun].
  Qed.

  Lemma coupled_run_machine_projection P s actions s' :
    coupled_run P s actions s' ->
    LkmmMachine.run P s.(coupled_machine) (machine_actions actions) s'.(coupled_machine).
  Proof.
    intros Hrun. induction Hrun; first constructor.
    destruct H; simpl in *; last done. econstructor; done.
  Qed.

  Lemma coupled_run_builder_projection P s actions s' :
    coupled_run P s actions s' -> builder_run s.(coupled_builder) s'.(coupled_builder).
  Proof.
    intros Hrun. induction Hrun; first constructor.
    destruct H; simpl in *; first done. econstructor; done.
  Qed.

  Local Lemma core_step_generated_mono P core a core' :
    core_step P core a core' -> core_allocation_wf core ->
    event_structure_included core.(core_events) core'.(core_events) /\
    core.(core_rmw) ⊆ core'.(core_rmw) /\
    core.(core_direct_addr) ⊆ core'.(core_direct_addr) /\
    core.(core_direct_data) ⊆ core'.(core_direct_data) /\
    core.(core_direct_ctrl) ⊆ core'.(core_direct_ctrl).
  Proof.
    intros Hstep (_ & Hids & _). destruct Hstep; split_and!; cbn;
      try solve [intros eid ev Hlookup; exact Hlookup | set_solver];
      intros eid ev Hlookup; unfold lookup_event in *;
      repeat (apply lookup_insert_Some; right; split;
        [intros Heq; subst eid; specialize (Hids _ _ Hlookup); lia |]); done.
  Qed.

  Local Lemma core_run_generated_mono P core actions core' :
    core_run P core actions core' -> core_allocation_wf core ->
    event_structure_included core.(core_events) core'.(core_events) /\
    core.(core_rmw) ⊆ core'.(core_rmw) /\
    core.(core_direct_addr) ⊆ core'.(core_direct_addr) /\
    core.(core_direct_data) ⊆ core'.(core_direct_data) /\
    core.(core_direct_ctrl) ⊆ core'.(core_direct_ctrl).
  Proof.
    intros Hrun. induction Hrun; intros Hwf.
    - split_and!; try done. intros eid ev Hlookup. exact Hlookup.
    - destruct (core_step_generated_mono _ _ _ _ H Hwf) as
        (HE & HRMW & HADDR & HDATA & HCTRL).
      destruct IHHrun as (HE' & HRMW' & HADDR' & HDATA' & HCTRL');
        first by eapply core_step_preserves_allocation.
      split_and!.
      + intros eid ev Hlookup. exact (HE' eid ev (HE eid ev Hlookup)).
      + intros edge Hedge. exact (HRMW' edge (HRMW edge Hedge)).
      + intros edge Hedge. exact (HADDR' edge (HADDR edge Hedge)).
      + intros edge Hedge. exact (HDATA' edge (HDATA edge Hedge)).
      + intros edge Hedge. exact (HCTRL' edge (HCTRL edge Hedge)).
  Qed.

  Local Lemma step_preserves_generated_prefix P s a s' :
    coupled_step P s a s' -> core_allocation_wf s.(coupled_machine).(machine_core) ->
    generated_prefix s.(coupled_machine) s.(coupled_builder).(bs_raw) ->
    generated_prefix s'.(coupled_machine) s'.(coupled_builder).(bs_raw).
  Proof.
    intros Hstep Hwf (HE & HRMW & HADDR & HDATA & HCTRL).
    destruct Hstep; simpl in *; last done.
    pose proof (step_core_projection _ _ _ _ H) as Hcore.
    destruct (core_run_generated_mono _ _ _ _ Hcore Hwf) as
      (HE' & HRMW' & HADDR' & HDATA' & HCTRL').
    split_and!.
    - intros eid ev Hlookup. exact (HE' eid ev (HE eid ev Hlookup)).
    - intros edge Hedge. exact (HRMW' edge (HRMW edge Hedge)).
    - intros edge Hedge. exact (HADDR' edge (HADDR edge Hedge)).
    - intros edge Hedge. exact (HDATA' edge (HDATA edge Hedge)).
    - intros edge Hedge. exact (HCTRL' edge (HCTRL edge Hedge)).
  Qed.

  (** No reachable builder prefix invents an event or generated relation. *)
  Theorem coupled_run_generated_prefix P actions s :
    coupled_run P (initial_coupled P) actions s ->
    generated_prefix s.(coupled_machine) s.(coupled_builder).(bs_raw).
  Proof.
    assert (forall s1 actions0 s2, coupled_run P s1 actions0 s2 ->
      core_allocation_wf s1.(coupled_machine).(machine_core) ->
      generated_prefix s1.(coupled_machine) s1.(coupled_builder).(bs_raw) ->
      generated_prefix s2.(coupled_machine) s2.(coupled_builder).(bs_raw)) as Hpreserve.
    { intros s1 actions0 s2 Hrun. induction Hrun; intros Hwf Hprefix; first done.
      apply IHHrun; last by eapply step_preserves_generated_prefix.
      destruct H; simpl in *; last done.
      eapply core_run_preserves_allocation; [by apply step_core_projection | done]. }
    intros Hrun. eapply Hpreserve; first done.
    - apply core_initial_allocation_wf.
    - split_and!; try set_solver. intros eid ev Hlookup. discriminate Hlookup.
  Qed.

  Theorem coupled_operational_soundness P actions s :
    coupled_run P (initial_coupled P) actions s -> coupled_complete s ->
    complete_core_run P (project_actions (machine_actions actions))
      s.(coupled_machine).(machine_core) /\
    machine_matches_raw s.(coupled_machine) s.(coupled_builder).(bs_raw) /\
    graph_consistent (graph_of_raw s.(coupled_builder).(bs_raw)) /\
    core_allocation_wf s.(coupled_machine).(machine_core) /\
    no_unmatched_unlocks s.(coupled_machine) /\
    certificates_sound s.(coupled_machine).
  Proof.
    intros Hrun [Hcomplete Hmatches].
    pose proof (coupled_run_machine_projection _ _ _ _ Hrun) as Hmachine.
    pose proof (coupled_run_builder_projection _ _ _ _ Hrun) as Hbuilder.
    destruct (run_rcu_safety _ _ _ Hmachine) as [Hsafe Hcerts].
    pose proof (run_allocation_wf _ _ _ Hmachine) as Halloc.
    split_and!; try done.
    - apply complete_machine_run_core_projection. split; done.
    - by eapply completed_builder_run_consistent.
  Qed.

  Theorem coupled_completed_certificate_snapshot_clear P actions s cert :
    coupled_run P (initial_coupled P) actions s ->
    In cert s.(coupled_machine).(gp_certificates) ->
    forall lock, In lock cert.(gc_snapshot) -> ~ In lock (snapshot s.(coupled_machine)).
  Proof.
    intros Hrun Hcert.
    pose proof (coupled_run_machine_projection _ _ _ _ Hrun) as Hmachine.
    exact (completed_snapshot_clear P (machine_actions actions) s.(coupled_machine)
      cert Hmachine Hcert).
  Qed.

  Theorem coupled_run_program_graph P actions s :
    coupled_run P (initial_coupled P) actions s -> coupled_complete s ->
    coupled_program_graph_obligations s -> program_graph P (coupled_candidate s).
  Proof.
    intros Hrun Hcomplete Hobligations.
    destruct (coupled_operational_soundness _ _ _ Hrun Hcomplete)
      as (Hcore & (Hevents & Hrmw_eq & Haddr_eq & Hdata_eq & Hctrl_eq) &
        _ & [Halloc _] & _).
    pose proof (complete_core_run_generated_relations_wf _ _ _ Hcore) as
      (Hrmw & Haddr & Hdata & Hctrl).
    destruct Hcomplete as [[_ [_ Hmatching]] _].
    constructor.
    - exists (project_actions (machine_actions actions)), s.(coupled_machine).(machine_core).
      split_and!; try done; symmetry; done.
    - destruct Hobligations as [Hrf Hco].
      unfold core_candidate_wf. split_and!; try done.
      + change (event_structure_wf s.(coupled_builder).(bs_raw).(raw_events)).
        by rewrite Hevents.
      + change (rmw_wf s.(coupled_builder).(bs_raw).(raw_events)
          (list_to_set s.(coupled_builder).(bs_raw).(raw_rmw))).
        by rewrite Hevents, Hrmw_eq.
      + change (direct_addr_wf s.(coupled_builder).(bs_raw).(raw_events)
          (list_to_set s.(coupled_builder).(bs_raw).(raw_direct_addr))).
        by rewrite Hevents, Haddr_eq.
      + change (direct_data_wf s.(coupled_builder).(bs_raw).(raw_events)
          (list_to_set s.(coupled_builder).(bs_raw).(raw_direct_data))).
        by rewrite Hevents, Hdata_eq.
      + change (direct_ctrl_wf s.(coupled_builder).(bs_raw).(raw_events)
          (list_to_set s.(coupled_builder).(bs_raw).(raw_direct_ctrl))).
        by rewrite Hevents, Hctrl_eq.
      + change (rcu_matching_complete s.(coupled_builder).(bs_raw).(raw_events)).
        by rewrite Hevents.
  Qed.

  Theorem coupled_candidate_lkmm_consistent P actions s :
    coupled_run P (initial_coupled P) actions s ->
    lkmm_consistent (coupled_candidate s).
  Proof.
    intros Hrun.
    pose proof (coupled_run_builder_projection _ _ _ _ Hrun) as Hbuilder.
    change (graph_consistent (graph_of_raw s.(coupled_builder).(bs_raw))).
    by eapply completed_builder_run_consistent.
  Qed.

  Theorem coupled_run_soundness P actions s :
    coupled_run P (initial_coupled P) actions s -> coupled_complete s ->
    coupled_program_graph_obligations s ->
    program_graph P (coupled_candidate s) /\ lkmm_consistent (coupled_candidate s).
  Proof.
    intros Hrun Hcomplete Hobligations. split.
    - by eapply coupled_run_program_graph.
    - by eapply coupled_candidate_lkmm_consistent.
  Qed.

  Lemma lift_machine_run P m actions m' b :
    LkmmMachine.run P m actions m' ->
    coupled_run P (CoupledState m b) (map CoupledMachineAction actions) (CoupledState m' b).
  Proof.
    intros Hrun. induction Hrun; simpl; first constructor.
    econstructor; [by apply CoupledStepMachine | done].
  Qed.

  Local Lemma builder_run_graph_le b b' :
    builder_run b b' -> graph_le (graph_of_raw b.(bs_raw)) (graph_of_raw b'.(bs_raw)).
  Proof.
    intros Hrun. induction Hrun; first apply graph_le_refl.
    eapply graph_le_trans; last done.
    destruct H; simpl; [by apply raw_step_graph_le | apply graph_le_refl].
  Qed.

  Local Lemma generated_prefix_backward m r r' :
    graph_le (graph_of_raw r) (graph_of_raw r') ->
    generated_prefix m r' -> generated_prefix m r.
  Proof.
    intros Hle (HE & HRMW & HADDR & HDATA & HCTRL). split_and!.
    - intros eid ev Hlookup. apply HE. by eapply (graph_le_events _ _ Hle).
    - intros edge Hedge. apply HRMW. by eapply (graph_le_rmw _ _ Hle).
    - intros edge Hedge. apply HADDR. by eapply (graph_le_direct_addr _ _ Hle).
    - intros edge Hedge. apply HDATA. by eapply (graph_le_direct_data _ _ Hle).
    - intros edge Hedge. apply HCTRL. by eapply (graph_le_direct_ctrl _ _ Hle).
  Qed.

  Lemma lift_builder_run P m b b' :
    builder_run b b' -> generated_prefix m b'.(bs_raw) ->
    exists actions, coupled_run P (CoupledState m b) actions (CoupledState m b').
  Proof.
    intros Hrun Hprefix. induction Hrun; first by exists []; constructor.
    destruct IHHrun as [actions Hactions]; first done.
    exists (CoupledBuilderAction :: actions). econstructor; last done.
    apply CoupledStepBuilder; first done.
    eapply generated_prefix_backward; [by apply builder_run_graph_le | done].
  Qed.

  (** Relative scheduling: the machine execution is supplied as a premise,
      not reconstructed from arbitrary LKMM-consistent program graphs. *)
  Definition consistent_program_candidate (P : core_program) (C : finite_candidate) : Prop :=
    candidate_well_formed C /\ graph_consistent (candidate_graph C) /\
    exists actions m,
      LkmmMachine.complete_machine_run P actions m /\ machine_matches_raw m (candidate_raw C).

  Theorem consistent_program_candidate_is_schedulable P C :
    consistent_program_candidate P C ->
    exists actions s,
      coupled_run P (initial_coupled P) actions s /\ coupled_complete s /\
      s.(coupled_builder).(bs_raw) = candidate_raw C.
  Proof.
    intros (Hwf & Hconsistent & machine_actions0 & m & [Hmachine Hcomplete] & Hmatches).
    destruct (consistent_candidate_is_incrementally_schedulable C Hwf Hconsistent)
      as (b & Hbuilder & Hraw & _).
    pose proof (lift_machine_run P _ _ _ initial_builder Hmachine) as Hmachine_lift.
    assert (generated_prefix m b.(bs_raw)) as Hprefix.
    { rewrite Hraw. destruct Hmatches as (HE & HRMW & HADDR & HDATA & HCTRL). split_and!.
      - rewrite HE. intros eid ev Hlookup. done.
      - rewrite HRMW. done.
      - rewrite HADDR. done.
      - rewrite HDATA. done.
      - rewrite HCTRL. done. }
    destruct (lift_builder_run P m _ _ Hbuilder Hprefix) as [builder_actions Hbuilder_lift].
    exists (map CoupledMachineAction machine_actions0 ++ builder_actions), (CoupledState m b).
    split; first by eapply coupled_run_trans.
    split; last done. split; first done. simpl. by rewrite Hraw.
  Qed.

  Module CouplingTests.
    Definition program : core_program :=
      CoreProgram {[0 := 0%Z]} {[0 := SXchg 0 RmwRelaxed (EConst 0) (EConst 1)]}.
    Definition finished : LkmmMachine.state :=
      State (add_rmw_events (core_initial_state program) 0
        (ThreadState (SXchg 0 RmwRelaxed (EConst 0) (EConst 1)) [] ∅)
        AccessOnce 0 0%Z 1%Z {[0 := RegValue 0%Z {[1]}]} ∅ ∅ ∅) ∅ [].
    Definition candidate : finite_candidate :=
      FiniteCandidate
        [LabeledEvent 2 (EAgent 0 1 (LMemory AccessWrite AccessOnce RmwMarked 0 1%Z));
         LabeledEvent 1 (EAgent 0 0 (LMemory AccessRead AccessOnce RmwMarked 0 0%Z));
         LabeledEvent 0 (EInitWrite 0 0%Z)]
        [(0, 1)] [(0, 2)] [(1, 2)] [] [] [].

    Local Lemma machine_run :
      LkmmMachine.complete_machine_run program [Execute (CoreObserve 0 0%Z)] finished.
    Proof.
      split.
      - econstructor; last constructor. eapply StepCore; try done.
        eapply StepXchg with (mode := RmwRelaxed) (result := RegValue 1%Z ∅);
          try reflexivity.
        unfold location_initialized. by eexists.
      - unfold complete. split_and!; try done.
        intros agent thread Hlookup.
        change (({[0 := ThreadState SSkip [] {[0 := RegValue 0%Z {[1]}]}]} :
          gmap agent_id thread_state) !! agent = Some thread) in Hlookup.
        apply lookup_singleton_Some in Hlookup as [<- <-]. done.
    Qed.

    Local Lemma candidate_wf : candidate_well_formed candidate.
    Proof.
      unfold candidate_well_formed. split_and!.
      - vm_compute. repeat constructor; set_solver.
      - vm_compute. split_and!; done.
      - destruct machine_run as [Hrun _].
        destruct (run_allocation_wf _ _ _ Hrun) as [Hwf _]. exact Hwf.
      - split; done.
      - unfold rf_prefix_wf, rf_functional. split.
        + intros write read Hrf.
          unfold rf, edge_relation in Hrf. simpl in Hrf.
          assert (write = 0 /\ read = 1) as [-> ->] by set_solver.
          eexists _, _, 0%Z. split_and!; try reflexivity.
          exists 0. split; reflexivity.
        + intros write1 write2 read Hrf1 Hrf2.
          unfold rf, edge_relation in Hrf1, Hrf2. simpl in Hrf1, Hrf2. set_solver.
      - unfold co_prefix_wf, rel_acyclic, rel_irreflexive. split.
        + intros write1 write2 Hco.
          unfold co, edge_relation in Hco. simpl in Hco.
          assert (write1 = 0 /\ write2 = 2) as [-> ->] by set_solver.
          eexists _, _. split_and!; try reflexivity.
          exists 0. split; reflexivity.
        + assert (forall source target,
            co {[(0, 2)]} source target -> source < target) as Hstep.
          { unfold co, edge_relation. set_solver. }
          assert (forall source target,
            tc (co {[(0, 2)]}) source target -> source < target) as Hpath.
          { intros source target Hcycle. induction Hcycle.
            - by apply Hstep.
            - lia. }
          intros write Hcycle. pose proof (Hpath write write Hcycle). lia.
      - unfold rmw_prefix_wf, rmw_functional, rmw_injective. split_and!.
        + intros read write Hrmw.
          unfold rmw, edge_relation in Hrmw. simpl in Hrmw.
          assert (read = 1 /\ write = 2) as [-> ->] by set_solver.
          eexists _, _. split_and!; try reflexivity.
          * exists 0, 0, 1,
              (LMemory AccessRead AccessOnce RmwMarked 0 0%Z),
              (LMemory AccessWrite AccessOnce RmwMarked 0 1%Z).
            split_and!; try reflexivity; lia.
          * exists 0. split; reflexivity.
          * exists AccessOnce. split; reflexivity.
        + intros read write1 write2 Hrmw1 Hrmw2.
          unfold rmw, edge_relation in Hrmw1, Hrmw2. simpl in Hrmw1, Hrmw2. set_solver.
        + intros read1 read2 write Hrmw1 Hrmw2.
          unfold rmw, edge_relation in Hrmw1, Hrmw2. simpl in Hrmw1, Hrmw2. set_solver.
      - intros x y Hin. inversion Hin.
      - intros x y Hin. inversion Hin.
      - intros x y Hin. inversion Hin.
    Qed.

    Example generated_rmw_commitments :
      graph_consistent (candidate_graph candidate) ->
      exists actions s,
        coupled_run program (initial_coupled program) actions s /\ coupled_complete s /\
        s.(coupled_builder).(bs_raw) = candidate_raw candidate.
    Proof.
      intros Hconsistent.
      apply consistent_program_candidate_is_schedulable. split; first apply candidate_wf.
      split; first done.
      exists [Execute (CoreObserve 0 0%Z)], finished. split; first apply machine_run.
      split; done.
    Qed.

    (** A builder may lag, but cannot invent generated provenance or declare
        completion before every generated collection has caught up. *)
    Example provenance_and_completion_guards :
      generated_prefix (LkmmMachine.initial_state program)
        (add_event empty_raw (LabeledEvent 0 (EInitWrite 0 0%Z))) /\
      ~ generated_prefix (LkmmMachine.initial_state program) (candidate_raw candidate) /\
      ~ generated_prefix finished (add_rmw (candidate_raw candidate) (2, 1)) /\
      ~ generated_prefix finished (add_direct_addr (candidate_raw candidate) (2, 1)) /\
      ~ coupled_complete (initial_coupled program) /\
      ~ coupled_complete (CoupledState finished initial_builder) /\
      ~ coupled_complete (CoupledState finished
        (BuilderState (RawGraph finished.(machine_core).(core_events) [] [] [] [] [] []) []
          initial_builder.(bs_seen_consistency))).
    Proof.
      split_and!.
      - split_and!; try set_solver. intros eid ev Hlookup. exact Hlookup.
      - intros [HE _]. specialize (HE 1
          (EAgent 0 0 (LMemory AccessRead AccessOnce RmwMarked 0 0%Z)) eq_refl).
        discriminate HE.
      - intros (_ & HRMW & _). specialize (HRMW (2, 1)). vm_compute in HRMW. naive_solver.
      - intros (_ & _ & HADDR & _). specialize (HADDR (2, 1)).
        vm_compute in HADDR. naive_solver.
      - intros [[Hthreads _] _]. destruct (Hthreads 0 _ eq_refl) as [Hstmt _].
        discriminate Hstmt.
      - intros [_ [HE _]].
        pose proof (f_equal (fun E => lookup_event E 0) HE) as Hlookup. discriminate Hlookup.
      - intros [_ (_ & HRMW & _)].
        change ((∅ : edge_set) = finished.(machine_core).(core_rmw)) in HRMW.
        assert ((1, 2) ∈ (∅ : edge_set)) by (rewrite HRMW; set_solver). set_solver.
    Qed.
  End CouplingTests.

  Module ProgramGraphBridgeTests.
    Import LkmmProgramGraph.ProgramGraphTests.

    Definition written : core_state :=
      add_single_event (core_initial_state program) 0 (initial_thread writer)
        (LMemory AccessWrite AccessOnce NotRmw 0 1%Z) ∅ ∅ ∅ ∅.
    Definition finished : LkmmMachine.state :=
      State (add_single_event written 1 (initial_thread reader)
        (LMemory AccessRead AccessOnce NotRmw 0 1%Z)
        {[0 := RegValue 1%Z {[2]}]} ∅ ∅ ∅) ∅ [].
    Definition finite_graph : finite_candidate :=
      FiniteCandidate [LabeledEvent 2 read; LabeledEvent 1 write; LabeledEvent 0 init_write]
        [(1, 2)] [(0, 1)] [] [] [] [].

    Local Lemma machine_run :
      LkmmMachine.complete_machine_run program [Execute (CoreEmit 0); Execute (CoreObserve 1 1%Z)]
        finished.
    Proof.
      split.
      - eapply RunCons with (s2 := State written ∅ []).
        { eapply StepCore; try done.
          eapply StepStore with (mode := StoreOnce) (result := RegValue 1%Z ∅);
            try done. by eexists. }
        eapply RunCons; last constructor.
        eapply StepCore; try done.
        eapply StepLoad with (mode := LoadOnce) (dst := 0); try done. by eexists.
      - unfold complete. split_and!; try done.
        intros agent thread Hlookup.
        change (({[1 := ThreadState SSkip [] {[0 := RegValue 1%Z {[2]}]};
          0 := ThreadState SSkip [] ∅]} : gmap agent_id thread_state) !! agent = Some thread)
          in Hlookup.
        apply lookup_insert_Some in Hlookup as [[<- <-] | [_ Hlookup]]; first done.
        apply lookup_singleton_Some in Hlookup as [<- <-]. done.
    Qed.

    Local Lemma finite_graph_wf : candidate_well_formed finite_graph.
    Proof.
      destruct (program_graph_wf _ _ two_agent_program_graph)
        as (HE & Hrf & Hco & Hrmw & _ & _ & _ & Hmatching).
      unfold candidate_well_formed. split_and!; try done.
      - vm_compute. repeat constructor; set_solver.
      - by apply rf_wf_prefix.
      - by apply co_wf_prefix.
    Qed.

    Example completed_coupled_run_has_program_graph :
      graph_consistent (candidate_graph finite_graph) ->
      exists actions s,
        coupled_run program (initial_coupled program) actions s /\ coupled_complete s /\
        program_graph program (coupled_candidate s) /\
        lkmm_consistent (coupled_candidate s) /\
        candidate_rf (coupled_candidate s) = sample_rf /\
        candidate_co (coupled_candidate s) = sample_co.
    Proof.
      intros Hconsistent.
      assert (consistent_program_candidate program finite_graph) as Hcandidate.
      { split; first apply finite_graph_wf.
        split; first done.
        exists [Execute (CoreEmit 0); Execute (CoreObserve 1 1%Z)], finished.
        split; first apply machine_run. split_and!; done. }
      destruct (consistent_program_candidate_is_schedulable _ _ Hcandidate)
        as (actions & s & Hrun & Hcomplete & Hraw).
      assert (coupled_program_graph_obligations s) as Hobligations.
      { unfold coupled_program_graph_obligations, coupled_candidate. rewrite Hraw.
        destruct (program_graph_wf _ _ two_agent_program_graph) as (_ & Hrf & Hco & _).
        split; done. }
      destruct (coupled_run_soundness _ _ _ Hrun Hcomplete Hobligations)
        as [Hprogram_graph Hlkmm].
      exists actions, s. split; first done. split; first done.
      split; first done. split; first done.
      unfold coupled_candidate. rewrite Hraw. split; done.
    Qed.

    Example malformed_rf_is_an_explicit_obligation :
      ~ coupled_program_graph_obligations (CoupledState finished
        (BuilderState (RawGraph sample_events [(1, 1)] [(0, 1)] [] [] [] []) []
          initial_builder.(bs_seen_consistency))).
    Proof.
      intros [Hrf _]. destruct Hrf as [Hedges _].
      assert (rf (list_to_set [(1, 1)]) 1 1) as Hedge by set_solver.
      destruct (Hedges 1 1 Hedge) as (ev1 & ev2 & val & _ & Hlookup & _ & Hread & _).
      change (Some write = Some ev2) in Hlookup. injection Hlookup as <-. done.
    Qed.
  End ProgramGraphBridgeTests.

End LkmmCoupled.
