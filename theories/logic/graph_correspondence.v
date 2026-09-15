From Stdlib Require Import List.
From stdpp Require Import gmap tactics.
From iris_lkmm.lkmm Require Import memory_relations event_renaming.
From iris_lkmm.lang Require Import candidate_renaming.
From iris_lkmm.operational Require Import lkmm_machine lkmm_coupled.
From iris_lkmm.logic Require Import graph_domain.
Import ListNotations.

Module LkmmGraphCorrespondence.
  Export LkmmGraphDomain LkmmCoupled.
  Import LkmmMachine LkmmCandidateRenaming LkmmMemoryRelations EventRenaming.

  Definition coupled_core_action (a : coupled_action) : list core_action :=
    match a with
    | CoupledMachineAction a => core_actions_of a
    | CoupledBuilderAction => []
    end.

  Definition coupled_core_actions (actions : list coupled_action) : list core_action :=
    flat_map coupled_core_action actions.

  Lemma coupled_core_actions_machine actions :
    coupled_core_actions actions = project_actions (machine_actions actions).
  Proof. induction actions as [|[a|] actions IH]; simpl; by rewrite ?IH. Qed.

  Lemma coupled_core_actions_app prefix suffix :
    coupled_core_actions (prefix ++ suffix) =
    coupled_core_actions prefix ++ coupled_core_actions suffix.
  Proof. apply flat_map_app. Qed.

  Lemma coupled_step_core_projection P s a next :
    coupled_step P s a next ->
    core_run P s.(coupled_machine).(machine_core) (coupled_core_action a)
      next.(coupled_machine).(machine_core).
  Proof.
    intros Hstep. destruct Hstep; simpl.
    - by apply step_core_projection.
    - constructor.
  Qed.

  Lemma coupled_run_core_projection P s actions final :
    coupled_run P s actions final ->
    core_run P s.(coupled_machine).(machine_core) (coupled_core_actions actions)
      final.(coupled_machine).(machine_core).
  Proof.
    intros Hrun. rewrite coupled_core_actions_machine.
    apply run_core_projection. by apply coupled_run_machine_projection.
  Qed.

  Lemma coupled_complete_generated_matches final :
    coupled_complete final ->
    generated_matches final.(coupled_machine).(machine_core) (coupled_candidate final).
  Proof.
    intros [_ (HE & HRMW & HA & HD & HC)].
    unfold generated_matches, coupled_candidate. cbn. split_and!; symmetry; done.
  Qed.

  (** Exact projection of the given run, without scheduling or renaming it. *)
  Theorem coupled_run_candidate_execution P actions final :
    coupled_run P (initial_coupled P) actions final -> coupled_complete final ->
    candidate_execution P (coupled_candidate final) (coupled_core_actions actions)
      final.(coupled_machine).(machine_core).
  Proof.
    intros Hrun Hcomplete. split.
    - split; first exact (coupled_run_core_projection _ _ _ _ Hrun).
      exact (proj1 (proj1 Hcomplete)).
    - by apply coupled_complete_generated_matches.
  Qed.

  (** Retain the full trace and machine/builder states.  In particular,
      GP begin may change pending snapshots without emitting a Core event. *)
  Record coupled_execution_position := CoupledExecutionPosition {
    coupled_prefix_actions : list coupled_action;
    coupled_position_state : coupled_state;
    coupled_suffix_actions : list coupled_action;
    coupled_position_final : coupled_state
  }.

  Definition coupled_position_actions (p : coupled_execution_position) : list coupled_action :=
    p.(coupled_prefix_actions) ++ p.(coupled_suffix_actions).

  (** A cut of an accepted coupled execution. Completion, [rf]/[co]
      obligations, and candidate agreement concern the final state;
      the current builder may still lag behind machine emission. *)
  Definition coupled_position P G (p : coupled_execution_position) : Prop :=
    coupled_run P (initial_coupled P) p.(coupled_prefix_actions) p.(coupled_position_state) /\
    coupled_run P p.(coupled_position_state) p.(coupled_suffix_actions) p.(coupled_position_final) /\
    coupled_complete p.(coupled_position_final) /\
    coupled_program_graph_obligations p.(coupled_position_final) /\
    coupled_candidate p.(coupled_position_final) = G.

  Definition coupled_position_to_core (p : coupled_execution_position) : execution_position :=
    ExecutionPosition (coupled_core_actions p.(coupled_prefix_actions))
      p.(coupled_position_state).(coupled_machine).(machine_core)
      (coupled_core_actions p.(coupled_suffix_actions))
      p.(coupled_position_final).(coupled_machine).(machine_core).

  (** GP begin leaves the Core view unchanged, but changes the local
      protocol phase from [None] to [Some locks]. Even [Some []] is a waiting
      GP; finish emits the synchronization event and clears the snapshot. *)
  Record coupled_thread_view := CoupledThreadView {
    coupled_view_core : thread_view;
    coupled_view_pending_gp : option (list event_id)
  }.

  (** Add the agent's pending-GP snapshot to its Core view. The outer
      [None] means the thread is absent, not that it has no pending GP. *)
  Definition lookup_coupled_thread_view (p : coupled_execution_position) (agent : agent_id) :
      option coupled_thread_view :=
    (fun v => CoupledThreadView v
      (p.(coupled_position_state).(coupled_machine).(pending_gp) !! agent)) <$>
      lookup_thread_view (coupled_position_to_core p) agent.

  Definition coupled_thread_at P G p agent v : Prop :=
    coupled_position P G p /\ lookup_coupled_thread_view p agent = Some v.

  Lemma lookup_coupled_thread_view_lookup p agent v :
    lookup_coupled_thread_view p agent = Some v ->
    p.(coupled_position_state).(coupled_machine).(machine_core).(core_threads) !! agent =
      Some v.(coupled_view_core).(view_thread).
  Proof.
    unfold lookup_coupled_thread_view, lookup_thread_view.
    intros Hview. apply fmap_Some in Hview as (cv & Hcore & Heq). subst v.
    apply fmap_Some in Hcore as (thread & Hlookup & Heq). subst cv. done.
  Qed.

  Lemma lookup_coupled_thread_view_index p agent v :
    lookup_coupled_thread_view p agent = Some v ->
    next_agent_index p.(coupled_position_state).(coupled_machine).(machine_core) agent =
      v.(coupled_view_core).(view_event_index).
  Proof.
    unfold lookup_coupled_thread_view, lookup_thread_view.
    intros Hview. apply fmap_Some in Hview as (cv & Hcore & Heq). subst v.
    apply fmap_Some in Hcore as (thread & Hlookup & Heq). subst cv. done.
  Qed.

  Lemma coupled_position_to_core_actions p :
    position_actions (coupled_position_to_core p) = coupled_core_actions (coupled_position_actions p).
  Proof. symmetry. apply coupled_core_actions_app. Qed.

  Lemma coupled_position_run P G p :
    coupled_position P G p ->
    coupled_run P (initial_coupled P) (coupled_position_actions p) p.(coupled_position_final).
  Proof. intros (Hprefix & Hsuffix & _). by eapply coupled_run_trans. Qed.

  Lemma coupled_position_consistent_program_graph P G p :
    coupled_position P G p -> consistent_program_graph P G.
  Proof.
    intros Hpos. pose proof (coupled_position_run _ _ _ Hpos) as Hrun.
    destruct Hpos as (_ & _ & Hcomplete & Hobligations & <-).
    by eapply coupled_run_soundness.
  Qed.

  Theorem coupled_position_projection P G p :
    coupled_position P G p -> candidate_position P G (coupled_position_to_core p).
  Proof.
    intros (Hprefix & Hsuffix & Hcomplete & Hobligations & <-).
    split; first exact (coupled_run_core_projection _ _ _ _ Hprefix).
    split; first exact (coupled_run_core_projection _ _ _ _ Hsuffix).
    split; first exact (proj1 (proj1 Hcomplete)).
    by apply coupled_complete_generated_matches.
  Qed.

  Local Lemma coupled_run_split P start prefix suffix final :
    coupled_run P start (prefix ++ suffix) final ->
    exists current, coupled_run P start prefix current /\ coupled_run P current suffix final.
  Proof.
    revert start. induction prefix as [|a prefix IH]; intros start Hrun; simpl in Hrun.
    - exists start. split; first constructor. done.
    - inversion Hrun as [|s1 s2 s3 a' rest Hstep Hrest]; subst.
      destruct (IH _ Hrest) as (current & Hprefix & Hsuffix).
      exists current. split; last done. econstructor; done.
  Qed.

  (** Every cut of every accepted coupled run is covered.  The two action
      lists and the final state are the caller's, not existential replays. *)
  Theorem coupled_run_positions P prefix suffix final :
    coupled_run P (initial_coupled P) (prefix ++ suffix) final ->
    coupled_complete final -> coupled_program_graph_obligations final ->
    exists current,
      coupled_position P (coupled_candidate final)
        (CoupledExecutionPosition prefix current suffix final) /\
      candidate_position P (coupled_candidate final)
        (coupled_position_to_core (CoupledExecutionPosition prefix current suffix final)).
  Proof.
    intros Hrun Hcomplete Hobligations.
    destruct (coupled_run_split _ _ _ _ _ Hrun) as (current & Hprefix & Hsuffix).
    assert (coupled_position P (coupled_candidate final)
      (CoupledExecutionPosition prefix current suffix final)) as Hpos by (split_and!; done).
    exists current. split; first done. by apply coupled_position_projection.
  Qed.

  Lemma coupled_position_advance P G prefix s a suffix final :
    coupled_position P G (CoupledExecutionPosition prefix s (a :: suffix) final) ->
    exists next, coupled_step P s a next /\
      coupled_position P G (CoupledExecutionPosition (prefix ++ [a]) next suffix final) /\
      core_run P s.(coupled_machine).(machine_core) (coupled_core_action a)
        next.(coupled_machine).(machine_core).
  Proof.
    intros (Hprefix & Hsuffix & Hcomplete & Hobligations & HG).
    inversion Hsuffix; subst.
    eexists. split; first done. split.
    - split; simpl.
      + eapply coupled_run_trans; first done. econstructor; first done. constructor.
      + split_and!; done.
    - by apply coupled_step_core_projection.
  Qed.

  Lemma coupled_position_thread_lookup P G p t v :
    thread_at P G (coupled_position_to_core p) t v ->
    p.(coupled_position_state).(coupled_machine).(machine_core).(core_threads) !! t =
      Some v.(view_thread).
  Proof. intros Hview. exact (proj1 (thread_at_lookup _ _ _ _ _ Hview)). Qed.

  Lemma coupled_position_certificate_clear P G p cert :
    coupled_position P G p ->
    In cert p.(coupled_position_state).(coupled_machine).(gp_certificates) ->
    forall lock, In lock cert.(gc_captured_readers) ->
      ~ In lock (all_open_readers p.(coupled_position_state).(coupled_machine)).
  Proof.
    intros [Hprefix _] Hcert. by eapply coupled_completed_certificate_snapshot_clear.
  Qed.

  (** Reverse coverage is existential and uses the existing completeness
      theorem.  It does not preserve a prescribed schedule or arbitrary cut. *)
  Theorem consistent_program_graph_coupled_coverage P G :
    consistent_program_graph P G -> exists actions final f,
      coupled_run P (initial_coupled P) actions final /\
      coupled_complete final /\ coupled_program_graph_obligations final /\
      candidate_renaming f G (coupled_candidate final) /\
      candidate_execution P (coupled_candidate final) (coupled_core_actions actions)
        final.(coupled_machine).(machine_core).
  Proof.
    intros [Hgraph Hconsistent].
    destruct (coupled_run_completeness _ _ Hgraph Hconsistent)
      as (actions & final & f & Hrun & Hcomplete & Hobligations & Hrename).
    exists actions, final, f. split; first done. split; first done.
    split; first done. split; first done. by apply coupled_run_candidate_execution.
  Qed.

  (** Transport graph facts, not the allocation order of the operational
      machine.  Labels include values, agents, and agent-local indices. *)
  Lemma renamed_position_event P G H f p eid ev :
    candidate_renaming f G H -> candidate_position P H p ->
    lookup_event p.(position_state).(core_events) eid = Some ev ->
    exists old, lookup_event G.(candidate_events) old = Some ev /\ f old = eid.
  Proof.
    intros Hrename Hpos Hlookup.
    pose proof (candidate_position_events _ _ _ Hpos _ _ Hlookup) as Hfinal.
    by eapply (renaming_surjective _ _ _ (candidate_renaming_events _ _ _ Hrename)).
  Qed.

  Lemma renamed_thread_register_origin P G H f p t v r result source :
    candidate_renaming f G H -> thread_at P H p t v ->
    v.(view_thread).(thread_registers) !! r = Some result -> source ∈ result.(reg_origins) ->
    exists old index label, f old = source /\
      lookup_event G.(candidate_events) old = Some (EAgent t index label) /\
      is_read (EAgent t index label) /\ index < v.(view_event_index).
  Proof.
    intros Hrename Hview Hreg Horigin.
    destruct (thread_at_register_origin _ _ _ _ _ _ _ _ Hview Hreg Horigin)
      as (index & label & Hlookup & Hread & Hindex).
    destruct (renaming_surjective _ _ _ (candidate_renaming_events _ _ _ Hrename)
      _ _ Hlookup) as (old & Hold & Hname).
    exists old, index, label. split_and!; done.
  Qed.

  Lemma renamed_thread_control_origin P G H f p t v source :
    candidate_renaming f G H -> thread_at P H p t v ->
    source ∈ thread_control_origins v.(view_thread) ->
    exists old index label, f old = source /\
      lookup_event G.(candidate_events) old = Some (EAgent t index label) /\
      is_read (EAgent t index label) /\ index < v.(view_event_index).
  Proof.
    intros Hrename Hview Horigin.
    destruct (thread_at_control_origin _ _ _ _ _ _ Hview Horigin)
      as (index & label & Hlookup & Hread & Hindex).
    destruct (renaming_surjective _ _ _ (candidate_renaming_events _ _ _ Hrename)
      _ _ Hlookup) as (old & Hold & Hname).
    exists old, index, label. split_and!; done.
  Qed.

  Lemma renamed_position_read_source P G H f p read read_event :
    candidate_renaming f G H -> program_graph P H -> candidate_position P H p ->
    lookup_event p.(position_state).(core_events) read = Some read_event -> is_read read_event ->
    exists old_write old_read write,
      rf G.(candidate_rf) old_write old_read /\ f old_write = write /\ f old_read = read /\
      rf H.(candidate_rf) write read /\ rf_edge_wf H.(candidate_events) write read.
  Proof.
    intros Hrename Hgraph Hpos Hlookup Hread.
    destruct (candidate_position_read_source _ _ _ _ _ Hgraph Hpos Hlookup Hread)
      as (write & Hrf & Hwf & _).
    pose proof Hrf as Himage. unfold rf in Himage.
    rewrite (candidate_renaming_rf _ _ _ Hrename) in Himage.
    apply rename_edges_spec in Himage as (old_write & old_read & Hedge & Hwrite & Hread').
    exists old_write, old_read, write. split_and!; done.
  Qed.
End LkmmGraphCorrespondence.
