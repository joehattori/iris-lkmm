From Stdlib Require Import List.
From stdpp Require Import gmap tactics.
From iris_lkmm.lkmm Require Import memory_relations.
From iris_lkmm.lang Require Import core_agent_replay.
Import ListNotations.

(** The proof domain for a graph-relative WP.  These are predicates on
    existing Core executions, not new operational transition rules.  A
    complete candidate is fixed outside the local thread judgments. *)
Module LkmmGraphDomain.
  Export LkmmCoreAgentReplay.
  Import LkmmMemoryRelations.

  Definition consistent_program_graph (P : core_program) (G : core_candidate) : Prop :=
    program_graph P G /\ lkmm_consistent G.

  (** [rf] and [co] belong to [G], not to the executing Core state. *)
  Definition generated_matches (s : core_state) (G : core_candidate) : Prop :=
    s.(core_events) = G.(candidate_events) /\
    s.(core_rmw) = G.(candidate_rmw) /\
    s.(core_direct_addr) = G.(candidate_direct_addr) /\
    s.(core_direct_data) = G.(candidate_direct_data) /\
    s.(core_direct_ctrl) = G.(candidate_direct_ctrl).

  Definition candidate_execution P G actions final : Prop :=
    complete_core_run P actions final /\ generated_matches final G.

  (** Retain both sides of the cut, including silent steps.  The future
      is a proof witness; it is never installed in the operational state.
      All witnesses will be quantified over, not one chosen replay. *)
  Record execution_position := ExecutionPosition {
    position_prefix : list core_action;
    position_state : core_state;
    position_suffix : list core_action;
    position_final : core_state
  }.

  Definition position_actions (p : execution_position) : list core_action :=
    p.(position_prefix) ++ p.(position_suffix).

  (** Both sides of this execution cut run, and the final Core state is
      complete and matches [G]'s generated fields. Candidate well-formedness
      and LKMM consistency are separate premises. *)
  Definition candidate_position P G (p : execution_position) : Prop :=
    core_run P (core_initial_state P) p.(position_prefix) p.(position_state) /\
    core_run P p.(position_state) p.(position_suffix) p.(position_final) /\
    core_complete p.(position_final) /\ generated_matches p.(position_final) G.

  Definition initial_position P actions final : execution_position :=
    ExecutionPosition [] (core_initial_state P) actions final.

  Definition terminal_position actions final : execution_position :=
    ExecutionPosition actions final [] final.

  (** A view keeps the whole continuation and register provenance.  The
      event index and action history are different: silent steps advance
      only the latter, and an RMW emits two events in one action. *)
  Record thread_view := ThreadView {
    view_thread : thread_state;
    view_event_index : event_index;
    view_actions : list core_action
  }.

  (** Look up [t]'s current thread, adding its next local event index and
      Core action history from the prefix. Return [None] if [t] is absent. *)
  Definition lookup_thread_view (p : execution_position) (t : agent_id) : option thread_view :=
    (fun th => ThreadView th (next_agent_index p.(position_state) t)
      (agent_actions t p.(position_prefix))) <$>
      p.(position_state).(core_threads) !! t.

  Definition thread_at P G p t v : Prop :=
    candidate_position P G p /\ lookup_thread_view p t = Some v.

  Lemma program_graph_execution P G :
    program_graph P G <->
    (exists actions final, candidate_execution P G actions final) /\ core_candidate_wf G.
  Proof.
    split.
    - intros [(actions & final & Hrun & Hmatch) Hwf].
      split; last done. exists actions, final. done.
    - intros [(actions & final & Hrun & Hmatch) Hwf].
      constructor; last done. exists actions, final. done.
  Qed.

  Lemma candidate_execution_initial P G actions final :
    candidate_execution P G actions final ->
    candidate_position P G (initial_position P actions final).
  Proof. intros [[Hrun Hcomplete] Hmatch]. split; first constructor. done. Qed.

  Lemma candidate_execution_terminal P G actions final :
    candidate_execution P G actions final ->
    candidate_position P G (terminal_position actions final).
  Proof. intros [[Hrun Hcomplete] Hmatch]. split; first done. split; first constructor. done. Qed.

  Lemma candidate_position_execution P G p :
    candidate_position P G p ->
    candidate_execution P G (position_actions p) p.(position_final).
  Proof.
    intros (Hprefix & Hsuffix & Hcomplete & Hmatch).
    split; last done. split; last done. by eapply core_run_append.
  Qed.

  (** This advances a cut in an existing execution.  It neither adds a
      transition guard nor asserts that every raw successor fits [G]. *)
  Lemma candidate_position_advance P G prefix s a suffix final :
    candidate_position P G (ExecutionPosition prefix s (a :: suffix) final) ->
    exists s', core_step P s a s' /\
      candidate_position P G (ExecutionPosition (prefix ++ [a]) s' suffix final).
  Proof.
    intros (Hprefix & Hsuffix & Hcomplete & Hmatch).
    inversion Hsuffix; subst.
    eexists. split; first done. split; simpl.
    - eapply core_run_append; first done. econstructor; first done. constructor.
    - done.
  Qed.

  Lemma program_graph_has_positions P G :
    program_graph P G -> exists actions final,
      candidate_position P G (initial_position P actions final) /\
      candidate_position P G (terminal_position actions final).
  Proof.
    rewrite program_graph_execution. intros [(actions & final & Hrun) _].
    exists actions, final. split.
    - by apply candidate_execution_initial.
    - by apply candidate_execution_terminal.
  Qed.

  Lemma candidate_position_generated_wf P G p :
    candidate_position P G p -> core_generated_wf p.(position_state).
  Proof. intros [Hprefix _]. by eapply core_run_generated_wf. Qed.

  Lemma candidate_position_events P G p :
    candidate_position P G p ->
    event_structure_included p.(position_state).(core_events) G.(candidate_events).
  Proof.
    intros (Hprefix & Hsuffix & Hcomplete & Hevents & Hmatch).
    rewrite <- Hevents. eapply core_run_events_included; first done.
    by eapply core_run_allocation_wf.
  Qed.

  Local Lemma core_step_generated_edges P s a s' :
    core_step P s a s' ->
    s.(core_rmw) ⊆ s'.(core_rmw) /\
    s.(core_direct_addr) ⊆ s'.(core_direct_addr) /\
    s.(core_direct_data) ⊆ s'.(core_direct_data) /\
    s.(core_direct_ctrl) ⊆ s'.(core_direct_ctrl).
  Proof.
    intros Hstep. destruct Hstep; cbn; unfold add_origin_edges, add_control_edges;
      split_and!; set_solver.
  Qed.

  Local Lemma core_run_generated_edges P s actions final :
    core_run P s actions final ->
    s.(core_rmw) ⊆ final.(core_rmw) /\
    s.(core_direct_addr) ⊆ final.(core_direct_addr) /\
    s.(core_direct_data) ⊆ final.(core_direct_data) /\
    s.(core_direct_ctrl) ⊆ final.(core_direct_ctrl).
  Proof.
    induction 1; first (split_and!; done).
    destruct (core_step_generated_edges _ _ _ _ H) as (? & ? & ? & ?).
    destruct IHcore_run as (? & ? & ? & ?). split_and!; set_solver.
  Qed.

  Lemma candidate_position_edges P G p :
    candidate_position P G p ->
    p.(position_state).(core_rmw) ⊆ G.(candidate_rmw) /\
    p.(position_state).(core_direct_addr) ⊆ G.(candidate_direct_addr) /\
    p.(position_state).(core_direct_data) ⊆ G.(candidate_direct_data) /\
    p.(position_state).(core_direct_ctrl) ⊆ G.(candidate_direct_ctrl).
  Proof.
    intros (_ & Hsuffix & _ & _ & Hrmw & Haddr & Hdata & Hctrl).
    rewrite <- Hrmw, <- Haddr, <- Hdata, <- Hctrl.
    by eapply core_run_generated_edges.
  Qed.

  Lemma thread_at_lookup P G p t v :
    thread_at P G p t v ->
    p.(position_state).(core_threads) !! t = Some v.(view_thread) /\
    v.(view_event_index) = next_agent_index p.(position_state) t /\
    v.(view_actions) = agent_actions t p.(position_prefix).
  Proof.
    intros [_ Hview]. unfold lookup_thread_view in Hview.
    apply fmap_Some in Hview as (th & Hlookup & Heq). subst v. done.
  Qed.

  Lemma thread_at_unique P G p t v1 v2 :
    thread_at P G p t v1 -> thread_at P G p t v2 -> v1 = v2.
  Proof. intros [_ H1] [_ H2]. congruence. Qed.

  (** A register's origins still refer to earlier reads by this agent in
      the SAME final candidate.  No provenance is reconstructed from values. *)
  Lemma thread_at_register_origin P G p t v r result source :
    thread_at P G p t v ->
    v.(view_thread).(thread_registers) !! r = Some result ->
    source ∈ result.(reg_origins) ->
    exists index label,
      lookup_event G.(candidate_events) source = Some (EAgent t index label) /\
      is_read (EAgent t index label) /\ index < v.(view_event_index).
  Proof.
    intros Hview Hreg Hsource.
    destruct (thread_at_lookup _ _ _ _ _ Hview) as (Hthread & Hindex & _).
    destruct Hview as [Hpos _].
    destruct (candidate_position_generated_wf _ _ _ Hpos) as (_ & Hprov & _).
    destruct (Hprov t _ Hthread) as [Hregs _].
    destruct (Hregs r result Hreg source Hsource) as (index & label & Hlookup & Hread & Hlt).
    exists index, label. split; first by eapply candidate_position_events.
    split; first done. by rewrite Hindex.
  Qed.

  Lemma thread_at_control_origin P G p t v source :
    thread_at P G p t v ->
    source ∈ thread_control_origins v.(view_thread) ->
    exists index label,
      lookup_event G.(candidate_events) source = Some (EAgent t index label) /\
      is_read (EAgent t index label) /\ index < v.(view_event_index).
  Proof.
    intros Hview Hsource.
    destruct (thread_at_lookup _ _ _ _ _ Hview) as (Hthread & Hindex & _).
    destruct Hview as [Hpos _].
    destruct (candidate_position_generated_wf _ _ _ Hpos) as (_ & Hprov & _).
    destruct (Hprov t _ Hthread) as [_ Hcontrol].
    destruct (Hcontrol source Hsource) as (index & label & Hlookup & Hread & Hlt).
    exists index, label. split; first by eapply candidate_position_events.
    split; first done. by rewrite Hindex.
  Qed.

  (** Pure graph fact only, not a load triple or a transfer of ownership.
      The source is looked up in [G], with NO requirement that it has
      already appeared at the current execution position. *)
  Lemma candidate_position_read_source P G p read read_event :
    program_graph P G -> candidate_position P G p ->
    lookup_event p.(position_state).(core_events) read = Some read_event ->
    is_read read_event ->
    exists write, rf G.(candidate_rf) write read /\
      rf_edge_wf G.(candidate_events) write read /\
      (forall other, rf G.(candidate_rf) other read -> other = write).
  Proof.
    intros Hgraph Hpos Hlookup Hread.
    destruct (program_graph_wf _ _ Hgraph) as (_ & Hrf_wf & _).
    destruct Hrf_wf as (Hedges & Hfunctional & Htotal).
    pose proof (candidate_position_events _ _ _ Hpos _ _ Hlookup) as Hfinal.
    destruct (Htotal read read_event Hfinal Hread) as (write & Hrf).
    exists write. split; first done. split; first by apply Hedges.
    intros other Hother. by eapply Hfunctional.
  Qed.
End LkmmGraphDomain.
