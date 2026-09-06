From Stdlib Require Import Arith List Relations.Relation_Operators.
From stdpp Require Import base gmap sets tactics.
From iris_lkmm.lkmm Require Import memory_relations rcu_graph rcu_mono.
Import ListNotations.

(** Incremental construction of the finite RCU graph kernel.

    A mutation contributes exactly one event, base-relation edge, or direct
    dependency edge.  RCU
    critical sections are recomputed from the canonical event structure.
    Link commitments record witnesses for
    [po? ; hb* ; pb* ; prop ; po] only after their components are present.
    Each raw mutation supplies exact deltas for the five selected LKMM
    consistency checks.  The local obligations reject newly exposed cycles
    in coherence, happens-before, propagation, and RCU [rb], and reject every
    newly exposed atomicity violation.  They do not mention a final candidate
    or invoke a completed-graph consistency predicate. *)
Module RcuBuilder.
  Import LkmmMemoryRelations RcuGraph RcuMono.

  Record labeled_event := LabeledEvent {
    le_id : event_id;
    le_event : event
  }.

  Record raw_graph := RawGraph {
    raw_events : event_structure;
    raw_rf : list edge;
    raw_co : list edge;
    raw_rmw : list edge;
    raw_direct_addr : list edge;
    raw_direct_data : list edge;
    raw_direct_ctrl : list edge
  }.

  Definition graph_of_raw (r : raw_graph) : graph :=
    {|
      events := r.(raw_events);
      rf_edges := list_to_set r.(raw_rf);
      co_edges := list_to_set r.(raw_co);
      rmw_edges := list_to_set r.(raw_rmw);
      direct_addr_edges := list_to_set r.(raw_direct_addr);
      direct_data_edges := list_to_set r.(raw_direct_data);
      direct_ctrl_edges := list_to_set r.(raw_direct_ctrl)
    |}.

  Definition empty_raw : raw_graph := RawGraph ∅ [] [] [] [] [] [].

  Definition add_event (r : raw_graph) (ev : labeled_event) : raw_graph :=
    RawGraph (<[ev.(le_id) := ev.(le_event)]> r.(raw_events))
      r.(raw_rf) r.(raw_co) r.(raw_rmw)
      r.(raw_direct_addr) r.(raw_direct_data) r.(raw_direct_ctrl).

  Definition add_rf (r : raw_graph) (e : edge) : raw_graph :=
    RawGraph r.(raw_events) (e :: r.(raw_rf)) r.(raw_co)
      r.(raw_rmw) r.(raw_direct_addr) r.(raw_direct_data) r.(raw_direct_ctrl).

  Definition add_co (r : raw_graph) (e : edge) : raw_graph :=
    RawGraph r.(raw_events) r.(raw_rf) (e :: r.(raw_co))
      r.(raw_rmw) r.(raw_direct_addr) r.(raw_direct_data) r.(raw_direct_ctrl).

  Definition add_rmw (r : raw_graph) (e : edge) : raw_graph :=
    RawGraph r.(raw_events) r.(raw_rf) r.(raw_co) (e :: r.(raw_rmw))
      r.(raw_direct_addr) r.(raw_direct_data) r.(raw_direct_ctrl).

  Definition add_direct_addr (r : raw_graph) (e : edge) : raw_graph :=
    RawGraph r.(raw_events) r.(raw_rf) r.(raw_co) r.(raw_rmw)
      (e :: r.(raw_direct_addr)) r.(raw_direct_data) r.(raw_direct_ctrl).

  Definition add_direct_data (r : raw_graph) (e : edge) : raw_graph :=
    RawGraph r.(raw_events) r.(raw_rf) r.(raw_co) r.(raw_rmw)
      r.(raw_direct_addr) (e :: r.(raw_direct_data)) r.(raw_direct_ctrl).

  Definition add_direct_ctrl (r : raw_graph) (e : edge) : raw_graph :=
    RawGraph r.(raw_events) r.(raw_rf) r.(raw_co) r.(raw_rmw)
      r.(raw_direct_addr) r.(raw_direct_data) (e :: r.(raw_direct_ctrl)).

  Definition raw_relations_wf (r : raw_graph) : Prop :=
    rf_prefix_wf r.(raw_events) (list_to_set r.(raw_rf)) /\
    co_prefix_wf r.(raw_events) (list_to_set r.(raw_co)) /\
    rmw_prefix_wf r.(raw_events) (list_to_set r.(raw_rmw)) /\
    direct_addr_wf r.(raw_events) (list_to_set r.(raw_direct_addr)) /\
    direct_data_wf r.(raw_events) (list_to_set r.(raw_direct_data)) /\
    direct_ctrl_wf r.(raw_events) (list_to_set r.(raw_direct_ctrl)).

  Inductive raw_step : raw_graph -> raw_graph -> Prop :=
  | RawStepEvent r ev :
      rcu_trace_tail r.(raw_events) ev.(le_id) ev.(le_event) ->
      raw_step r (add_event r ev)
  | RawStepRf r e :
      rf_prefix_wf r.(raw_events) (list_to_set (e :: r.(raw_rf))) ->
      raw_step r (add_rf r e)
  | RawStepCo r e :
      co_prefix_wf r.(raw_events) (list_to_set (e :: r.(raw_co))) ->
      raw_step r (add_co r e)
  | RawStepRmw r e :
      rmw_prefix_wf r.(raw_events) (list_to_set (e :: r.(raw_rmw))) ->
      raw_step r (add_rmw r e)
  | RawStepDirectAddr r e :
      direct_addr_wf r.(raw_events) (list_to_set (e :: r.(raw_direct_addr))) ->
      raw_step r (add_direct_addr r e)
  | RawStepDirectData r e :
      direct_data_wf r.(raw_events) (list_to_set (e :: r.(raw_direct_data))) ->
      raw_step r (add_direct_data r e)
  | RawStepDirectCtrl r e :
      direct_ctrl_wf r.(raw_events) (list_to_set (e :: r.(raw_direct_ctrl))) ->
      raw_step r (add_direct_ctrl r e).

  Inductive raw_run : raw_graph -> raw_graph -> Prop :=
  | RawRunRefl r : raw_run r r
  | RawRunCons r1 r2 r3 :
      raw_step r1 r2 ->
      raw_run r2 r3 ->
      raw_run r1 r3.

  Lemma raw_run_single r r' :
    raw_step r r' -> raw_run r r'.
  Proof. intros Hstep. econstructor; [done | constructor]. Qed.

  Lemma raw_run_trans r1 r2 r3 :
    raw_run r1 r2 -> raw_run r2 r3 -> raw_run r1 r3.
  Proof.
    intros H12 H23. induction H12 as [r | a b c Hstep Hrun IH]; first done.
    econstructor; first done.
    by apply IH.
  Qed.

  Lemma raw_step_graph_le r r' :
    raw_step r r' -> graph_le (graph_of_raw r) (graph_of_raw r').
  Proof.
    intros Hstep. destruct Hstep.
    - constructor; simpl.
      + intros old old_event Hlookup. unfold lookup_event in Hlookup |- *.
        change (r.(raw_events) !! old = Some old_event) in Hlookup.
        change ((<[ev.(le_id) := ev.(le_event)]> r.(raw_events)) !! old =
          Some old_event).
        apply lookup_insert_Some. right. split; last done.
        intros Heq. pose proof (proj1 H) as Hfresh.
        unfold lookup_event in Hfresh. congruence.
      + intros edge Hedge. done.
      + intros edge Hedge. done.
      + intros edge Hedge. done.
      + intros edge Hedge. done.
      + intros edge Hedge. done.
      + intros edge Hedge. done.
      + apply rcu_rscsi_tail_mono. done.
    - constructor; simpl; try unfold event_structure_included, rel_included;
        solve [intros; assumption | intros; right; assumption | set_solver].
    - constructor; simpl; try unfold event_structure_included, rel_included;
        solve [intros; assumption | intros; right; assumption | set_solver].
    - constructor; simpl; try unfold event_structure_included, rel_included;
        solve [intros; assumption | intros; right; assumption | set_solver].
    - constructor; simpl; try unfold event_structure_included, rel_included;
        solve [intros; assumption | intros; right; assumption | set_solver].
    - constructor; simpl; try unfold event_structure_included, rel_included;
        solve [intros; assumption | intros; right; assumption | set_solver].
    - constructor; simpl; try unfold event_structure_included, rel_included;
        solve [intros; assumption | intros; right; assumption | set_solver].
  Qed.

  Lemma raw_run_graph_le r r' :
    raw_run r r' -> graph_le (graph_of_raw r) (graph_of_raw r').
  Proof.
    intros Hrun. induction Hrun.
    - apply graph_le_refl.
    - eapply graph_le_trans; [by eapply raw_step_graph_le | done].
  Qed.

  Lemma empty_raw_relations_wf :
    raw_relations_wf empty_raw.
  Proof.
    unfold raw_relations_wf, empty_raw. cbn. split_and!.
    - apply rf_empty_prefix_wf.
    - apply co_empty_prefix_wf.
    - apply rmw_empty_prefix_wf.
    - apply direct_addr_empty_wf.
    - apply direct_data_empty_wf.
    - apply direct_ctrl_empty_wf.
  Qed.

  Lemma raw_step_preserves_relations_wf r r' :
    raw_relations_wf r -> raw_step r r' -> raw_relations_wf r'.
  Proof.
    intros (Hrf & Hco & Hrmw & Haddr & Hdata & Hctrl) Hstep. destruct Hstep as
      [r ev Htail | r e Hnew | r e Hnew | r e Hnew |
       r e Hnew | r e Hnew | r e Hnew]; simpl in *.
    - pose proof (raw_step_graph_le _ _ (RawStepEvent r ev Htail)) as Hle.
      assert (event_structure_included r.(raw_events) (add_event r ev).(raw_events)) as HE.
      { exact (graph_le_events _ _ Hle). }
      split_and!.
      + by eapply rf_prefix_wf_mono.
      + by eapply co_prefix_wf_mono.
      + by eapply rmw_prefix_wf_mono.
      + by eapply direct_addr_wf_mono.
      + by eapply direct_data_wf_mono.
      + by eapply direct_ctrl_wf_mono.
    - split_and!; done.
    - split_and!; done.
    - split_and!; done.
    - split_and!; done.
    - split_and!; done.
    - split_and!; done.
  Qed.

  Lemma raw_run_preserves_relations_wf r r' :
    raw_relations_wf r -> raw_run r r' -> raw_relations_wf r'.
  Proof.
    intros Hwf Hrun. induction Hrun; first done.
    apply IHHrun. by eapply raw_step_preserves_relations_wf.
  Qed.

  (** An [rcu_link_commitment] makes the existential decomposition of one
      [rcu_link] explicit.  It records the source and target together with
      the four intermediate events witnessing
      [po? ; hb* ; pb* ; prop ; po].  The record contains only event IDs;
      [rcu_link_commitment_valid] states that the recorded path is present in
      a particular graph.  Once valid, the commitment remains valid as the
      graph grows. *)
  Record rcu_link_commitment := RcuLinkCommitment {
    lc_source : event_id;
    lc_optional_po : event_id;
    lc_after_hb : event_id;
    lc_after_pb : event_id;
    lc_after_prop : event_id;
    lc_target : event_id
  }.

  Definition rcu_link_commitment_valid (G : graph) (k : rcu_link_commitment) : Prop :=
    optional (graph_po G) k.(lc_source) k.(lc_optional_po) /\
    rtc (graph_hb G) k.(lc_optional_po) k.(lc_after_hb) /\
    rtc (graph_pb G) k.(lc_after_hb) k.(lc_after_pb) /\
    graph_prop G k.(lc_after_pb) k.(lc_after_prop) /\
    graph_po G k.(lc_after_prop) k.(lc_target).

  Lemma rcu_link_commitment_sound G k :
    rcu_link_commitment_valid G k ->
    rcu_link G k.(lc_source) k.(lc_target).
  Proof.
    intros (Hpo & Hhb & Hpb & Hprop & Hlast).
    exists k.(lc_optional_po), k.(lc_after_hb),
      k.(lc_after_pb), k.(lc_after_prop).
    done.
  Qed.

  Lemma rcu_link_commitment_complete G x y :
    rcu_link G x y ->
    exists k, k.(lc_source) = x /\ k.(lc_target) = y /\
      rcu_link_commitment_valid G k.
  Proof.
    intros (a & b & c & d & Hpo & Hhb & Hpb & Hprop & Hlast).
    exists (RcuLinkCommitment x a b c d y). simpl.
    split_and!; done.
  Qed.

  Lemma rcu_link_commitment_valid_mono G H k :
    graph_le G H -> rcu_link_commitment_valid G k ->
    rcu_link_commitment_valid H k.
  Proof.
    intros GH (Hpo & Hhb & Hpb & Hprop & Hlast).
    split_and!.
    - eapply optional_mono; [by eapply graph_le_po | done].
    - eapply rtc_mono; [by eapply graph_le_hb | done].
    - eapply rtc_mono; [by eapply graph_le_pb | done].
    - by eapply graph_prop_mono.
    - by eapply graph_le_po.
  Qed.

  Record consistency_relations := ConsistencyRelations {
    cr_coherence : relation;
    cr_atomicity : relation;
    cr_happens_before : relation;
    cr_propagation : relation;
    cr_rb : relation
  }.

  Definition graph_consistency_relations (G : graph) : consistency_relations :=
    ConsistencyRelations
      (tc (graph_coherence_order G))
      (graph_atomicity_violation G)
      (tc (graph_hb G))
      (tc (graph_pb G))
      (rb G).

  Definition consistency_relations_union
      (left right : consistency_relations) : consistency_relations :=
    ConsistencyRelations
      (rel_union left.(cr_coherence) right.(cr_coherence))
      (rel_union left.(cr_atomicity) right.(cr_atomicity))
      (rel_union left.(cr_happens_before) right.(cr_happens_before))
      (rel_union left.(cr_propagation) right.(cr_propagation))
      (rel_union left.(cr_rb) right.(cr_rb)).

  Definition consistency_relations_exact
      (G : graph) (seen : consistency_relations) : Prop :=
    (forall x y, seen.(cr_coherence) x y <-> tc (graph_coherence_order G) x y) /\
    (forall x y, seen.(cr_atomicity) x y <-> graph_atomicity_violation G x y) /\
    (forall x y, seen.(cr_happens_before) x y <-> tc (graph_hb G) x y) /\
    (forall x y, seen.(cr_propagation) x y <-> tc (graph_pb G) x y) /\
    (forall x y, seen.(cr_rb) x y <-> rb G x y).

  Definition consistency_delta_exact (new : raw_graph)
      (seen delta : consistency_relations) : Prop :=
    consistency_relations_exact (graph_of_raw new) (consistency_relations_union seen delta).

  Definition consistency_relations_safe (relations : consistency_relations) : Prop :=
    rel_irreflexive relations.(cr_coherence) /\
    rel_is_empty relations.(cr_atomicity) /\
    rel_irreflexive relations.(cr_happens_before) /\
    rel_irreflexive relations.(cr_propagation) /\
    rel_irreflexive relations.(cr_rb).

  Lemma graph_consistency_relations_safe G :
    consistency_relations_safe (graph_consistency_relations G) <-> graph_consistent G.
  Proof.
    unfold consistency_relations_safe, graph_consistency_relations, graph_consistent,
      graph_coherence, graph_atomicity, graph_happens_before, graph_propagation,
      rcu_consistent, rel_acyclic. done.
  Qed.

  Lemma consistency_relations_union_safe left right :
    consistency_relations_safe left -> consistency_relations_safe right ->
    consistency_relations_safe (consistency_relations_union left right).
  Proof.
    intros (Hco1 & Hat1 & Hhb1 & Hpb1 & Hrb1)
      (Hco2 & Hat2 & Hhb2 & Hpb2 & Hrb2).
    unfold consistency_relations_safe, consistency_relations_union. cbn. split_and!.
    - intros eid [Hcycle | Hcycle]; [by apply (Hco1 eid) | by apply (Hco2 eid)].
    - intros source target [Hbad | Hbad]; [by apply (Hat1 source target) |
        by apply (Hat2 source target)].
    - intros eid [Hcycle | Hcycle]; [by apply (Hhb1 eid) | by apply (Hhb2 eid)].
    - intros eid [Hcycle | Hcycle]; [by apply (Hpb1 eid) | by apply (Hpb2 eid)].
    - intros eid [Hcycle | Hcycle]; [by apply (Hrb1 eid) | by apply (Hrb2 eid)].
  Qed.

  Record builder_state := BuilderState {
    bs_raw : raw_graph;
    bs_rcu_links : list rcu_link_commitment;
    bs_seen_consistency : consistency_relations
  }.

  Inductive builder_step : builder_state -> builder_state -> Prop :=
  | BuilderStepRaw r r' links seen delta :
      raw_step r r' ->
      consistency_delta_exact r' seen delta ->
      consistency_relations_safe delta ->
      builder_step
        (BuilderState r links seen)
        (BuilderState r' links (consistency_relations_union seen delta))
  | BuilderStepRcuLink r links seen k :
      rcu_link_commitment_valid (graph_of_raw r) k ->
      builder_step
        (BuilderState r links seen)
        (BuilderState r (k :: links) seen).

  Inductive builder_run : builder_state -> builder_state -> Prop :=
  | BuilderRunRefl s : builder_run s s
  | BuilderRunCons s1 s2 s3 :
      builder_step s1 s2 ->
      builder_run s2 s3 ->
      builder_run s1 s3.

  Definition builder_invariant (s : builder_state) : Prop :=
    consistency_relations_exact (graph_of_raw s.(bs_raw)) s.(bs_seen_consistency) /\
    consistency_relations_safe s.(bs_seen_consistency) /\
    (forall k, In k s.(bs_rcu_links) -> rcu_link_commitment_valid (graph_of_raw s.(bs_raw)) k).

  Definition initial_builder : builder_state :=
    BuilderState empty_raw [] (graph_consistency_relations (graph_of_raw empty_raw)).

  Lemma empty_raw_has_no_rb x y :
    ~ rb (graph_of_raw empty_raw) x y.
  Proof.
    intros Hrb. unfold rb in Hrb.
    apply rel_seq_id_on_r in Hrb as [_ Hmarked].
    unfold graph_marked, graph_of_raw, empty_raw in Hmarked. cbn in Hmarked.
    destruct Hmarked as [Hin _].
    apply in_event_structure_lookup_iff in Hin as (ev & Hlookup).
    inversion Hlookup.
  Qed.

  Local Lemma empty_raw_has_no_coherence_edge x y :
    ~ graph_coherence_order (graph_of_raw empty_raw) x y.
  Proof.
    intros [Hpo | Hcom].
    - destruct Hpo as [(agent & index1 & index2 & label1 & label2 & Hlookup & _) _].
      inversion Hlookup.
    - destruct Hcom as [Hrf | [Hco | Hfr]].
      + unfold rf, edge_relation, graph_of_raw, empty_raw in Hrf. set_solver.
      + unfold co, edge_relation, graph_of_raw, empty_raw in Hco. set_solver.
      + destruct Hfr as (write & Hrf & _).
        unfold rf, edge_relation, graph_of_raw, empty_raw in Hrf. set_solver.
  Qed.

  Local Lemma empty_raw_has_no_marked eid :
    ~ graph_marked (graph_of_raw empty_raw) eid.
  Proof.
    intros [Hin _]. apply in_event_structure_lookup_iff in Hin as (ev & Hlookup).
    inversion Hlookup.
  Qed.

  Local Lemma empty_raw_has_no_hb x y :
    ~ graph_hb (graph_of_raw empty_raw) x y.
  Proof.
    intros Hhb. apply rel_seq_id_on_r in Hhb as [Hprefix _].
    apply rel_seq_id_on_l in Hprefix as [Hmarked _].
    by apply (empty_raw_has_no_marked x).
  Qed.

  Local Lemma empty_raw_has_no_pb x y :
    ~ graph_pb (graph_of_raw empty_raw) x y.
  Proof.
    intros Hpb. apply rel_seq_id_on_r in Hpb as [_ Hmarked].
    by apply (empty_raw_has_no_marked y).
  Qed.

  Local Lemma tc_of_empty_is_empty relation :
    (forall x y, ~ relation x y) -> forall x y, ~ tc relation x y.
  Proof.
    intros Hempty x y Hpath. induction Hpath; [by eapply Hempty | done].
  Qed.

  Lemma empty_raw_graph_consistent :
    graph_consistent (graph_of_raw empty_raw).
  Proof.
    unfold graph_consistent, graph_coherence, graph_atomicity,
      graph_happens_before, graph_propagation, rel_acyclic. split_and!.
    - intros eid. by apply tc_of_empty_is_empty, empty_raw_has_no_coherence_edge.
    - intros source target [Hrmw _].
      unfold rmw, edge_relation, graph_of_raw, empty_raw in Hrmw. set_solver.
    - intros eid. by apply tc_of_empty_is_empty, empty_raw_has_no_hb.
    - intros eid. by apply tc_of_empty_is_empty, empty_raw_has_no_pb.
    - intros eid. by apply empty_raw_has_no_rb.
  Qed.

  Lemma initial_builder_invariant :
    builder_invariant initial_builder.
  Proof.
    unfold builder_invariant, initial_builder. simpl. split_and!.
    - unfold consistency_relations_exact, graph_consistency_relations. cbn.
      split_and!; intros; done.
    - apply graph_consistency_relations_safe, empty_raw_graph_consistent.
    - intros k Hin. inversion Hin.
  Qed.

  Lemma builder_step_preserves_invariant s s' :
    builder_invariant s ->
    builder_step s s' ->
    builder_invariant s'.
  Proof.
    intros (Hexact & Hsafe & Hlinks) Hstep.
    destruct Hstep as
      [r r' links seen delta Hraw Hdelta Hlocal |
       r links seen k Hvalid]; simpl in *.
    - split_and!.
      + exact Hdelta.
      + by apply consistency_relations_union_safe.
      + intros k Hin. eapply rcu_link_commitment_valid_mono.
        * by eapply raw_step_graph_le.
        * by apply Hlinks.
    - split_and!; try done.
      intros k' [-> | Hin]; [done | by apply Hlinks].
  Qed.

  Lemma builder_run_preserves_invariant s s' :
    builder_invariant s ->
    builder_run s s' ->
    builder_invariant s'.
  Proof.
    intros Hinv Hrun. induction Hrun; first done.
    apply IHHrun. by eapply builder_step_preserves_invariant.
  Qed.

  Lemma builder_step_preserves_relations_wf s s' :
    raw_relations_wf s.(bs_raw) ->
    builder_step s s' -> raw_relations_wf s'.(bs_raw).
  Proof.
    intros Hwf Hstep. destruct Hstep as [r r' links seen delta Hraw |]; simpl; last done.
    by eapply raw_step_preserves_relations_wf.
  Qed.

  Lemma builder_run_preserves_relations_wf s s' :
    raw_relations_wf s.(bs_raw) ->
    builder_run s s' -> raw_relations_wf s'.(bs_raw).
  Proof.
    intros Hwf Hrun. induction Hrun; first done.
    apply IHHrun. by eapply builder_step_preserves_relations_wf.
  Qed.

  Theorem builder_run_relations_wf s :
    builder_run initial_builder s -> raw_relations_wf s.(bs_raw).
  Proof.
    apply builder_run_preserves_relations_wf, empty_raw_relations_wf.
  Qed.

  Theorem completed_builder_run_consistent s :
    builder_run initial_builder s ->
    graph_consistent (graph_of_raw s.(bs_raw)).
  Proof.
    intros Hrun.
    pose proof (builder_run_preserves_invariant _ _ initial_builder_invariant
      Hrun) as (Hexact & Hsafe & _).
    apply graph_consistency_relations_safe.
    destruct Hexact as (Hco & Hat & Hhb & Hpb & Hrb).
    destruct Hsafe as (Hco_safe & Hat_safe & Hhb_safe & Hpb_safe & Hrb_safe).
    unfold consistency_relations_safe, graph_consistency_relations. cbn. split_and!.
    - intros eid Hcycle. apply (Hco_safe eid), Hco, Hcycle.
    - intros source target Hbad. apply (Hat_safe source target), Hat, Hbad.
    - intros eid Hcycle. apply (Hhb_safe eid), Hhb, Hcycle.
    - intros eid Hcycle. apply (Hpb_safe eid), Hpb, Hcycle.
    - intros eid Hcycle. apply (Hrb_safe eid), Hrb, Hcycle.
  Qed.

  Theorem committed_rcu_links_are_sound s k :
    builder_run initial_builder s ->
    In k s.(bs_rcu_links) ->
    rcu_link (graph_of_raw s.(bs_raw))
      k.(lc_source) k.(lc_target).
  Proof.
    intros Hrun Hin.
    apply rcu_link_commitment_sound.
    pose proof (builder_run_preserves_invariant _ _ initial_builder_invariant
      Hrun) as (_ & _ & Hlinks).
    by apply Hlinks.
  Qed.

  Theorem commit_ready_rcu_link s k :
    rcu_link_commitment_valid (graph_of_raw s.(bs_raw)) k ->
    exists s', builder_step s s' /\ In k s'.(bs_rcu_links).
  Proof.
    destruct s as [r links seen]. simpl.
    intros Hvalid. exists (BuilderState r (k :: links) seen).
    split; [by constructor | by left].
  Qed.

End RcuBuilder.
