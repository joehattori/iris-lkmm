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
    The [rb_delta] premise is a local monitor obligation: it describes the
    newly exposed [rb] pairs and rejects only reflexive new pairs.  It does
    not mention a final candidate or [rcu_consistent]. *)
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

  Record builder_state := BuilderState {
    bs_raw : raw_graph;
    bs_rcu_links : list rcu_link_commitment;
    bs_seen_rb : relation
  }.

  Definition rb_delta_exact (old new : raw_graph) (seen delta : relation) : Prop :=
    forall x y, rb (graph_of_raw new) x y <-> seen x y \/ delta x y.

  Definition locally_safe (delta : relation) : Prop := forall e, ~ delta e e.

  Inductive builder_step : builder_state -> builder_state -> Prop :=
  | BuilderStepRaw r r' links seen delta :
      raw_step r r' ->
      rb_delta_exact r r' seen delta ->
      locally_safe delta ->
      builder_step
        (BuilderState r links seen)
        (BuilderState r' links (fun x y => seen x y \/ delta x y))
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
    (forall x y, s.(bs_seen_rb) x y <-> rb (graph_of_raw s.(bs_raw)) x y) /\
    (forall e, ~ s.(bs_seen_rb) e e) /\
    (forall k, In k s.(bs_rcu_links) -> rcu_link_commitment_valid (graph_of_raw s.(bs_raw)) k).

  Definition initial_builder : builder_state := BuilderState empty_raw [] (fun _ _ => False).

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

  Lemma initial_builder_invariant :
    builder_invariant initial_builder.
  Proof.
    unfold builder_invariant, initial_builder. simpl.
    split.
    - intros x y. split; [contradiction | by intros H; exfalso; eapply empty_raw_has_no_rb].
    - split.
      + intros e Hfalse. done.
      + intros k Hin. inversion Hin.
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
      + intros x y. symmetry. by apply Hdelta.
      + intros e [Hold | Hnew].
        * by apply (Hsafe e).
        * by apply (Hlocal e).
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

  Theorem completed_builder_run_rb_irreflexive s :
    builder_run initial_builder s ->
    rcu_consistent (graph_of_raw s.(bs_raw)).
  Proof.
    intros Hrun e Hrb.
    pose proof (builder_run_preserves_invariant _ _ initial_builder_invariant
      Hrun) as (Hexact & Hsafe & _).
    apply (Hsafe e). by apply Hexact.
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
