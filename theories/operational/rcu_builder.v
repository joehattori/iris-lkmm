From Stdlib Require Import Arith List Relations.Relation_Operators.
From stdpp Require Import base gmap sets tactics.
From iris_lkmm.lkmm Require Import rcu_graph rcu_mono.
Import ListNotations.

(** Incremental construction of the finite RCU graph kernel.

    A mutation contributes exactly one event or finite/base-relation edge.  RCU
    critical sections are recomputed from the canonical event structure.
    Link commitments record witnesses for
    [po? ; hb* ; pb* ; prop ; po] only after their components are present.
    The [rb_delta] premise is a local monitor obligation: it describes the
    newly exposed [rb] pairs and rejects only reflexive new pairs.  It does
    not mention a final candidate or [rcu_consistent]. *)
Module RcuBuilder.
  Import RcuGraph RcuMono.

  Record labeled_event := LabeledEvent {
    le_id : event_id;
    le_event : event
  }.

  Definition edge_rel (edges : list edge) : relation := fun x y => In (x, y) edges.

  Record raw_graph := RawGraph {
    raw_events : event_structure;
    raw_rf : list edge;
    raw_co : list edge;
    raw_hb : list edge;
    raw_prop : list edge;
    raw_pb : list edge
  }.

  Definition graph_of_raw (r : raw_graph) : graph :=
    {|
      events := r.(raw_events);
      rf_edges := list_to_set r.(raw_rf);
      co_edges := list_to_set r.(raw_co);
      hb := edge_rel r.(raw_hb);
      prop := edge_rel r.(raw_prop);
      pb := edge_rel r.(raw_pb)
    |}.

  Definition empty_raw : raw_graph := RawGraph ∅ [] [] [] [] [].

  Definition add_event (r : raw_graph) (ev : labeled_event) : raw_graph :=
    RawGraph (<[ev.(le_id) := ev.(le_event)]> r.(raw_events))
      r.(raw_rf) r.(raw_co) r.(raw_hb) r.(raw_prop) r.(raw_pb).

  Definition add_rf (r : raw_graph) (e : edge) : raw_graph :=
    RawGraph r.(raw_events) (e :: r.(raw_rf)) r.(raw_co)
      r.(raw_hb) r.(raw_prop) r.(raw_pb).

  Definition add_co (r : raw_graph) (e : edge) : raw_graph :=
    RawGraph r.(raw_events) r.(raw_rf) (e :: r.(raw_co))
      r.(raw_hb) r.(raw_prop) r.(raw_pb).

  Definition add_hb (r : raw_graph) (e : edge) : raw_graph :=
    RawGraph r.(raw_events) r.(raw_rf) r.(raw_co)
      (e :: r.(raw_hb)) r.(raw_prop) r.(raw_pb).

  Definition add_prop (r : raw_graph) (e : edge) : raw_graph :=
    RawGraph r.(raw_events) r.(raw_rf) r.(raw_co)
      r.(raw_hb) (e :: r.(raw_prop)) r.(raw_pb).

  Definition add_pb (r : raw_graph) (e : edge) : raw_graph :=
    RawGraph r.(raw_events) r.(raw_rf) r.(raw_co)
      r.(raw_hb) r.(raw_prop) (e :: r.(raw_pb)).

  Inductive raw_step : raw_graph -> raw_graph -> Prop :=
  | RawStepEvent r ev :
      rcu_trace_tail r.(raw_events) ev.(le_id) ev.(le_event) ->
      raw_step r (add_event r ev)
  | RawStepRf r e : raw_step r (add_rf r e)
  | RawStepCo r e : raw_step r (add_co r e)
  | RawStepHb r e : raw_step r (add_hb r e)
  | RawStepProp r e : raw_step r (add_prop r e)
  | RawStepPb r e : raw_step r (add_pb r e).

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
      + unfold rel_included, edge_rel. done.
      + unfold rel_included, edge_rel. done.
      + unfold rel_included, edge_rel. done.
      + apply rcu_rscsi_tail_mono. done.
    - constructor; simpl; try unfold rel_included; try unfold edge_rel;
        solve [intros; assumption | intros; right; assumption | set_solver].
    - constructor; simpl; try unfold rel_included; try unfold edge_rel;
        solve [intros; assumption | intros; right; assumption | set_solver].
    - constructor; simpl; try unfold rel_included; try unfold edge_rel;
        solve [intros; assumption | intros; right; assumption | set_solver].
    - constructor; simpl; try unfold rel_included; try unfold edge_rel;
        solve [intros; assumption | intros; right; assumption | set_solver].
    - constructor; simpl; try unfold rel_included; try unfold edge_rel;
        solve [intros; assumption | intros; right; assumption | set_solver].
  Qed.

  Lemma raw_run_graph_le r r' :
    raw_run r r' -> graph_le (graph_of_raw r) (graph_of_raw r').
  Proof.
    intros Hrun. induction Hrun.
    - apply graph_le_refl.
    - eapply graph_le_trans; [by eapply raw_step_graph_le | done].
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
    rtc G.(hb) k.(lc_optional_po) k.(lc_after_hb) /\
    rtc G.(pb) k.(lc_after_hb) k.(lc_after_pb) /\
    G.(prop) k.(lc_after_pb) k.(lc_after_prop) /\
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
    - by eapply graph_le_prop.
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
    apply rel_seq_id_on_r in Hrb as [Hprefix _].
    destruct Hprefix as (c & (b & (a & Hprop & _) & _) & _).
    inversion Hprop.
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
