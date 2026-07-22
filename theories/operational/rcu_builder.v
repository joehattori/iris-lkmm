From Stdlib Require Import Arith List Relations.Relation_Operators.
From stdpp Require Import base tactics.
From iris_lkmm.lkmm Require Import rcu_graph rcu_mono.
Import ListNotations.

(** Incremental construction of the finite RCU graph kernel.

    A mutation contributes exactly one event, base-relation edge, or matched
    critical section.  Link commitments record witnesses for
    [po? ; hb* ; pb* ; prop ; po] only after their components are present.
    The [rb_delta] premise is a local monitor obligation: it describes the
    newly exposed [rb] pairs and rejects only reflexive new pairs.  It does
    not mention a final candidate or [rcu_consistent]. *)
Module RcuBuilder.
  Import RcuGraph RcuMono.

  Record labeled_event := LabeledEvent {
    le_id : event_id;
    le_label : label
  }.

  Definition edge := (event_id * event_id)%type.

  Fixpoint lookup_label (evs : list labeled_event) (e : event_id) : label :=
    match evs with
    | [] => LRead
    | ev :: evs' =>
        if Nat.eq_dec ev.(le_id) e then ev.(le_label)
        else lookup_label evs' e
    end.

  Definition edge_rel (edges : list edge) : relation :=
    fun x y => In (x, y) edges.

  Record raw_graph := RawGraph {
    raw_events : list labeled_event;
    raw_po : list edge;
    raw_hb : list edge;
    raw_prop : list edge;
    raw_pb : list edge;
    raw_sections : list critical_section
  }.

  Definition graph_of_raw (r : raw_graph) : graph :=
    Graph (map le_id r.(raw_events)) (lookup_label r.(raw_events))
      (edge_rel r.(raw_po)) (edge_rel r.(raw_hb))
      (edge_rel r.(raw_prop)) (edge_rel r.(raw_pb))
      r.(raw_sections).

  Definition empty_raw : raw_graph :=
    RawGraph [] [] [] [] [] [].

  Definition add_event (r : raw_graph) (ev : labeled_event) : raw_graph :=
    RawGraph (ev :: r.(raw_events)) r.(raw_po) r.(raw_hb)
      r.(raw_prop) r.(raw_pb) r.(raw_sections).

  Definition add_po (r : raw_graph) (e : edge) : raw_graph :=
    RawGraph r.(raw_events) (e :: r.(raw_po)) r.(raw_hb)
      r.(raw_prop) r.(raw_pb) r.(raw_sections).

  Definition add_hb (r : raw_graph) (e : edge) : raw_graph :=
    RawGraph r.(raw_events) r.(raw_po) (e :: r.(raw_hb))
      r.(raw_prop) r.(raw_pb) r.(raw_sections).

  Definition add_prop (r : raw_graph) (e : edge) : raw_graph :=
    RawGraph r.(raw_events) r.(raw_po) r.(raw_hb)
      (e :: r.(raw_prop)) r.(raw_pb) r.(raw_sections).

  Definition add_pb (r : raw_graph) (e : edge) : raw_graph :=
    RawGraph r.(raw_events) r.(raw_po) r.(raw_hb)
      r.(raw_prop) (e :: r.(raw_pb)) r.(raw_sections).

  Definition add_section (r : raw_graph)
      (cs : critical_section) : raw_graph :=
    RawGraph r.(raw_events) r.(raw_po) r.(raw_hb)
      r.(raw_prop) r.(raw_pb) (cs :: r.(raw_sections)).

  Inductive raw_step : raw_graph -> raw_graph -> Prop :=
  | RawStepEvent r ev :
      ~ In ev.(le_id) (map le_id r.(raw_events)) ->
      raw_step r (add_event r ev)
  | RawStepPo r e : raw_step r (add_po r e)
  | RawStepHb r e : raw_step r (add_hb r e)
  | RawStepProp r e : raw_step r (add_prop r e)
  | RawStepPb r e : raw_step r (add_pb r e)
  | RawStepSection r cs : raw_step r (add_section r cs).

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
    intros H12 H23. induction H12 as [r | a b c Hstep Hrun IH].
    - done.
    - econstructor; [done | by apply IH].
  Qed.

  Lemma lookup_label_fresh ev evs e :
    ev.(le_id) <> e ->
    lookup_label (ev :: evs) e = lookup_label evs e.
  Proof.
    intros Hneq. simpl. destruct (Nat.eq_dec ev.(le_id) e); congruence.
  Qed.

  Lemma old_id_neq_fresh ev evs e :
    ~ In ev.(le_id) (map le_id evs) ->
    In e (map le_id evs) ->
    ev.(le_id) <> e.
  Proof.
    intros Hfresh Hin Heq. apply Hfresh. by rewrite Heq.
  Qed.

  Lemma raw_step_graph_le r r' :
    raw_step r r' -> graph_le (graph_of_raw r) (graph_of_raw r').
  Proof.
    intros Hstep. destruct Hstep.
    - constructor; simpl.
      + intros old Hold. by right.
      + intros old [Hin Hlabel]. split; first by right.
        change (lookup_label (ev :: r.(raw_events)) old = LSyncRcu).
        rewrite lookup_label_fresh; first done.
        by eapply old_id_neq_fresh.
      + intros old [Hin Hlabel]. split; first by right.
        change (lookup_label (ev :: r.(raw_events)) old = LRead \/
          lookup_label (ev :: r.(raw_events)) old = LWrite).
        rewrite lookup_label_fresh; first done.
        by eapply old_id_neq_fresh.
      + unfold rel_included, edge_rel. intros x y Hxy. done.
      + unfold rel_included, edge_rel. intros x y Hxy. done.
      + unfold rel_included, edge_rel. intros x y Hxy. done.
      + unfold rel_included, edge_rel. intros x y Hxy. done.
      + intros cs Hcs. done.
    - constructor; simpl; try unfold rel_included; try unfold edge_rel;
        solve [intros; assumption | intros; right; assumption].
    - constructor; simpl; try unfold rel_included; try unfold edge_rel;
        solve [intros; assumption | intros; right; assumption].
    - constructor; simpl; try unfold rel_included; try unfold edge_rel;
        solve [intros; assumption | intros; right; assumption].
    - constructor; simpl; try unfold rel_included; try unfold edge_rel;
        solve [intros; assumption | intros; right; assumption].
    - constructor; simpl; try unfold rel_included; try unfold edge_rel;
        solve [intros; assumption | intros; right; assumption].
  Qed.

  Lemma raw_run_graph_le r r' :
    raw_run r r' -> graph_le (graph_of_raw r) (graph_of_raw r').
  Proof.
    intros Hrun. induction Hrun.
    - apply graph_le_refl.
    - eapply graph_le_trans; [by eapply raw_step_graph_le | done].
  Qed.

  Record link_commitment := LinkCommitment {
    lc_source : event_id;
    lc_optional_po : event_id;
    lc_after_hb : event_id;
    lc_after_pb : event_id;
    lc_after_prop : event_id;
    lc_target : event_id
  }.

  Definition link_valid (G : graph) (k : link_commitment) : Prop :=
    optional G.(po) k.(lc_source) k.(lc_optional_po) /\
    rtc G.(hb) k.(lc_optional_po) k.(lc_after_hb) /\
    rtc G.(pb) k.(lc_after_hb) k.(lc_after_pb) /\
    G.(prop) k.(lc_after_pb) k.(lc_after_prop) /\
    G.(po) k.(lc_after_prop) k.(lc_target).

  Lemma link_valid_sound G k :
    link_valid G k -> rcu_link G k.(lc_source) k.(lc_target).
  Proof.
    intros (Hpo & Hhb & Hpb & Hprop & Hlast).
    exists k.(lc_optional_po), k.(lc_after_hb),
      k.(lc_after_pb), k.(lc_after_prop).
    done.
  Qed.

  Lemma link_valid_complete G x y :
    rcu_link G x y ->
    exists k, k.(lc_source) = x /\ k.(lc_target) = y /\ link_valid G k.
  Proof.
    intros (a & b & c & d & Hpo & Hhb & Hpb & Hprop & Hlast).
    exists (LinkCommitment x a b c d y). simpl.
    repeat split; done.
  Qed.

  Lemma link_valid_mono G H k :
    graph_le G H -> link_valid G k -> link_valid H k.
  Proof.
    intros GH (Hpo & Hhb & Hpb & Hprop & Hlast).
    repeat split.
    - eapply optional_mono; [by eapply graph_le_po | done].
    - eapply rtc_mono; [by eapply graph_le_hb | done].
    - eapply rtc_mono; [by eapply graph_le_pb | done].
    - by eapply graph_le_prop.
    - by eapply graph_le_po.
  Qed.

  Record builder_state := BuilderState {
    bs_raw : raw_graph;
    bs_links : list link_commitment;
    bs_seen_rb : relation
  }.

  Definition rb_delta_exact (old new : raw_graph)
      (seen delta : relation) : Prop :=
    forall x y,
      rb (graph_of_raw new) x y <-> seen x y \/ delta x y.

  Definition locally_safe (delta : relation) : Prop :=
    forall e, ~ delta e e.

  Inductive builder_step : builder_state -> builder_state -> Prop :=
  | BuilderStepRaw r r' links seen delta :
      raw_step r r' ->
      rb_delta_exact r r' seen delta ->
      locally_safe delta ->
      builder_step
        (BuilderState r links seen)
        (BuilderState r' links (fun x y => seen x y \/ delta x y))
  | BuilderStepLink r links seen k :
      link_valid (graph_of_raw r) k ->
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
    (forall x y, s.(bs_seen_rb) x y <->
      rb (graph_of_raw s.(bs_raw)) x y) /\
    (forall e, ~ s.(bs_seen_rb) e e) /\
    (forall k, In k s.(bs_links) ->
      link_valid (graph_of_raw s.(bs_raw)) k).

  Definition initial_builder : builder_state :=
    BuilderState empty_raw [] (fun _ _ => False).

  Lemma empty_raw_has_no_rb x y :
    ~ rb (graph_of_raw empty_raw) x y.
  Proof. intros (a & b & c & d & Hprop & _). inversion Hprop. Qed.

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
    - split.
      + intros x y. symmetry. by apply Hdelta.
      + split.
        * intros e [Hold | Hnew].
          -- by apply (Hsafe e).
          -- by apply (Hlocal e).
        * intros k Hin. eapply link_valid_mono.
          -- by eapply raw_step_graph_le.
          -- by apply Hlinks.
    - split; first done.
      split; first done.
      intros k' [-> | Hin]; [done | by apply Hlinks].
  Qed.

  Lemma builder_run_preserves_invariant s s' :
    builder_invariant s ->
    builder_run s s' ->
    builder_invariant s'.
  Proof.
    intros Hinv Hrun. induction Hrun.
    - done.
    - apply IHHrun. by eapply builder_step_preserves_invariant.
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

  Theorem committed_links_are_sound s k :
    builder_run initial_builder s ->
    In k s.(bs_links) ->
    rcu_link (graph_of_raw s.(bs_raw))
      k.(lc_source) k.(lc_target).
  Proof.
    intros Hrun Hin.
    apply link_valid_sound.
    pose proof (builder_run_preserves_invariant _ _ initial_builder_invariant
      Hrun) as (_ & _ & Hlinks).
    by apply Hlinks.
  Qed.

  Theorem commit_ready_link s k :
    link_valid (graph_of_raw s.(bs_raw)) k ->
    exists s', builder_step s s' /\ In k s'.(bs_links).
  Proof.
    destruct s as [r links seen]. simpl.
    intros Hvalid. exists (BuilderState r (k :: links) seen).
    split; [by constructor | by left].
  Qed.

End RcuBuilder.
