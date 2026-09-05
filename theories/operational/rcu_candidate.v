From Stdlib Require Import Arith Classical List.
From stdpp Require Import base fin_map_dom gmap sets tactics.
From iris_lkmm.lkmm Require Import memory_relations rcu_graph rcu_mono.
From iris_lkmm.operational Require Import rcu_builder.
Import ListNotations.

(** Declarative finite candidates and scheduling completeness.

    [finite_candidate] contains graph data only.  In particular, it contains
    no builder state, transition sequence, delta monitor, or schedule.  The
    completeness theorem starts from the single constant [initial_builder]
    and constructs the candidate one component at a time. *)
Module RcuCandidate.
  Import LkmmMemoryRelations RcuGraph RcuMono RcuBuilder.

  Definition edge_endpoints_in (ids : list event_id) (edges : list edge) : Prop :=
    forall x y, In (x, y) edges -> In x ids /\ In y ids.

  Record finite_candidate := FiniteCandidate {
    fc_events : list labeled_event;
    fc_rf : list edge;
    fc_co : list edge;
    fc_rmw : list edge;
    fc_hb : list edge;
    fc_pb : list edge
  }.

  Fixpoint load_events (evs : list labeled_event) : raw_graph :=
    match evs with
    | [] => empty_raw
    | ev :: evs' => add_event (load_events evs') ev
    end.

  (** Candidate event lists are stored in reverse loading order.  Each event
      must extend the already-loaded suffix after its canonical RCU token
      trace; non-RCU events impose no additional ordering condition. *)
  Fixpoint events_in_canonical_order (evs : list labeled_event) : Prop :=
    match evs with
    | [] => True
    | ev :: evs' =>
        events_in_canonical_order evs' /\
        rcu_trace_tail (load_events evs').(raw_events) ev.(le_id) ev.(le_event)
    end.

  Definition candidate_well_formed (C : finite_candidate) : Prop :=
    NoDup (map le_id C.(fc_events)) /\
    events_in_canonical_order C.(fc_events) /\
    event_structure_wf (load_events C.(fc_events)).(raw_events) /\
    rcu_matching_complete (load_events C.(fc_events)).(raw_events) /\
    rf_prefix_wf (load_events C.(fc_events)).(raw_events) (list_to_set C.(fc_rf)) /\
    co_prefix_wf (load_events C.(fc_events)).(raw_events) (list_to_set C.(fc_co)) /\
    rmw_prefix_wf (load_events C.(fc_events)).(raw_events) (list_to_set C.(fc_rmw)) /\
    edge_endpoints_in (map le_id C.(fc_events)) C.(fc_hb) /\
    edge_endpoints_in (map le_id C.(fc_events)) C.(fc_pb).

  Fixpoint load_rf (edges : list edge) (r : raw_graph) : raw_graph :=
    match edges with
    | [] => r
    | e :: edges' => add_rf (load_rf edges' r) e
    end.

  Fixpoint load_co (edges : list edge) (r : raw_graph) : raw_graph :=
    match edges with
    | [] => r
    | e :: edges' => add_co (load_co edges' r) e
    end.

  Fixpoint load_rmw (edges : list edge) (r : raw_graph) : raw_graph :=
    match edges with
    | [] => r
    | e :: edges' => add_rmw (load_rmw edges' r) e
    end.

  Fixpoint load_hb (edges : list edge) (r : raw_graph) : raw_graph :=
    match edges with
    | [] => r
    | e :: edges' => add_hb (load_hb edges' r) e
    end.

  Fixpoint load_pb (edges : list edge) (r : raw_graph) : raw_graph :=
    match edges with
    | [] => r
    | e :: edges' => add_pb (load_pb edges' r) e
    end.

  Lemma load_rf_events edges r :
    (load_rf edges r).(raw_events) = r.(raw_events).
  Proof. induction edges; simpl; done. Qed.

  Lemma load_co_events edges r :
    (load_co edges r).(raw_events) = r.(raw_events).
  Proof. induction edges; simpl; done. Qed.

  Lemma load_rmw_events edges r :
    (load_rmw edges r).(raw_events) = r.(raw_events).
  Proof. induction edges; simpl; done. Qed.

  Lemma load_hb_events edges r :
    (load_hb edges r).(raw_events) = r.(raw_events).
  Proof. induction edges; simpl; done. Qed.

  Lemma load_pb_events edges r :
    (load_pb edges r).(raw_events) = r.(raw_events).
  Proof. induction edges; simpl; done. Qed.

  Lemma load_events_relations evs :
    (load_events evs).(raw_rf) = [] /\
    (load_events evs).(raw_co) = [] /\
    (load_events evs).(raw_rmw) = [].
  Proof. induction evs; simpl; done. Qed.

  Lemma load_rf_edges edges r :
    r.(raw_rf) = [] -> (load_rf edges r).(raw_rf) = edges.
  Proof. induction edges; simpl; intros; [done | by rewrite IHedges]. Qed.

  Lemma load_rf_other edges r :
    (load_rf edges r).(raw_co) = r.(raw_co) /\
    (load_rf edges r).(raw_rmw) = r.(raw_rmw).
  Proof. induction edges; simpl; done. Qed.

  Lemma load_co_edges edges r :
    r.(raw_co) = [] -> (load_co edges r).(raw_co) = edges.
  Proof. induction edges; simpl; intros; [done | by rewrite IHedges]. Qed.

  Lemma load_co_rmw edges r :
    (load_co edges r).(raw_rmw) = r.(raw_rmw).
  Proof. induction edges; simpl; done. Qed.

  Lemma load_rmw_edges edges r :
    r.(raw_rmw) = [] -> (load_rmw edges r).(raw_rmw) = edges.
  Proof. induction edges; simpl; intros; [done | by rewrite IHedges]. Qed.

  Definition candidate_raw (C : finite_candidate) : raw_graph :=
    load_pb C.(fc_pb)
      (load_hb C.(fc_hb)
        (load_rmw C.(fc_rmw)
          (load_co C.(fc_co)
            (load_rf C.(fc_rf) (load_events C.(fc_events)))))).

  Lemma candidate_raw_events C :
    (candidate_raw C).(raw_events) = (load_events C.(fc_events)).(raw_events).
  Proof.
    unfold candidate_raw.
    rewrite load_pb_events, load_hb_events, load_rmw_events,
      load_co_events, load_rf_events. done.
  Qed.

  Definition candidate_graph (C : finite_candidate) : graph := graph_of_raw (candidate_raw C).

  Lemma load_events_schedule evs :
    events_in_canonical_order evs ->
    raw_run empty_raw (load_events evs).
  Proof.
    induction evs as [|ev evs IH]; intros Horder; first constructor.
    destruct Horder as [Horder Htail].
    eapply raw_run_trans.
    - by apply IH.
    - apply raw_run_single. by apply RawStepEvent.
  Qed.

  Lemma load_rf_schedule edges r :
    r.(raw_rf) = [] ->
    rf_prefix_wf r.(raw_events) (list_to_set edges) ->
    raw_run r (load_rf edges r).
  Proof.
    intros Hempty Hwf. induction edges as [|e edges IH]; simpl; first constructor.
    assert (rf_prefix_wf r.(raw_events) (list_to_set edges)) as Htail.
    { eapply rf_prefix_wf_subset; last exact Hwf. set_solver. }
    eapply raw_run_trans; first by apply IH.
    apply raw_run_single, RawStepRf.
    rewrite load_rf_events, (load_rf_edges edges r Hempty). exact Hwf.
  Qed.

  Lemma load_co_schedule edges r :
    r.(raw_co) = [] ->
    co_prefix_wf r.(raw_events) (list_to_set edges) ->
    raw_run r (load_co edges r).
  Proof.
    intros Hempty Hwf. induction edges as [|e edges IH]; simpl; first constructor.
    assert (co_prefix_wf r.(raw_events) (list_to_set edges)) as Htail.
    { eapply co_prefix_wf_subset; last exact Hwf. set_solver. }
    eapply raw_run_trans; first by apply IH.
    apply raw_run_single, RawStepCo.
    rewrite load_co_events, (load_co_edges edges r Hempty). exact Hwf.
  Qed.

  Lemma load_rmw_schedule edges r :
    r.(raw_rmw) = [] ->
    rmw_prefix_wf r.(raw_events) (list_to_set edges) ->
    raw_run r (load_rmw edges r).
  Proof.
    intros Hempty Hwf. induction edges as [|e edges IH]; simpl; first constructor.
    assert (rmw_prefix_wf r.(raw_events) (list_to_set edges)) as Htail.
    { eapply rmw_prefix_wf_subset; last exact Hwf. set_solver. }
    eapply raw_run_trans; first by apply IH.
    apply raw_run_single, RawStepRmw.
    rewrite load_rmw_events, (load_rmw_edges edges r Hempty). exact Hwf.
  Qed.

  Lemma load_hb_schedule edges r :
    raw_run r (load_hb edges r).
  Proof.
    induction edges as [|e edges IH]; simpl; first constructor.
    eapply raw_run_trans; first apply IH.
    apply raw_run_single. apply RawStepHb.
  Qed.

  Lemma load_pb_schedule edges r :
    raw_run r (load_pb edges r).
  Proof.
    induction edges as [|e edges IH]; simpl; first constructor.
    eapply raw_run_trans; first apply IH.
    apply raw_run_single. apply RawStepPb.
  Qed.

  Theorem candidate_has_raw_schedule C :
    candidate_well_formed C ->
    raw_run empty_raw (candidate_raw C).
  Proof.
    intros (_ & Horder & _ & _ & Hrf & Hco & Hrmw & _).
    pose proof (load_events_relations C.(fc_events)) as (Hempty_rf & Hempty_co & Hempty_rmw).
    unfold candidate_raw.
    eapply raw_run_trans; first by apply load_events_schedule.
    eapply raw_run_trans.
    { apply load_rf_schedule; done. }
    eapply raw_run_trans.
    { apply load_co_schedule.
      - by rewrite (proj1 (load_rf_other C.(fc_rf) (load_events C.(fc_events)))).
      - by rewrite load_rf_events. }
    eapply raw_run_trans.
    { apply load_rmw_schedule.
      - rewrite load_co_rmw, (proj2 (load_rf_other C.(fc_rf)
          (load_events C.(fc_events)))). done.
      - by rewrite load_co_events, load_rf_events. }
    eapply raw_run_trans; first apply load_hb_schedule.
    apply load_pb_schedule.
  Qed.

  Definition rb_difference (old new : raw_graph) : relation :=
    fun x y =>
      rb (graph_of_raw new) x y /\
      ~ rb (graph_of_raw old) x y.

  Lemma rb_difference_exact old new seen :
    graph_le (graph_of_raw old) (graph_of_raw new) ->
    (forall x y, seen x y <-> rb (graph_of_raw old) x y) ->
    rb_delta_exact old new seen (rb_difference old new).
  Proof.
    intros Hle Hexact x y. split.
    - intros Hnew.
      destruct (classic (rb (graph_of_raw old) x y)) as [Hold | Hnot].
      + left. by apply Hexact.
      + right. by split.
    - intros [Hseen | (Hnew & _)]; last done.
      eapply rb_mono; first done.
      by apply Hexact.
  Qed.

  Lemma rb_difference_locally_safe old new final :
    raw_run new final ->
    rcu_consistent (graph_of_raw final) ->
    locally_safe (rb_difference old new).
  Proof.
    intros Hsuffix Hconsistent e (Hnew & _).
    apply (Hconsistent e).
    eapply rb_mono; last done.
    by eapply raw_run_graph_le.
  Qed.

  Lemma builder_run_trans s1 s2 s3 :
    builder_run s1 s2 -> builder_run s2 s3 -> builder_run s1 s3.
  Proof.
    intros H12 H23. induction H12 as
      [s | a b c Hstep Hrun IH]; first done.
    econstructor; [done | by apply IH].
  Qed.

  Lemma lift_safe_raw_schedule r final s :
    s.(bs_raw) = r ->
    builder_invariant s ->
    raw_run r final ->
    rcu_consistent (graph_of_raw final) ->
    exists s',
      builder_run s s' /\
      s'.(bs_raw) = final /\
      builder_invariant s'.
  Proof.
    intros Hraw Hinv Hrun.
    revert s Hraw Hinv.
    induction Hrun as
      [r | r r' final Hstep Hsuffix IH];
      intros s Hraw Hinv Hconsistent.
    - exists s. split; first constructor.
      split; done.
    - destruct s as [current links seen]. simpl in Hraw. subst current.
      pose (delta := rb_difference r r').
      pose (next := BuilderState r' links
        (fun x y => seen x y \/ delta x y)).
      assert (Hbuilder : builder_step
          (BuilderState r links seen) next).
      { unfold next. apply BuilderStepRaw; first done.
        - unfold delta. apply rb_difference_exact.
          + by apply raw_step_graph_le.
          + by destruct Hinv as (Hexact & _).
        - unfold delta. by eapply rb_difference_locally_safe.
      }
      assert (Hnext : builder_invariant next).
      { by eapply builder_step_preserves_invariant. }
      destruct (IH next eq_refl Hnext Hconsistent)
        as (s' & Hrest & Hfinal & Hinvariant).
      exists s'. split.
      + by econstructor.
      + split; done.
  Qed.

  (** Finite scheduling completeness for the RCU graph kernel.  The only
      builder state in the premise is the fixed empty [initial_builder];
      [C] is used by the meta-level existence proof to choose successive
      locally safe mutations, never stored in the initial state. *)
  Theorem consistent_candidate_is_incrementally_schedulable C :
    candidate_well_formed C ->
    rcu_consistent (candidate_graph C) ->
    exists s,
      builder_run initial_builder s /\
      s.(bs_raw) = candidate_raw C /\
      graph_of_raw s.(bs_raw) = candidate_graph C.
  Proof.
    intros Hwf Hconsistent.
    pose proof (candidate_has_raw_schedule C Hwf) as Hschedule.
    destruct (lift_safe_raw_schedule empty_raw (candidate_raw C)
      initial_builder eq_refl initial_builder_invariant
      Hschedule Hconsistent) as (s & Hrun & Hraw & _).
    exists s. split_and!; try done.
    by rewrite Hraw.
  Qed.

  (** Any link present in a scheduled candidate has an explicit witness that
      can be committed by one further local step. *)
  Theorem scheduled_candidate_rcu_link_can_be_committed C s x y :
    builder_run initial_builder s ->
    s.(bs_raw) = candidate_raw C ->
    rcu_link (candidate_graph C) x y ->
    exists k s',
      builder_run initial_builder s' /\
      In k s'.(bs_rcu_links) /\
      k.(lc_source) = x /\
      k.(lc_target) = y.
  Proof.
    intros Hrun Hraw Hlink.
    destruct (rcu_link_commitment_complete (candidate_graph C) x y Hlink)
      as (k & Hsource & Htarget & Hvalid).
    assert (Hvalid' :
      rcu_link_commitment_valid (graph_of_raw s.(bs_raw)) k).
    { by rewrite Hraw. }
    destruct (commit_ready_rcu_link s k Hvalid') as (s' & Hstep & Hin).
    exists k, s'. split_and!; try done.
    eapply builder_run_trans; first done.
    econstructor; [done | constructor].
  Qed.

End RcuCandidate.
