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

  Record finite_candidate := FiniteCandidate {
    fc_events : list labeled_event;
    fc_rf : list edge;
    fc_co : list edge;
    fc_rmw : list edge;
    fc_direct_addr : list edge;
    fc_direct_data : list edge;
    fc_direct_ctrl : list edge
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
    direct_addr_wf (load_events C.(fc_events)).(raw_events)
      (list_to_set C.(fc_direct_addr)) /\
    direct_data_wf (load_events C.(fc_events)).(raw_events)
      (list_to_set C.(fc_direct_data)) /\
    direct_ctrl_wf (load_events C.(fc_events)).(raw_events)
      (list_to_set C.(fc_direct_ctrl)).

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

  Fixpoint load_direct_addr (edges : list edge) (r : raw_graph) : raw_graph :=
    match edges with
    | [] => r
    | e :: edges' => add_direct_addr (load_direct_addr edges' r) e
    end.

  Fixpoint load_direct_data (edges : list edge) (r : raw_graph) : raw_graph :=
    match edges with
    | [] => r
    | e :: edges' => add_direct_data (load_direct_data edges' r) e
    end.

  Fixpoint load_direct_ctrl (edges : list edge) (r : raw_graph) : raw_graph :=
    match edges with
    | [] => r
    | e :: edges' => add_direct_ctrl (load_direct_ctrl edges' r) e
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

  Lemma load_direct_addr_events edges r :
    (load_direct_addr edges r).(raw_events) = r.(raw_events).
  Proof. induction edges; simpl; done. Qed.

  Lemma load_direct_data_events edges r :
    (load_direct_data edges r).(raw_events) = r.(raw_events).
  Proof. induction edges; simpl; done. Qed.

  Lemma load_direct_ctrl_events edges r :
    (load_direct_ctrl edges r).(raw_events) = r.(raw_events).
  Proof. induction edges; simpl; done. Qed.

  Lemma load_events_relations evs :
    (load_events evs).(raw_rf) = [] /\
    (load_events evs).(raw_co) = [] /\
    (load_events evs).(raw_rmw) = [] /\
    (load_events evs).(raw_direct_addr) = [] /\
    (load_events evs).(raw_direct_data) = [] /\
    (load_events evs).(raw_direct_ctrl) = [].
  Proof. induction evs; simpl; done. Qed.

  Lemma load_rf_edges edges r :
    r.(raw_rf) = [] -> (load_rf edges r).(raw_rf) = edges.
  Proof. induction edges; simpl; intros; [done | by rewrite IHedges]. Qed.

  Lemma load_rf_other edges r :
    (load_rf edges r).(raw_co) = r.(raw_co) /\
    (load_rf edges r).(raw_rmw) = r.(raw_rmw) /\
    (load_rf edges r).(raw_direct_addr) = r.(raw_direct_addr) /\
    (load_rf edges r).(raw_direct_data) = r.(raw_direct_data) /\
    (load_rf edges r).(raw_direct_ctrl) = r.(raw_direct_ctrl).
  Proof. induction edges; simpl; done. Qed.

  Lemma load_co_edges edges r :
    r.(raw_co) = [] -> (load_co edges r).(raw_co) = edges.
  Proof. induction edges; simpl; intros; [done | by rewrite IHedges]. Qed.

  Lemma load_co_other edges r :
    (load_co edges r).(raw_rmw) = r.(raw_rmw) /\
    (load_co edges r).(raw_direct_addr) = r.(raw_direct_addr) /\
    (load_co edges r).(raw_direct_data) = r.(raw_direct_data) /\
    (load_co edges r).(raw_direct_ctrl) = r.(raw_direct_ctrl).
  Proof. induction edges; simpl; done. Qed.

  Lemma load_rmw_edges edges r :
    r.(raw_rmw) = [] -> (load_rmw edges r).(raw_rmw) = edges.
  Proof. induction edges; simpl; intros; [done | by rewrite IHedges]. Qed.

  Lemma load_rmw_other edges r :
    (load_rmw edges r).(raw_direct_addr) = r.(raw_direct_addr) /\
    (load_rmw edges r).(raw_direct_data) = r.(raw_direct_data) /\
    (load_rmw edges r).(raw_direct_ctrl) = r.(raw_direct_ctrl).
  Proof. induction edges; simpl; done. Qed.

  Lemma load_direct_addr_edges edges r :
    r.(raw_direct_addr) = [] ->
    (load_direct_addr edges r).(raw_direct_addr) = edges.
  Proof. induction edges; simpl; intros; [done | by rewrite IHedges]. Qed.

  Lemma load_direct_addr_other edges r :
    (load_direct_addr edges r).(raw_direct_data) = r.(raw_direct_data) /\
    (load_direct_addr edges r).(raw_direct_ctrl) = r.(raw_direct_ctrl).
  Proof. induction edges; simpl; done. Qed.

  Lemma load_direct_data_edges edges r :
    r.(raw_direct_data) = [] ->
    (load_direct_data edges r).(raw_direct_data) = edges.
  Proof. induction edges; simpl; intros; [done | by rewrite IHedges]. Qed.

  Lemma load_direct_data_ctrl edges r :
    (load_direct_data edges r).(raw_direct_ctrl) = r.(raw_direct_ctrl).
  Proof. induction edges; simpl; done. Qed.

  Lemma load_direct_ctrl_edges edges r :
    r.(raw_direct_ctrl) = [] ->
    (load_direct_ctrl edges r).(raw_direct_ctrl) = edges.
  Proof. induction edges; simpl; intros; [done | by rewrite IHedges]. Qed.

  Definition candidate_raw (C : finite_candidate) : raw_graph :=
    load_direct_ctrl C.(fc_direct_ctrl)
      (load_direct_data C.(fc_direct_data)
        (load_direct_addr C.(fc_direct_addr)
          (load_rmw C.(fc_rmw)
            (load_co C.(fc_co)
              (load_rf C.(fc_rf) (load_events C.(fc_events))))))).

  Lemma candidate_raw_events C :
    (candidate_raw C).(raw_events) = (load_events C.(fc_events)).(raw_events).
  Proof.
    unfold candidate_raw.
    rewrite load_direct_ctrl_events, load_direct_data_events,
      load_direct_addr_events, load_rmw_events, load_co_events, load_rf_events. done.
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

  Lemma load_direct_addr_schedule edges r :
    r.(raw_direct_addr) = [] ->
    direct_addr_wf r.(raw_events) (list_to_set edges) ->
    raw_run r (load_direct_addr edges r).
  Proof.
    intros Hempty Hwf. induction edges as [|e edges IH]; simpl; first constructor.
    assert (direct_addr_wf r.(raw_events) (list_to_set edges)) as Htail.
    { eapply direct_addr_wf_subset; last exact Hwf. set_solver. }
    eapply raw_run_trans; first by apply IH.
    apply raw_run_single, RawStepDirectAddr.
    rewrite load_direct_addr_events, (load_direct_addr_edges edges r Hempty). exact Hwf.
  Qed.

  Lemma load_direct_data_schedule edges r :
    r.(raw_direct_data) = [] ->
    direct_data_wf r.(raw_events) (list_to_set edges) ->
    raw_run r (load_direct_data edges r).
  Proof.
    intros Hempty Hwf. induction edges as [|e edges IH]; simpl; first constructor.
    assert (direct_data_wf r.(raw_events) (list_to_set edges)) as Htail.
    { eapply direct_data_wf_subset; last exact Hwf. set_solver. }
    eapply raw_run_trans; first by apply IH.
    apply raw_run_single, RawStepDirectData.
    rewrite load_direct_data_events, (load_direct_data_edges edges r Hempty). exact Hwf.
  Qed.

  Lemma load_direct_ctrl_schedule edges r :
    r.(raw_direct_ctrl) = [] ->
    direct_ctrl_wf r.(raw_events) (list_to_set edges) ->
    raw_run r (load_direct_ctrl edges r).
  Proof.
    intros Hempty Hwf. induction edges as [|e edges IH]; simpl; first constructor.
    assert (direct_ctrl_wf r.(raw_events) (list_to_set edges)) as Htail.
    { eapply direct_ctrl_wf_subset; last exact Hwf. set_solver. }
    eapply raw_run_trans; first by apply IH.
    apply raw_run_single, RawStepDirectCtrl.
    rewrite load_direct_ctrl_events, (load_direct_ctrl_edges edges r Hempty). exact Hwf.
  Qed.

  Theorem candidate_has_raw_schedule C :
    candidate_well_formed C ->
    raw_run empty_raw (candidate_raw C).
  Proof.
    intros (_ & Horder & _ & _ & Hrf & Hco & Hrmw & Haddr & Hdata & Hctrl).
    pose proof (load_events_relations C.(fc_events)) as
      (Hempty_rf & Hempty_co & Hempty_rmw & Hempty_addr & Hempty_data & Hempty_ctrl).
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
      - rewrite (proj1 (load_co_other C.(fc_co) _)).
        rewrite (proj1 (proj2 (load_rf_other C.(fc_rf) _))). exact Hempty_rmw.
      - by rewrite load_co_events, load_rf_events. }
    eapply raw_run_trans.
    { apply (load_direct_addr_schedule C.(fc_direct_addr)).
      - rewrite (proj1 (load_rmw_other C.(fc_rmw) _)).
        rewrite (proj1 (proj2 (load_co_other C.(fc_co) _))).
        rewrite (proj1 (proj2 (proj2 (load_rf_other C.(fc_rf) _)))). exact Hempty_addr.
      - by rewrite load_rmw_events, load_co_events, load_rf_events. }
    eapply raw_run_trans.
    { apply (load_direct_data_schedule C.(fc_direct_data)).
      - rewrite (proj1 (load_direct_addr_other C.(fc_direct_addr) _)).
        rewrite (proj1 (proj2 (load_rmw_other C.(fc_rmw) _))).
        rewrite (proj1 (proj2 (proj2 (load_co_other C.(fc_co) _)))).
        rewrite (proj1 (proj2 (proj2 (proj2 (load_rf_other C.(fc_rf) _))))).
        exact Hempty_data.
      - by rewrite load_direct_addr_events, load_rmw_events, load_co_events, load_rf_events. }
    apply (load_direct_ctrl_schedule C.(fc_direct_ctrl)).
    - rewrite load_direct_data_ctrl.
      rewrite (proj2 (load_direct_addr_other C.(fc_direct_addr) _)).
      rewrite (proj2 (proj2 (load_rmw_other C.(fc_rmw) _))).
      rewrite (proj2 (proj2 (proj2 (load_co_other C.(fc_co) _)))).
      rewrite (proj2 (proj2 (proj2 (proj2 (load_rf_other C.(fc_rf) _))))).
      exact Hempty_ctrl.
    - by rewrite load_direct_data_events, load_direct_addr_events,
        load_rmw_events, load_co_events, load_rf_events.
  Qed.

  Definition relation_difference (old new : relation) : relation :=
    fun x y => new x y /\ ~ old x y.

  Definition consistency_difference (old new : raw_graph) : consistency_relations :=
    let old_relations := graph_consistency_relations (graph_of_raw old) in
    let new_relations := graph_consistency_relations (graph_of_raw new) in
    ConsistencyRelations
      (relation_difference old_relations.(cr_coherence) new_relations.(cr_coherence))
      (relation_difference old_relations.(cr_atomicity) new_relations.(cr_atomicity))
      (relation_difference old_relations.(cr_happens_before)
        new_relations.(cr_happens_before))
      (relation_difference old_relations.(cr_propagation) new_relations.(cr_propagation))
      (relation_difference old_relations.(cr_rb) new_relations.(cr_rb)).

  Definition consistency_relations_included
      (relations1 relations2 : consistency_relations) : Prop :=
    rel_included relations1.(cr_coherence) relations2.(cr_coherence) /\
    rel_included relations1.(cr_atomicity) relations2.(cr_atomicity) /\
    rel_included relations1.(cr_happens_before) relations2.(cr_happens_before) /\
    rel_included relations1.(cr_propagation) relations2.(cr_propagation) /\
    rel_included relations1.(cr_rb) relations2.(cr_rb).

  Local Lemma edge_relation_mono edges1 edges2 :
    edges1 ⊆ edges2 -> rel_included (edge_relation edges1) (edge_relation edges2).
  Proof. intros Hedges source target Hedge. by apply Hedges. Qed.

  Local Lemma graph_fr_mono G H :
    graph_le G H ->
    rel_included (fr G.(rf_edges) G.(co_edges)) (fr H.(rf_edges) H.(co_edges)).
  Proof.
    intros GH. unfold fr. apply rel_seq_mono.
    - apply rel_inverse_mono, edge_relation_mono. by eapply graph_le_rf.
    - apply edge_relation_mono. by eapply graph_le_co.
  Qed.

  Local Lemma graph_coherence_order_mono G H :
    graph_le G H -> rel_included (graph_coherence_order G) (graph_coherence_order H).
  Proof.
    intros GH. unfold graph_coherence_order, po_loc, com. apply rel_union_mono.
    - apply rel_intersection_mono.
      + by apply po_mono, (graph_le_events _ _ GH).
      + by apply same_attribute_mono, (graph_le_events _ _ GH).
    - apply rel_union_mono.
      + apply edge_relation_mono. by eapply graph_le_rf.
      + apply rel_union_mono.
        * apply edge_relation_mono. by eapply graph_le_co.
        * by apply graph_fr_mono.
  Qed.

  Local Lemma graph_atomicity_violation_mono r r' :
    raw_relations_wf r -> graph_le (graph_of_raw r) (graph_of_raw r') ->
    rel_included (graph_atomicity_violation (graph_of_raw r))
      (graph_atomicity_violation (graph_of_raw r')).
  Proof.
    intros (_ & Hco_wf & Hrmw_wf & _) Hle read write [Hrmw Hchain].
    destruct Hrmw_wf as (Hrmw_edges & _).
    destruct Hco_wf as (Hco_edges & _).
    destruct (Hrmw_edges read write Hrmw) as
      (read_event & write_event & Hread & Hwrite & _).
    destruct Hchain as (middle & [Hfr Hext1] & [Hco Hext2]).
    destruct (Hco_edges middle write Hco) as
      (middle_event & write_event' & Hmiddle & Hwrite' & _).
    assert (in_event_structure r.(raw_events) read) as Hin_read.
    { by eapply lookup_event_in. }
    assert (in_event_structure r.(raw_events) middle) as Hin_middle.
    { by eapply lookup_event_in. }
    assert (in_event_structure r.(raw_events) write) as Hin_write.
    { by eapply lookup_event_in. }
    assert (event_structure_included r.(raw_events) r'.(raw_events)) as HE.
    { exact (graph_le_events _ _ Hle). }
    split.
    - by eapply graph_le_rmw.
    - exists middle. split.
      + split.
        * by eapply graph_fr_mono.
        * by eapply ext_mono.
      + split.
        * by eapply graph_le_co.
        * by eapply ext_mono.
  Qed.

  Lemma graph_consistency_relations_mono r r' :
    raw_relations_wf r -> graph_le (graph_of_raw r) (graph_of_raw r') ->
    consistency_relations_included
      (graph_consistency_relations (graph_of_raw r))
      (graph_consistency_relations (graph_of_raw r')).
  Proof.
    intros Hwf Hle. unfold consistency_relations_included, graph_consistency_relations.
    cbn. split_and!.
    - apply tc_mono. by apply graph_coherence_order_mono.
    - by eapply graph_atomicity_violation_mono.
    - apply tc_mono. by eapply graph_le_hb.
    - apply tc_mono. by eapply graph_le_pb.
    - by eapply rb_mono.
  Qed.

  Lemma consistency_difference_exact old new seen :
    raw_relations_wf old -> graph_le (graph_of_raw old) (graph_of_raw new) ->
    consistency_relations_exact (graph_of_raw old) seen ->
    consistency_delta_exact new seen (consistency_difference old new).
  Proof.
    intros Hwf Hle Hexact.
    pose proof (graph_consistency_relations_mono old new Hwf Hle) as Hmono.
    destruct Hmono as (Hco_mono & Hat_mono & Hhb_mono & Hpb_mono & Hrb_mono).
    destruct Hexact as (Hco & Hat & Hhb & Hpb & Hrb).
    unfold consistency_delta_exact, consistency_relations_exact,
      consistency_relations_union, consistency_difference, graph_consistency_relations.
    cbn. split_and!; intros x y; split.
    - intros [Hold | (Hnew & _)]; last done. apply Hco_mono, Hco, Hold.
    - intros Hnew. destruct (classic (tc (graph_coherence_order (graph_of_raw old)) x y)).
      + left. by apply Hco.
      + right. by split.
    - intros [Hold | (Hnew & _)]; last done. apply Hat_mono, Hat, Hold.
    - intros Hnew. destruct (classic (graph_atomicity_violation (graph_of_raw old) x y)).
      + left. by apply Hat.
      + right. by split.
    - intros [Hold | (Hnew & _)]; last done. apply Hhb_mono, Hhb, Hold.
    - intros Hnew. destruct (classic (tc (graph_hb (graph_of_raw old)) x y)).
      + left. by apply Hhb.
      + right. by split.
    - intros [Hold | (Hnew & _)]; last done. apply Hpb_mono, Hpb, Hold.
    - intros Hnew. destruct (classic (tc (graph_pb (graph_of_raw old)) x y)).
      + left. by apply Hpb.
      + right. by split.
    - intros [Hold | (Hnew & _)]; last done. apply Hrb_mono, Hrb, Hold.
    - intros Hnew. destruct (classic (rb (graph_of_raw old) x y)).
      + left. by apply Hrb.
      + right. by split.
  Qed.

  Lemma consistency_difference_safe old new final :
    raw_relations_wf new -> raw_run new final ->
    graph_consistent (graph_of_raw final) ->
    consistency_relations_safe (consistency_difference old new).
  Proof.
    intros Hwf Hsuffix Hconsistent.
    pose proof (raw_run_graph_le _ _ Hsuffix) as Hle.
    pose proof (graph_consistency_relations_mono new final Hwf Hle) as Hmono.
    apply graph_consistency_relations_safe in Hconsistent.
    destruct Hmono as (Hco_mono & Hat_mono & Hhb_mono & Hpb_mono & Hrb_mono).
    destruct Hconsistent as (Hco & Hat & Hhb & Hpb & Hrb).
    unfold consistency_relations_safe, consistency_difference. cbn. split_and!.
    - intros eid [Hnew _]. apply (Hco eid), Hco_mono, Hnew.
    - intros source target [Hnew _]. apply (Hat source target), Hat_mono, Hnew.
    - intros eid [Hnew _]. apply (Hhb eid), Hhb_mono, Hnew.
    - intros eid [Hnew _]. apply (Hpb eid), Hpb_mono, Hnew.
    - intros eid [Hnew _]. apply (Hrb eid), Hrb_mono, Hnew.
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
    raw_relations_wf r ->
    raw_run r final ->
    graph_consistent (graph_of_raw final) ->
    exists s',
      builder_run s s' /\
      s'.(bs_raw) = final /\
      builder_invariant s'.
  Proof.
    intros Hraw Hinv Hwf Hrun.
    revert s Hraw Hinv Hwf.
    induction Hrun as
      [r | r r' final Hstep Hsuffix IH];
      intros s Hraw Hinv Hwf Hconsistent.
    - exists s. split; first constructor.
      split; done.
    - destruct s as [current links seen]. simpl in Hraw. subst current.
      pose (delta := consistency_difference r r').
      pose (next := BuilderState r' links
        (consistency_relations_union seen delta)).
      assert (raw_relations_wf r') as Hwf'.
      { by eapply raw_step_preserves_relations_wf. }
      assert (Hbuilder : builder_step
          (BuilderState r links seen) next).
      { unfold next. apply BuilderStepRaw; first done.
        - unfold delta. apply consistency_difference_exact; try done.
          + by apply raw_step_graph_le.
          + by destruct Hinv as (Hexact & _).
        - unfold delta. by eapply consistency_difference_safe.
      }
      assert (Hnext : builder_invariant next).
      { by eapply builder_step_preserves_invariant. }
      destruct (IH next eq_refl Hnext Hwf' Hconsistent)
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
    graph_consistent (candidate_graph C) ->
    exists s,
      builder_run initial_builder s /\
      s.(bs_raw) = candidate_raw C /\
      graph_of_raw s.(bs_raw) = candidate_graph C.
  Proof.
    intros Hwf Hconsistent.
    pose proof (candidate_has_raw_schedule C Hwf) as Hschedule.
    destruct (lift_safe_raw_schedule empty_raw (candidate_raw C)
      initial_builder eq_refl initial_builder_invariant
      empty_raw_relations_wf Hschedule Hconsistent) as (s & Hrun & Hraw & _).
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
