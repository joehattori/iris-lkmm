From stdpp Require Import base tactics.
From iris_lkmm.lkmm Require Import rcu_graph.

(** Monotonicity of the normal-RCU kernel under finite graph extension. *)
Module RcuMono.
  Import RcuGraph.

  Record graph_le (G H : graph) : Prop := GraphLe {
    graph_le_events :
      forall eid ev, lookup_event G.(events) eid = Some ev ->
        lookup_event H.(events) eid = Some ev;
    graph_le_rf : G.(rf_edges) ⊆ H.(rf_edges);
    graph_le_co : G.(co_edges) ⊆ H.(co_edges);
    graph_le_hb : rel_included G.(hb) H.(hb);
    graph_le_prop : rel_included G.(prop) H.(prop);
    graph_le_pb : rel_included G.(pb) H.(pb);
    graph_le_rscsi : rel_included (graph_rcu_rscsi G) (graph_rcu_rscsi H)
  }.

  Lemma graph_le_refl G : graph_le G G.
  Proof. constructor; try unfold rel_included; intros; done. Qed.

  Lemma graph_le_trans G H K :
    graph_le G H -> graph_le H K -> graph_le G K.
  Proof.
    intros [GE GRF GCO GHB GPR GPB GCS] [HE HRF HCO HHB HPR HPB HCS].
    constructor.
    - intros eid ev Hlookup. apply HE. by apply GE.
    - intros edge Hedge. apply HRF. by apply GRF.
    - intros edge Hedge. apply HCO. by apply GCO.
    - intros x y Hxy. apply HHB. by apply GHB.
    - intros x y Hxy. apply HPR. by apply GPR.
    - intros x y Hxy. apply HPB. by apply GPB.
    - intros x y Hxy. apply HCS. by apply GCS.
  Qed.

  Lemma graph_le_in_graph G H :
    graph_le G H -> forall eid, in_graph G eid -> in_graph H eid.
  Proof.
    intros GH eid Hin. apply in_event_structure_lookup_iff in Hin as (ev & Hlookup).
    apply in_event_structure_lookup_iff. exists ev. by eapply graph_le_events.
  Qed.

  Lemma graph_le_gp G H :
    graph_le G H -> forall eid, is_gp G eid -> is_gp H eid.
  Proof.
    intros GH eid Hgp. apply event_has_barrier_kind_lookup in Hgp as (ev & Hlookup & Hkind).
    apply event_has_barrier_kind_lookup. exists ev. split; last done.
    by eapply graph_le_events.
  Qed.

  Lemma graph_le_po G H :
    graph_le G H -> rel_included (graph_po G) (graph_po H).
  Proof.
    intros GH x y (agent & index1 & index2 & label1 & label2 & Hx & Hy & Hlt).
    exists agent, index1, index2, label1, label2. split_and!; try done;
      by eapply graph_le_events.
  Qed.

  Lemma graph_le_marked G H :
    graph_le G H -> forall eid, graph_marked G eid -> graph_marked H eid.
  Proof.
    intros GH eid [Hin Hnot_plain]. split; first by eapply graph_le_in_graph.
    intros [Hmode Hnot_rmw]. apply Hnot_plain. split.
    - apply event_has_access_mode_lookup in Hmode as (ev & Hlookup & Hmode).
      apply event_has_access_mode_lookup. exists ev. split; last done.
      assert (lookup_event G.(events) eid = Some ev) as HlookupG.
      { apply in_event_structure_lookup_iff in Hin as (old & Hold).
        pose proof (graph_le_events G H GH eid old Hold) as HoldH. congruence. }
      done.
    - intros Hrmw. apply Hnot_rmw.
      apply event_is_rmw_marked_lookup in Hrmw as (ev & Hlookup & Hmark).
      apply event_is_rmw_marked_lookup. exists ev. split; last done.
      apply in_event_structure_lookup_iff in Hin as (old & Hold).
      pose proof (graph_le_events G H GH eid old Hold) as HoldH. congruence.
  Qed.

  Lemma graph_rcu_rscsi_mono G H :
    graph_le G H ->
    rel_included (graph_rcu_rscsi G) (graph_rcu_rscsi H).
  Proof. apply graph_le_rscsi. Qed.

  Lemma rcu_link_mono G H :
    graph_le G H ->
    rel_included (rcu_link G) (rcu_link H).
  Proof.
    intros GH x y (a & b & c & d & Hpo & Hhb & Hpb & Hprop & Hlast).
    exists a, b, c, d. split_and!.
    - eapply optional_mono; [by eapply graph_le_po | done].
    - eapply rtc_mono; [by eapply graph_le_hb | done].
    - eapply rtc_mono; [by eapply graph_le_pb | done].
    - by eapply graph_le_prop.
    - by eapply graph_le_po.
  Qed.

  Lemma rcu_order_mono G H x y :
    graph_le G H ->
    rcu_order G x y ->
    rcu_order H x y.
  Proof.
    intros GH Horder. induction Horder.
    - apply RO_gp. by eapply graph_le_gp.
    - eapply RO_gp_rscs.
      + by eapply graph_le_gp.
      + by eapply rcu_link_mono.
      + by eapply graph_rcu_rscsi_mono.
    - eapply RO_rscs_gp.
      + by eapply graph_rcu_rscsi_mono.
      + by eapply rcu_link_mono.
      + by eapply graph_le_gp.
    - eapply RO_gp_inner_rscs.
      + by eapply graph_le_gp.
      + by eapply rcu_link_mono.
      + done.
      + by eapply rcu_link_mono.
      + by eapply graph_rcu_rscsi_mono.
    - eapply RO_rscs_inner_gp.
      + by eapply graph_rcu_rscsi_mono.
      + by eapply rcu_link_mono.
      + done.
      + by eapply rcu_link_mono.
      + by eapply graph_le_gp.
    - eapply RO_join; try done.
      by eapply rcu_link_mono.
  Qed.

  Lemma rcu_fence_mono G H :
    graph_le G H ->
    rel_included (rcu_fence G) (rcu_fence H).
  Proof.
    intros GH x y (a & b & Hpo & Horder & Hlast).
    exists a, b. split_and!.
    - by eapply graph_le_po.
    - by eapply rcu_order_mono.
    - eapply optional_mono; [by eapply graph_le_po | done].
  Qed.

  Lemma rb_mono G H :
    graph_le G H ->
    rel_included (rb G) (rb H).
  Proof.
    intros GH x y Hrb. unfold rb in Hrb |- *.
    apply rel_seq_id_on_r in Hrb as [Hprefix Hmark].
    apply rel_seq_id_on_r. split_and!; last by eapply graph_le_marked.
    destruct Hprefix as (c & (b & (a & Hprop & Hfence) & Hhb) & Hpb).
    exists c. split.
    - exists b. split.
      + exists a. split.
        * by eapply graph_le_prop.
        * by eapply rcu_fence_mono.
      + eapply rtc_mono; [by eapply graph_le_hb | done].
    - eapply rtc_mono; [by eapply graph_le_pb | done].
  Qed.

End RcuMono.
