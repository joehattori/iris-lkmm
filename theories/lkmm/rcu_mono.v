From stdpp Require Import base tactics.
From iris_lkmm.lkmm Require Import rcu_graph.

(** Monotonicity of the normal-RCU kernel under finite graph extension. *)
Module RcuMono.
  Import RcuGraph.

  Record graph_le (G H : graph) : Prop := GraphLe {
    graph_le_events : forall e, in_graph G e -> in_graph H e;
    graph_le_gp : forall e, is_gp G e -> is_gp H e;
    graph_le_po : rel_included G.(po) H.(po);
    graph_le_hb : rel_included G.(hb) H.(hb);
    graph_le_prop : rel_included G.(prop) H.(prop);
    graph_le_pb : rel_included G.(pb) H.(pb);
    graph_le_sections :
      forall cs, In cs G.(critical_sections) -> In cs H.(critical_sections)
  }.

  Lemma graph_le_refl G : graph_le G G.
  Proof. constructor; try unfold rel_included; intros; done. Qed.

  Lemma graph_le_trans G H K :
    graph_le G H -> graph_le H K -> graph_le G K.
  Proof.
    intros [GE GGP GPO GHB GPR GPB GCS]
      [HE HGP HPO HHB HPR HPB HCS].
    constructor.
    - intros e He. apply HE. by apply GE.
    - intros e He. apply HGP. by apply GGP.
    - intros x y Hxy. apply HPO. by apply GPO.
    - intros x y Hxy. apply HHB. by apply GHB.
    - intros x y Hxy. apply HPR. by apply GPR.
    - intros x y Hxy. apply HPB. by apply GPB.
    - intros cs Hcs. apply HCS. by apply GCS.
  Qed.

  Lemma rcu_rscsi_mono G H :
    graph_le G H ->
    rel_included (rcu_rscsi G) (rcu_rscsi H).
  Proof.
    intros GH u l (cs & Hcs & Hu & Hl).
    exists cs. split; first by eapply graph_le_sections.
    split; done.
  Qed.

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
      + by eapply rcu_rscsi_mono.
    - eapply RO_rscs_gp.
      + by eapply rcu_rscsi_mono.
      + by eapply rcu_link_mono.
      + by eapply graph_le_gp.
    - eapply RO_gp_inner_rscs.
      + by eapply graph_le_gp.
      + by eapply rcu_link_mono.
      + done.
      + by eapply rcu_link_mono.
      + by eapply rcu_rscsi_mono.
    - eapply RO_rscs_inner_gp.
      + by eapply rcu_rscsi_mono.
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
    apply rel_seq_id_on_r. split_and!; last by eapply graph_le_events.
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
