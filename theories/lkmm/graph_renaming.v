From Stdlib Require Import Relations.Relation_Operators.
From stdpp Require Import tactics.
From iris_lkmm.lkmm Require Import memory_renaming rcu_renaming rcu_graph.

(** Transport the derived memory and recursive RCU relations before
    transporting their consistency constraints. No execution is assumed. *)
Module GraphRenaming.
  Export MemoryRenaming RcuGraph.
  Import RcuRenaming.

  Local Lemma gp_member G x : is_gp G x -> in_graph G x.
  Proof.
    intros (ev & Hlookup & _)%event_has_barrier_kind_lookup.
    by eapply lookup_event_in.
  Qed.

  Local Lemma rscsi_supported G :
    event_structure_wf G.(events) -> relation_supported G.(events) (graph_rcu_rscsi G).
  Proof.
    intros HE x y Hsection.
    destruct (rcu_rscs_endpoints _ _ _ HE Hsection). done.
  Qed.

  Local Lemma rcu_order_supported G :
    event_structure_wf G.(events) -> relation_supported G.(events) (rcu_order G).
  Proof.
    intros HE x y Horder. induction Horder.
    - pose proof (gp_member _ _ H). done.
    - destruct (rscsi_supported _ HE _ _ H1). pose proof (gp_member _ _ H). done.
    - destruct (rscsi_supported _ HE _ _ H). pose proof (gp_member _ _ H1). done.
    - destruct (rscsi_supported _ HE _ _ H2). pose proof (gp_member _ _ H). done.
    - destruct (rscsi_supported _ HE _ _ H). pose proof (gp_member _ _ H2). done.
    - naive_solver.
  Qed.

  Local Lemma rcu_link_supported G :
    relation_domain G.(events) (rcu_link G) -> relation_supported G.(events) (rcu_link G).
  Proof.
    intros Hdom x y Hlink. pose proof Hlink as (a & b & c & d & _ & _ & _ & _ & Hpo).
    destruct (po_endpoints _ _ _ Hpo) as [_ Hy]. split; last done.
    by eapply relation_domain_right.
  Qed.

  Section RcuRelations.
    Context (f : event_id -> event_id) (G H : graph).
    Context (Hren : event_renaming f G.(events) H.(events)).
    Context (HE : event_structure_wf G.(events)).
    Context (HPROP : relation_renaming f G.(events) H.(events) (graph_prop G) (graph_prop H)).
    Context (HHB : relation_renaming f G.(events) H.(events) (graph_hb G) (graph_hb H)).
    Context (HPB : relation_renaming f G.(events) H.(events) (graph_pb G) (graph_pb H)).

    Let HF := event_renaming_wf f G.(events) H.(events) Hren HE.
    Let POren := relation_renaming_po f G.(events) H.(events) Hren.

    Lemma rcu_link_renaming :
      relation_renaming f G.(events) H.(events) (rcu_link G) (rcu_link H).
    Proof.
      eapply relation_renaming_ext with
        (r' := rel_seq (optional (graph_po G)) (rel_seq (rtc (graph_hb G))
          (rel_seq (rtc (graph_pb G)) (rel_seq (graph_prop G) (graph_po G)))))
        (s' := rel_seq (optional (graph_po H)) (rel_seq (rtc (graph_hb H))
          (rel_seq (rtc (graph_pb H)) (rel_seq (graph_prop H) (graph_po H))))).
      - intros x y. unfold rcu_link, rel_seq. naive_solver.
      - intros x y. unfold rcu_link, rel_seq. naive_solver.
      - apply relation_renaming_seq; first done.
        + apply relation_renaming_optional; done.
        + apply relation_renaming_seq; first done.
          * apply relation_renaming_rtc; done.
          * apply relation_renaming_seq; first done.
            -- apply relation_renaming_rtc; done.
            -- apply relation_renaming_seq; done.
    Qed.

    Lemma rscsi_renaming :
      relation_renaming f G.(events) H.(events) (graph_rcu_rscsi G) (graph_rcu_rscsi H).
    Proof.
      constructor.
      - apply relation_supported_domain, rscsi_supported. done.
      - apply relation_supported_domain, rscsi_supported. done.
      - intros x y Hx Hy. by apply rcu_rscs_rename.
    Qed.

    Lemma rcu_order_renaming :
      relation_renaming f G.(events) H.(events) (rcu_order G) (rcu_order H).
    Proof.
      assert (forall x, is_gp G x -> is_gp H (f x)) as Hgp_forward.
      { intros x Hx. apply (event_renaming_barrier f G.(events) H.(events) x
          BarrierSyncRcu Hren); [by apply gp_member | done]. }
      assert (forall y, is_gp H y -> exists x, is_gp G x /\ f x = y) as Hgp_backward.
      { intros y (ev & Hy & Hkind)%event_has_barrier_kind_lookup.
        destruct (renaming_surjective _ _ _ Hren _ _ Hy) as (x & Hx & <-).
        exists x. split; last done. apply event_has_barrier_kind_lookup. by exists ev. }
      pose proof (relation_renaming_forward _ _ _ _ _ rscsi_renaming
        (rscsi_supported G HE)) as Hsection_forward.
      pose proof (relation_renaming_forward _ _ _ _ _ rcu_link_renaming
        (rcu_link_supported G (relation_renaming_source _ _ _ _ _ rcu_link_renaming))) as Hlink_forward.
      pose proof (relation_renaming_backward _ _ _ Hren _ _ rscsi_renaming
        (rscsi_supported H HF)) as Hsection_backward.
      pose proof (relation_renaming_iff _ _ _ _ _ rcu_link_renaming) as Hlink_backward.
      assert (forall x y, rcu_order G x y -> rcu_order H (f x) (f y)) as Hforward.
      { intros x y Horder. induction Horder.
        - apply RO_gp. by apply Hgp_forward.
        - eapply RO_gp_rscs; [by apply Hgp_forward | by apply Hlink_forward | by apply Hsection_forward].
        - eapply RO_rscs_gp; [by apply Hsection_forward | by apply Hlink_forward | by apply Hgp_forward].
        - eapply RO_gp_inner_rscs; [by apply Hgp_forward | by apply Hlink_forward | done |
            by apply Hlink_forward | by apply Hsection_forward].
        - eapply RO_rscs_inner_gp; [by apply Hsection_forward | by apply Hlink_forward | done |
            by apply Hlink_forward | by apply Hgp_forward].
        - eapply RO_join; [done | by apply Hlink_forward | done]. }
      assert (forall x y, rcu_order H x y ->
        exists a b, rcu_order G a b /\ f a = x /\ f b = y) as Hbackward.
      { intros x y Horder. induction Horder.
        - destruct (Hgp_backward _ H0) as (g' & Hg & <-).
          exists g', g'. split; last done. by apply RO_gp.
        - destruct (Hgp_backward _ H0) as (g' & Hg & <-).
          destruct (Hsection_backward _ _ H2) as (u' & l' & Hsection & <- & <-).
          destruct (rscsi_supported _ HE _ _ Hsection).
          exists g', l'. split; last done. eapply RO_gp_rscs; try done.
          apply Hlink_backward; [by apply gp_member | done | done].
        - destruct (Hsection_backward _ _ H0) as (u' & l' & Hsection & <- & <-).
          destruct (Hgp_backward _ H2) as (g' & Hg & <-).
          destruct (rscsi_supported _ HE _ _ Hsection).
          exists u', g'. split; last done. eapply RO_rscs_gp; try done.
          apply Hlink_backward; [done | by apply gp_member | done].
        - destruct (Hgp_backward _ H0) as (g' & Hg & <-).
          destruct (Hsection_backward _ _ H3) as (u' & l' & Hsection & <- & <-).
          destruct IHHorder as (a & b & Hinner & <- & <-).
          destruct (rscsi_supported _ HE _ _ Hsection).
          destruct (rcu_order_supported _ HE _ _ Hinner).
          exists g', l'. split; last done. eapply RO_gp_inner_rscs; try done.
          + apply Hlink_backward; [by apply gp_member | done | done].
          + apply Hlink_backward; done.
        - destruct (Hsection_backward _ _ H0) as (u' & l' & Hsection & <- & <-).
          destruct (Hgp_backward _ H3) as (g' & Hg & <-).
          destruct IHHorder as (a & b & Hinner & <- & <-).
          destruct (rscsi_supported _ HE _ _ Hsection).
          destruct (rcu_order_supported _ HE _ _ Hinner).
          exists u', g'. split; last done. eapply RO_rscs_inner_gp; try done.
          + apply Hlink_backward; done.
          + apply Hlink_backward; [done | by apply gp_member | done].
        - destruct IHHorder1 as (a & b & Hleft & <- & <-).
          destruct IHHorder2 as (c & d & Hright & <- & <-).
          destruct (rcu_order_supported _ HE _ _ Hleft).
          destruct (rcu_order_supported _ HE _ _ Hright).
          exists a, d. split; last done. eapply RO_join; try done.
          apply Hlink_backward; done. }
      constructor.
      - apply relation_supported_domain, rcu_order_supported. done.
      - apply relation_supported_domain, rcu_order_supported. done.
      - intros x y Hx Hy. split; last apply Hforward.
        intros Horder. destruct (Hbackward _ _ Horder) as (a & b & Hab & Ha & Hb).
        destruct (rcu_order_supported _ HE _ _ Hab).
        assert (a = x) as -> by (eapply (event_renaming_injective _ _ _ _ _ Hren); eauto).
        assert (b = y) as -> by (eapply (event_renaming_injective _ _ _ _ _ Hren); eauto).
        done.
    Qed.

    Lemma rcu_fence_renaming :
      relation_renaming f G.(events) H.(events) (rcu_fence G) (rcu_fence H).
    Proof.
      eapply relation_renaming_ext with
        (r' := rel_seq (graph_po G) (rel_seq (rcu_order G) (optional (graph_po G))))
        (s' := rel_seq (graph_po H) (rel_seq (rcu_order H) (optional (graph_po H)))).
      - intros x y. unfold rcu_fence, rel_seq. naive_solver.
      - intros x y. unfold rcu_fence, rel_seq. naive_solver.
      - apply relation_renaming_seq; first done; first exact POren.
        apply relation_renaming_seq; first done; first apply rcu_order_renaming.
        apply relation_renaming_optional; done.
    Qed.

    Lemma rb_renaming : relation_renaming f G.(events) H.(events) (rb G) (rb H).
    Proof.
      unfold rb. apply relation_renaming_seq; first done.
      - apply relation_renaming_seq; first done.
        + apply relation_renaming_seq; first done.
          * apply relation_renaming_seq; first done; first exact HPROP.
            apply rcu_fence_renaming.
          * apply relation_renaming_rtc; done.
        + apply relation_renaming_rtc; done.
      - apply relation_renaming_id_on; first done.
        intros x Hx. by apply marked_rename.
    Qed.
  End RcuRelations.

  Theorem graph_consistent_rename f G H :
    event_renaming f G.(events) H.(events) ->
    event_structure_wf G.(events) ->
    relation_supported G.(events) (rf G.(rf_edges)) ->
    relation_supported G.(events) (co G.(co_edges)) ->
    relation_supported G.(events) (rmw G.(rmw_edges)) ->
    relation_supported G.(events) (direct_addr G.(direct_addr_edges)) ->
    relation_supported G.(events) (direct_data G.(direct_data_edges)) ->
    relation_supported G.(events) (direct_ctrl G.(direct_ctrl_edges)) ->
    H.(rf_edges) = rename_edges f G.(rf_edges) ->
    H.(co_edges) = rename_edges f G.(co_edges) ->
    H.(rmw_edges) = rename_edges f G.(rmw_edges) ->
    H.(direct_addr_edges) = rename_edges f G.(direct_addr_edges) ->
    H.(direct_data_edges) = rename_edges f G.(direct_data_edges) ->
    H.(direct_ctrl_edges) = rename_edges f G.(direct_ctrl_edges) ->
    graph_consistent G -> graph_consistent H.
  Proof.
    intros Hren HE HRF HCO HRMW HADDR HDATA HCTRL Hrf Hco Hrmw Haddr Hdata Hctrl
      (Hcoherent & Hatomic & Hhappens & Hpropagation & Hrcu).
    assert (relation_renaming f G.(events) H.(events) (graph_prop G) (graph_prop H)) as HPROP.
    { unfold graph_prop. rewrite Hrmw, Hrf, Hco. by apply prop_renaming. }
    assert (relation_renaming f G.(events) H.(events) (graph_hb G) (graph_hb H)) as HHB.
    { unfold graph_hb. rewrite Hrmw, Hrf, Hco, Hdata, Haddr, Hctrl. by apply hb_renaming. }
    assert (relation_renaming f G.(events) H.(events) (graph_pb G) (graph_pb H)) as HPB.
    { unfold graph_pb. rewrite Hrmw, Hrf, Hco, Hdata, Haddr, Hctrl. by apply pb_renaming. }
    pose proof (rb_renaming f G H Hren HE HPROP HHB HPB) as HRB.
    unfold graph_consistent. split; [|split; [|split; [|split]]].
    - eapply relation_renaming_acyclic with (r := graph_coherence_order G); [done | | | done].
      + unfold graph_coherence_order. rewrite Hrf, Hco. by apply coherence_order_renaming.
      + unfold graph_coherence_order. rewrite Hrf, Hco.
        apply coherence_order_supported; by eapply rename_edges_supported.
    - eapply relation_renaming_empty with (r := graph_atomicity_violation G); [done | | | done].
      + unfold graph_atomicity_violation. rewrite Hrmw, Hrf, Hco.
        by apply atomicity_violation_renaming.
      + intros x y [Hxy _]. rewrite Hrmw in Hxy.
        exact (rename_edges_supported f G.(events) H.(events) Hren _ HRMW x y Hxy).
    - eapply relation_renaming_acyclic with (r := graph_hb G); [done | exact HHB | | done].
      apply marked_tail_supported. exact (relation_renaming_target _ _ _ _ _ HHB).
    - eapply relation_renaming_acyclic with (r := graph_pb G); [done | exact HPB | | done].
      apply marked_tail_supported. exact (relation_renaming_target _ _ _ _ _ HPB).
    - eapply relation_renaming_irreflexive with (r := rb G); [done | exact HRB | | done].
      intros x Hxx. apply (proj1 (marked_tail_supported _ _
        (relation_renaming_target _ _ _ _ _ HRB) x x Hxx)).
  Qed.
End GraphRenaming.
