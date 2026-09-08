From stdpp Require Import gmap tactics.
From iris_lkmm.lkmm Require Import relation_renaming memory_relations.

(** Well-formedness and derived memory relations under event-ID renaming.
    Injectivity is needed only on allocated events; well-formed base edges
    supply that domain, including for negative event-class and identity tests. *)
Module MemoryRenaming.
  Export RelationRenaming LkmmMemoryRelations.

  Section Renaming.
    Context (f : event_id -> event_id) (E F : event_structure).
    Context (Hren : event_renaming f E F).

    Lemma rf_edge_wf_rename x y :
      rf_edge_wf E x y -> rf_edge_wf F (f x) (f y).
    Proof.
      intros (ex & ey & val & Hx & Hy & Hwrite & Hread & Hloc & Hvx & Hvy).
      exists ex, ey, val. split_and!; try done.
      - by apply (renaming_lookup _ _ _ Hren).
      - by apply (renaming_lookup _ _ _ Hren).
      - apply (event_renaming_same_attribute location_of f E F x y Hren);
          [by eapply lookup_event_in | by eapply lookup_event_in | done].
    Qed.

    Theorem rf_wf_rename edges : rf_wf E edges -> rf_wf F (rename_edges f edges).
    Proof.
      intros Hwf. pose proof (fun x y => rf_wf_endpoints E edges x y Hwf) as Hends.
      destruct Hwf as (Hedges & Hfunctional & Htotal). split; [|split].
      - intros x y Hedge. apply rename_edges_spec in Hedge as (a & b & Hab & <- & <-).
        apply rf_edge_wf_rename. by apply Hedges.
      - intros x y read Hx Hy.
        apply rename_edges_spec in Hx as (a & r & Har & <- & <-).
        apply rename_edges_spec in Hy as (b & r' & Hbr & <- & Heq).
        assert (r' = r) as ->.
        { eapply (event_renaming_injective _ _ _ _ _ Hren);
            [exact (proj2 (Hends _ _ Hbr)) | exact (proj2 (Hends _ _ Har)) | done]. }
        f_equal. by eapply Hfunctional.
      - intros read ev Hread Hkind.
        destruct (renaming_surjective _ _ _ Hren _ _ Hread) as (r & Hr & <-).
        destruct (Htotal _ _ Hr Hkind) as [w Hw].
        exists (f w). by apply rename_edges_forward.
    Qed.

    Lemma rmw_edge_wf_rename x y :
      rmw_edge_wf E x y -> rmw_edge_wf F (f x) (f y).
    Proof.
      intros (ex & ey & Hx & Hy & Hread & Hwrite & Hmx & Hmy & Hpo & Hloc & Hmode).
      pose proof (lookup_event_in _ _ _ Hx) as Hinx.
      pose proof (lookup_event_in _ _ _ Hy) as Hiny.
      exists ex, ey. split_and!; try done.
      - by apply (renaming_lookup _ _ _ Hren).
      - by apply (renaming_lookup _ _ _ Hren).
      - by apply (event_renaming_po f E F x y Hren Hinx Hiny).
      - by apply (event_renaming_same_attribute location_of f E F x y Hren Hinx Hiny).
      - by apply (event_renaming_same_attribute access_mode_of f E F x y Hren Hinx Hiny).
    Qed.

    Theorem rmw_wf_rename edges : rmw_wf E edges -> rmw_wf F (rename_edges f edges).
    Proof.
      intros Hwf. pose proof (fun x y => rmw_wf_endpoints E edges x y Hwf) as Hends.
      destruct Hwf as (Hedges & Hfunctional & Hinjective & Htotal).
      split; [|split; [|split]].
      - intros x y Hedge. apply rename_edges_spec in Hedge as (a & b & Hab & <- & <-).
        apply rmw_edge_wf_rename. by apply Hedges.
      - intros read x y Hx Hy.
        apply rename_edges_spec in Hx as (r & a & Hra & <- & <-).
        apply rename_edges_spec in Hy as (r' & b & Hrb & Heq & <-).
        assert (r' = r) as ->.
        { eapply (event_renaming_injective _ _ _ _ _ Hren);
            [exact (proj1 (Hends _ _ Hrb)) | exact (proj1 (Hends _ _ Hra)) | done]. }
        f_equal. by eapply Hfunctional.
      - intros x y write Hx Hy.
        apply rename_edges_spec in Hx as (a & w & Haw & <- & <-).
        apply rename_edges_spec in Hy as (b & w' & Hbw & <- & Heq).
        assert (w' = w) as ->.
        { eapply (event_renaming_injective _ _ _ _ _ Hren);
            [exact (proj2 (Hends _ _ Hbw)) | exact (proj2 (Hends _ _ Haw)) | done]. }
        f_equal. by eapply Hinjective.
      - intros write ev Hwrite Hkind Hmarked.
        destruct (renaming_surjective _ _ _ Hren _ _ Hwrite) as (w & Hw & <-).
        destruct (Htotal _ _ Hw Hkind Hmarked) as [r Hr].
        exists (f r). by apply rename_edges_forward.
    Qed.

    Lemma co_edge_wf_rename x y :
      co_edge_wf E x y -> co_edge_wf F (f x) (f y).
    Proof.
      intros (ex & ey & Hx & Hy & Hwrite_x & Hwrite_y & Hloc).
      exists ex, ey. split_and!; try done.
      - by apply (renaming_lookup _ _ _ Hren).
      - by apply (renaming_lookup _ _ _ Hren).
      - apply (event_renaming_same_attribute location_of f E F x y Hren);
          [by eapply lookup_event_in | by eapply lookup_event_in | done].
    Qed.

    Theorem co_wf_rename edges : co_wf E edges -> co_wf F (rename_edges f edges).
    Proof.
      intros Hwf. pose proof (fun x y => co_wf_endpoints E edges x y Hwf) as Hends.
      destruct Hwf as (Hedges & Hirr & Htrans & Htotal & Hexists & Hunique & Hfirst).
      split; [|split; [|split; [|split; [|split; [|split]]]]].
      - intros x y Hedge. apply rename_edges_spec in Hedge as (a & b & Hab & <- & <-).
        apply co_edge_wf_rename. by apply Hedges.
      - intros x Hedge. apply rename_edges_spec in Hedge as (a & b & Hab & <- & Heq).
        assert (b = a) as ->.
        { eapply (event_renaming_injective _ _ _ _ _ Hren);
            [exact (proj2 (Hends _ _ Hab)) | exact (proj1 (Hends _ _ Hab)) | done]. }
        by apply (Hirr a).
      - intros x y z Hxy Hyz.
        apply rename_edges_spec in Hxy as (a & b & Hab & <- & <-).
        apply rename_edges_spec in Hyz as (b' & c & Hbc & Heq & <-).
        assert (b' = b) as ->.
        { eapply (event_renaming_injective _ _ _ _ _ Hren);
            [exact (proj1 (Hends _ _ Hbc)) | exact (proj2 (Hends _ _ Hab)) | done]. }
        apply rename_edges_forward. by eapply Htrans.
      - intros x y ex ey Hx Hy Hwrite_x Hwrite_y Hloc Hne.
        destruct (renaming_surjective _ _ _ Hren _ _ Hx) as (a & Ha & <-).
        destruct (renaming_surjective _ _ _ Hren _ _ Hy) as (b & Hb & <-).
        assert (same_location E a b) as Hloc'.
        { apply (event_renaming_same_attribute location_of f E F a b Hren);
            [by eapply lookup_event_in | by eapply lookup_event_in | done]. }
        assert (a <> b) as Hne' by congruence.
        destruct (Htotal _ _ _ _ Ha Hb Hwrite_x Hwrite_y Hloc' Hne') as [Hab | Hba];
          [left | right]; by apply rename_edges_forward.
      - intros loc [x Hloc].
        change ((lookup_event F x ≫= location_of) = Some loc) in Hloc.
        apply bind_Some in Hloc as (ev & Hx & Hloc).
        destruct (renaming_surjective _ _ _ Hren _ _ Hx) as (a & Ha & <-).
        assert (location_used E loc) as Hused.
        { exists a. change ((lookup_event E a ≫= location_of) = Some loc).
          by rewrite Ha. }
        destruct (Hexists loc Hused) as (initial & val & Hinitial).
        exists (f initial), val. by apply (renaming_lookup _ _ _ Hren).
      - intros loc x y [vx Hx] [vy Hy].
        destruct (renaming_surjective _ _ _ Hren _ _ Hx) as (a & Ha & <-).
        destruct (renaming_surjective _ _ _ Hren _ _ Hy) as (b & Hb & <-).
        f_equal. apply (Hunique loc); [by exists vx | by exists vy].
      - intros initial write loc ev [val Hinitial] Hwrite Hkind Hloc Hne.
        destruct (renaming_surjective _ _ _ Hren _ _ Hinitial) as (i & Hi & <-).
        destruct (renaming_surjective _ _ _ Hren _ _ Hwrite) as (w & Hw & <-).
        apply rename_edges_forward. apply (Hfirst i w loc ev); try done.
        + by exists val.
        + apply (event_renaming_same_attribute location_of f E F i w Hren);
            [by eapply lookup_event_in | by eapply lookup_event_in | done].
        + congruence.
    Qed.

    Lemma direct_addr_wf_rename edges :
      direct_addr_wf E edges -> direct_addr_wf F (rename_edges f edges).
    Proof.
      intros Hwf x y Hedge.
      apply rename_edges_spec in Hedge as (a & b & Hab & <- & <-).
      destruct (Hwf _ _ Hab) as ((ex & Hx & Hread) & (ey & Hy & Hmemory) & Hpo).
      split; [|split].
      - exists ex. split; [by apply (renaming_lookup _ _ _ Hren) | done].
      - exists ey. split; [by apply (renaming_lookup _ _ _ Hren) | done].
      - apply (event_renaming_po f E F a b Hren);
          [by eapply lookup_event_in | by eapply lookup_event_in | done].
    Qed.

    Lemma direct_data_wf_rename edges :
      direct_data_wf E edges -> direct_data_wf F (rename_edges f edges).
    Proof.
      intros Hwf x y Hedge.
      apply rename_edges_spec in Hedge as (a & b & Hab & <- & <-).
      destruct (Hwf _ _ Hab) as ((ex & Hx & Hread) & (ey & Hy & Hwrite) & Hpo).
      split; [|split].
      - exists ex. split; [by apply (renaming_lookup _ _ _ Hren) | done].
      - exists ey. split; [by apply (renaming_lookup _ _ _ Hren) | done].
      - apply (event_renaming_po f E F a b Hren);
          [by eapply lookup_event_in | by eapply lookup_event_in | done].
    Qed.

    Lemma direct_ctrl_wf_rename edges :
      direct_ctrl_wf E edges -> direct_ctrl_wf F (rename_edges f edges).
    Proof. apply direct_data_wf_rename. Qed.
  End Renaming.

  Section Relations.
    Context (f : event_id -> event_id) (E F : event_structure).
    Context (Hren : event_renaming f E F).
    Context (rmw0 rf0 co0 data0 addr0 ctrl0 : edge_set).
    Context (HRMW : relation_supported E (rmw rmw0)).
    Context (HRF : relation_supported E (rf rf0)) (HCO : relation_supported E (co co0)).
    Context (HDATA : relation_supported E (direct_data data0)).
    Context (HADDR : relation_supported E (direct_addr addr0)).
    Context (HCTRL : relation_supported E (direct_ctrl ctrl0)).

    Let RMWren := relation_renaming_edges f E F Hren rmw0 HRMW.
    Let RFren := relation_renaming_edges f E F Hren rf0 HRF.
    Let COren := relation_renaming_edges f E F Hren co0 HCO.
    Let DATAren := relation_renaming_edges f E F Hren data0 HDATA.
    Let ADDRren := relation_renaming_edges f E F Hren addr0 HADDR.
    Let CTRLren := relation_renaming_edges f E F Hren ctrl0 HCTRL.

    Local Lemma read_rename x : in_event_structure E x ->
      (event_is_read F (f x) <-> event_is_read E x).
    Proof. apply renaming_event_predicate, Hren. Qed.

    Local Lemma write_rename x : in_event_structure E x ->
      (event_is_write F (f x) <-> event_is_write E x).
    Proof. apply renaming_event_predicate, Hren. Qed.

    Local Lemma memory_rename x : in_event_structure E x ->
      (event_is_memory F (f x) <-> event_is_memory E x).
    Proof. apply renaming_event_predicate, Hren. Qed.

    Local Lemma mode_rename mode x : in_event_structure E x ->
      (event_has_access_mode F mode (f x) <-> event_has_access_mode E mode x).
    Proof. intros Hx. rewrite !event_has_access_mode_lookup. by apply renaming_event_predicate. Qed.

    Local Lemma kind_rename kind x : in_event_structure E x ->
      (event_has_access_kind F kind (f x) <-> event_has_access_kind E kind x).
    Proof.
      intros Hx. change (((lookup_event F (f x) ≫= access_kind_of) = Some kind) <->
        (lookup_event E x ≫= access_kind_of) = Some kind).
      by rewrite (renaming_attribute f E F Hren access_kind_of x Hx).
    Qed.

    Local Lemma rmw_mark_rename x : in_event_structure E x ->
      (event_is_rmw_marked F (f x) <-> event_is_rmw_marked E x).
    Proof. intros Hx. rewrite !event_is_rmw_marked_lookup. by apply renaming_event_predicate. Qed.

    Local Lemma failed_rmw_rename x : in_event_structure E x ->
      (failed_rmw F (rename_edges f rmw0) (f x) <-> failed_rmw E rmw0 x).
    Proof.
      intros Hx. unfold failed_rmw.
      by rewrite (rmw_mark_rename x Hx),
        (relation_renaming_domain f E F Hren _ _ x RMWren Hx),
        (relation_renaming_range f E F Hren _ _ x RMWren Hx).
    Qed.

    Lemma marked_rename x : in_event_structure E x ->
      (marked F (f x) <-> marked E x).
    Proof.
      intros Hx. unfold marked, plain.
      rewrite (mode_rename AccessPlain x Hx), (rmw_mark_rename x Hx).
      pose proof (renaming_member f E F Hren x Hx). tauto.
    Qed.

    (** Normalize the CAT relation expressions to their algebraic operators;
        event classes and negative tests are transported by equivalences. *)
    Local Ltac transport_class :=
      let x := fresh "eid" in let Hx := fresh "Hin" in
      intros x Hx;
      unfold acquire, release, mb_event, r4_rmb, noreturn, plain;
      rewrite ?(read_rename x Hx), ?(write_rename x Hx), ?(memory_rename x Hx),
        ?(rmw_mark_rename x Hx), ?(failed_rmw_rename x Hx), ?(marked_rename x Hx),
        ?(mode_rename _ x Hx), ?(kind_rename _ x Hx),
        ?(event_renaming_barrier f E F x _ Hren Hx);
      done.

    Local Ltac transport :=
      first [exact RMWren | exact RFren | exact COren | exact DATAren | exact ADDRren | exact CTRLren |
      lazymatch goal with
      | |- relation_renaming _ _ _ (po _) _ => apply relation_renaming_po; exact Hren
      | |- relation_renaming _ _ _ rel_id _ => apply relation_renaming_id; exact Hren
      | |- relation_renaming _ _ _ (rel_id_on _) _ =>
          apply relation_renaming_id_on; [exact Hren | transport_class]
      | |- relation_renaming _ _ _ (rel_union _ _) _ => apply relation_renaming_union; transport
      | |- relation_renaming _ _ _ (rel_seq _ _) _ =>
          apply relation_renaming_seq; [exact Hren | transport | transport]
      | |- relation_renaming _ _ _ (rel_inverse _) _ => apply relation_renaming_inverse; transport
      | |- relation_renaming _ _ _ (optional _) _ =>
          apply relation_renaming_optional; [exact Hren | transport]
      | |- relation_renaming _ _ _ (rtc _) _ => apply relation_renaming_rtc; [exact Hren | transport]
      | |- relation_renaming _ _ _ (rel_difference _ _) _ => apply relation_renaming_difference; transport
      | |- relation_renaming _ _ _ (rel_intersection _ _) _ =>
          apply relation_renaming_intersection; [transport |];
          let x := fresh "x" in let y := fresh "y" in
          let Hx := fresh "Hx" in let Hy := fresh "Hy" in
          intros x y Hx Hy;
          first [apply event_renaming_same_attribute; done
          | unfold ext, same_agent;
            rewrite (event_renaming_same_attribute agent_of f E F x y Hren Hx Hy); done
          | apply (relation_renaming_iff f E F _ _); [transport | exact Hx | exact Hy]]
      end].

    Local Ltac expand_memory :=
      cbv [ppo to_r to_w rwdep dep addr data ctrl carry_dep
        fence nonrw_fence strong_fence mb gp po_rel acq_po wmb rmb fencerel
        prop cumul_fence a_cumul rmw_sequence overwrite fr rfi rfe coe fre].

    Lemma ppo_renaming : relation_renaming f E F
      (ppo E rmw0 rf0 co0 data0 addr0 ctrl0)
      (ppo F (rename_edges f rmw0) (rename_edges f rf0) (rename_edges f co0)
        (rename_edges f data0) (rename_edges f addr0) (rename_edges f ctrl0)).
    Proof. expand_memory. transport. Qed.

    Lemma prop_renaming : relation_renaming f E F
      (prop E rmw0 rf0 co0)
      (prop F (rename_edges f rmw0) (rename_edges f rf0) (rename_edges f co0)).
    Proof. expand_memory. transport. Qed.

    Lemma hb_renaming : relation_renaming f E F
      (hb E rmw0 rf0 co0 data0 addr0 ctrl0)
      (hb F (rename_edges f rmw0) (rename_edges f rf0) (rename_edges f co0)
        (rename_edges f data0) (rename_edges f addr0) (rename_edges f ctrl0)).
    Proof.
      unfold hb. repeat apply relation_renaming_seq; try done.
      - apply relation_renaming_id_on; [done | transport_class].
      - apply relation_renaming_union; first apply ppo_renaming.
        apply relation_renaming_union.
        + unfold rfe. transport.
        + apply relation_renaming_intersection.
          * apply relation_renaming_difference; [apply prop_renaming | transport].
          * intros x y Hx Hy. by apply event_renaming_same_attribute.
      - apply relation_renaming_id_on; [done | transport_class].
    Qed.

    Lemma pb_renaming : relation_renaming f E F
      (pb E rmw0 rf0 co0 data0 addr0 ctrl0)
      (pb F (rename_edges f rmw0) (rename_edges f rf0) (rename_edges f co0)
        (rename_edges f data0) (rename_edges f addr0) (rename_edges f ctrl0)).
    Proof.
      unfold pb. apply relation_renaming_seq; first done.
      - apply relation_renaming_seq; first done.
        + apply relation_renaming_seq; first done.
          * apply prop_renaming.
          * expand_memory. transport.
        + apply relation_renaming_rtc; [done | apply hb_renaming].
      - apply relation_renaming_id_on; [done | transport_class].
    Qed.

    Lemma coherence_order_renaming : relation_renaming f E F
      (rel_union (po_loc E) (com rf0 co0))
      (rel_union (po_loc F) (com (rename_edges f rf0) (rename_edges f co0))).
    Proof. unfold po_loc, com, fr. transport. Qed.

    Lemma atomicity_violation_renaming : relation_renaming f E F
      (rel_intersection (rmw rmw0) (rel_seq (fre E rf0 co0) (coe E co0)))
      (rel_intersection (rmw (rename_edges f rmw0))
        (rel_seq (fre F (rename_edges f rf0) (rename_edges f co0))
          (coe F (rename_edges f co0)))).
    Proof. unfold fre, coe, fr. transport. Qed.
  End Relations.

  Lemma marked_tail_supported E r :
    relation_domain E (rel_seq r (rel_id_on (marked E))) ->
    relation_supported E (rel_seq r (rel_id_on (marked E))).
  Proof.
    intros Hdomain x y Hxy. pose proof Hxy as Htail.
    apply rel_seq_id_on_r in Htail as [_ [Hy _]]. split; last done.
    by eapply relation_domain_right.
  Qed.

  Lemma coherence_order_supported E rf0 co0 :
    relation_supported E (rf rf0) -> relation_supported E (co co0) ->
    relation_supported E (rel_union (po_loc E) (com rf0 co0)).
  Proof.
    intros Hrf Hco x y [[Hpo _] | [H | [H | (z & Hrf' & Hco')]]].
    - by apply po_endpoints.
    - by apply Hrf.
    - by apply Hco.
    - split; [exact (proj2 (Hrf z x Hrf')) | exact (proj2 (Hco z y Hco'))].
  Qed.
End MemoryRenaming.
