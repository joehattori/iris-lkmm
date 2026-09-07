From stdpp Require Import gmap tactics.
From iris_lkmm.lkmm Require Import event_renaming memory_relations.

(** Preservation of base-relation well-formedness under event-ID renaming.
    Injectivity is needed only on allocated events; edge well-formedness
    supplies that domain for each use below. *)
Module MemoryRenaming.
  Export EventRenaming LkmmMemoryRelations.

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
End MemoryRenaming.
