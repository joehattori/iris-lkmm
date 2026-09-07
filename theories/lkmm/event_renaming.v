From Stdlib Require Import Arith Lia List.
From stdpp Require Import gmap fin_sets tactics list.
From iris_lkmm.lkmm Require Import execution.
Import ListNotations.

(** Renaming only the allocated event IDs.  Event values retain their labels,
    agents and local positions; initial writes keep their original IDs. *)
Module EventRenaming.
  Export LkmmExecution.

  (** The exact image of a base edge set under renaming of both endpoints.
      Shared by Core-state and complete-candidate correspondences. *)
  Definition rename_edges (f : event_id -> event_id) (edges : edge_set) : edge_set :=
    set_map (fun p : edge => (f p.1, f p.2)) edges.

  Lemma rename_edges_spec f edges x y :
    edge_relation (rename_edges f edges) x y <->
    exists a b, edge_relation edges a b /\ f a = x /\ f b = y.
  Proof.
    unfold edge_relation, rename_edges. rewrite elem_of_map.
    split.
    - intros ([a b] & Heq & Hedge). simpl in Heq. exists a, b. naive_solver.
    - intros (a & b & Hedge & <- & <-). by exists (a, b).
  Qed.

  Lemma rename_edges_forward f edges x y :
    edge_relation edges x y -> edge_relation (rename_edges f edges) (f x) (f y).
  Proof. intros Hedge. apply rename_edges_spec. by exists x, y. Qed.

  Record event_renaming (f : event_id -> event_id) (E F : event_structure) : Prop := {
    renaming_injective : forall x y ex ey,
      lookup_event E x = Some ex -> lookup_event E y = Some ey ->
      f x = f y -> x = y;
    renaming_lookup : forall x ev,
      lookup_event E x = Some ev -> lookup_event F (f x) = Some ev;
    renaming_surjective : forall y ev,
      lookup_event F y = Some ev ->
      exists x, lookup_event E x = Some ev /\ f x = y;
    renaming_initial : forall x loc val,
      lookup_event E x = Some (EInitWrite loc val) -> f x = x
  }.

  Lemma event_renaming_injective f E F x y :
    event_renaming f E F -> in_event_structure E x -> in_event_structure E y ->
    f x = f y -> x = y.
  Proof.
    intros Hren Hx Hy Heq.
    apply in_event_structure_lookup_iff in Hx as [ex Hx], Hy as [ey Hy].
    by eapply (renaming_injective _ _ _ Hren).
  Qed.

  Lemma event_renaming_lookup f E F x :
    event_renaming f E F -> in_event_structure E x ->
    lookup_event F (f x) = lookup_event E x.
  Proof.
    intros Hren Hx. apply in_event_structure_lookup_iff in Hx as [ev Hx].
    rewrite Hx. by apply (renaming_lookup _ _ _ Hren).
  Qed.

  Lemma event_renaming_same_attribute {A} (project : event -> option A) f E F x y :
    event_renaming f E F -> in_event_structure E x -> in_event_structure E y ->
    (same_attribute project F (f x) (f y) <-> same_attribute project E x y).
  Proof.
    intros Hren Hx Hy.
    change ((exists value, (lookup_event F (f x) ≫= project) = Some value /\
        (lookup_event F (f y) ≫= project) = Some value) <->
      exists value, (lookup_event E x ≫= project) = Some value /\
        (lookup_event E y ≫= project) = Some value).
    by rewrite (event_renaming_lookup _ _ _ _ Hren Hx),
      (event_renaming_lookup _ _ _ _ Hren Hy).
  Qed.

  Lemma event_renaming_lookup_iff f E F x ev :
    event_renaming f E F -> in_event_structure E x ->
    (lookup_event F (f x) = Some ev <-> lookup_event E x = Some ev).
  Proof.
    intros Hren Hx. split; last by apply (renaming_lookup _ _ _ Hren).
    intros Hlookup. destruct (renaming_surjective _ _ _ Hren _ _ Hlookup)
      as (old & Hold & Heq).
    apply in_event_structure_lookup_iff in Hx as [ex Hx].
    assert (old = x) as -> by (eapply (renaming_injective _ _ _ Hren); eauto).
    done.
  Qed.

  Lemma event_renaming_wf f E F :
    event_renaming f E F -> event_structure_wf E -> event_structure_wf F.
  Proof.
    intros Hren HE x y t n lx ly Hx Hy.
    destruct (renaming_surjective _ _ _ Hren _ _ Hx) as (a & Ha & <-).
    destruct (renaming_surjective _ _ _ Hren _ _ Hy) as (b & Hb & <-).
    by rewrite (HE a b t n lx ly Ha Hb).
  Qed.

  Lemma event_renaming_po f E F x y :
    event_renaming f E F -> in_event_structure E x -> in_event_structure E y ->
    (po F (f x) (f y) <-> po E x y).
  Proof.
    intros Hren Hx Hy. unfold po.
    setoid_rewrite (event_renaming_lookup_iff f E F x _ Hren Hx).
    setoid_rewrite (event_renaming_lookup_iff f E F y _ Hren Hy). done.
  Qed.

  Lemma event_renaming_barrier f E F x kind :
    event_renaming f E F -> in_event_structure E x ->
    (event_has_barrier_kind F kind (f x) <-> event_has_barrier_kind E kind x).
  Proof.
    intros Hren Hx. rewrite !event_has_barrier_kind_lookup.
    setoid_rewrite (event_renaming_lookup_iff f E F x _ Hren Hx). done.
  Qed.

  Lemma event_renaming_entries f E F :
    event_renaming f E F ->
    map_to_list F ≡ₚ (fun p : event_id * event => (f p.1, p.2)) <$> map_to_list E.
  Proof.
    intros Hren. apply NoDup_Permutation.
    - apply NoDup_map_to_list.
    - apply NoDup_fmap_2_strong; last apply NoDup_map_to_list.
      intros [x ex] [y ey] Hx Hy Heq.
      apply elem_of_map_to_list in Hx. apply elem_of_map_to_list in Hy.
      simpl in Heq. injection Heq as Hxy ->.
      assert (x = y) as -> by (eapply (renaming_injective _ _ _ Hren); eauto). done.
    - intros [y ev]. rewrite (elem_of_map_to_list F y ev), list_elem_of_fmap.
      split.
      + intros Hy. destruct (renaming_surjective _ _ _ Hren _ _ Hy) as (x & Hx & <-).
        exists (x, ev). split; first done. by apply elem_of_map_to_list.
      + intros ([x ex] & Heq & Hx). simpl in Heq. injection Heq as Hy Hev. subst y ex.
        apply elem_of_map_to_list in Hx. by apply (renaming_lookup _ _ _ Hren).
  Qed.
End EventRenaming.
