From Stdlib Require Import Relations.Relation_Operators.
From stdpp Require Import gmap tactics.
From iris_lkmm.lkmm Require Import event_renaming.

(** Relation algebra for a bijection on allocated events. Reflexive closures
    also contain identities outside the event structure; [relation_domain]
    permits these without assuming global injectivity of the renaming. *)
Module RelationRenaming.
  Export EventRenaming.

  Definition relation_domain E (r : relation) : Prop :=
    forall x y, r x y -> x = y \/
      (in_event_structure E x /\ in_event_structure E y).

  Lemma relation_domain_left E r x y :
    relation_domain E r -> r x y -> in_event_structure E x -> in_event_structure E y.
  Proof. intros H Hr Hx. destruct (H x y Hr) as [-> | [_ Hy]]; done. Qed.

  Lemma relation_domain_right E r x y :
    relation_domain E r -> r x y -> in_event_structure E y -> in_event_structure E x.
  Proof. intros H Hr Hy. destruct (H x y Hr) as [-> | [Hx _]]; done. Qed.

  Lemma relation_domain_seq E r s :
    relation_domain E r -> relation_domain E s -> relation_domain E (rel_seq r s).
  Proof.
    intros Hr Hs x y (z & Hxz & Hzy).
    destruct (Hr x z Hxz) as [-> | [Hx Hz]];
      destruct (Hs z y Hzy) as [-> | [Hz' Hy]]; auto.
  Qed.

  Lemma relation_domain_tc E r : relation_domain E r -> relation_domain E (tc r).
  Proof.
    intros Hr x y Hxy. induction Hxy; first by apply Hr.
    destruct IHHxy1 as [-> | [Hx Hy]]; destruct IHHxy2 as [-> | [Hy' Hz]]; auto.
  Qed.

  Lemma relation_domain_rtc E r : relation_domain E r -> relation_domain E (rtc r).
  Proof.
    intros Hr x y Hxy. induction Hxy; [by apply Hr | by left |].
    destruct IHHxy1 as [-> | [Hx Hy]]; destruct IHHxy2 as [-> | [Hy' Hz]]; auto.
  Qed.

  (** Unlike [relation_domain], this excludes all unallocated endpoints. *)
  Definition relation_supported E (r : relation) : Prop :=
    forall x y, r x y -> in_event_structure E x /\ in_event_structure E y.

  Lemma relation_supported_domain E r : relation_supported E r -> relation_domain E r.
  Proof. intros H x y Hr. right. by apply H. Qed.

  Lemma relation_supported_tc E r : relation_supported E r -> relation_supported E (tc r).
  Proof.
    intros Hr x y Hxy. induction Hxy; first by apply Hr.
    naive_solver.
  Qed.

  Record relation_renaming f E F (r s : relation) : Prop := {
    relation_renaming_source : relation_domain E r;
    relation_renaming_target : relation_domain F s;
    relation_renaming_iff : forall x y,
      in_event_structure E x -> in_event_structure E y ->
      (s (f x) (f y) <-> r x y)
  }.

  Section Renaming.
    Context (f : event_id -> event_id) (E F : event_structure).
    Context (Hren : event_renaming f E F).

    Lemma renaming_member x : in_event_structure E x -> in_event_structure F (f x).
    Proof.
      intros [ev Hx]%in_event_structure_lookup_iff.
      eapply lookup_event_in. by apply (renaming_lookup _ _ _ Hren).
    Qed.

    Lemma renaming_preimage y : in_event_structure F y ->
      exists x, in_event_structure E x /\ f x = y.
    Proof.
      intros [ev Hy]%in_event_structure_lookup_iff.
      destruct (renaming_surjective _ _ _ Hren _ _ Hy) as (x & Hx & <-).
      exists x. split; last done. by eapply lookup_event_in.
    Qed.

    Lemma renaming_event_predicate (p : event -> Prop) x :
      in_event_structure E x ->
      ((exists ev, lookup_event F (f x) = Some ev /\ p ev) <->
        exists ev, lookup_event E x = Some ev /\ p ev).
    Proof. intros Hx. by rewrite (event_renaming_lookup _ _ _ _ Hren Hx). Qed.

    Lemma renaming_attribute {A} (p : event -> option A) x :
      in_event_structure E x ->
      (lookup_event F (f x) ≫= p) = (lookup_event E x ≫= p).
    Proof. intros Hx. by rewrite (event_renaming_lookup _ _ _ _ Hren Hx). Qed.

    Lemma rename_edges_supported edges :
      relation_supported E (edge_relation edges) ->
      relation_supported F (edge_relation (rename_edges f edges)).
    Proof.
      intros H x y (a & b & Hab & <- & <-)%rename_edges_spec.
      destruct (H a b Hab). split; by apply renaming_member.
    Qed.

    Lemma relation_renaming_edges edges :
      relation_supported E (edge_relation edges) ->
      relation_renaming f E F (edge_relation edges) (edge_relation (rename_edges f edges)).
    Proof.
      intros Hends. constructor.
      - by apply relation_supported_domain.
      - apply relation_supported_domain. by apply rename_edges_supported.
      - intros x y Hx Hy. split; last apply rename_edges_forward.
        intros (a & b & Hab & Ha & Hb)%rename_edges_spec.
        destruct (Hends a b Hab) as [Hina Hinb].
        assert (a = x) as -> by (eapply (event_renaming_injective _ _ _ _ _ Hren); eauto).
        assert (b = y) as -> by (eapply (event_renaming_injective _ _ _ _ _ Hren); eauto).
        done.
    Qed.

    Lemma relation_renaming_po : relation_renaming f E F (po E) (po F).
    Proof.
      constructor; try (apply relation_supported_domain; intros x y Hxy; by apply po_endpoints).
      intros x y Hx Hy. by apply event_renaming_po.
    Qed.

    Lemma relation_renaming_ext r s r' s' :
      (forall x y, r x y <-> r' x y) -> (forall x y, s x y <-> s' x y) ->
      relation_renaming f E F r' s' -> relation_renaming f E F r s.
    Proof.
      intros Hr Hs [HE HF H]. constructor.
      - intros x y Hxy. apply HE. by apply Hr.
      - intros x y Hxy. apply HF. by apply Hs.
      - intros x y Hx Hy. by rewrite Hr, Hs, (H x y Hx Hy).
    Qed.

    Lemma relation_renaming_forward r s :
      relation_renaming f E F r s -> relation_supported E r ->
      forall x y, r x y -> s (f x) (f y).
    Proof.
      intros [_ _ H] Hends x y Hxy. destruct (Hends x y Hxy).
      by apply H.
    Qed.

    Lemma relation_renaming_backward r s :
      relation_renaming f E F r s -> relation_supported F s ->
      forall x y, s x y -> exists a b, r a b /\ f a = x /\ f b = y.
    Proof.
      intros [_ _ H] Hends x y Hxy. destruct (Hends x y Hxy) as [Hx Hy].
      destruct (renaming_preimage x Hx) as (a & Ha & <-).
      destruct (renaming_preimage y Hy) as (b & Hb & <-).
      exists a, b. split; last done. by apply H.
    Qed.

    Lemma relation_renaming_id : relation_renaming f E F rel_id rel_id.
    Proof.
      constructor; try (intros x y H; by left).
      intros x y Hx Hy. split; last congruence.
      by apply (event_renaming_injective _ _ _ _ _ Hren).
    Qed.

    Lemma relation_renaming_id_on p q :
      (forall x, in_event_structure E x -> (q (f x) <-> p x)) ->
      relation_renaming f E F (rel_id_on p) (rel_id_on q).
    Proof.
      intros Hp. constructor; try (intros x y [H _]; by left).
      intros x y Hx Hy. unfold rel_id_on.
      rewrite (Hp x Hx). split; intros [Heq H]; split; try done.
      - by apply (event_renaming_injective _ _ _ _ _ Hren).
      - congruence.
    Qed.

    Lemma relation_renaming_union r1 r2 s1 s2 :
      relation_renaming f E F r1 s1 -> relation_renaming f E F r2 s2 ->
      relation_renaming f E F (rel_union r1 r2) (rel_union s1 s2).
    Proof.
      intros [Hr1 Hs1 H1] [Hr2 Hs2 H2]. constructor.
      - intros x y [H | H]; [by apply Hr1 | by apply Hr2].
      - intros x y [H | H]; [by apply Hs1 | by apply Hs2].
      - intros x y Hx Hy. unfold rel_union. by rewrite (H1 x y Hx Hy), (H2 x y Hx Hy).
    Qed.

    (** The second relation is a filter, e.g. [ext], which need not itself
        have allocated endpoints. *)
    Lemma relation_renaming_intersection r1 r2 s1 s2 :
      relation_renaming f E F r1 s1 ->
      (forall x y, in_event_structure E x -> in_event_structure E y ->
        (s2 (f x) (f y) <-> r2 x y)) ->
      relation_renaming f E F (rel_intersection r1 r2) (rel_intersection s1 s2).
    Proof.
      intros [Hr Hs H1] H2. constructor.
      - intros x y [H _]. by apply Hr.
      - intros x y [H _]. by apply Hs.
      - intros x y Hx Hy. unfold rel_intersection.
        by rewrite (H1 x y Hx Hy), (H2 x y Hx Hy).
    Qed.

    Lemma relation_renaming_difference r1 r2 s1 s2 :
      relation_renaming f E F r1 s1 -> relation_renaming f E F r2 s2 ->
      relation_renaming f E F (rel_difference r1 r2) (rel_difference s1 s2).
    Proof.
      intros [Hr Hs H1] [_ _ H2]. constructor.
      - intros x y [H _]. by apply Hr.
      - intros x y [H _]. by apply Hs.
      - intros x y Hx Hy. unfold rel_difference.
        by rewrite (H1 x y Hx Hy), (H2 x y Hx Hy).
    Qed.

    Lemma relation_renaming_inverse r s :
      relation_renaming f E F r s ->
      relation_renaming f E F (rel_inverse r) (rel_inverse s).
    Proof.
      intros [Hr Hs H]. constructor.
      - intros x y Hyx. destruct (Hr y x Hyx); naive_solver.
      - intros x y Hyx. destruct (Hs y x Hyx); naive_solver.
      - intros x y Hx Hy. by apply H.
    Qed.

    Lemma relation_renaming_seq r1 r2 s1 s2 :
      relation_renaming f E F r1 s1 -> relation_renaming f E F r2 s2 ->
      relation_renaming f E F (rel_seq r1 r2) (rel_seq s1 s2).
    Proof.
      intros [Hr1 Hs1 H1] [Hr2 Hs2 H2]. constructor.
      - by apply relation_domain_seq.
      - by apply relation_domain_seq.
      - intros x y Hx Hy. split.
        + intros (z & Hxz & Hzy).
          assert (in_event_structure F z) as Hz.
          { eapply relation_domain_left; [exact Hs1 | exact Hxz | by apply renaming_member]. }
          destruct (renaming_preimage z Hz) as (a & Ha & <-).
          exists a. split; [by apply H1 | by apply H2].
        + intros (z & Hxz & Hzy).
          assert (in_event_structure E z) as Hz.
          { eapply relation_domain_left; [exact Hr1 | exact Hxz | done]. }
          exists (f z). split; [by apply H1 | by apply H2].
    Qed.

    Lemma relation_renaming_optional r s :
      relation_renaming f E F r s -> relation_renaming f E F (optional r) (optional s).
    Proof. intros H. apply relation_renaming_union; [apply relation_renaming_id | done]. Qed.

    Lemma relation_renaming_tc r s :
      relation_renaming f E F r s -> relation_renaming f E F (tc r) (tc s).
    Proof.
      intros [Hr Hs H]. constructor; try by apply relation_domain_tc.
      intros x y Hx Hy. split.
      - intros Hpath. remember (f x) as a eqn:Ha. remember (f y) as b eqn:Hb.
        induction Hpath in x, y, Hx, Hy, Ha, Hb |- *.
        + subst. apply t_step. by apply H.
        + assert (in_event_structure F y0) as Hmid.
          { eapply relation_domain_left; [by apply relation_domain_tc | exact Hpath1 |].
            rewrite Ha. by apply renaming_member. }
          destruct (renaming_preimage y0 Hmid) as (middle & Hmiddle & Heq).
          eapply t_trans; [by eapply IHHpath1 | by eapply IHHpath2].
      - intros Hpath. induction Hpath.
        + apply t_step. by apply H.
        + assert (in_event_structure E y) as Hmid.
          { eapply relation_domain_left; [by apply relation_domain_tc | exact Hpath1 | done]. }
          eapply t_trans; [by apply IHHpath1 | by apply IHHpath2].
    Qed.

    Lemma relation_renaming_rtc r s :
      relation_renaming f E F r s -> relation_renaming f E F (rtc r) (rtc s).
    Proof.
      intros [Hr Hs H]. constructor; try by apply relation_domain_rtc.
      intros x y Hx Hy. split.
      - intros Hpath. remember (f x) as a eqn:Ha. remember (f y) as b eqn:Hb.
        induction Hpath in x, y, Hx, Hy, Ha, Hb |- *.
        + subst. apply rt_step. by apply H.
        + assert (x = y) as -> by (eapply (event_renaming_injective _ _ _ _ _ Hren); eauto; congruence).
          apply rt_refl.
        + assert (in_event_structure F y0) as Hmid.
          { eapply relation_domain_left; [by apply relation_domain_rtc | exact Hpath1 |].
            rewrite Ha. by apply renaming_member. }
          destruct (renaming_preimage y0 Hmid) as (middle & Hmiddle & Heq).
          eapply rt_trans; [by eapply IHHpath1 | by eapply IHHpath2].
      - intros Hpath. induction Hpath.
        + apply rt_step. by apply H.
        + apply rt_refl.
        + assert (in_event_structure E y) as Hmid.
          { eapply relation_domain_left; [by apply relation_domain_rtc | exact Hpath1 | done]. }
          eapply rt_trans; [by apply IHHpath1 | by apply IHHpath2].
    Qed.

    Lemma relation_renaming_domain r s x :
      relation_renaming f E F r s -> in_event_structure E x ->
      (rel_domain s (f x) <-> rel_domain r x).
    Proof.
      intros [Hr Hs H] Hx. split.
      - intros [y Hxy].
        assert (in_event_structure F y) as Hy.
        { eapply relation_domain_left; [exact Hs | exact Hxy | by apply renaming_member]. }
        destruct (renaming_preimage y Hy) as (z & Hz & <-). exists z. by apply H.
      - intros [y Hxy]. exists (f y). apply H; try done.
        by eapply relation_domain_left.
    Qed.

    Lemma relation_renaming_range r s x :
      relation_renaming f E F r s -> in_event_structure E x ->
      (rel_range s (f x) <-> rel_range r x).
    Proof.
      intros H Hx. apply (relation_renaming_domain (rel_inverse r) (rel_inverse s));
        last done. by apply relation_renaming_inverse.
    Qed.

    Lemma relation_renaming_empty r s :
      relation_renaming f E F r s -> relation_supported F s ->
      rel_is_empty r -> rel_is_empty s.
    Proof.
      intros [_ _ H] Hends Hempty x y Hxy.
      destruct (Hends x y Hxy) as [Hx Hy].
      destruct (renaming_preimage x Hx) as (a & Ha & <-).
      destruct (renaming_preimage y Hy) as (b & Hb & <-).
      apply (Hempty a b). by apply H.
    Qed.

    Lemma relation_renaming_irreflexive r s :
      relation_renaming f E F r s ->
      (forall x, s x x -> in_event_structure F x) ->
      rel_irreflexive r -> rel_irreflexive s.
    Proof.
      intros [_ _ H] Hends Hirr x Hxx.
      destruct (renaming_preimage x (Hends x Hxx)) as (a & Ha & <-).
      apply (Hirr a). by apply H.
    Qed.
    Lemma relation_renaming_acyclic r s :
      relation_renaming f E F r s -> relation_supported F s ->
      rel_acyclic r -> rel_acyclic s.
    Proof.
      intros H Hends. apply relation_renaming_irreflexive.
      - by apply relation_renaming_tc.
      - intros x Hxx. exact (proj1 (relation_supported_tc _ _ Hends x x Hxx)).
    Qed.
  End Renaming.
End RelationRenaming.
