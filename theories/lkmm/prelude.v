From Stdlib Require Import Relations.Relation_Operators.
From stdpp Require Import base tactics.

(** Shared foundations for the relational LKMM model.  This module remains
    independent of Iris. *)
Module LkmmPrelude.
  Definition event_id := nat.
  Definition relation := event_id -> event_id -> Prop.

  Definition rel_empty : relation := fun _ _ => False.

  Definition rel_is_empty (r : relation) : Prop := forall x y, ~ r x y.

  Definition rel_id : relation := eq.

  (** CAT's [[S]]: identity restricted to the event set [S]. *)
  Definition rel_id_on (pred : event_id -> Prop) : relation := fun x y => x = y /\ pred x.

  Definition rel_union (r1 r2 : relation) : relation := fun x y => r1 x y \/ r2 x y.

  Definition rel_intersection (r1 r2 : relation) : relation := fun x y => r1 x y /\ r2 x y.

  Definition rel_difference (r1 r2 : relation) : relation := fun x y => r1 x y /\ ~ r2 x y.

  Definition rel_inverse (r : relation) : relation := fun x y => r y x.

  Definition rel_seq (r1 r2 : relation) : relation := fun x z => exists y, r1 x y /\ r2 y z.

  Definition optional (r : relation) : relation := rel_union rel_id r.

  Definition tc (r : relation) : relation := clos_trans event_id r.

  Definition rtc (r : relation) : relation := clos_refl_trans event_id r.

  Definition rel_domain (r : relation) (x : event_id) : Prop := exists y, r x y.

  Definition rel_range (r : relation) (y : event_id) : Prop := exists x, r x y.

  Definition rel_included (r1 r2 : relation) : Prop := forall x y, r1 x y -> r2 x y.

  Definition rel_irreflexive (r : relation) : Prop := forall x, ~ r x x.

  Definition rel_acyclic (r : relation) : Prop := rel_irreflexive (tc r).

  Lemma relation_union_l (r₁ r₂ : relation) (x y : event_id) :
    r₁ x y -> rel_union r₁ r₂ x y.
  Proof. intros H; left; exact H. Qed.

  Lemma relation_union_r (r₁ r₂ : relation) (x y : event_id) :
    r₂ x y -> rel_union r₁ r₂ x y.
  Proof. intros H; right; exact H. Qed.

  Lemma rel_included_refl r : rel_included r r.
  Proof. intros x y Hxy. done. Qed.

  Lemma rel_included_trans r1 r2 r3 :
    rel_included r1 r2 -> rel_included r2 r3 -> rel_included r1 r3.
  Proof. intros H12 H23 x y Hxy. apply H23, H12, Hxy. Qed.

  Lemma rel_inverse_involutive r x y :
    rel_inverse (rel_inverse r) x y <-> r x y.
  Proof. done. Qed.

  Lemma rel_seq_assoc r1 r2 r3 x y :
    rel_seq (rel_seq r1 r2) r3 x y <->
    rel_seq r1 (rel_seq r2 r3) x y.
  Proof.
    split.
    - intros (z & (w & Hxw & Hwz) & Hzy).
      exists w. split; first done. by exists z.
    - intros (w & Hxw & z & Hwz & Hzy).
      exists z. split; last done. by exists w.
  Qed.

  Lemma rel_seq_id_on_l pred r x y :
    rel_seq (rel_id_on pred) r x y <-> pred x /\ r x y.
  Proof.
    split.
    - intros (z & [-> Hpred] & Hzy). done.
    - intros [Hpred Hxy]. exists x. split_and!; done.
  Qed.

  Lemma rel_seq_id_on_r r pred x y :
    rel_seq r (rel_id_on pred) x y <-> r x y /\ pred y.
  Proof.
    split.
    - intros (z & Hxz & [-> Hpred]). done.
    - intros [Hxy Hpred]. exists y. split_and!; done.
  Qed.

  Lemma optional_mono r1 r2 :
    rel_included r1 r2 ->
    rel_included (optional r1) (optional r2).
  Proof.
    intros Hr x y [Hxy | Hxy]; [by left | right; by apply Hr].
  Qed.

  Lemma tc_mono r1 r2 :
    rel_included r1 r2 ->
    rel_included (tc r1) (tc r2).
  Proof.
    intros Hr x y Hxy. induction Hxy.
    - apply t_step. by apply Hr.
    - by eapply t_trans.
  Qed.

  Lemma rtc_mono r1 r2 :
    rel_included r1 r2 ->
    rel_included (rtc r1) (rtc r2).
  Proof.
    intros Hr x y Hxy. induction Hxy.
    - apply rt_step. by apply Hr.
    - apply rt_refl.
    - by eapply rt_trans.
  Qed.
End LkmmPrelude.
