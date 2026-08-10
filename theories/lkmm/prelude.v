From stdpp Require Import base.

(** Shared foundations for the relational LKMM model.  This module remains
    independent of Iris. *)
Module LkmmPrelude.
  Definition event_id := nat.
  Definition relation := event_id -> event_id -> Prop.

  Lemma relation_union_l (r₁ r₂ : relation) (x y : event_id) :
    r₁ x y -> (r₁ x y \/ r₂ x y).
  Proof. intros H; left; exact H. Qed.
End LkmmPrelude.

