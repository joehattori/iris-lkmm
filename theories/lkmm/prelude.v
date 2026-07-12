From stdpp Require Import base relations.
From iris.algebra Require Import auth gmap.
From iris.base_logic Require Import invariants.
From iris.proofmode Require Import proofmode.

(** Compile-time smoke test for the Rocq, stdpp, and Iris dependencies. *)
Module FoundationSmokeTest.
  Definition event_id := nat.
  Definition relation := event_id -> event_id -> Prop.

  Lemma relation_union_l (r₁ r₂ : relation) (x y : event_id) :
    r₁ x y -> (r₁ x y \/ r₂ x y).
  Proof. by left. Qed.
End FoundationSmokeTest.

