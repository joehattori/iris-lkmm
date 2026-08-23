From stdpp Require Import fin_map_dom gmap sets.
From iris.base_logic Require Import invariants.
From iris.proofmode Require Import proofmode.
From iris_lkmm.logic Require Import rcu_ghost.

Module RcuGhostGateExamples.
  Import RcuGhost.

  Section lifecycle.
    Context `{!rcuG Σ}.

    Definition reader0_open : gmap rscs_id unit := {[0 := tt]}.

    Definition reader0_snapshot : gset rscs_id := dom reader0_open.

    Definition gp7_pending_map : gmap gp_id gp_status := {[7 := GpPending reader0_snapshot 0]}.

    Definition reader0_closed : gmap rscs_id unit := delete 0 reader0_open.

    Definition gp7_done_map : gmap gp_id gp_status :=
      <[7 := GpDone reader0_snapshot 0 1]> gp7_pending_map.

    Definition lifecycle_result (γ : rcu_names) : iProp Σ :=
      rcu_auth γ reader0_closed gp7_done_map 1 ∗
      gp_done γ 7 reader0_snapshot 0 1.

    (** This exercises the complete ghost protocol.  The GP captures reader
        0, the reader consumes its exclusive token on exit, and completion
        returns a persistent done certificate at MaxNat epoch 1. *)
    Example one_reader_gp_reclamation_lifecycle :
      ⊢ |==> ∃ γ, lifecycle_result γ.
    Proof.
      iMod rcu_ghost_alloc as (γ) "Hauth".
      iMod (rcu_reader_enter γ ∅ ∅ 0 0 with "Hauth")
        as "[Hauth Hreader]"; first by apply lookup_empty.
      change (rcu_auth γ reader0_open ∅ 0) with "Hauth".
      iMod (rcu_gp_begin γ reader0_open ∅ 0 7 with "Hauth")
        as "[Hauth Hpending]"; first by apply lookup_empty.
      change (rcu_auth γ reader0_open gp7_pending_map 0) with "Hauth".
      change (gp_pending γ 7 reader0_snapshot 0) with "Hpending".
      iMod (rcu_reader_exit γ reader0_open gp7_pending_map 0 0
        with "[$Hauth $Hreader]") as "Hauth".
      change (rcu_auth γ reader0_closed gp7_pending_map 0) with "Hauth".
      iMod (rcu_gp_finish γ reader0_closed gp7_pending_map 0 7
        reader0_snapshot 0 with "[$Hauth $Hpending]")
        as "[Hauth #Hdone]".
      { rewrite /reader0_snapshot /reader0_closed /reader0_open.
        set_solver. }
      change (rcu_auth γ reader0_closed gp7_done_map 1) with "Hauth".
      iModIntro. iExists γ. rewrite /lifecycle_result.
      iFrame "Hauth". iExact "Hdone".
    Qed.

  End lifecycle.

End RcuGhostGateExamples.
