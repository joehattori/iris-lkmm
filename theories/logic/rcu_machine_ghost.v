From Stdlib Require Import List.
From stdpp Require Import fin_map_dom gmap.
From iris.base_logic Require Import invariants.
From iris.proofmode Require Import proofmode.
From iris_lkmm.operational Require Import
  rcu_machine rcu_machine_safety.
From iris_lkmm.logic Require Import rcu_ghost.

(** End-to-end bridge from completed operational grace periods to the Iris
    reclamation update. *)
Module RcuMachineGhost.
  Import RcuMachine RcuMachineSafety RcuGhost.

  Section bridge.
    Context `{!rcuG Σ}.

    Theorem completed_machine_gp_reclamation_update
        P agents actions s cert γ gps epoch gid start :
      RcuMachine.run P agents initial_state actions s ->
      In cert s.(gp_certificates) ->
      rcu_auth γ (open_map_from_locks (snapshot agents s)) gps epoch ∗
        gp_pending γ gid (lock_set cert.(gc_snapshot)) start ==∗
      rcu_auth γ
          (open_map_from_locks (snapshot agents s))
          (<[gid := GpDone (lock_set cert.(gc_snapshot))
            start (S epoch)]> gps) (S epoch) ∗
        gp_done γ gid (lock_set cert.(gc_snapshot)) start (S epoch).
    Proof.
      intros Hrun Hcert. apply rcu_gp_finish.
      by eapply completed_run_certificate_enables_iris_finish.
    Qed.

    Theorem completed_machine_gp_reclamation_frame
        P agents actions s cert γ gps epoch gid start (R : iProp Σ) :
      RcuMachine.run P agents initial_state actions s ->
      In cert s.(gp_certificates) ->
      rcu_auth γ
          (open_map_from_locks (snapshot agents s)) gps epoch ∗
        gp_pending γ gid (lock_set cert.(gc_snapshot)) start ∗ R ==∗
      rcu_auth γ
          (open_map_from_locks (snapshot agents s))
          (<[gid := GpDone (lock_set cert.(gc_snapshot))
            start (S epoch)]> gps) (S epoch) ∗
        gp_done γ gid (lock_set cert.(gc_snapshot)) start (S epoch) ∗ R.
    Proof.
      intros Hrun Hcert. apply rcu_gp_finish_frame.
      by eapply completed_run_certificate_enables_iris_finish.
    Qed.

  End bridge.

End RcuMachineGhost.
