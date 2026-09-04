From Stdlib Require Import List.
From stdpp Require Import fin_map_dom gmap tactics.
From iris.base_logic Require Import invariants.
From iris.proofmode Require Import proofmode.
From iris_lkmm.operational Require Import lkmm_machine lkmm_coupled.
From iris_lkmm.logic Require Import rcu_ghost.

(** Completed Core-machine GPs justify the Iris completion update.  The
    authoritative open-reader map and the registered pending-GP token remain
    explicit resources; a machine certificate alone does not manufacture them. *)
Module LkmmMachineGhost.
  Import LkmmMachine LkmmCoupled RcuGhost.

  Definition open_reader_map (s : LkmmMachine.state) : gmap rscs_id unit :=
    list_to_map (map (fun lock => (lock, tt)) (snapshot s)).

  Local Lemma dom_open_reader_map s :
    dom (open_reader_map s) = (list_to_set (snapshot s) : gset rscs_id).
  Proof.
    unfold open_reader_map. rewrite dom_list_to_map_L.
    induction (snapshot s) as [|lock locks IH]; simpl; first done. by f_equal.
  Qed.

  Lemma completed_certificate_enables_iris_finish P actions s cert :
    LkmmMachine.run P (initial_state P) actions s -> In cert s.(gp_certificates) ->
    (list_to_set cert.(gc_snapshot) : gset rscs_id) ## dom (open_reader_map s).
  Proof.
    intros Hrun Hcert. rewrite dom_open_reader_map.
    apply elem_of_disjoint. intros lock Hcaptured Hopen.
    rewrite elem_of_list_to_set list_elem_of_In in Hcaptured.
    rewrite elem_of_list_to_set list_elem_of_In in Hopen.
    exact (completed_snapshot_clear P actions s cert Hrun Hcert lock Hcaptured Hopen).
  Qed.

  Section bridge.
    Context `{!rcuG Σ}.

    Theorem completed_machine_gp_reclamation_update P actions s cert γ gps epoch gid start :
      LkmmMachine.run P (initial_state P) actions s -> In cert s.(gp_certificates) ->
      rcu_auth γ (open_reader_map s) gps epoch ∗
        gp_pending γ gid (list_to_set cert.(gc_snapshot)) start ==∗
      rcu_auth γ (open_reader_map s)
          (<[gid := GpDone (list_to_set cert.(gc_snapshot)) start (S epoch)]> gps) (S epoch) ∗
        gp_done γ gid (list_to_set cert.(gc_snapshot)) start (S epoch).
    Proof.
      intros Hrun Hcert. apply rcu_gp_finish.
      by eapply completed_certificate_enables_iris_finish.
    Qed.

    Theorem completed_machine_gp_reclamation_frame
        P actions s cert γ gps epoch gid start (R : iProp Σ) :
      LkmmMachine.run P (initial_state P) actions s -> In cert s.(gp_certificates) ->
      rcu_auth γ (open_reader_map s) gps epoch ∗
        gp_pending γ gid (list_to_set cert.(gc_snapshot)) start ∗ R ==∗
      rcu_auth γ (open_reader_map s)
          (<[gid := GpDone (list_to_set cert.(gc_snapshot)) start (S epoch)]> gps) (S epoch) ∗
        gp_done γ gid (list_to_set cert.(gc_snapshot)) start (S epoch) ∗ R.
    Proof.
      intros Hrun Hcert. apply rcu_gp_finish_frame.
      by eapply completed_certificate_enables_iris_finish.
    Qed.

    Theorem completed_coupled_gp_reclamation_frame
        P actions s cert γ gps epoch gid start (R : iProp Σ) :
      coupled_run P (initial_coupled P) actions s ->
      In cert s.(coupled_machine).(gp_certificates) ->
      rcu_auth γ (open_reader_map s.(coupled_machine)) gps epoch ∗
        gp_pending γ gid (list_to_set cert.(gc_snapshot)) start ∗ R ==∗
      rcu_auth γ (open_reader_map s.(coupled_machine))
          (<[gid := GpDone (list_to_set cert.(gc_snapshot)) start (S epoch)]> gps) (S epoch) ∗
        gp_done γ gid (list_to_set cert.(gc_snapshot)) start (S epoch) ∗ R.
    Proof.
      intros Hrun Hcert.
      pose proof (coupled_run_machine_projection _ _ _ _ Hrun) as Hmachine.
      exact (completed_machine_gp_reclamation_frame P (machine_actions actions)
        s.(coupled_machine) cert γ gps epoch gid start R Hmachine Hcert).
    Qed.
  End bridge.
End LkmmMachineGhost.
