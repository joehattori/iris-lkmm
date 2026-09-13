From Stdlib Require Import List.
From stdpp Require Import fin_map_dom gmap tactics.
From iris.base_logic Require Import invariants.
From iris.proofmode Require Import proofmode.
From iris_lkmm.lkmm Require Import rcu_matching.
From iris_lkmm.lang Require Import core_rcu.
From iris_lkmm.operational Require Import lkmm_machine lkmm_coupled.
From iris_lkmm.logic Require Import rcu_ghost.

(** Completed Core-machine GPs justify the Iris completion update.  The
    authoritative open-reader map and the registered pending-GP token remain
    explicit resources; a machine certificate alone does not manufacture them. *)
Module LkmmMachineGhost.
  Import LkmmMachine LkmmCoupled RcuGhost.
  Import RcuMatching LkmmCoreRcu.

  Definition open_reader_map (s : LkmmMachine.state) : gmap rscs_id unit :=
    list_to_map (map (fun lock => (lock, tt)) (all_open_readers s)).

  Lemma dom_open_reader_map s :
    dom (open_reader_map s) = (list_to_set (all_open_readers s) : gset rscs_id).
  Proof.
    unfold open_reader_map. rewrite dom_list_to_map_L.
    induction (all_open_readers s) as [|lock locks IH]; simpl; first done. by f_equal.
  Qed.

  Lemma open_reader_map_lookup s lock :
    event_structure_wf s.(machine_core).(core_events) ->
    (open_reader_map s !! lock = Some tt <-> exists agent, In lock (open_readers s agent)).
  Proof.
    intros HE. rewrite <- (unmatched_lock_in_agent_stack _ _ HE).
    change (open_reader_map s !! lock = Some tt <-> In lock (all_open_readers s)).
    rewrite -list_elem_of_In -(elem_of_list_to_set (C := gset rscs_id))
      -dom_open_reader_map elem_of_dom.
    destruct (open_reader_map s !! lock) as [[]|]; naive_solver.
  Qed.

  Lemma open_reader_map_next_fresh s :
    core_allocation_wf s.(machine_core) ->
    open_reader_map s !! s.(machine_core).(core_next_id) = None.
  Proof.
    intros Hwf. apply eq_None_not_Some. intros [[] Hopen].
    apply (open_reader_map_lookup _ _ (proj1 Hwf)) in Hopen as (agent & Hin).
    destruct (computed_agent_stack_lookup _ _ _ (proj1 Hwf) Hin) as (index & Hlookup).
    by rewrite (core_next_id_fresh _ Hwf) in Hlookup.
  Qed.

  Lemma open_reader_map_read_lock s agent thread :
    core_allocation_wf s.(machine_core) ->
    open_reader_map (with_core s (emit_rcu s agent thread BarrierRcuLock)) =
      <[s.(machine_core).(core_next_id) := tt]> (open_reader_map s).
  Proof.
    intros Hwf.
    pose proof (next_event_tail s.(machine_core) agent (LBarrier BarrierRcuLock) Hwf) as Htail.
    pose proof (add_single_event_allocation_wf s.(machine_core) agent thread
      (LBarrier BarrierRcuLock) thread.(thread_registers) ∅ ∅ ∅ Hwf) as Hwf'.
    pose proof (open_reader_map_next_fresh _ Hwf) as Hfresh.
    apply map_eq. intros lock. apply option_eq. intros [].
    rewrite lookup_insert_Some
      (open_reader_map_lookup (with_core s (emit_rcu s agent thread BarrierRcuLock)) lock (proj1 Hwf'))
      (open_reader_map_lookup s lock (proj1 Hwf)).
    assert (forall reader, open_readers (with_core s (emit_rcu s agent thread BarrierRcuLock)) reader =
      if decide (agent = reader) then s.(machine_core).(core_next_id) :: open_readers s reader
      else open_readers s reader) as Hstacks.
    { intros reader. unfold open_readers, emit_rcu. cbn.
      destruct (decide (agent = reader)) as [<-|Hother].
      - exact (computed_agent_stack_insert_lock _ _ _
          (RcuToken _ agent _ RcuTokenLock) Htail eq_refl eq_refl).
      - exact (computed_agent_stack_insert_other _ _
          (EAgent agent (next_agent_index s.(machine_core) agent) (LBarrier BarrierRcuLock))
          (RcuToken _ agent _ RcuTokenLock) reader (proj1 Htail) eq_refl Hother). }
    assert (forall reader, ~ In s.(machine_core).(core_next_id) (open_readers s reader)) as Hnotopen.
    { intros reader Hin.
      assert (open_reader_map s !! s.(machine_core).(core_next_id) = Some tt) as Hlookup.
      { apply (open_reader_map_lookup _ _ (proj1 Hwf)). by exists reader. }
      by rewrite Hfresh in Hlookup. }
    split.
    - intros (reader & Hin). rewrite Hstacks in Hin.
      destruct (decide (agent = reader)); cbn in Hin; naive_solver.
    - intros [[<- _]|(_ & reader & Hin)].
      + exists agent. rewrite Hstacks. case_decide; cbn; naive_solver.
      + exists reader. rewrite Hstacks. case_decide; cbn; naive_solver.
  Qed.

  Lemma open_reader_map_read_unlock s agent thread lock rest :
    core_allocation_wf s.(machine_core) ->
    open_readers s agent = lock :: rest ->
    open_reader_map (with_core s (emit_rcu s agent thread BarrierRcuUnlock)) =
      delete lock (open_reader_map s).
  Proof.
    intros Hwf Hstack.
    pose proof Hstack as Hids. unfold open_readers, computed_agent_stack in Hids.
    destruct (token_stack (compute_agent_match_state s.(machine_core).(core_events) agent) agent)
      as [|lock_token tokens] eqn:Htokens; first discriminate.
    injection Hids as <- <-.
    pose proof (next_event_tail s.(machine_core) agent (LBarrier BarrierRcuUnlock) Hwf) as Htail.
    pose proof (add_single_event_allocation_wf s.(machine_core) agent thread
      (LBarrier BarrierRcuUnlock) thread.(thread_registers) ∅ ∅ ∅ Hwf) as Hwf'.
    assert (forall reader, open_readers (with_core s (emit_rcu s agent thread BarrierRcuUnlock)) reader =
      if decide (agent = reader) then token_id <$> tokens else open_readers s reader) as Hstacks.
    { intros reader. unfold open_readers, emit_rcu. cbn.
      destruct (decide (agent = reader)) as [<-|Hother].
      - exact (computed_agent_stack_insert_unlock _ _ _
          (RcuToken _ agent _ RcuTokenUnlock) lock_token tokens Htail eq_refl eq_refl Htokens).
      - exact (computed_agent_stack_insert_other _ _
          (EAgent agent (next_agent_index s.(machine_core) agent) (LBarrier BarrierRcuUnlock))
          (RcuToken _ agent _ RcuTokenUnlock) reader (proj1 Htail) eq_refl Hother). }
    assert (rcu_rscs (emit_rcu s agent thread BarrierRcuUnlock).(core_events)
      lock_token.(token_id) s.(machine_core).(core_next_id)) as Hclosed.
    { apply (proj2 (rcu_rscs_agent_tail_unlock _ _ _
        (RcuToken _ agent _ RcuTokenUnlock) lock_token tokens _ _
        Htail eq_refl eq_refl Htokens)). by left. }
    assert (forall reader,
      ~ In lock_token.(token_id) (open_readers
        (with_core s (emit_rcu s agent thread BarrierRcuUnlock)) reader)) as Hnotopen.
    { intros reader Hin. exact (computed_agent_stack_unmatched _ _ _ _ (proj1 Hwf') Hin Hclosed). }
    apply map_eq. intros rid. apply option_eq. intros [].
    rewrite lookup_delete_Some
      (open_reader_map_lookup (with_core s (emit_rcu s agent thread BarrierRcuUnlock)) rid (proj1 Hwf'))
      (open_reader_map_lookup s rid (proj1 Hwf)).
    split.
    - intros (reader & Hin). split.
      { intros Heq. apply (Hnotopen reader). by rewrite Heq. }
      exists reader. rewrite Hstacks in Hin.
      destruct (decide (agent = reader)) as [<-|]; last done.
      rewrite Hstack. by right.
    - intros (Hneq & reader & Hin). exists reader. rewrite Hstacks.
      destruct (decide (agent = reader)) as [<-|]; last done.
      rewrite Hstack in Hin. cbn in Hin. naive_solver.
  Qed.

  Lemma all_closed_open_reader_map_disjoint s locks :
    event_structure_wf s.(machine_core).(core_events) ->
    all_closed s.(machine_core).(core_events) locks ->
    (list_to_set locks : gset rscs_id) ## dom (open_reader_map s).
  Proof.
    intros Hwf Hclosed. apply elem_of_disjoint. intros lock Hcaptured Hopen.
    rewrite elem_of_list_to_set list_elem_of_In in Hcaptured.
    apply elem_of_dom in Hopen as [[] Hlookup].
    apply (open_reader_map_lookup _ _ Hwf) in Hlookup as (agent & Hin).
    destruct (Hclosed lock Hcaptured) as (unlock & Hmatched).
    by eapply computed_agent_stack_unmatched.
  Qed.

  Lemma open_reader_map_finish_gp s agent thread locks :
    core_allocation_wf s.(machine_core) ->
    open_reader_map (finish_gp s agent thread locks) = open_reader_map s.
  Proof.
    intros Hwf. unfold open_reader_map, all_open_readers. cbn.
    rewrite compute_rcu_matching_insert_non_rcu; last done.
    - done.
    - by apply core_next_id_fresh.
  Qed.

  Lemma completed_certificate_enables_iris_finish P actions s cert :
    LkmmMachine.run P (initial_state P) actions s -> In cert s.(gp_certificates) ->
    (list_to_set cert.(gc_captured_readers) : gset rscs_id) ## dom (open_reader_map s).
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
        gp_pending γ gid (list_to_set cert.(gc_captured_readers)) start ==∗
      rcu_auth γ (open_reader_map s)
          (<[gid := GpDone (list_to_set cert.(gc_captured_readers)) start (S epoch)]> gps) (S epoch) ∗
        gp_done γ gid (list_to_set cert.(gc_captured_readers)) start (S epoch).
    Proof.
      intros Hrun Hcert. apply rcu_gp_finish.
      by eapply completed_certificate_enables_iris_finish.
    Qed.

    Theorem completed_machine_gp_reclamation_frame
        P actions s cert γ gps epoch gid start (R : iProp Σ) :
      LkmmMachine.run P (initial_state P) actions s -> In cert s.(gp_certificates) ->
      rcu_auth γ (open_reader_map s) gps epoch ∗
        gp_pending γ gid (list_to_set cert.(gc_captured_readers)) start ∗ R ==∗
      rcu_auth γ (open_reader_map s)
          (<[gid := GpDone (list_to_set cert.(gc_captured_readers)) start (S epoch)]> gps) (S epoch) ∗
        gp_done γ gid (list_to_set cert.(gc_captured_readers)) start (S epoch) ∗ R.
    Proof.
      intros Hrun Hcert. apply rcu_gp_finish_frame.
      by eapply completed_certificate_enables_iris_finish.
    Qed.

    Theorem completed_coupled_gp_reclamation_frame
        P actions s cert γ gps epoch gid start (R : iProp Σ) :
      coupled_run P (initial_coupled P) actions s ->
      In cert s.(coupled_machine).(gp_certificates) ->
      rcu_auth γ (open_reader_map s.(coupled_machine)) gps epoch ∗
        gp_pending γ gid (list_to_set cert.(gc_captured_readers)) start ∗ R ==∗
      rcu_auth γ (open_reader_map s.(coupled_machine))
          (<[gid := GpDone (list_to_set cert.(gc_captured_readers)) start (S epoch)]> gps) (S epoch) ∗
        gp_done γ gid (list_to_set cert.(gc_captured_readers)) start (S epoch) ∗ R.
    Proof.
      intros Hrun Hcert.
      pose proof (coupled_run_machine_projection _ _ _ _ Hrun) as Hmachine.
      exact (completed_machine_gp_reclamation_frame P (machine_actions actions)
        s.(coupled_machine) cert γ gps epoch gid start R Hmachine Hcert).
    Qed.
  End bridge.
End LkmmMachineGhost.
