From Stdlib Require Import List.
From iris.base_logic.lib Require Import fancy_updates.
From iris.proofmode Require Import proofmode.
From iris_lkmm.lkmm Require Import rcu_matching.
From iris_lkmm.lang Require Import core_rcu.
From iris_lkmm.operational Require Import lkmm_machine lkmm_coupled.
From iris_lkmm.logic Require Import graph_correspondence rcu_ghost state_interp wp.
Import ListNotations.

Module LkmmWpRcu.
  Import LkmmMachine LkmmCoupled LkmmCoreRcu RcuMatching.
  Import LkmmGraphCorrespondence RcuGhost LkmmStateInterp LkmmWp.

  Definition rcu_next_view agent v := CoupledThreadView
    (ThreadView
      (emitted_thread v.(coupled_view_core).(view_thread)
        v.(coupled_view_core).(view_thread).(thread_registers))
      (S v.(coupled_view_core).(view_event_index))
      (v.(coupled_view_core).(view_actions) ++ [CoreEmit agent])) None.

  Definition gp_wait_view v locks := CoupledThreadView v.(coupled_view_core) (Some locks).

  Local Lemma lookup_coupled_thread_view_pending p agent v :
    lookup_coupled_thread_view p agent = Some v ->
    p.(coupled_position_state).(coupled_machine).(pending_gp) !! agent =
      v.(coupled_view_pending_gp).
  Proof.
    unfold lookup_coupled_thread_view. intros Hview.
    apply fmap_Some in Hview as (cv & Hcore & Heq). by subst v.
  Qed.

  Local Lemma read_lock_step P s a next agent thread :
    s.(coupled_machine).(machine_core).(core_threads) !! agent = Some thread ->
    thread.(thread_statement) = SRcuReadLock -> executing_agent a = agent ->
    coupled_step P s (CoupledMachineAction a) next ->
    a = ReadLock agent /\ next = CoupledState
      (with_core s.(coupled_machine) (emit_rcu s.(coupled_machine) agent thread BarrierRcuLock))
      s.(coupled_builder).
  Proof.
    intros Hlookup Hstmt Hagent Hstep.
    revert Hagent. inversion Hstep as [m m' b action Hmachine |]; subst. intros Hagent.
    destruct Hmachine as
      [m core' action actual Hthread Hordinary Hready Hcore |
       m owner actual [Hthread Hstatement] Hready |
       m owner actual lock rest [Hthread Hstatement] Hready Hstack |
       m owner actual [Hthread Hstatement] Hready |
       m owner actual locks [Hthread Hstatement] Hpending Hclosed];
      simpl in Hagent; subst; cbn in Hlookup;
      try rewrite Hagent in Hthread;
      rewrite Hlookup in Hthread; injection Hthread as <-;
      try solve [rewrite Hstmt in Hordinary; done | rewrite Hstmt in Hstatement; discriminate].
    done.
  Qed.

  Local Lemma read_unlock_step P s a next agent thread :
    s.(coupled_machine).(machine_core).(core_threads) !! agent = Some thread ->
    thread.(thread_statement) = SRcuReadUnlock -> executing_agent a = agent ->
    coupled_step P s (CoupledMachineAction a) next ->
    a = ReadUnlock agent /\
      next = CoupledState
        (with_core s.(coupled_machine) (emit_rcu s.(coupled_machine) agent thread BarrierRcuUnlock))
      s.(coupled_builder) /\
      exists lock rest, open_readers s.(coupled_machine) agent = lock :: rest.
  Proof.
    intros Hlookup Hstmt Hagent Hstep.
    revert Hagent. inversion Hstep as [m m' b action Hmachine |]; subst. intros Hagent.
    destruct Hmachine as
      [m core' action actual Hthread Hordinary Hready Hcore |
       m owner actual [Hthread Hstatement] Hready |
       m owner actual lock rest [Hthread Hstatement] Hready Hstack |
       m owner actual [Hthread Hstatement] Hready |
       m owner actual locks [Hthread Hstatement] Hpending Hclosed];
      simpl in Hagent; subst; cbn in Hlookup;
      try rewrite Hagent in Hthread;
      rewrite Hlookup in Hthread; injection Hthread as <-;
      try solve [rewrite Hstmt in Hordinary; done | rewrite Hstmt in Hstatement; discriminate].
    split_and!; try done. by exists lock, rest.
  Qed.

  Local Lemma begin_gp_step P s a next agent thread :
    s.(coupled_machine).(machine_core).(core_threads) !! agent = Some thread ->
    thread.(thread_statement) = SSynchronizeRcu ->
    s.(coupled_machine).(pending_gp) !! agent = None -> executing_agent a = agent ->
    coupled_step P s (CoupledMachineAction a) next ->
    a = BeginGp agent /\
    next = CoupledState (begin_gp s.(coupled_machine) agent) s.(coupled_builder).
  Proof.
    intros Hlookup Hstmt Hpending Hagent Hstep.
    revert Hagent. inversion Hstep as [m m' b action Hmachine |]; subst. intros Hagent.
    destruct Hmachine as
      [m core' action actual Hthread Hordinary Hready Hcore |
       m owner actual [Hthread Hstatement] Hready |
       m owner actual lock rest [Hthread Hstatement] Hready Hstack |
       m owner actual [Hthread Hstatement] Hready |
       m owner actual locks [Hthread Hstatement] Hwaiting Hclosed];
      simpl in Hagent; subst; cbn in Hlookup, Hpending;
      try rewrite Hagent in Hthread;
      rewrite Hlookup in Hthread; injection Hthread as <-;
      try solve [rewrite Hstmt in Hordinary; done | congruence].
    done.
  Qed.

  Local Lemma finish_gp_step P s a next agent thread locks :
    s.(coupled_machine).(machine_core).(core_threads) !! agent = Some thread ->
    s.(coupled_machine).(pending_gp) !! agent = Some locks -> executing_agent a = agent ->
    coupled_step P s (CoupledMachineAction a) next ->
    a = FinishGp agent /\ next = CoupledState
      (finish_gp s.(coupled_machine) agent thread locks) s.(coupled_builder).
  Proof.
    intros Hlookup Hpending Hagent Hstep.
    revert Hagent. inversion Hstep as [m m' b action Hmachine |]; subst. intros Hagent.
    destruct (pending_agent_only_finishes _ _ _ _ _ _ Hmachine Hagent Hpending) as [-> _].
    inversion Hmachine as [| | | |m0 owner actual saved [Hthread Hstmt] Hwaiting Hclosed]; subst.
    cbn in Hlookup, Hpending. rewrite Hlookup in Hthread. injection Hthread as <-.
    rewrite Hpending in Hwaiting. injection Hwaiting as <-. done.
  Qed.

  Local Lemma begin_gp_project_next prefix s suffix final agent v :
    lookup_coupled_thread_view
      (CoupledExecutionPosition prefix s (CoupledMachineAction (BeginGp agent) :: suffix) final)
      agent = Some v ->
    lookup_coupled_thread_view
      (CoupledExecutionPosition (prefix ++ [CoupledMachineAction (BeginGp agent)])
        (CoupledState (begin_gp s.(coupled_machine) agent) s.(coupled_builder)) suffix final)
      agent = Some (gp_wait_view v (all_open_readers s.(coupled_machine))).
  Proof.
    unfold lookup_coupled_thread_view, lookup_thread_view, coupled_position_to_core.
    intros Hview. apply fmap_Some in Hview as (cv & Hcore & Heq). subst v.
    apply fmap_Some in Hcore as (thread & Hlookup & Heq). subst cv.
    cbn. rewrite Hlookup lookup_insert_eq /= flat_map_app /= app_nil_r. reflexivity.
  Qed.

  Local Lemma finish_gp_project_next prefix s suffix final agent v locks :
    lookup_coupled_thread_view
      (CoupledExecutionPosition prefix s (CoupledMachineAction (FinishGp agent) :: suffix) final)
      agent = Some v ->
    lookup_coupled_thread_view
      (CoupledExecutionPosition (prefix ++ [CoupledMachineAction (FinishGp agent)])
        (CoupledState
          (finish_gp s.(coupled_machine) agent v.(coupled_view_core).(view_thread) locks)
          s.(coupled_builder)) suffix final) agent = Some (rcu_next_view agent v).
  Proof.
    unfold lookup_coupled_thread_view, lookup_thread_view, coupled_position_to_core.
    intros Hview. apply fmap_Some in Hview as (cv & Hcore & Heq). subst v.
    apply fmap_Some in Hcore as (thread & Hlookup & Heq). subst cv.
    cbn. rewrite lookup_insert_eq lookup_delete_eq /=.
    unfold next_agent_index at 1. cbn. rewrite lookup_insert_eq /=.
    rewrite flat_map_app /= /agent_actions filter_app /=.
    rewrite filter_cons_True; last done. reflexivity.
  Qed.

  Local Lemma rcu_project_next prefix s suffix final agent v kind a :
    lookup_coupled_thread_view
      (CoupledExecutionPosition prefix s (CoupledMachineAction a :: suffix) final)
      agent = Some v ->
    v.(coupled_view_pending_gp) = None -> core_actions_of a = [CoreEmit agent] ->
    lookup_coupled_thread_view
      (CoupledExecutionPosition (prefix ++ [CoupledMachineAction a])
        (CoupledState (with_core s.(coupled_machine)
          (emit_rcu s.(coupled_machine) agent v.(coupled_view_core).(view_thread) kind))
          s.(coupled_builder)) suffix final) agent = Some (rcu_next_view agent v).
  Proof.
    intros Hview Hpending Haction.
    unfold lookup_coupled_thread_view, lookup_thread_view, coupled_position_to_core in *.
    apply fmap_Some in Hview as (cv & Hcore & Heq). subst v.
    apply fmap_Some in Hcore as (thread & Hlookup & Heq). subst cv.
    cbn in Hpending |- *. rewrite lookup_insert_eq.
    unfold next_agent_index at 1. cbn. rewrite lookup_insert_eq /= Hpending.
    rewrite flat_map_app /= Haction /agent_actions filter_app /=.
    rewrite filter_cons_True; last done. reflexivity.
  Qed.

  Local Lemma rcu_event_id P G prefix s suffix final agent v kind a eid pending certs :
    lookup_coupled_thread_view
      (CoupledExecutionPosition prefix s (CoupledMachineAction a :: suffix) final) agent = Some v ->
    coupled_position P G (CoupledExecutionPosition (prefix ++ [CoupledMachineAction a])
      (CoupledState (State
        (emit_rcu s.(coupled_machine) agent v.(coupled_view_core).(view_thread) kind) pending certs)
        s.(coupled_builder)) suffix final) ->
    lookup_event G.(candidate_events) eid =
      Some (EAgent agent v.(coupled_view_core).(view_event_index) (LBarrier kind)) ->
    s.(coupled_machine).(machine_core).(core_next_id) = eid.
  Proof.
    intros Hview Hpos Hevent.
    pose proof (coupled_position_projection _ _ _ Hpos) as Hcorepos.
    pose proof (candidate_position_events _ _ _ Hcorepos) as Hincluded.
    destruct (coupled_position_consistent_program_graph _ _ _ Hpos) as [Hgraph _].
    destruct (program_graph_wf _ _ Hgraph) as (Hwf & _).
    unfold lookup_coupled_thread_view, lookup_thread_view in Hview.
    apply fmap_Some in Hview as (cv & Hcore & Heq). subst v.
    apply fmap_Some in Hcore as (thread & Hlookup & Heq). subst cv.
    eapply Hwf; last exact Hevent. apply Hincluded. apply lookup_insert_eq.
  Qed.

  Local Lemma position_rcu_pair P G p lock unlock :
    coupled_position P G p ->
    rcu_rscs p.(coupled_position_state).(coupled_machine).(machine_core).(core_events) lock unlock ->
    rcu_rscs G.(candidate_events) lock unlock.
  Proof.
    intros Hpos Hpair.
    destruct (coupled_position_projection _ _ _ Hpos)
      as (Hprefix & Hsuffix & Hcomplete & Hevents & _).
    pose proof (core_run_allocation_wf _ _ _ Hprefix) as Halloc.
    rewrite <- Hevents. clear Hpos Hprefix Hcomplete Hevents.
    cbn in Hsuffix, Halloc |- *.
    revert Halloc Hpair. induction Hsuffix; intros Halloc Hpair; first done.
    apply IHHsuffix.
    - by eapply core_step_preserves_allocation.
    - by eapply core_step_sections_mono.
  Qed.

  (** The final graph's matching pair identifies the current stack head. *)
  Local Lemma unlock_innermost P G prefix s suffix final agent thread lock actual rest :
    core_allocation_wf s.(coupled_machine).(machine_core) ->
    coupled_position P G (CoupledExecutionPosition prefix
      (CoupledState (with_core s.(coupled_machine)
        (emit_rcu s.(coupled_machine) agent thread BarrierRcuUnlock)) s.(coupled_builder))
      suffix final) ->
    open_readers s.(coupled_machine) agent = actual :: rest ->
    rcu_rscs G.(candidate_events) lock s.(coupled_machine).(machine_core).(core_next_id) ->
    actual = lock.
  Proof.
    intros Halloc Hpos Hstack Hpair.
    destruct (coupled_position_consistent_program_graph _ _ _ Hpos) as [Hgraph _].
    destruct (program_graph_wf _ _ Hgraph) as (Hwf & _).
    eapply rcu_rscs_injective; [exact Hwf | | exact Hpair].
    eapply position_rcu_pair; first exact Hpos.
    unfold open_readers, computed_agent_stack in Hstack.
    destruct (token_stack (compute_agent_match_state
      s.(coupled_machine).(machine_core).(core_events) agent) agent)
      as [|token tokens] eqn:Htokens; first discriminate.
    injection Hstack as <- <-.
    apply (proj2 (rcu_rscs_agent_tail_unlock _ _ _
      (RcuToken _ agent _ RcuTokenUnlock) token tokens _ _
      (next_event_tail _ agent (LBarrier BarrierRcuUnlock) Halloc)
      eq_refl eq_refl Htokens)). by left.
  Qed.

  Section rules.
    Context `{!invGS Σ, !stateG Σ}.

    (** [G] names the event; the actual step allocates its reader token. *)
    Lemma wp_read_lock P G γ E agent v lock Φ :
      v.(coupled_view_core).(view_thread).(thread_statement) = SRcuReadLock ->
      v.(coupled_view_pending_gp) = None ->
      lookup_event G.(candidate_events) lock =
        Some (EAgent agent v.(coupled_view_core).(view_event_index) (LBarrier BarrierRcuLock)) ->
      (▷ (event_fact γ lock
          (EAgent agent v.(coupled_view_core).(view_event_index) (LBarrier BarrierRcuLock)) -∗
        reader_token γ.(rcu_name) lock -∗ wp P G γ E agent (rcu_next_view agent v) Φ)) -∗
      wp P G γ E agent v Φ.
    Proof.
      intros Hstmt Hpending Hevent. iIntros "Hwp". iApply wp_lift_step.
      { intros [[Hskip _] _]. congruence. }
      iNext. iIntros (prefix s a suffix final next) "%Hfacts Hstate".
      destruct Hfacts as ([Hpos Hview] & Hagent & Hstep & Hnext).
      pose proof (lookup_coupled_thread_view_lookup _ _ _ Hview) as Hlookup.
      pose proof (lookup_coupled_thread_view_index _ _ _ Hview) as Hindex.
      destruct (read_lock_step _ _ _ _ _ _ Hlookup Hstmt Hagent Hstep) as [-> ->].
      pose proof (rcu_project_next _ _ _ _ _ _ BarrierRcuLock _ Hview Hpending eq_refl) as Hview'.
      pose proof (rcu_event_id _ _ _ _ _ _ _ _ _ _ _ _ _ Hview Hnext Hevent) as Hid.
      pose proof (core_run_allocation_wf _ _ _
        (proj1 (coupled_position_projection _ _ _ Hpos))) as Halloc.
      iMod (state_interp_read_lock _ _ _ _ _ _ Hstep Halloc with "Hstate")
        as "(Hstate & Hthread & #Hlock & Hreader)".
      cbn in Hid, Hindex. rewrite Hid Hindex.
      iModIntro. iExists (rcu_next_view agent v). iFrame "Hstate Hthread".
      iSplit; first done. iApply ("Hwp" with "Hlock Hreader").
    Qed.

    Lemma wp_read_unlock P G γ E agent v lock unlock Φ :
      v.(coupled_view_core).(view_thread).(thread_statement) = SRcuReadUnlock ->
      v.(coupled_view_pending_gp) = None ->
      lookup_event G.(candidate_events) unlock =
        Some (EAgent agent v.(coupled_view_core).(view_event_index) (LBarrier BarrierRcuUnlock)) ->
      rcu_rscs G.(candidate_events) lock unlock ->
      reader_token γ.(rcu_name) lock -∗
      (▷ (event_fact γ unlock
          (EAgent agent v.(coupled_view_core).(view_event_index) (LBarrier BarrierRcuUnlock)) -∗
        wp P G γ E agent (rcu_next_view agent v) Φ)) -∗
      wp P G γ E agent v Φ.
    Proof.
      intros Hstmt Hpending Hevent Hpair. iIntros "Hreader Hwp". iApply wp_lift_step.
      { intros [[Hskip _] _]. congruence. }
      iNext. iIntros (prefix s a suffix final next) "%Hfacts Hstate".
      destruct Hfacts as ([Hpos Hview] & Hagent & Hstep & Hnext).
      pose proof (lookup_coupled_thread_view_lookup _ _ _ Hview) as Hlookup.
      pose proof (lookup_coupled_thread_view_index _ _ _ Hview) as Hindex.
      destruct (read_unlock_step _ _ _ _ _ _ Hlookup Hstmt Hagent Hstep)
        as (-> & -> & actual & rest & Hstack).
      pose proof (rcu_project_next _ _ _ _ _ _ BarrierRcuUnlock _ Hview Hpending eq_refl) as Hview'.
      pose proof (rcu_event_id _ _ _ _ _ _ _ _ _ _ _ _ _ Hview Hnext Hevent) as Hid.
      pose proof (core_run_allocation_wf _ _ _
        (proj1 (coupled_position_projection _ _ _ Hpos))) as Halloc.
      assert (actual = lock) as ->.
      { eapply unlock_innermost; [exact Halloc | exact Hnext | exact Hstack |].
        by rewrite Hid. }
      iDestruct "Hstate" as "[Hstate Hthread]".
      iMod (state_interp_read_unlock _ _ _ _ _ _ _ _ Hstep Halloc Hstack
        with "[$Hstate $Hthread $Hreader]") as "(Hstate & Hthread & #Hunlock)".
      cbn in Hid, Hindex. rewrite Hid Hindex.
      iModIntro. iExists (rcu_next_view agent v). iFrame "Hstate Hthread".
      iSplit; first done. iApply ("Hwp" with "Hunlock").
    Qed.

    (** Beginning a GP emits no event. Its snapshot and start epoch depend
        on the execution, so the continuation accepts every captured set. *)
    Lemma wp_begin_gp P G γ E agent v Φ :
      v.(coupled_view_core).(view_thread).(thread_statement) = SSynchronizeRcu ->
      v.(coupled_view_pending_gp) = None ->
      (▷ ∀ locks start,
        gp_pending γ.(rcu_name) (gp_encoding agent v.(coupled_view_core).(view_event_index))
          (list_to_set locks) start -∗
        wp P G γ E agent (gp_wait_view v locks) Φ) -∗
      wp P G γ E agent v Φ.
    Proof.
      intros Hstmt Hpending. iIntros "Hwp". iApply wp_lift_step.
      { intros [[Hskip _] _]. congruence. }
      iNext. iIntros (prefix s a suffix final next) "%Hfacts Hstate".
      destruct Hfacts as ([Hpos Hview] & Hagent & Hstep & Hnext).
      pose proof (lookup_coupled_thread_view_lookup _ _ _ Hview) as Hlookup.
      pose proof (lookup_coupled_thread_view_index _ _ _ Hview) as Hindex.
      pose proof (lookup_coupled_thread_view_pending _ _ _ Hview) as Hwaiting.
      rewrite Hpending in Hwaiting.
      destruct (begin_gp_step _ _ _ _ _ _ Hlookup Hstmt Hwaiting Hagent Hstep) as [-> ->].
      pose proof (begin_gp_project_next _ _ _ _ _ _ Hview) as Hview'.
      pose proof (core_run_allocation_wf _ _ _
        (proj1 (coupled_position_projection _ _ _ Hpos))) as Halloc.
      iMod (state_interp_begin_gp _ _ _ _ _ _ Hstep Halloc with "Hstate")
        as "(Hstate & Hthread & Hpending)".
      cbn in Hindex. rewrite Hindex.
      iModIntro. iExists (gp_wait_view v (all_open_readers s.(coupled_machine))).
      iFrame "Hstate Hthread". iSplit; first done. iApply ("Hwp" with "Hpending").
    Qed.

    (** Finishing consumes the pending token for this GP and returns persistent
        completion and synchronization-event facts. Certificate allocation is
        obtained from the machine prefix, independently of the final graph. *)
    Lemma wp_finish_gp P G γ E agent v locks start sync Φ :
      v.(coupled_view_core).(view_thread).(thread_statement) = SSynchronizeRcu ->
      v.(coupled_view_pending_gp) = Some locks ->
      lookup_event G.(candidate_events) sync =
        Some (EAgent agent v.(coupled_view_core).(view_event_index) (LBarrier BarrierSyncRcu)) ->
      gp_pending γ.(rcu_name) (gp_encoding agent v.(coupled_view_core).(view_event_index))
        (list_to_set locks) start -∗
      (▷ ∀ finish,
        event_fact γ sync
          (EAgent agent v.(coupled_view_core).(view_event_index) (LBarrier BarrierSyncRcu)) -∗
        gp_done γ.(rcu_name) (gp_encoding agent v.(coupled_view_core).(view_event_index))
          (list_to_set locks) start finish -∗
        wp P G γ E agent (rcu_next_view agent v) Φ) -∗
      wp P G γ E agent v Φ.
    Proof.
      intros Hstmt Hpending Hevent. iIntros "Hpending Hwp". iApply wp_lift_step.
      { intros [[Hskip _] _]. congruence. }
      iNext. iIntros (prefix s a suffix final next) "%Hfacts Hstate".
      destruct Hfacts as ([Hpos Hview] & Hagent & Hstep & Hnext).
      pose proof (lookup_coupled_thread_view_lookup _ _ _ Hview) as Hlookup.
      pose proof (lookup_coupled_thread_view_index _ _ _ Hview) as Hindex.
      pose proof (lookup_coupled_thread_view_pending _ _ _ Hview) as Hwaiting.
      rewrite Hpending in Hwaiting.
      destruct (finish_gp_step _ _ _ _ _ _ _ Hlookup Hwaiting Hagent Hstep) as [-> ->].
      pose proof (finish_gp_project_next _ _ _ _ _ _ locks Hview) as Hview'.
      pose proof (rcu_event_id _ _ _ _ _ _ _ _ _ _ _ _ _ Hview Hnext Hevent) as Hid.
      pose proof (coupled_run_machine_projection _ _ _ _ (proj1 Hpos)) as Hrun.
      pose proof (run_allocation_wf _ _ _ Hrun) as Halloc.
      pose proof (run_certificate_events_allocated _ _ _ Hrun) as Hcerts.
      iDestruct "Hstate" as "[Hstate Hthread]".
      cbn in Hindex. iEval (rewrite <- Hindex) in "Hpending".
      iMod (state_interp_finish_gp _ _ _ _ _ _ _ _ Hstep Halloc Hcerts
        with "[$Hstate $Hthread $Hpending]") as "(Hstate & Hthread & #Hsync & #Hdone)".
      cbn in Hid. rewrite Hid Hindex.
      iModIntro. iExists (rcu_next_view agent v). iFrame "Hstate Hthread".
      iSplit; first done. iApply ("Hwp" with "Hsync Hdone").
    Qed.
  End rules.
End LkmmWpRcu.
