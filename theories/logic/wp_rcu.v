From Stdlib Require Import List.
From iris.base_logic.lib Require Import fancy_updates.
From iris.proofmode Require Import proofmode.
From iris_lkmm.lkmm Require Import rcu_matching.
From iris_lkmm.lang Require Import core_rcu.
From iris_lkmm.operational Require Import lkmm_machine lkmm_operational.
From iris_lkmm.logic Require Import graph_correspondence rcu_ghost state_interp wp.
Import ListNotations.

Module LkmmWpRcu.
  Import LkmmMachine LkmmOperational LkmmCoreRcu RcuMatching.
  Import LkmmGraphCorrespondence RcuGhost LkmmStateInterp LkmmWp.

  Definition rcu_next_view agent v := LkmmThreadView
    (ThreadView
      (emitted_thread v.(lkmm_view_core).(view_thread)
        v.(lkmm_view_core).(view_thread).(thread_registers))
      (S v.(lkmm_view_core).(view_event_index))
      (v.(lkmm_view_core).(view_actions) ++ [CoreEmit agent])) None.

  Definition gp_wait_view v locks := LkmmThreadView v.(lkmm_view_core) (Some locks).

  Local Lemma lookup_lkmm_thread_view_pending p agent v :
    lookup_lkmm_thread_view p agent = Some v ->
    p.(lkmm_position_state).(lkmm_machine).(pending_gp) !! agent =
      v.(lkmm_view_pending_gp).
  Proof.
    unfold lookup_lkmm_thread_view. intros Hview.
    apply fmap_Some in Hview as (cv & Hcore & Heq). by subst v.
  Qed.

  Local Lemma read_lock_step P s a next agent thread :
    s.(lkmm_machine).(machine_core).(core_threads) !! agent = Some thread ->
    thread.(thread_statement) = SRcuReadLock -> executing_agent a = agent ->
    lkmm_step P s (LkmmMachineAction a) next ->
    a = ReadLock agent /\ next = LkmmState
      (with_core s.(lkmm_machine) (emit_rcu s.(lkmm_machine) agent thread BarrierRcuLock))
      s.(lkmm_builder).
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
    s.(lkmm_machine).(machine_core).(core_threads) !! agent = Some thread ->
    thread.(thread_statement) = SRcuReadUnlock -> executing_agent a = agent ->
    lkmm_step P s (LkmmMachineAction a) next ->
    a = ReadUnlock agent /\
      next = LkmmState
        (with_core s.(lkmm_machine) (emit_rcu s.(lkmm_machine) agent thread BarrierRcuUnlock))
      s.(lkmm_builder) /\
      exists lock rest, open_readers s.(lkmm_machine) agent = lock :: rest.
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
    s.(lkmm_machine).(machine_core).(core_threads) !! agent = Some thread ->
    thread.(thread_statement) = SSynchronizeRcu ->
    s.(lkmm_machine).(pending_gp) !! agent = None -> executing_agent a = agent ->
    lkmm_step P s (LkmmMachineAction a) next ->
    a = BeginGp agent /\
    next = LkmmState (begin_gp s.(lkmm_machine) agent) s.(lkmm_builder).
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
    s.(lkmm_machine).(machine_core).(core_threads) !! agent = Some thread ->
    s.(lkmm_machine).(pending_gp) !! agent = Some locks -> executing_agent a = agent ->
    lkmm_step P s (LkmmMachineAction a) next ->
    a = FinishGp agent /\ next = LkmmState
      (finish_gp s.(lkmm_machine) agent thread locks) s.(lkmm_builder).
  Proof.
    intros Hlookup Hpending Hagent Hstep.
    revert Hagent. inversion Hstep as [m m' b action Hmachine |]; subst. intros Hagent.
    destruct (pending_agent_only_finishes _ _ _ _ _ _ Hmachine Hagent Hpending) as [-> _].
    inversion Hmachine as [| | | |m0 owner actual saved [Hthread Hstmt] Hwaiting Hclosed]; subst.
    cbn in Hlookup, Hpending. rewrite Hlookup in Hthread. injection Hthread as <-.
    rewrite Hpending in Hwaiting. injection Hwaiting as <-. done.
  Qed.

  Local Lemma begin_gp_project_next prefix s suffix final agent v :
    lookup_lkmm_thread_view
      (LkmmExecutionPosition prefix s (LkmmMachineAction (BeginGp agent) :: suffix) final)
      agent = Some v ->
    lookup_lkmm_thread_view
      (LkmmExecutionPosition (prefix ++ [LkmmMachineAction (BeginGp agent)])
        (LkmmState (begin_gp s.(lkmm_machine) agent) s.(lkmm_builder)) suffix final)
      agent = Some (gp_wait_view v (all_open_readers s.(lkmm_machine))).
  Proof.
    unfold lookup_lkmm_thread_view, lookup_thread_view, lkmm_position_to_core.
    intros Hview. apply fmap_Some in Hview as (cv & Hcore & Heq). subst v.
    apply fmap_Some in Hcore as (thread & Hlookup & Heq). subst cv.
    cbn. rewrite Hlookup lookup_insert_eq /= flat_map_app /= app_nil_r. reflexivity.
  Qed.

  Local Lemma finish_gp_project_next prefix s suffix final agent v locks :
    lookup_lkmm_thread_view
      (LkmmExecutionPosition prefix s (LkmmMachineAction (FinishGp agent) :: suffix) final)
      agent = Some v ->
    lookup_lkmm_thread_view
      (LkmmExecutionPosition (prefix ++ [LkmmMachineAction (FinishGp agent)])
        (LkmmState
          (finish_gp s.(lkmm_machine) agent v.(lkmm_view_core).(view_thread) locks)
          s.(lkmm_builder)) suffix final) agent = Some (rcu_next_view agent v).
  Proof.
    unfold lookup_lkmm_thread_view, lookup_thread_view, lkmm_position_to_core.
    intros Hview. apply fmap_Some in Hview as (cv & Hcore & Heq). subst v.
    apply fmap_Some in Hcore as (thread & Hlookup & Heq). subst cv.
    cbn. rewrite lookup_insert_eq lookup_delete_eq /=.
    unfold next_agent_index at 1. cbn. rewrite lookup_insert_eq /=.
    rewrite flat_map_app /= /agent_actions filter_app /=.
    rewrite filter_cons_True; last done. reflexivity.
  Qed.

  Local Lemma rcu_project_next prefix s suffix final agent v kind a :
    lookup_lkmm_thread_view
      (LkmmExecutionPosition prefix s (LkmmMachineAction a :: suffix) final)
      agent = Some v ->
    v.(lkmm_view_pending_gp) = None -> core_actions_of a = [CoreEmit agent] ->
    lookup_lkmm_thread_view
      (LkmmExecutionPosition (prefix ++ [LkmmMachineAction a])
        (LkmmState (with_core s.(lkmm_machine)
          (emit_rcu s.(lkmm_machine) agent v.(lkmm_view_core).(view_thread) kind))
          s.(lkmm_builder)) suffix final) agent = Some (rcu_next_view agent v).
  Proof.
    intros Hview Hpending Haction.
    unfold lookup_lkmm_thread_view, lookup_thread_view, lkmm_position_to_core in *.
    apply fmap_Some in Hview as (cv & Hcore & Heq). subst v.
    apply fmap_Some in Hcore as (thread & Hlookup & Heq). subst cv.
    cbn in Hpending |- *. rewrite lookup_insert_eq.
    unfold next_agent_index at 1. cbn. rewrite lookup_insert_eq /= Hpending.
    rewrite flat_map_app /= Haction /agent_actions filter_app /=.
    rewrite filter_cons_True; last done. reflexivity.
  Qed.

  Local Lemma rcu_event_id P G prefix s suffix final agent v kind a eid pending certs :
    lookup_lkmm_thread_view
      (LkmmExecutionPosition prefix s (LkmmMachineAction a :: suffix) final) agent = Some v ->
    lkmm_position P G (LkmmExecutionPosition (prefix ++ [LkmmMachineAction a])
      (LkmmState (State
        (emit_rcu s.(lkmm_machine) agent v.(lkmm_view_core).(view_thread) kind) pending certs)
        s.(lkmm_builder)) suffix final) ->
    lookup_event G.(candidate_events) eid =
      Some (EAgent agent v.(lkmm_view_core).(view_event_index) (LBarrier kind)) ->
    s.(lkmm_machine).(machine_core).(core_next_id) = eid.
  Proof.
    intros Hview Hpos Hevent.
    pose proof (lkmm_position_projection _ _ _ Hpos) as Hcorepos.
    pose proof (candidate_position_events _ _ _ Hcorepos) as Hincluded.
    destruct (lkmm_position_consistent_program_graph _ _ _ Hpos) as [Hgraph _].
    destruct (program_graph_wf _ _ Hgraph) as (Hwf & _).
    unfold lookup_lkmm_thread_view, lookup_thread_view in Hview.
    apply fmap_Some in Hview as (cv & Hcore & Heq). subst v.
    apply fmap_Some in Hcore as (thread & Hlookup & Heq). subst cv.
    eapply Hwf; last exact Hevent. apply Hincluded. apply lookup_insert_eq.
  Qed.

  Local Lemma position_rcu_pair P G p lock unlock :
    lkmm_position P G p ->
    rcu_rscs p.(lkmm_position_state).(lkmm_machine).(machine_core).(core_events) lock unlock ->
    rcu_rscs G.(candidate_events) lock unlock.
  Proof.
    intros Hpos Hpair.
    destruct (lkmm_position_projection _ _ _ Hpos)
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
    core_allocation_wf s.(lkmm_machine).(machine_core) ->
    lkmm_position P G (LkmmExecutionPosition prefix
      (LkmmState (with_core s.(lkmm_machine)
        (emit_rcu s.(lkmm_machine) agent thread BarrierRcuUnlock)) s.(lkmm_builder))
      suffix final) ->
    open_readers s.(lkmm_machine) agent = actual :: rest ->
    rcu_rscs G.(candidate_events) lock s.(lkmm_machine).(machine_core).(core_next_id) ->
    actual = lock.
  Proof.
    intros Halloc Hpos Hstack Hpair.
    destruct (lkmm_position_consistent_program_graph _ _ _ Hpos) as [Hgraph _].
    destruct (program_graph_wf _ _ Hgraph) as (Hwf & _).
    eapply rcu_rscs_injective; [exact Hwf | | exact Hpair].
    eapply position_rcu_pair; first exact Hpos.
    unfold open_readers, computed_agent_stack in Hstack.
    destruct (token_stack (compute_agent_match_state
      s.(lkmm_machine).(machine_core).(core_events) agent) agent)
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
      v.(lkmm_view_core).(view_thread).(thread_statement) = SRcuReadLock ->
      v.(lkmm_view_pending_gp) = None ->
      lookup_event G.(candidate_events) lock =
        Some (EAgent agent v.(lkmm_view_core).(view_event_index) (LBarrier BarrierRcuLock)) ->
      (▷ (event_fact γ lock
          (EAgent agent v.(lkmm_view_core).(view_event_index) (LBarrier BarrierRcuLock)) -∗
        reader_token γ.(rcu_name) lock -∗ wp P G γ E agent (rcu_next_view agent v) Φ)) -∗
      wp P G γ E agent v Φ.
    Proof.
      intros Hstmt Hpending Hevent. iIntros "Hwp". iApply wp_lift_step.
      { intros [[Hskip _] _]. congruence. }
      iNext. iIntros (prefix s a suffix final next) "%Hfacts Hstate".
      destruct Hfacts as ([Hpos Hview] & Hagent & Hstep & Hnext).
      pose proof (lookup_lkmm_thread_view_lookup _ _ _ Hview) as Hlookup.
      pose proof (lookup_lkmm_thread_view_index _ _ _ Hview) as Hindex.
      destruct (read_lock_step _ _ _ _ _ _ Hlookup Hstmt Hagent Hstep) as [-> ->].
      pose proof (rcu_project_next _ _ _ _ _ _ BarrierRcuLock _ Hview Hpending eq_refl) as Hview'.
      pose proof (rcu_event_id _ _ _ _ _ _ _ _ _ _ _ _ _ Hview Hnext Hevent) as Hid.
      pose proof (core_run_allocation_wf _ _ _
        (proj1 (lkmm_position_projection _ _ _ Hpos))) as Halloc.
      iMod (state_interp_read_lock _ _ _ _ _ _ Hstep Halloc with "Hstate")
        as "(Hstate & Hthread & #Hlock & Hreader)".
      cbn in Hid, Hindex. rewrite Hid Hindex.
      iModIntro. iExists (rcu_next_view agent v). iFrame "Hstate Hthread".
      iSplit; first done. iApply ("Hwp" with "Hlock Hreader").
    Qed.

    Lemma wp_read_unlock P G γ E agent v lock unlock Φ :
      v.(lkmm_view_core).(view_thread).(thread_statement) = SRcuReadUnlock ->
      v.(lkmm_view_pending_gp) = None ->
      lookup_event G.(candidate_events) unlock =
        Some (EAgent agent v.(lkmm_view_core).(view_event_index) (LBarrier BarrierRcuUnlock)) ->
      rcu_rscs G.(candidate_events) lock unlock ->
      reader_token γ.(rcu_name) lock -∗
      (▷ (event_fact γ unlock
          (EAgent agent v.(lkmm_view_core).(view_event_index) (LBarrier BarrierRcuUnlock)) -∗
        wp P G γ E agent (rcu_next_view agent v) Φ)) -∗
      wp P G γ E agent v Φ.
    Proof.
      intros Hstmt Hpending Hevent Hpair. iIntros "Hreader Hwp". iApply wp_lift_step.
      { intros [[Hskip _] _]. congruence. }
      iNext. iIntros (prefix s a suffix final next) "%Hfacts Hstate".
      destruct Hfacts as ([Hpos Hview] & Hagent & Hstep & Hnext).
      pose proof (lookup_lkmm_thread_view_lookup _ _ _ Hview) as Hlookup.
      pose proof (lookup_lkmm_thread_view_index _ _ _ Hview) as Hindex.
      destruct (read_unlock_step _ _ _ _ _ _ Hlookup Hstmt Hagent Hstep)
        as (-> & -> & actual & rest & Hstack).
      pose proof (rcu_project_next _ _ _ _ _ _ BarrierRcuUnlock _ Hview Hpending eq_refl) as Hview'.
      pose proof (rcu_event_id _ _ _ _ _ _ _ _ _ _ _ _ _ Hview Hnext Hevent) as Hid.
      pose proof (core_run_allocation_wf _ _ _
        (proj1 (lkmm_position_projection _ _ _ Hpos))) as Halloc.
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
        on the execution, so the continuation accepts every captured set.
        The accessor exposes the post-step state to seal client loans against
        this exact snapshot before the next scheduled step. *)
    Lemma wp_begin_gp_acc P G γ E agent v Φ :
      v.(lkmm_view_core).(view_thread).(thread_statement) = SSynchronizeRcu ->
      v.(lkmm_view_pending_gp) = None ->
      (▷ ∀ s locks start,
        ⌜all_open_readers s.(lkmm_machine) = locks⌝ -∗
        state_interp γ s -∗
        gp_pending γ.(rcu_name) (gp_encoding agent v.(lkmm_view_core).(view_event_index))
          (list_to_set locks) start -∗
        |={E}=> state_interp γ s ∗ wp P G γ E agent (gp_wait_view v locks) Φ) -∗
      wp P G γ E agent v Φ.
    Proof.
      intros Hstmt Hpending. iIntros "Hwp". iApply wp_lift_step.
      { intros [[Hskip _] _]. congruence. }
      iNext. iIntros (prefix s a suffix final next) "%Hfacts Hstate".
      destruct Hfacts as ([Hpos Hview] & Hagent & Hstep & Hnext).
      pose proof (lookup_lkmm_thread_view_lookup _ _ _ Hview) as Hlookup.
      pose proof (lookup_lkmm_thread_view_index _ _ _ Hview) as Hindex.
      pose proof (lookup_lkmm_thread_view_pending _ _ _ Hview) as Hwaiting.
      rewrite Hpending in Hwaiting.
      destruct (begin_gp_step _ _ _ _ _ _ Hlookup Hstmt Hwaiting Hagent Hstep) as [-> ->].
      pose proof (begin_gp_project_next _ _ _ _ _ _ Hview) as Hview'.
      pose proof (core_run_allocation_wf _ _ _
        (proj1 (lkmm_position_projection _ _ _ Hpos))) as Halloc.
      iMod (state_interp_begin_gp _ _ _ _ _ _ Hstep Halloc with "Hstate")
        as "(Hstate & Hthread & Hpending)".
      cbn in Hindex. rewrite Hindex.
      iMod ("Hwp" with "[] Hstate Hpending") as "[Hstate Hwp]"; first done.
      iModIntro. iExists (gp_wait_view v (all_open_readers s.(lkmm_machine))).
      iFrame "Hstate Hthread Hwp". done.
    Qed.

    Lemma wp_begin_gp P G γ E agent v Φ :
      v.(lkmm_view_core).(view_thread).(thread_statement) = SSynchronizeRcu ->
      v.(lkmm_view_pending_gp) = None ->
      (▷ ∀ locks start,
        gp_pending γ.(rcu_name) (gp_encoding agent v.(lkmm_view_core).(view_event_index))
          (list_to_set locks) start -∗
        wp P G γ E agent (gp_wait_view v locks) Φ) -∗
      wp P G γ E agent v Φ.
    Proof.
      intros Hstmt Hpending. iIntros "Hwp". iApply wp_begin_gp_acc; try done.
      iNext. iIntros (s locks start _) "Hstate Hpending". iModIntro.
      iFrame "Hstate". iApply ("Hwp" with "Hpending").
    Qed.

    (** Finishing consumes the pending token for this GP and returns persistent
        completion and synchronization-event facts. Certificate allocation is
        obtained from the machine prefix, independently of the final graph.
        The accessor supplies that prefix for client reclamation updates. *)
    Lemma wp_finish_gp_acc P G γ E agent v locks start sync Φ :
      v.(lkmm_view_core).(view_thread).(thread_statement) = SSynchronizeRcu ->
      v.(lkmm_view_pending_gp) = Some locks ->
      lookup_event G.(candidate_events) sync =
        Some (EAgent agent v.(lkmm_view_core).(view_event_index) (LBarrier BarrierSyncRcu)) ->
      gp_pending γ.(rcu_name) (gp_encoding agent v.(lkmm_view_core).(view_event_index))
        (list_to_set locks) start -∗
      (▷ ∀ actions s finish,
        ⌜lkmm_run P (initial_lkmm P) actions s⌝ -∗
        state_interp γ s -∗
        event_fact γ sync
          (EAgent agent v.(lkmm_view_core).(view_event_index) (LBarrier BarrierSyncRcu)) -∗
        gp_done γ.(rcu_name) (gp_encoding agent v.(lkmm_view_core).(view_event_index))
          (list_to_set locks) start finish -∗
        |={E}=> state_interp γ s ∗ wp P G γ E agent (rcu_next_view agent v) Φ) -∗
      wp P G γ E agent v Φ.
    Proof.
      intros Hstmt Hpending Hevent. iIntros "Hpending Hwp". iApply wp_lift_step.
      { intros [[Hskip _] _]. congruence. }
      iNext. iIntros (prefix s a suffix final next) "%Hfacts Hstate".
      destruct Hfacts as ([Hpos Hview] & Hagent & Hstep & Hnext).
      pose proof (lookup_lkmm_thread_view_lookup _ _ _ Hview) as Hlookup.
      pose proof (lookup_lkmm_thread_view_index _ _ _ Hview) as Hindex.
      pose proof (lookup_lkmm_thread_view_pending _ _ _ Hview) as Hwaiting.
      rewrite Hpending in Hwaiting.
      destruct (finish_gp_step _ _ _ _ _ _ _ Hlookup Hwaiting Hagent Hstep) as [-> ->].
      pose proof (finish_gp_project_next _ _ _ _ _ _ locks Hview) as Hview'.
      pose proof (rcu_event_id _ _ _ _ _ _ _ _ _ _ _ _ _ Hview Hnext Hevent) as Hid.
      pose proof (lkmm_run_machine_projection _ _ _ _ (proj1 Hpos)) as Hrun.
      pose proof (run_allocation_wf _ _ _ Hrun) as Halloc.
      pose proof (run_certificate_events_allocated _ _ _ Hrun) as Hcerts.
      iDestruct "Hstate" as "[Hstate Hthread]".
      cbn in Hindex. iEval (rewrite <- Hindex) in "Hpending".
      iMod (state_interp_finish_gp _ _ _ _ _ _ _ _ Hstep Halloc Hcerts
        with "[$Hstate $Hthread $Hpending]") as "(Hstate & Hthread & #Hsync & #Hdone)".
      cbn in Hid. rewrite Hid Hindex.
      iMod ("Hwp" $! _ _ _ (proj1 Hnext) with "Hstate Hsync Hdone") as "[Hstate Hwp]".
      iModIntro. iExists (rcu_next_view agent v). iFrame "Hstate Hthread".
      by iFrame.
    Qed.

    Lemma wp_finish_gp P G γ E agent v locks start sync Φ :
      v.(lkmm_view_core).(view_thread).(thread_statement) = SSynchronizeRcu ->
      v.(lkmm_view_pending_gp) = Some locks ->
      lookup_event G.(candidate_events) sync =
        Some (EAgent agent v.(lkmm_view_core).(view_event_index) (LBarrier BarrierSyncRcu)) ->
      gp_pending γ.(rcu_name) (gp_encoding agent v.(lkmm_view_core).(view_event_index))
        (list_to_set locks) start -∗
      (▷ ∀ finish,
        event_fact γ sync
          (EAgent agent v.(lkmm_view_core).(view_event_index) (LBarrier BarrierSyncRcu)) -∗
        gp_done γ.(rcu_name) (gp_encoding agent v.(lkmm_view_core).(view_event_index))
          (list_to_set locks) start finish -∗
        wp P G γ E agent (rcu_next_view agent v) Φ) -∗
      wp P G γ E agent v Φ.
    Proof.
      intros Hstmt Hpending Hevent. iIntros "Hpending Hwp".
      iApply (wp_finish_gp_acc with "Hpending"); try done.
      iNext. iIntros (actions s finish _) "Hstate #Hsync #Hdone". iModIntro.
      iFrame "Hstate". iApply ("Hwp" with "Hsync Hdone").
    Qed.
  End rules.
End LkmmWpRcu.
