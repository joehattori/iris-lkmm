From Stdlib Require Import List Lia.
From stdpp Require Import gmap tactics.
From iris_lkmm.lang Require Import core_agent_replay.
From iris_lkmm.lkmm Require Import rcu_replay.
Import ListNotations.

(** RCU matching along Core execution prefixes.  These facts concern the
    existing Core steps; they impose no new transition rules. *)
Module LkmmCoreRcu.
  Export LkmmCoreAgentReplay RcuReplay.

  Lemma next_event_tail core agent label :
    core_allocation_wf core ->
    rcu_agent_tail core.(core_events) core.(core_next_id)
      (EAgent agent (next_agent_index core agent) label).
  Proof.
    intros Hwf. split; first by apply core_next_id_fresh.
    destruct Hwf as (_ & _ & Hindices).
    destruct label as [kind mode mark loc val | barrier]; simpl; first done.
    destruct barrier; simpl; try done;
      rewrite Forall_forall; intros token Hin;
      destruct (rcu_agent_token_trace_lookup _ _ _ Hin) as [Hagent Hlookup];
      unfold event_of_rcu_token in Hlookup;
      destruct (token_kind token); simpl in Hlookup;
      pose proof (Hindices _ _ _ _ Hlookup) as Hindex;
      unfold rcu_token_le; simpl; naive_solver lia.
  Qed.

  Lemma next_rmw_matching core agent thread mode loc old new regs addr data ctrl reader :
    core_allocation_wf core ->
    compute_agent_match_state
      (add_rmw_events core agent thread mode loc old new regs addr data ctrl).(core_events)
      reader = compute_agent_match_state core.(core_events) reader.
  Proof.
    intros Hwf. cbn.
    rewrite compute_agent_state_insert_non_rcu; last done.
    - rewrite compute_agent_state_insert_non_rcu; [done | by apply core_next_id_fresh | done].
    - apply lookup_insert_None. split; last lia.
      apply eq_None_not_Some. intros [ev Hlookup].
      destruct Hwf as (_ & Hids & _). specialize (Hids _ _ Hlookup). lia.
  Qed.

  Lemma core_step_sections_mono P core a core' :
    core_step P core a core' -> core_allocation_wf core ->
    rel_included (rcu_rscs core.(core_events)) (rcu_rscs core'.(core_events)).
  Proof.
    intros Hstep Hwf. destruct Hstep;
      try solve [intros x y Hxy; exact Hxy];
      try solve [apply rcu_rscs_agent_tail_mono; by apply next_event_tail];
      intros lock unlock [reader Hsection]; exists reader;
      unfold compute_agent_matching, result_of_state in *;
      by rewrite next_rmw_matching.
  Qed.

  Lemma initial_agent_matching P agent :
    compute_agent_match_state (core_initial_state P).(core_events) agent = empty_match_state.
  Proof.
    unfold compute_agent_match_state.
    assert (rcu_agent_token_trace (core_initial_state P).(core_events) agent = []) as ->.
    { apply nil_length_inv. destruct (rcu_agent_token_trace
        (core_initial_state P).(core_events) agent) as [|token tokens] eqn:Htrace; first done.
      exfalso. assert (In token
        (rcu_agent_token_trace (core_initial_state P).(core_events) agent)) as Hin.
      { rewrite Htrace. by left. }
      apply rcu_agent_token_trace_lookup in Hin as [_ Hlookup].
      assert (forall eid ev, lookup_event (∅ : event_structure) eid = Some ev ->
        exists loc val, ev = EInitWrite loc val) as Hempty.
      { intros eid ev Hnone. discriminate Hnone. }
      destruct (insert_initial_events_shape (initial_entries P) 0 ∅ _ _
        Hempty Hlookup) as (loc & val & Hshape).
      unfold event_of_rcu_token in Hshape. discriminate. }
    done.
  Qed.

  (** A Core step either leaves a reader's matcher unchanged or appends that
      reader's next lock/unlock token. *)
  Definition core_matching_update (s s' : core_state) (actor reader : agent_id) : Prop :=
    compute_agent_match_state s'.(core_events) reader =
      compute_agent_match_state s.(core_events) reader \/
    exists token,
      token.(token_agent) = reader /\ reader = actor /\
      token.(token_index) = next_agent_index s reader /\
      rcu_token_valid s'.(core_events) token /\
      compute_agent_match_state s'.(core_events) reader =
        match_token (compute_agent_match_state s.(core_events) reader) token.

  Local Lemma single_event_matching s agent thread label regs addr data ctrl reader :
    core_allocation_wf s ->
    core_matching_update s (add_single_event s agent thread label regs addr data ctrl)
      agent reader.
  Proof.
    intros Halloc. unfold core_matching_update. cbn.
    pose proof (next_event_tail s agent label Halloc) as Htail.
    destruct (rcu_token_of_entry
      (core_next_id s, EAgent agent (next_agent_index s agent) label)) as [token |] eqn:Htoken.
    - destruct (decide (token_agent token = reader)) as [Hagent | Hother].
      + right. exists token.
        pose proof (rcu_token_of_entry_Some _ _ Htoken) as Hentry.
        unfold event_of_rcu_token in Hentry.
        injection Hentry as Hid Howner Hindex Hlabel.
        assert (reader = agent) as -> by congruence.
        split_and!; try congruence.
        * unfold rcu_token_valid, event_of_rcu_token, lookup_event.
          rewrite <- Hid, <- Howner, <- Hindex, <- Hlabel. apply lookup_insert_eq.
        * pose proof (compute_agent_state_insert_tail _ _ _ _ Htail Htoken) as Hmatch.
          by rewrite Hagent in Hmatch.
      + left. exact (compute_agent_state_insert_other _ _ _ _ _ (proj1 Htail) Htoken Hother).
    - left. exact (compute_agent_state_insert_non_rcu _ _ _ _ (proj1 Htail) Htoken).
  Qed.

  Lemma core_step_matching P s a s' reader :
    core_step P s a s' -> core_allocation_wf s ->
    core_matching_update s s' (core_action_agent a) reader.
  Proof.
    intros Hstep Halloc. destruct Hstep;
      try solve [left; done];
      try solve [left; by apply next_rmw_matching];
      by apply single_event_matching.
  Qed.

  Lemma core_step_matching_other P s a s' reader :
    core_step P s a s' -> core_allocation_wf s -> core_action_agent a <> reader ->
    compute_agent_match_state s'.(core_events) reader =
      compute_agent_match_state s.(core_events) reader.
  Proof.
    intros Hstep Halloc Hother.
    destruct (core_step_matching _ _ _ _ reader Hstep Halloc) as [Hsame | (token & _ & Heq & _)];
      congruence.
  Qed.

  Lemma core_run_matching_other P s actions s' reader :
    core_run P s actions s' -> core_allocation_wf s ->
    Forall (fun a => core_action_agent a <> reader) actions ->
    compute_agent_match_state s'.(core_events) reader =
      compute_agent_match_state s.(core_events) reader.
  Proof.
    intros Hrun. induction Hrun; intros Halloc Hother; first done.
    inversion Hother; subst.
    rewrite IHHrun; [by eapply core_step_matching_other |
      by eapply core_step_preserves_allocation | done].
  Qed.

  Lemma core_step_index_mono P s a s' reader :
    core_step P s a s' -> next_agent_index s reader <= next_agent_index s' reader.
  Proof.
    intros Hstep. destruct Hstep; unfold next_agent_index; cbn; try done.
    all: destruct (decide (agent = reader)) as [-> | Hother];
      [rewrite lookup_insert_eq | rewrite lookup_insert_ne by done].
    all: cbn; unfold next_agent_index; done || lia.
  Qed.

  Lemma core_run_unmatched_unlocks_mono P s actions s' reader unlock :
    core_run P s actions s' -> core_allocation_wf s ->
    In unlock (compute_agent_match_state s.(core_events) reader).(match_unmatched_unlocks) ->
    In unlock (compute_agent_match_state s'.(core_events) reader).(match_unmatched_unlocks).
  Proof.
    intros Hrun. induction Hrun; intros Halloc Hin; first done.
    apply IHHrun; first by eapply core_step_preserves_allocation.
    destruct (core_step_matching _ _ _ _ reader H Halloc)
      as [-> | (token & _ & _ & _ & _ & ->)]; first done.
    by apply match_token_unmatched_unlocks_mono.
  Qed.

  (** A section first matched after this prefix has its unlock at a later
      per-agent position.  In particular, an open lock cannot be closed in
      the past when Core execution continues. *)
  Lemma core_run_section_source P s actions s' reader section :
    core_run P s actions s' -> core_allocation_wf s ->
    In section (compute_agent_match_state s'.(core_events) reader).(match_sections) ->
    In section (compute_agent_match_state s.(core_events) reader).(match_sections) \/
    exists index,
      lookup_event s'.(core_events) section.(cs_unlock) =
        Some (EAgent reader index (LBarrier BarrierRcuUnlock)) /\
      next_agent_index s reader <= index.
  Proof.
    intros Hrun. induction Hrun; intros Halloc Hin; first by left.
    assert (core_allocation_wf state2) as Halloc2 by (eapply core_step_preserves_allocation; done).
    destruct (IHHrun Halloc2 Hin) as [Hmid | (index & Hlookup & Hindex)].
    - destruct (core_step_matching _ _ _ _ reader H Halloc)
        as [Hsame | (token & Hagent & _ & Hindex & Hvalid & Hmatch)].
      + left. by rewrite Hsame in Hmid.
      + rewrite Hmatch in Hmid.
        destruct (match_token_section_source _ _ _ Hmid) as [Hold | [Hunlock Hkind]];
          first by left.
        right. exists (token_index token). split; last lia.
        rewrite Hunlock. apply (core_run_events_included _ _ _ _ Hrun Halloc2).
        unfold rcu_token_valid, event_of_rcu_token in Hvalid.
        by rewrite Hagent, Hkind in Hvalid.
    - right. exists index. split; first done.
      pose proof (core_step_index_mono _ _ _ _ reader H). lia.
  Qed.

  Lemma core_unlock_has_open_reader P s agent thread actions final :
    core_allocation_wf s ->
    core_run P (add_single_event s agent thread (LBarrier BarrierRcuUnlock)
      thread.(thread_registers) ∅ ∅ ∅) actions final ->
    rcu_matching_complete final.(core_events) ->
    computed_agent_stack s.(core_events) agent <> [].
  Proof.
    intros Halloc Hrun Hcomplete Hempty.
    set (next := add_single_event s agent thread (LBarrier BarrierRcuUnlock)
      thread.(thread_registers) ∅ ∅ ∅) in *.
    assert (core_allocation_wf next) as Hnext by (apply add_single_event_allocation_wf; done).
    pose proof (core_run_preserves_allocation _ _ _ _ Hrun Hnext) as [Hfinal _].
    pose proof (compute_agent_state_insert_tail _ _ _
      (RcuToken (core_next_id s) agent (next_agent_index s agent) RcuTokenUnlock)
      (next_event_tail s agent (LBarrier BarrierRcuUnlock) Halloc) eq_refl) as Hmatch.
    cbn [token_agent] in Hmatch.
    assert (In s.(core_next_id)
      (compute_agent_match_state next.(core_events) agent).(match_unmatched_unlocks)) as Hbad.
    { unfold next. cbn [add_single_event core_events]. rewrite Hmatch.
      unfold computed_agent_stack in Hempty. cbn [match_token token_kind token_agent].
      destruct (token_stack (compute_agent_match_state s.(core_events) agent) agent);
        simpl in Hempty |- *; [by left | discriminate]. }
    pose proof (core_run_unmatched_unlocks_mono _ _ _ _ _ _ Hrun Hnext Hbad) as Hbad_final.
    rewrite (rcu_matching_complete_agent_unlocks _ agent Hfinal Hcomplete) in Hbad_final. done.
  Qed.

  Lemma core_sync_has_no_open_reader P s agent thread actions final :
    core_allocation_wf s ->
    core_run P (add_single_event s agent thread (LBarrier BarrierSyncRcu)
      thread.(thread_registers) ∅ ∅ ∅) actions final ->
    rcu_replay_wf final.(core_events) ->
    computed_agent_stack s.(core_events) agent = [].
  Proof.
    intros Halloc Hrun [Hcomplete Houtside].
    set (next := add_single_event s agent thread (LBarrier BarrierSyncRcu)
      thread.(thread_registers) ∅ ∅ ∅) in *.
    assert (core_allocation_wf next) as Hnext by (apply add_single_event_allocation_wf; done).
    pose proof (core_run_preserves_allocation _ _ _ _ Hrun Hnext) as [Hfinal _].
    pose proof (core_run_events_included _ _ _ _ Hrun Hnext) as Hfuture.
    pose proof (proj1 (add_single_event_extends s agent thread (LBarrier BarrierSyncRcu)
      thread.(thread_registers) ∅ ∅ ∅ Halloc)) as Hprefix.
    assert (compute_agent_match_state next.(core_events) agent =
      compute_agent_match_state s.(core_events) agent) as Hsame.
    { apply compute_agent_state_insert_non_rcu; [by apply core_next_id_fresh | done]. }
    destruct (computed_agent_stack s.(core_events) agent) as [|lock rest] eqn:Hstack; first done.
    exfalso.
    assert (In lock (computed_agent_stack s.(core_events) agent)) as Hopen.
    { rewrite Hstack. by left. }
    destruct (computed_agent_stack_lookup _ _ _ (proj1 Halloc) Hopen) as [li Hlock].
    pose proof (Hfuture _ _ (Hprefix _ _ Hlock)) as Hlock_final.
    assert (lookup_event final.(core_events) s.(core_next_id) =
      Some (EAgent agent (next_agent_index s agent) (LBarrier BarrierSyncRcu))) as Hgp.
    { apply Hfuture. apply lookup_insert_eq. }
    assert (event_has_barrier_kind final.(core_events) BarrierRcuLock lock) as Hlock_tag.
    { apply event_has_barrier_kind_lookup. eexists. split; [exact Hlock_final | done]. }
    destruct (rcu_matching_complete_covers_lock _ _ Hcomplete Hlock_tag) as [unlock Hsection].
    destruct Hsection as [reader Hsection].
    destruct (compute_agent_matching_section_agent _ _ _ Hfinal Hsection)
      as (li' & ui & Hlock' & _).
    cbn in Hlock'. unfold lookup_event in Hlock_final.
    assert (reader = agent) as -> by congruence.
    assert (rcu_rscs final.(core_events) lock unlock) as Hmatched by (exists agent; done).
    destruct (core_run_section_source _ _ _ _ _ _ Hrun Hnext Hsection)
      as [Hold | (index & Hlookup & Hindex)].
    - rewrite Hsame in Hold.
      apply (computed_agent_stack_unmatched _ _ _ unlock (proj1 Halloc) Hopen).
      exists agent. done.
    - apply (Houtside lock unlock s.(core_next_id) Hmatched).
      + apply event_has_barrier_kind_lookup. eexists. split; [exact Hgp | done].
      + exists agent, li, (next_agent_index s agent),
          (LBarrier BarrierRcuLock), (LBarrier BarrierSyncRcu).
        split_and!; try done. by apply (proj2 (proj2 Halloc) lock agent li (LBarrier BarrierRcuLock)).
      + exists agent, (next_agent_index s agent), index,
          (LBarrier BarrierSyncRcu), (LBarrier BarrierRcuUnlock).
        split_and!; try done.
        unfold next, next_agent_index in Hindex. cbn in Hindex.
        rewrite lookup_insert_eq in Hindex. cbn in Hindex. lia.
  Qed.

  (** These guards are local to the stepping agent and hold for any Core
      schedule that extends to an RCU-well-formed completed event structure. *)
  Theorem core_step_rcu_local_guards P s a next actions final thread :
    core_step P s a next -> core_run P next actions final ->
    core_allocation_wf s -> rcu_replay_wf final.(core_events) ->
    s.(core_threads) !! core_action_agent a = Some thread ->
    (thread.(thread_statement) = SRcuReadUnlock ->
      computed_agent_stack s.(core_events) (core_action_agent a) <> []) /\
    (thread.(thread_statement) = SSynchronizeRcu ->
      computed_agent_stack s.(core_events) (core_action_agent a) = []).
  Proof.
    intros Hstep Hrun Halloc Hrcu Hthread. destruct Hstep; cbn in Hthread |- *;
      simplify_eq; split; intros Hstmt; try congruence.
    - eapply core_unlock_has_open_reader; [done | done | exact (proj1 Hrcu)].
    - by eapply core_sync_has_no_open_reader.
  Qed.

End LkmmCoreRcu.
