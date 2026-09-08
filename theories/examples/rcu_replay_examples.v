From Stdlib Require Import Arith Lia List.
From stdpp Require Import gmap tactics.
From iris_lkmm.lkmm Require Import rcu_renaming rcu_graph.
From iris_lkmm.operational Require Import core_to_machine candidate_encoding rcu_builder.
Import ListNotations.

Module RcuReplayExamples.
  Import RcuRenaming RcuGraph.

  (** Grace periods before and after nested sections of the same agent. *)
  Definition nested_events : event_structure := {[
    0 := EAgent 0 0 (LBarrier BarrierSyncRcu);
    1 := EAgent 0 1 (LBarrier BarrierRcuLock);
    2 := EAgent 0 2 (LBarrier BarrierRcuLock);
    3 := EAgent 0 3 (LBarrier BarrierRcuUnlock);
    4 := EAgent 0 4 (LBarrier BarrierRcuUnlock);
    5 := EAgent 0 5 (LBarrier BarrierSyncRcu)
  ]}.

  Local Lemma nested_lookup eid ev :
    lookup_event nested_events eid = Some ev ->
    (eid = 0 /\ ev = EAgent 0 0 (LBarrier BarrierSyncRcu)) \/
    (eid = 1 /\ ev = EAgent 0 1 (LBarrier BarrierRcuLock)) \/
    (eid = 2 /\ ev = EAgent 0 2 (LBarrier BarrierRcuLock)) \/
    (eid = 3 /\ ev = EAgent 0 3 (LBarrier BarrierRcuUnlock)) \/
    (eid = 4 /\ ev = EAgent 0 4 (LBarrier BarrierRcuUnlock)) \/
    (eid = 5 /\ ev = EAgent 0 5 (LBarrier BarrierSyncRcu)).
  Proof.
    intros Hlookup. unfold lookup_event, nested_events in Hlookup.
    repeat (apply lookup_insert_Some in Hlookup;
      destruct Hlookup as [[<- <-] | [_ Hlookup]]; first naive_solver).
    apply lookup_singleton_Some in Hlookup. naive_solver.
  Qed.

  Local Lemma nested_events_replay_wf : rcu_replay_wf nested_events.
  Proof.
    split; first by vm_compute.
    intros lock unlock gp Hsection Hgp Hbefore Hafter.
    apply event_has_barrier_kind_lookup in Hgp as (ev & Hlookup & Hkind).
    apply nested_lookup in Hlookup.
    destruct Hbefore as (t & i & j & li & lj & Hl & Hg & Hij).
    destruct Hafter as (t' & j' & k & lj' & lk & Hg' & Hu & Hjk).
    apply nested_lookup in Hl. apply nested_lookup in Hg.
    apply nested_lookup in Hg'. apply nested_lookup in Hu.
    naive_solver lia.
  Qed.

  (** Another agent's GP may have an ID between this reader's lock and
      unlock; event-ID order is not program order between agents. *)
  Definition independent_gp_events : event_structure := {[
    0 := EAgent 0 0 (LBarrier BarrierRcuLock);
    1 := EAgent 1 0 (LBarrier BarrierSyncRcu);
    2 := EAgent 0 1 (LBarrier BarrierRcuUnlock)
  ]}.

  Local Lemma independent_gp_replay_wf : rcu_replay_wf independent_gp_events.
  Proof.
    split; first by vm_compute.
    intros lock unlock gp Hsection Hgp Hbefore Hafter.
    apply event_has_barrier_kind_lookup in Hgp as (ev & Hlookup & Hkind).
    unfold lookup_event, independent_gp_events in Hlookup.
    apply lookup_insert_Some in Hlookup as [[<- <-] | [_ Hlookup]];
      first discriminate Hkind.
    apply lookup_insert_Some in Hlookup as [[<- <-] | [_ Hlookup]].
    - destruct Hbefore as (t & i & j & li & lj & Hl & Hg & Hij).
      change (Some (EAgent 1 0 (LBarrier BarrierSyncRcu)) = Some (EAgent t j lj)) in Hg.
      injection Hg as <- <- <-. lia.
    - apply lookup_singleton_Some in Hlookup as [<- <-]. discriminate Hkind.
  Qed.

  (** Closing the inner section is insufficient while its outer section
      still surrounds the GP. *)
  Definition outer_section_gp_events : event_structure := {[
    0 := EAgent 0 0 (LBarrier BarrierRcuLock);
    1 := EAgent 0 1 (LBarrier BarrierRcuLock);
    2 := EAgent 0 2 (LBarrier BarrierRcuUnlock);
    3 := EAgent 0 3 (LBarrier BarrierSyncRcu);
    4 := EAgent 0 4 (LBarrier BarrierRcuUnlock)
  ]}.

  (** The enclosing section produces an [rb] self-edge even without memory
      edges; this also exercises the same-agent internal-GP exclusion. *)
  Example outer_section_gp_rb_cycle :
    rb (Graph outer_section_gp_events ∅ ∅ ∅ ∅ ∅ ∅) 3 3.
  Proof.
    apply gp_in_read_section_rb with (lock := 0) (unlock := 4).
    - change (event_structure_wf outer_section_gp_events).
      intros x y t n lx ly Hx Hy.
      unfold lookup_event, outer_section_gp_events in Hx, Hy.
      repeat (apply lookup_insert_Some in Hx; destruct Hx as [[? ?] | [? Hx]]);
        try apply lookup_singleton_Some in Hx;
        repeat (apply lookup_insert_Some in Hy; destruct Hy as [[? ?] | [? Hy]]);
        try apply lookup_singleton_Some in Hy; naive_solver.
    - exists 0. vm_compute. auto.
    - reflexivity.
    - exists 0, 0, 3, (LBarrier BarrierRcuLock), (LBarrier BarrierSyncRcu).
      split_and!; try reflexivity; lia.
    - exists 0, 3, 4, (LBarrier BarrierSyncRcu), (LBarrier BarrierRcuUnlock).
      split_and!; try reflexivity; lia.
  Qed.

  (** Numeric IDs run backwards here, while each event retains its agent
      and program position.  Matching must follow the positions, not IDs. *)
  Definition reverse_id (i : event_id) : event_id := 5 - i.
  Definition reversed_nested_events : event_structure := {[
    5 := EAgent 0 0 (LBarrier BarrierSyncRcu);
    4 := EAgent 0 1 (LBarrier BarrierRcuLock);
    3 := EAgent 0 2 (LBarrier BarrierRcuLock);
    2 := EAgent 0 3 (LBarrier BarrierRcuUnlock);
    1 := EAgent 0 4 (LBarrier BarrierRcuUnlock);
    0 := EAgent 0 5 (LBarrier BarrierSyncRcu)
  ]}.

  Local Lemma reverse_nested_renaming :
    event_renaming reverse_id nested_events reversed_nested_events.
  Proof.
    constructor.
    - intros x y ex ey Hx Hy Heq. apply nested_lookup in Hx, Hy.
      unfold reverse_id in Heq. naive_solver lia.
    - intros x ev Hx. apply nested_lookup in Hx.
      repeat destruct Hx as [[-> ->] | Hx]; try reflexivity.
      destruct Hx as [-> ->]. reflexivity.
    - intros y ev Hy. unfold lookup_event, reversed_nested_events in Hy.
      repeat (apply lookup_insert_Some in Hy; destruct Hy as [[<- <-] | [_ Hy]];
        first (match goal with
          |- exists x, lookup_event _ x = Some (EAgent _ ?n _) /\ _ =>
            exists n; split; reflexivity
          end)).
      apply lookup_singleton_Some in Hy as [<- <-]. exists 5. split; reflexivity.
    - intros x loc val Hx. apply nested_lookup in Hx. naive_solver.
  Qed.

  Example reversed_ids_preserve_nested_rcu :
    rcu_replay_wf reversed_nested_events /\
    rcu_rscs reversed_nested_events (reverse_id 1) (reverse_id 4) /\
    rcu_rscs reversed_nested_events (reverse_id 2) (reverse_id 3) /\
    token_id <$> collect_rcu_tokens
      ((fun e => (RcuBuilder.le_id e, RcuBuilder.le_event e)) <$>
        LkmmCandidateEncoding.canonical_events reversed_nested_events) = [1;2;3;4].
  Proof.
    assert (event_structure_wf nested_events) as HE.
    { intros x y t n lx ly Hx Hy. apply nested_lookup in Hx, Hy. naive_solver. }
    split; [| split; [| split]].
    - eapply rcu_replay_wf_rename; [apply reverse_nested_renaming | done |].
      apply nested_events_replay_wf.
    - eapply rcu_rscs_rename_forward; [apply reverse_nested_renaming | done |].
      exists 0. vm_compute. auto.
    - eapply rcu_rscs_rename_forward; [apply reverse_nested_renaming | done |].
      exists 0. vm_compute. auto.
    - vm_compute. reflexivity.
  Qed.

  Module CoreGuards.
    Import LkmmCoreToMachine.

    Definition program := CoreProgram ∅
      {[0 := SSeq SRcuReadLock SRcuReadUnlock; 1 := SSynchronizeRcu]}.
    Definition actions := [CoreSilent 0; CoreEmit 0; CoreEmit 1; CoreSilent 0; CoreEmit 0].
    Definition lock_thread := ThreadState SRcuReadLock [KSeq SRcuReadUnlock] ∅.
    Definition after_lock := add_single_event
      (update_thread (core_initial_state program) 0 lock_thread) 0 lock_thread
      (LBarrier BarrierRcuLock) ∅ ∅ ∅ ∅.

    Local Lemma agent_enumeration agents :
      agents = [0;1] \/ agents = [1;0] -> program_agent_enumeration program agents.
    Proof.
      intros [-> | ->]; split; try (repeat constructor; set_solver);
        intros agent; unfold program; simpl;
        rewrite !lookup_insert_is_Some, lookup_singleton_is_Some; simpl; set_solver.
    Qed.

    Local Lemma lock_prefix :
      core_run program (core_initial_state program) [CoreSilent 0; CoreEmit 0] after_lock.
    Proof.
      eapply CoreRunCons; first by eapply StepSequence.
      eapply CoreRunCons; [by eapply StepRcuReadLock | constructor].
    Qed.

    (** The source can emit the other agent's GP while the reader is open.
        This prefix fails the empty-snapshot guard used by serial replay. *)
    Example interleaved_gp_snapshot_nonempty :
      ~ core_rcu_step_guards after_lock (CoreEmit 1).
    Proof.
      intros Hguards.
      destruct (Hguards (initial_thread SSynchronizeRcu) eq_refl) as [_ Hsync].
      specialize (Hsync eq_refl). discriminate Hsync.
    Qed.

    Local Lemma source_run : exists final,
      complete_core_run program actions final /\ final.(core_events) = independent_gp_events.
    Proof.
      eexists. split.
      - split.
        + eapply core_run_append with (xs := [CoreSilent 0; CoreEmit 0])
            (ys := [CoreEmit 1; CoreSilent 0; CoreEmit 0]); first exact lock_prefix.
          eapply CoreRunCons; first by eapply StepSynchronizeRcu.
          eapply CoreRunCons; first by eapply StepSkipSequence.
          eapply CoreRunCons; [by eapply StepRcuReadUnlock | constructor].
        + intros agent thread Hlookup. destruct (decide (agent = 0)) as [-> | Hne0].
          * simpl in Hlookup. injection Hlookup as <-. done.
          * destruct (decide (agent = 1)) as [-> | Hne1].
            -- simpl in Hlookup. injection Hlookup as <-. done.
            -- simpl in Hlookup. simplify_map_eq.
      - vm_compute. reflexivity.
    Qed.

    (** The original GP has a nonempty snapshot, as shown above.  Final
        RCU well-formedness alone suffices to construct a completed machine
        execution in either block order, without a source guard certificate. *)
    Example independent_gp_machine_replay : exists source,
      complete_core_run program actions source /\
      forall agents, agents = [0;1] \/ agents = [1;0] ->
        exists machine_actions s f,
          complete_machine_run program machine_actions s /\
          core_state_renaming f source s.(machine_core) /\
          project_actions machine_actions = serial_actions agents actions.
    Proof.
      destruct source_run as (source & Hrun & Hevents).
      exists source. split; first done. intros agents Horder.
      eapply complete_core_run_machine_replay_order;
        [done | by apply agent_enumeration |].
      rewrite Hevents. apply independent_gp_replay_wf.
    Qed.
  End CoreGuards.

End RcuReplayExamples.
