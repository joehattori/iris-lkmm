From Stdlib Require Import Arith Lia List.
From stdpp Require Import gmap tactics.
From iris_lkmm.lkmm Require Import rcu_replay.
Import ListNotations.

Module RcuReplayExamples.
  Import RcuReplay.

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

  Example nested_events_replay_wf : rcu_replay_wf nested_events.
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

  Example independent_gp_replay_wf : rcu_replay_wf independent_gp_events.
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

  Definition internal_gp_events : event_structure := {[
    0 := EAgent 0 0 (LBarrier BarrierRcuLock);
    1 := EAgent 0 1 (LBarrier BarrierSyncRcu);
    2 := EAgent 0 2 (LBarrier BarrierRcuUnlock)
  ]}.

  Example matched_section_with_internal_gp_rejected :
    rcu_matching_complete internal_gp_events /\ ~ rcu_replay_wf internal_gp_events.
  Proof.
    split; first by vm_compute.
    intros [_ Hno_gp]. apply (Hno_gp 0 2 1).
    - exists 0. vm_compute. auto.
    - reflexivity.
    - exists 0, 0, 1, (LBarrier BarrierRcuLock), (LBarrier BarrierSyncRcu).
      split_and!; try reflexivity; lia.
    - exists 0, 1, 2, (LBarrier BarrierSyncRcu), (LBarrier BarrierRcuUnlock).
      split_and!; try reflexivity; lia.
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

  Example outer_section_with_internal_gp_rejected :
    rcu_matching_complete outer_section_gp_events /\ ~ rcu_replay_wf outer_section_gp_events.
  Proof.
    split; first by vm_compute.
    intros [_ Hno_gp]. apply (Hno_gp 0 4 3).
    - exists 0. vm_compute. auto.
    - reflexivity.
    - exists 0, 0, 3, (LBarrier BarrierRcuLock), (LBarrier BarrierSyncRcu).
      split_and!; try reflexivity; lia.
    - exists 0, 3, 4, (LBarrier BarrierSyncRcu), (LBarrier BarrierRcuUnlock).
      split_and!; try reflexivity; lia.
  Qed.
End RcuReplayExamples.
