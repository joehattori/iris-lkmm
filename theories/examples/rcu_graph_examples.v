From Stdlib Require Import Arith Lia List ZArith Relations.Relation_Operators.
From iris_lkmm.lkmm Require Import execution memory_relations rcu_graph.
From iris_lkmm.lkmm Require Import rcu_obligations.
From iris_lkmm.operational Require Import rcu_builder.
From iris_lkmm.operational Require Import rcu_candidate.
From stdpp Require Import fin_maps gmap sets tactics.
Import ListNotations.

Module RcuGraphExamples.
  Import LkmmExecution LkmmMemoryRelations RcuGraph RcuObligations.
  Import RcuBuilder RcuCandidate.

  Section RecursiveKernel.
    Context (G : graph) (g1 g2 u l : event_id).
    Hypothesis Hgp1 : is_gp G g1.
    Hypothesis Hgp2 : is_gp G g2.
    Hypothesis Hlink1 : rcu_link G g1 u.
    Hypothesis Hcs : graph_rcu_rscsi G u l.
    Hypothesis Hlink2 : rcu_link G l g2.

    Example two_grace_period_chain :
      exists ng nc, rcu_segment G g1 g2 ng nc /\ nc <= ng.
    Proof.
      exists 2, 1. split; last lia.
      eapply RS_join with (y := l) (z := g2)
        (ng1 := 1) (nc1 := 1) (ng2 := 1) (nc2 := 0).
      - eapply RS_gp_rscs with (u := u); done.
      - done.
      - by apply RS_gp.
    Qed.

    (** Prefix nonnegativity would incorrectly reject this upstream CAT case:
        the inverse critical section contributes [-1] before the GP restores
        the final balance to zero. *)
    Example rscs_first_implies_cat_order :
      chain_balance [AtomRscs u l] = (-1)%Z /\
      rcu_order G u g2.
    Proof.
      split; first reflexivity.
      apply (proj2 (rcu_order_chain_equiv G u g2)).
      exists [AtomRscs u l; AtomGp g2]. split.
      - eapply Linked_cons with (x := g2); try done.
        by apply Linked_one.
      - change (0 <= (0 : Z))%Z. lia.
    Qed.
  End RecursiveKernel.

  Definition link_events : event_structure :=
    {[0 := EAgent 0 0 (LMemory AccessRead AccessOnce NotRmw 0 0%Z);
      1 := EAgent 0 1 (LBarrier BarrierSyncRcu);
      2 := EAgent 0 2 (LMemory AccessRead AccessOnce NotRmw 0 0%Z)]}.

  Definition link_raw : raw_graph := RawGraph link_events [] [] [] [] [] [].

  Definition rcu_link_witness : rcu_link_commitment := RcuLinkCommitment 0 0 0 0 1 2.

  (** The commitment records the five pieces of the upstream link in order:
      optional po, hb closure, pb closure, prop, and final po. *)
  Example incremental_link_witness_denotes_rcu_link :
    rcu_link (graph_of_raw link_raw) 0 2.
  Proof.
    apply (rcu_link_commitment_sound _ rcu_link_witness).
    split_and!.
    - by left.
    - apply rt_refl.
    - apply rt_refl.
    - change (LkmmMemoryRelations.prop link_events ∅ ∅ ∅ 0 1).
      assert (LkmmMemoryRelations.marked link_events 0) as Hmarked0.
      { unfold LkmmMemoryRelations.marked, LkmmMemoryRelations.plain. split.
        - apply in_event_structure_lookup_iff. eexists. reflexivity.
        - intros [Hmode _]. discriminate. }
      assert (LkmmMemoryRelations.marked link_events 1) as Hmarked1.
      { unfold LkmmMemoryRelations.marked, LkmmMemoryRelations.plain. split.
        - apply in_event_structure_lookup_iff. eexists. reflexivity.
        - intros [Hmode _]. discriminate. }
      assert (po link_events 0 1) as Hpo.
      { exists 0, 0, 1, (LMemory AccessRead AccessOnce NotRmw 0 0%Z), (LBarrier BarrierSyncRcu).
        split_and!; try reflexivity; lia. }
      assert (LkmmMemoryRelations.gp link_events 0 1) as Hgp.
      { unfold LkmmMemoryRelations.gp. exists 1. split.
        - exists 1. split; first done. split; [done | reflexivity].
        - by left. }
      assert (LkmmMemoryRelations.cumul_fence link_events ∅ ∅ 0 1) as Hcumul.
      { unfold LkmmMemoryRelations.cumul_fence. exists 1. split.
        - apply rel_seq_id_on_r. split; last done.
          apply rel_seq_id_on_l. split; first done. left.
          unfold LkmmMemoryRelations.a_cumul. exists 0. split; first by left.
          left. by right.
        - apply rt_refl. }
      apply rel_seq_id_on_r. split; last done.
      exists 1. split.
      + apply rel_seq_id_on_r. split; last done.
        exists 0. split; last by apply rt_step.
        apply rel_seq_id_on_l. split; first done. by left.
      + by left.
    - unfold graph_po, po, graph_of_raw, link_raw. simpl.
      exists 0, 1, 2, (LBarrier BarrierSyncRcu), (LMemory AccessRead AccessOnce NotRmw 0 0%Z).
      split_and!; try reflexivity; lia.
  Qed.

  Definition empty_candidate : finite_candidate := FiniteCandidate [] [] [] [] [] [] [].

  Example empty_candidate_has_incremental_schedule :
    exists s,
      builder_run initial_builder s /\
      bs_raw s = candidate_raw empty_candidate /\
      graph_of_raw (bs_raw s) = candidate_graph empty_candidate.
  Proof.
    apply consistent_candidate_is_incrementally_schedulable;
      last apply empty_raw_graph_consistent.
    unfold candidate_well_formed, empty_candidate. cbn. split_and!.
    - constructor.
    - done.
    - apply empty_event_structure_wf.
    - vm_compute. split_and!; reflexivity.
    - apply rf_empty_prefix_wf.
    - apply co_empty_prefix_wf.
    - apply rmw_empty_prefix_wf.
    - intros x y Hin. inversion Hin.
    - intros x y Hin. inversion Hin.
    - intros x y Hin. inversion Hin.
  Qed.

  Definition one_reader_candidate : finite_candidate :=
    FiniteCandidate
      [LabeledEvent 3 (EAgent 1 0 (LBarrier BarrierSyncRcu));
       LabeledEvent 2 (EAgent 0 2 (LBarrier BarrierRcuUnlock));
       LabeledEvent 1 (EAgent 0 1 (LMemory AccessRead AccessOnce NotRmw 0 0%Z));
       LabeledEvent 0 (EAgent 0 0 (LBarrier BarrierRcuLock))]
      [] [] [] [] [] [].

  Example one_reader_candidate_well_formed :
    candidate_well_formed one_reader_candidate.
  Proof.
    unfold candidate_well_formed. split_and!.
    - vm_compute. repeat constructor; set_solver.
    - vm_compute. split_and!; try reflexivity; try apply Forall_nil.
      all: apply Forall_cons; [lia | apply Forall_nil].
    - change (event_structure_wf
        {[3 := EAgent 1 0 (LBarrier BarrierSyncRcu);
          2 := EAgent 0 2 (LBarrier BarrierRcuUnlock);
          1 := EAgent 0 1 (LMemory AccessRead AccessOnce NotRmw 0 0%Z);
          0 := EAgent 0 0 (LBarrier BarrierRcuLock)]}).
      intros eid1 eid2 agent index label1 label2 Hlookup1 Hlookup2.
      unfold lookup_event in Hlookup1, Hlookup2.
      repeat (apply lookup_insert_Some in Hlookup1 as [[? ?] | [? Hlookup1]]);
        repeat (apply lookup_insert_Some in Hlookup2 as [[? ?] | [? Hlookup2]]);
        try (apply lookup_singleton_Some in Hlookup1);
        try (apply lookup_singleton_Some in Hlookup2); naive_solver.
    - vm_compute. split_and!; reflexivity.
    - apply rf_empty_prefix_wf.
    - apply co_empty_prefix_wf.
    - apply rmw_empty_prefix_wf.
    - intros x y Hin. inversion Hin.
    - intros x y Hin. inversion Hin.
    - intros x y Hin. inversion Hin.
  Qed.

End RcuGraphExamples.
