From Stdlib Require Import Arith Lia List ZArith Relations.Relation_Operators.
From iris_lkmm.lkmm Require Import execution memory_relations rcu_graph.
From iris_lkmm.lkmm Require Import rcu_obligations.
From iris_lkmm.lang Require Import lkmm_lang.
From iris_lkmm.operational Require Import rcu_machine.
From iris_lkmm.operational Require Import rcu_refinement.
From iris_lkmm.operational Require Import rcu_builder.
From iris_lkmm.operational Require Import rcu_candidate.
From iris_lkmm.operational Require Import rcu_coupled.
From stdpp Require Import sets tactics.
Import ListNotations.

Module RcuGateExamples.
  Import LkmmExecution RcuGraph RcuObligations LkmmLang RcuMachine RcuRefinement.
  Import RcuBuilder RcuCandidate.
  Import RcuCoupled.

  Definition agents : list agent := [0; 1].

  Definition one_reader_program : program :=
    fun a => if Nat.eq_dec a 0
             then [IRcuLock; IRead; IRcuUnlock]
             else [ISynchronizeRcu].

  Definition s0 := initial_state.
  Definition s1 := lock_emit s0 0.
  Definition s2 := begin_gp agents s1 1.
  Definition s3 := ordinary_emit s2 0 LRead.
  Definition s4 := unlock_emit s3 0 0 [].
  Definition s5 := finish_gp s4 1 [0].

  Example one_reader_one_gp :
    run one_reader_program agents s0
      [ALock 0; ABeginGp 1; ARead 0; AUnlock 0; AFinishGp 1] s5.
  Proof.
    eapply Run_cons with (s2 := s1).
    { unfold s0, s1. apply Step_lock. vm_compute. reflexivity. }
    eapply Run_cons with (s2 := s2).
    { unfold s1, s2. apply Step_begin_gp; vm_compute; reflexivity. }
    eapply Run_cons with (s2 := s3).
    { unfold s2, s3. apply Step_read. vm_compute. reflexivity. }
    eapply Run_cons with (s2 := s4).
    { unfold s3, s4. eapply Step_unlock; vm_compute; reflexivity. }
    eapply Run_cons with (s2 := s5).
      - unfold s4, s5.
        eapply Step_finish_gp; [vm_compute; reflexivity | vm_compute; reflexivity |].
        unfold all_closed, lock_closed. simpl.
        intros l [<- | []].
        exists (CriticalSection 0 2). split; [by left | done].
      - apply Run_nil.
  Qed.

  Example one_reader_certificate_is_sound :
    certificates_sound s5.
  Proof.
    eapply operational_soundness.
    apply one_reader_one_gp.
  Qed.

  Definition permissive_relations : abstract_relations :=
    AbstractRelations ∅ ∅ ∅
      (fun source target => source = 3 /\ target = 0) (fun _ _ => False).

  Definition reader_cert := GpCertificate 3 [0].
  Definition reader_cs := CriticalSection 0 2.

  Example one_reader_certificate_covers_section :
    certificate_covers s5 reader_cert reader_cs.
  Proof. vm_compute. split_and!; by left.
  Qed.

  Lemma one_reader_gp_link :
    rcu_link (graph_of_state permissive_relations s5) 3 2.
  Proof.
    exists 3, 0, 0, 0. split_and!.
    - by left.
    - apply rt_step. split; reflexivity.
    - apply rt_refl.
    - change (LkmmMemoryRelations.prop s5.(generated) ∅ ∅ ∅ 0 0).
      assert (LkmmMemoryRelations.marked s5.(generated) 0) as Hmarked0.
      { unfold LkmmMemoryRelations.marked, LkmmMemoryRelations.plain. split.
        - apply in_event_structure_lookup_iff. eexists. vm_compute. reflexivity.
        - intros [Hmode _]. vm_compute in Hmode. discriminate. }
      apply rel_seq_id_on_r. split; last done.
      exists 0. split.
      + apply rel_seq_id_on_r. split; last done.
        exists 0. split; last apply rt_refl.
        apply rel_seq_id_on_l. split; first done. by left.
      + by left.
    - unfold graph_po, po, graph_of_state. cbn.
      exists 0, 0, 2, (canonical_label LRcuLock), (canonical_label LRcuUnlock).
      split_and!; try reflexivity; lia.
  Qed.

  Example one_reader_snapshot_refines_gp_rscs_chain :
    rcu_chain_order (graph_of_state permissive_relations s5) 3 0.
  Proof.
    eapply covered_gp_rscs_chain with (cert := reader_cert) (cs := reader_cs).
    - eapply operational_event_integrity. apply one_reader_one_gp.
    - apply one_reader_certificate_covers_section.
    - apply one_reader_gp_link.
  Qed.

  Definition nested0 := lock_emit initial_state 0.
  Definition nested1 := lock_emit nested0 0.

  (** The inner lock is first in the captured stack, but both nesting levels
      become independent grace-period obligations. *)
  Example nested_readers_are_all_captured :
    snapshot [0] nested1 = [1; 0].
  Proof. vm_compute. reflexivity. Qed.

  Definition after_begin := begin_gp [0; 1] nested0 1.
  Definition after_new_reader := lock_emit after_begin 0.

  (** Starting another (nested) reader after a GP begins does not mutate the
      GP's already-captured obligation set. *)
  Example later_reader_does_not_extend_snapshot :
    after_new_reader.(pending_gp) 1 = Some [0].
  Proof. vm_compute. reflexivity. Qed.

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
    Example rscs_first_has_negative_prefix :
      chain_balance [AtomRscs u l] = (-1)%Z /\
      chain_balance [AtomRscs u l; AtomGp g2] = (0)%Z.
    Proof. vm_compute. lia. Qed.

    Example rscs_first_is_an_obligation_chain :
      rcu_chain_order G u g2.
    Proof.
      exists [AtomRscs u l; AtomGp g2]. split.
      - eapply Linked_cons with (x := g2); try done.
        by apply Linked_one.
      - change (0 <= (0 : Z))%Z. lia.
    Qed.

    Example independent_chain_implies_cat_order :
      rcu_order G u g2.
    Proof.
      apply (proj2 (rcu_order_chain_equiv G u g2)).
      apply rscs_first_is_an_obligation_chain.
    Qed.
  End RecursiveKernel.

  Definition link_events : event_structure :=
    {[0 := EAgent 0 0 (canonical_label LRead);
      1 := EAgent 0 1 (canonical_label LSyncRcu);
      2 := EAgent 0 2 (canonical_label LRead)]}.

  Definition link_raw : raw_graph := RawGraph link_events [] [] [] [] [].

  Definition rcu_link_witness : rcu_link_commitment := RcuLinkCommitment 0 0 0 0 1 2.

  (** The commitment records the five pieces of the upstream link in order:
      optional po, hb closure, pb closure, prop, and final po. *)
  Example incremental_link_witness_is_valid :
    rcu_link_commitment_valid (graph_of_raw link_raw) rcu_link_witness.
  Proof.
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
      { exists 0, 0, 1, (canonical_label LRead), (canonical_label LSyncRcu).
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
      exists 0, 1, 2, (canonical_label LSyncRcu), (canonical_label LRead).
      split_and!; try reflexivity; lia.
  Qed.

  Example incremental_link_witness_denotes_rcu_link :
    rcu_link (graph_of_raw link_raw) 0 2.
  Proof.
    apply (rcu_link_commitment_sound _ rcu_link_witness).
    apply incremental_link_witness_is_valid.
  Qed.

  Definition empty_candidate : finite_candidate := FiniteCandidate [] [] [] [] [] [].

  Example empty_candidate_well_formed :
    candidate_well_formed empty_candidate.
  Proof.
    unfold candidate_well_formed, empty_candidate. cbn. split_and!.
    - constructor.
    - done.
    - apply empty_event_structure_wf.
    - vm_compute. split_and!; reflexivity.
    - intros x y Hin. inversion Hin.
    - intros x y Hin. inversion Hin.
    - intros x y Hin. inversion Hin.
    - intros x y Hin. inversion Hin.
    - intros x y Hin. inversion Hin.
  Qed.

  Example empty_candidate_consistent :
    rcu_consistent (candidate_graph empty_candidate).
  Proof.
    intros e. apply empty_raw_has_no_rb.
  Qed.

  Example empty_candidate_has_incremental_schedule :
    exists s,
      builder_run initial_builder s /\
      bs_raw s = candidate_raw empty_candidate /\
      graph_of_raw (bs_raw s) = candidate_graph empty_candidate.
  Proof.
    apply consistent_candidate_is_incrementally_schedulable.
    - apply empty_candidate_well_formed.
    - apply empty_candidate_consistent.
  Qed.

  Definition one_reader_candidate : finite_candidate :=
    FiniteCandidate
      [LabeledEvent 3 (EAgent 1 0 (canonical_label LSyncRcu));
       LabeledEvent 2 (EAgent 0 2 (canonical_label LRcuUnlock));
       LabeledEvent 1 (EAgent 0 1 (canonical_label LRead));
       LabeledEvent 0 (EAgent 0 0 (canonical_label LRcuLock))]
      [] [] [] [] [].

  Example one_reader_candidate_well_formed :
    candidate_well_formed one_reader_candidate.
  Proof.
    unfold candidate_well_formed. split_and!.
    - vm_compute. repeat constructor; set_solver.
    - vm_compute. split_and!; try reflexivity; try apply Forall_nil.
      all: apply Forall_cons; [lia | apply Forall_nil].
    - pose proof (operational_event_integrity _ _ _ _ one_reader_one_gp)
        as (_ & _ & Hwf & _).
      replace (raw_events (load_events (fc_events one_reader_candidate)))
        with s5.(generated) by (vm_compute; reflexivity). done.
    - vm_compute. split_and!; reflexivity.
    - intros x y Hin. inversion Hin.
    - intros x y Hin. inversion Hin.
    - intros x y Hin. inversion Hin.
    - intros x y Hin. inversion Hin.
    - intros x y Hin. inversion Hin.
  Qed.

  Example one_reader_candidate_matches_machine :
    machine_matches_raw s5 (candidate_raw one_reader_candidate).
  Proof. vm_compute. split; reflexivity. Qed.

End RcuGateExamples.
