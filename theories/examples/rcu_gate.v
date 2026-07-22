From Stdlib Require Import Arith Lia List ZArith Relations.Relation_Operators.
From iris_lkmm.lkmm Require Import rcu_graph.
From iris_lkmm.lkmm Require Import rcu_obligations.
From iris_lkmm.operational Require Import rcu_machine.
From iris_lkmm.operational Require Import rcu_refinement.
From iris_lkmm.operational Require Import rcu_builder.
From iris_lkmm.operational Require Import rcu_candidate.
From iris_lkmm.operational Require Import rcu_coupled.
From stdpp Require Import base sets tactics.
Import ListNotations.

Module RcuGateExamples.
  Import RcuGraph RcuObligations RcuMachine RcuRefinement.
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
    - unfold s0, s1. apply Step_lock. vm_compute. reflexivity.
    - eapply Run_cons with (s2 := s2).
      + unfold s1, s2. apply Step_begin_gp; vm_compute; reflexivity.
      + eapply Run_cons with (s2 := s3).
        * unfold s2, s3. apply Step_read. vm_compute. reflexivity.
        * eapply Run_cons with (s2 := s4).
          -- unfold s3, s4. eapply Step_unlock; vm_compute; reflexivity.
          -- eapply Run_cons with (s2 := s5).
             ++ unfold s4, s5.
                eapply Step_finish_gp;
                  [vm_compute; reflexivity | vm_compute; reflexivity |].
                unfold all_closed, lock_closed. simpl.
                intros l [<- | []].
                exists (CriticalSection 0 2). split; [by left | done].
             ++ apply Run_nil.
  Qed.

  Example one_reader_certificate_is_sound :
    certificates_sound s5.
  Proof.
    eapply operational_soundness.
    apply one_reader_one_gp.
  Qed.

  Definition permissive_relations : abstract_relations :=
    AbstractRelations (fun _ _ => True) (fun _ _ => False)
      (fun _ _ => True) (fun _ _ => False).

  Lemma permissive_link s x y :
    rcu_link (graph_of_state permissive_relations s) x y.
  Proof.
    exists x, x, x, x. repeat split.
    - by left.
    - apply rt_refl.
    - apply rt_refl.
  Qed.

  Definition reader_cert := GpCertificate 3 [0].
  Definition reader_cs := CriticalSection 0 2.

  Example one_reader_certificate_covers_section :
    certificate_covers s5 reader_cert reader_cs.
  Proof.
    vm_compute.
    split; [by left |].
    split; by left.
  Qed.

  Example one_reader_snapshot_refines_rscs_gp_chain :
    rcu_chain_order (graph_of_state permissive_relations s5) 2 3.
  Proof.
    eapply covered_rscs_gp_chain with
      (cert := reader_cert) (cs := reader_cs).
    - eapply operational_event_integrity.
      apply one_reader_one_gp.
    - apply one_reader_certificate_covers_section.
    - apply permissive_link.
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
    Hypothesis Hcs : rcu_rscsi G u l.
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

  Definition link_raw : raw_graph :=
    RawGraph
      [LabeledEvent 0 LSyncRcu;
       LabeledEvent 1 LRead;
       LabeledEvent 2 LRead]
      [(1, 2)] [] [(0, 1)] [] [].

  Definition link_witness : link_commitment :=
    LinkCommitment 0 0 0 0 1 2.

  (** The commitment records the five pieces of the upstream link in order:
      optional po, hb closure, pb closure, prop, and final po. *)
  Example incremental_link_witness_is_valid :
    link_valid (graph_of_raw link_raw) link_witness.
  Proof.
    repeat split.
    - by left.
    - apply rt_refl.
    - apply rt_refl.
    - by left.
    - by left.
  Qed.

  Example incremental_link_witness_denotes_rcu_link :
    rcu_link (graph_of_raw link_raw) 0 2.
  Proof.
    apply (link_valid_sound _ link_witness).
    apply incremental_link_witness_is_valid.
  Qed.

  Definition empty_candidate : finite_candidate :=
    FiniteCandidate [] [] [] [] [] [].

  Example empty_candidate_well_formed :
    candidate_well_formed empty_candidate.
  Proof.
    unfold candidate_well_formed, empty_candidate. simpl.
    split; first constructor.
    split; first by intros x y Hin; inversion Hin.
    split; first by intros x y Hin; inversion Hin.
    split; first by intros x y Hin; inversion Hin.
    split; first by intros x y Hin; inversion Hin.
    intros cs Hin. inversion Hin.
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
      [LabeledEvent 3 LSyncRcu;
       LabeledEvent 2 LRcuUnlock;
       LabeledEvent 1 LRead;
       LabeledEvent 0 LRcuLock]
      [] [] [] [] [CriticalSection 0 2].

  Example one_reader_candidate_well_formed :
    candidate_well_formed one_reader_candidate.
  Proof.
    unfold candidate_well_formed, one_reader_candidate. simpl.
    split.
    - apply NoDup_cons_2; first set_solver.
      apply NoDup_cons_2; first set_solver.
      apply NoDup_cons_2; first set_solver.
      apply NoDup_cons_2; first set_solver.
      apply NoDup_nil_2.
    - split; first by intros x y Hin; inversion Hin.
      split; first by intros x y Hin; inversion Hin.
      split; first by intros x y Hin; inversion Hin.
      split; first by intros x y Hin; inversion Hin.
      intros cs Hin. destruct Hin as [Heq | []]. subst cs.
      simpl. repeat split; auto.
  Qed.

  Example one_reader_candidate_consistent :
    rcu_consistent (candidate_graph one_reader_candidate).
  Proof.
    intros e (a & b & c & d & Hprop & _).
    inversion Hprop.
  Qed.

  Example one_reader_candidate_matches_machine :
    machine_matches_raw s5 (candidate_raw one_reader_candidate).
  Proof. vm_compute. split; reflexivity. Qed.

  Example one_reader_program_candidate :
    consistent_program_candidate one_reader_program agents
      one_reader_candidate.
  Proof.
    split; first apply one_reader_candidate_well_formed.
    split; first apply one_reader_candidate_consistent.
    exists [ALock 0; ABeginGp 1; ARead 0; AUnlock 0; AFinishGp 1], s5.
    split; [apply one_reader_one_gp | apply one_reader_candidate_matches_machine].
  Qed.

  Example one_reader_candidate_has_completed_coupled_run :
    exists actions s,
      coupled_run one_reader_program agents initial_coupled actions s /\
      coupled_complete s /\
      bs_raw s.(coupled_builder) = candidate_raw one_reader_candidate.
  Proof.
    apply consistent_program_candidate_is_schedulable.
    apply one_reader_program_candidate.
  Qed.

End RcuGateExamples.
