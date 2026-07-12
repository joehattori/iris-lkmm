From Stdlib Require Import Arith Lia List.
From iris_lkmm.lkmm Require Import rcu_graph.
From iris_lkmm.operational Require Import rcu_machine.
From stdpp Require Import base tactics.
Import ListNotations.

Module RcuGateExamples.
  Import RcuGraph RcuMachine.

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
    exact one_reader_one_gp.
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
      - eapply RS_gp_rscs with (u := u); eauto.
      - exact Hlink2.
      - by apply RS_gp.
    Qed.
  End RecursiveKernel.

End RcuGateExamples.
