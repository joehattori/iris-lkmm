From Stdlib Require Import Arith Lia List ZArith.
From stdpp Require Import base tactics.
From iris_lkmm.lkmm Require Import rcu_graph rcu_obligations.
From iris_lkmm.operational Require Import rcu_machine.
Import ListNotations.

(** Refinement from the event-generating RCU machine to the independent
    chain/obligation semantics.  The abstract memory relations remain
    parameters: this file connects snapshots, events, and matched sections,
    but deliberately does not manufacture [rcu_link] witnesses. *)
Module RcuRefinement.
  Import RcuGraph RcuObligations RcuMachine.

  Definition generated_has (evs : list generated_event)
      (e : event_id) (lab : label) : Prop :=
    exists a, In (GeneratedEvent e a lab) evs.

  Definition stacks_generated (s : state) : Prop :=
    forall a l, In l (s.(open_stack) a) ->
      generated_has s.(generated) l LRcuLock.

  Definition sections_generated (s : state) : Prop :=
    forall cs, In cs s.(closed_sections) ->
      generated_has s.(generated) cs.(cs_lock) LRcuLock /\
      generated_has s.(generated) cs.(cs_unlock) LRcuUnlock.

  Definition certificates_generated (s : state) : Prop :=
    forall cert, In cert s.(gp_certificates) ->
      generated_has s.(generated) cert.(gc_event) LSyncRcu.

  Definition event_integrity (s : state) : Prop :=
    stacks_generated s /\ sections_generated s /\ certificates_generated s.

  Lemma generated_has_cons ev evs e lab :
    generated_has evs e lab ->
    generated_has (ev :: evs) e lab.
  Proof.
    intros (a & Hin). exists a. by right.
  Qed.

  Lemma event_integrity_step P agents s act s' :
    event_integrity s ->
    step P agents s act s' ->
    event_integrity s'.
  Proof.
    intros (Hstacks & Hsections & Hcerts) Hstep.
    inversion Hstep; subst; simpl.
    - split.
      + intros a' l Hin. apply generated_has_cons.
        exact (Hstacks a' l Hin).
      + split.
        * intros cs Hin. destruct (Hsections cs Hin) as [Hlock Hunlock].
          split; by apply generated_has_cons.
        * intros cert Hin. apply generated_has_cons.
          exact (Hcerts cert Hin).
    - split.
      + intros a' l Hin. apply generated_has_cons.
        exact (Hstacks a' l Hin).
      + split.
        * intros cs Hin. destruct (Hsections cs Hin) as [Hlock Hunlock].
          split; by apply generated_has_cons.
        * intros cert Hin. apply generated_has_cons.
          exact (Hcerts cert Hin).
    - split.
      + intros a' l Hin.
        unfold lock_emit, update in Hin. simpl in Hin.
        destruct (Nat.eq_dec a a') as [Heq | Hneq].
        * subst a'.
          simpl in Hin.
          destruct Hin as [Heql | Hin].
          -- subst l. unfold lock_emit. simpl. exists a. by left.
          -- apply generated_has_cons. exact (Hstacks a l Hin).
        * simpl in Hin.
          apply generated_has_cons. exact (Hstacks a' l Hin).
      + split.
        * intros cs Hin. destruct (Hsections cs Hin) as [Hlock Hunlock].
          split; by apply generated_has_cons.
        * intros cert Hin. apply generated_has_cons.
          exact (Hcerts cert Hin).
    - split.
      + intros a' l' Hin.
        unfold unlock_emit, update in Hin. simpl in Hin.
        destruct (Nat.eq_dec a a') as [Heq | Hneq].
        * subst a'. simpl in Hin.
          apply generated_has_cons.
          apply Hstacks with a. rewrite H0. by right.
        * simpl in Hin. apply generated_has_cons.
          exact (Hstacks a' l' Hin).
      + split.
        * intros cs Hin.
          unfold unlock_emit in Hin. simpl in Hin.
          destruct Hin as [Hnew | Hin].
          -- subst cs. split.
             ++ apply generated_has_cons.
                apply Hstacks with a. rewrite H0. by left.
             ++ unfold unlock_emit. simpl. exists a. by left.
          -- destruct (Hsections cs Hin) as [Hlock Hunlock].
             split; by apply generated_has_cons.
        * intros cert Hin. apply generated_has_cons.
          exact (Hcerts cert Hin).
    - unfold begin_gp. simpl. split; first exact Hstacks.
      split; [exact Hsections | exact Hcerts].
    - split.
      + intros a' l Hin. apply generated_has_cons.
        exact (Hstacks a' l Hin).
      + split.
        * intros cs Hin. destruct (Hsections cs Hin) as [Hlock Hunlock].
          split; by apply generated_has_cons.
        * intros cert Hin.
          unfold finish_gp in Hin. simpl in Hin.
          destruct Hin as [Hnew | Hin].
          -- subst cert. unfold finish_gp. simpl. exists a. by left.
          -- apply generated_has_cons. exact (Hcerts cert Hin).
  Qed.

  Lemma event_integrity_initial :
    event_integrity initial_state.
  Proof.
    split.
    - intros a l Hin. inversion Hin.
    - split.
      + intros cs Hin. inversion Hin.
      + intros cert Hin. inversion Hin.
  Qed.

  Lemma run_preserves_event_integrity P agents s1 actions s2 :
    event_integrity s1 ->
    run P agents s1 actions s2 ->
    event_integrity s2.
  Proof.
    intros Hwf Hrun. induction Hrun.
    - done.
    - apply IHHrun. by eapply event_integrity_step.
  Qed.

  Theorem operational_event_integrity P agents actions s :
    run P agents initial_state actions s ->
    event_integrity s.
  Proof.
    intros Hrun. eapply run_preserves_event_integrity; last done.
    apply event_integrity_initial.
  Qed.

  Record abstract_relations := AbstractRelations {
    ar_po : relation;
    ar_hb : relation;
    ar_prop : relation;
    ar_pb : relation
  }.

  Definition is_sync_at (e : event_id) (ev : generated_event) : bool :=
    Nat.eqb ev.(ge_id) e &&
    match ev.(ge_label) with LSyncRcu => true | _ => false end.

  Definition generated_label (s : state) (e : event_id) : label :=
    if existsb (is_sync_at e) s.(generated) then LSyncRcu else LRead.

  Definition graph_of_state (rels : abstract_relations) (s : state) : graph :=
    Graph (map ge_id s.(generated)) (generated_label s)
      rels.(ar_po) rels.(ar_hb) rels.(ar_prop) rels.(ar_pb)
      s.(closed_sections).

  Lemma generated_has_sync_label s e :
    generated_has s.(generated) e LSyncRcu ->
    generated_label s e = LSyncRcu.
  Proof.
    intros (a & Hin). unfold generated_label.
    destruct (existsb (is_sync_at e) s.(generated)) eqn:Hexists; first done.
    exfalso. apply Bool.not_true_iff_false in Hexists.
    apply Hexists. apply existsb_exists.
    exists (GeneratedEvent e a LSyncRcu). split; first done.
    unfold is_sync_at. simpl. by rewrite Nat.eqb_refl.
  Qed.

  Lemma generated_has_in_graph rels s e lab :
    generated_has s.(generated) e lab ->
    in_graph (graph_of_state rels s) e.
  Proof.
    intros (a & Hin). simpl. apply in_map_iff.
    exists (GeneratedEvent e a lab). split; [done | done].
  Qed.

  Lemma certificate_gp_atom_valid rels s cert :
    event_integrity s ->
    In cert s.(gp_certificates) ->
    atom_valid (graph_of_state rels s) (AtomGp cert.(gc_event)).
  Proof.
    intros (_ & _ & Hcerts) Hin. simpl. split.
    - apply generated_has_in_graph with LSyncRcu.
      exact (Hcerts cert Hin).
    - apply generated_has_sync_label. exact (Hcerts cert Hin).
  Qed.

  Lemma closed_section_atom_valid rels s cs :
    In cs s.(closed_sections) ->
    atom_valid (graph_of_state rels s)
      (AtomRscs cs.(cs_unlock) cs.(cs_lock)).
  Proof.
    intros Hin. simpl. exists cs. naive_solver.
  Qed.

  Definition certificate_covers (s : state)
      (cert : gp_certificate) (cs : critical_section) : Prop :=
    In cert s.(gp_certificates) /\
    In cs s.(closed_sections) /\
    In cs.(cs_lock) cert.(gc_snapshot).

  Lemma sound_certificate_resolves s cert l :
    certificates_sound s ->
    In cert s.(gp_certificates) ->
    In l cert.(gc_snapshot) ->
    exists cs,
      certificate_covers s cert cs /\ cs.(cs_lock) = l.
  Proof.
    intros Hsound Hcert Hl.
    destruct (Hsound cert Hcert l Hl) as (cs & Hcs & Hlock).
    exists cs. split.
    - unfold certificate_covers. repeat split; try done.
      by rewrite Hlock.
    - done.
  Qed.

  Theorem completed_run_snapshot_resolves P agents actions s cert l :
    run P agents initial_state actions s ->
    In cert s.(gp_certificates) ->
    In l cert.(gc_snapshot) ->
    exists cs,
      certificate_covers s cert cs /\ cs.(cs_lock) = l.
  Proof.
    intros Hrun Hcert Hl.
    eapply sound_certificate_resolves; [|done|done].
    exact (operational_soundness P agents actions s Hrun).
  Qed.

  Lemma covered_rscs_gp_chain rels s cert cs :
    event_integrity s ->
    certificate_covers s cert cs ->
    rcu_link (graph_of_state rels s) cs.(cs_lock) cert.(gc_event) ->
    rcu_chain_order (graph_of_state rels s)
      cs.(cs_unlock) cert.(gc_event).
  Proof.
    intros Hwf (Hcert & Hcs & _) Hlink.
    exists [AtomRscs cs.(cs_unlock) cs.(cs_lock);
      AtomGp cert.(gc_event)]. split.
    - eapply Linked_cons with (x := cert.(gc_event)).
      + by apply closed_section_atom_valid.
      + apply Linked_one. by apply certificate_gp_atom_valid.
      + done.
    - change (0 <= (0 : Z))%Z. lia.
  Qed.

  Lemma covered_gp_rscs_chain rels s cert cs :
    event_integrity s ->
    certificate_covers s cert cs ->
    rcu_link (graph_of_state rels s) cert.(gc_event) cs.(cs_unlock) ->
    rcu_chain_order (graph_of_state rels s)
      cert.(gc_event) cs.(cs_lock).
  Proof.
    intros Hwf (Hcert & Hcs & _) Hlink.
    exists [AtomGp cert.(gc_event);
      AtomRscs cs.(cs_unlock) cs.(cs_lock)]. split.
    - eapply Linked_cons with (x := cs.(cs_unlock)).
      + by apply certificate_gp_atom_valid.
      + apply Linked_one. by apply closed_section_atom_valid.
      + done.
    - change (0 <= (0 : Z))%Z. lia.
  Qed.

  Theorem completed_run_snapshot_chain_bridge
      P agents actions s rels cert l :
    run P agents initial_state actions s ->
    In cert s.(gp_certificates) ->
    In l cert.(gc_snapshot) ->
    exists cs,
      certificate_covers s cert cs /\
      cs.(cs_lock) = l /\
      atom_valid (graph_of_state rels s) (AtomGp cert.(gc_event)) /\
      atom_valid (graph_of_state rels s)
        (AtomRscs cs.(cs_unlock) cs.(cs_lock)) /\
      (rcu_link (graph_of_state rels s) cs.(cs_lock) cert.(gc_event) ->
        rcu_chain_order (graph_of_state rels s)
          cs.(cs_unlock) cert.(gc_event)) /\
      (rcu_link (graph_of_state rels s) cert.(gc_event) cs.(cs_unlock) ->
        rcu_chain_order (graph_of_state rels s)
          cert.(gc_event) cs.(cs_lock)).
  Proof.
    intros Hrun Hcert Hl.
    pose proof (operational_event_integrity P agents actions s Hrun) as Hwf.
    destruct (completed_run_snapshot_resolves P agents actions s cert l
        Hrun Hcert Hl) as (cs & Hcovers & Hlock).
    exists cs. split; first exact Hcovers.
    split; first exact Hlock.
    split.
    - by apply certificate_gp_atom_valid.
    - split.
      + apply closed_section_atom_valid.
        by destruct Hcovers as (_ & ? & _).
      + split.
        * by apply covered_rscs_gp_chain.
        * by apply covered_gp_rscs_chain.
  Qed.

End RcuRefinement.
