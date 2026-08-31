From Stdlib Require Import Arith Lia List ZArith.
From stdpp Require Import base gmap tactics.
From iris_lkmm.lkmm Require Import rcu_graph rcu_obligations.
From iris_lkmm.operational Require Import rcu_machine.
Import ListNotations.

(** Refinement from the event-generating RCU machine to the independent
    chain/obligation semantics.  The abstract memory relations remain
    parameters: this file connects snapshots, events, and matched sections,
    but deliberately does not manufacture [rcu_link] witnesses. *)
Module RcuRefinement.
  Import RcuGraph RcuObligations RcuMachine.

  Definition generated_has (E : event_structure) (e : event_id) (lab : label) : Prop :=
    exists agent index,
      lookup_event E e = Some (EAgent agent index (canonical_label lab)).

  Definition generated_below (s : state) : Prop :=
    forall eid ev, lookup_event s.(generated) eid = Some ev -> (eid < s.(next_id))%nat.

  Definition generated_before_pc (s : state) : Prop :=
    forall eid agent index label,
      lookup_event s.(generated) eid = Some (EAgent agent index label) ->
      (index < s.(pc) agent)%nat.

  Definition stacks_generated (s : state) : Prop :=
    forall a l, In l (s.(open_rscs_stack) a) ->
      generated_has s.(generated) l LRcuLock.

  Definition sections_generated (s : state) : Prop :=
    forall cs, In cs s.(closed_sections) ->
      generated_has s.(generated) cs.(cs_lock) LRcuLock /\
      generated_has s.(generated) cs.(cs_unlock) LRcuUnlock.

  Definition certificates_generated (s : state) : Prop :=
    forall cert, In cert s.(gp_certificates) ->
      generated_has s.(generated) cert.(gc_event) LSyncRcu.

  Definition stacks_match (s : state) : Prop :=
    forall agent, computed_agent_stack s.(generated) agent = s.(open_rscs_stack) agent.

  Definition sections_match (s : state) : Prop :=
    forall cs,
      In cs s.(closed_sections) <->
      rcu_rscs s.(generated) cs.(cs_lock) cs.(cs_unlock).

  Definition event_integrity (s : state) : Prop :=
    generated_below s /\
    generated_before_pc s /\
    event_structure_wf s.(generated) /\
    stacks_generated s /\
    sections_generated s /\
    certificates_generated s /\
    stacks_match s /\
    sections_match s.

  Lemma generated_fresh s :
    generated_below s -> lookup_event s.(generated) s.(next_id) = None.
  Proof.
    intros Hbelow. destruct (lookup_event s.(generated) s.(next_id)) as [ev |]
      eqn:Hlookup; last done. exfalso. pose proof (Hbelow _ _ Hlookup). lia.
  Qed.

  Lemma generated_has_emit_old s a new_lab old old_lab :
    generated_below s -> generated_has s.(generated) old old_lab ->
    generated_has (<[s.(next_id) := generated_event s a new_lab]> s.(generated)) old old_lab.
  Proof.
    intros Hbelow (agent & index & Hlookup). exists agent, index.
    unfold lookup_event in Hlookup |- *. apply lookup_insert_Some. right. split; last done.
    intros Heq. subst old. pose proof (Hbelow _ _ Hlookup). lia.
  Qed.

  Lemma generated_has_emit_new s a lab :
    generated_has (<[s.(next_id) := generated_event s a lab]> s.(generated))
      s.(next_id) lab.
  Proof.
    exists a, (s.(pc) a). unfold lookup_event, generated_event.
    apply lookup_insert_Some. by left.
  Qed.

  Lemma generated_below_emit s a lab :
    generated_below s ->
    forall eid ev,
      lookup_event (<[s.(next_id) := generated_event s a lab]> s.(generated)) eid =
        Some ev ->
      (eid < S s.(next_id))%nat.
  Proof.
    intros Hbelow eid ev Hlookup. unfold lookup_event in Hlookup.
    apply lookup_insert_Some in Hlookup as [[-> _] | [_ Hlookup]]; first lia.
    eapply Nat.lt_trans; first by eapply Hbelow. lia.
  Qed.

  Lemma generated_before_pc_emit s a lab :
    generated_before_pc s ->
    forall eid agent index label,
      lookup_event (<[s.(next_id) := generated_event s a lab]> s.(generated)) eid =
        Some (EAgent agent index label) ->
      (index < update s.(pc) a (S (s.(pc) a)) agent)%nat.
  Proof.
    intros Hbefore eid agent index label Hlookup. unfold lookup_event in Hlookup.
    apply lookup_insert_Some in Hlookup as [[_ Hevent] | [_ Hlookup]].
    - unfold generated_event in Hevent. injection Hevent as <- <- <-.
      rewrite update_eq. lia.
    - destruct (Nat.eq_dec a agent) as [-> | Hneq].
      + rewrite update_eq. eapply Nat.lt_trans; first by eapply Hbefore. lia.
      + rewrite update_neq; last done. by eapply Hbefore.
  Qed.

  Lemma event_structure_wf_emit s a lab :
    event_structure_wf s.(generated) ->
    generated_before_pc s ->
    event_structure_wf
      (<[s.(next_id) := generated_event s a lab]> s.(generated)).
  Proof.
    intros Hwf Hbefore eid1 eid2 agent index label1 label2 Hlookup1 Hlookup2.
    unfold lookup_event in Hlookup1, Hlookup2.
    apply lookup_insert_Some in Hlookup1 as [[Heid1 Hevent1] | [Hneq1 Hlookup1]];
      apply lookup_insert_Some in Hlookup2 as [[Heid2 Hevent2] | [Hneq2 Hlookup2]].
    - congruence.
    - subst eid1. unfold generated_event in Hevent1. injection Hevent1 as <- <- <-.
      exfalso. pose proof (Hbefore _ _ _ _ Hlookup2). lia.
    - subst eid2. unfold generated_event in Hevent2. injection Hevent2 as <- <- <-.
      exfalso. pose proof (Hbefore _ _ _ _ Hlookup1). lia.
    - by eapply Hwf.
  Qed.

  Lemma emitted_event_agent_tail s a lab :
    generated_below s -> generated_before_pc s ->
    rcu_agent_tail s.(generated) s.(next_id) (generated_event s a lab).
  Proof.
    intros Hbelow Hbefore. split; first by apply generated_fresh.
    destruct lab; simpl; try done;
      rewrite Forall_forall; intros token Hin;
      destruct (rcu_agent_token_trace_lookup _ _ _ Hin) as [Hagent Hlookup];
      unfold event_of_rcu_token in Hlookup;
      destruct (token_kind token); simpl in Hlookup;
      pose proof (Hbefore _ _ _ _ Hlookup) as Hindex;
      unfold rcu_token_le; simpl; naive_solver lia.
  Qed.

  Lemma sections_match_non_rcu_emit s a lab :
    sections_match s ->
    generated_below s ->
    rcu_token_of_entry (s.(next_id), generated_event s a lab) = None ->
    sections_match
      {|
        next_id := S s.(next_id);
        pc := update s.(pc) a (S (s.(pc) a));
        open_rscs_stack := s.(open_rscs_stack);
        pending_gp := s.(pending_gp);
        generated := <[s.(next_id) := generated_event s a lab]> s.(generated);
        closed_sections := s.(closed_sections);
        gp_certificates := s.(gp_certificates)
      |}.
  Proof.
    intros Hsections Hbelow Hnone cs. simpl. rewrite (Hsections cs).
    symmetry. apply rcu_rscs_insert_non_rcu; [by apply generated_fresh | done].
  Qed.

  Lemma event_integrity_step P agents s act s' :
    event_integrity s ->
    step P agents s act s' ->
    event_integrity s'.
  Proof.
    intros (Hbelow & Hbefore & Hwf & Hstacks & Hsections & Hcerts & Hstack_match &
      Hsection_match) Hstep.
    inversion Hstep; subst.
    - unfold event_integrity, ordinary_emit. simpl. split_and!.
      + exact (generated_below_emit s a LRead Hbelow).
      + exact (generated_before_pc_emit s a LRead Hbefore).
      + exact (event_structure_wf_emit s a LRead Hwf Hbefore).
      + intros agent lock Hin. eapply generated_has_emit_old; [done | by eapply Hstacks].
      + intros section Hin. destruct (Hsections section Hin). split;
          eapply generated_has_emit_old; eauto.
      + intros cert Hin. eapply generated_has_emit_old; [done | by eapply Hcerts].
      + intros agent. cbn. rewrite <- Hstack_match.
        apply computed_agent_stack_insert_non_rcu; [by apply generated_fresh | done].
      + intros section. cbn. rewrite (Hsection_match section). symmetry.
        apply rcu_rscs_insert_non_rcu; [by apply generated_fresh | done].
    - unfold event_integrity, ordinary_emit. simpl. split_and!.
      + exact (generated_below_emit s a LWrite Hbelow).
      + exact (generated_before_pc_emit s a LWrite Hbefore).
      + exact (event_structure_wf_emit s a LWrite Hwf Hbefore).
      + intros agent lock Hin. eapply generated_has_emit_old; [done | by eapply Hstacks].
      + intros section Hin. destruct (Hsections section Hin). split;
          eapply generated_has_emit_old; eauto.
      + intros cert Hin. eapply generated_has_emit_old; [done | by eapply Hcerts].
      + intros agent. cbn. rewrite <- Hstack_match.
        apply computed_agent_stack_insert_non_rcu; [by apply generated_fresh | done].
      + intros section. cbn. rewrite (Hsection_match section). symmetry.
        apply rcu_rscs_insert_non_rcu; [by apply generated_fresh | done].
    - pose (token := RcuToken s.(next_id) a (s.(pc) a) RcuTokenLock).
      assert (Htail : rcu_agent_tail s.(generated) s.(next_id)
          (generated_event s a LRcuLock)) by (by apply emitted_event_agent_tail).
      assert (Htoken : rcu_token_of_entry
          (s.(next_id), generated_event s a LRcuLock) = Some token) by done.
      unfold event_integrity, lock_emit. simpl. split_and!.
      + exact (generated_below_emit s a LRcuLock Hbelow).
      + exact (generated_before_pc_emit s a LRcuLock Hbefore).
      + exact (event_structure_wf_emit s a LRcuLock Hwf Hbefore).
      + intros agent lock Hin. cbn in Hin. destruct (Nat.eq_dec a agent) as [-> | Hneq].
        * rewrite update_eq in Hin. destruct Hin as [-> | Hin].
          -- exists agent, (s.(pc) agent). unfold lookup_event, generated_event.
             change ((<[lock := EAgent agent (s.(pc) agent)
               (canonical_label LRcuLock)]> s.(generated)) !! lock =
               Some (EAgent agent (s.(pc) agent) (canonical_label LRcuLock))).
             apply lookup_insert_Some. by left.
          -- eapply generated_has_emit_old; [done | by eapply Hstacks].
        * rewrite update_neq in Hin; last done.
          eapply generated_has_emit_old; [done | by eapply Hstacks].
      + intros section Hin. destruct (Hsections section Hin). split;
          eapply generated_has_emit_old; eauto.
      + intros cert Hin. eapply generated_has_emit_old; [done | by eapply Hcerts].
      + intros agent. cbn. destruct (Nat.eq_dec a agent) as [-> | Hneq].
        * rewrite update_eq, <- Hstack_match.
          by apply (computed_agent_stack_insert_lock _ _ _ token).
        * rewrite update_neq; last done. rewrite <- Hstack_match.
          apply computed_agent_stack_insert_other with (token := token); try done.
          by apply generated_fresh.
      + intros section. cbn. rewrite (Hsection_match section). symmetry.
        by apply (rcu_rscs_agent_tail_lock _ _ _ token).
    - pose (token := RcuToken s.(next_id) a (s.(pc) a) RcuTokenUnlock).
      assert (Htail : rcu_agent_tail s.(generated) s.(next_id)
          (generated_event s a LRcuUnlock)) by (by apply emitted_event_agent_tail).
      assert (Htoken : rcu_token_of_entry
          (s.(next_id), generated_event s a LRcuUnlock) = Some token) by done.
      pose proof (Hstack_match a) as Hstack_a. rewrite H0 in Hstack_a.
      unfold computed_agent_stack in Hstack_a.
      destruct (token_stack (compute_agent_match_state s.(generated) a) a)
        as [|lock_token token_rest] eqn:Htokens; simpl in Hstack_a; first discriminate.
      injection Hstack_a as Hlock Hrest.
      unfold event_integrity, unlock_emit. simpl. split_and!.
      + exact (generated_below_emit s a LRcuUnlock Hbelow).
      + exact (generated_before_pc_emit s a LRcuUnlock Hbefore).
      + exact (event_structure_wf_emit s a LRcuUnlock Hwf Hbefore).
      + intros agent lock Hin. cbn in Hin. destruct (Nat.eq_dec a agent) as [-> | Hneq].
        * rewrite update_eq in Hin. eapply generated_has_emit_old; first done.
          apply Hstacks with agent. rewrite H0. by right.
        * rewrite update_neq in Hin; last done.
          eapply generated_has_emit_old; [done | by eapply Hstacks].
      + intros section [Heq | Hin].
        * subst section. split.
          -- eapply generated_has_emit_old; first done.
             apply Hstacks with a. rewrite H0. change (In l (l :: rest)). by left.
          -- exists a, (s.(pc) a). unfold lookup_event, generated_event.
             change ((<[s.(next_id) := EAgent a (s.(pc) a)
               (canonical_label LRcuUnlock)]> s.(generated)) !! s.(next_id) =
               Some (EAgent a (s.(pc) a) (canonical_label LRcuUnlock))).
             apply lookup_insert_Some. by left.
        * destruct (Hsections section Hin). split; eapply generated_has_emit_old; eauto.
      + intros cert Hin. eapply generated_has_emit_old; [done | by eapply Hcerts].
      + intros agent. cbn. destruct (Nat.eq_dec a agent) as [-> | Hneq].
        * rewrite update_eq, <- Hrest.
          apply computed_agent_stack_insert_unlock with
            (token := token) (lock_token := lock_token); try done.
        * rewrite update_neq; last done.
          rewrite <- (Hstack_match agent).
          apply computed_agent_stack_insert_other with (token := token); try done.
          by apply generated_fresh.
      + intros section. cbn. split.
        * intros [Heq | Hin].
          -- subst section.
             apply (proj2 (rcu_rscs_agent_tail_unlock _ _ _ token lock_token token_rest
                l s.(next_id) Htail Htoken eq_refl Htokens)).
             left. split; [symmetry; exact Hlock | reflexivity].
          -- apply (proj2 (rcu_rscs_agent_tail_unlock _ _ _ token lock_token token_rest
                section.(cs_lock) section.(cs_unlock) Htail Htoken eq_refl Htokens)).
             right. by apply Hsection_match.
        * intros Hmatched.
          apply (proj1 (rcu_rscs_agent_tail_unlock _ _ _ token lock_token token_rest
            section.(cs_lock) section.(cs_unlock) Htail Htoken eq_refl Htokens)) in Hmatched.
          destruct Hmatched as [[Hcslock Hcsunlock] | Hold].
          -- left. destruct section. simpl in *. subst. f_equal; congruence.
          -- right. by apply Hsection_match.
    - unfold event_integrity, begin_gp. simpl. split_and!; done.
    - unfold event_integrity, finish_gp. simpl. split_and!.
      + exact (generated_below_emit s a LSyncRcu Hbelow).
      + exact (generated_before_pc_emit s a LSyncRcu Hbefore).
      + exact (event_structure_wf_emit s a LSyncRcu Hwf Hbefore).
      + intros agent lock Hin. eapply generated_has_emit_old; [done | by eapply Hstacks].
      + intros section Hin. destruct (Hsections section Hin). split;
          eapply generated_has_emit_old; eauto.
      + intros cert [Heq | Hin].
        * subst cert. exists a, (s.(pc) a). unfold lookup_event, generated_event.
          change ((<[s.(next_id) := EAgent a (s.(pc) a)
            (canonical_label LSyncRcu)]> s.(generated)) !! s.(next_id) =
            Some (EAgent a (s.(pc) a) (canonical_label LSyncRcu))).
          apply lookup_insert_Some. by left.
        * eapply generated_has_emit_old; [done | by eapply Hcerts].
      + intros agent. cbn. rewrite <- Hstack_match.
        apply computed_agent_stack_insert_non_rcu; [by apply generated_fresh | done].
      + intros section. cbn. rewrite (Hsection_match section). symmetry.
        apply rcu_rscs_insert_non_rcu; [by apply generated_fresh | done].
  Qed.

  Lemma event_integrity_initial :
    event_integrity initial_state.
  Proof.
    unfold event_integrity. split_and!; cbn.
    - intros eid ev Hlookup. exfalso. unfold lookup_event in Hlookup.
      change ((∅ : event_structure) !! eid = Some ev) in Hlookup.
      change (None = Some ev) in Hlookup. discriminate.
    - intros eid agent index label Hlookup. exfalso. unfold lookup_event in Hlookup.
      change ((∅ : event_structure) !! eid = Some (EAgent agent index label)) in Hlookup.
      change (None = Some (EAgent agent index label)) in Hlookup. discriminate.
    - apply empty_event_structure_wf.
    - intros a l Hin. inversion Hin.
    - intros cs Hin. inversion Hin.
    - intros cert Hin. inversion Hin.
    - intros agent. vm_compute. reflexivity.
    - intros cs. vm_compute. split.
      + intros Hfalse. contradiction.
      + intros (agent & Hfalse). contradiction.
  Qed.

  Lemma run_preserves_event_integrity P agents s1 actions s2 :
    event_integrity s1 ->
    run P agents s1 actions s2 ->
    event_integrity s2.
  Proof.
    intros Hwf Hrun. induction Hrun; first done.
    apply IHHrun. by eapply event_integrity_step.
  Qed.

  Theorem operational_event_integrity P agents actions s :
    run P agents initial_state actions s ->
    event_integrity s.
  Proof.
    intros Hrun. eapply run_preserves_event_integrity; last done.
    apply event_integrity_initial.
  Qed.

  Record abstract_relations := AbstractRelations {
    ar_hb : relation;
    ar_prop : relation;
    ar_pb : relation
  }.

  Definition graph_of_state (rels : abstract_relations) (s : state) : graph :=
    Graph s.(generated) rels.(ar_hb) rels.(ar_prop) rels.(ar_pb).

  Lemma generated_has_in_graph rels s e lab :
    generated_has s.(generated) e lab ->
    in_graph (graph_of_state rels s) e.
  Proof.
    intros (agent & index & Hlookup). unfold in_graph, graph_of_state. simpl.
    apply in_event_structure_lookup_iff. eauto.
  Qed.

  Lemma certificate_gp_atom_valid rels s cert :
    event_integrity s ->
    In cert s.(gp_certificates) ->
    atom_valid (graph_of_state rels s) (AtomGp cert.(gc_event)).
  Proof.
    intros (_ & _ & _ & _ & _ & Hcerts & _ & _) Hin.
    destruct (Hcerts cert Hin) as (agent & index & Hlookup).
    unfold atom_valid, is_gp, graph_of_state. simpl.
    apply event_has_barrier_kind_lookup.
    exists (EAgent agent index (canonical_label LSyncRcu)). split; first done.
    reflexivity.
  Qed.

  Lemma closed_section_atom_valid rels s cs :
    event_integrity s ->
    In cs s.(closed_sections) ->
    atom_valid (graph_of_state rels s)
      (AtomRscs cs.(cs_unlock) cs.(cs_lock)).
  Proof.
    intros (_ & _ & _ & _ & _ & _ & _ & Hsections) Hin.
    unfold atom_valid, graph_rcu_rscsi, graph_of_state, rcu_rscsi. simpl.
    by apply Hsections.
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
    exists cs. split; last done.
    unfold certificate_covers. split_and!; try done.
    by rewrite Hlock.
  Qed.

  Theorem completed_run_snapshot_resolves P agents actions s cert l :
    run P agents initial_state actions s ->
    In cert s.(gp_certificates) ->
    In l cert.(gc_snapshot) ->
    exists cs,
      certificate_covers s cert cs /\ cs.(cs_lock) = l.
  Proof.
    intros Hrun Hcert Hl.
    eapply sound_certificate_resolves; try done.
    by apply (operational_soundness P agents actions s Hrun).
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
    - eapply Linked_cons with (x := cert.(gc_event)); last done.
      + by apply closed_section_atom_valid.
      + apply Linked_one. by apply certificate_gp_atom_valid.
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
    - eapply Linked_cons with (x := cs.(cs_unlock)); last done.
      + by apply certificate_gp_atom_valid.
      + apply Linked_one. by apply closed_section_atom_valid.
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
    exists cs. split; first done.
    split; first done.
    split.
    - by apply certificate_gp_atom_valid.
    - split.
      + apply closed_section_atom_valid.
        * done.
        * by destruct Hcovers as (_ & ? & _).
      + split.
        * by apply covered_rscs_gp_chain.
        * by apply covered_gp_rscs_chain.
  Qed.

End RcuRefinement.
