From Stdlib Require Import Arith Lia List.
From stdpp Require Import base fin_map_dom gmap sets tactics.
From iris_lkmm.lkmm Require Import rcu_graph.
From iris_lkmm.operational Require Import rcu_machine.
Import ListNotations.

(** Safety facts connecting operational reader stacks to the finite-set
    disjointness premise of the Iris grace-period completion rule. *)
Module RcuMachineSafety.
  Import RcuGraph RcuMachine.

  Definition stack_unique (stacks : agent -> list event_id) : Prop :=
    (forall a, List.NoDup (stacks a)) /\
    (forall a b l, In l (stacks a) -> In l (stacks b) -> a = b).

  Definition stacks_below (s : state) : Prop :=
    forall a l, In l (s.(open_rscs_stack) a) -> l < s.(next_id).

  Definition sections_below (s : state) : Prop :=
    forall cs, In cs s.(closed_sections) ->
      cs.(cs_lock) < s.(next_id) /\ cs.(cs_unlock) < s.(next_id).

  Definition sections_disjoint_from_stacks (s : state) : Prop :=
    forall a l cs,
      In l (s.(open_rscs_stack) a) ->
      In cs s.(closed_sections) ->
      cs.(cs_lock) <> l.

  Definition machine_stack_safe (s : state) : Prop :=
    stacks_below s /\
    sections_below s /\
    stack_unique s.(open_rscs_stack) /\
    sections_disjoint_from_stacks s.

  Lemma stack_fresh_below s :
    stacks_below s ->
    forall a, ~ In s.(next_id) (s.(open_rscs_stack) a).
  Proof.
    intros Hbelow a Hin.
    pose proof (Hbelow a s.(next_id) Hin). lia.
  Qed.

  Lemma stack_unique_push stacks a x :
    stack_unique stacks ->
    (forall b, ~ In x (stacks b)) ->
    stack_unique (update stacks a (x :: stacks a)).
  Proof.
    intros (Hnodup & Howner) Hfresh. split.
    - intros b. destruct (Nat.eq_dec a b) as [-> | Hneq].
      + rewrite update_eq. constructor; [apply Hfresh | apply Hnodup].
      + rewrite update_neq; [apply Hnodup | done].
    - intros b c l Hb Hc.
      destruct (Nat.eq_dec a b) as [Hab | Hab];
        destruct (Nat.eq_dec a c) as [Hac | Hac].
      + subst b. subst c. done.
      + subst b.
        rewrite update_eq in Hb. rewrite update_neq in Hc; last done.
        destruct Hb as [-> | Hb].
        * exfalso. by apply (Hfresh c).
        * pose proof (Howner a c l Hb Hc). congruence.
      + subst c.
        rewrite update_neq in Hb; last done. rewrite update_eq in Hc.
        destruct Hc as [-> | Hc].
        * exfalso. by apply (Hfresh b).
        * pose proof (Howner b a l Hb Hc). congruence.
      + rewrite update_neq in Hb; last done.
        rewrite update_neq in Hc; last done.
        by eapply Howner.
  Qed.

  Lemma pop_stack_subset (stacks : agent -> list event_id)
      (a : agent) (l : event_id) (rest : list event_id) :
    stacks a = l :: rest ->
    forall b x,
      In x (update stacks a rest b) -> In x (stacks b).
  Proof.
    intros Hstack b x Hin.
    destruct (Nat.eq_dec a b) as [-> | Hneq].
    - rewrite update_eq in Hin. rewrite Hstack. by right.
    - rewrite update_neq in Hin; done.
  Qed.

  Lemma stack_unique_pop (stacks : agent -> list event_id)
      (a : agent) (l : event_id) (rest : list event_id) :
    stacks a = l :: rest ->
    stack_unique stacks ->
    stack_unique (update stacks a rest).
  Proof.
    intros Hstack (Hnodup & Howner). split.
    - intros b. destruct (Nat.eq_dec a b) as [Heq | Hneq].
      + subst b. rewrite update_eq. pose proof (Hnodup a) as Hnd.
        rewrite Hstack in Hnd. inversion Hnd. done.
      + rewrite update_neq; [apply Hnodup | done].
    - intros b c x Hb Hc. eapply Howner.
      + by eapply pop_stack_subset.
      + by eapply pop_stack_subset.
  Qed.

  Lemma pushed_sections_disjoint
      (stacks : agent -> list event_id)
      (closed : list critical_section) (next : event_id) (a : agent) :
    (forall cs, In cs closed -> cs.(cs_lock) < next) ->
    (forall b l cs, In l (stacks b) -> In cs closed -> cs.(cs_lock) <> l) ->
    forall b l cs,
      In l (update stacks a (next :: stacks a) b) ->
      In cs closed -> cs.(cs_lock) <> l.
  Proof.
    intros Hbelow Hdisjoint b l cs Hin Hcs.
    destruct (Nat.eq_dec a b) as [-> | Hneq].
    - rewrite update_eq in Hin. destruct Hin as [-> | Hin].
      + pose proof (Hbelow cs Hcs). lia.
      + by eapply Hdisjoint.
    - rewrite update_neq in Hin; last done. by eapply Hdisjoint.
  Qed.

  Lemma popped_lock_not_open (stacks : agent -> list event_id)
      (a : agent) (l : event_id) (rest : list event_id) :
    stacks a = l :: rest ->
    stack_unique stacks ->
    forall b x,
      In x (update stacks a rest b) -> l <> x.
  Proof.
    intros Hstack (Hnodup & Howner) b x Hin Heq. subst x.
    pose proof (pop_stack_subset stacks a l rest Hstack b l Hin) as Hold.
    assert (a = b) by (eapply Howner; [rewrite Hstack; by left | done]).
    subst b. rewrite update_eq in Hin.
    pose proof (Hnodup a) as Hnd. rewrite Hstack in Hnd.
    inversion Hnd. contradiction.
  Qed.

  Lemma popped_sections_disjoint
      (stacks : agent -> list event_id)
      (closed : list critical_section) (a : agent)
      (l : event_id) (rest : list event_id) (u : event_id) :
    stacks a = l :: rest ->
    stack_unique stacks ->
    (forall b x cs,
      In x (stacks b) -> In cs closed -> cs.(cs_lock) <> x) ->
    forall b x cs,
      In x (update stacks a rest b) ->
      In cs (CriticalSection l u :: closed) ->
      cs.(cs_lock) <> x.
  Proof.
    intros Hstack Hunique Hdisjoint b x cs Hx [Hnew | Hcs].
    - subst cs. simpl. by eapply popped_lock_not_open.
    - eapply Hdisjoint; [by eapply pop_stack_subset | done].
  Qed.

  Lemma stacks_below_step P agents s act s' :
    stacks_below s ->
    RcuMachine.step P agents s act s' ->
    stacks_below s'.
  Proof.
    intros Hbelow Hstep. inversion Hstep; subst.
    - unfold ordinary_emit. simpl. intros a' l Hin.
      eapply Nat.lt_trans; [by eapply Hbelow | apply Nat.lt_succ_diag_r].
    - unfold ordinary_emit. simpl. intros a' l Hin.
      eapply Nat.lt_trans; [by eapply Hbelow | apply Nat.lt_succ_diag_r].
    - unfold lock_emit. simpl. intros a' l Hin.
      change (In l (update s.(open_rscs_stack) a
        (s.(next_id) :: s.(open_rscs_stack) a) a')) in Hin.
      destruct (Nat.eq_dec a a') as [Heq | Hneq].
      + subst a'. rewrite update_eq in Hin. destruct Hin as [-> | Hin].
        * apply Nat.lt_succ_diag_r.
        * eapply Nat.lt_trans; [by eapply Hbelow | apply Nat.lt_succ_diag_r].
      + rewrite update_neq in Hin; last done.
        eapply Nat.lt_trans; [by eapply Hbelow | apply Nat.lt_succ_diag_r].
    - unfold unlock_emit. simpl. intros a' l' Hin.
      change (In l' (update s.(open_rscs_stack) a rest a')) in Hin.
      destruct (Nat.eq_dec a a') as [Heq | Hneq].
      + subst a'. rewrite update_eq in Hin. eapply Nat.lt_trans.
        * apply Hbelow with a. rewrite H0. by right.
        * apply Nat.lt_succ_diag_r.
      + rewrite update_neq in Hin; last done.
        eapply Nat.lt_trans; [by eapply Hbelow | apply Nat.lt_succ_diag_r].
    - unfold begin_gp. simpl. done.
    - unfold finish_gp. simpl. intros a' l Hin.
      eapply Nat.lt_trans; [by eapply Hbelow | apply Nat.lt_succ_diag_r].
  Qed.

  Lemma sections_below_step P agents s act s' :
    stacks_below s ->
    sections_below s ->
    RcuMachine.step P agents s act s' ->
    sections_below s'.
  Proof.
    intros Hstacks Hsections Hstep. inversion Hstep; subst.
    - unfold ordinary_emit. simpl. intros cs Hcs.
      destruct (Hsections cs Hcs) as [Hl Hu]. split.
      + eapply Nat.lt_trans; [done | apply Nat.lt_succ_diag_r].
      + eapply Nat.lt_trans; [done | apply Nat.lt_succ_diag_r].
    - unfold ordinary_emit. simpl. intros cs Hcs.
      destruct (Hsections cs Hcs) as [Hl Hu]. split.
      + eapply Nat.lt_trans; [done | apply Nat.lt_succ_diag_r].
      + eapply Nat.lt_trans; [done | apply Nat.lt_succ_diag_r].
    - unfold lock_emit. simpl. intros cs Hcs.
      destruct (Hsections cs Hcs) as [Hl Hu]. split.
      + eapply Nat.lt_trans; [done | apply Nat.lt_succ_diag_r].
      + eapply Nat.lt_trans; [done | apply Nat.lt_succ_diag_r].
    - unfold unlock_emit. simpl. intros cs [Hnew | Hcs].
      + subst cs. simpl. split.
        * eapply Nat.lt_trans.
          -- apply Hstacks with a. rewrite H0. by left.
          -- apply Nat.lt_succ_diag_r.
        * apply Nat.lt_succ_diag_r.
      + destruct (Hsections cs Hcs) as [Hl Hu]. split.
        * eapply Nat.lt_trans; [done | apply Nat.lt_succ_diag_r].
        * eapply Nat.lt_trans; [done | apply Nat.lt_succ_diag_r].
    - unfold begin_gp. simpl. done.
    - unfold finish_gp. simpl. intros cs Hcs.
      destruct (Hsections cs Hcs) as [Hl Hu]. split.
      + eapply Nat.lt_trans; [done | apply Nat.lt_succ_diag_r].
      + eapply Nat.lt_trans; [done | apply Nat.lt_succ_diag_r].
  Qed.

  Lemma stack_unique_step P agents s act s' :
    stacks_below s ->
    stack_unique s.(open_rscs_stack) ->
    RcuMachine.step P agents s act s' ->
    stack_unique s'.(open_rscs_stack).
  Proof.
    intros Hbelow Hunique Hstep. inversion Hstep; subst; simpl; try done.
    - apply stack_unique_push; first done.
      by apply stack_fresh_below.
    - by eapply stack_unique_pop.
  Qed.

  Lemma sections_disjoint_step P agents s act s' :
    stacks_below s ->
    sections_below s ->
    stack_unique s.(open_rscs_stack) ->
    sections_disjoint_from_stacks s ->
    RcuMachine.step P agents s act s' ->
    sections_disjoint_from_stacks s'.
  Proof.
    intros Hstacks Hsections Hunique Hdisjoint Hstep.
    inversion Hstep; subst; simpl; try done.
    - unfold sections_disjoint_from_stacks, lock_emit. simpl.
      eapply (@pushed_sections_disjoint s.(open_rscs_stack)
        s.(closed_sections) s.(next_id) a); last done.
      intros cs Hcs. by destruct (Hsections cs Hcs).
    - unfold sections_disjoint_from_stacks, unlock_emit. simpl.
      eapply (@popped_sections_disjoint s.(open_rscs_stack)
        s.(closed_sections) a l rest s.(next_id)); done.
  Qed.

  Lemma machine_stack_safe_step P agents s act s' :
    machine_stack_safe s ->
    RcuMachine.step P agents s act s' ->
    machine_stack_safe s'.
  Proof.
    intros (Hstacks & Hsections & Hunique & Hdisjoint) Hstep.
    split.
    - by eapply stacks_below_step.
    - split.
      + by eapply sections_below_step.
      + split.
        * by eapply stack_unique_step.
        * by eapply sections_disjoint_step.
  Qed.

  Lemma machine_stack_safe_initial :
    machine_stack_safe initial_state.
  Proof.
    unfold machine_stack_safe. split.
    - intros a l Hin. inversion Hin.
    - split.
      + intros cs Hin. inversion Hin.
      + split.
        * split.
          -- intros a. constructor.
          -- intros a b l Hin. inversion Hin.
        * intros a l cs Hin. inversion Hin.
  Qed.

  Lemma run_preserves_stack_safe P agents s1 actions s2 :
    machine_stack_safe s1 ->
    RcuMachine.run P agents s1 actions s2 ->
    machine_stack_safe s2.
  Proof.
    intros Hsafe Hrun. induction Hrun; first done.
    apply IHHrun. by eapply machine_stack_safe_step.
  Qed.

  Theorem machine_run_stack_safe P agents actions s :
    RcuMachine.run P agents initial_state actions s ->
    machine_stack_safe s.
  Proof.
    intros Hrun. eapply run_preserves_stack_safe; last done.
    apply machine_stack_safe_initial.
  Qed.

  Definition lock_set (locks : list event_id) : gset event_id := list_to_set locks.

  Definition open_map_from_locks (locks : list event_id) :
      gmap event_id unit :=
    list_to_map (map (fun l => (l, tt)) locks).

  Lemma dom_open_map_from_locks locks :
    dom (open_map_from_locks locks) = lock_set locks.
  Proof.
    unfold open_map_from_locks, lock_set. rewrite dom_list_to_map_L.
    induction locks as [|l locks IH]; simpl; first done.
    f_equal. done.
  Qed.

  Lemma completed_snapshot_disjoint_from_open agents s captured :
    machine_stack_safe s ->
    all_closed captured s.(closed_sections) ->
    lock_set captured ## lock_set (snapshot agents s).
  Proof.
    intros (_ & _ & _ & Hdisjoint) Hclosed.
    apply elem_of_disjoint. intros l Hcaptured Hopen.
    unfold lock_set in Hcaptured, Hopen.
    rewrite elem_of_list_to_set, list_elem_of_In in Hcaptured, Hopen.
    destruct (Hclosed l Hcaptured) as (cs & Hcs & Hlock).
    unfold snapshot in Hopen. apply in_flat_map in Hopen.
    destruct Hopen as (a & _ & Hstack).
    by apply (Hdisjoint a l cs).
  Qed.

  Theorem completed_run_certificate_snapshot_clear
      P agents actions s cert :
    RcuMachine.run P agents initial_state actions s ->
    In cert s.(gp_certificates) ->
    lock_set cert.(gc_snapshot) ## lock_set (snapshot agents s).
  Proof.
    intros Hrun Hcert.
    eapply completed_snapshot_disjoint_from_open.
    - by eapply machine_run_stack_safe.
    - pose proof (RcuMachine.operational_soundness P agents actions s Hrun)
        as Hsound.
      by apply (Hsound cert).
  Qed.

  Theorem completed_run_certificate_enables_iris_finish
      P agents actions s cert :
    RcuMachine.run P agents initial_state actions s ->
    In cert s.(gp_certificates) ->
    lock_set cert.(gc_snapshot) ##
      dom (open_map_from_locks (snapshot agents s)).
  Proof.
    intros Hrun Hcert. rewrite dom_open_map_from_locks.
    by eapply completed_run_certificate_snapshot_clear.
  Qed.

End RcuMachineSafety.
