From Stdlib Require Import List Lia.
From stdpp Require Import gmap fin_map_dom fin_sets tactics list.
From iris_lkmm.lang Require Import core_agent_replay.
Import ListNotations.

(** Whole-program Core replay.  The certificates below retain the exact
    per-agent graph/provenance correspondence at each replay boundary.  They
    are proof witnesses, not additional Core transition rules or state. *)
Module LkmmCoreReplay.
  Export LkmmCoreAgentReplay.

  Fixpoint serial_actions (agents : list agent_id) (actions : list core_action) :=
    match agents with
    | [] => []
    | t :: rest => agent_actions t actions ++ serial_actions rest actions
    end.

  Lemma agent_actions_app t xs ys :
    agent_actions t (xs ++ ys) = agent_actions t xs ++ agent_actions t ys.
  Proof. unfold agent_actions. apply filter_app. Qed.

  Lemma agent_actions_same t actions :
    agent_actions t (agent_actions t actions) = agent_actions t actions.
  Proof. unfold agent_actions. apply list_filter_filter_l. done. Qed.

  Lemma agent_actions_other t other actions :
    t <> other -> agent_actions t (agent_actions other actions) = [].
  Proof.
    intros Hne. apply elem_of_nil_inv. intros a Hin.
    apply list_elem_of_filter in Hin as [Ht Hin].
    apply list_elem_of_filter in Hin as [Hother _]. congruence.
  Qed.

  Lemma serial_actions_agent_absent agents actions t :
    t ∉ agents -> agent_actions t (serial_actions agents actions) = [].
  Proof.
    induction agents as [|other rest IH]; intros Hnotin; first done.
    simpl. rewrite agent_actions_app, agent_actions_other by set_solver.
    simpl. apply IH. set_solver.
  Qed.

  (** Serialization changes only the interleaving.  Every agent keeps exactly
      its original actions, including all observed values and silent steps. *)
  Theorem serial_actions_agent agents actions t :
    NoDup agents -> t ∈ agents ->
    agent_actions t (serial_actions agents actions) = agent_actions t actions.
  Proof.
    intros Hnodup. induction Hnodup as [|other rest Hnotin Hnodup IH]; intros Hin;
      first set_solver.
    simpl. rewrite agent_actions_app. destruct (decide (t = other)) as [-> | Hne].
    - rewrite agent_actions_same, serial_actions_agent_absent by done.
      by rewrite app_nil_r.
    - rewrite agent_actions_other by done. simpl. apply IH. set_solver.
  Qed.

  Definition program_agent_order (P : core_program) (agents : list agent_id) : Prop :=
    NoDup agents /\ forall t, t ∈ agents <-> is_Some (P.(program_agents) !! t).

  Definition program_agents_list (P : core_program) : list agent_id :=
    elements (dom P.(program_agents) : gset agent_id).

  Lemma program_agents_list_order P : program_agent_order P (program_agents_list P).
  Proof.
    unfold program_agent_order, program_agents_list. split; first apply NoDup_elements.
    intros t. rewrite elem_of_elements. apply elem_of_dom.
  Qed.

  Inductive serial_replay (P : core_program) (actions : list core_action)
      (source : core_state) : list agent_id -> core_state -> core_state -> Prop :=
  | SerialReplayNil base : serial_replay P actions source [] base base
  | SerialReplayCons t rest base next final :
      core_run P base (agent_actions t actions) next ->
      replay_state (replay_id source.(core_events) t base.(core_next_id))
        source.(core_events) t base source next ->
      serial_replay P actions source rest next final ->
      serial_replay P actions source (t :: rest) base final.

  Lemma serial_replay_run P actions source agents base final :
    serial_replay P actions source agents base final ->
    core_run P base (serial_actions agents actions) final.
  Proof.
    intros Hreplay. induction Hreplay; simpl; first constructor.
    by eapply core_run_append.
  Qed.

  (** Induction invariant: remaining agents are initial, while agents outside
      the remaining list have already completed.  Replaying the head moves
      exactly one agent from the former group to the latter. *)
  Lemma complete_core_run_replay_remaining P actions source agents base :
    complete_core_run P actions source -> NoDup agents -> core_allocation_wf base ->
    (forall t, t ∈ agents ->
      base.(core_threads) !! t = (core_initial_state P).(core_threads) !! t /\
      next_agent_index base t = 0) ->
    (forall t th, t ∉ agents -> base.(core_threads) !! t = Some th -> thread_complete th) ->
    exists final, serial_replay P actions source agents base final /\ core_complete final.
  Proof.
    intros Hsource Hnodup. revert base.
    induction Hnodup as [|t rest Hnotin Hnodup IH]; intros base Halloc Hinitial Hfinished.
    - exists base. split; first constructor. intros other th Hlookup.
      eapply (Hfinished other th); [set_solver | done].
    - destruct (Hinitial t ltac:(set_solver)) as [Hthread Hindex].
      destruct (complete_core_run_replay_agent _ _ _ _ _ Hsource Halloc Hthread Hindex)
        as (next & Hrun & Hmatch & Hcomplete).
      assert (core_allocation_wf next) as Hnext.
      { by eapply core_run_preserves_allocation. }
      assert (forall other, other ∈ rest ->
        next.(core_threads) !! other = (core_initial_state P).(core_threads) !! other /\
        next_agent_index next other = 0) as Hrest_initial.
      { intros other Hin. assert (other <> t) as Hne by set_solver.
        destruct (Hinitial other ltac:(set_solver)) as [Hth Hidx]. split.
        - rewrite (replay_other_threads _ _ _ _ _ _ Hmatch other Hne). done.
        - rewrite (agent_replay_other_index _ _ _ _ _ _ Hrun Hne). done. }
      assert (forall other th, other ∉ rest -> next.(core_threads) !! other = Some th ->
        thread_complete th) as Hrest_finished.
      { intros other th Hout Hlookup. destruct (decide (other = t)) as [-> | Hne].
        - by apply Hcomplete.
        - rewrite (replay_other_threads _ _ _ _ _ _ Hmatch other Hne) in Hlookup.
          eapply (Hfinished other th); [set_solver | done]. }
      destruct (IH next Hnext Hrest_initial Hrest_finished) as (final & Hserial & Hfinal).
      exists final. split; last done. by econstructor.
  Qed.

  (** Any enumeration of the program's agents, with no repetitions, gives
      a completed serialized Core run with the original per-agent actions. *)
  Theorem complete_core_run_replay_order P actions source agents :
    complete_core_run P actions source -> program_agent_order P agents ->
    exists final,
      complete_core_run P (serial_actions agents actions) final /\
      serial_replay P actions source agents (core_initial_state P) final.
  Proof.
    intros Hsource [Hnodup Hcover].
    destruct (complete_core_run_replay_remaining P actions source agents (core_initial_state P)
      Hsource Hnodup (core_initial_allocation_wf P)) as (final & Hserial & Hfinal).
    - intros t Hin. split; done.
    - intros t th Hout Hlookup. simpl in Hlookup.
      apply lookup_fmap_Some in Hlookup as (body & Hth & Hbody).
      exfalso. apply Hout, Hcover. by exists body.
    - exists final. split; last done. split; last done. by apply serial_replay_run in Hserial.
  Qed.

  Theorem complete_core_run_replay P actions source :
    complete_core_run P actions source ->
    exists final,
      complete_core_run P (serial_actions (program_agents_list P) actions) final /\
      serial_replay P actions source (program_agents_list P) (core_initial_state P) final.
  Proof.
    intros Hsource. apply complete_core_run_replay_order; first done.
    apply program_agents_list_order.
  Qed.
End LkmmCoreReplay.
