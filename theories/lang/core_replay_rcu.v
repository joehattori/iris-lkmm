From Stdlib Require Import List Lia.
From stdpp Require Import gmap tactics list.
From iris_lkmm.lang Require Import core_replay core_rcu.
Import ListNotations.

(** RCU guards for serialized Core replay.  A certificate below records
    properties of existing Core steps, ready for a later machine lifting. *)
Module LkmmCoreReplayRcu.
  Export LkmmCoreReplay LkmmCoreRcu.

  Definition core_rcu_step_guards (s : core_state) (a : core_action) : Prop :=
    forall thread, s.(core_threads) !! core_action_agent a = Some thread ->
      (thread.(thread_statement) = SRcuReadUnlock ->
        computed_agent_stack s.(core_events) (core_action_agent a) <> []) /\
      (thread.(thread_statement) = SSynchronizeRcu ->
        (compute_rcu_matching s.(core_events)).(unmatched_locks) = []).

  Inductive core_run_rcu_guards (P : core_program) :
      core_state -> list core_action -> core_state -> Prop :=
  | CoreRunRcuGuardsNil s : core_run_rcu_guards P s [] s
  | CoreRunRcuGuardsCons s next final a actions :
      core_step P s a next -> core_rcu_step_guards s a ->
      core_run_rcu_guards P next actions final ->
      core_run_rcu_guards P s (a :: actions) final.

  Lemma core_run_rcu_guards_run P s actions final :
    core_run_rcu_guards P s actions final -> core_run P s actions final.
  Proof. intros Hguards. induction Hguards; by econstructor. Qed.

  Lemma core_run_rcu_guards_append P s actions mid rest final :
    core_run_rcu_guards P s actions mid -> core_run_rcu_guards P mid rest final ->
    core_run_rcu_guards P s (actions ++ rest) final.
  Proof.
    intros Hguards Hrest. induction Hguards; simpl; first done.
    econstructor; [done | done | by apply IHHguards].
  Qed.

  Lemma agent_actions_only agent actions :
    Forall (fun a => core_action_agent a = agent) (agent_actions agent actions).
  Proof.
    apply Forall_forall. intros a Hin. by apply list_elem_of_filter in Hin as [Hagent _].
  Qed.

  Lemma serial_actions_other agents actions reader :
    reader ∉ agents ->
    Forall (fun a => core_action_agent a <> reader) (serial_actions agents actions).
  Proof.
    intros Habsent. apply Forall_forall. intros a Hin Heq.
    assert (a ∈ agent_actions reader (serial_actions agents actions)) as Hfiltered.
    { apply list_elem_of_filter. done. }
    rewrite serial_actions_agent_absent in Hfiltered by done. set_solver.
  Qed.

  (** During one agent's block, every other reader stack remains empty.
      The final RCU premises supply the active agent's local guards. *)
  Lemma core_agent_run_rcu_guards P s actions mid rest final agent :
    core_run P s actions mid ->
    Forall (fun a => core_action_agent a = agent) actions ->
    core_run P mid rest final -> core_allocation_wf s ->
    rcu_replay_wf final.(core_events) ->
    (forall reader, reader <> agent -> computed_agent_stack s.(core_events) reader = []) ->
    core_run_rcu_guards P s actions mid.
  Proof.
    intros Hrun. induction Hrun; intros Honly Hrest Halloc Hrcu Hinactive; first constructor.
    inversion Honly as [|a' actions' Hagent Htail]; subst a' actions'.
    assert (core_allocation_wf state2) as Hnext by (eapply core_step_preserves_allocation; done).
    econstructor; first done.
    - intros thread Hthread.
      assert (core_run P state2 (actions ++ rest) final) as Hfuture.
      { by eapply core_run_append. }
      destruct (core_step_rcu_local_guards _ _ _ _ _ _ _ H Hfuture Halloc Hrcu Hthread)
        as [Hunlock Hsync]. split; first done.
      intros Hstmt. apply computed_agent_stacks_empty; first exact (proj1 Halloc).
      intros reader. destruct (decide (reader = agent)) as [-> | Hother].
      + rewrite <- Hagent. by apply Hsync.
      + by apply Hinactive.
    - apply IHHrun; try done. intros reader Hother. unfold computed_agent_stack.
      rewrite (core_step_matching_other _ _ _ _ reader H Halloc) by congruence.
      by apply Hinactive.
  Qed.

  Theorem serial_replay_rcu_guards P actions source agents base final :
    serial_replay P actions source agents base final -> NoDup agents ->
    core_allocation_wf base -> rcu_replay_wf final.(core_events) ->
    (forall reader, computed_agent_stack base.(core_events) reader = []) ->
    core_run_rcu_guards P base (serial_actions agents actions) final.
  Proof.
    intros Hserial. induction Hserial as
      [base | agent agents base next final Hrun Hmatch Hserial IH];
      intros Hnodup Halloc Hrcu Hempty; first constructor.
    apply NoDup_cons in Hnodup as [Habsent Hnodup].
    pose proof (serial_replay_run _ _ _ _ _ _ Hserial) as Hrest.
    assert (core_allocation_wf next) as Hnext by (eapply core_run_preserves_allocation; done).
    simpl. eapply core_run_rcu_guards_append.
    - eapply core_agent_run_rcu_guards; try done. apply agent_actions_only.
    - apply IH; try done. intros reader.
      destruct (decide (reader = agent)) as [-> | Hother].
      + unfold computed_agent_stack.
        rewrite <- (core_run_matching_other _ _ _ _ agent Hrest Hnext
          (serial_actions_other _ _ _ Habsent)).
        apply rcu_matching_complete_agent_stack; last exact (proj1 Hrcu).
        exact (proj1 (core_run_preserves_allocation _ _ _ _ Hrest Hnext)).
      + unfold computed_agent_stack.
        rewrite (core_run_matching_other _ _ _ _ reader Hrun Halloc); first apply Hempty.
        apply Forall_forall. intros a Hin.
        apply list_elem_of_filter in Hin as [Hagent _]. congruence.
  Qed.

  (** Any enumeration of whole agent blocks gives a completed replay whose
      unlocks are enabled and whose synchronizations have empty snapshots.
      This does not quantify over arbitrary action interleavings. *)
  Theorem complete_core_run_replay_rcu_order P actions source agents :
    complete_core_run P actions source -> program_agent_enumeration P agents ->
    rcu_replay_wf source.(core_events) ->
    exists final f,
      complete_core_run P (serial_actions agents actions) final /\
      core_state_renaming f source final /\ rcu_replay_wf final.(core_events) /\
      core_run_rcu_guards P (core_initial_state P) (serial_actions agents actions) final.
  Proof.
    intros Hrun Henumeration Hrcu.
    destruct (complete_core_run_replay_order _ _ _ _ Hrun Henumeration)
      as (final & f & Hcomplete & Hserial & Hrename).
    assert (rcu_replay_wf final.(core_events)) as Hfinal.
    { eapply core_state_renaming_rcu; [done | | done].
      exact (core_run_allocation_wf _ _ _ (proj1 Hrun)). }
    exists final, f. split; first done. split; first done. split; first done.
    eapply serial_replay_rcu_guards; [done | exact (proj1 Henumeration) |
      apply core_initial_allocation_wf | done |].
    intros reader. unfold computed_agent_stack. by rewrite initial_agent_matching.
  Qed.

  Theorem complete_core_run_replay_rcu P actions source :
    complete_core_run P actions source -> rcu_replay_wf source.(core_events) ->
    exists final f,
      complete_core_run P (serial_actions (program_agents_list P) actions) final /\
      core_state_renaming f source final /\ rcu_replay_wf final.(core_events) /\
      core_run_rcu_guards P (core_initial_state P)
        (serial_actions (program_agents_list P) actions) final.
  Proof.
    intros Hrun Hrcu. eapply complete_core_run_replay_rcu_order;
      [done | apply program_agents_list_enumeration | done].
  Qed.
End LkmmCoreReplayRcu.
