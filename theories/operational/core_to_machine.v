From Stdlib Require Import List.
From stdpp Require Import gmap tactics.
From iris_lkmm.lang Require Import core_replay_rcu.
From iris_lkmm.operational Require Import lkmm_machine.
Import ListNotations.

(** Construct machine executions by lifting guarded Core runs, then compose
    this lifting with serialized replay for completed Core runs satisfying
    the event-level RCU premises.  The resulting correspondence to the
    original Core state is recorded by an event-ID renaming. *)
Module LkmmCoreToMachine.
  Export LkmmMachine LkmmCoreReplayRcu.

  Definition lift_core_action (a : core_action) (statement : stmt) : list action :=
    match statement with
    | SRcuReadLock => [ReadLock (core_action_agent a)]
    | SRcuReadUnlock => [ReadUnlock (core_action_agent a)]
    | SSynchronizeRcu => [BeginGp (core_action_agent a); FinishGp (core_action_agent a)]
    | _ => [Execute a]
    end.

  (** Even an empty snapshot has a begin and a finish step.  Finishing
      retains previous certificates and clears the newly pending GP. *)
  Lemma empty_snapshot_gp_run P s agent thread :
    current s agent thread SSynchronizeRcu -> s.(pending_gp) = ∅ -> all_open_readers s = [] ->
    run P s [BeginGp agent; FinishGp agent]
      (State (emit_rcu s agent thread BarrierSyncRcu) ∅
        (GpCertificate s.(machine_core).(core_next_id) [] :: s.(gp_certificates))).
  Proof.
    intros Hcurrent Hpending Hsnapshot.
    replace (State (emit_rcu s agent thread BarrierSyncRcu) ∅
      (GpCertificate s.(machine_core).(core_next_id) [] :: s.(gp_certificates)))
      with (finish_gp (begin_gp s agent) agent thread []).
    - eapply RunCons.
      + eapply StepBeginGp; first done. by rewrite Hpending, lookup_empty.
      + eapply RunCons; last constructor. apply StepFinishGp.
        * exact Hcurrent.
        * cbn. by rewrite lookup_insert_eq, Hsnapshot.
        * intros lock Hfalse. done.
    - unfold finish_gp, begin_gp, emit_rcu. cbn.
      by rewrite delete_insert_eq, Hpending, delete_empty.
  Qed.

  Lemma core_step_machine_lift P s a core' thread :
    core_step P s.(machine_core) a core' -> core_rcu_step_guards s.(machine_core) a ->
    s.(pending_gp) = ∅ ->
    s.(machine_core).(core_threads) !! core_action_agent a = Some thread ->
    exists s',
      run P s (lift_core_action a thread.(thread_statement)) s' /\
      s'.(machine_core) = core' /\ s'.(pending_gp) = ∅ /\
      project_actions (lift_core_action a thread.(thread_statement)) = [a].
  Proof.
    destruct s as [core pending certs]. cbn. intros Hstep Hguards -> Hthread.
    destruct (Hguards thread Hthread) as [Hunlock Hsync].
    pose proof Hstep as Hcore. destruct Hstep; cbn in Hthread |- *; simplify_eq;
      rewrite H0; cbn [lift_core_action core_action_agent];
      try solve [eexists; split;
        [eapply RunCons; [eapply StepCore; [exact H | rewrite H0; done | done | exact Hcore] |
          constructor] | split_and!; done]].
    - eexists. split.
      + eapply RunCons; last constructor. eapply StepReadLock; [split; done | done].
      + split_and!; done.
    - specialize (Hunlock H0).
      destruct (computed_agent_stack (core_events state0) agent) as [|lock rest] eqn:Hstack;
        first done.
      eexists. split.
      + eapply RunCons; last constructor.
        eapply StepReadUnlock; [split; done | done | exact Hstack].
      + split_and!; done.
    - eexists. split.
      + apply empty_snapshot_gp_run; [split; done | done | by apply Hsync].
      + split_and!; done.
  Qed.

  Local Lemma machine_run_append P s actions mid rest final :
    run P s actions mid -> run P mid rest final -> run P s (actions ++ rest) final.
  Proof.
    intros Hrun Hrest. induction Hrun; simpl; first done.
    econstructor; [done | by apply IHHrun].
  Qed.

  (** Empty pending maps at Core-step boundaries allow the next step to
      run.  No completion premise is needed to lift an execution prefix. *)
  Theorem core_run_machine_lift P core actions final s :
    core_run_rcu_guards P core actions final -> s.(machine_core) = core ->
    s.(pending_gp) = ∅ ->
    exists machine_actions s',
      run P s machine_actions s' /\ s'.(machine_core) = final /\
      s'.(pending_gp) = ∅ /\ project_actions machine_actions = actions.
  Proof.
    intros Hguards. revert s.
    induction Hguards as [core | core next final a actions Hstep Hguard Hrest IH];
      intros s Hcore Hpending.
    - exists [], s. split; first constructor. split_and!; done.
    - destruct (core_step_actor _ _ _ _ Hstep) as [thread Hthread].
      rewrite <- Hcore in Hstep, Hguard, Hthread.
      destruct (core_step_machine_lift _ _ _ _ _ Hstep Hguard Hpending Hthread)
        as (mid & Hlift & Hmid_core & Hmid_pending & Hproject).
      destruct (IH mid Hmid_core Hmid_pending)
        as (rest & s' & Hrun & Hfinal & Hempty & Hproject_rest).
      exists (lift_core_action a thread.(thread_statement) ++ rest), s'.
      split; first by eapply machine_run_append.
      split; first done. split; first done.
      unfold project_actions in *. by rewrite flat_map_app, Hproject, Hproject_rest.
  Qed.

  (** The supplied Core schedule and event IDs are preserved. Final matching
      is required separately: Core threads may finish with an open reader
      even when every executed step satisfies the local guards. *)
  Theorem complete_core_run_machine_lift P actions final :
    complete_core_run P actions final ->
    core_run_rcu_guards P (core_initial_state P) actions final ->
    rcu_matching_complete final.(core_events) ->
    exists machine_actions s,
      complete_machine_run P machine_actions s /\ s.(machine_core) = final /\
      project_actions machine_actions = actions.
  Proof.
    intros [_ Hcomplete] Hguards Hmatching.
    destruct (core_run_machine_lift _ _ _ _ (initial_state P) Hguards eq_refl eq_refl)
      as (machine_actions & s & Hrun & Hcore & Hpending & Hproject).
    exists machine_actions, s. split; last done. split; first done.
    unfold complete. rewrite Hcore. split_and!; done.
  Qed.

  (** Conditional Core-to-machine completeness.  Replay establishes the
      guards internally; the original execution need not satisfy them.
      The chosen enumeration orders whole agent blocks, preserving each
      agent's original action subsequence. *)
  Theorem complete_core_run_machine_replay_order P actions source agents :
    complete_core_run P actions source -> program_agent_enumeration P agents ->
    rcu_replay_wf source.(core_events) ->
    exists machine_actions s f,
      complete_machine_run P machine_actions s /\ core_state_renaming f source s.(machine_core) /\
      project_actions machine_actions = serial_actions agents actions.
  Proof.
    intros Hsource Henumeration Hrcu.
    destruct (complete_core_run_replay_rcu_order _ _ _ _ Hsource Henumeration Hrcu)
      as (replayed & f & Hcomplete & Hrename & Hreplayed_rcu & Hguards).
    destruct (complete_core_run_machine_lift _ _ _ Hcomplete Hguards (proj1 Hreplayed_rcu))
      as (machine_actions & s & Hrun & Hcore & Hproject).
    exists machine_actions, s, f. split; first done. split; last done.
    by rewrite Hcore.
  Qed.

  Theorem complete_core_run_machine_replay P actions source :
    complete_core_run P actions source -> rcu_replay_wf source.(core_events) ->
    exists machine_actions s f,
      complete_machine_run P machine_actions s /\ core_state_renaming f source s.(machine_core) /\
      project_actions machine_actions = serial_actions (program_agents_list P) actions.
  Proof.
    intros Hsource Hrcu. eapply complete_core_run_machine_replay_order;
      [done | apply program_agents_list_enumeration | done].
  Qed.
End LkmmCoreToMachine.
