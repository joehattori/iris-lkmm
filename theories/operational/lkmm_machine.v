From Stdlib Require Import List Lia.
From stdpp Require Import gmap tactics.
From iris_lkmm.lang Require Import lkmm_core core_rcu.
From iris_lkmm.lkmm Require Import rcu_matching.
Import ListNotations.

(** LKMM-Core execution with normal-RCU snapshot waiting.
    Reader stacks and completed sections are computed from canonical events;
    only pending snapshots and completion certificates need additional state.
    This machine neither chooses [rf]/[co] nor tests final LKMM consistency. *)
Module LkmmMachine.
  Export LkmmCore.
  Import RcuMatching LkmmCoreRcu.

  Record gp_certificate := GpCertificate {
    gc_event : event_id;
    gc_snapshot : list event_id
  }.

  Record state := State {
    machine_core : core_state;
    pending_gp : gmap agent_id (list event_id);
    gp_certificates : list gp_certificate
  }.

  Definition initial_state (P : core_program) : state := State (core_initial_state P) ∅ [].

  Definition open_readers (s : state) (agent : agent_id) : list event_id :=
    computed_agent_stack s.(machine_core).(core_events) agent.

  Definition snapshot (s : state) : list event_id :=
    (compute_rcu_matching s.(machine_core).(core_events)).(unmatched_locks).

  Definition all_closed (E : event_structure) (locks : list event_id) : Prop :=
    forall lock, In lock locks -> exists unlock, rcu_rscs E lock unlock.

  Definition current (s : state) (agent : agent_id) (thread : thread_state)
      (statement : stmt) : Prop :=
    s.(machine_core).(core_threads) !! agent = Some thread /\
    thread.(thread_statement) = statement.

  Definition ordinary_statement (statement : stmt) : Prop :=
    match statement with
    | SRcuReadLock | SRcuReadUnlock | SSynchronizeRcu => False
    | _ => True
    end.

  Definition action_agent (a : core_action) : agent_id :=
    match a with CoreSilent agent | CoreEmit agent | CoreObserve agent _ => agent end.

  Definition with_core (s : state) (core : core_state) : state :=
    State core s.(pending_gp) s.(gp_certificates).

  Definition emit_rcu (s : state) (agent : agent_id) (thread : thread_state)
      (kind : barrier_kind) : core_state :=
    add_single_event s.(machine_core) agent thread (LBarrier kind)
      thread.(thread_registers) ∅ ∅ ∅.

  Definition begin_gp (s : state) (agent : agent_id) : state :=
    State s.(machine_core) (<[agent := snapshot s]> s.(pending_gp)) s.(gp_certificates).

  Definition finish_gp (s : state) (agent : agent_id) (thread : thread_state)
      (locks : list event_id) : state :=
    State (emit_rcu s agent thread BarrierSyncRcu) (delete agent s.(pending_gp))
      (GpCertificate s.(machine_core).(core_next_id) locks :: s.(gp_certificates)).

  Inductive action :=
  | Execute (a : core_action)
  | ReadLock (agent : agent_id)
  | ReadUnlock (agent : agent_id)
  | BeginGp (agent : agent_id)
  | FinishGp (agent : agent_id).

  Inductive step (P : core_program) : state -> action -> state -> Prop :=
  | StepCore s core' a thread :
      s.(machine_core).(core_threads) !! action_agent a = Some thread ->
      ordinary_statement thread.(thread_statement) ->
      s.(pending_gp) !! action_agent a = None ->
      core_step P s.(machine_core) a core' ->
      step P s (Execute a) (with_core s core')
  | StepReadLock s agent thread :
      current s agent thread SRcuReadLock ->
      s.(pending_gp) !! agent = None ->
      step P s (ReadLock agent) (with_core s (emit_rcu s agent thread BarrierRcuLock))
  | StepReadUnlock s agent thread lock rest :
      current s agent thread SRcuReadUnlock ->
      s.(pending_gp) !! agent = None ->
      open_readers s agent = lock :: rest ->
      step P s (ReadUnlock agent) (with_core s (emit_rcu s agent thread BarrierRcuUnlock))
  | StepBeginGp s agent thread :
      current s agent thread SSynchronizeRcu ->
      s.(pending_gp) !! agent = None ->
      step P s (BeginGp agent) (begin_gp s agent)
  | StepFinishGp s agent thread locks :
      current s agent thread SSynchronizeRcu ->
      s.(pending_gp) !! agent = Some locks ->
      all_closed s.(machine_core).(core_events) locks ->
      step P s (FinishGp agent) (finish_gp s agent thread locks).

  Inductive run (P : core_program) : state -> list action -> state -> Prop :=
  | RunNil s : run P s [] s
  | RunCons s1 s2 s3 a actions :
      step P s1 a s2 -> run P s2 actions s3 -> run P s1 (a :: actions) s3.

  Definition complete (s : state) : Prop :=
    core_complete s.(machine_core) /\ s.(pending_gp) = ∅ /\
    rcu_matching_complete s.(machine_core).(core_events).

  Definition complete_run (P : core_program) (actions : list action) (s : state) : Prop :=
    run P (initial_state P) actions s /\ complete s.

  Definition core_actions_of (a : action) : list core_action :=
    match a with
    | Execute a => [a]
    | ReadLock agent | ReadUnlock agent | FinishGp agent => [CoreEmit agent]
    | BeginGp _ => []
    end.

  Definition project_actions (actions : list action) : list core_action :=
    flat_map core_actions_of actions.

  Lemma step_core_projection P s a s' :
    step P s a s' ->
    core_run P s.(machine_core) (core_actions_of a) s'.(machine_core).
  Proof.
    intros Hstep. destruct Hstep as
      [s core' a thread Hthread Hordinary Hready Hcore |
       s agent thread [Hthread Hstmt] Hready |
       s agent thread lock rest [Hthread Hstmt] Hready Hstack |
       s agent thread [Hthread Hstmt] Hready |
       s agent thread locks [Hthread Hstmt] Hpending Hclosed]; simpl.
    - econstructor; [done | constructor].
    - econstructor; last constructor. by apply StepRcuReadLock.
    - econstructor; last constructor. by apply StepRcuReadUnlock.
    - constructor.
    - econstructor; last constructor. by apply StepSynchronizeRcu.
  Qed.

  Local Lemma core_run_app P core1 actions1 core2 actions2 core3 :
    core_run P core1 actions1 core2 -> core_run P core2 actions2 core3 ->
    core_run P core1 (actions1 ++ actions2) core3.
  Proof.
    intros Hrun Hrest. induction Hrun; simpl; first done.
    econstructor; [done | by apply IHHrun].
  Qed.

  Theorem run_core_projection P s actions s' :
    run P s actions s' ->
    core_run P s.(machine_core) (project_actions actions) s'.(machine_core).
  Proof.
    intros Hrun. induction Hrun; simpl; first constructor.
    eapply core_run_app; last done. by apply step_core_projection.
  Qed.

  Theorem complete_run_core_projection P actions s :
    complete_run P actions s -> complete_core_run P (project_actions actions) s.(machine_core).
  Proof.
    intros [Hrun [Hcomplete _]]. split; last done.
    by apply run_core_projection in Hrun.
  Qed.

  Theorem run_allocation_wf P actions s :
    run P (initial_state P) actions s -> core_allocation_wf s.(machine_core).
  Proof.
    intros Hrun. apply run_core_projection in Hrun.
    exact (core_run_allocation_wf P (project_actions actions) s.(machine_core) Hrun).
  Qed.

  (** A begun GP retains its snapshot while any other agent executes. *)
  Definition executing_agent (a : action) : agent_id :=
    match a with
    | Execute a => action_agent a
    | ReadLock agent | ReadUnlock agent | BeginGp agent | FinishGp agent => agent
    end.

  Lemma step_pending_other P s a s' agent :
    step P s a s' -> executing_agent a <> agent ->
    s'.(pending_gp) !! agent = s.(pending_gp) !! agent.
  Proof.
    intros Hstep Hother. destruct Hstep; simpl in *; try done.
    - by rewrite lookup_insert_ne.
    - by rewrite lookup_delete_ne.
  Qed.

  Lemma pending_agent_only_finishes P s a s' agent locks :
    step P s a s' -> executing_agent a = agent ->
    s.(pending_gp) !! agent = Some locks ->
    a = FinishGp agent /\ all_closed s.(machine_core).(core_events) locks.
  Proof.
    intros Hstep Hagent Hpending. destruct Hstep; simpl in Hagent; subst;
      simplify_eq; try congruence. split; done.
  Qed.

  Lemma finish_gp_enabled P s agent thread locks :
    current s agent thread SSynchronizeRcu ->
    s.(pending_gp) !! agent = Some locks ->
    all_closed s.(machine_core).(core_events) locks ->
    step P s (FinishGp agent) (finish_gp s agent thread locks).
  Proof. intros. by econstructor. Qed.

  Local Lemma ordinary_step_matching P core a core' thread reader :
    core.(core_threads) !! action_agent a = Some thread ->
    ordinary_statement thread.(thread_statement) ->
    core_step P core a core' -> core_allocation_wf core ->
    compute_agent_match_state core'.(core_events) reader =
      compute_agent_match_state core.(core_events) reader.
  Proof.
    intros Hthread Hordinary Hstep Hwf. destruct Hstep; cbn in Hthread;
      simplify_eq; try done;
      try solve [rewrite H0 in Hordinary; done];
      try solve [apply next_rmw_matching; done];
      try solve [apply compute_agent_state_insert_non_rcu;
        [by apply core_next_id_fresh | done]].
    destruct kind; apply compute_agent_state_insert_non_rcu;
      solve [by apply core_next_id_fresh | done].
  Qed.

  Definition no_unmatched_unlocks (s : state) : Prop :=
    forall agent,
      (compute_agent_match_state s.(machine_core).(core_events) agent).(match_unmatched_unlocks)
        = [].

  Local Lemma emit_rcu_no_underflow s agent thread kind :
    core_allocation_wf s.(machine_core) -> no_unmatched_unlocks s ->
    (kind = BarrierRcuUnlock -> open_readers s agent <> []) ->
    forall reader,
      (compute_agent_match_state (emit_rcu s agent thread kind).(core_events) reader)
        .(match_unmatched_unlocks) = [].
  Proof.
    intros Hwf Hsafe Hnonempty reader.
    pose proof (next_event_tail s.(machine_core) agent (LBarrier kind) Hwf) as Htail.
    pose proof (core_next_id_fresh s.(machine_core) Hwf) as Hfresh.
    unfold emit_rcu. cbn.
    destruct kind; try solve [rewrite compute_agent_state_insert_non_rcu;
      [apply Hsafe | done | done]].
    - destruct (decide (agent = reader)) as [<- | Hother].
      + pose proof (compute_agent_state_insert_tail _ _ _
          (RcuToken _ agent _ RcuTokenLock) Htail eq_refl) as Hmatch.
        cbn in Hmatch. rewrite Hmatch. cbn. apply Hsafe.
      + rewrite (compute_agent_state_insert_other _ _
          (EAgent agent (next_agent_index s.(machine_core) agent) (LBarrier BarrierRcuLock))
          (RcuToken _ agent _ RcuTokenLock) reader Hfresh eq_refl Hother). apply Hsafe.
    - destruct (decide (agent = reader)) as [<- | Hother].
      + pose proof (compute_agent_state_insert_tail _ _ _
          (RcuToken _ agent _ RcuTokenUnlock) Htail eq_refl) as Hmatch.
        cbn in Hmatch. rewrite Hmatch. cbn.
        specialize (Hnonempty eq_refl). unfold open_readers, computed_agent_stack in Hnonempty.
        destruct (token_stack (compute_agent_match_state s.(machine_core).(core_events) agent)
          agent); first done. cbn. apply Hsafe.
      + rewrite (compute_agent_state_insert_other _ _
          (EAgent agent (next_agent_index s.(machine_core) agent) (LBarrier BarrierRcuUnlock))
          (RcuToken _ agent _ RcuTokenUnlock) reader Hfresh eq_refl Hother). apply Hsafe.
  Qed.

  Lemma step_preserves_no_unmatched_unlocks P s a s' :
    step P s a s' -> core_allocation_wf s.(machine_core) ->
    no_unmatched_unlocks s -> no_unmatched_unlocks s'.
  Proof.
    intros Hstep Hwf Hsafe reader. destruct Hstep; cbn.
    - rewrite (ordinary_step_matching _ _ _ _ _ reader H H0 H2 Hwf). apply Hsafe.
    - eapply (emit_rcu_no_underflow s agent thread); done.
    - eapply (emit_rcu_no_underflow s agent thread); try done. intros _.
      rewrite H1. done.
    - apply Hsafe.
    - eapply (emit_rcu_no_underflow s agent thread); done.
  Qed.

  Definition certificates_sound (s : state) : Prop :=
    forall cert, In cert s.(gp_certificates) ->
      all_closed s.(machine_core).(core_events) cert.(gc_snapshot).

  Local Lemma all_closed_mono E E' locks :
    rel_included (rcu_rscs E) (rcu_rscs E') -> all_closed E locks -> all_closed E' locks.
  Proof.
    intros Hmono Hclosed lock Hin. destruct (Hclosed lock Hin) as [unlock Hsection].
    exists unlock. by apply Hmono.
  Qed.

  Lemma step_preserves_certificates P s a s' :
    step P s a s' -> core_allocation_wf s.(machine_core) ->
    certificates_sound s -> certificates_sound s'.
  Proof.
    intros Hstep Hwf Hcerts.
    assert (rel_included (rcu_rscs s.(machine_core).(core_events))
      (rcu_rscs s'.(machine_core).(core_events))) as Hmono.
    { pose proof (step_core_projection _ _ _ _ Hstep) as Hrun.
      induction Hrun; first by intros x y Hxy.
      eapply rel_included_trans; first by eapply core_step_sections_mono.
      apply IHHrun. by eapply core_step_preserves_allocation. }
    destruct Hstep; intros cert Hin; cbn in *;
      try solve [eapply all_closed_mono; [exact Hmono | by apply Hcerts]].
    destruct Hin as [<- | Hin].
    - eapply all_closed_mono; done.
    - eapply all_closed_mono; [exact Hmono | by apply Hcerts].
  Qed.

  Theorem run_rcu_safety P actions s :
    run P (initial_state P) actions s ->
    no_unmatched_unlocks s /\ certificates_sound s.
  Proof.
    intros Hrun.
    assert (forall s1 actions0 s2, run P s1 actions0 s2 ->
      core_allocation_wf s1.(machine_core) -> no_unmatched_unlocks s1 ->
      certificates_sound s1 -> no_unmatched_unlocks s2 /\ certificates_sound s2) as Hpreserve.
    { intros s1 actions0 s2 Hsteps. induction Hsteps; intros Hwf Hsafe Hcerts; first done.
      apply IHHsteps.
      - eapply core_run_preserves_allocation; [by apply step_core_projection | done].
      - by eapply step_preserves_no_unmatched_unlocks.
      - by eapply step_preserves_certificates. }
    eapply Hpreserve; first done.
    - apply core_initial_allocation_wf.
    - intros agent. change ((compute_agent_match_state
        (core_initial_state P).(core_events) agent).(match_unmatched_unlocks) = []).
      by rewrite initial_agent_matching.
    - intros cert Hfalse. inversion Hfalse.
  Qed.

  Local Lemma matched_lock_not_open E lock unlock :
    event_structure_wf E -> rcu_rscs E lock unlock ->
    ~ In lock (compute_rcu_matching E).(unmatched_locks).
  Proof.
    intros HE Hmatched.
    assert (forall agent, ~ In lock (compute_agent_matching E agent).(unmatched_locks)) as Hlocal.
    { intros agent Hlock. unfold compute_agent_matching, result_of_state in Hlock. cbn in Hlock.
      apply in_map_iff in Hlock as (token & <- & Hstacked).
      apply stacked_tokens_spec in Hstacked as (stack_agent & stack & Hstack & Hin).
      destruct (compute_agent_match_state_wf E agent HE) as [Hstacks _].
      destruct (Hstacks stack_agent stack Hstack token Hin) as
        (Htoken & Hstack_agent & Hkind & Hvalid).
      pose proof (rcu_agent_token_trace_lookup E agent token Htoken) as [Hagent _].
      assert (stack_agent = agent) as -> by congruence.
      destruct Hmatched as (matched_agent & Hsection).
      destruct (compute_agent_matching_section_agent E matched_agent
        (CriticalSection (token_id token) unlock) HE Hsection) as
        (lock_index & unlock_index & Hlookup & _).
      cbn in Hlookup. unfold rcu_token_valid, event_of_rcu_token in Hvalid.
      rewrite Hkind in Hvalid. unfold lookup_event in Hvalid.
      assert (matched_agent = agent) as -> by congruence.
      destruct (compute_agent_match_state_unique E agent) as (Hlocks & _).
      unfold agent_lock_ids in Hlocks.
      apply (proj1 (stdpp.list_relations.list.NoDup_app _ _)) in Hlocks as (_ & Hdisjoint & _).
      apply (Hdisjoint (token_id token)).
      - rewrite list_elem_of_In. apply in_map_iff.
        exists (CriticalSection (token_id token) unlock). done.
      - rewrite list_elem_of_In. apply in_map_iff. exists token. split; first done.
        unfold token_stack. rewrite Hstack. done. }
    unfold compute_rcu_matching. induction (rcu_agents E) as [|agent agents IH]; cbn.
    - intros Hfalse. exact Hfalse.
    - intros Hin. apply in_app_or in Hin as [Hin | Hin].
      + by apply (Hlocal agent).
      + by apply IH.
  Qed.

  Theorem completed_snapshot_clear P actions s cert :
    run P (initial_state P) actions s -> In cert s.(gp_certificates) ->
    forall lock, In lock cert.(gc_snapshot) -> ~ In lock (snapshot s).
  Proof.
    intros Hrun Hcert lock Hlock.
    destruct (run_rcu_safety _ _ _ Hrun) as [_ Hsound].
    destruct (Hsound cert Hcert lock Hlock) as (unlock & Hmatched).
    apply (matched_lock_not_open _ _ unlock); last done.
    by destruct (run_allocation_wf _ _ _ Hrun) as [HE _].
  Qed.

  Lemma captured_reader_blocks_finish P s agent locks lock :
    core_allocation_wf s.(machine_core) -> s.(pending_gp) !! agent = Some locks ->
    In lock locks -> In lock (snapshot s) -> forall s', ~ step P s (FinishGp agent) s'.
  Proof.
    intros [HE _] Hpending Hlock Hopen s' Hstep.
    destruct (pending_agent_only_finishes _ _ _ _ _ _ Hstep eq_refl Hpending) as [_ Hclosed].
    destruct (Hclosed lock Hlock) as (unlock & Hmatched).
    by apply (matched_lock_not_open _ _ _ HE Hmatched).
  Qed.

  Corollary run_has_no_unmatched_unlocks P actions s :
    run P (initial_state P) actions s ->
    (compute_rcu_matching s.(machine_core).(core_events)).(unmatched_unlocks) = [].
  Proof.
    intros Hrun. destruct (run_rcu_safety _ _ _ Hrun) as [Hsafe _].
    unfold compute_rcu_matching. induction (rcu_agents s.(machine_core).(core_events));
      cbn; first done.
    change ((compute_agent_match_state s.(machine_core).(core_events) a).(match_unmatched_unlocks)
      ++ unmatched_unlocks (combine_agent_matchings s.(machine_core).(core_events) l) = []).
    by rewrite Hsafe, IHl.
  Qed.

  Module MachineTests.
    Definition reader : stmt :=
      SSeq SRcuReadLock (SSeq SRcuReadLock (SSeq SRcuReadUnlock SRcuReadUnlock)).
    Definition synchronizer : stmt := SSeq SSynchronizeRcu (SLoad 0 LoadAcquire (EConst 0)).
    Definition late_reader : stmt := SSeq SRcuReadLock SRcuReadUnlock.
    Definition program : core_program :=
      CoreProgram {[0 := 0%Z]} {[0 := reader; 1 := synchronizer; 2 := late_reader]}.

    Definition prefix : list action := [
      Execute (CoreSilent 0); ReadLock 0;
      Execute (CoreSilent 0); Execute (CoreSilent 0); ReadLock 0;
      Execute (CoreSilent 1); BeginGp 1;
      Execute (CoreSilent 0); Execute (CoreSilent 0); ReadUnlock 0;
      Execute (CoreSilent 2); ReadLock 2
    ].
    Definition through_gp : list action := [Execute (CoreSilent 0); ReadUnlock 0; FinishGp 1].
    Definition suffix : list action := [
      Execute (CoreSilent 1); Execute (CoreObserve 1 0%Z);
      Execute (CoreSilent 2); ReadUnlock 2
    ].

    Local Ltac solve_core_step :=
      first [solve [eapply StepSequence; reflexivity]
        | solve [eapply StepSkipSequence; reflexivity]
        | solve [eapply StepLoad;
            solve [reflexivity | unfold location_initialized; eexists; reflexivity]]].

    Local Ltac solve_machine_step :=
      first
        [eapply StepCore; [reflexivity | done | reflexivity | solve_core_step]
        | eapply StepReadLock; [split; reflexivity | reflexivity]
        | eapply StepReadUnlock; [split; reflexivity | reflexivity | reflexivity]
        | eapply StepBeginGp; [split; reflexivity | reflexivity]
        | eapply StepFinishGp; [split; reflexivity | reflexivity |]] .

    Local Ltac normalize_machine :=
      lazymatch goal with
      | |- run ?P ?s ?actions ?final =>
          let reduced := (eval vm_compute in s) in
          change (run P reduced actions final)
      end.

    Example nested_snapshot_waiting :
      exists waiting finished final,
        run program (initial_state program) prefix waiting /\
        waiting.(pending_gp) !! 1 = Some [2; 1] /\
        open_readers waiting 0 = [1] /\
        In 1 (snapshot waiting) /\
        (forall next, ~ step program waiting (FinishGp 1) next) /\
        run program waiting through_gp finished /\
        finished.(pending_gp) !! 1 = None /\
        open_readers finished 2 = [4] /\
        finished.(gp_certificates) = [GpCertificate 6 [2; 1]] /\
        run program finished suffix final /\ complete final /\
        final.(machine_core).(core_threads) !! 1 =
          Some (ThreadState SSkip [] {[0 := RegValue 0%Z {[7]}]}).
    Proof.
      evar (waiting : state).
      assert (Hprefix : run program (initial_state program) prefix waiting).
      { unfold prefix.
        repeat (eapply RunCons; first solve_machine_step; normalize_machine).
        unfold waiting. constructor. }
      evar (finished : state).
      assert (Hgp : run program waiting through_gp finished).
      { unfold through_gp.
        eapply RunCons; first solve_machine_step.
        eapply RunCons; first solve_machine_step.
        eapply RunCons.
        + solve_machine_step. intros lock [<- | [<- | Hfalse]]; last done.
          * exists 3, 0. vm_compute. auto.
          * exists 5, 0. vm_compute. auto.
        + unfold finished. constructor. }
      evar (final : state).
      assert (Hsuffix : run program finished suffix final).
      { unfold suffix.
        repeat (eapply RunCons; first solve_machine_step; normalize_machine).
        unfold final. constructor. }
      exists waiting, finished, final. split_and!; try done.
      - vm_compute. auto.
      - eapply captured_reader_blocks_finish with (locks := [2; 1]) (lock := 1); try done.
        + by eapply run_allocation_wf.
        + by right; left.
        + vm_compute. auto.
      - unfold complete. split_and!; try done.
        intros agent thread Hlookup.
        change (({[0 := ThreadState SSkip [] ∅;
          1 := ThreadState SSkip [] {[0 := RegValue 0%Z {[7]}]};
          2 := ThreadState SSkip [] ∅]} : gmap agent_id thread_state) !! agent = Some thread)
          in Hlookup.
        apply lookup_insert_Some in Hlookup as [[<- <-] | [_ Hlookup]]; first done.
        repeat (apply lookup_insert_Some in Hlookup as [[<- <-] | [_ Hlookup]]; first done).
        apply lookup_singleton_Some in Hlookup as [<- <-]. done.
    Qed.

    Definition guard_program : core_program :=
      CoreProgram {[0 := 0%Z]}
        {[0 := SSynchronizeRcu; 1 := SRcuReadUnlock;
          2 := SXchg 0 RmwRelaxed (EConst 0) (EConst 1)]}.
    Definition guard_waiting : state := begin_gp (initial_state guard_program) 0.
    Definition guard_rmw : state :=
      with_core guard_waiting
        (add_rmw_events guard_waiting.(machine_core) 2
          (initial_thread (SXchg 0 RmwRelaxed (EConst 0) (EConst 1))) AccessOnce 0 0%Z 1%Z
          {[0 := RegValue 0%Z {[1]}]} ∅ ∅ ∅).
    Definition guard_finished : state :=
      finish_gp guard_rmw 0 (initial_thread SSynchronizeRcu) [].

    Example empty_snapshot_and_step_guards :
      run guard_program (initial_state guard_program)
        [BeginGp 0; Execute (CoreObserve 2 0%Z); FinishGp 0] guard_finished /\
      guard_rmw.(pending_gp) !! 0 = Some [] /\
      guard_finished.(machine_core).(core_rmw) = {[(1, 2)]} /\
      guard_finished.(gp_certificates) = [GpCertificate 3 []] /\
      (forall next, ~ step guard_program (initial_state guard_program) (FinishGp 0) next) /\
      (forall next, ~ step guard_program guard_waiting (Execute (CoreEmit 0)) next) /\
      (forall next, ~ step guard_program guard_waiting (BeginGp 0) next) /\
      (forall next, ~ step guard_program guard_waiting (ReadUnlock 1) next) /\
      (forall next, ~ step guard_program guard_waiting (Execute (CoreEmit 1)) next) /\
      ~ complete guard_finished.
    Proof.
      split_and!; try done.
      - eapply RunCons with (s2 := guard_waiting).
        { eapply StepBeginGp; [split; reflexivity | reflexivity]. }
        eapply RunCons with (s2 := guard_rmw).
        { eapply StepCore; [reflexivity | done | reflexivity |].
          eapply StepXchg with (dst := 0) (mode := RmwRelaxed)
            (result := RegValue 1%Z ∅) (address_sources := ∅);
            solve [reflexivity | unfold location_initialized; eexists; reflexivity]. }
        eapply RunCons; last constructor.
        eapply StepFinishGp; [split; reflexivity | reflexivity |]. intros lock Hfalse. done.
      - intros next Hstep. inversion Hstep; subst. discriminate H1.
      - intros next Hstep.
        pose proof (pending_agent_only_finishes _ _ _ _ 0 [] Hstep eq_refl eq_refl) as [Heq _].
        discriminate.
      - intros next Hstep.
        pose proof (pending_agent_only_finishes _ _ _ _ 0 [] Hstep eq_refl eq_refl) as [Heq _].
        discriminate.
      - intros next Hstep. inversion Hstep; subst.
        match goal with Hstack : open_readers _ _ = _ :: _ |- _ => discriminate Hstack end.
      - intros next Hstep. inversion Hstep; subst.
        match goal with Hlookup : core_threads _ !! _ = Some _ |- _ =>
          change (Some (initial_thread SRcuReadUnlock) = Some thread) in Hlookup;
          injection Hlookup as <-
        end. done.
      - intros [Hcore _].
        specialize (Hcore 1 (initial_thread SRcuReadUnlock) eq_refl).
        destruct Hcore as [Hstatement _]. discriminate.
    Qed.
  End MachineTests.

End LkmmMachine.
