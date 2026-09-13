From Stdlib Require Import List Lia.
From stdpp Require Import gmap countable.
From iris.base_logic.lib Require Import ghost_map.
From iris.proofmode Require Import proofmode.
From iris_lkmm.lkmm Require Import rcu_matching.
From iris_lkmm.lang Require Import core_rcu.
From iris_lkmm.operational Require Import lkmm_machine lkmm_coupled rcu_builder.
From iris_lkmm.logic Require Import rcu_ghost lkmm_machine_ghost.

Module LkmmStateInterp.
  Import LkmmMachine LkmmCoupled RcuBuilder RcuGhost LkmmMachineGhost.
  Import RcuMatching LkmmCoreRcu.

  (** A waiting agent emits no events until GP finish. Its local event index
      identifies the GP before the global event ID is allocated. *)
  Definition gp_encoding (agent : agent_id) (index : event_index) : gp_id :=
    encode_nat (agent, index).

  Lemma gp_encoding_inj agent index agent' index' :
    gp_encoding agent index = gp_encoding agent' index' ->
    agent = agent' /\ index = index'.
  Proof. unfold gp_encoding. intros H. apply (inj encode_nat) in H. by simplify_eq. Qed.

  Definition pending_gp_at (s : LkmmMachine.state) (gid : gp_id) (captured : gset rscs_id) : Prop :=
    exists agent locks, s.(pending_gp) !! agent = Some locks /\
      gid = gp_encoding agent (next_agent_index s.(machine_core) agent) /\
      captured = list_to_set locks.

  Definition completed_gp_at (s : LkmmMachine.state) (gid : gp_id)
      (captured : gset rscs_id) : Prop :=
    exists cert agent index, In cert s.(gp_certificates) /\
      lookup_event s.(machine_core).(core_events) cert.(gc_event) =
        Some (EAgent agent index (LBarrier BarrierSyncRcu)) /\
      gid = gp_encoding agent index /\ captured = list_to_set cert.(gc_captured_readers).

  (** Both directions exclude missing and phantom protocol entries. Epochs
      count completed GPs; their allocation and evolution are proved separately. *)
  Definition rcu_state_matches (s : LkmmMachine.state)
      (gps : gmap gp_id gp_status) : Prop :=
    (forall gid captured, pending_gp_at s gid captured <->
      exists start, gps !! gid = Some (GpPending captured start)) /\
    (forall gid captured, completed_gp_at s gid captured <->
      exists start finish, gps !! gid = Some (GpDone captured start finish)) /\
    (forall gid status, gps !! gid = Some status ->
      match status with
      | GpPending _ start => start <= length s.(gp_certificates)
      | GpDone _ start finish => start < finish /\ finish <= length s.(gp_certificates)
      end).

  Lemma rcu_state_matches_execute P s a s' gps :
    LkmmMachine.step P s (Execute a) s' -> core_allocation_wf s.(machine_core) ->
    rcu_state_matches s gps -> rcu_state_matches s' gps.
  Proof.
    intros Hstep Hwf Hmatches.
    inversion Hstep as [m core' action thread Hthread Hordinary Hready Hcore | | | |]; subst.
    change (s.(pending_gp) !! core_action_agent a = None) in Hready.
    assert (forall gid captured,
      pending_gp_at (with_core s core') gid captured <-> pending_gp_at s gid captured)
      as Hpending.
    { intros gid captured. unfold pending_gp_at. cbn.
      split; intros (agent & locks & Hlookup & Hgid & Hcaptured);
        assert (core_action_agent a <> agent) as Hother by (intros <-; congruence);
        pose proof (core_step_other_index _ _ _ _ _ Hcore Hother) as Hindex;
        exists agent, locks.
      all: split; first done; split; last done.
      - by rewrite Hindex in Hgid.
      - by rewrite Hindex. }
    assert (forall gid captured,
      completed_gp_at (with_core s core') gid captured <-> completed_gp_at s gid captured)
      as Hcompleted.
    { intros gid captured. unfold completed_gp_at. cbn.
      split; intros (cert & agent & index & Hcert & Hlookup & Hgid & Hcaptured);
        exists cert, agent, index.
      all: split; first done; split; last done.
      all: by apply (execute_preserves_gp_events _ _ _ _ _ _ _ Hstep Hwf). }
    unfold rcu_state_matches. setoid_rewrite Hpending. setoid_rewrite Hcompleted.
    done.
  Qed.

  Lemma initial_open_reader_map P : open_reader_map (initial_state P) = ∅.
  Proof.
    assert (all_open_readers (initial_state P) = nil) as Hreaders.
    { unfold all_open_readers. apply computed_agent_stacks_empty.
      - exact (proj1 (core_initial_allocation_wf P)).
      - intros agent. unfold computed_agent_stack.
        by rewrite initial_agent_matching. }
    unfold open_reader_map. by rewrite Hreaders.
  Qed.

  Lemma rcu_state_matches_emit_rcu s agent thread kind gps :
    kind <> BarrierSyncRcu ->
    core_allocation_wf s.(machine_core) -> s.(pending_gp) !! agent = None ->
    rcu_state_matches s gps ->
    rcu_state_matches (with_core s (emit_rcu s agent thread kind)) gps.
  Proof.
    intros Hkind Hwf Hready Hmatches.
    assert (forall gid captured,
      pending_gp_at (with_core s (emit_rcu s agent thread kind)) gid captured <->
      pending_gp_at s gid captured) as Hpending.
    { intros gid captured. unfold pending_gp_at. cbn.
      split; intros (owner & locks & Hlookup & Hgid & Hcaptured);
        assert (agent <> owner) as Hother by (intros ->; congruence);
        exists owner, locks.
      all: split; first done; split; last done.
      - unfold next_agent_index in Hgid. cbn in Hgid.
        by rewrite lookup_insert_ne in Hgid.
      - unfold next_agent_index. cbn. by rewrite lookup_insert_ne. }
    assert (forall eid owner index,
      lookup_event (emit_rcu s agent thread kind).(core_events) eid =
        Some (EAgent owner index (LBarrier BarrierSyncRcu)) <->
      lookup_event s.(machine_core).(core_events) eid =
        Some (EAgent owner index (LBarrier BarrierSyncRcu))) as Hgp.
    { intros eid owner index. cbn. unfold lookup_event. rewrite lookup_insert_Some.
      pose proof (core_next_id_fresh _ Hwf) as Hfresh. unfold lookup_event in Hfresh.
      naive_solver. }
    unfold rcu_state_matches. setoid_rewrite Hpending.
    unfold completed_gp_at. cbn. setoid_rewrite Hgp. done.
  Qed.

  Lemma rcu_state_matches_next_gp_fresh s gps agent :
    core_allocation_wf s.(machine_core) -> s.(pending_gp) !! agent = None ->
    rcu_state_matches s gps ->
    gps !! gp_encoding agent (next_agent_index s.(machine_core) agent) = None.
  Proof.
    intros (_ & _ & Hindices) Hready (Hpending & Hcompleted & _).
    apply eq_None_not_Some. intros [[captured start | captured start finish] Hlookup].
    - destruct (proj2 (Hpending _ captured) (ex_intro _ start Hlookup))
        as (owner & locks & Hlocks & Hgid & _).
      apply gp_encoding_inj in Hgid as [<- _]. congruence.
    - destruct (proj2 (Hcompleted _ captured) (ex_intro _ start (ex_intro _ finish Hlookup)))
        as (cert & owner & index & _ & Hevent & Hgid & _).
      apply gp_encoding_inj in Hgid as [<- <-].
      pose proof (Hindices _ _ _ _ Hevent). lia.
  Qed.

  Lemma rcu_state_matches_begin_gp s agent gps :
    core_allocation_wf s.(machine_core) -> s.(pending_gp) !! agent = None ->
    rcu_state_matches s gps ->
    rcu_state_matches (begin_gp s agent)
      (<[gp_encoding agent (next_agent_index s.(machine_core) agent) :=
        GpPending (list_to_set (all_open_readers s)) (length s.(gp_certificates))]> gps).
  Proof.
    intros Hwf Hready Hmatches.
    pose proof (rcu_state_matches_next_gp_fresh _ _ _ Hwf Hready Hmatches) as Hfresh.
    destruct Hmatches as (Hpending & Hcompleted & Hepochs).
    assert (forall gid captured, pending_gp_at (begin_gp s agent) gid captured <->
      (gid = gp_encoding agent (next_agent_index s.(machine_core) agent) /\
        captured = list_to_set (all_open_readers s)) \/ pending_gp_at s gid captured) as Hpending'.
    { intros gid captured. unfold pending_gp_at. cbn. split.
      - intros (owner & locks & Hlookup & Hgid & Hcaptured).
        apply lookup_insert_Some in Hlookup as [[<- <-] | [_ Hlookup]].
        + by left.
        + right. by exists owner, locks.
      - intros [[-> ->] | (owner & locks & Hlookup & Hgid & Hcaptured)].
        + exists agent, (all_open_readers s). split; first apply lookup_insert_eq. done.
        + exists owner, locks. split; last done.
          rewrite lookup_insert_ne; first done. intros ->. congruence. }
    split.
    - intros gid captured. rewrite Hpending' Hpending.
      setoid_rewrite lookup_insert_Some.
      clear Hpending' Hpending Hcompleted Hepochs Hwf Hready. naive_solver.
    - split.
      + intros gid captured.
        change (completed_gp_at (begin_gp s agent) gid captured)
          with (completed_gp_at s gid captured).
        rewrite Hcompleted. setoid_rewrite lookup_insert_Some.
        clear Hpending' Hpending Hcompleted Hepochs Hwf Hready. naive_solver.
      + intros gid status Hlookup. apply lookup_insert_Some in Hlookup as [[_ <-] | [_ Hlookup]].
        * cbn. lia.
        * by apply (Hepochs gid status).
  Qed.

  Local Lemma pending_gp_at_finish_gp s agent thread locks gid captured :
    pending_gp_at (finish_gp s agent thread locks) gid captured <->
    gp_encoding agent (next_agent_index s.(machine_core) agent) <> gid /\
      pending_gp_at s gid captured.
  Proof.
    assert (forall owner, agent <> owner ->
      next_agent_index (emit_rcu s agent thread BarrierSyncRcu) owner =
      next_agent_index s.(machine_core) owner) as Hindex.
    { intros owner Hother. unfold next_agent_index, emit_rcu. cbn.
      by rewrite lookup_insert_ne. }
    unfold pending_gp_at, finish_gp. cbn -[emit_rcu next_agent_index gp_encoding]. split.
    - intros (owner & saved & Hlookup & Hgid & Hcaptured).
      apply lookup_delete_Some in Hlookup as [Hother Hlookup].
      rewrite Hindex in Hgid; last done. split.
      + intros Heq. rewrite Hgid in Heq. apply gp_encoding_inj in Heq. naive_solver.
      + by exists owner, saved.
    - intros (Hneq & owner & saved & Hlookup & Hgid & Hcaptured).
      assert (agent <> owner) as Hother by (intros ->; congruence).
      exists owner, saved. split.
      + apply lookup_delete_Some. done.
      + rewrite Hindex; done.
  Qed.

  Local Lemma completed_gp_at_finish_gp s agent thread locks gid captured :
    core_allocation_wf s.(machine_core) -> certificate_events_allocated s ->
    (completed_gp_at (finish_gp s agent thread locks) gid captured <->
      (gid = gp_encoding agent (next_agent_index s.(machine_core) agent) /\
        captured = list_to_set locks) \/ completed_gp_at s gid captured).
  Proof.
    intros Hwf Hcerts.
    assert (forall cert, In cert s.(gp_certificates) ->
      lookup_event (emit_rcu s agent thread BarrierSyncRcu).(core_events) cert.(gc_event) =
      lookup_event s.(machine_core).(core_events) cert.(gc_event)) as Hlookup_old.
    { intros cert Hin. destruct (Hcerts cert Hin) as (owner & index & Hlookup).
      cbn. unfold lookup_event. rewrite lookup_insert_ne; first done.
      intros Heq. rewrite -Heq (core_next_id_fresh _ Hwf) in Hlookup. discriminate. }
    unfold completed_gp_at, finish_gp. cbn -[emit_rcu next_agent_index gp_encoding]. split.
    - intros (cert & owner & index & [<- | Hin] & Hlookup & Hgid & Hcaptured).
      + change (<[s.(machine_core).(core_next_id) :=
          EAgent agent (next_agent_index s.(machine_core) agent) (LBarrier BarrierSyncRcu)]>
          s.(machine_core).(core_events) !! s.(machine_core).(core_next_id) =
          Some (EAgent owner index (LBarrier BarrierSyncRcu))) in Hlookup.
        rewrite lookup_insert_eq in Hlookup. injection Hlookup as <- <-. by left.
      + right. exists cert, owner, index. rewrite Hlookup_old in Hlookup; done.
    - intros [[-> ->] | (cert & owner & index & Hin & Hlookup & Hgid & Hcaptured)].
      + exists (GpCertificate s.(machine_core).(core_next_id) locks), agent,
          (next_agent_index s.(machine_core) agent).
        split; first by left. split; first apply lookup_insert_eq. done.
      + exists cert, owner, index. split; first by right.
        rewrite Hlookup_old; done.
  Qed.

  Lemma rcu_state_matches_finish_gp s agent thread locks gps start :
    core_allocation_wf s.(machine_core) -> certificate_events_allocated s ->
    rcu_state_matches s gps ->
    gps !! gp_encoding agent (next_agent_index s.(machine_core) agent) =
      Some (GpPending (list_to_set locks) start) ->
    rcu_state_matches (finish_gp s agent thread locks)
      (<[gp_encoding agent (next_agent_index s.(machine_core) agent) :=
        GpDone (list_to_set locks) start (S (length s.(gp_certificates)))]> gps).
  Proof.
    intros Hwf Hcerts (Hpending & Hcompleted & Hepochs) Hregistered.
    pose proof (Hepochs _ _ Hregistered) as Hstart. split.
    - intros gid captured. rewrite pending_gp_at_finish_gp Hpending.
      setoid_rewrite lookup_insert_Some.
      clear Hpending Hcompleted Hepochs Hwf Hcerts Hstart. naive_solver.
    - split.
      + intros gid captured. rewrite (completed_gp_at_finish_gp _ _ _ _ _ _ Hwf Hcerts) Hcompleted.
        setoid_rewrite lookup_insert_Some.
        clear Hpending Hcompleted Hepochs Hwf Hcerts Hstart. naive_solver.
      + intros gid status Hlookup. apply lookup_insert_Some in Hlookup as [[_ <-] | [_ Hlookup]].
        * cbn in Hstart |- *. lia.
        * specialize (Hepochs _ _ Hlookup). destruct status; cbn in Hepochs |- *; lia.
  Qed.

  Lemma initial_rcu_state_matches P : rcu_state_matches (initial_state P) ∅.
  Proof.
    unfold rcu_state_matches, pending_gp_at, completed_gp_at.
    simpl. setoid_rewrite lookup_empty. naive_solver.
  Qed.

  Definition stateΣ : gFunctors :=
    #[ghost_mapΣ agent_id thread_state; ghost_mapΣ event_id event; rcuΣ].

  Class stateG Σ := StateG {
    #[local] state_threads_G :: ghost_mapG Σ agent_id thread_state;
    #[local] state_events_G :: ghost_mapG Σ event_id event;
    #[global] state_rcu_G :: rcuG Σ
  }.

  Global Instance subG_stateΣ Σ : subG stateΣ Σ -> stateG Σ.
  Proof. solve_inG. Qed.

  Record state_names := StateNames {
    threads_name : gname;
    events_name : gname;
    rcu_name : rcu_names
  }.

  Section resources.
    Context `{!stateG Σ}.

    Definition thread_token (γ : state_names) (agent : agent_id)
        (thread : thread_state) : iProp Σ :=
      agent ↪[γ.(threads_name)] thread.

    (** Records an emitted event, without granting ownership of its location. *)
    Definition event_fact (γ : state_names) (eid : event_id) (ev : event) : iProp Σ :=
      eid ↪[γ.(events_name)]□ ev.

    Global Instance event_fact_persistent γ eid ev : Persistent (event_fact γ eid ev).
    Proof. apply _. Qed.

    (** Interpret the current coupled state. The final graph and execution
        witnesses stay in [coupled_position], outside this resource assertion.
        Thread, reader, and pending-GP tokens are held separately by clients. *)
    Definition state_interp (γ : state_names) (s : coupled_state) : iProp Σ :=
      ⌜generated_prefix s.(coupled_machine) s.(coupled_builder).(bs_raw)⌝ ∗
      ghost_map_auth γ.(threads_name) 1 s.(coupled_machine).(machine_core).(core_threads) ∗
      ghost_map_auth γ.(events_name) 1 s.(coupled_machine).(machine_core).(core_events) ∗
      ∃ gps, ⌜rcu_state_matches s.(coupled_machine) gps⌝ ∗
        rcu_auth γ.(rcu_name) (open_reader_map s.(coupled_machine)) gps
          (length s.(coupled_machine).(gp_certificates)).

    (** Allocation uses only the initial program state, with no final-graph
        or completion premise. Thread tokens can be distributed to agents. *)
    Lemma state_interp_alloc P :
      ⊢ |==> ∃ γ, state_interp γ (initial_coupled P) ∗
        ([∗ map] agent ↦ body ∈ P.(program_agents),
          thread_token γ agent (initial_thread body)) ∗
        ([∗ map] eid ↦ ev ∈ core_initial_events P, event_fact γ eid ev).
    Proof.
      iMod (ghost_map_alloc (initial_thread <$> P.(program_agents)))
        as (γthreads) "[Hthreads Htokens]".
      iMod (ghost_map_alloc_empty (K := event_id) (V := event)) as (γevents) "Hevents".
      iMod (ghost_map_insert_persist_big (core_initial_events P) with "Hevents")
        as "[Hevents #Hfacts]"; first apply map_disjoint_empty_r.
      iEval (rewrite right_id_L) in "Hevents".
      iMod rcu_ghost_alloc as (γrcu) "Hrcu".
      iModIntro. iExists (StateNames γthreads γevents γrcu).
      iSplitL "Hthreads Hevents Hrcu".
      - rewrite /state_interp /=. iSplit.
        { iPureIntro. apply (coupled_run_generated_prefix P nil (initial_coupled P)).
          constructor. }
        iFrame "Hthreads Hevents". iExists ∅. iSplit.
        { iPureIntro. apply initial_rcu_state_matches. }
        by rewrite initial_open_reader_map.
      - rewrite /thread_token /event_fact /= big_sepM_fmap. iFrame "Htokens Hfacts".
    Qed.

    Lemma state_interp_thread γ s agent thread :
      state_interp γ s -∗ thread_token γ agent thread -∗
      ⌜s.(coupled_machine).(machine_core).(core_threads) !! agent = Some thread⌝.
    Proof.
      iIntros "(_ & Hthreads & _) Hthread".
      iApply (ghost_map_lookup with "Hthreads Hthread").
    Qed.

    Lemma state_interp_silent_step P γ s agent s' thread thread' :
      coupled_step P s (CoupledMachineAction (Execute (CoreSilent agent))) s' ->
      s'.(coupled_machine).(machine_core).(core_threads) !! agent = Some thread' ->
      state_interp γ s ∗ thread_token γ agent thread ==∗
      state_interp γ s' ∗ thread_token γ agent thread'.
    Proof.
      intros Hstep Hlookup.
      destruct (coupled_silent_step_update_thread _ _ _ _ Hstep) as (next & ->).
      change (<[agent := next]> s.(coupled_machine).(machine_core).(core_threads) !! agent =
        Some thread') in Hlookup.
      rewrite lookup_insert_eq in Hlookup. injection Hlookup as ->.
      iIntros "((%Hprefix & Hthreads & Hevents & Hrcu) & Hthread)".
      iDestruct "Hrcu" as (gps) "[%Hmatches Hrcu]".
      iMod (ghost_map_update thread' with "Hthreads Hthread") as "[Hthreads Hthread]".
      iModIntro. rewrite /state_interp /thread_token /=. iFrame "Hthread".
      iSplit; first by iPureIntro.
      iFrame "Hthreads Hevents". iExists gps. iFrame "Hrcu". by iPureIntro.
    Qed.

    (** Builder steps supply the new generated-prefix condition and leave
        the machine, hence every ghost resource, unchanged. *)
    Lemma state_interp_builder_step P γ s s' :
      coupled_step P s CoupledBuilderAction s' ->
      state_interp γ s ⊢ state_interp γ s'.
    Proof.
      intros Hstep. inversion Hstep; subst.
      iIntros "(_ & Hthreads & Hevents & Hrcu)".
      rewrite /state_interp /=. iFrame. by iPureIntro.
    Qed.

    (** Ordinary execution updates its thread and allocates facts for exactly
        the new events (two for a successful RMW). Allocation well-formedness
        comes from the execution prefix; no final-graph premise is needed. *)
    Lemma state_interp_execute P γ s a s' thread thread' :
      coupled_step P s (CoupledMachineAction (Execute a)) s' ->
      core_allocation_wf s.(coupled_machine).(machine_core) ->
      s'.(coupled_machine).(machine_core).(core_threads) !! action_agent a = Some thread' ->
      state_interp γ s ∗ thread_token γ (action_agent a) thread ==∗
      state_interp γ s' ∗ thread_token γ (action_agent a) thread' ∗
        ([∗ map] eid ↦ ev ∈ s'.(coupled_machine).(machine_core).(core_events) ∖
            s.(coupled_machine).(machine_core).(core_events), event_fact γ eid ev).
    Proof.
      intros Hstep Hwf Hlookup.
      pose proof (step_preserves_generated_prefix _ _ _ _ Hstep Hwf) as Hprefix'.
      inversion Hstep as [m m' b action Hmachine |]; subst.
      pose proof (execute_preserves_rcu_matching _ _ _ _ Hmachine Hwf) as Hmatching.
      inversion Hmachine as [m0 core' action thread0 Hthread Hordinary Hready Hcore | | | |]; subst.
      assert (core'.(core_threads) = <[action_agent a := thread']> m.(machine_core).(core_threads))
        as Hthreads'.
      { assert (exists next, core'.(core_threads) =
          <[action_agent a := next]> m.(machine_core).(core_threads)) as [next Heq].
        { destruct Hcore; eexists; reflexivity. }
        cbn in Hlookup. rewrite Heq lookup_insert_eq in Hlookup. by simplify_eq. }
      assert (m.(machine_core).(core_events) ⊆ core'.(core_events)) as Hevents.
      { apply map_subseteq_spec. by eapply core_step_events_included. }
      iIntros "((%Hprefix & Hthreads & Hevents & Hrcu) & Hthread)".
      iDestruct "Hrcu" as (gps) "[%Hmatches Hrcu]".
      pose proof (rcu_state_matches_execute _ _ _ _ gps Hmachine Hwf Hmatches) as Hmatches'.
      iMod (ghost_map_update thread' with "Hthreads Hthread") as "[Hthreads Hthread]".
      iMod (ghost_map_insert_persist_big (core'.(core_events) ∖ m.(machine_core).(core_events))
        with "Hevents") as "[Hevents #Hfacts]".
      { apply map_disjoint_difference_l1. done. }
      iEval (rewrite map_union_comm; last by apply map_disjoint_difference_l1) in "Hevents".
      iEval (rewrite map_difference_union //) in "Hevents".
      iModIntro. rewrite /state_interp /thread_token /event_fact /=.
      iFrame "Hthread Hfacts". iSplit; first by iPureIntro; apply Hprefix'.
      rewrite Hthreads'. iFrame "Hthreads Hevents".
      iExists gps. iSplit; first by iPureIntro; apply Hmatches'.
      by rewrite /open_reader_map /all_open_readers /= Hmatching.
    Qed.

    Lemma state_interp_read_lock P γ s agent s' thread :
      coupled_step P s (CoupledMachineAction (ReadLock agent)) s' ->
      core_allocation_wf s.(coupled_machine).(machine_core) ->
      state_interp γ s ∗ thread_token γ agent thread ==∗
      state_interp γ s' ∗
        thread_token γ agent (emitted_thread thread thread.(thread_registers)) ∗
        event_fact γ s.(coupled_machine).(machine_core).(core_next_id)
          (EAgent agent (next_agent_index s.(coupled_machine).(machine_core) agent)
            (LBarrier BarrierRcuLock)) ∗
        reader_token γ.(rcu_name) s.(coupled_machine).(machine_core).(core_next_id).
    Proof.
      intros Hstep Hwf.
      pose proof (step_preserves_generated_prefix _ _ _ _ Hstep Hwf) as Hprefix'.
      inversion Hstep as [m m' b action Hmachine |]; subst.
      inversion Hmachine as [|m0 agent0 actual [Hlookup Hstmt] Hready| | |]; subst.
      iIntros "((%Hprefix & Hthreads & Hevents & Hrcu) & Hthread)".
      iDestruct (ghost_map_lookup with "Hthreads Hthread") as %Howned.
      cbn in Howned.
      assert (thread = actual) as -> by congruence.
      iDestruct "Hrcu" as (gps) "[%Hmatches Hrcu]".
      iMod (ghost_map_update (emitted_thread actual actual.(thread_registers))
        with "Hthreads Hthread") as "[Hthreads Hthread]".
      iMod (ghost_map_insert_persist m.(machine_core).(core_next_id)
        (EAgent agent (next_agent_index m.(machine_core) agent) (LBarrier BarrierRcuLock))
        with "Hevents") as "[Hevents #Hlock]"; first by apply core_next_id_fresh.
      iMod (rcu_reader_enter _ _ _ _ m.(machine_core).(core_next_id) with "Hrcu")
        as "[Hrcu Hreader]"; first by apply open_reader_map_next_fresh.
      iModIntro. rewrite /state_interp /thread_token /event_fact /=.
      iFrame "Hthread Hlock Hreader". iSplit; first by iPureIntro; apply Hprefix'.
      iFrame "Hthreads Hevents". iExists gps. iSplit.
      { iPureIntro. apply rcu_state_matches_emit_rcu; done. }
      by rewrite open_reader_map_read_lock.
    Qed.

    (** Unlock consumes the innermost reader token. Captured GP snapshots
        retain the lock's identity after it leaves the open-reader map. *)
    Lemma state_interp_read_unlock P γ s agent s' thread lock rest :
      coupled_step P s (CoupledMachineAction (ReadUnlock agent)) s' ->
      core_allocation_wf s.(coupled_machine).(machine_core) ->
      open_readers s.(coupled_machine) agent = lock :: rest ->
      state_interp γ s ∗ thread_token γ agent thread ∗ reader_token γ.(rcu_name) lock ==∗
      state_interp γ s' ∗
        thread_token γ agent (emitted_thread thread thread.(thread_registers)) ∗
        event_fact γ s.(coupled_machine).(machine_core).(core_next_id)
          (EAgent agent (next_agent_index s.(coupled_machine).(machine_core) agent)
            (LBarrier BarrierRcuUnlock)).
    Proof.
      intros Hstep Hwf Hstack.
      pose proof (step_preserves_generated_prefix _ _ _ _ Hstep Hwf) as Hprefix'.
      inversion Hstep as [m m' b action Hmachine |]; subst.
      inversion Hmachine as [| |m0 agent0 actual lock0 rest0 [Hlookup Hstmt] Hready Hstack0| |]; subst.
      iIntros "((%Hprefix & Hthreads & Hevents & Hrcu) & Hthread & Hreader)".
      iDestruct (ghost_map_lookup with "Hthreads Hthread") as %Howned.
      cbn in Howned.
      assert (thread = actual) as -> by congruence.
      iDestruct "Hrcu" as (gps) "[%Hmatches Hrcu]".
      iMod (ghost_map_update (emitted_thread actual actual.(thread_registers))
        with "Hthreads Hthread") as "[Hthreads Hthread]".
      iMod (ghost_map_insert_persist m.(machine_core).(core_next_id)
        (EAgent agent (next_agent_index m.(machine_core) agent) (LBarrier BarrierRcuUnlock))
        with "Hevents") as "[Hevents #Hunlock]"; first by apply core_next_id_fresh.
      iMod (rcu_reader_exit with "[$Hrcu $Hreader]") as "Hrcu".
      iModIntro. rewrite /state_interp /thread_token /event_fact /=.
      iFrame "Hthread Hunlock". iSplit; first by iPureIntro; apply Hprefix'.
      iFrame "Hthreads Hevents". iExists gps. iSplit.
      { iPureIntro. apply rcu_state_matches_emit_rcu; done. }
      by rewrite (open_reader_map_read_unlock _ _ _ lock rest Hwf Hstack).
    Qed.

    Lemma state_interp_begin_gp P γ s agent s' thread :
      coupled_step P s (CoupledMachineAction (BeginGp agent)) s' ->
      core_allocation_wf s.(coupled_machine).(machine_core) ->
      state_interp γ s ∗ thread_token γ agent thread ==∗
      state_interp γ s' ∗ thread_token γ agent thread ∗
        gp_pending γ.(rcu_name)
          (gp_encoding agent (next_agent_index s.(coupled_machine).(machine_core) agent))
          (list_to_set (all_open_readers s.(coupled_machine)))
          (length s.(coupled_machine).(gp_certificates)).
    Proof.
      intros Hstep Hwf.
      inversion Hstep as [m m' b action Hmachine |]; subst.
      inversion Hmachine as [| | |m0 agent0 actual Hcurrent Hready|]; subst.
      iIntros "((%Hprefix & Hthreads & Hevents & Hrcu) & Hthread)".
      iDestruct "Hrcu" as (gps) "[%Hmatches Hrcu]".
      iMod (rcu_gp_begin _ _ _ _ (gp_encoding agent (next_agent_index m.(machine_core) agent))
        with "Hrcu") as "[Hrcu Hpending]".  { by apply rcu_state_matches_next_gp_fresh. }
      iEval (rewrite dom_open_reader_map) in "Hrcu Hpending".
      iModIntro. rewrite /state_interp /=. iFrame "Hthread Hpending".
      iSplit; first by iPureIntro.
      iFrame "Hthreads Hevents". iExists _. iFrame "Hrcu".
      iPureIntro. by apply rcu_state_matches_begin_gp.
    Qed.

    (** The pending token fixes the captured readers and start epoch. Both
        allocation premises follow from the machine execution prefix. *)
    Lemma state_interp_finish_gp P γ s agent s' thread captured start :
      coupled_step P s (CoupledMachineAction (FinishGp agent)) s' ->
      core_allocation_wf s.(coupled_machine).(machine_core) ->
      certificate_events_allocated s.(coupled_machine) ->
      state_interp γ s ∗ thread_token γ agent thread ∗
        gp_pending γ.(rcu_name)
          (gp_encoding agent (next_agent_index s.(coupled_machine).(machine_core) agent))
          captured start ==∗
      state_interp γ s' ∗
        thread_token γ agent (emitted_thread thread thread.(thread_registers)) ∗
        event_fact γ s.(coupled_machine).(machine_core).(core_next_id)
          (EAgent agent (next_agent_index s.(coupled_machine).(machine_core) agent)
            (LBarrier BarrierSyncRcu)) ∗
        gp_done γ.(rcu_name)
          (gp_encoding agent (next_agent_index s.(coupled_machine).(machine_core) agent))
          captured start (S (length s.(coupled_machine).(gp_certificates))).
    Proof.
      intros Hstep Hwf Hcerts.
      pose proof (step_preserves_generated_prefix _ _ _ _ Hstep Hwf) as Hprefix'.
      inversion Hstep as [m m' b action Hmachine |]; subst.
      inversion Hmachine as [| | | |m0 agent0 actual locks [Hlookup Hstmt] Hwaiting Hclosed]; subst.
      iIntros "((%Hprefix & Hthreads & Hevents & Hrcu) & Hthread & Hpending)".
      iDestruct (ghost_map_lookup with "Hthreads Hthread") as %Howned.
      cbn in Howned. assert (thread = actual) as -> by congruence.
      iDestruct "Hrcu" as (gps) "(%Hmatches & Hopen & Hgps & Hepoch)".
      iDestruct (ghost_map_lookup with "Hgps Hpending") as %Hregistered.
      destruct (proj2 (proj1 Hmatches _ captured) (ex_intro _ start Hregistered))
        as (owner & saved & Hsaved & Hgid & Hcaptured).
      apply gp_encoding_inj in Hgid as [<- _].
      cbn in Hsaved. assert (saved = locks) as -> by congruence. subst captured.
      iMod (ghost_map_update (emitted_thread actual actual.(thread_registers))
        with "Hthreads Hthread") as "[Hthreads Hthread]".
      iMod (ghost_map_insert_persist m.(machine_core).(core_next_id)
        (EAgent agent (next_agent_index m.(machine_core) agent) (LBarrier BarrierSyncRcu))
        with "Hevents") as "[Hevents #Hsync]"; first by apply core_next_id_fresh.
      iMod (rcu_gp_finish with "[$Hopen $Hgps $Hepoch $Hpending]") as "[Hrcu #Hdone]".
      { apply all_closed_open_reader_map_disjoint; [exact (proj1 Hwf) | done]. }
      iModIntro. rewrite /state_interp /thread_token /event_fact /=.
      iFrame "Hthread Hsync Hdone". iSplit; first by iPureIntro; apply Hprefix'.
      iFrame "Hthreads Hevents". iExists _. iSplit.
      { iPureIntro. by apply rcu_state_matches_finish_gp. }
      by rewrite open_reader_map_finish_gp.
    Qed.

    Lemma state_interp_event γ s eid ev :
      state_interp γ s -∗ event_fact γ eid ev -∗
      ⌜lookup_event s.(coupled_machine).(machine_core).(core_events) eid = Some ev⌝.
    Proof.
      iIntros "(_ & _ & Hevents & _) Hevent".
      iApply (ghost_map_lookup with "Hevents Hevent").
    Qed.

    Lemma state_interp_reader γ s rid :
      state_interp γ s -∗ reader_token γ.(rcu_name) rid -∗
      ⌜open_reader_map s.(coupled_machine) !! rid = Some tt⌝.
    Proof.
      iIntros "(_ & _ & _ & Hrcu) Hreader".
      iDestruct "Hrcu" as (gps) "(_ & Hopen & _)".
      iApply (ghost_map_lookup with "Hopen Hreader").
    Qed.

    Lemma state_interp_pending γ s gid captured start :
      state_interp γ s -∗ gp_pending γ.(rcu_name) gid captured start -∗
      ⌜pending_gp_at s.(coupled_machine) gid captured⌝.
    Proof.
      iIntros "(_ & _ & _ & Hrcu) Hpending".
      iDestruct "Hrcu" as (gps) "(%Hmatch & _ & Hgps & _)".
      iDestruct (ghost_map_lookup with "Hgps Hpending") as %Hlookup.
      iPureIntro. apply (proj2 (proj1 Hmatch gid captured)). by exists start.
    Qed.

    Lemma state_interp_done γ s gid captured start finish :
      state_interp γ s -∗ gp_done γ.(rcu_name) gid captured start finish -∗
      ⌜completed_gp_at s.(coupled_machine) gid captured⌝.
    Proof.
      iIntros "(_ & _ & _ & Hrcu) [Hdone _]".
      iDestruct "Hrcu" as (gps) "(%Hmatch & _ & Hgps & _)".
      iDestruct (ghost_map_lookup with "Hgps Hdone") as %Hlookup.
      iPureIntro. apply (proj2 (proj1 (proj2 Hmatch) gid captured)). by exists start, finish.
    Qed.
  End resources.
End LkmmStateInterp.
