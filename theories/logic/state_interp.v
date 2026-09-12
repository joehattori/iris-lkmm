From Stdlib Require Import List.
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
  Definition gp_identity (agent : agent_id) (index : event_index) : gp_id :=
    encode_nat (agent, index).

  Lemma gp_identity_inj agent index agent' index' :
    gp_identity agent index = gp_identity agent' index' ->
    agent = agent' /\ index = index'.
  Proof. unfold gp_identity. intros H. apply (inj encode_nat) in H. by simplify_eq. Qed.

  Definition pending_gp_at (s : LkmmMachine.state) (gid : gp_id)
      (captured : gset rscs_id) : Prop :=
    exists agent locks, s.(pending_gp) !! agent = Some locks /\
      gid = gp_identity agent (next_agent_index s.(machine_core) agent) /\
      captured = list_to_set locks.

  Definition completed_gp_at (s : LkmmMachine.state) (gid : gp_id)
      (captured : gset rscs_id) : Prop :=
    exists cert agent index, In cert s.(gp_certificates) /\
      lookup_event s.(machine_core).(core_events) cert.(gc_event) =
        Some (EAgent agent index (LBarrier BarrierSyncRcu)) /\
      gid = gp_identity agent index /\ captured = list_to_set cert.(gc_snapshot).

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

  Lemma initial_open_reader_map P : open_reader_map (initial_state P) = ∅.
  Proof.
    assert (snapshot (initial_state P) = nil) as Hsnapshot.
    { unfold snapshot. apply computed_agent_stacks_empty.
      - exact (proj1 (core_initial_allocation_wf P)).
      - intros agent. unfold computed_agent_stack.
        by rewrite initial_agent_matching. }
    unfold open_reader_map. by rewrite Hsnapshot.
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
    #[local] state_rcu_G :: rcuG Σ
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
