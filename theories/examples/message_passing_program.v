From Stdlib Require Import List Lia Relations.Relation_Operators.
From stdpp Require Import gmap fin_maps tactics.
From iris_lkmm.lkmm Require Import memory_relations rcu_graph.
From iris_lkmm.lang Require Import core_agent_replay core_renaming.
Import ListNotations.

(** The four message-passing variants. Locations 0 and 1
    represent data and flag; consumer registers 0 and 1 hold their reads.
    The consumer always performs both loads: no control dependency is added. *)
Module MessagePassingProgram.
  Import LkmmCoreRenaming LkmmMemoryRelations RcuGraph.

  Definition producer sm :=
    SSeq (SStore StoreOnce (EConst 0) (EConst 1))
      (SStore sm (EConst 1) (EConst 1)).
  Definition consumer lm :=
    SSeq (SLoad 0 lm (EConst 1)) (SLoad 1 LoadOnce (EConst 0)).
  Definition program sm lm :=
    CoreProgram {[0 := 0%Z; 1 := 0%Z]} {[0 := producer sm; 1 := consumer lm]}.

  Definition data_write := EAgent 0 0 (LMemory AccessWrite AccessOnce NotRmw 0 1%Z).
  Definition flag_write sm :=
    EAgent 0 1 (LMemory AccessWrite (store_access_mode sm) NotRmw 1 1%Z).
  Definition flag_read lm v :=
    EAgent 1 0 (LMemory AccessRead (load_access_mode lm) NotRmw 1 v).
  Definition data_read v := EAgent 1 1 (LMemory AccessRead AccessOnce NotRmw 0 v).
  Definition sample_events sm lm : event_structure :=
    {[0 := EInitWrite 0 0%Z; 1 := EInitWrite 1 0%Z;
      2 := data_write; 3 := flag_write sm; 4 := flag_read lm 1%Z; 5 := data_read 0%Z]}.
  Definition sample_rf : edge_set := {[(3,4); (0,5)]}.
  Definition sample_co : edge_set := {[(0,2); (1,3)]}.
  Definition candidate sm lm := CoreCandidate (sample_events sm lm)
    sample_rf sample_co ∅ ∅ ∅ ∅.

  (** This outcome uses agent-local instruction positions, never allocation
      IDs or a chosen schedule. *)
  Definition bad_outcome lm (C : core_candidate) : Prop :=
    exists c d,
      lookup_event C.(candidate_events) c = Some (flag_read lm 1%Z) /\
      lookup_event C.(candidate_events) d = Some (data_read 0%Z).

  Lemma sample_lookup sm lm i ev : lookup_event (sample_events sm lm) i = Some ev ->
    (i = 0 /\ ev = EInitWrite 0 0%Z) \/ (i = 1 /\ ev = EInitWrite 1 0%Z) \/
    (i = 2 /\ ev = data_write) \/ (i = 3 /\ ev = flag_write sm) \/
    (i = 4 /\ ev = flag_read lm 1%Z) \/ (i = 5 /\ ev = data_read 0%Z).
  Proof.
    unfold lookup_event, sample_events.
    intros H.
    repeat (apply lookup_insert_Some in H as [[? ?]|[? H]]);
      try apply lookup_singleton_Some in H; naive_solver.
  Qed.

  Ltac lookup_cases :=
    repeat match goal with
    | H : lookup_event (sample_events _ _) _ = Some _ |- _ =>
        apply sample_lookup in H;
        destruct H as [[-> H]|[[-> H]|[[-> H]|[[-> H]|[[-> H]|[-> H]]]]]];
        unfold data_write, flag_write, flag_read, data_read in H; simplify_eq
    end.

  Lemma sample_complete_run sm lm : exists actions state,
    complete_core_run (program sm lm) actions state /\
    state.(core_events) = sample_events sm lm /\
    state.(core_rmw) = (∅ : edge_set) /\
    state.(core_direct_addr) = (∅ : edge_set) /\
    state.(core_direct_data) = (∅ : edge_set) /\
    state.(core_direct_ctrl) = (∅ : edge_set).
  Proof.
    exists [CoreSilent 0; CoreEmit 0; CoreSilent 0; CoreEmit 0;
      CoreSilent 1; CoreObserve 1 1%Z; CoreSilent 1; CoreObserve 1 0%Z].
    eexists. split.
    - split.
      + eapply CoreRunCons. { eapply StepSequence; reflexivity. }
        eapply CoreRunCons. { eapply StepStore; try reflexivity. by eexists. }
        eapply CoreRunCons. { eapply StepSkipSequence; reflexivity. }
        eapply CoreRunCons. { eapply StepStore; try reflexivity. by eexists. }
        eapply CoreRunCons. { eapply StepSequence; reflexivity. }
        eapply CoreRunCons. { eapply StepLoad; try reflexivity. by eexists. }
        eapply CoreRunCons. { eapply StepSkipSequence; reflexivity. }
        eapply CoreRunCons. { eapply StepLoad; try reflexivity. by eexists. }
        constructor.
      + intros agent th Hlookup. destruct (decide (agent = 0)) as [->|H0].
        * simpl in Hlookup. injection Hlookup as <-. done.
        * destruct (decide (agent = 1)) as [->|H1].
          -- simpl in Hlookup. injection Hlookup as <-. done.
          -- simpl in Hlookup. simplify_map_eq.
    - split_and!; destruct sm, lm; vm_compute; reflexivity.
  Qed.

  Lemma sample_rf_wf sm lm : rf_wf (sample_events sm lm) sample_rf.
  Proof.
    split_and!.
    - intros w r Hrf. unfold rf, edge_relation, sample_rf in Hrf.
      assert ((w = 3 /\ r = 4) \/ (w = 0 /\ r = 5)) as [[-> ->]|[-> ->]] by set_solver;
        eexists _, _, _; split_and!; try reflexivity; eexists; split; reflexivity.
    - unfold rf_functional, rf, edge_relation, sample_rf. set_solver.
    - intros r ev Hlookup Hread. lookup_cases; try discriminate.
      + exists 3. unfold rf, edge_relation, sample_rf. set_solver.
      + exists 0. unfold rf, edge_relation, sample_rf. set_solver.
  Qed.

  Lemma sample_co_wf sm lm : co_wf (sample_events sm lm) sample_co.
  Proof.
    split_and!.
    - intros x y Hco. unfold co, edge_relation, sample_co in Hco.
      assert ((x = 0 /\ y = 2) \/ (x = 1 /\ y = 3)) as [[-> ->]|[-> ->]] by set_solver;
        eexists _, _; split_and!; try reflexivity; eexists; split; reflexivity.
    - unfold co_irreflexive, co, edge_relation, sample_co. set_solver.
    - unfold co_transitive, co, edge_relation, sample_co. set_solver.
    - intros x y ex ey Hx Hy Hwx Hwy Hloc Hne. lookup_cases;
        try discriminate; try congruence;
        unfold same_location, same_attribute in Hloc; vm_compute in Hloc;
        unfold co, edge_relation, sample_co; set_solver.
    - intros loc (i & Hloc). unfold event_has_location in Hloc.
      apply bind_Some in Hloc as (ev & Hlookup & Hloc). lookup_cases;
        vm_compute in Hloc; injection Hloc as <-;
        first [exists 0, 0%Z; reflexivity | exists 1, 0%Z; reflexivity].
    - intros loc x y (vx & Hx) (vy & Hy).
      apply sample_lookup in Hx, Hy. unfold data_write, flag_write, flag_read, data_read in *.
      naive_solver.
    - intros x y loc ev (v & Hx) Hy Hwrite Hloc Hne.
      apply sample_lookup in Hx. destruct Hx as [[-> Hx]|[[-> Hx]|Hx]];
        try (unfold data_write, flag_write, flag_read, data_read in Hx; naive_solver);
        injection Hx; intros; subst loc v; lookup_cases; try discriminate; try congruence;
        unfold same_location, same_attribute in Hloc; vm_compute in Hloc;
        unfold co, edge_relation, sample_co; set_solver.
  Qed.

  Lemma sample_program_graph sm lm : program_graph (program sm lm) (candidate sm lm).
  Proof.
    constructor; first apply sample_complete_run.
    destruct (sample_complete_run sm lm) as (actions & state & [Hrun _] & HE & HR & HA & HD & HC).
    pose proof (core_run_generated_wf _ _ _ Hrun) as ((Hwf & _) & _ & Hrmw & Haddr & Hdata & Hctrl).
    unfold core_candidate_wf, candidate; cbn.
    rewrite HE, HR, HA, HD, HC in *.
    split_and!; try done; [apply sample_rf_wf | apply sample_co_wf].
  Qed.

  Lemma sample_bad_outcome sm lm : bad_outcome lm (candidate sm lm).
  Proof. exists 4, 5. split; reflexivity. Qed.


  (** Canonical per-agent replays. The exact-run lemmas below invert the
      four steps (sequence, access, continuation, access). Their observed
      values remain arbitrary; no LKMM-consistency premise is used. *)
  Definition writer_ready sm := ThreadState
    (SStore StoreOnce (EConst 0) (EConst 1))
    [KSeq (SStore sm (EConst 1) (EConst 1))] ∅.
  Definition writer_started sm lm := update_thread (core_initial_state (program sm lm)) 0 (writer_ready sm).
  Definition writer_first sm lm := add_single_event (writer_started sm lm) 0 (writer_ready sm)
    (LMemory AccessWrite AccessOnce NotRmw 0 1%Z) ∅ ∅ ∅ ∅.
  Definition writer_last sm lm := update_thread (writer_first sm lm) 0
    (initial_thread (SStore sm (EConst 1) (EConst 1))).
  Definition writer_finished sm lm := add_single_event (writer_last sm lm) 0
    (initial_thread (SStore sm (EConst 1) (EConst 1)))
    (LMemory AccessWrite (store_access_mode sm) NotRmw 1 1%Z) ∅ ∅ ∅ ∅.

  Local Ltac invert_mp_step H :=
    inversion H; subst; clear H;
    cbn [core_action_agent] in *; simplify_eq;
    repeat match goal with
    | Ht : core_threads ?s !! ?t = Some ?th |- _ =>
      let Htmp := fresh in
      let v := eval vm_compute in (core_threads s !! t) in
      change (v = Some th) in Ht; injection Ht as Htmp; subst th
    end;
    repeat progress (cbn [thread_statement thread_continuation thread_registers eval_expr reg_integer reg_origins] in *; simplify_eq);
    repeat match goal with Hl : eval_location _ _ = Some _ |- _ =>
      vm_compute in Hl; simplify_eq end.

  Lemma writer_replay_exact sm lm actions final :
    core_run (program sm lm) (core_initial_state (program sm lm)) actions final ->
    Forall (fun a => core_action_agent a = 0) actions ->
    (forall th, final.(core_threads) !! 0 = Some th -> thread_complete th) ->
    final = writer_finished sm lm.
  Proof.
    intros Hrun Howners Hdone.
    repeat match goal with
    | Hr : core_run _ _ ?acts _, Ho : Forall _ ?acts |- _ =>
      inversion Hr; subst; clear Hr;
      [ first [reflexivity | exfalso; specialize (Hdone _ eq_refl);
          vm_compute in Hdone; destruct Hdone; discriminate] |
        inversion Ho; subst; clear Ho;
        match goal with Hstep : core_step _ _ _ _ |- _ => invert_mp_step Hstep end ]
    end.
  Qed.

  Definition reader_ready lm := ThreadState (SLoad 0 lm (EConst 1))
    [KSeq (SLoad 1 LoadOnce (EConst 0))] ∅.
  Definition reader_started sm lm := update_thread (core_initial_state (program sm lm)) 1 (reader_ready lm).
  Definition reader_first sm lm v := add_single_event (reader_started sm lm) 1 (reader_ready lm)
    (LMemory AccessRead (load_access_mode lm) NotRmw 1 v)
    {[0 := RegValue v {[2]}]} ∅ ∅ ∅.
  Definition reader_last sm lm v := update_thread (reader_first sm lm v) 1
    (ThreadState (SLoad 1 LoadOnce (EConst 0)) [] {[0 := RegValue v {[2]}]}).
  Definition reader_finished sm lm v w := add_single_event (reader_last sm lm v) 1
    (ThreadState (SLoad 1 LoadOnce (EConst 0)) [] {[0 := RegValue v {[2]}]})
    (LMemory AccessRead AccessOnce NotRmw 0 w)
    {[1 := RegValue w {[3]}; 0 := RegValue v {[2]}]} ∅ ∅ ∅.

  Lemma reader_replay_exact sm lm actions final :
    core_run (program sm lm) (core_initial_state (program sm lm)) actions final ->
    Forall (fun a => core_action_agent a = 1) actions ->
    (forall th, final.(core_threads) !! 1 = Some th -> thread_complete th) ->
    exists v w, final = reader_finished sm lm v w.
  Proof.
    intros Hrun Howners Hdone.
    repeat match goal with
    | Hr : core_run _ _ ?acts _, Ho : Forall _ ?acts |- _ =>
      inversion Hr; subst; clear Hr;
      [ first [solve [do 2 eexists; reflexivity] | exfalso; specialize (Hdone _ eq_refl);
          vm_compute in Hdone; destruct Hdone; discriminate] |
        inversion Ho; subst; clear Ho;
        match goal with Hstep : core_step _ _ _ _ |- _ => invert_mp_step Hstep end ]
    end.
  Qed.

End MessagePassingProgram.
