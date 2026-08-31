From Stdlib Require Import List.
From stdpp Require Import sets tactics.
From iris_lkmm.lkmm Require Import rcu_graph.
From iris_lkmm.lang Require Import lkmm_lang.
From iris_lkmm.operational Require Import
  rcu_machine rcu_machine_safety rcu_refinement rcu_builder rcu_candidate.
Import ListNotations.

(** Delayed-commitment product semantics for the feasibility gate.

    Program execution and graph commitment interleave, but neither component
    contains the other component's final state.  A completed execution is one
    in which the builder has caught up with the machine's emitted events and
    the canonical matcher has no unmatched RCU events.  This is the permitted
    delayed-commitment design from the semantic architecture, not a final-graph
    oracle. *)
Module RcuCoupled.
  Import RcuGraph LkmmLang RcuMachine RcuMachineSafety RcuRefinement.
  Import RcuBuilder RcuCandidate.

  Definition machine_matches_raw (m : RcuMachine.state) (r : raw_graph) : Prop :=
    r.(raw_events) = m.(generated).

  Record coupled_state := CoupledState {
    coupled_machine : RcuMachine.state;
    coupled_builder : builder_state
  }.

  Inductive coupled_action :=
  | CoupledMachineAction (a : RcuMachine.action)
  | CoupledBuilderAction.

  Inductive coupled_step (P : program) (agents : list agent) :
      coupled_state -> coupled_action -> coupled_state -> Prop :=
  | CoupledStepMachine m m' b a :
      RcuMachine.step P agents m a m' ->
      coupled_step P agents (CoupledState m b)
        (CoupledMachineAction a) (CoupledState m' b)
  | CoupledStepBuilder m b b' :
      builder_step b b' ->
      coupled_step P agents (CoupledState m b)
        CoupledBuilderAction (CoupledState m b').

  Inductive coupled_run (P : program) (agents : list agent) :
      coupled_state -> list coupled_action -> coupled_state -> Prop :=
  | CoupledRunNil s : coupled_run P agents s [] s
  | CoupledRunCons s1 s2 s3 a actions :
      coupled_step P agents s1 a s2 ->
      coupled_run P agents s2 actions s3 ->
      coupled_run P agents s1 (a :: actions) s3.

  Fixpoint machine_actions (actions : list coupled_action) :
      list RcuMachine.action :=
    match actions with
    | [] => []
    | CoupledMachineAction a :: actions' => a :: machine_actions actions'
    | CoupledBuilderAction :: actions' => machine_actions actions'
    end.

  Definition initial_coupled : coupled_state := CoupledState initial_state initial_builder.

  Definition coupled_complete (s : coupled_state) : Prop :=
    machine_matches_raw s.(coupled_machine) s.(coupled_builder).(bs_raw) /\
    rcu_matching_complete s.(coupled_builder).(bs_raw).(raw_events).

  (** The program-graph predicate for the minimal gate language.  The memory
      relations remain the independently committed abstract graph layer; this
      predicate states exactly that its events and computed RCU matching came
      from a run of [P]. *)
  Definition minimal_program_graph (P : program) (agents : list agent) (r : raw_graph) : Prop :=
    exists actions m,
      RcuMachine.run P agents initial_state actions m /\
      machine_matches_raw m r /\
      rcu_matching_complete r.(raw_events).

  Lemma coupled_run_trans P agents s1 as1 s2 as2 s3 :
    coupled_run P agents s1 as1 s2 ->
    coupled_run P agents s2 as2 s3 ->
    coupled_run P agents s1 (as1 ++ as2) s3.
  Proof.
    intros H12 H23. induction H12 as
      [s | a b c act actions Hstep Hrun IH]; simpl; first done.
    econstructor; [done | by apply IH].
  Qed.

  Lemma coupled_run_machine_projection P agents s actions s' :
    coupled_run P agents s actions s' ->
    RcuMachine.run P agents s.(coupled_machine)
      (machine_actions actions) s'.(coupled_machine).
  Proof.
    intros Hrun. induction Hrun.
    - constructor.
    - destruct H as [m1 m2 b1 a Hmachine | m1 b1 b2 Hbuilder];
        simpl in *; last done.
      econstructor; done.
  Qed.

  Lemma coupled_run_builder_projection P agents s actions s' :
    coupled_run P agents s actions s' ->
    builder_run s.(coupled_builder) s'.(coupled_builder).
  Proof.
    intros Hrun. induction Hrun.
    - constructor.
    - destruct H as [m1 m2 b1 a Hmachine | m1 b1 b2 Hbuilder];
        simpl in *; first done.
      econstructor; done.
  Qed.

  Lemma lift_machine_run P agents m actions m' b :
    RcuMachine.run P agents m actions m' ->
    coupled_run P agents (CoupledState m b)
      (map CoupledMachineAction actions) (CoupledState m' b).
  Proof.
    intros Hrun. induction Hrun; simpl.
    - constructor.
    - econstructor; last done.
      by apply CoupledStepMachine.
  Qed.

  Lemma lift_builder_run P agents m b b' :
    builder_run b b' ->
    exists actions,
      coupled_run P agents (CoupledState m b) actions
        (CoupledState m b').
  Proof.
    intros Hrun. induction Hrun.
    - exists []. constructor.
    - destruct IHHrun as (actions & Hactions).
      exists (CoupledBuilderAction :: actions).
      econstructor; [by apply CoupledStepBuilder | done].
  Qed.

  Theorem coupled_operational_soundness P agents actions s :
    coupled_run P agents initial_coupled actions s ->
    coupled_complete s ->
    minimal_program_graph P agents s.(coupled_builder).(bs_raw) /\
    rcu_consistent (graph_of_raw s.(coupled_builder).(bs_raw)) /\
    certificates_sound s.(coupled_machine) /\
    event_integrity s.(coupled_machine) /\
    machine_stack_safe s.(coupled_machine).
  Proof.
    destruct s as [m b]. simpl.
    intros Hrun (Hmatches & Hcomplete).
    pose proof (coupled_run_machine_projection P agents
      initial_coupled actions (CoupledState m b) Hrun) as Hmachine.
    pose proof (coupled_run_builder_projection P agents
      initial_coupled actions (CoupledState m b) Hrun) as Hbuilder.
    split; first by exists (machine_actions actions), m.
    split; first by eapply completed_builder_run_rb_irreflexive.
    split; first by eapply RcuMachine.operational_soundness.
    split.
    - by eapply operational_event_integrity.
    - by eapply machine_run_stack_safe.
  Qed.

  Theorem coupled_completed_certificate_snapshot_clear P agents actions s cert :
    coupled_run P agents initial_coupled actions s ->
    In cert s.(coupled_machine).(gp_certificates) ->
    lock_set cert.(gc_snapshot) ##
      lock_set (snapshot agents s.(coupled_machine)).
  Proof.
    intros Hrun Hcert.
    pose proof (coupled_run_machine_projection P agents initial_coupled
      actions s Hrun) as Hmachine.
    change (RcuMachine.run P agents initial_state
      (machine_actions actions) s.(coupled_machine)) in Hmachine.
    eapply completed_run_certificate_snapshot_clear; done.
  Qed.

  Definition consistent_program_candidate (P : program)
      (agents : list agent) (C : finite_candidate) : Prop :=
    candidate_well_formed C /\
    rcu_consistent (candidate_graph C) /\
    exists actions m,
      RcuMachine.run P agents initial_state actions m /\
      machine_matches_raw m (candidate_raw C).

  Theorem consistent_program_candidate_is_schedulable P agents C :
    consistent_program_candidate P agents C ->
    exists actions s,
      coupled_run P agents initial_coupled actions s /\
      coupled_complete s /\
      s.(coupled_builder).(bs_raw) = candidate_raw C.
  Proof.
    intros (Hwf & Hconsistent & machine_actions0 & m & Hmachine & Hmatches).
    destruct (consistent_candidate_is_incrementally_schedulable C
      Hwf Hconsistent) as (b & Hbuilder & Hraw & _).
    pose proof (lift_machine_run P agents initial_state machine_actions0 m
      initial_builder Hmachine) as Hmachine_lift.
    destruct (lift_builder_run P agents m initial_builder b Hbuilder)
      as (builder_actions & Hbuilder_lift).
    exists (map CoupledMachineAction machine_actions0 ++ builder_actions),
      (CoupledState m b). simpl.
    split.
    - by eapply coupled_run_trans.
    - split; last done.
      unfold coupled_complete. simpl. split; first by rewrite Hraw.
      destruct Hwf as (_ & _ & _ & Hcomplete & _). simpl in Hcomplete.
      rewrite Hraw, candidate_raw_events. done.
  Qed.

End RcuCoupled.
