From Stdlib Require Import Arith List.
From stdpp Require Import base tactics.
From iris_lkmm.lkmm Require Import rcu_graph.
Import ListNotations.

(** A deliberately small event-generating machine for the feasibility gate.
    [synchronize_rcu] has a begin and finish transition.  Begin snapshots the
    currently open (including nested) read-side sections; finish is enabled
    exactly when those sections have closed.  Readers opened after begin are
    absent from the snapshot and therefore cannot delay that grace period. *)
Module RcuMachine.
  Import RcuGraph.

  Definition agent := nat.

  Inductive instruction :=
  | IRead | IWrite | IRcuLock | IRcuUnlock | ISynchronizeRcu.

  Definition program := agent -> list instruction.

  Record generated_event := GeneratedEvent {
    ge_id : event_id;
    ge_agent : agent;
    ge_label : label
  }.

  Record gp_certificate := GpCertificate {
    gc_event : event_id;
    gc_snapshot : list event_id
  }.

  Record state := State {
    next_id : event_id;
    pc : agent -> nat;
    open_stack : agent -> list event_id;
    pending_gp : agent -> option (list event_id);
    generated : list generated_event;
    closed_sections : list critical_section;
    gp_certificates : list gp_certificate
  }.

  Definition update {A} (f : nat -> A) (k : nat) (v : A) : nat -> A :=
    fun k' => if Nat.eq_dec k k' then v else f k'.

  Lemma update_eq {A} (f : nat -> A) k v :
    update f k v k = v.
  Proof. unfold update. destruct (Nat.eq_dec k k); congruence. Qed.

  Lemma update_neq {A} (f : nat -> A) k k' v :
    k <> k' -> update f k v k' = f k'.
  Proof.
    intros Hneq. unfold update. destruct (Nat.eq_dec k k'); congruence.
  Qed.

  Definition current (P : program) (s : state) (a : agent)
      (i : instruction) : Prop :=
    nth_error (P a) (s.(pc) a) = Some i.

  Definition snapshot (agents : list agent) (s : state) : list event_id :=
    flat_map s.(open_stack) agents.

  Definition lock_closed (closed : list critical_section)
      (l : event_id) : Prop :=
    exists cs, In cs closed /\ cs.(cs_lock) = l.

  Definition all_closed (locks : list event_id)
      (closed : list critical_section) : Prop :=
    forall l, In l locks -> lock_closed closed l.

  Definition certificates_sound (s : state) : Prop :=
    forall cert, In cert s.(gp_certificates) ->
      all_closed cert.(gc_snapshot) s.(closed_sections).

  Definition ordinary_emit (s : state) (a : agent) (lab : label) : state :=
    State (S s.(next_id))
      (update s.(pc) a (S (s.(pc) a)))
      s.(open_stack) s.(pending_gp)
      (GeneratedEvent s.(next_id) a lab :: s.(generated))
      s.(closed_sections) s.(gp_certificates).

  Definition lock_emit (s : state) (a : agent) : state :=
    State (S s.(next_id))
      (update s.(pc) a (S (s.(pc) a)))
      (update s.(open_stack) a (s.(next_id) :: s.(open_stack) a))
      s.(pending_gp)
      (GeneratedEvent s.(next_id) a LRcuLock :: s.(generated))
      s.(closed_sections) s.(gp_certificates).

  Definition unlock_emit (s : state) (a : agent)
      (l : event_id) (rest : list event_id) : state :=
    State (S s.(next_id))
      (update s.(pc) a (S (s.(pc) a)))
      (update s.(open_stack) a rest)
      s.(pending_gp)
      (GeneratedEvent s.(next_id) a LRcuUnlock :: s.(generated))
      (CriticalSection l s.(next_id) :: s.(closed_sections))
      s.(gp_certificates).

  Definition begin_gp (agents : list agent) (s : state) (a : agent) : state :=
    State s.(next_id) s.(pc) s.(open_stack)
      (update s.(pending_gp) a (Some (snapshot agents s)))
      s.(generated) s.(closed_sections) s.(gp_certificates).

  Definition finish_gp (s : state) (a : agent)
      (snap : list event_id) : state :=
    State (S s.(next_id))
      (update s.(pc) a (S (s.(pc) a)))
      s.(open_stack)
      (update s.(pending_gp) a None)
      (GeneratedEvent s.(next_id) a LSyncRcu :: s.(generated))
      s.(closed_sections)
      (GpCertificate s.(next_id) snap :: s.(gp_certificates)).

  Inductive action :=
  | ARead (a : agent)
  | AWrite (a : agent)
  | ALock (a : agent)
  | AUnlock (a : agent)
  | ABeginGp (a : agent)
  | AFinishGp (a : agent).

  Inductive step (P : program) (agents : list agent) :
      state -> action -> state -> Prop :=
  | Step_read s a :
      current P s a IRead ->
      step P agents s (ARead a) (ordinary_emit s a LRead)
  | Step_write s a :
      current P s a IWrite ->
      step P agents s (AWrite a) (ordinary_emit s a LWrite)
  | Step_lock s a :
      current P s a IRcuLock ->
      step P agents s (ALock a) (lock_emit s a)
  | Step_unlock s a l rest :
      current P s a IRcuUnlock ->
      s.(open_stack) a = l :: rest ->
      step P agents s (AUnlock a) (unlock_emit s a l rest)
  | Step_begin_gp s a :
      current P s a ISynchronizeRcu ->
      s.(pending_gp) a = None ->
      step P agents s (ABeginGp a) (begin_gp agents s a)
  | Step_finish_gp s a snap :
      current P s a ISynchronizeRcu ->
      s.(pending_gp) a = Some snap ->
      all_closed snap s.(closed_sections) ->
      step P agents s (AFinishGp a) (finish_gp s a snap).

  Inductive run (P : program) (agents : list agent) :
      state -> list action -> state -> Prop :=
  | Run_nil s : run P agents s [] s
  | Run_cons s1 s2 s3 a actions :
      step P agents s1 a s2 ->
      run P agents s2 actions s3 ->
      run P agents s1 (a :: actions) s3.

  Definition initial_state : state :=
    State 0 (fun _ => 0) (fun _ => []) (fun _ => None) [] [] [].

  Lemma all_closed_mono locks closed cs :
    all_closed locks closed ->
    all_closed locks (cs :: closed).
  Proof.
    intros Hclosed l Hin. destruct (Hclosed l Hin) as (old & Hold & Hlock).
    exists old. split; [by right | done].
  Qed.

  Lemma certificates_sound_step P agents s a s' :
    certificates_sound s ->
    step P agents s a s' ->
    certificates_sound s'.
  Proof.
    intros Hsound Hstep. induction Hstep; simpl; try done.
    - intros cert Hcert.
      eapply all_closed_mono. by apply Hsound.
    - intros cert [Hnew | Hcert]; simpl.
      + subst cert. done.
      + by apply Hsound.
  Qed.

  Lemma run_preserves_certificates P agents s1 actions s2 :
    certificates_sound s1 ->
    run P agents s1 actions s2 ->
    certificates_sound s2.
  Proof.
    intros Hsound Hrun. induction Hrun; first done.
    apply IHHrun. by eapply certificates_sound_step.
  Qed.

  Theorem operational_soundness P agents actions s :
    run P agents initial_state actions s ->
    certificates_sound s.
  Proof.
    intros Hrun. eapply run_preserves_certificates; last done.
    intros cert Hfalse. inversion Hfalse.
  Qed.

  (** Local completeness of the grace-period transition: discharging precisely
      the captured obligations is sufficient to finish.  No final graph or
      final-graph consistency predicate occurs in this premise. *)
  Theorem finish_gp_complete P agents s a snap :
    current P s a ISynchronizeRcu ->
    s.(pending_gp) a = Some snap ->
    all_closed snap s.(closed_sections) ->
    exists s', step P agents s (AFinishGp a) s'.
  Proof.
    intros Hcur Hpending Hclosed. exists (finish_gp s a snap).
    by econstructor.
  Qed.

  Lemma begin_gp_captures_current_readers P agents s a :
    current P s a ISynchronizeRcu ->
    s.(pending_gp) a = None ->
    exists s', step P agents s (ABeginGp a) s' /\
      s'.(pending_gp) a = Some (snapshot agents s).
  Proof.
    intros Hcur Hnone. exists (begin_gp agents s a). split.
    - by constructor.
    - simpl. by rewrite update_eq.
  Qed.

End RcuMachine.
