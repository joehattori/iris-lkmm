From Stdlib Require Import Arith Classical List.
From stdpp Require Import base tactics.
From iris_lkmm.lkmm Require Import rcu_graph rcu_mono.
From iris_lkmm.operational Require Import rcu_builder.
Import ListNotations.

(** Declarative finite candidates and scheduling completeness.

    [finite_candidate] contains graph data only.  In particular, it contains
    no builder state, transition sequence, delta monitor, or schedule.  The
    completeness theorem starts from the single constant [initial_builder]
    and constructs the candidate one component at a time. *)
Module RcuCandidate.
  Import RcuGraph RcuMono RcuBuilder.

  Definition edge_endpoints_in
      (ids : list event_id) (edges : list edge) : Prop :=
    forall x y, In (x, y) edges -> In x ids /\ In y ids.

  Definition sections_well_formed
      (evs : list labeled_event) (sections : list critical_section) : Prop :=
    forall cs, In cs sections ->
      In cs.(cs_lock) (map le_id evs) /\
      In cs.(cs_unlock) (map le_id evs) /\
      lookup_label evs cs.(cs_lock) = LRcuLock /\
      lookup_label evs cs.(cs_unlock) = LRcuUnlock.

  Record finite_candidate := FiniteCandidate {
    fc_events : list labeled_event;
    fc_po : list edge;
    fc_hb : list edge;
    fc_prop : list edge;
    fc_pb : list edge;
    fc_sections : list critical_section
  }.

  Definition candidate_well_formed (C : finite_candidate) : Prop :=
    NoDup (map le_id C.(fc_events)) /\
    edge_endpoints_in (map le_id C.(fc_events)) C.(fc_po) /\
    edge_endpoints_in (map le_id C.(fc_events)) C.(fc_hb) /\
    edge_endpoints_in (map le_id C.(fc_events)) C.(fc_prop) /\
    edge_endpoints_in (map le_id C.(fc_events)) C.(fc_pb) /\
    sections_well_formed C.(fc_events) C.(fc_sections).

  Fixpoint load_events (evs : list labeled_event) : raw_graph :=
    match evs with
    | [] => empty_raw
    | ev :: evs' => add_event (load_events evs') ev
    end.

  Fixpoint load_po (edges : list edge) (r : raw_graph) : raw_graph :=
    match edges with
    | [] => r
    | e :: edges' => add_po (load_po edges' r) e
    end.

  Fixpoint load_hb (edges : list edge) (r : raw_graph) : raw_graph :=
    match edges with
    | [] => r
    | e :: edges' => add_hb (load_hb edges' r) e
    end.

  Fixpoint load_prop (edges : list edge) (r : raw_graph) : raw_graph :=
    match edges with
    | [] => r
    | e :: edges' => add_prop (load_prop edges' r) e
    end.

  Fixpoint load_pb (edges : list edge) (r : raw_graph) : raw_graph :=
    match edges with
    | [] => r
    | e :: edges' => add_pb (load_pb edges' r) e
    end.

  Fixpoint load_sections (sections : list critical_section)
      (r : raw_graph) : raw_graph :=
    match sections with
    | [] => r
    | cs :: sections' => add_section (load_sections sections' r) cs
    end.

  Definition candidate_raw (C : finite_candidate) : raw_graph :=
    load_sections C.(fc_sections)
      (load_pb C.(fc_pb)
        (load_prop C.(fc_prop)
          (load_hb C.(fc_hb)
            (load_po C.(fc_po) (load_events C.(fc_events)))))).

  Definition candidate_graph (C : finite_candidate) : graph :=
    graph_of_raw (candidate_raw C).

  Lemma load_events_ids evs :
    map le_id (raw_events (load_events evs)) = map le_id evs.
  Proof.
    induction evs as [|ev evs IH]; first done.
    simpl. unfold add_event. simpl. by rewrite IH.
  Qed.

  Lemma load_events_schedule evs :
    NoDup (map le_id evs) ->
    raw_run empty_raw (load_events evs).
  Proof.
    induction evs as [|ev evs IH]; intros Hnodup; first constructor.
    inversion Hnodup as [|id ids Hfresh Htail]; subst.
    eapply raw_run_trans.
    - by apply IH.
    - apply raw_run_single. apply RawStepEvent.
      rewrite load_events_ids. intros Hin. apply Hfresh.
      by apply list_elem_of_In.
  Qed.

  Lemma load_po_schedule edges r :
    raw_run r (load_po edges r).
  Proof.
    induction edges as [|e edges IH]; simpl; first constructor.
    eapply raw_run_trans; first apply IH.
    apply raw_run_single. apply RawStepPo.
  Qed.

  Lemma load_hb_schedule edges r :
    raw_run r (load_hb edges r).
  Proof.
    induction edges as [|e edges IH]; simpl; first constructor.
    eapply raw_run_trans; first apply IH.
    apply raw_run_single. apply RawStepHb.
  Qed.

  Lemma load_prop_schedule edges r :
    raw_run r (load_prop edges r).
  Proof.
    induction edges as [|e edges IH]; simpl; first constructor.
    eapply raw_run_trans; first apply IH.
    apply raw_run_single. apply RawStepProp.
  Qed.

  Lemma load_pb_schedule edges r :
    raw_run r (load_pb edges r).
  Proof.
    induction edges as [|e edges IH]; simpl; first constructor.
    eapply raw_run_trans; first apply IH.
    apply raw_run_single. apply RawStepPb.
  Qed.

  Lemma load_sections_schedule sections r :
    raw_run r (load_sections sections r).
  Proof.
    induction sections as [|cs sections IH]; simpl; first constructor.
    eapply raw_run_trans; first apply IH.
    apply raw_run_single. apply RawStepSection.
  Qed.

  Theorem candidate_has_raw_schedule C :
    candidate_well_formed C ->
    raw_run empty_raw (candidate_raw C).
  Proof.
    intros (Hnodup & _).
    unfold candidate_raw.
    eapply raw_run_trans; first by apply load_events_schedule.
    eapply raw_run_trans; first apply load_po_schedule.
    eapply raw_run_trans; first apply load_hb_schedule.
    eapply raw_run_trans; first apply load_prop_schedule.
    eapply raw_run_trans; first apply load_pb_schedule.
    apply load_sections_schedule.
  Qed.

  Definition rb_difference (old new : raw_graph) : relation :=
    fun x y =>
      rb (graph_of_raw new) x y /\
      ~ rb (graph_of_raw old) x y.

  Lemma rb_difference_exact old new seen :
    graph_le (graph_of_raw old) (graph_of_raw new) ->
    (forall x y, seen x y <-> rb (graph_of_raw old) x y) ->
    rb_delta_exact old new seen (rb_difference old new).
  Proof.
    intros Hle Hexact x y. split.
    - intros Hnew.
      destruct (classic (rb (graph_of_raw old) x y)) as [Hold | Hnot].
      + left. by apply Hexact.
      + right. by split.
    - intros [Hseen | (Hnew & _)].
      + eapply rb_mono; first exact Hle.
        by apply Hexact.
      + done.
  Qed.

  Lemma rb_difference_locally_safe old new final :
    raw_run new final ->
    rcu_consistent (graph_of_raw final) ->
    locally_safe (rb_difference old new).
  Proof.
    intros Hsuffix Hconsistent e (Hnew & _).
    apply (Hconsistent e).
    eapply rb_mono; last exact Hnew.
    by eapply raw_run_graph_le.
  Qed.

  Lemma builder_run_trans s1 s2 s3 :
    builder_run s1 s2 -> builder_run s2 s3 -> builder_run s1 s3.
  Proof.
    intros H12 H23. induction H12.
    - done.
    - econstructor; eauto.
  Qed.

  Lemma lift_safe_raw_schedule r final s :
    s.(bs_raw) = r ->
    builder_invariant s ->
    raw_run r final ->
    rcu_consistent (graph_of_raw final) ->
    exists s',
      builder_run s s' /\
      s'.(bs_raw) = final /\
      builder_invariant s'.
  Proof.
    intros Hraw Hinv Hrun.
    revert s Hraw Hinv.
    induction Hrun as
      [r | r r' final Hstep Hsuffix IH];
      intros s Hraw Hinv Hconsistent.
    - exists s. split; first constructor.
      split; [exact Hraw | exact Hinv].
    - destruct s as [current links seen]. simpl in Hraw. subst current.
      pose (delta := rb_difference r r').
      pose (next := BuilderState r' links
        (fun x y => seen x y \/ delta x y)).
      assert (Hbuilder : builder_step
          (BuilderState r links seen) next).
      { unfold next. apply BuilderStepRaw.
        - exact Hstep.
        - unfold delta. apply rb_difference_exact.
          + by apply raw_step_graph_le.
          + by destruct Hinv as (Hexact & _).
        - unfold delta. by eapply rb_difference_locally_safe.
      }
      assert (Hnext : builder_invariant next).
      { eapply builder_step_preserves_invariant; eauto. }
      destruct (IH next eq_refl Hnext Hconsistent)
        as (s' & Hrest & Hfinal & Hinvariant).
      exists s'. split.
      + by econstructor.
      + split; [exact Hfinal | exact Hinvariant].
  Qed.

  (** Finite scheduling completeness for the RCU graph kernel.  The only
      builder state in the premise is the fixed empty [initial_builder];
      [C] is used by the meta-level existence proof to choose successive
      locally safe mutations, never stored in the initial state. *)
  Theorem consistent_candidate_is_incrementally_schedulable C :
    candidate_well_formed C ->
    rcu_consistent (candidate_graph C) ->
    exists s,
      builder_run initial_builder s /\
      s.(bs_raw) = candidate_raw C /\
      graph_of_raw s.(bs_raw) = candidate_graph C.
  Proof.
    intros Hwf Hconsistent.
    pose proof (candidate_has_raw_schedule C Hwf) as Hschedule.
    destruct (lift_safe_raw_schedule empty_raw (candidate_raw C)
      initial_builder eq_refl initial_builder_invariant
      Hschedule Hconsistent) as (s & Hrun & Hraw & _).
    exists s. repeat split; try done.
    by rewrite Hraw.
  Qed.

  (** Any link present in a scheduled candidate has an explicit witness that
      can be committed by one further local step. *)
  Theorem scheduled_candidate_link_can_be_committed C s x y :
    builder_run initial_builder s ->
    s.(bs_raw) = candidate_raw C ->
    rcu_link (candidate_graph C) x y ->
    exists k s',
      builder_run initial_builder s' /\
      In k s'.(bs_links) /\
      k.(lc_source) = x /\
      k.(lc_target) = y.
  Proof.
    intros Hrun Hraw Hlink.
    destruct (link_valid_complete (candidate_graph C) x y Hlink)
      as (k & Hsource & Htarget & Hvalid).
    assert (Hvalid' : link_valid (graph_of_raw s.(bs_raw)) k).
    { by rewrite Hraw. }
    destruct (commit_ready_link s k Hvalid') as (s' & Hstep & Hin).
    exists k, s'. repeat split; try done.
    eapply builder_run_trans; first exact Hrun.
    econstructor; [exact Hstep | constructor].
  Qed.

End RcuCandidate.
