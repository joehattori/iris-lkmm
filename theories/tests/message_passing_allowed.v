From Stdlib Require Import List Lia Relations.Relation_Operators.
From stdpp Require Import gmap fin_maps tactics.
From iris_lkmm.lkmm Require Import execution memory_relations rcu_graph.
From iris_lkmm.lang Require Import core_renaming.
From iris_lkmm.examples Require Import message_passing_code.
Import ListNotations.

(** Existential model regressions. These remain independent of Iris:
    a universal WP guarantee cannot replace an allowed-execution witness. *)
Module MessagePassingAllowed.
  Import LkmmCoreRenaming LkmmMemoryRelations RcuGraph MessagePassingCode.
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


  Lemma sample_no_barrier sm lm k i :
    ~ event_has_barrier_kind (sample_events sm lm) k i.
  Proof.
    intros H. apply event_has_barrier_kind_lookup in H as (ev & Hlookup & H).
    lookup_cases; discriminate.
  Qed.

  Lemma sample_no_rmw sm lm i : ~ event_is_rmw_marked (sample_events sm lm) i.
  Proof.
    intros H. apply event_is_rmw_marked_lookup in H as (ev & Hlookup & H).
    lookup_cases; discriminate.
  Qed.

  Lemma sample_no_mb sm lm i : ~ mb_event (sample_events sm lm) ∅ i.
  Proof.
    intros [[H|H] _]; last by eapply sample_no_barrier.
    apply event_has_access_mode_lookup in H as (ev & Hlookup & H).
    lookup_cases; destruct sm, lm; discriminate.
  Qed.

  Lemma sample_strong_empty sm lm x y : ~ strong_fence (sample_events sm lm) ∅ x y.
  Proof.
    pose proof (sample_no_barrier sm lm) as HB.
    pose proof (sample_no_rmw sm lm) as HR.
    pose proof (sample_no_mb sm lm) as HM.
    unfold strong_fence, mb, gp, fencerel, rel_union, rel_seq, rel_id_on,
      rel_intersection, optional. naive_solver.
  Qed.

  Lemma sample_rw_fences_empty sm lm x y :
    ~ wmb (sample_events sm lm) x y /\ ~ rmb (sample_events sm lm) x y.
  Proof.
    pose proof (sample_no_barrier sm lm) as HB.
    unfold wmb, rmb, fencerel, rel_seq, rel_id_on. naive_solver.
  Qed.

  Lemma sample_po sm lm x y : po (sample_events sm lm) x y ->
    (x = 2 /\ y = 3) \/ (x = 4 /\ y = 5).
  Proof.
    intros (t & nx & ny & lx & ly & Hx & Hy & Hlt).
    lookup_cases; unfold data_write, flag_write, flag_read, data_read in *;
      simplify_eq; try lia; auto.
  Qed.

  Lemma sample_po_loc_empty sm lm x y : ~ po_loc (sample_events sm lm) x y.
  Proof.
    intros [Hpo Hloc]. apply sample_po in Hpo as [[-> ->]|[-> ->]];
      vm_compute in Hloc; naive_solver.
  Qed.

  Lemma sample_po_rel sm lm x y : po_rel (sample_events sm lm) ∅ x y ->
    sm = StoreRelease /\ x = 2 /\ y = 3.
  Proof.
    intros (z & (w & [-> _] & Hpo) & [-> [Hrel _]]).
    apply sample_po in Hpo as [[-> ->]|[-> ->]];
      destruct sm, lm; vm_compute in Hrel; auto; discriminate.
  Qed.

  Lemma sample_acq_po sm lm x y : acq_po (sample_events sm lm) ∅ x y ->
    lm = LoadAcquire /\ x = 4 /\ y = 5.
  Proof.
    intros (z & (w & [-> [Hacq _]] & Hpo) & [-> _]).
    apply sample_po in Hpo as [[-> ->]|[-> ->]];
      destruct sm, lm; vm_compute in Hacq; auto; discriminate.
  Qed.

  Lemma sample_rmw_sequence x y : rmw_sequence sample_rf ∅ x y -> x = y.
  Proof.
    intros H. induction H; try congruence.
    destruct H as (z & _ & H). unfold rmw, edge_relation in H. set_solver.
  Qed.

  Lemma sample_cumul sm lm x y : cumul_fence (sample_events sm lm) ∅ sample_rf x y ->
    sm = StoreRelease /\ x = 2 /\ y = 3.
  Proof.
    intros (z & (w & (v & [-> Hmarked] & Hfence) & [-> _]) & Hrmw).
    apply sample_rmw_sequence in Hrmw. subst z.
    destruct Hfence as [(u & Hprefix & [Hstrong|Hrel])|Hwmb].
    - exfalso. by eapply sample_strong_empty.
    - apply sample_po_rel in Hrel as (-> & -> & ->).
      destruct Hprefix as [->|(r & [Hrf _] & [-> _])]; first done.
      unfold rf, edge_relation, sample_rf in Hrf. set_solver.
    - exfalso. exact (proj1 (sample_rw_fences_empty _ _ _ _) Hwmb).
  Qed.

  Lemma sample_cumul_rtc sm lm x y : rtc (cumul_fence (sample_events sm lm) ∅ sample_rf) x y ->
    x = y \/ (sm = StoreRelease /\ x = 2 /\ y = 3).
  Proof.
    intros H. induction H; [right; by apply (sample_cumul sm lm) | by left | naive_solver].
  Qed.

  Lemma sample_prop sm lm x y : prop (sample_events sm lm) ∅ sample_rf sample_co x y ->
    x = y \/ (x,y) ∈ ({[(0,2); (1,3); (5,2); (0,5); (3,4); (1,4)]} : edge_set) \/
      (sm = StoreRelease /\ (x,y) ∈ ({[(2,3); (2,4); (0,3); (0,4); (5,3); (5,4)]} : edge_set)).
  Proof.
    intros (z & (w & (v & (u & (t & [-> _] & Hover) & Hcumul) & [-> _]) & Hrfe) & [-> _]).
    apply sample_cumul_rtc in Hcumul.
    unfold optional, rel_id, rel_intersection, overwrite, rel_union, fr,
      rel_seq, rel_inverse, rfe, rel_intersection, rf, co, edge_relation, sample_rf, sample_co in *.
    set_solver.
  Qed.

  Lemma sample_ppo sm lm x y : ppo (sample_events sm lm) ∅ sample_rf sample_co ∅ ∅ ∅ x y ->
    (sm = StoreRelease /\ x = 2 /\ y = 3) \/
    (lm = LoadAcquire /\ x = 4 /\ y = 5).
  Proof.
    assert (forall a b, ~ dep (sample_events sm lm) sample_rf ∅ ∅ a b) as HD.
    { unfold dep, addr, data, direct_addr, direct_data, rel_union, rel_seq, edge_relation. set_solver. }
    assert (forall a b, ~ addr (sample_events sm lm) sample_rf ∅ ∅ a b) as HA.
    { unfold addr, direct_addr, rel_seq, edge_relation. set_solver. }
    assert (forall a b, ~ ctrl (sample_events sm lm) sample_rf ∅ ∅ a b) as HC.
    { unfold ctrl, direct_ctrl, rel_seq, edge_relation. set_solver. }
    intros [Hto_r|[Hto_w|[Hfence _]]].
    - unfold to_r, rel_union, rel_seq in Hto_r. naive_solver.
    - unfold to_w, rwdep, rel_union, rel_seq, rel_intersection in Hto_w.
      destruct Hto_w as [H|[[Hover Hint]|H]]; try by exfalso; naive_solver.
      unfold overwrite, rel_union, co, fr, rel_seq, rel_inverse, rf,
        edge_relation, sample_rf, sample_co in Hover.
      assert ((x = 0 /\ y = 2) \/ (x = 1 /\ y = 3) \/ (x = 5 /\ y = 2)) as H by set_solver.
      destruct H as [[-> ->]|[[-> ->]|[-> ->]]]; vm_compute in Hint; naive_solver.
    - destruct Hfence as [[Hstrong|[Hrel|Hacq]]|[Hwmb|Hrmb]].
      + exfalso. by eapply sample_strong_empty.
      + left. by apply (sample_po_rel sm lm).
      + right. by apply (sample_acq_po sm lm).
      + exfalso. exact (proj1 (sample_rw_fences_empty _ _ _ _) Hwmb).
      + exfalso. exact (proj2 (sample_rw_fences_empty _ _ _ _) Hrmb).
  Qed.

  Lemma sample_hb sm lm x y : candidate_hb (candidate sm lm) x y ->
    (x = 0 /\ y = 5) \/ (x = 3 /\ y = 4) \/
    (sm = StoreRelease /\ ((x = 2 /\ y = 3) \/ (x = 5 /\ y = 4))) \/
    (lm = LoadAcquire /\ x = 4 /\ y = 5).
  Proof.
    intros (z & (w & [<- _] & [Hppo|[Hrfe|[[Hprop Hne] Hint]]]) & [-> _]).
    - apply sample_ppo in Hppo. naive_solver.
    - destruct Hrfe as [Hrf _]. unfold rf, edge_relation, sample_rf in Hrf. set_solver.
    - apply sample_prop in Hprop as [Heq|[Hbase|[Hrel Hrelease]]]; first done.
      + unfold rel_id in Hne.
        assert ((x = 0 /\ y = 2) \/ (x = 1 /\ y = 3) \/ (x = 5 /\ y = 2) \/
          (x = 0 /\ y = 5) \/ (x = 3 /\ y = 4) \/ (x = 1 /\ y = 4)) as H by set_solver.
        destruct H as [[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[-> ->]]]]]];
          vm_compute in Hint; naive_solver.
      + assert ((x = 2 /\ y = 3) \/ (x = 2 /\ y = 4) \/ (x = 0 /\ y = 3) \/
          (x = 0 /\ y = 4) \/ (x = 5 /\ y = 3) \/ (x = 5 /\ y = 4)) as H by set_solver.
        destruct H as [[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[-> ->]]]]]];
          vm_compute in Hint; naive_solver.
  Qed.

  Lemma acyclic_rank (r : relation) (rank : event_id -> nat) :
    (forall x y, r x y -> rank x < rank y) -> rel_acyclic r.
  Proof.
    intros Hstep x Hcycle.
    assert (forall a b, tc r a b -> rank a < rank b) as Hpath.
    { intros a b H. induction H; [by apply Hstep | lia]. }
    pose proof (Hpath x x Hcycle). lia.
  Qed.

  Definition coherence_rank (i : event_id) : nat :=
    match i with 0 | 1 => 0 | 5 => 1 | 2 | 3 => 2 | _ => 3 end.
  Definition release_rank (i : event_id) : nat :=
    match i with 0 | 1 => 0 | 2 => 1 | 3 => 2 | 5 => 3 | _ => 4 end.

  Lemma sample_consistent sm lm : sm = StoreOnce \/ lm = LoadOnce ->
    lkmm_consistent (candidate sm lm).
  Proof.
    intros Hweak. split_and!.
    - apply (acyclic_rank _ coherence_rank).
      intros x y [Hpo|[Hrf|[Hco|Hfr]]].
      { exfalso. exact (sample_po_loc_empty sm lm x y Hpo). }
      all: unfold fr, rel_seq, rel_inverse, rf, co, edge_relation, sample_rf, sample_co in *;
        cbn in *.
      all: assert ((x = 0 /\ y = 2) \/ (x = 1 /\ y = 3) \/ (x = 5 /\ y = 2) \/
          (x = 0 /\ y = 5) \/ (x = 3 /\ y = 4)) as H by set_solver;
        destruct H as [[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[-> ->]]]]]; cbn; lia.
    - intros x y [Hrmw _]. unfold rmw, edge_relation in Hrmw. set_solver.
    - destruct Hweak as [-> | ->].
      + apply (acyclic_rank _ (fun i => i)). intros x y H.
        apply sample_hb in H. naive_solver lia.
      + apply (acyclic_rank _ release_rank). intros x y H.
        apply sample_hb in H.
        destruct H as [(-> & ->)|[(-> & ->)|[(? & [(-> & ->)|(-> & ->)])|(? & -> & ->)]]];
          cbn; congruence || lia.
    - intros x Hcycle. assert (forall a b, graph_pb (core_candidate_graph (candidate sm lm)) a b -> False) as Hempty.
      { intros a b (z & (w & (v & _ & Hstrong) & _) & _).
        exact (sample_strong_empty sm lm _ _ Hstrong). }
      induction Hcycle; naive_solver.
    - intros x (z & (w & (v & (u & _ & Hfence) & _) & _) & _).
      destruct Hfence as (a & b & _ & Horder & _).
      induction Horder; try done;
        unfold is_gp in *; exfalso; eapply (sample_no_barrier sm lm BarrierSyncRcu); eassumption.
  Qed.

  Lemma mp_weakened_allowed sm lm : sm = StoreOnce \/ lm = LoadOnce ->
    exists C, program_graph (program sm lm) C /\ bad_outcome lm C /\ lkmm_consistent C.
  Proof.
    intros Hweak. exists (candidate sm lm). split_and!.
    - apply sample_program_graph.
    - apply sample_bad_outcome.
    - by apply sample_consistent.
  Qed.

  Theorem mp_once_once_allowed : exists C,
    program_graph (program StoreOnce LoadOnce) C /\
    bad_outcome LoadOnce C /\ lkmm_consistent C.
  Proof. apply mp_weakened_allowed. by left. Qed.

  Theorem mp_release_once_allowed : exists C,
    program_graph (program StoreRelease LoadOnce) C /\
    bad_outcome LoadOnce C /\ lkmm_consistent C.
  Proof. apply mp_weakened_allowed. by right. Qed.

  Theorem mp_once_acquire_allowed : exists C,
    program_graph (program StoreOnce LoadAcquire) C /\
    bad_outcome LoadAcquire C /\ lkmm_consistent C.
  Proof. apply mp_weakened_allowed. by left. Qed.
End MessagePassingAllowed.
