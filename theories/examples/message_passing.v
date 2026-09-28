From Stdlib Require Import List Lia Relations.Relation_Operators.
From stdpp Require Import gmap fin_maps tactics.
From iris_lkmm.lkmm Require Import execution memory_relations rcu_graph.
From iris_lkmm.lang Require Import core_renaming.
From iris_lkmm.examples Require Import message_passing_program.

(** Outcome theorems for the four message-passing variants. *)
Module MessagePassing.
  Export MessagePassingProgram.
  Import LkmmCoreRenaming LkmmMemoryRelations RcuGraph.

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

  Lemma filtered_actions_owner t actions :
    Forall (fun a => core_action_agent a = t) (agent_actions t actions).
  Proof.
    unfold agent_actions. induction actions as [|a actions IH]; cbn; first constructor.
    case_decide; [constructor; done | done].
  Qed.

  Lemma writer_lookup sm lm i ev : lookup_event (writer_finished sm lm).(core_events) i = Some ev ->
    ev = EInitWrite 0 0%Z \/ ev = EInitWrite 1 0%Z \/ ev = data_write \/ ev = flag_write sm.
  Proof.
    intros H. change (lookup_event {[0 := EInitWrite 0 0%Z; 1 := EInitWrite 1 0%Z;
      2 := data_write; 3 := flag_write sm]} i = Some ev) in H.
    unfold lookup_event in H.
    repeat (apply lookup_insert_Some in H as [[? ?]|[? H]]);
      try apply lookup_singleton_Some in H; naive_solver.
  Qed.

  Lemma reader_lookup sm lm v w i ev : lookup_event (reader_finished sm lm v w).(core_events) i = Some ev ->
    ev = EInitWrite 0 0%Z \/ ev = EInitWrite 1 0%Z \/ ev = flag_read lm v \/ ev = data_read w.
  Proof.
    intros H. change (lookup_event {[0 := EInitWrite 0 0%Z; 1 := EInitWrite 1 0%Z;
      2 := flag_read lm v; 3 := data_read w]} i = Some ev) in H.
    unfold lookup_event in H.
    repeat (apply lookup_insert_Some in H as [[? ?]|[? H]]);
      try apply lookup_singleton_Some in H; naive_solver.
  Qed.

  (** Replay each agent to account for all writes in any candidate, and
      recover the two producer events in the original allocation. *)
  Lemma program_writes sm lm C : program_graph (program sm lm) C ->
    exists a b,
      lookup_event C.(candidate_events) a = Some data_write /\
      lookup_event C.(candidate_events) b = Some (flag_write sm) /\
      (forall i ev, lookup_event C.(candidate_events) i = Some ev -> is_write ev ->
        ev = EInitWrite 0 0%Z \/ ev = EInitWrite 1 0%Z \/ ev = data_write \/ ev = flag_write sm).
  Proof.
    intros [(actions & final & Hrun & HE & _) Hwf].
    destruct (complete_core_run_replay_agent_initial _ _ _ 0 Hrun)
      as (writer & HW & HMW & HCW).
    assert (writer = writer_finished sm lm) as ->.
    { eapply writer_replay_exact; [done | apply filtered_actions_owner | done]. }
    destruct (complete_core_run_replay_agent_initial _ _ _ 1 Hrun)
      as (reader & HR & HMR & HCR).
    destruct (reader_replay_exact _ _ _ _ HR (filtered_actions_owner _ _) HCR) as (v & w & ->).
    assert (exists a, lookup_event final.(core_events) a = Some data_write) as [a Ha].
    { destruct (proj1 (replay_event_lookup _ _ _ _ _ _ 2 0
        (LMemory AccessWrite AccessOnce NotRmw 0 1%Z) HMW) eq_refl) as [Hbad|(a & Ha & _)];
        first discriminate. by exists a. }
    assert (exists b, lookup_event final.(core_events) b = Some (flag_write sm)) as [b Hb].
    { destruct (proj1 (replay_event_lookup _ _ _ _ _ _ 3 1
        (LMemory AccessWrite (store_access_mode sm) NotRmw 1 1%Z) HMW) eq_refl) as [Hbad|(b & Hb & _)];
        first discriminate. by exists b. }
    exists a, b. rewrite <- HE. split_and!; try done.
    intros i ev Hi Hwrite.
    destruct (core_run_events_source _ _ _ _ _ _ (proj1 Hrun) Hi) as [Hinit|(t & n & label & th & -> & Hth)].
    - change (lookup_event {[0 := EInitWrite 0 0%Z; 1 := EInitWrite 1 0%Z]} i = Some ev) in Hinit.
      unfold lookup_event in Hinit.
      apply lookup_insert_Some in Hinit as [[_ Hinit]|[_ Hinit]];
        last apply lookup_singleton_Some in Hinit; naive_solver.
    - destruct (decide (t = 0)) as [->|H0].
      + apply (writer_lookup sm lm (replay_id final.(core_events) 0 2 i)).
        apply (proj2 (replay_event_lookup _ _ _ _ _ _ _ _ _ HMW)).
        right. exists i. split; done.
      + destruct (decide (t = 1)) as [->|H1].
        * assert (lookup_event (reader_finished sm lm v w).(core_events)
            (replay_id final.(core_events) 1 2 i) = Some (EAgent 1 n label)) as Hlookup.
          { apply (proj2 (replay_event_lookup _ _ _ _ _ _ _ _ _ HMR)).
            right. exists i. split; done. }
          apply reader_lookup in Hlookup.
          unfold flag_read, data_read in Hlookup. destruct Hlookup as [H|[H|[H|H]]];
            inversion H; subst; discriminate.
        * cbn in Hth. rewrite !lookup_fmap in Hth. simplify_map_eq.
  Qed.
  Lemma memory_marked E i t n kind mode loc val :
    lookup_event E i = Some (EAgent t n (LMemory kind mode NotRmw loc val)) ->
    mode <> AccessPlain -> marked E i.
  Proof.
    intros Hi Hmode. split; first by eapply lookup_event_in.
    intros [Hplain _]. apply event_has_access_mode_lookup in Hplain as (ev & Hev & Hplain).
    rewrite Hi in Hev. injection Hev as <-. cbn in Hplain. congruence.
  Qed.

  (** The LKMM reason for rejecting MP: propagation from the stale data
      read back to the flag read, opposed by the acquire's preserved order. *)
  Lemma mp_cycle C a b c d :
    lookup_event C.(candidate_events) a = Some data_write ->
    lookup_event C.(candidate_events) b = Some (flag_write StoreRelease) ->
    lookup_event C.(candidate_events) c = Some (flag_read LoadAcquire 1%Z) ->
    lookup_event C.(candidate_events) d = Some (data_read 0%Z) ->
    rfe C.(candidate_events) C.(candidate_rf) b c ->
    fre C.(candidate_events) C.(candidate_rf) C.(candidate_co) d a ->
    ~ lkmm_consistent C.
  Proof.
    intros Ha Hb Hc Hd Hrfe Hfre (_ & _ & Hacyclic & _).
    assert (marked C.(candidate_events) a) as Hma by (eapply memory_marked; [exact Ha|discriminate]).
    assert (marked C.(candidate_events) b) as Hmb by (eapply memory_marked; [exact Hb|discriminate]).
    assert (marked C.(candidate_events) c) as Hmc by (eapply memory_marked; [exact Hc|discriminate]).
    assert (marked C.(candidate_events) d) as Hmd by (eapply memory_marked; [exact Hd|discriminate]).
    assert (po C.(candidate_events) a b) as Hab.
    { do 5 eexists. split_and!; [exact Ha|exact Hb|lia]. }
    assert (po C.(candidate_events) c d) as Hcd.
    { do 5 eexists. split_and!; [exact Hc|exact Hd|lia]. }
    assert (same_agent C.(candidate_events) d c) as Hsame.
    { eapply same_attribute_from_lookup; [exact Hd|exact Hc|reflexivity|reflexivity]. }
    assert (d <> c) as Hne by (intros ->; rewrite Hd in Hc; discriminate).
    assert (release C.(candidate_events) C.(candidate_rmw) b) as Hrelease.
    { unfold release, failed_rmw, event_has_access_mode, event_has_access_kind,
        event_is_rmw_marked, execution.LkmmExecution.event_attribute.
      rewrite Hb. cbn. intuition discriminate. }
    assert (acquire C.(candidate_events) C.(candidate_rmw) c) as Hacquire.
    { unfold acquire, failed_rmw, event_has_access_mode, event_has_access_kind,
        event_is_rmw_marked, execution.LkmmExecution.event_attribute.
      rewrite Hc. cbn. intuition discriminate. }
    assert (po_rel C.(candidate_events) C.(candidate_rmw) a b) as Hrel.
    { exists b. split; last by split.
      exists a. split; last done. split; first done. exists data_write. split; done. }
    assert (cumul_fence C.(candidate_events) C.(candidate_rmw) C.(candidate_rf) a b) as Hcumul.
    { exists b. split; last apply rt_refl.
      exists b. split; last by split.
      exists a. split; first by split. left.
      exists a. split; [by left|by right]. }
    assert (prop C.(candidate_events) C.(candidate_rmw) C.(candidate_rf) C.(candidate_co) d c) as Hprop.
    { exists c. split; last by split.
      exists b. split; last by right.
      exists b. split; last by split.
      exists a. split; last by apply rt_step.
      exists d. split; first by split.
      right. destruct Hfre as [Hfr Hext]. split; [by right|done]. }
    assert (candidate_hb C d c) as Hback.
    { exists c. split; last by split. exists d. split; first by split.
      right. right. split; last done. split; done. }
    assert (candidate_hb C c d) as Hforward.
    { exists d. split; last by split. exists c. split; first by split.
      left. right. right. split.
      - left. right. right. exists d. split.
        + exists c. split; [by split|done].
        + split; first done. exists (data_read 0%Z). split; done.
      - unfold same_agent, same_attribute in *. naive_solver. }
    apply (Hacyclic c). eapply t_trans; apply t_step; eassumption.
  Qed.
  Lemma read_source C r t n mode loc val :
    core_candidate_wf C ->
    lookup_event C.(candidate_events) r =
      Some (EAgent t n (LMemory AccessRead mode NotRmw loc val)) ->
    exists w ev,
      lookup_event C.(candidate_events) w = Some ev /\ is_write ev /\
      location_of ev = Some loc /\ value_of ev = Some val /\
      rf C.(candidate_rf) w r.
  Proof.
    intros (_ & Hrf & _) Hr.
    destruct (rf_wf_total _ _ Hrf r _ Hr eq_refl) as [w Hwr].
    destruct (rf_wf_edge _ _ _ _ Hrf Hwr) as (ev & rev & v & Hw & Hread & Hwrite & _ & Hloc & Hv & Hrv).
    rewrite Hr in Hread. injection Hread as <-. cbn in Hrv. injection Hrv as <-.
    unfold same_location, same_attribute, execution.LkmmExecution.event_attribute in Hloc.
    rewrite Hw, Hr in Hloc. cbn in Hloc.
    exists w, ev. split_and!; try done. naive_solver.
  Qed.

  (** No restriction to a canonical graph, event-ID scheme, or interleaving. *)
  Theorem mp_release_acquire_forbidden C :
    program_graph (program StoreRelease LoadAcquire) C ->
    bad_outcome LoadAcquire C -> ~ lkmm_consistent C.
  Proof.
    intros Hprogram (c & d & Hc & Hd).
    destruct (program_writes _ _ _ Hprogram) as (a & b & Ha & Hb & Hw).
    pose proof (program_graph_wf _ _ Hprogram) as Hwf.
    destruct (program_graph_wf _ _ Hprogram) as (HE & HRF & HCO & Hrest).
    assert (rf C.(candidate_rf) b c) as Hbc.
    { destruct (read_source _ _ _ _ _ _ _ Hwf Hc) as (w & ev & Hwe & Hkind & Hloc & Hval & Hrf).
      destruct (Hw w ev Hwe Hkind) as [->|[->|[->| ->]]]; try discriminate.
      assert (w = b) as -> by (eapply HE; [exact Hwe|exact Hb]). done. }
    assert (exists i, lookup_event C.(candidate_events) i = Some (EInitWrite 0 0%Z) /\
      rf C.(candidate_rf) i d) as (i & Hi & Hid).
    { destruct (read_source _ _ _ _ _ _ _ Hwf Hd) as (w & ev & Hwe & Hkind & Hloc & Hval & Hrf).
      destruct (Hw w ev Hwe Hkind) as [->|[->|[->| ->]]]; try discriminate.
      exists w. split; done. }
    assert (co C.(candidate_co) i a) as Hia.
    { eapply (co_wf_initial_first _ _ HCO i a 0 data_write).
      - exists 0%Z. done.
      - done.
      - reflexivity.
      - eapply same_attribute_from_lookup; [exact Hi|exact Ha|reflexivity|reflexivity].
      - intros ->. rewrite Ha in Hi. discriminate. }
    eapply mp_cycle; [exact Ha|exact Hb|exact Hc|exact Hd| |].
    - split; first done. unfold ext, same_agent, same_attribute, execution.LkmmExecution.event_attribute.
      rewrite Hb, Hc. cbn. naive_solver.
    - split; first by exists i.
      unfold ext, same_agent, same_attribute, execution.LkmmExecution.event_attribute.
      rewrite Hd, Ha. cbn. naive_solver.
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
End MessagePassing.
