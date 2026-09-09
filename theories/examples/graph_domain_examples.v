From Stdlib Require Import List.
From stdpp Require Import gmap tactics.
From iris.base_logic.lib Require Import iprop.
From iris.proofmode Require Import proofmode.
From iris_lkmm.lkmm Require Import memory_relations rcu_graph.
From iris_lkmm.lang Require Import program_graph.
From iris_lkmm.logic Require Import graph_judgment.
From iris_lkmm.examples Require Import candidate_renaming_examples.
Import ListNotations.

Module GraphDomainExamples.
  Import LkmmGraphJudgment LkmmMemoryRelations RcuGraph.
  Module Sample := LkmmProgramGraph.ProgramGraphTests.
  Module Renaming := CandidateRenamingExamples.

  Module FutureSource.
    Definition after_read := add_single_event (core_initial_state Sample.program) 1
      (initial_thread Sample.reader)
      (LMemory AccessRead AccessOnce NotRmw 0 1%Z)
      {[0 := RegValue 1%Z {[1]}]} ∅ ∅ ∅.
    Definition final := add_single_event after_read 0 (initial_thread Sample.writer)
      (LMemory AccessWrite AccessOnce NotRmw 0 1%Z) ∅ ∅ ∅ ∅.
    Definition candidate := CoreCandidate Renaming.swapped_events
      {[(2, 1)]} {[(0, 2)]} ∅ ∅ ∅ ∅.
    Definition position := ExecutionPosition [CoreObserve 1 1%Z] after_read [CoreEmit 0] final.

    Lemma execution :
      candidate_execution Sample.program candidate [CoreObserve 1 1%Z; CoreEmit 0] final.
    Proof.
      split.
      - split.
        + econstructor.
          { eapply StepLoad; try reflexivity. by eexists. }
          econstructor.
          { eapply StepStore; try reflexivity. by eexists. }
          constructor.
        + intros agent thread Hlookup.
          destruct (decide (agent = 0)) as [-> | Hne0].
          * cbn in Hlookup. injection Hlookup as <-. done.
          * destruct (decide (agent = 1)) as [-> | Hne1].
            -- cbn in Hlookup. injection Hlookup as <-. done.
            -- cbn in Hlookup. simplify_map_eq.
      - split_and!; vm_compute; reflexivity.
    Qed.

    Lemma graph : program_graph Sample.program candidate.
    Proof.
      apply program_graph_execution. split.
      - eexists _, _. apply execution.
      - exact (proj1 Renaming.candidate_swap_wf_and_consistency).
    Qed.

    Local Lemma event_cases eid ev :
      lookup_event candidate.(candidate_events) eid = Some ev ->
      (eid = 0 /\ ev = Sample.init_write) \/
      (eid = 1 /\ ev = Sample.read) \/ (eid = 2 /\ ev = Sample.write).
    Proof.
      intros Hlookup. change (Renaming.swapped_events !! eid = Some ev) in Hlookup.
      unfold Renaming.swapped_events in Hlookup.
      apply lookup_insert_Some in Hlookup as [[Heid Hev] | [_ Hlookup]]; first naive_solver.
      apply lookup_insert_Some in Hlookup as [[Heid Hev] | [_ Hlookup]]; first naive_solver.
      apply lookup_singleton_Some in Hlookup. naive_solver.
    Qed.

    Local Lemma no_po x y : ~ po candidate.(candidate_events) x y.
    Proof.
      intros (t & i & j & l1 & l2 & Hx & Hy & Hlt).
      destruct (event_cases _ _ Hx) as [(-> & Hx') | [(-> & Hx') | (-> & Hx')]];
        destruct (event_cases _ _ Hy) as [(-> & Hy') | [(-> & Hy') | (-> & Hy')]];
        inversion Hx'; inversion Hy'; subst; lia.
    Qed.

    Local Lemma internal_eq x y : same_agent candidate.(candidate_events) x y -> x = y.
    Proof.
      intros (t & Hx & Hy).
      apply bind_Some in Hx as (ex & Hx & Htx).
      apply bind_Some in Hy as (ey & Hy & Hty).
      destruct (event_cases _ _ Hx) as [(-> & ->) | [(-> & ->) | (-> & ->)]];
        destruct (event_cases _ _ Hy) as [(-> & ->) | [(-> & ->) | (-> & ->)]];
        cbn in Htx, Hty; congruence.
    Qed.

    Local Lemma no_fr x y : ~ fr candidate.(candidate_rf) candidate.(candidate_co) x y.
    Proof. unfold fr, rel_seq, rel_inverse, rf, co, edge_relation, candidate. cbn. set_solver. Qed.

    Local Lemma no_internal_overwrite x y :
      ~ rel_intersection (overwrite candidate.(candidate_rf) candidate.(candidate_co))
          (same_agent candidate.(candidate_events)) x y.
    Proof.
      intros [Hedge Hint]. apply internal_eq in Hint. subst y.
      destruct Hedge as [Hco | Hfr]; last by eapply no_fr.
      unfold co, edge_relation, candidate in Hco. cbn in Hco. set_solver.
    Qed.

    Local Lemma no_fence x y : ~ fence candidate.(candidate_events) ∅ x y.
    Proof.
      unfold fence, nonrw_fence, strong_fence, mb, gp, po_rel, acq_po,
        rmb, wmb, fencerel, rel_union, rel_seq, rel_intersection, rel_id_on, optional.
      pose proof no_po. naive_solver.
    Qed.

    Local Lemma no_strong_fence x y : ~ strong_fence candidate.(candidate_events) ∅ x y.
    Proof.
      intros H. apply (no_fence x y). left. left. done.
    Qed.

    Local Lemma no_ppo x y :
      ~ ppo candidate.(candidate_events) ∅ candidate.(candidate_rf) candidate.(candidate_co)
          ∅ ∅ ∅ x y.
    Proof.
      assert (forall a b, ~ addr candidate.(candidate_events) candidate.(candidate_rf) ∅ ∅ a b)
        as Haddr by (unfold addr, rel_seq, direct_addr, edge_relation; set_solver).
      assert (forall a b, ~ data candidate.(candidate_events) candidate.(candidate_rf) ∅ a b)
        as Hdata by (unfold data, rel_seq, direct_data, edge_relation; set_solver).
      assert (forall a b, ~ ctrl candidate.(candidate_events) candidate.(candidate_rf) ∅ ∅ a b)
        as Hctrl by (unfold ctrl, rel_seq, direct_ctrl, edge_relation; set_solver).
      pose proof no_fence. pose proof no_internal_overwrite.
      unfold ppo, to_r, to_w, rwdep, dep, rel_union, rel_seq, rel_intersection in *.
      naive_solver.
    Qed.

    Definition rank (eid : event_id) : nat :=
      if decide (eid = 1) then 2 else if decide (eid = 2) then 1 else eid.

    Local Lemma rf_increases x y : rf candidate.(candidate_rf) x y -> rank x < rank y.
    Proof.
      intros H. unfold rf, edge_relation, candidate in H. cbn in H.
      assert (x = 2 /\ y = 1) as [-> ->] by set_solver.
      unfold rank. vm_compute. lia.
    Qed.

    Local Lemma coherence_increases x y :
      graph_coherence_order (core_candidate_graph candidate) x y -> rank x < rank y.
    Proof.
      intros [[Hpo _] | [Hrf | [Hco | Hfr]]].
      - by destruct (no_po _ _ Hpo).
      - by apply rf_increases.
      - unfold co, edge_relation, candidate in Hco. cbn in Hco.
        assert (x = 0 /\ y = 2) as [-> ->] by set_solver.
        unfold rank. vm_compute. lia.
      - by destruct (no_fr _ _ Hfr).
    Qed.

    Local Lemma hb_increases x y :
      graph_hb (core_candidate_graph candidate) x y -> rank x < rank y.
    Proof.
      intros H. apply rel_seq_id_on_r in H as [H _].
      apply rel_seq_id_on_l in H as [_ [Hppo | [[Hrf _] | [[_ Hne] Hint]]]].
      - by destruct (no_ppo _ _ Hppo).
      - by apply rf_increases.
      - destruct Hne. by apply internal_eq.
    Qed.

    Local Lemma no_pb x y : ~ graph_pb (core_candidate_graph candidate) x y.
    Proof.
      unfold graph_pb, pb, rel_seq. cbn.
      pose proof no_strong_fence. naive_solver.
    Qed.

    Local Lemma no_rb x y : ~ rb (core_candidate_graph candidate) x y.
    Proof.
      unfold rb, rcu_fence, graph_po, rel_seq. cbn.
      pose proof no_po. naive_solver.
    Qed.

    Local Lemma ranked_acyclic R :
      (forall x y, R x y -> rank x < rank y) -> rel_acyclic R.
    Proof.
      intros Hrank.
      assert (forall x y, tc R x y -> rank x < rank y) as Hpath.
      { intros x y H. induction H; first by apply Hrank. lia. }
      intros x H. specialize (Hpath x x H). lia.
    Qed.

    Lemma consistent : lkmm_consistent candidate.
    Proof.
      split_and!.
      - apply ranked_acyclic, coherence_increases.
      - intros x y [Hrmw _]. unfold rmw, edge_relation, candidate in Hrmw. cbn in Hrmw.
        set_solver.
      - apply ranked_acyclic, hb_increases.
      - apply ranked_acyclic. intros x y H. by destruct (no_pb _ _ H).
      - intros x H. by destruct (no_rb _ _ H).
    Qed.

    Example consistent_graph : consistent_program_graph Sample.program candidate.
    Proof. split; [apply graph | apply consistent]. Qed.

    Lemma at_read : candidate_position Sample.program candidate position.
    Proof.
      split.
      - econstructor; last constructor.
        eapply StepLoad with (dst := 0) (mode := LoadOnce) (address_sources := ∅);
          try reflexivity. by eexists.
      - split.
        + econstructor; last constructor.
          eapply StepStore with (mode := StoreOnce) (result := RegValue 1%Z ∅)
            (address_sources := ∅); try reflexivity. by eexists.
        + destruct execution as [[_ Hcomplete] Hmatch]. done.
    Qed.

    (** The source exists in the complete candidate but is absent from the
        current event map.  [consistent_graph] also proves this graph LKMM-consistent.
        This is a domain regression; it is not yet a WP load proof. *)
    Example source_need_not_have_been_emitted :
      candidate_position Sample.program candidate position /\
      rf candidate.(candidate_rf) 2 1 /\
      lookup_event after_read.(core_events) 2 = None /\
      lookup_event candidate.(candidate_events) 2 = Some Sample.write.
    Proof. split; first apply at_read. split; first set_solver. split; reflexivity. Qed.

    Example reader_and_writer_share_candidate :
      thread_at Sample.program candidate position 1
        (ThreadView (ThreadState SSkip [] {[0 := RegValue 1%Z {[1]}]})
          1 [CoreObserve 1 1%Z]) /\
      thread_at Sample.program candidate position 0
        (ThreadView (initial_thread Sample.writer) 0 []).
    Proof. split; (split; first apply at_read); reflexivity. Qed.

    Example register_provenance_is_retained :
      exists index label,
        lookup_event candidate.(candidate_events) 1 = Some (EAgent 1 index label) /\
        is_read (EAgent 1 index label) /\ index < 1.
    Proof.
      eapply (thread_at_register_origin Sample.program candidate position 1
        (ThreadView (ThreadState SSkip [] {[0 := RegValue 1%Z {[1]}]})
          1 [CoreObserve 1 1%Z]) 0 (RegValue 1%Z {[1]}) 1).
      - exact (proj1 reader_and_writer_share_candidate).
      - reflexivity.
      - set_solver.
    Qed.

    Example invented_dependency_rejects_position :
      ~ candidate_position Sample.program
        (CoreCandidate candidate.(candidate_events) candidate.(candidate_rf)
          candidate.(candidate_co) ∅ ∅ {[(1, 2)]} ∅) position.
    Proof.
      intros (_ & _ & _ & _ & _ & _ & Hdata & _).
      change ((∅ : edge_set) = {[(1, 2)]}) in Hdata. set_solver.
    Qed.
  End FutureSource.

  Module InitializedLoad.
    Definition program := CoreProgram {[0 := 0%Z]} {[0 := Sample.reader]}.
    Definition final observed := add_single_event (core_initial_state program) 0
      (initial_thread Sample.reader)
      (LMemory AccessRead AccessOnce NotRmw 0 observed)
      {[0 := RegValue observed {[1]}]} ∅ ∅ ∅.
    Definition candidate observed edges :=
      CoreCandidate (final observed).(core_events) edges ∅ ∅ ∅ ∅ ∅.

    Example arbitrary_value_is_still_a_raw_step :
      core_step program (core_initial_state program) (CoreObserve 0 42%Z) (final 42%Z).
    Proof.
      eapply StepLoad with (dst := 0) (mode := LoadOnce) (address_sources := ∅);
        try reflexivity. by eexists.
    Qed.

    (** No choice of rf can justify a different value.  This is a pure
        domain fact, without ghost ownership or an axiomatized load triple. *)
    Lemma only_initialized_value observed edges :
      program_graph program (candidate observed edges) -> observed = 0%Z.
    Proof.
      intros Hgraph. destruct (program_graph_wf _ _ Hgraph) as (_ & Hrf & _).
      destruct Hrf as (Hedges & _ & Htotal).
      destruct (Htotal 1 (EAgent 0 0
        (LMemory AccessRead AccessOnce NotRmw 0 observed)) eq_refl eq_refl) as (write & Hedge).
      destruct (Hedges write 1 Hedge) as
        (we & re & val & Hwrite & Hread & Hiswrite & _ & _ & Hwval & Hrval).
      change (Some (EAgent 0 0 (LMemory AccessRead AccessOnce NotRmw 0 observed)) = Some re)
        in Hread. injection Hread as <-.
      change (({[1 := EAgent 0 0 (LMemory AccessRead AccessOnce NotRmw 0 observed);
        0 := EInitWrite 0 0%Z]} : event_structure) !! write = Some we) in Hwrite.
      apply lookup_insert_Some in Hwrite as [[Heid Heq] | [_ Hwrite]].
      - subst we. done.
      - apply lookup_singleton_Some in Hwrite as [Heid Heq]. subst we.
        cbn in Hwval, Hrval. congruence.
    Qed.

    Example forty_two_has_no_program_graph edges :
      ~ program_graph program (candidate 42%Z edges).
    Proof. intros Hgraph. discriminate (only_initialized_value _ _ Hgraph). Qed.
  End InitializedLoad.

  (** A projection regression: silent actions count as proof positions,
      but do not invent events.  The continuation is retained verbatim. *)
  Example silent_action_view :
    let P := CoreProgram ∅ {[0 := SSeq SSkip SSkip]} in
    let s := update_thread (core_initial_state P) 0 (ThreadState SSkip [KSeq SSkip] ∅) in
    let final := update_thread s 0 (ThreadState SSkip [] ∅) in
    let p := ExecutionPosition [CoreSilent 0] s [CoreSilent 0] final in
    candidate_position P (CoreCandidate ∅ ∅ ∅ ∅ ∅ ∅ ∅) p /\
    project_thread p 0 = Some (ThreadView (ThreadState SSkip [KSeq SSkip] ∅) 0 [CoreSilent 0]).
  Proof.
    intros P s final p. split; last reflexivity. split.
    - econstructor; last constructor.
      by eapply StepSequence with (thread := initial_thread (SSeq SSkip SSkip)).
    - split.
      + econstructor; last constructor.
        by eapply StepSkipSequence with (thread := ThreadState SSkip [KSeq SSkip] ∅).
      + split.
        * intros agent thread Hlookup.
          change (({[0 := ThreadState SSkip [] ∅]} : gmap agent_id thread_state) !! agent = Some thread)
            in Hlookup. apply lookup_singleton_Some in Hlookup as [Heq <-]. done.
        * split_and!; reflexivity.
  Qed.

  Section quantification.
    Context {Σ : gFunctors}.

    Example every_position_retains_its_events P :
      ⊢ all_candidate_positions (Σ := Σ) P (fun G p =>
        ⌜event_structure_included p.(position_state).(core_events) G.(candidate_events)⌝).
    Proof.
      iIntros (G HG p Hpos). iPureIntro. by eapply candidate_position_events.
    Qed.

    Example quantification_covers_future_source Ψ :
      all_candidate_positions (Σ := Σ) Sample.program Ψ ⊢
        Ψ FutureSource.candidate FutureSource.position.
    Proof.
      apply all_candidate_positions_elim.
      - apply FutureSource.consistent_graph.
      - apply FutureSource.at_read.
    Qed.
  End quantification.
End GraphDomainExamples.
