From Stdlib Require Import List.
From iris.base_logic.lib Require Import fancy_updates.
From iris.proofmode Require Import proofmode.
From iris_lkmm.lkmm Require Import memory_relations.
From iris_lkmm.operational Require Import lkmm_machine lkmm_operational rcu_builder.
From iris_lkmm.logic Require Import graph_correspondence state_interp wp wp_parallel.
Import ListNotations.

Module WpParallelExamples.
  Import LkmmMachine LkmmOperational RcuBuilder LkmmGraphCorrespondence.
  Import LkmmStateInterp LkmmWp LkmmWpParallel LkmmMemoryRelations.

  Definition increment := SAssign 0 (EBin OpAdd (EReg 0) (EConst 2)).
  Definition first := SSeq (SAssign 0 (EConst 40)) increment.
  Definition second := SAssign 0 (EConst 7).
  Definition program := CoreProgram ∅ {[0 := first; 1 := second]}.
  Definition graph := CoreCandidate ∅ ∅ ∅ ∅ ∅ ∅ ∅.
  Definition result_thread value := ThreadState SSkip [] {[0 := RegValue value ∅]}.
  Definition result_view agent value steps := LkmmThreadView
    (ThreadView (result_thread value) 0 (replicate steps (CoreSilent agent))) None.

  Definition finished := LkmmState
    (State (CoreState {[0 := result_thread 42; 1 := result_thread 7]} 0 ∅ ∅ ∅ ∅ ∅ ∅) ∅ [])
    initial_builder.
  Definition interleaving := [LkmmMachineAction (Execute (CoreSilent 0));
    LkmmMachineAction (Execute (CoreSilent 1));
    LkmmMachineAction (Execute (CoreSilent 0));
    LkmmMachineAction (Execute (CoreSilent 0));
    LkmmMachineAction (Execute (CoreSilent 0))].

  (** Agent 1 completes between agent 0's sequence entry and first assignment.
      This concrete witness also establishes that the tested domain is inhabited. *)
  Example interleaved_position :
    lkmm_position program graph
      (LkmmExecutionPosition [] (initial_lkmm program) interleaving finished).
  Proof.
    split; first constructor. split.
    - econstructor.
      { apply LkmmStepMachine. eapply StepCore; [reflexivity | done | reflexivity |].
        eapply StepSequence; reflexivity. }
      econstructor.
      { apply LkmmStepMachine. eapply StepCore; [reflexivity | done | reflexivity |].
        eapply StepAssign; reflexivity. }
      econstructor.
      { apply LkmmStepMachine. eapply StepCore; [reflexivity | done | reflexivity |].
        eapply StepAssign; reflexivity. }
      econstructor.
      { apply LkmmStepMachine. eapply StepCore; [reflexivity | done | reflexivity |].
        eapply StepSkipSequence; reflexivity. }
      econstructor.
      { apply LkmmStepMachine. eapply StepCore; [reflexivity | done | reflexivity |].
        eapply StepAssign; reflexivity. }
      constructor.
    - split.
      + split.
        * split; last (split; first reflexivity; split; reflexivity).
          intros agent thread Hlookup. cbn in Hlookup.
          apply lookup_insert_Some in Hlookup as [[<- <-] | [_ Hlookup]]; first done.
          apply lookup_singleton_Some in Hlookup as [<- <-]. done.
        * split_and!; reflexivity.
      + split; last reflexivity.
        unfold lkmm_program_graph_obligations, rf_wf, rf_functional, rf_total,
          co_wf, co_irreflexive, co_transitive, co_total, initial_writes_exist,
          initial_writes_unique, co_initial_first, initial_write_at, location_used, event_has_location,
          rf, co, edge_relation. cbn.
        split_and!; intros; set_solver.
  Qed.

  Section proof.
    Context `{!invGS Σ, !stateG Σ}.

    Definition post (R0 R1 : iProp Σ) agent v : iProp Σ :=
      (if decide (agent = 0) then ⌜v = result_view 0 42 4⌝ ∗ R0
      else ⌜v = result_view 1 7 1⌝ ∗ R1)%I.

    Lemma assignment_wps G γ E (R0 R1 : iProp Σ) :
      R0 ∗ R1 -∗
      [∗ map] agent ↦ body ∈ program.(program_agents),
        wp program G γ E agent (initial_thread_view body) (post R0 R1 agent).
    Proof.
      iIntros "[HR0 HR1]". iApply big_sepM_insert; first reflexivity. iSplitL "HR0".
      - iApply wp_seq. iNext. iApply wp_assign; first reflexivity.
        iNext. iApply wp_skip_seq. iNext. iApply wp_assign; first reflexivity.
        iNext. rewrite wp_unfold /wp_body /post /result_view /result_thread /=.
        iModIntro. iFrame. iPureIntro. by rewrite insert_insert_eq.
      - iApply big_sepM_singleton. iApply wp_assign; first reflexivity.
        iNext. rewrite wp_unfold /wp_body /post /result_view /result_thread /=.
        iModIntro. iFrame. done.
    Qed.

    (** Each local proof receives its own resource. Composition follows any
        accepted schedule and returns both results, even if an agent ended early. *)
    Example parallel_assignments E actions final (R0 R1 : iProp Σ) :
      lkmm_position program graph
        (LkmmExecutionPosition [] (initial_lkmm program) actions final) ->
      R0 ∗ R1 -∗ |={E}=> ∃ γ,
        |={E}[∅]▷=>^(length actions) |={E}=>
          state_interp γ final ∗ R0 ∗ R1 ∗
          ⌜final.(lkmm_machine).(machine_core).(core_threads) !! 0 = Some (result_thread 42) /\
            final.(lkmm_machine).(machine_core).(core_threads) !! 1 = Some (result_thread 7)⌝.
    Proof.
      intros Hpos. iIntros "[HR0 HR1]".
      iMod (state_interp_alloc program) as (γ) "(Hstate & Htokens & _)".
      iPoseProof (assignment_wps graph γ E R0 R1 with "[$HR0 $HR1]") as "Hwps".
      iPoseProof (wp_parallel_init program graph γ E actions final (post R0 R1)
        with "Htokens Hwps") as "Hpool".
      iPoseProof (wp_parallel_run_post _ _ _ _ _ _ _ _ _ Hpos with "[$Hstate $Hpool]") as "Hrun".
      iModIntro. iExists γ. iApply (step_fupdN_wand with "Hrun").
      iIntros ">[Hstate Hposts]".
      iDestruct (big_sepM_delete _ _ 0 with "Hposts") as "[H0 Hposts]"; first reflexivity.
      iDestruct (big_sepM_lookup _ _ 1 with "Hposts") as "H1"; first reflexivity.
      iDestruct "H0" as (v0) "(%Hview0 & %Hv0 & HR0)".
      iDestruct "H1" as (v1) "(%Hview1 & %Hv1 & HR1)".
      subst v0 v1. iModIntro. iFrame. iPureIntro. split.
      - exact (lookup_lkmm_thread_view_lookup _ _ _ Hview0).
      - exact (lookup_lkmm_thread_view_lookup _ _ _ Hview1).
    Qed.
  End proof.
End WpParallelExamples.
