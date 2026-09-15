From Stdlib Require Import List.
From iris.base_logic.lib Require Import invariants fancy_updates.
From iris.proofmode Require Import proofmode.
From iris_lkmm.logic Require Import memory_ghost wp_memory wp_parallel.
From iris_lkmm.lang Require Import program_graph.
From iris_lkmm.operational Require Import lkmm_machine.
From iris_lkmm.lkmm Require Import memory_relations.
From iris_lkmm.examples Require Import graph_domain_examples graph_correspondence_examples.
Import ListNotations.

Module MemoryOwnershipExamples.
  Import LkmmMemoryGhost LkmmWpMemory LkmmWpParallel LkmmMachine LkmmMemoryRelations.
  Module Future := GraphDomainExamples.FutureSource.
  Module Sample := LkmmProgramGraph.ProgramGraphTests.

  Definition initial_history : event_structure := {[0 := Sample.init_write]}.

  Module FailedCmpxchg.
    Definition body := SCmpxchg 0 RmwAcquire (EConst 0) (EConst 1) (EConst 2).
    Definition program := CoreProgram {[0 := 0%Z]} {[0 := body]}.
    Definition read_event := EAgent 0 0 (LMemory AccessRead AccessAcquire RmwMarked 0 0%Z).
    Definition after := CoupledState
      (with_core (initial_state program)
        (add_single_event (core_initial_state program) 0 (initial_thread body)
          (LMemory AccessRead AccessAcquire RmwMarked 0 0%Z)
          {[0 := RegValue 0%Z {[1]}]} ∅ ∅ ∅)) (initial_coupled program).(coupled_builder).

    Lemma step : coupled_step program (initial_coupled program)
      (CoupledMachineAction (Execute (CoreObserve 0 0%Z))) after.
    Proof.
      apply CoupledStepMachine. eapply StepCore; try done.
      eapply StepCmpxchgFailure with (dst := 0) (mode := RmwAcquire)
        (address := EConst 0) (expected := EConst 1) (desired := EConst 2)
        (expected_result := RegValue 1%Z ∅) (desired_result := RegValue 2%Z ∅);
        try done. by eexists.
    Qed.
  End FailedCmpxchg.

  Section resources.
    Context `{!invGS Σ, !stateG Σ}.

    Example future_write_cannot_be_owned_as_emitted γ b q :
      state_interp γ (CoupledState (State Future.after_read ∅ []) b) -∗
      memory_own γ.(memory_names_of) 0 q (<[2 := Sample.write]> initial_history) -∗ False.
    Proof.
      iIntros "Hstate Hloc".
      iDestruct (state_interp_memory with "Hstate Hloc") as %Hhistory.
      apply (f_equal (fun history => history !! 2)) in Hhistory.
      vm_compute in Hhistory. discriminate.
    Qed.

    (** Failure emits only a marked read: both existing halves survive and
        the history still contains just the initialized write. *)
    Example failed_cmpxchg_preserves_shares :
      ⊢ |==> ∃ γ, state_interp γ FailedCmpxchg.after ∗
        memory_own γ.(memory_names_of) 0 (1/2) initial_history ∗
        memory_own γ.(memory_names_of) 0 (1/2) initial_history ∗
        event_fact γ 1 FailedCmpxchg.read_event.
    Proof.
      iMod (state_interp_alloc_memory FailedCmpxchg.program)
        as (γ) "(Hstate & Hthreads & _ & Hlocations)".
      iDestruct (big_sepM_lookup _ _ 0 with "Hthreads") as "Hthread"; first reflexivity.
      iDestruct (big_sepM_lookup _ _ 0 with "Hlocations") as "Hloc"; first reflexivity.
      iDestruct "Hloc" as "[Hleft Hright]".
      iMod (state_interp_execute _ _ _ _ _ _ _ FailedCmpxchg.step
        with "[$Hstate $Hthread]") as "(Hrestore & Hmemory & Hthread & #Hnew)"; try done.
      { apply core_initial_allocation_wf. }
      iDestruct (memory_auth_read _ _ 1 FailedCmpxchg.read_event with "Hmemory") as "Hmemory"; try done.
      iDestruct ("Hrestore" with "Hmemory") as "Hstate".
      iDestruct (big_sepM_lookup _ _ 1 with "Hnew") as "#Hread"; first reflexivity.
      change (write_history (core_initial_events FailedCmpxchg.program) 0) with initial_history.
      iModIntro. iExists γ. iFrame "Hstate Hleft Hright Hread".
    Qed.

    Definition shared_memory γ N : iProp Σ :=
      inv N (∃ history, memory_own γ.(memory_names_of) 0 1 history).

    Definition reader_post γ (v : coupled_thread_view) : iProp Σ :=
      ⌜v.(coupled_view_core).(view_thread).(thread_registers) !! 0 =
        Some (RegValue 1%Z {[1]})⌝ ∗ event_fact γ 1 Sample.read.

    Definition writer_post γ (_ : coupled_thread_view) : iProp Σ :=
      ∃ write, event_fact γ write Sample.write.

    Lemma shared_reader γ E N :
      ↑N ⊆ E -> shared_memory γ N -∗
      wp Sample.program Future.candidate γ E 1 (initial_thread_view Sample.reader) (reader_post γ).
    Proof.
      intros Hmask. iIntros "#Hinv". iApply (wp_load_acc _ _ _ _ (E ∖ ↑N)); first reflexivity.
      iNext. iInv N as (history) ">Hloc" "Hclose".
      iDestruct "Hloc" as "[Hload Hkeep]".
      iModIntro. iExists (1/2)%Qp, history. iFrame "Hload".
      iIntros (read observed source) "%Hsource Hload #Hread".
      iMod ("Hclose" with "[Hload Hkeep]") as "_".
      { iNext. iExists history. iCombine "Hload Hkeep" as "$". }
      destruct Hsource as [Hrf (ev & Hlookup & _ & _ & Hvalue)].
      assert (source = 2 /\ read = 1) as [-> ->].
      { unfold rf, edge_relation, Future.candidate in Hrf. cbn in Hrf. set_solver. }
      change (Some Sample.write = Some ev) in Hlookup. injection Hlookup as <-.
      cbn in Hvalue. injection Hvalue as <-.
      iModIntro. rewrite wp_unfold /wp_body /reader_post /memory_view /=.
      iModIntro. iFrame "Hread". done.
    Qed.

    Lemma shared_writer γ E N :
      ↑N ⊆ E -> shared_memory γ N -∗
      wp Sample.program Future.candidate γ E 0 (initial_thread_view Sample.writer) (writer_post γ).
    Proof.
      intros Hmask. iIntros "#Hinv". iApply (wp_store_acc _ _ _ _ (E ∖ ↑N)); try done.
      iNext. iInv N as (history) ">Hloc" "Hclose".
      iModIntro. iExists history. iFrame "Hloc". iIntros (write) "Hloc #Hwrite".
      iMod ("Hclose" with "[Hloc]") as "_".
      { iNext. iExists _. iExact "Hloc". }
      iModIntro. rewrite wp_unfold /wp_body /writer_post /memory_view /=.
      iModIntro. iExists write. iExact "Hwrite".
    Qed.

    Definition parallel_post γ agent :=
      if decide (agent = 0) then writer_post γ else reader_post γ.

    (** Resources are allocated from the program. The invariant lends and
        recovers ownership independently at each agent's scheduled step.
        [GraphCorrespondenceExamples.future_source_coupled_cut] witnesses
        the read-before-write schedule. The reader uses half the share. *)
    Example parallel_future_read E N actions final :
      ↑N ⊆ E ->
      coupled_position Sample.program Future.candidate
        (CoupledExecutionPosition [] (initial_coupled Sample.program) actions final) ->
      ⊢ |={E}=> ∃ γ, |={E}[∅]▷=>^(length actions) |={E}=>
        state_interp γ final ∗
        ⌜exists thread, final.(coupled_machine).(machine_core).(core_threads) !! 1 = Some thread /\
          thread.(thread_registers) !! 0 = Some (RegValue 1%Z {[1]})⌝ ∗
        event_fact γ 1 Sample.read ∗ (∃ write, event_fact γ write Sample.write).
    Proof.
      intros Hmask Hpos.
      iMod (state_interp_alloc_memory Sample.program) as (γ) "(Hstate & Htokens & _ & Hlocations)".
      iDestruct (big_sepM_lookup _ _ 0 with "Hlocations") as "Hloc"; first reflexivity.
      iMod (inv_alloc N _ (∃ history, memory_own γ.(memory_names_of) 0 1 history)
        with "[Hloc]") as "#Hinv".
      { iNext. iExists _. iExact "Hloc". }
      iAssert ([∗ map] agent ↦ body ∈ Sample.program.(program_agents),
        wp Sample.program Future.candidate γ E agent (initial_thread_view body)
          (parallel_post γ agent))%I with "[]" as "Hwps".
      { iApply big_sepM_insert; first reflexivity. iSplitL.
        - iApply shared_writer; done.
        - iApply big_sepM_singleton. iApply shared_reader; done. }
      iPoseProof (wp_parallel_init _ _ _ _ actions final (parallel_post γ)
        with "Htokens Hwps") as "Hpool".
      iPoseProof (wp_parallel_run_post _ _ _ _ _ _ _ _ _ Hpos with "[$Hstate $Hpool]") as "Hrun".
      iModIntro. iExists γ. iApply (step_fupdN_wand with "Hrun").
      iIntros ">[Hstate Hposts]".
      iDestruct (big_sepM_delete _ _ 0 with "Hposts") as "[Hwriter Hposts]"; first reflexivity.
      iDestruct (big_sepM_lookup _ _ 1 with "Hposts") as "Hreader"; first reflexivity.
      iDestruct "Hwriter" as (vw) "(_ & Hwrite)".
      iDestruct "Hreader" as (vr) "(%Hview & %Hreg & Hread)".
      iModIntro. iFrame "Hstate Hread Hwrite". iPureIntro.
      exists vr.(coupled_view_core).(view_thread). split; last done.
      exact (lookup_coupled_thread_view_lookup _ _ _ Hview).
    Qed.
  End resources.
End MemoryOwnershipExamples.
