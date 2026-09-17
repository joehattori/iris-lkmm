From Stdlib Require Import List.
From iris.base_logic.lib Require Import fancy_updates ghost_var.
From iris.proofmode Require Import proofmode.
From iris_lkmm.lkmm Require Import memory_relations.
From iris_lkmm.operational Require Import lkmm_machine lkmm_operational.
From iris_lkmm.logic Require Import graph_correspondence state_interp wp wp_parallel wp_memory adequacy.
From iris_lkmm.examples Require Import wp_parallel_examples.
Import ListNotations.

Module AdequacyExamples.
  Import LkmmMachine LkmmOperational LkmmGraphCorrespondence.
  Import LkmmMemoryRelations.
  Import LkmmStateInterp LkmmWp LkmmWpParallel LkmmWpMemory LkmmAdequacy.
  Module Assign := WpParallelExamples.

  Definition adequacyΣ : gFunctors := #[invΣ; stateΣ; ghost_varΣ nat].

  Definition assignment_result (_ : list lkmm_action) final : Prop :=
    final.(lkmm_machine).(machine_core).(core_threads) !! 0 =
      Some (Assign.result_thread 42) /\
    final.(lkmm_machine).(machine_core).(core_threads) !! 1 =
      Some (Assign.result_thread 7).

  (** Setup allocates a client resource before the candidate is supplied.
      Half travels through agent 0's WP and half stays in the extraction rule. *)
  Lemma assignment_program_proof `{!invGS Σ, !stateG Σ, !ghost_varG Σ nat} :
    ⊢ completed_program_wp Assign.program assignment_result.
  Proof.
    iIntros (γ) "_".
    iMod (ghost_var_alloc (42 : nat)) as (δ) "[Hagent Hkeep]".
    iModIntro. iIntros (G HG).
    iExists (Assign.post (ghost_var δ (1/2) 42) True).
    iSplitL "Hagent".
    { iApply Assign.assignment_wps. by iFrame. }
    iIntros (actions final) "_ [_ Hposts]".
    iDestruct (big_sepM_delete _ _ 0 with "Hposts") as "[H0 Hposts]"; first reflexivity.
    iDestruct (big_sepM_lookup _ _ 1 with "Hposts") as "H1"; first reflexivity.
    iDestruct "H0" as (v0) "(%Hview0 & %Hv0 & Hagent)".
    iDestruct "H1" as (v1) "(%Hview1 & %Hv1 & _)".
    iCombine "Hagent Hkeep" as "Hfull".
    iMod (ghost_var_update 0 with "Hfull") as "_".
    subst v0 v1. iApply fupd_mask_intro_discard; first set_solver.
    iPureIntro. split.
    - exact (lookup_lkmm_thread_view_lookup _ _ _ Hview0).
    - exact (lookup_lkmm_thread_view_lookup _ _ _ Hview1).
  Qed.

  (** A pure result for every accepted schedule, obtained through adequacy. *)
  Theorem assignments_adequate actions final :
    lkmm_run Assign.program (initial_lkmm Assign.program) actions final ->
    lkmm_complete final -> lkmm_program_graph_obligations final ->
    assignment_result actions final.
  Proof.
    apply (wp_adequacy (Σ := adequacyΣ)).
    intros Hinv. apply assignment_program_proof.
  Qed.

  Example interleaved_assignments_result : assignment_result Assign.interleaving Assign.finished.
  Proof.
    destruct Assign.interleaved_position as (_ & Hrun & Hcomplete & Hobligations & _).
    by apply assignments_adequate.
  Qed.

  Definition idle_program := CoreProgram ∅ {[0 := SSkip]}.
  Definition idle_result (_ : list lkmm_action) final : Prop :=
    final.(lkmm_machine).(machine_core).(core_threads) !! 0 = Some (initial_thread SSkip).

  Lemma idle_program_proof `{!invGS Σ, !stateG Σ} :
    ⊢ completed_program_wp idle_program idle_result.
  Proof.
    iIntros (γ) "_". iModIntro. iIntros (G HG).
    iExists (fun _ v => ⌜v = initial_thread_view SSkip⌝%I). iSplitL.
    { iApply big_sepM_singleton. rewrite wp_unfold /wp_body /=. by iModIntro. }
    iIntros (actions final) "_ [_ Hposts]".
    iDestruct (big_sepM_lookup _ _ 0 with "Hposts") as (v) "[%Hview %Hv]"; first reflexivity.
    subst v. iApply fupd_mask_intro_discard; first set_solver.
    iPureIntro. exact (lookup_lkmm_thread_view_lookup _ _ _ Hview).
  Qed.

  (** The zero-step case still has to discharge initialization and final
      updates; there is no operational step available to hide a later. *)
  Example zero_step_result : idle_result [] (initial_lkmm idle_program).
  Proof.
    eapply (wp_adequacy (Σ := adequacyΣ)); first (intros Hinv; apply idle_program_proof).
    - constructor.
    - split.
      + split; last (split; first reflexivity; split; reflexivity).
        intros agent thread Hlookup.
        cbn in Hlookup. rewrite map_fmap_singleton in Hlookup.
        apply lookup_singleton_Some in Hlookup as [_ <-]. done.
      + split_and!; reflexivity.
    - unfold lkmm_program_graph_obligations, rf_wf, rf_functional, rf_total,
        co_wf, co_irreflexive, co_transitive, co_total, initial_writes_exist,
        initial_writes_unique, co_initial_first, initial_write_at, location_used,
        event_has_location, rf, co, edge_relation. cbn.
      split_and!; intros; set_solver.
  Qed.

  Definition store_body := SStore StoreOnce (EConst 0) (EConst 42).
  Definition store_program := CoreProgram {[0 := 0%Z]} {[0 := store_body]}.
  Definition stored_event := EAgent 0 0 (LMemory AccessWrite AccessOnce NotRmw 0 42%Z).
  Definition store_result (_ : list lkmm_action) final : Prop :=
    exists write, lookup_event final.(lkmm_machine).(machine_core).(core_events) write =
      Some stored_event.

  (** Initial memory pays for the store. The final interpretation connects
      its returned event fact to the actual emitted event structure. *)
  Lemma store_program_proof `{!invGS Σ, !stateG Σ} :
    ⊢ completed_program_wp store_program store_result.
  Proof.
    iIntros (γ) "[_ Hmemory]".
    iDestruct (big_sepM_lookup _ _ 0 with "Hmemory") as "Hloc"; first reflexivity.
    iModIntro. iIntros (G HG).
    iExists (fun _ _ => ∃ write, event_fact γ write stored_event)%I. iSplitL "Hloc".
    - iApply big_sepM_singleton. iApply (wp_store with "Hloc"); try reflexivity.
      iNext. iIntros (write) "_ Hwrite".
      rewrite wp_unfold /wp_body /memory_view /=. iModIntro. by iExists write.
    - iIntros (actions final) "_ [Hstate Hposts]".
      iDestruct (big_sepM_lookup _ _ 0 with "Hposts") as (v) "[_ Hwrite]"; first reflexivity.
      iDestruct "Hwrite" as (write) "Hwrite".
      iDestruct (state_interp_event with "Hstate Hwrite") as %Hwrite.
      iApply fupd_mask_intro_discard; first set_solver. iPureIntro. by exists write.
  Qed.

  Theorem store_adequate actions final :
    lkmm_run store_program (initial_lkmm store_program) actions final ->
    lkmm_complete final -> lkmm_program_graph_obligations final ->
    store_result actions final.
  Proof.
    apply (wp_adequacy (Σ := adequacyΣ)). intros Hinv. apply store_program_proof.
  Qed.
End AdequacyExamples.
