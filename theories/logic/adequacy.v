From Stdlib Require Import List.
From iris.base_logic.lib Require Import fancy_updates.
From iris.proofmode Require Import proofmode.
From iris_lkmm.operational Require Import lkmm_machine lkmm_operational.
From iris_lkmm.logic Require Import graph_correspondence graph_judgment state_interp wp wp_parallel.
Import ListNotations.

Module LkmmAdequacy.
  Import LkmmMachine LkmmOperational LkmmGraphCorrespondence LkmmGraphJudgment.
  Import LkmmStateInterp LkmmWp LkmmWpParallel.

  Section program_proof.
    Context `{!invGS Σ, !stateG Σ}.

    (** The execution retains the state interpretation and thread tokens.
        Clients receive exactly the initialized event facts and memory. *)
    Definition initial_resources P γ : iProp Σ :=
      ([∗ map] eid ↦ ev ∈ core_initial_events P, event_fact γ eid ev) ∗
      ([∗ map] loc ↦ val ∈ P.(program_initial_memory),
        memory_own γ.(memory_names_of) loc 1
          (write_history (core_initial_events P) loc)).

    Definition agent_wps_at P G γ E
        (Φ : agent_id -> lkmm_thread_view -> iProp Σ) : iProp Σ :=
      [∗ map] agent ↦ body ∈ P.(program_agents),
        wp P G γ E agent (initial_thread_view body) (Φ agent).

    Definition agent_wps P G γ := agent_wps_at P G γ ⊤.

    Definition final_posts P
        (Φ : agent_id -> lkmm_thread_view -> iProp Σ) actions final : iProp Σ :=
      [∗ map] agent ↦ body ∈ P.(program_agents),
        ∃ v, ⌜lookup_lkmm_thread_view
          (LkmmExecutionPosition actions final [] final) agent = Some v⌝ ∗
          Φ agent v.

    (** Setup precedes candidate selection. Each candidate supplies one WP
        per agent and an extraction rule for every accepted trace and final
        state. The extraction rule may retain resources alongside the WPs. *)
    Definition program_wp
        P E (Q : list lkmm_action -> lkmm_state -> iProp Σ) : iProp Σ :=
      (∀ γ, initial_resources P γ ={E}=∗
        all_candidates P (fun G =>
          ∃ Φ : agent_id -> lkmm_thread_view -> iProp Σ,
            agent_wps_at P G γ E Φ ∗
            (∀ actions final,
              ⌜lkmm_position P G (LkmmExecutionPosition actions final [] final)⌝ -∗
              state_interp γ final ∗ final_posts P Φ actions final
              ={E,∅}=∗ Q actions final)))%I.

    (** The existing adequacy interface is the pure-postcondition instance. *)
    Definition completed_program_wp
        P (Q : list lkmm_action -> lkmm_state -> Prop) : iProp Σ :=
      program_wp P ⊤ (fun actions final => ⌜Q actions final⌝)%I.

    (** Move the mask changes between steps into the surrounding update,
        so generic Iris soundness can consume the guards at the empty mask. *)
    Local Lemma step_fupdN_extract E n (R : iProp Σ) :
      (|={E}[∅]▷=>^n |={E,∅}=> R) -∗
      |={E,∅}=> |={∅}▷=>^n |={∅}=> R.
    Proof.
      induction n as [|n IH]; simpl; iIntros "H".
      - by iMod "H" as "$".
      - iMod "H" as "H". iModIntro. iModIntro. iNext.
        iMod "H" as "H". by iApply IH.
    Qed.
  End program_proof.

  (** External partial correctness for the supplied completed execution.
      No prefix-safety, termination, or GP-liveness premise is used. *)
  Theorem wp_adequacy {Σ : gFunctors} `{!invGpreS Σ, !stateG Σ}
      P (Q : list lkmm_action -> lkmm_state -> Prop) :
    (forall `{!invGS Σ}, ⊢ completed_program_wp P Q) ->
    forall actions final,
      lkmm_run P (initial_lkmm P) actions final ->
      lkmm_complete final ->
      lkmm_program_graph_obligations final ->
      Q actions final.
  Proof.
    intros Hwp actions final Hrun Hcomplete Hobligations.
    assert (lkmm_position P (lkmm_candidate final)
      (LkmmExecutionPosition [] (initial_lkmm P) actions final)) as Hinitial.
    { split; first constructor. split_and!; done. }
    assert (lkmm_position P (lkmm_candidate final)
      (LkmmExecutionPosition actions final [] final)) as Hfinal.
    { split; first done. split; first constructor. split_and!; done. }
    apply (pure_soundness (PROP := iPropI Σ)).
    eapply (step_fupdN_soundness_lc _ (length actions) 0).
    iIntros (Hinv) "_".
    iMod (state_interp_alloc_memory P) as (γ) "(Hstate & Htokens & Hfacts & Hmemory)".
    iMod (Hwp Hinv $! γ with "[$Hfacts $Hmemory]") as "Hclient".
    iDestruct (all_candidates_elim with "Hclient") as (Φ) "[Hwps Hfinish]".
    { by eapply lkmm_run_soundness. }
    iPoseProof (wp_parallel_init P (lkmm_candidate final) γ ⊤ actions final Φ
      with "Htokens Hwps") as "Hpool".
    iPoseProof (wp_parallel_run_post _ _ _ _ _ _ _ _ _ Hinitial
      with "[$Hstate $Hpool]") as "Hposts".
    iAssert (|={⊤}[∅]▷=>^(length actions) |={⊤,∅}=> ⌜Q actions final⌝)%I
      with "[Hposts Hfinish]" as "Hresult".
    { iApply (step_fupdN_wand with "Hposts"). iIntros ">[Hstate Hposts]".
      iApply ("Hfinish" $! actions final with "[] [$Hstate $Hposts]"); done. }
    iMod (step_fupdN_extract with "Hresult") as "Hresult".
    destruct (length actions) as [|n].
    { by iMod "Hresult". }
    iModIntro. by iApply step_fupdN_S_fupd.
  Qed.
End LkmmAdequacy.
