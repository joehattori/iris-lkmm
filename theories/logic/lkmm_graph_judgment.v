From iris.base_logic.lib Require Import iprop.
From iris.proofmode Require Import proofmode.
From iris_lkmm.logic Require Import graph_judgment graph_correspondence.

Module LkmmOperationalGraphJudgment.
  Export LkmmGraphJudgment LkmmGraphCorrespondence.

  Section judgments.
    Context {Σ : gFunctors}.

    (** Keep the operational witness available for assertions about actions,
        pending GPs, certificates, or builder state that Core projection loses. *)
    Definition all_lkmm_positions (P : core_program)
        (Ψ : core_candidate -> lkmm_execution_position -> iProp Σ) : iProp Σ :=
      all_candidates P (fun G => ∀ p, ⌜lkmm_position P G p⌝ -∗ Ψ G p)%I.

    Lemma all_lkmm_positions_elim P Ψ G p :
      lkmm_position P G p -> all_lkmm_positions P Ψ ⊢ Ψ G p.
    Proof.
      iIntros (Hpos) "H".
      iDestruct (all_candidates_elim with "H") as "H";
        first by eapply lkmm_position_consistent_program_graph.
      by iApply ("H" $! p).
    Qed.

    (** Logical specialization of the proved projection, not WP adequacy. *)
    Lemma candidate_positions_cover_lkmm P Ψ :
      all_candidate_positions P Ψ ⊢
      all_lkmm_positions P (fun G p => Ψ G (lkmm_position_to_core p)).
    Proof.
      iIntros "H". iIntros (G HG p Hpos).
      iApply (all_candidate_positions_elim with "H"); first done.
      by apply lkmm_position_projection.
    Qed.

    Lemma all_lkmm_positions_at_run_end P Ψ actions final :
      lkmm_run P (initial_lkmm P) actions final ->
      lkmm_complete final -> lkmm_program_graph_obligations final ->
      all_lkmm_positions P Ψ ⊢
        Ψ (lkmm_candidate final) (LkmmExecutionPosition actions final nil final).
    Proof.
      intros Hrun Hcomplete Hobligations. apply all_lkmm_positions_elim.
      split; first done. split; first constructor. split_and!; done.
    Qed.
  End judgments.
End LkmmOperationalGraphJudgment.
