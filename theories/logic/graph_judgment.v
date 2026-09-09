From iris.base_logic.lib Require Import iprop.
From iris.proofmode Require Import proofmode.
From iris_lkmm.logic Require Import graph_domain.

(** Universal closure for the future graph-relative Iris WP.  These
    connectives specify the quantifier boundary, not the recursive WP,
    its state interpretation, primitive rules, or adequacy. *)
Module LkmmGraphJudgment.
  Export LkmmGraphDomain.

  Section judgments.
    Context {Σ : gFunctors}.

    Definition all_candidates (P : core_program) (Ψ : core_candidate -> iProp Σ) : iProp Σ :=
      (∀ G, ⌜consistent_program_graph P G⌝ -∗ Ψ G)%I.

    Definition all_candidate_executions (P : core_program)
        (Ψ : core_candidate -> list core_action -> core_state -> iProp Σ) : iProp Σ :=
      all_candidates P (fun G => ∀ actions final,
        ⌜candidate_execution P G actions final⌝ -∗ Ψ G actions final)%I.

    Definition all_candidate_positions (P : core_program)
        (Ψ : core_candidate -> execution_position -> iProp Σ) : iProp Σ :=
      all_candidates P (fun G => ∀ p, ⌜candidate_position P G p⌝ -∗ Ψ G p)%I.

    Lemma all_candidates_elim P Ψ G :
      consistent_program_graph P G -> all_candidates P Ψ ⊢ Ψ G.
    Proof. iIntros (HG) "H". by iApply ("H" $! G). Qed.

    Lemma all_candidate_executions_elim P Ψ G actions final :
      consistent_program_graph P G -> candidate_execution P G actions final ->
      all_candidate_executions P Ψ ⊢ Ψ G actions final.
    Proof.
      iIntros (HG Hrun) "H".
      iDestruct (all_candidates_elim with "H") as "H"; first done.
      by iApply ("H" $! actions final).
    Qed.

    Lemma all_candidate_positions_elim P Ψ G p :
      consistent_program_graph P G -> candidate_position P G p ->
      all_candidate_positions P Ψ ⊢ Ψ G p.
    Proof.
      iIntros (HG Hpos) "H".
      iDestruct (all_candidates_elim with "H") as "H"; first done.
      by iApply ("H" $! p).
    Qed.
  End judgments.
End LkmmGraphJudgment.
