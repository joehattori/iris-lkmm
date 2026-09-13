From Stdlib Require Import List.
From iris.base_logic.lib Require Import fancy_updates.
From iris.proofmode Require Import proofmode.
From iris_lkmm.operational Require Import lkmm_machine lkmm_coupled.
From iris_lkmm.logic Require Import graph_correspondence state_interp wp.
From iris_lkmm.examples Require Import graph_correspondence_examples.
Import ListNotations.

Module WpBodyExamples.
  Import LkmmMachine LkmmCoupled LkmmGraphCorrespondence LkmmStateInterp LkmmWp.
  Module GP := GraphCorrespondenceExamples.GpState.

  Definition sync_view := ThreadView (initial_thread SSynchronizeRcu) 0 [].

  (** Even an empty captured set changes which half of synchronization runs. *)
  Example begin_distinguishes_local_gp_phases suffix final :
    project_coupled_thread (CoupledExecutionPosition [] GP.before
      (CoupledMachineAction (BeginGp 0) :: suffix) final) 0 =
      Some (CoupledThreadView sync_view None) /\
    project_coupled_thread (CoupledExecutionPosition [CoupledMachineAction (BeginGp 0)]
      GP.waiting suffix final) 0 = Some (CoupledThreadView sync_view (Some [])) /\
    CoupledThreadView sync_view None <> CoupledThreadView sync_view (Some []).
  Proof. split; first reflexivity. split; first reflexivity. discriminate. Qed.

  (** Unfolding the WP of a finished thread exposes its resource postcondition. *)
  Example terminal_wp_requires_postcondition `{!invGS Σ, !stateG Σ}
      P G γ E agent regs index actions (Φ : coupled_thread_view -> iProp Σ) :
    let v := CoupledThreadView (ThreadView (ThreadState SSkip [] regs) index actions) None in
    wp P G γ E agent v Φ ⊣⊢ |={E}=> Φ v.
  Proof. intros v. by rewrite wp_unfold /wp_body. Qed.

  Module SilentAssignment.
    Definition before := CoupledThreadView
      (ThreadView (initial_thread (SAssign 0 (EConst 42%Z))) 0 []) None.
    Definition after := CoupledThreadView
      (ThreadView (ThreadState SSkip [] {[0 := RegValue 42%Z ∅]}) 0 [CoreSilent 0]) None.

    Lemma successor P G prefix s a suffix final next :
      coupled_thread_at P G
        (CoupledExecutionPosition prefix s (CoupledMachineAction a :: suffix) final) 0 before ->
      executing_agent a = 0 -> coupled_step P s (CoupledMachineAction a) next ->
      a = Execute (CoreSilent 0) /\
      project_coupled_thread
        (CoupledExecutionPosition (prefix ++ [CoupledMachineAction a]) next suffix final)
        0 = Some after.
    Proof.
      intros [_ Hview] Hagent Hstep.
      pose proof (project_coupled_thread_lookup _ _ _ Hview) as Hlookup.
      inversion Hstep as [m m' b action Hmachine |]; subst.
      destruct Hmachine as
        [m core' action thread Hthread Hordinary Hready Hcore |
         m owner thread [Hthread Hstmt] Hready |
         m owner thread lock rest [Hthread Hstmt] Hready Hstack |
         m owner thread [Hthread Hstmt] Hready |
         m owner thread locks [Hthread Hstmt] Hpending Hclosed];
        simpl in Hagent; subst; cbn in Hlookup;
        try rewrite Hagent in Hthread;
        rewrite Hlookup in Hthread; injection Hthread as <-; try discriminate.
      inversion Hcore; subst; simplify_eq/=.
      split; first reflexivity.
      unfold project_coupled_thread, project_thread, coupled_position_to_core in *.
      cbn in Hview. rewrite Hlookup Hready in Hview. cbn in Hview.
      injection Hview as Hindex Hactions.
      cbn. rewrite lookup_insert_eq Hready.
      rewrite flat_map_app filter_app /=.
      unfold next_agent_index in Hindex |- *. cbn.
      by rewrite Hindex Hactions.
    Qed.

    (** The step updates the register and history while retaining owned resources. *)
    Example assignment_keeps_resources `{!invGS Σ, !stateG Σ} P G γ E (R : iProp Σ) :
      ▷ R -∗ wp P G γ E 0 before (fun v => ⌜v = after⌝ ∗ R).
    Proof.
      iIntros "HR". iApply (wp_lift_silent_step _ _ _ _ _ _ after).
      { intros [[Hstmt _] _]. discriminate. }
      { apply successor. }
      iNext. rewrite wp_unfold /wp_body /after /=.
      iModIntro. iFrame. done.
    Qed.
  End SilentAssignment.
End WpBodyExamples.
