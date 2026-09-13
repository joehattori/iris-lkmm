From Stdlib Require Import List Lia.
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

  Module RmwEmission.
    Definition body := SXchg 0 RmwRelaxed (EConst 0) (EConst 1).
    Definition before := CoupledThreadView (ThreadView (initial_thread body) 0 []) None.
    Definition after read observed := CoupledThreadView
      (ThreadView (ThreadState SSkip [] {[0 := RegValue observed {[read]}]})
        2 [CoreObserve 0 observed]) None.
    Definition read_event observed := EAgent 0 0 (LMemory AccessRead AccessOnce RmwMarked 0 observed).
    Definition write_event := EAgent 0 1 (LMemory AccessWrite AccessOnce RmwMarked 0 1%Z).

    (** One nondeterministic observation produces two event facts, a register
        origin, and one action-history entry. Both facts remain duplicable. *)
    Example exchange_records_both_events `{!invGS Σ, !stateG Σ} P G γ E (R : iProp Σ) :
      ▷ R -∗ wp P G γ E 0 before (fun v => ∃ read observed,
        ⌜v = after read observed⌝ ∗ R ∗
        event_fact γ read (read_event observed) ∗
        event_fact γ (S read) write_event ∗ event_fact γ (S read) write_event).
    Proof.
      iIntros "HR". iApply wp_lift_execute.
      { intros [[Hstmt _] _]. discriminate. }
      { done. }
      iNext. iIntros (prefix s a suffix final next v') "%Hfacts #Hnew".
      destruct Hfacts as ((Hpos & Hview) & Hagent & Hstep & Hnext & Hview').
      pose proof (project_coupled_thread_lookup _ _ _ Hview) as Hlookup.
      pose proof (project_coupled_thread_index _ _ _ Hview) as Hindex.
      pose proof (core_run_allocation_wf _ _ _
        (proj1 (coupled_position_projection _ _ _ Hpos))) as Halloc.
      inversion Hstep as [m m' b action Hmachine |]; subst.
      inversion Hmachine as [m0 core' action thread Hthread Hordinary Hready Hcore | | | |]; subst.
      rewrite Hagent in Hthread. cbn in Hlookup. rewrite Hlookup in Hthread.
      injection Hthread as <-. inversion Hcore; subst; simplify_eq/=.
      unfold body in *. simplify_eq/=.
      injection H1 as <- <-.
      assert (v' = after m.(machine_core).(core_next_id) observed) as ->.
      { unfold project_coupled_thread, project_thread, coupled_position_to_core in *.
        cbn in Hview. rewrite Hlookup Hready in Hview. cbn in Hview.
        injection Hview as Hindex' Hactions.
        cbn in Hview'. rewrite lookup_insert_eq Hready in Hview'. cbn in Hview'.
        rewrite flat_map_app filter_app /= in Hview'.
        unfold next_agent_index at 1 in Hview'. cbn in Hview'.
        rewrite lookup_insert_eq /= Hindex' Hactions in Hview'.
        by injection Hview'. }
      iDestruct (big_sepM_lookup _ _ m.(machine_core).(core_next_id) with "Hnew") as "#Hread".
      { apply lookup_difference_Some. split.
        - cbn. rewrite lookup_insert_ne; last lia. rewrite lookup_insert_eq. reflexivity.
        - by apply core_next_id_fresh. }
      iDestruct (big_sepM_lookup _ _ (S m.(machine_core).(core_next_id)) with "Hnew") as "#Hwrite".
      { apply lookup_difference_Some. split.
        - cbn. rewrite lookup_insert_eq. reflexivity.
        - apply eq_None_not_Some. intros [ev Hev].
          pose proof (proj1 (proj2 Halloc) _ _ Hev). lia. }
      rewrite wp_unfold /wp_body /after /=. iModIntro. iModIntro.
      iExists _, _. iSplit; first done. cbn in Hindex.
      iEval (rewrite Hindex) in "Hread Hwrite". iFrame "HR Hread Hwrite".
    Qed.
    (** Reuse the exchange proof, weaken its exact-view postcondition, and
        consume an owned update only when the exchange has completed. *)
    Example exchange_consequence `{!invGS Σ, !stateG Σ} P G γ E (R S : iProp Σ) :
      ▷ R -∗ (R ={E}=∗ S) -∗
      wp P G γ E 0 before (fun v =>
        ⌜thread_complete v.(coupled_view_core).(view_thread) /\
          v.(coupled_view_core).(view_event_index) = 2⌝ ∗ S ∗
        ∃ write, event_fact γ write write_event).
    Proof.
      iIntros "HR Hupdate". iApply (wp_consequence with "[HR] [Hupdate]").
      { iApply (exchange_records_both_events with "HR"). }
      iIntros (v) "Hpost".
      iDestruct "Hpost" as (read observed) "(-> & HR & _ & #Hwrite & _)".
      iMod ("Hupdate" with "HR") as "HS".
      iModIntro. iSplit; first done. iFrame "HS". iExists _. iExact "Hwrite".
    Qed.

    (** Frame a separate owned assertion around the existing exchange proof,
        outside its existential postcondition, using proof-mode framing. *)
    Example exchange_frames_resource `{!invGS Σ, !stateG Σ} P G γ E (R F : iProp Σ) :
      ▷ R -∗ F -∗ wp P G γ E 0 before (fun v =>
        (∃ read observed, ⌜v = after read observed⌝ ∗ R ∗
          event_fact γ read (read_event observed) ∗
          event_fact γ (S read) write_event ∗
          event_fact γ (S read) write_event) ∗ F).
    Proof.
      iIntros "HR HF". iFrame "HF".
      iApply (exchange_records_both_events with "HR").
    Qed.
  End RmwEmission.
End WpBodyExamples.
