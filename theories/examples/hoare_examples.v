From Stdlib Require Import List.
From iris.proofmode Require Import proofmode.
From iris_lkmm.logic Require Import hoare.
Import ListNotations.

Module HoareExamples.
  Import LkmmHoare.

  Section specs.
    Context `{!invGS Σ, !stateG Σ}.
    Context (c : wp_context) (E : coPset).

    Definition assigned_view dst z := LkmmThreadView
      (ThreadView (ThreadState SSkip [] {[dst := RegValue z ∅]})
        0 [CoreSilent c.(wp_agent)]) None.

    (** A fixed RET, an arbitrary mask, and an arbitrary owned resource. *)
    Lemma assign_spec dst z (R : iProp Σ) :
      {{{ R }}} SAssign dst (EConst z) @ c; E
      {{{ RET assigned_view dst z; R }}}.
    Proof.
      iIntros (Φ) "HR HΦ". iApply wp_assign; first reflexivity.
      iNext. rewrite wp_unfold /wp_body /=.
      iModIntro. by iApply "HΦ".
    Qed.

    (** Apply the triple while retaining a separate resource in its caller,
        and expose a register property instead of an exact final view. *)
    Example assign_with_frame dst z (R F : iProp Σ) :
      R ∗ F -∗ WP SAssign dst (EConst z) @ c; E {{ v,
        ⌜v.(lkmm_view_core).(view_thread).(thread_registers) !! dst =
          Some (RegValue z ∅)⌝ ∗ R ∗ F }}.
    Proof.
      iIntros "[HR HF]". iApply (assign_spec with "HR").
      iNext. iIntros "HR". iFrame. iPureIntro. apply lookup_insert_eq.
    Qed.

    (** A full-view triple preserves the copied register's dependency origins
        and the existing event index/history, including when dst = src. *)
    Lemma copy_spec dst src regs result index actions (R : iProp Σ) :
      regs !! src = Some result ->
      {{{ R }}}
        LkmmThreadView
          (ThreadView (ThreadState (SAssign dst (EReg src)) [] regs) index actions)
          None @ c; E
      {{{ RET LkmmThreadView
          (ThreadView (ThreadState SSkip [] (<[dst := result]> regs))
            index (actions ++ [CoreSilent c.(wp_agent)])) None; R }}}.
    Proof.
      intros Hreg. iIntros (Φ) "HR HΦ".
      iApply wp_assign; first exact Hreg.
      iNext. rewrite wp_unfold /wp_body /=.
      iModIntro. by iApply "HΦ".
    Qed.

    (** A completed statement uses the unguarded WP value case: it does not
        take a step that could discharge a Texan triple's delayed callback. *)
    Example skip_wp (R : iProp Σ) :
      R -∗ WP SSkip @ c; E {{ v, ⌜v = initial_thread_view SSkip⌝ ∗ R }}.
    Proof.
      iIntros "HR". rewrite stmt_wp_unfold wp_unfold /wp_body /=.
      iModIntro. by iFrame.
    Qed.
  End specs.
End HoareExamples.
