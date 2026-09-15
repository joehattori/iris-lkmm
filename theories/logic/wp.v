From Stdlib Require Import List.
From iris.base_logic.lib Require Import fancy_updates.
From iris.proofmode Require Import proofmode.
From iris_lkmm.operational Require Import lkmm_machine.
From iris_lkmm.logic Require Import graph_correspondence state_interp.
Import ListNotations.

Module LkmmWp.
  Import LkmmMachine LkmmGraphCorrespondence LkmmStateInterp.

  Local Lemma ordinary_coupled_successor P prefix s a suffix final next agent thread :
    s.(coupled_machine).(machine_core).(core_threads) !! agent = Some thread ->
    ordinary_statement thread.(thread_statement) -> executing_agent a = agent ->
    coupled_step P s (CoupledMachineAction a) next ->
    exists action v', a = Execute action /\
      lookup_coupled_thread_view
        (CoupledExecutionPosition (prefix ++ [CoupledMachineAction a]) next suffix final)
        agent = Some v'.
  Proof.
    intros Hlookup Hordinary Hagent Hstep.
    revert Hagent. inversion Hstep as [m m' b action Hmachine |]; subst. intros Hagent.
    destruct Hmachine as
      [m core' action actual Hthread Hordinary' Hready Hcore |
       m owner actual [Hthread Hstmt] Hready |
       m owner actual lock rest [Hthread Hstmt] Hready Hstack |
       m owner actual [Hthread Hstmt] Hready |
       m owner actual locks [Hthread Hstmt] Hpending Hclosed];
      simpl in Hagent; subst; cbn in Hlookup;
      try rewrite Hagent in Hthread;
      rewrite Hlookup in Hthread; injection Hthread as <-;
      try solve [rewrite Hstmt in Hordinary; done].
    exists action. unfold lookup_coupled_thread_view, lookup_thread_view, coupled_position_to_core.
    destruct Hcore; simpl; rewrite lookup_insert_eq; eexists; done.
  Qed.

  Local Lemma silent_project_next prefix s suffix final agent v thread' :
    lookup_coupled_thread_view
      (CoupledExecutionPosition prefix s
        (CoupledMachineAction (Execute (CoreSilent agent)) :: suffix) final) agent = Some v ->
    v.(coupled_view_pending_gp) = None ->
    lookup_coupled_thread_view
      (CoupledExecutionPosition (prefix ++ [CoupledMachineAction (Execute (CoreSilent agent))])
        (CoupledState (with_core s.(coupled_machine)
          (update_thread s.(coupled_machine).(machine_core) agent thread')) s.(coupled_builder))
        suffix final) agent = Some (CoupledThreadView
          (ThreadView thread' v.(coupled_view_core).(view_event_index)
            (v.(coupled_view_core).(view_actions) ++ [CoreSilent agent])) None).
  Proof.
    unfold lookup_coupled_thread_view, lookup_thread_view, coupled_position_to_core.
    intros Hview Hpending. apply fmap_Some in Hview as (cv & Hcore & Heq). subst v.
    apply fmap_Some in Hcore as (thread & Hlookup & Heq). subst cv.
    cbn in Hpending |- *. rewrite lookup_insert_eq Hpending /=.
    rewrite flat_map_app /= /agent_actions filter_app /=.
    rewrite filter_cons_True; last done. reflexivity.
  Qed.

  Section wp.
    Context `{!invGS Σ, !stateG Σ}.

    (** One layer of the per-agent WP, with [P], [G], and [γ] fixed for
        recursive calls. All accepted schedules of this local view are
        quantified over. Builder and other-agent steps are handled by the
        surrounding execution; this body handles the scheduled agent.

        The execution supplies the state interpretation and thread token.
        Reader and pending-GP tokens must come from the proof's resources
        and pass to the continuation when still owned. *)
    Definition wp_body (P : core_program) (G : core_candidate) (γ : state_names)
        (recurse : coPset -d> agent_id -d> coupled_thread_view -d>
          (coupled_thread_view -d> iPropO Σ) -d> iPropO Σ) :
        coPset -d> agent_id -d> coupled_thread_view -d>
          (coupled_thread_view -d> iPropO Σ) -d> iPropO Σ := λ E agent v Φ,
      match v.(coupled_view_core).(view_thread).(thread_statement),
          v.(coupled_view_core).(view_thread).(thread_continuation),
          v.(coupled_view_pending_gp) with
      | SSkip, [], None => |={E}=> Φ v
      | _, _, _ =>
          ∀ prefix s a suffix final,
            let p := CoupledExecutionPosition prefix s (CoupledMachineAction a :: suffix) final in
            ⌜coupled_thread_at P G p agent v /\ executing_agent a = agent⌝ -∗
            state_interp γ s ∗ thread_token γ agent v.(coupled_view_core).(view_thread)
              ={E,∅}=∗
            ∀ next,
              let p' := CoupledExecutionPosition (prefix ++ [CoupledMachineAction a])
                next suffix final in
              ⌜coupled_step P s (CoupledMachineAction a) next /\ coupled_position P G p'⌝ -∗
              |={∅}=> ▷ |={∅,E}=> ∃ v',
                ⌜lookup_coupled_thread_view p' agent = Some v'⌝ ∗
                state_interp γ next ∗
                thread_token γ agent v'.(coupled_view_core).(view_thread) ∗
                recurse E agent v' Φ
      end%I.

    Local Instance wp_body_contractive P G γ : Contractive (wp_body P G γ).
    Proof.
      rewrite /wp_body /= => n recurse recurse' Hrecurse E agent v Φ.
      repeat (f_contractive || f_equiv); apply Hrecurse.
    Qed.

    Definition wp P G γ :
        coPset -d> agent_id -d> coupled_thread_view -d>
          (coupled_thread_view -d> iPropO Σ) -d> iPropO Σ :=
      fixpoint (wp_body P G γ).

    Lemma wp_unfold P G γ E agent v Φ :
      wp P G γ E agent v Φ ⊣⊢ wp_body P G γ (wp P G γ) E agent v Φ.
    Proof. apply (fixpoint_unfold (wp_body P G γ)). Qed.

    (** The postcondition transformation may own resources and update them
        at [E]. It is carried through the guarded steps and used at completion;
        the program, candidate, agent, and mask remain fixed. *)
    Lemma wp_consequence P G γ E agent v Φ Ψ :
      wp P G γ E agent v Φ -∗
      (∀ v', Φ v' ={E}=∗ Ψ v') -∗ wp P G γ E agent v Ψ.
    Proof.
      iIntros "Hwp Hpost". iLöb as "IH" forall (v).
      rewrite !wp_unfold /wp_body.
      destruct v as [[thread index actions] pending].
      destruct thread as [statement continuation regs].
      destruct statement, continuation, pending; simpl in *;
        try (iMod "Hwp" as "HΦ"; iApply ("Hpost" with "HΦ")).
      all: iIntros (prefix s a suffix final) "%Hcurrent Hstate";
        iMod ("Hwp" $! prefix s a suffix final with "[] Hstate") as "Hstep"; first done.
      all: iModIntro; iIntros (next) "%Hnext";
        iMod ("Hstep" $! next with "[]") as "Hnext"; first done.
      all: iModIntro; iNext;
        iMod "Hnext" as (v') "(%Hview & Hstate & Hthread & Hwp)";
        iModIntro; iExists v'; iFrame "Hstate Hthread";
        iSplit; first done.
      all: iApply ("IH" with "Hwp Hpost").
    Qed.

    Lemma wp_mono P G γ E agent v Φ Ψ :
      (forall v', Φ v' ⊢ Ψ v') ->
      wp P G γ E agent v Φ ⊢ wp P G γ E agent v Ψ.
    Proof.
      intros Hpost. iIntros "Hwp". iApply (wp_consequence with "Hwp").
      iIntros (v') "HΦ". iModIntro. by iApply Hpost.
    Qed.

    (** Carry an arbitrary separately owned assertion to the postcondition. *)
    Lemma wp_frame_l P G γ E agent v Φ R :
      R ∗ wp P G γ E agent v Φ ⊢ wp P G γ E agent v (fun v' => R ∗ Φ v').
    Proof.
      iIntros "[HR Hwp]". iApply (wp_consequence with "Hwp").
      iIntros (v') "HΦ". iModIntro. iFrame.
    Qed.

    Lemma wp_frame_r P G γ E agent v Φ R :
      wp P G γ E agent v Φ ∗ R ⊢ wp P G γ E agent v (fun v' => Φ v' ∗ R).
    Proof.
      iIntros "[Hwp HR]". iApply (wp_consequence with "Hwp").
      iIntros (v') "HΦ". iModIntro. iFrame.
    Qed.

    Global Instance frame_wp p P G γ E agent v R Φ Ψ :
      (FrameInstantiateExistDisabled -> forall v', Frame p R (Φ v') (Ψ v')) ->
      Frame p R (wp P G γ E agent v Φ) (wp P G γ E agent v Ψ) | 2.
    Proof.
      rewrite /Frame => Hframe. rewrite wp_frame_l.
      apply wp_mono, Hframe. constructor.
    Qed.

    (** Lift an update at mask [E] for every successor compatible with [G].
        The handler may own additional resources for the operation; this
        rule supplies the state/thread resources and handles the later and masks. *)
    Lemma wp_lift_step P G γ E agent v Φ :
      ~ (thread_complete v.(coupled_view_core).(view_thread) /\ v.(coupled_view_pending_gp) = None)
      ->
      (▷ ∀ prefix s a suffix final next,
        let p := CoupledExecutionPosition prefix s (CoupledMachineAction a :: suffix) final in
        let p' := CoupledExecutionPosition (prefix ++ [CoupledMachineAction a]) next suffix final in
        ⌜coupled_thread_at P G p agent v /\ executing_agent a = agent /\
          coupled_step P s (CoupledMachineAction a) next /\ coupled_position P G p'⌝ -∗
        state_interp γ s ∗ thread_token γ agent v.(coupled_view_core).(view_thread)
          ={E}=∗ ∃ v',
            ⌜lookup_coupled_thread_view p' agent = Some v'⌝ ∗
            state_interp γ next ∗
            thread_token γ agent v'.(coupled_view_core).(view_thread) ∗
            wp P G γ E agent v' Φ) -∗
      wp P G γ E agent v Φ.
    Proof.
      intros Hactive. rewrite wp_unfold /wp_body.
      destruct v as [[thread index actions] pending].
      destruct thread as [statement continuation regs].
      destruct statement, continuation, pending; simpl in *;
        try (exfalso; apply Hactive; done).
      all: iIntros "Hstep" (prefix s a suffix final) "%Hcurrent Hstate";
        iApply fupd_mask_intro; first set_solver.
      all: iIntros "Hclose" (next) "%Hnext"; iModIntro; iNext;
        iMod "Hclose" as "_";
        iApply ("Hstep" $! prefix s a suffix final next with "[] Hstate");
        iPureIntro; naive_solver.
    Qed.

    (** Ordinary steps allocate persistent facts for exactly their new events.
        The wrapper supplies allocation well-formedness from the prefix and
        maintains the thread resources internally. The handler must return
        memory authority matching the new emitted writes before the state
        interpretation can be restored. It covers every compatible action and
        successor, including observations and both events of an RMW.
        Event facts grant no memory ownership. *)
    Lemma wp_lift_execute P G γ E agent v Φ :
      ~ (thread_complete v.(coupled_view_core).(view_thread) /\ v.(coupled_view_pending_gp) = None)
      ->
      ordinary_statement v.(coupled_view_core).(view_thread).(thread_statement) ->
      (▷ ∀ prefix s a suffix final next v',
        let p := CoupledExecutionPosition prefix s (CoupledMachineAction (Execute a) :: suffix)
          final in
        let p' := CoupledExecutionPosition (prefix ++ [CoupledMachineAction (Execute a)]) next
          suffix final in
        ⌜coupled_thread_at P G p agent v /\ action_agent a = agent /\
          coupled_step P s (CoupledMachineAction (Execute a)) next /\
          coupled_position P G p' /\ lookup_coupled_thread_view p' agent = Some v'⌝ -∗
        memory_auth γ.(memory_names_of) s.(coupled_machine).(machine_core).(core_events) ∗
        ([∗ map] eid ↦ ev ∈ next.(coupled_machine).(machine_core).(core_events) ∖
            s.(coupled_machine).(machine_core).(core_events), event_fact γ eid ev)
          ={E}=∗ memory_auth γ.(memory_names_of)
            next.(coupled_machine).(machine_core).(core_events) ∗ wp P G γ E agent v' Φ) -∗
      wp P G γ E agent v Φ.
    Proof.
      intros Hactive Hordinary. iIntros "Hwp". iApply wp_lift_step; first done.
      iNext. iIntros (prefix s a suffix final next) "%Hfacts Hstate".
      destruct Hfacts as (Hcurrent & Hagent & Hstep & Hpos).
      pose proof (lookup_coupled_thread_view_lookup _ _ _ (proj2 Hcurrent)) as Hlookup.
      destruct (ordinary_coupled_successor P prefix s a suffix final next agent _
        Hlookup Hordinary Hagent Hstep) as (action & v' & -> & Hview).
      pose proof (lookup_coupled_thread_view_lookup _ _ _ Hview) as Hlookup'.
      pose proof (core_run_allocation_wf _ _ _
        (proj1 (coupled_position_projection _ _ _ (proj1 Hcurrent)))) as Halloc.
      cbn in Hagent. rewrite <- Hagent in Hlookup'.
      iMod (state_interp_execute _ _ _ _ _ _ _ Hstep Halloc Hlookup'
        with "[Hstate]") as "(Hrestore & Hmemory & Hthread & Hnew)".
      { rewrite Hagent. iExact "Hstate". }
      iMod ("Hwp" $! prefix s action suffix final next v' with "[] [$Hmemory $Hnew]")
        as "[Hmemory Hwp]".
      { iPureIntro. split_and!; done. }
      iDestruct ("Hrestore" with "Hmemory") as "Hstate".
      iModIntro. iExists v'. rewrite Hagent. iFrame. done.
    Qed.

    Lemma wp_lift_silent_step P G γ E agent v v' Φ :
      ~ (thread_complete v.(coupled_view_core).(view_thread) /\ v.(coupled_view_pending_gp) = None)
      ->
      (forall prefix s a suffix final next,
        coupled_thread_at P G
          (CoupledExecutionPosition prefix s (CoupledMachineAction a :: suffix) final) agent v ->
        executing_agent a = agent -> coupled_step P s (CoupledMachineAction a) next ->
        a = Execute (CoreSilent agent) /\
        lookup_coupled_thread_view
          (CoupledExecutionPosition (prefix ++ [CoupledMachineAction a]) next suffix final)
          agent = Some v') ->
      ▷ wp P G γ E agent v' Φ -∗ wp P G γ E agent v Φ.
    Proof.
      intros Hactive Hsilent. iIntros "Hwp". iApply wp_lift_step; first done.
      iNext. iIntros (prefix s a suffix final next) "%Hfacts Hstate".
      destruct Hfacts as (Hcurrent & Hagent & Hstep & Hpos).
      destruct (Hsilent _ _ _ _ _ _ Hcurrent Hagent Hstep) as [-> Hview].
      pose proof (lookup_coupled_thread_view_lookup _ _ _ Hview) as Hlookup.
      iMod (state_interp_silent_step _ _ _ _ _ _ _ Hstep Hlookup with "Hstate")
        as "[Hstate Hthread]".
      iModIntro. iExists v'. iFrame. done.
    Qed.

    (** Sequencing keeps the second statement in the operational continuation.
        Entering the first statement is one silent step. *)
    Lemma wp_seq P G γ E agent first second ks regs index actions Φ :
      ▷ wp P G γ E agent
        (CoupledThreadView (ThreadView (ThreadState first (KSeq second :: ks) regs)
          index (actions ++ [CoreSilent agent])) None) Φ -∗
      wp P G γ E agent
        (CoupledThreadView (ThreadView (ThreadState (SSeq first second) ks regs)
          index actions) None) Φ.
    Proof.
      apply wp_lift_silent_step.
      { intros [[Hskip _] _]. discriminate. }
      intros prefix s a suffix final next [_ Hview] Hagent Hstep.
      pose proof (lookup_coupled_thread_view_lookup _ _ _ Hview) as Hlookup.
      revert Hagent. inversion Hstep as [m m' b action Hmachine |]; subst. intros Hagent.
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
      split; first reflexivity. by apply (silent_project_next _ _ _ _ _ _ _ Hview).
    Qed.

    (** Resume the saved statement, retaining registers and the outer frames. *)
    Lemma wp_skip_seq P G γ E agent next ks regs index actions Φ :
      ▷ wp P G γ E agent
        (CoupledThreadView (ThreadView (ThreadState next ks regs)
          index (actions ++ [CoreSilent agent])) None) Φ -∗
      wp P G γ E agent
        (CoupledThreadView (ThreadView (ThreadState SSkip (KSeq next :: ks) regs)
          index actions) None) Φ.
    Proof.
      apply wp_lift_silent_step.
      { intros [[_ Hempty] _]. discriminate. }
      intros prefix s a suffix final s' [_ Hview] Hagent Hstep.
      pose proof (lookup_coupled_thread_view_lookup _ _ _ Hview) as Hlookup.
      revert Hagent. inversion Hstep as [m m' b action Hmachine |]; subst. intros Hagent.
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
      split; first reflexivity. by apply (silent_project_next _ _ _ _ _ _ _ Hview).
    Qed.

    (** Assignment evaluates in the old registers and retains the result's
        dependency origins. It takes one silent step and preserves the frames. *)
    Lemma wp_assign P G γ E agent dst expression result ks regs index actions Φ :
      eval_expr regs expression = Some result ->
      ▷ wp P G γ E agent
        (CoupledThreadView (ThreadView (ThreadState SSkip ks (<[dst := result]> regs))
          index (actions ++ [CoreSilent agent])) None) Φ -∗
      wp P G γ E agent
        (CoupledThreadView (ThreadView (ThreadState (SAssign dst expression) ks regs)
          index actions) None) Φ.
    Proof.
      intros Heval. apply wp_lift_silent_step.
      { intros [[Hskip _] _]. discriminate. }
      intros prefix s a suffix final next [_ Hview] Hagent Hstep.
      pose proof (lookup_coupled_thread_view_lookup _ _ _ Hview) as Hlookup.
      revert Hagent. inversion Hstep as [m m' b action Hmachine |]; subst. intros Hagent.
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
      split; first reflexivity. by apply (silent_project_next _ _ _ _ _ _ _ Hview).
    Qed.

    (** Both branch outcomes retain the condition's origins until branch exit.
        Zero selects the else branch; every nonzero integer selects then. *)
    Lemma wp_if P G γ E agent condition then_branch else_branch result ks regs index actions Φ :
      eval_expr regs condition = Some result ->
      ▷ wp P G γ E agent
        (CoupledThreadView (ThreadView
          (ThreadState (if decide (result.(reg_integer) = 0%Z) then else_branch else then_branch)
            (KControl result.(reg_origins) :: ks) regs)
          index (actions ++ [CoreSilent agent])) None) Φ -∗
      wp P G γ E agent
        (CoupledThreadView (ThreadView (ThreadState (SIf condition then_branch else_branch) ks regs)
          index actions) None) Φ.
    Proof.
      intros Heval. apply wp_lift_silent_step.
      { intros [[Hskip _] _]. discriminate. }
      intros prefix s a suffix final next [_ Hview] Hagent Hstep.
      pose proof (lookup_coupled_thread_view_lookup _ _ _ Hview) as Hlookup.
      revert Hagent. inversion Hstep as [m m' b action Hmachine |]; subst. intros Hagent.
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
      - rewrite decide_False; last done.
        split; first reflexivity. by apply (silent_project_next _ _ _ _ _ _ _ Hview).
      - rewrite decide_True; last done.
        split; first reflexivity. by apply (silent_project_next _ _ _ _ _ _ _ Hview).
    Qed.

    Lemma wp_if_true P G γ E agent condition then_branch else_branch result ks regs index actions Φ :
      eval_expr regs condition = Some result -> result.(reg_integer) <> 0%Z ->
      ▷ wp P G γ E agent
        (CoupledThreadView (ThreadView
          (ThreadState then_branch (KControl result.(reg_origins) :: ks) regs)
          index (actions ++ [CoreSilent agent])) None) Φ -∗
      wp P G γ E agent
        (CoupledThreadView (ThreadView (ThreadState (SIf condition then_branch else_branch) ks regs)
          index actions) None) Φ.
    Proof.
      intros Heval Hnonzero.
      pose proof (wp_if P G γ E agent condition then_branch else_branch result ks regs index actions Φ
        Heval) as Hif.
      by rewrite decide_False in Hif.
    Qed.

    Lemma wp_if_false P G γ E agent condition then_branch else_branch result ks regs index actions Φ :
      eval_expr regs condition = Some result -> result.(reg_integer) = 0%Z ->
      ▷ wp P G γ E agent
        (CoupledThreadView (ThreadView
          (ThreadState else_branch (KControl result.(reg_origins) :: ks) regs)
          index (actions ++ [CoreSilent agent])) None) Φ -∗
      wp P G γ E agent
        (CoupledThreadView (ThreadView (ThreadState (SIf condition then_branch else_branch) ks regs)
          index actions) None) Φ.
    Proof.
      intros Heval Hzero.
      pose proof (wp_if P G γ E agent condition then_branch else_branch result ks regs index actions Φ
        Heval) as Hif.
      by rewrite decide_True in Hif.
    Qed.

    (** Leave the completed branch's control scope, retaining outer frames. *)
    Lemma wp_skip_control P G γ E agent condition_origins ks regs index actions Φ :
      ▷ wp P G γ E agent
        (CoupledThreadView (ThreadView (ThreadState SSkip ks regs)
          index (actions ++ [CoreSilent agent])) None) Φ -∗
      wp P G γ E agent
        (CoupledThreadView (ThreadView (ThreadState SSkip (KControl condition_origins :: ks) regs)
          index actions) None) Φ.
    Proof.
      apply wp_lift_silent_step.
      { intros [[_ Hempty] _]. discriminate. }
      intros prefix s a suffix final next [_ Hview] Hagent Hstep.
      pose proof (lookup_coupled_thread_view_lookup _ _ _ Hview) as Hlookup.
      revert Hagent. inversion Hstep as [m m' b action Hmachine |]; subst. intros Hagent.
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
      split; first reflexivity. by apply (silent_project_next _ _ _ _ _ _ _ Hview).
    Qed.
  End wp.
End LkmmWp.
