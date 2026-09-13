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
      project_coupled_thread
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
    exists action. unfold project_coupled_thread, project_thread, coupled_position_to_core.
    destruct Hcore; simpl; rewrite lookup_insert_eq; eexists; done.
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
                ⌜project_coupled_thread p' agent = Some v'⌝ ∗
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
            ⌜project_coupled_thread p' agent = Some v'⌝ ∗
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
        maintains the state/thread resources internally. The continuation
        covers every compatible action and successor, including observed values
        and both events of an RMW; event facts grant no memory ownership. *)
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
          coupled_position P G p' /\ project_coupled_thread p' agent = Some v'⌝ -∗
        ([∗ map] eid ↦ ev ∈ next.(coupled_machine).(machine_core).(core_events) ∖
            s.(coupled_machine).(machine_core).(core_events), event_fact γ eid ev)
          ={E}=∗ wp P G γ E agent v' Φ) -∗
      wp P G γ E agent v Φ.
    Proof.
      intros Hactive Hordinary. iIntros "Hwp". iApply wp_lift_step; first done.
      iNext. iIntros (prefix s a suffix final next) "%Hfacts Hstate".
      destruct Hfacts as (Hcurrent & Hagent & Hstep & Hpos).
      pose proof (project_coupled_thread_lookup _ _ _ (proj2 Hcurrent)) as Hlookup.
      destruct (ordinary_coupled_successor P prefix s a suffix final next agent _
        Hlookup Hordinary Hagent Hstep) as (action & v' & -> & Hview).
      pose proof (project_coupled_thread_lookup _ _ _ Hview) as Hlookup'.
      pose proof (core_run_allocation_wf _ _ _
        (proj1 (coupled_position_projection _ _ _ (proj1 Hcurrent)))) as Halloc.
      cbn in Hagent. rewrite <- Hagent in Hlookup'.
      iMod (state_interp_execute _ _ _ _ _ _ _ Hstep Halloc Hlookup'
        with "[Hstate]") as "(Hstate & Hthread & Hnew)".
      { rewrite Hagent. iExact "Hstate". }
      iMod ("Hwp" $! prefix s action suffix final next v' with "[] Hnew") as "Hwp".
      { iPureIntro. split_and!; done. }
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
        project_coupled_thread
          (CoupledExecutionPosition (prefix ++ [CoupledMachineAction a]) next suffix final)
          agent = Some v') ->
      ▷ wp P G γ E agent v' Φ -∗ wp P G γ E agent v Φ.
    Proof.
      intros Hactive Hsilent. iIntros "Hwp". iApply wp_lift_step; first done.
      iNext. iIntros (prefix s a suffix final next) "%Hfacts Hstate".
      destruct Hfacts as (Hcurrent & Hagent & Hstep & Hpos).
      destruct (Hsilent _ _ _ _ _ _ Hcurrent Hagent Hstep) as [-> Hview].
      pose proof (project_coupled_thread_lookup _ _ _ Hview) as Hlookup.
      iMod (state_interp_silent_step _ _ _ _ _ _ _ Hstep Hlookup with "Hstate")
        as "[Hstate Hthread]".
      iModIntro. iExists v'. iFrame. done.
    Qed.
  End wp.
End LkmmWp.
