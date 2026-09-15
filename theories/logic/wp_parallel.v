From Stdlib Require Import List.
From iris.base_logic.lib Require Import fancy_updates.
From iris.proofmode Require Import proofmode.
From iris_lkmm.lang Require Import core_renaming.
From iris_lkmm.operational Require Import lkmm_machine lkmm_coupled.
From iris_lkmm.logic Require Import graph_correspondence state_interp wp.
Import ListNotations.

Module LkmmWpParallel.
  Import LkmmMachine LkmmGraphCorrespondence LkmmStateInterp LkmmWp LkmmCoreRenaming.

  Local Lemma core_step_thread_active P s a next thread :
    core_step P s a next ->
    s.(core_threads) !! core_action_agent a = Some thread -> ~ thread_complete thread.
  Proof.
    intros Hstep Hlookup Hcomplete. destruct Hstep; cbn in Hlookup; simplify_eq.
    all: destruct Hcomplete as [Hskip Hempty]; congruence.
  Qed.

  Local Lemma machine_step_actor P s a next :
    step P s a next -> exists thread,
      s.(machine_core).(core_threads) !! executing_agent a = Some thread /\
      ~ thread_complete thread.
  Proof.
    intros Hstep. destruct Hstep as
      [s core' a thread Hthread Hordinary Hready Hcore |
       s agent thread [Hthread Hstmt] Hready |
       s agent thread lock rest [Hthread Hstmt] Hready Hstack |
       s agent thread [Hthread Hstmt] Hready |
       s agent thread locks [Hthread Hstmt] Hpending Hclosed];
      exists thread; split; try done.
    all: try solve [intros [Hskip _]; congruence].
    by eapply core_step_thread_active.
  Qed.

  Local Lemma machine_step_other_core P s a next other :
    step P s a next -> executing_agent a <> other ->
    next.(machine_core).(core_threads) !! other = s.(machine_core).(core_threads) !! other /\
    next_agent_index next.(machine_core) other = next_agent_index s.(machine_core) other.
  Proof.
    intros Hstep Hother. destruct Hstep as
      [s core' a thread Hthread Hordinary Hready Hcore |
       s agent thread Hcurrent Hready |
       s agent thread lock rest Hcurrent Hready Hstack |
       s agent thread Hcurrent Hready |
       s agent thread locks Hcurrent Hpending Hclosed]; cbn in Hother |- *.
    { split.
      - destruct Hcore; cbn in Hother |- *; by rewrite lookup_insert_ne.
      - by eapply core_step_other_index. }
    all: split; try done; unfold next_agent_index; cbn; by rewrite lookup_insert_ne.
  Qed.

  Local Lemma machine_action_other_history a other :
    executing_agent a <> other -> agent_actions other (core_actions_of a) = [].
  Proof.
    destruct a as [[agent | agent | agent value] | agent | agent | agent | agent];
      intros Hother; unfold agent_actions; cbn in Hother |- *; try done;
      case_decide; done.
  Qed.

  Lemma lookup_coupled_thread_view_other_step P prefix s a suffix final next other :
    coupled_step P s (CoupledMachineAction a) next -> executing_agent a <> other ->
    lookup_coupled_thread_view
      (CoupledExecutionPosition (prefix ++ [CoupledMachineAction a]) next suffix final) other =
    lookup_coupled_thread_view
      (CoupledExecutionPosition prefix s (CoupledMachineAction a :: suffix) final) other.
  Proof.
    intros Hstep Hother. inversion Hstep as [m m' b action Hmachine |]; subst.
    destruct (machine_step_other_core _ _ _ _ _ Hmachine Hother) as [Hthread Hindex].
    pose proof (step_pending_other _ _ _ _ _ Hmachine Hother) as Hpending.
    pose proof (machine_action_other_history a other Hother) as Hactions.
    unfold agent_actions in Hactions.
    unfold lookup_coupled_thread_view, lookup_thread_view, coupled_position_to_core. cbn.
    rewrite Hthread Hindex Hpending flat_map_app /= app_nil_r /agent_actions filter_app.
    by rewrite Hactions app_nil_r.
  Qed.

  Lemma lookup_coupled_thread_view_builder_step P prefix s suffix final next agent :
    coupled_step P s CoupledBuilderAction next ->
    lookup_coupled_thread_view
      (CoupledExecutionPosition (prefix ++ [CoupledBuilderAction]) next suffix final) agent =
    lookup_coupled_thread_view
      (CoupledExecutionPosition prefix s (CoupledBuilderAction :: suffix) final) agent.
  Proof.
    intros Hstep. inversion Hstep; subst.
    unfold lookup_coupled_thread_view, lookup_thread_view, coupled_position_to_core. cbn.
    by rewrite flat_map_app /= app_nil_r.
  Qed.

  Local Lemma coupled_step_actor_in_program P G prefix s a suffix final next :
    coupled_position P G
      (CoupledExecutionPosition prefix s (CoupledMachineAction a :: suffix) final) ->
    coupled_step P s (CoupledMachineAction a) next ->
    is_Some (P.(program_agents) !! executing_agent a).
  Proof.
    intros [Hprefix _] Hstep.
    pose proof (coupled_run_core_projection _ _ _ _ Hprefix) as Hcore.
    inversion Hstep as [m m' b action Hmachine |]; subst.
    destruct (machine_step_actor _ _ _ _ Hmachine) as (thread & Hlookup & _).
    assert (is_Some ((core_initial_state P).(core_threads) !! executing_agent a)) as [initial Hinitial].
    { apply (core_run_threads_dom _ _ _ _ _ Hcore). by exists thread. }
    cbn in Hinitial. apply lookup_fmap_Some in Hinitial as (body & _ & Hbody).
    by exists body.
  Qed.

  Local Lemma lookup_coupled_thread_view_complete p agent v :
    coupled_complete p.(coupled_position_state) -> lookup_coupled_thread_view p agent = Some v ->
    thread_complete v.(coupled_view_core).(view_thread) /\ v.(coupled_view_pending_gp) = None.
  Proof.
    intros [[Hthreads [Hpending _]] _] Hview. split.
    - apply (Hthreads agent). by eapply lookup_coupled_thread_view_lookup.
    - unfold lookup_coupled_thread_view in Hview.
      apply fmap_Some in Hview as (core & _ & Heq). subst v.
      cbn. by rewrite Hpending lookup_empty.
  Qed.

  Definition initial_thread_view body := CoupledThreadView
    (ThreadView (initial_thread body) 0 []) None.

  Section parallel.
    Context `{!invGS Σ, !stateG Σ}.

    (** Each fixed agent owns its thread token and continuation proof. The
        authoritative state interpretation is supplied once by the execution. *)
    Definition wp_parallel P G γ E p (Φ : agent_id -> coupled_thread_view -> iProp Σ) : iProp Σ :=
      [∗ map] agent ↦ body ∈ P.(program_agents),
        ∃ v, ⌜lookup_coupled_thread_view p agent = Some v⌝ ∗
          thread_token γ agent v.(coupled_view_core).(view_thread) ∗
          wp P G γ E agent v (Φ agent).

    Lemma wp_parallel_init P G γ E suffix final Φ :
      ([∗ map] agent ↦ body ∈ P.(program_agents), thread_token γ agent (initial_thread body)) -∗
      ([∗ map] agent ↦ body ∈ P.(program_agents),
        wp P G γ E agent (initial_thread_view body) (Φ agent)) -∗
      wp_parallel P G γ E (CoupledExecutionPosition [] (initial_coupled P) suffix final) Φ.
    Proof.
      iIntros "Htokens Hwps". iCombine "Htokens Hwps" as "Hagents".
      iEval (rewrite -big_sepM_sep) in "Hagents".
      iApply (big_sepM_mono with "Hagents"). iIntros (agent body Hbody) "[Htoken Hwp]".
      iExists (initial_thread_view body). iFrame. iPureIntro.
      unfold lookup_coupled_thread_view, lookup_thread_view, coupled_position_to_core. cbn.
      by rewrite lookup_fmap Hbody.
    Qed.

    Local Lemma wp_scheduled_step P G γ E prefix s a suffix final next v Φ :
      coupled_position P G
        (CoupledExecutionPosition prefix s (CoupledMachineAction a :: suffix) final) ->
      coupled_step P s (CoupledMachineAction a) next ->
      coupled_position P G
        (CoupledExecutionPosition (prefix ++ [CoupledMachineAction a]) next suffix final) ->
      lookup_coupled_thread_view
        (CoupledExecutionPosition prefix s (CoupledMachineAction a :: suffix) final)
        (executing_agent a) = Some v ->
      state_interp γ s ∗ thread_token γ (executing_agent a) v.(coupled_view_core).(view_thread) ∗
        wp P G γ E (executing_agent a) v Φ -∗
      |={E}[∅]▷=> ∃ v',
        ⌜lookup_coupled_thread_view
          (CoupledExecutionPosition (prefix ++ [CoupledMachineAction a]) next suffix final)
          (executing_agent a) = Some v'⌝ ∗
        state_interp γ next ∗ thread_token γ (executing_agent a) v'.(coupled_view_core).(view_thread) ∗
        wp P G γ E (executing_agent a) v' Φ.
    Proof.
      intros Hpos Hstep Hpos' Hview.
      assert (~ thread_complete v.(coupled_view_core).(view_thread)) as Hactive.
      { pose proof (lookup_coupled_thread_view_lookup _ _ _ Hview) as Hlookup.
        inversion Hstep as [m m' b action Hmachine |]; subst.
        destruct (machine_step_actor _ _ _ _ Hmachine) as (thread & Hthread & Hactive).
        rewrite Hthread in Hlookup. by injection Hlookup as <-. }
      iIntros "(Hstate & Hthread & Hwp)".
      destruct v as [[[statement continuation regs] index actions] pending].
      destruct statement;
        try (destruct continuation as [|frame continuation];
          first (exfalso; apply Hactive; done)).
      all: iEval (rewrite wp_unfold /wp_body /=) in "Hwp";
        iMod ("Hwp" $! prefix s a suffix final with "[] [$Hstate $Hthread]") as "Hstep";
        first by iPureIntro; split; [split|].
      all: iMod ("Hstep" $! next with "[]") as "Hnext"; first done.
      all: iModIntro; iNext; iExact "Hnext".
    Qed.

    (** One arbitrary scheduled action advances the whole collection. Builder
        actions preserve every local view; machine actions consume just their
        owner's WP. Each action is accounted for by one guarded update. *)
    Lemma wp_parallel_step P G γ E prefix s a suffix final next Φ :
      coupled_position P G (CoupledExecutionPosition prefix s (a :: suffix) final) ->
      coupled_step P s a next ->
      coupled_position P G (CoupledExecutionPosition (prefix ++ [a]) next suffix final) ->
      state_interp γ s ∗
        wp_parallel P G γ E (CoupledExecutionPosition prefix s (a :: suffix) final) Φ -∗
      |={E}[∅]▷=> state_interp γ next ∗
        wp_parallel P G γ E (CoupledExecutionPosition (prefix ++ [a]) next suffix final) Φ.
    Proof.
      intros Hpos Hstep Hpos'. iIntros "[Hstate Hpool]". destruct a as [a |].
      - destruct (coupled_step_actor_in_program _ _ _ _ _ _ _ _ Hpos Hstep) as [body Hbody].
        iDestruct (big_sepM_lookup_acc_impl (executing_agent a) body with "Hpool")
          as "[Hagent Hrest]"; first done.
        iDestruct "Hagent" as (v) "(%Hview & Hthread & Hwp)".
        iMod (wp_scheduled_step _ _ _ _ _ _ _ _ _ _ _ _ Hpos Hstep Hpos' Hview
          with "[$Hstate $Hthread $Hwp]") as "Hnext".
        iModIntro. iNext. iMod "Hnext" as (v') "(%Hview' & Hstate & Hthread & Hwp)".
        iModIntro. iFrame "Hstate". iApply ("Hrest" with "[] [Hthread Hwp]").
        { iIntros "!>" (other other_body) "%Hbody' %Hother Hother".
          iDestruct "Hother" as (other_view) "(%Hview_other & Hthread & Hwp)".
          iExists other_view. iFrame. iPureIntro.
          rewrite (lookup_coupled_thread_view_other_step _ _ _ _ _ _ _ _ Hstep); done. }
        iExists v'. iFrame. done.
      - iDestruct (state_interp_builder_step _ _ _ _ Hstep with "Hstate") as "Hstate".
        iApply fupd_mask_intro; first set_solver.
        iIntros "Hclose". iNext. iMod "Hclose" as "_". iModIntro. iFrame "Hstate".
        iApply (big_sepM_mono with "Hpool"). iIntros (agent body Hbody) "Hagent".
        iDestruct "Hagent" as (v) "(%Hview & Hthread & Hwp)".
        iExists v. iFrame. iPureIntro.
        by rewrite (lookup_coupled_thread_view_builder_step _ _ _ _ _ _ _ Hstep).
    Qed.

    (** Follow the supplied complete execution suffix, without choosing or
        serializing its schedule. The guards count all coupled actions. *)
    Lemma wp_parallel_run P G γ E prefix s actions final Φ :
      coupled_position P G (CoupledExecutionPosition prefix s actions final) ->
      state_interp γ s ∗
        wp_parallel P G γ E (CoupledExecutionPosition prefix s actions final) Φ -∗
      |={E}[∅]▷=>^(length actions) state_interp γ final ∗
        wp_parallel P G γ E (CoupledExecutionPosition (prefix ++ actions) final [] final) Φ.
    Proof.
      revert prefix s. induction actions as [|a actions IH]; intros prefix s Hpos.
      - destruct Hpos as (_ & Hrun & _). cbn in Hrun. inversion Hrun; subst.
        rewrite app_nil_r. iIntros "Hpool". iExact "Hpool".
      - destruct Hpos as (Hprefix & Hrun & Hcomplete & Hobligations & HG).
        cbn in Hprefix, Hrun, Hcomplete, Hobligations, HG.
        revert HG. inversion Hrun as [|s0 next final0 a0 actions0 Hstep Hrest]; subst. intros HG.
        assert (coupled_position P G
          (CoupledExecutionPosition (prefix ++ [a]) next actions final)) as Hpos'.
        { split.
          - eapply coupled_run_trans; first done. econstructor; first done. constructor.
          - split_and!; done. }
        iIntros "Hpool". cbn [length Nat.iter].
        iMod (wp_parallel_step with "Hpool") as "Hnext"; [split_and!; done | done | done |].
        iModIntro. iNext. iMod "Hnext" as "Hnext". iModIntro.
        rewrite (app_assoc prefix [a] actions). by iApply (IH with "Hnext").
    Qed.

    (** Completion exposes every agent's postcondition by separating
        conjunction. It neither duplicates resources nor removes step guards. *)
    Lemma wp_parallel_complete P G γ E p Φ :
      coupled_complete p.(coupled_position_state) ->
      wp_parallel P G γ E p Φ ={E}=∗
      [∗ map] agent ↦ body ∈ P.(program_agents),
        ∃ v, ⌜lookup_coupled_thread_view p agent = Some v⌝ ∗ Φ agent v.
    Proof.
      intros Hcomplete. iIntros "Hpool". iApply big_sepM_fupd.
      iApply (big_sepM_mono with "Hpool"). iIntros (agent body Hbody) "Hagent".
      iDestruct "Hagent" as (v) "(%Hview & Htoken & Hwp)".
      destruct (lookup_coupled_thread_view_complete _ _ _ Hcomplete Hview)
        as [[Hstmt Hks] Hpending].
      iEval (rewrite wp_unfold /wp_body Hstmt Hks Hpending) in "Hwp".
      iMod "Hwp" as "Hpost". iModIntro. iExists v. iFrame. done.
    Qed.

    Lemma wp_parallel_run_post P G γ E prefix s actions final Φ :
      coupled_position P G (CoupledExecutionPosition prefix s actions final) ->
      state_interp γ s ∗
        wp_parallel P G γ E (CoupledExecutionPosition prefix s actions final) Φ -∗
      |={E}[∅]▷=>^(length actions) |={E}=> state_interp γ final ∗
        ([∗ map] agent ↦ body ∈ P.(program_agents),
          ∃ v, ⌜lookup_coupled_thread_view
            (CoupledExecutionPosition (prefix ++ actions) final [] final) agent = Some v⌝ ∗
            Φ agent v).
    Proof.
      intros Hpos. iIntros "Hpool".
      iPoseProof (wp_parallel_run _ _ _ _ _ _ _ _ _ Hpos with "Hpool") as "Hrun".
      iApply (step_fupdN_wand with "Hrun").
      iIntros "[Hstate Hpool]".
      iMod (wp_parallel_complete with "Hpool") as "Hposts"; first exact (proj1 (proj2 (proj2 Hpos))).
      iModIntro. iFrame.
    Qed.
  End parallel.
End LkmmWpParallel.
