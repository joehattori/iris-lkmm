From Stdlib Require Import List.
From iris.base_logic.lib Require Import fancy_updates.
From iris.proofmode Require Import proofmode.
From iris_lkmm.logic Require Import wp state_interp graph_correspondence.
From iris_lkmm.lkmm Require Import execution memory_relations.
From iris_lkmm.operational Require Import lkmm_machine.
Import ListNotations.

Module LkmmWpMemory.
  Export LkmmWp LkmmStateInterp LkmmGraphCorrespondence.
  Import LkmmMachine LkmmMemoryRelations.

  Definition memory_view (thread : thread_state) index actions :=
    LkmmThreadView (ThreadView thread index actions) None.

  Local Lemma single_event_view prefix s a suffix final agent thread index actions
      label regs addr data ctrl :
    action_agent a = agent ->
    lookup_lkmm_thread_view
      (LkmmExecutionPosition prefix s (LkmmMachineAction (Execute a) :: suffix) final)
      agent = Some (memory_view thread index actions) ->
    lookup_lkmm_thread_view
      (LkmmExecutionPosition (prefix ++ [LkmmMachineAction (Execute a)])
        (LkmmState (with_core s.(lkmm_machine)
          (add_single_event s.(lkmm_machine).(machine_core) agent thread label regs addr data ctrl))
          s.(lkmm_builder)) suffix final) agent =
      Some (memory_view (emitted_thread thread regs) (S index) (actions ++ [a])).
  Proof.
    intros Hagent Hview.
    unfold lookup_lkmm_thread_view, lookup_thread_view, lkmm_position_to_core in *.
    cbn in Hview. apply fmap_Some in Hview as (cv & Hcore & Heq).
    apply fmap_Some in Hcore as (actual & Hlookup & Hcv). subst cv.
    injection Heq as Hthread Hindex Hactions Hpending. subst actual.
    cbn. rewrite lookup_insert_eq -Hpending /=.
    unfold next_agent_index at 1. cbn. rewrite lookup_insert_eq -Hindex.
    rewrite flat_map_app /= /agent_actions filter_app filter_cons_True; last done.
    cbn. by rewrite -Hactions.
  Qed.

  (** No emission-order premise: [source] is looked up in the complete
      candidate. This proposition contains no Iris resources. *)
  Definition read_from (G : core_candidate) (read source : event_id)
      (loc : location) (observed : value) : Prop :=
    rf G.(candidate_rf) source read /\
      exists ev, lookup_event G.(candidate_events) source = Some ev /\
      is_write ev /\ location_of ev = Some loc /\ value_of ev = Some observed.

  Lemma position_read_from P G p read agent index mode mark loc observed :
    lkmm_position P G p ->
    lookup_event p.(lkmm_position_state).(lkmm_machine).(machine_core).(core_events) read =
      Some (EAgent agent index (LMemory AccessRead mode mark loc observed)) ->
    exists source, read_from G read source loc observed.
  Proof.
    intros Hpos Hread.
    destruct (lkmm_position_consistent_program_graph _ _ _ Hpos) as [Hgraph _].
    destruct (candidate_position_read_source _ _ _ _ _ Hgraph
      (lkmm_position_projection _ _ _ Hpos) Hread eq_refl) as (source & Hrf & Hwf & _).
    destruct Hwf as (we & re & val & Hw & Hr & Hwrite & _ & Hloc & Hwval & Hrval).
    pose proof (candidate_position_events _ _ _ (lkmm_position_projection _ _ _ Hpos)
      _ _ Hread) as Hr'.
    rewrite Hr' in Hr. injection Hr as <-. cbn in Hloc, Hrval.
    unfold same_location, same_attribute in Hloc.
    destruct Hloc as (location & Hwl & Hrl).
    change (lookup_event G.(candidate_events) source ≫= location_of = Some location) in Hwl.
    change (lookup_event G.(candidate_events) read ≫= location_of = Some location) in Hrl.
    rewrite Hw /= in Hwl. rewrite Hr' /= in Hrl.
    exists source. split; first done. exists we. split_and!; congruence.
  Qed.

  Section rules.
    Context `{!invGS Σ, !stateG Σ}.

    (** Loading retains the owned prefix history. The observed value comes
        from rf in [G], and can differ from every value in that history.
        The accessor lends a share at [E'] and restores [E] before the
        continuation, allowing ownership to live in a shared invariant. *)
    Lemma wp_load_acc P G γ E E' agent dst mode address loc address_sources
        ks regs index actions Φ :
      eval_location regs address = Some (loc, address_sources) ->
      (▷ |={E,E'}=> ∃ q history,
        memory_own γ.(memory_names_of) loc q history ∗
        ∀ read observed source,
        ⌜read_from G read source loc observed⌝ -∗
        memory_own γ.(memory_names_of) loc q history -∗
        event_fact γ read (EAgent agent index
          (LMemory AccessRead (load_access_mode mode) NotRmw loc observed)) -∗
        |={E',E}=> wp P G γ E agent
          (memory_view (ThreadState SSkip ks (<[dst := RegValue observed {[read]}]> regs))
            (S index) (actions ++ [CoreObserve agent observed])) Φ) -∗
      wp P G γ E agent
        (memory_view (ThreadState (SLoad dst mode address) ks regs) index actions) Φ.
    Proof.
      intros Heval. iIntros "Hacc". iApply wp_lift_execute; try done.
      { intros [[Hskip _] _]. discriminate. }
      iNext. iIntros (prefix s a suffix final next v') "%Hfacts [Hmemory #Hnew]".
      iMod "Hacc" as (q history) "[Hloc Hwp]".
      destruct Hfacts as ((Hpos & Hview) & Hagent & Hstep & Hnext & Hview').
      pose proof (lookup_lkmm_thread_view_lookup _ _ _ Hview) as Hlookup.
      pose proof (lookup_lkmm_thread_view_index _ _ _ Hview) as Hindex.
      pose proof (core_run_allocation_wf _ _ _
        (proj1 (lkmm_position_projection _ _ _ Hpos))) as Halloc.
      inversion Hstep as [m m' b action Hmachine |]; subst.
      inversion Hmachine as [m0 core' action thread Hthread Hordinary Hready Hcore | | | |]; subst.
      cbn in Hlookup. rewrite Hlookup in Hthread.
      injection Hthread as <-. inversion Hcore; subst; simplify_eq/=.
      erewrite (single_event_view _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl Hview) in Hview'.
      injection Hview' as <-.
      destruct (position_read_from _ _ _ _ _ _ _ _ _ _ Hnext (lookup_insert_eq _ _ _))
        as [source Hsource].
      iDestruct (big_sepM_lookup _ _ m.(machine_core).(core_next_id) with "Hnew") as "#Hread".
      { apply lookup_difference_Some. split; first apply lookup_insert_eq.
        by apply core_next_id_fresh. }
      iDestruct (memory_auth_read _ _ read
        (EAgent agent (next_agent_index m.(machine_core) agent)
          (LMemory AccessRead (load_access_mode mode0) NotRmw loc observed))
        with "Hmemory") as "Hmemory"; try done.
      { by apply core_next_id_fresh. }
      iMod ("Hwp" with "[] Hloc Hread") as "Hwp"; first done.
      iModIntro. iFrame.
    Qed.

    Lemma wp_load P G γ E agent dst mode address loc address_sources
        ks regs index actions q history Φ :
      eval_location regs address = Some (loc, address_sources) ->
      memory_own γ.(memory_names_of) loc q history -∗
      (▷ ∀ read observed source,
        ⌜read_from G read source loc observed⌝ -∗
        memory_own γ.(memory_names_of) loc q history -∗
        event_fact γ read (EAgent agent index
          (LMemory AccessRead (load_access_mode mode) NotRmw loc observed)) -∗
        wp P G γ E agent
          (memory_view (ThreadState SSkip ks (<[dst := RegValue observed {[read]}]> regs))
            (S index) (actions ++ [CoreObserve agent observed])) Φ) -∗
      wp P G γ E agent
        (memory_view (ThreadState (SLoad dst mode address) ks regs) index actions) Φ.
    Proof.
      intros Heval. iIntros "Hloc Hwp". iApply (wp_load_acc _ _ _ _ E); first done.
      iNext. iModIntro. iExists q, history. iFrame "Hloc".
      iIntros (read observed source) "Hsource Hloc Hread". iModIntro.
      iApply ("Hwp" with "Hsource Hloc Hread").
    Qed.

    (** Storing appends an emitted write to the owned history. No read is
        promised to observe this write, and no coherence position is chosen. *)
    Lemma wp_store_acc P G γ E E' agent mode address expression loc address_sources result
        ks regs index actions Φ :
      eval_location regs address = Some (loc, address_sources) ->
      eval_expr regs expression = Some result ->
      (▷ |={E,E'}=> ∃ history,
        memory_own γ.(memory_names_of) loc 1 history ∗
        ∀ write,
        let ev := EAgent agent index
          (LMemory AccessWrite (store_access_mode mode) NotRmw loc result.(reg_integer)) in
        memory_own γ.(memory_names_of) loc 1 (<[write := ev]> history) -∗
        event_fact γ write ev -∗
        |={E',E}=> wp P G γ E agent (memory_view (ThreadState SSkip ks regs)
          (S index) (actions ++ [CoreEmit agent])) Φ) -∗
      wp P G γ E agent
        (memory_view (ThreadState (SStore mode address expression) ks regs) index actions) Φ.
    Proof.
      intros Haddr Hexpr. iIntros "Hacc". iApply wp_lift_execute; try done.
      { intros [[Hskip _] _]. discriminate. }
      iNext. iIntros (prefix s a suffix final next v') "%Hfacts [Hmemory #Hnew]".
      iMod "Hacc" as (history) "[Hloc Hwp]".
      destruct Hfacts as ((Hpos & Hview) & Hagent & Hstep & Hnext & Hview').
      pose proof (lookup_lkmm_thread_view_lookup _ _ _ Hview) as Hlookup.
      pose proof (lookup_lkmm_thread_view_index _ _ _ Hview) as Hindex.
      pose proof (core_run_allocation_wf _ _ _
        (proj1 (lkmm_position_projection _ _ _ Hpos))) as Halloc.
      inversion Hstep as [m m' b action Hmachine |]; subst.
      inversion Hmachine as [m0 core' action thread Hthread Hordinary Hready Hcore | | | |]; subst.
      cbn in Hlookup. rewrite Hlookup in Hthread.
      injection Hthread as <-. inversion Hcore; subst; simplify_eq/=.
      erewrite (single_event_view _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl Hview) in Hview'.
      injection Hview' as <-.
      iDestruct (big_sepM_lookup _ _ m.(machine_core).(core_next_id) with "Hnew") as "#Hwrite".
      { apply lookup_difference_Some. split; first apply lookup_insert_eq.
        by apply core_next_id_fresh. }
      iMod (memory_auth_store _ _ loc history m.(machine_core).(core_next_id)
        (EAgent agent (next_agent_index m.(machine_core) agent)
          (LMemory AccessWrite (store_access_mode mode0) NotRmw loc result.(reg_integer)))
        with "[$Hmemory $Hloc]") as "[Hmemory Hloc]"; try done.
      { by apply core_next_id_fresh. }
      iMod ("Hwp" with "Hloc Hwrite") as "Hwp". iModIntro. iFrame.
    Qed.

    Lemma wp_store P G γ E agent mode address expression loc address_sources result
        ks regs index actions history Φ :
      eval_location regs address = Some (loc, address_sources) ->
      eval_expr regs expression = Some result ->
      memory_own γ.(memory_names_of) loc 1 history -∗
      (▷ ∀ write,
        let ev := EAgent agent index
          (LMemory AccessWrite (store_access_mode mode) NotRmw loc result.(reg_integer)) in
        memory_own γ.(memory_names_of) loc 1 (<[write := ev]> history) -∗
        event_fact γ write ev -∗
        wp P G γ E agent (memory_view (ThreadState SSkip ks regs)
          (S index) (actions ++ [CoreEmit agent])) Φ) -∗
      wp P G γ E agent
        (memory_view (ThreadState (SStore mode address expression) ks regs) index actions) Φ.
    Proof.
      intros Haddr Hexpr. iIntros "Hloc Hwp". iApply (wp_store_acc _ _ _ _ E); try done.
      iNext. iModIntro. iExists history. iFrame "Hloc".
      iIntros (write) "Hloc Hwrite". iModIntro. iApply ("Hwp" with "Hloc Hwrite").
    Qed.
  End rules.
End LkmmWpMemory.
