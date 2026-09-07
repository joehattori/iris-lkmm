From Stdlib Require Import List Lia.
From stdpp Require Import gmap fin_sets tactics list.
From iris_lkmm.lang Require Import core_agent_replay.
From iris_lkmm.lkmm Require Import rcu_renaming.
Import ListNotations.

Module LkmmCoreRenaming.
  Export LkmmCoreAgentReplay RcuRenaming.

  Record core_state_renaming (f : event_id -> event_id) (source target : core_state) : Prop := {
    core_renaming_events : event_renaming f source.(core_events) target.(core_events);
    core_renaming_threads : target.(core_threads) = rename_thread f <$> source.(core_threads);
    core_renaming_indices : forall t, next_agent_index target t = next_agent_index source t;
    core_renaming_next : target.(core_next_id) = source.(core_next_id);
    core_renaming_rmw : target.(core_rmw) = rename_edges f source.(core_rmw);
    core_renaming_addr : target.(core_direct_addr) = rename_edges f source.(core_direct_addr);
    core_renaming_data : target.(core_direct_data) = rename_edges f source.(core_direct_data);
    core_renaming_ctrl : target.(core_direct_ctrl) = rename_edges f source.(core_direct_ctrl)
  }.

  Lemma rename_origins_agree f g xs :
    (forall i, i ∈ xs -> f i = g i) -> rename_origins f xs = rename_origins g xs.
  Proof.
    intros Hagree. apply set_eq. intros i. unfold rename_origins. rewrite !elem_of_map.
    split; intros (old & -> & Hin); exists old; split; try done;
      by rewrite (Hagree old Hin).
  Qed.

  Lemma rename_frames_agree f g ks :
    (forall i, i ∈ control_origins ks -> f i = g i) ->
    map (rename_frame f) ks = map (rename_frame g) ks.
  Proof.
    induction ks as [|[stmt | xs] ks IH]; intros Hagree; simpl in *; first done.
    - f_equal. by apply IH.
    - f_equal.
      + f_equal. apply rename_origins_agree. intros i Hi. apply Hagree. set_solver.
      + apply IH. intros i Hi. apply Hagree. set_solver.
  Qed.

  Lemma rename_thread_agree f g source t th :
    core_provenance_wf source -> source.(core_threads) !! t = Some th ->
    (forall i, owned source.(core_events) t i -> f i = g i) ->
    rename_thread f th = rename_thread g th.
  Proof.
    intros Hwf Hth Hagree. destruct (Hwf t th Hth) as [Hregs Hctrl].
    assert (forall i, origin_before source t i -> f i = g i) as Horigin.
    { intros i (n & label & Hlookup & _). apply Hagree. unfold owned.
      unfold lookup_event in Hlookup. by rewrite Hlookup. }
    unfold rename_thread. f_equal.
    - apply rename_frames_agree. intros i Hi. apply Horigin, Hctrl, Hi.
    - apply map_fmap_ext. intros r v Hv. unfold rename_value. f_equal.
      apply rename_origins_agree. intros i Hi. apply Horigin. by eapply Hregs.
  Qed.

  Definition agent_local_edges E (edges : edge_set) : Prop :=
    forall x y, (x,y) ∈ edges -> po E x y.

  Lemma generated_edges_local s :
    core_generated_wf s ->
    agent_local_edges s.(core_events) s.(core_rmw) /\
    agent_local_edges s.(core_events) s.(core_direct_addr) /\
    agent_local_edges s.(core_events) s.(core_direct_data) /\
    agent_local_edges s.(core_events) s.(core_direct_ctrl).
  Proof.
    intros (_ & _ & Hrmw & Haddr & Hdata & Hctrl). split_and!;
      intros x y Hxy.
    - by eapply memory_relations.LkmmMemoryRelations.rmw_wf_po.
    - exact (proj2 (proj2 (Haddr x y Hxy))).
    - exact (proj2 (proj2 (Hdata x y Hxy))).
    - exact (proj2 (proj2 (Hctrl x y Hxy))).
  Qed.

  Lemma replay_events_agree f g E t :
    (forall i, owned E t i -> f i = g i) -> replay_events f t E = replay_events g t E.
  Proof.
    intros Hagree. apply set_eq. intros [i ev]. unfold replay_events. rewrite !elem_of_map.
    assert (forall p : event_id * event,
      p ∈ filter (fun p => agent_of p.2 = Some t) (event_entries E) -> f p.1 = g p.1) as H.
    { intros [old original] Hp. apply elem_of_filter in Hp as [Hagent Hp].
      apply elem_of_map_to_set_pair in Hp. change (E !! old = Some original) in Hp. apply Hagree. unfold owned. simpl. by rewrite Hp. }
    split; intros (p & Heq & Hp); exists p; split; try done;
      rewrite (H p Hp) in *; done.
  Qed.

  Lemma replay_edges_agree f g E t edges :
    agent_local_edges E edges -> (forall i, owned E t i -> f i = g i) ->
    replay_edges f E t edges = replay_edges g E t edges.
  Proof.
    intros Hlocal Hagree. apply set_eq. intros [i j]. unfold replay_edges. rewrite !elem_of_map.
    assert (forall p : edge, p ∈ filter (fun p => owned E t p.2) edges ->
      f p.1 = g p.1 /\ f p.2 = g p.2) as H.
    { intros [x y] Hp. apply elem_of_filter in Hp as [Hy Hp].
      split; last by apply Hagree.
      destruct (Hlocal x y Hp) as (owner & nx & ny & lx & ly & Hx & Hlookup & _).
      unfold owned in Hy. simpl in Hy. unfold lookup_event in Hlookup, Hx. rewrite Hlookup in Hy. simpl in Hy. injection Hy as ->.
      apply Hagree. unfold owned. simpl. by rewrite Hx. }
    split; intros (p & Heq & Hp); exists p; split; try done;
      destruct (H p Hp) as [H1 H2]; rewrite H1, H2 in *; done.
  Qed.

  Lemma core_step_threads_dom P s a s' t :
    core_step P s a s' ->
    (is_Some (s'.(core_threads) !! t) <-> is_Some (s.(core_threads) !! t)).
  Proof.
    intros Hstep. destruct Hstep; simpl;
      match goal with Hth : core_threads ?s !! ?owner = Some ?th |- _ =>
        destruct (decide (t = owner)) as [-> | Hne];
        [rewrite lookup_insert_eq; split; [intros _; by exists th | intros _; by eexists] |
         by rewrite lookup_insert_ne]
      end.
  Qed.

  Lemma core_run_threads_dom P s actions s' t :
    core_run P s actions s' ->
    (is_Some (s'.(core_threads) !! t) <-> is_Some (s.(core_threads) !! t)).
  Proof.
    intros Hrun. induction Hrun; first done.
    rewrite IHHrun. by eapply core_step_threads_dom.
  Qed.

  Lemma core_step_events_source P s a s' i ev :
    core_step P s a s' -> lookup_event s'.(core_events) i = Some ev ->
    lookup_event s.(core_events) i = Some ev \/
    exists t n label th, ev = EAgent t n label /\ s.(core_threads) !! t = Some th.
  Proof.
    intros Hstep Hlookup. destruct Hstep; simpl in Hlookup; try by left.
    all: unfold lookup_event in Hlookup;
      repeat (apply lookup_insert_Some in Hlookup;
        destruct Hlookup as [[_ <-] | [_ Hlookup]];
        first (right; do 4 eexists; split; [done | eassumption])); by left.
  Qed.

  Lemma core_run_events_source P s actions s' i ev :
    core_run P s actions s' -> lookup_event s'.(core_events) i = Some ev ->
    lookup_event s.(core_events) i = Some ev \/
    exists t n label th, ev = EAgent t n label /\ s.(core_threads) !! t = Some th.
  Proof.
    intros Hrun. induction Hrun; intros Hlookup; first by left.
    destruct (IHHrun Hlookup) as [Hmid | (t & n & label & th & -> & Hth)].
    - by eapply core_step_events_source.
    - assert (is_Some (core_threads state1 !! t)) as [old Hold].
      { apply (core_step_threads_dom P state1 action state2 t H). by exists th. }
      right. by exists t, n, label, old.
  Qed.

  Lemma core_run_initial_events P actions s i loc val :
    core_run P (core_initial_state P) actions s ->
    (lookup_event s.(core_events) i = Some (EInitWrite loc val) <->
      lookup_event (core_initial_events P) i = Some (EInitWrite loc val)).
  Proof.
    intros Hrun. split.
    - intros Hlookup. destruct (core_run_events_source _ _ _ _ _ _ Hrun Hlookup)
        as [Hinitial | (t & n & label & th & Hbad & _)]; first done. discriminate.
    - apply (core_run_events_included _ _ _ _ Hrun (core_initial_allocation_wf P)).
  Qed.

  Lemma core_run_agent_in_program P actions s i t n label :
    core_run P (core_initial_state P) actions s ->
    lookup_event s.(core_events) i = Some (EAgent t n label) ->
    is_Some (P.(program_agents) !! t).
  Proof.
    intros Hrun Hlookup. destruct (core_run_events_source _ _ _ _ _ _ Hrun Hlookup)
      as [Hinitial | (owner & index & lab & th & Heq & Hth)].
    - exfalso. pose proof (insert_initial_events_shape (initial_entries P) 0 ∅ i
        (EAgent t n label)) as Hshape.
      destruct (Hshape ltac:(intros x ev Hbad; discriminate Hbad) Hinitial)
        as (loc & val & Hbad). discriminate.
    - injection Heq as <- <- <-. simpl in Hth.
      apply lookup_fmap_Some in Hth as (body & _ & Hbody). by exists body.
  Qed.

  Corollary core_state_renaming_rcu f source target :
    core_state_renaming f source target -> core_allocation_wf source ->
    rcu_replay_wf source.(core_events) -> rcu_replay_wf target.(core_events).
  Proof.
    intros Hren [HE _]. eapply rcu_replay_wf_rename; [exact (core_renaming_events _ _ _ Hren) | done].
  Qed.

  Lemma core_step_actor P s a s' :
    core_step P s a s' -> is_Some (s.(core_threads) !! core_action_agent a).
  Proof. intros Hstep. destruct Hstep; simpl; by eexists. Qed.

  Lemma core_run_absent_index P s actions s' t :
    core_run P s actions s' -> s.(core_threads) !! t = None ->
    next_agent_index s' t = next_agent_index s t.
  Proof.
    intros Hrun. induction Hrun; intros Hnone; first done.
    assert (core_threads state2 !! t = None) as Hnone'.
    { destruct (core_threads state2 !! t) as [th |] eqn:Hlookup; last done.
      exfalso. assert (is_Some (core_threads state1 !! t)) as [old Hold].
      { apply (core_step_threads_dom _ _ _ _ _ H). by exists th. }
      congruence. }
    rewrite (IHHrun Hnone'). eapply core_step_other_index; first done.
    intros Heq. destruct (core_step_actor _ _ _ _ H) as [th Hth]. rewrite Heq, Hnone in Hth.
    discriminate.
  Qed.

End LkmmCoreRenaming.
