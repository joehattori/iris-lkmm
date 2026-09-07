From Stdlib Require Import List Lia.
From stdpp Require Import gmap fin_map_dom fin_sets tactics list.
From iris_lkmm.lang Require Import core_renaming.
Import ListNotations.

(** Whole-program Core replay.  The certificates below retain the exact
    per-agent graph/provenance correspondence at each replay boundary.  They
    are proof witnesses, not additional Core transition rules or state. *)
Module LkmmCoreReplay.
  Export LkmmCoreRenaming.

  Fixpoint serial_actions (agents : list agent_id) (actions : list core_action) :=
    match agents with
    | [] => []
    | t :: rest => agent_actions t actions ++ serial_actions rest actions
    end.

  Lemma agent_actions_app t xs ys :
    agent_actions t (xs ++ ys) = agent_actions t xs ++ agent_actions t ys.
  Proof. unfold agent_actions. apply filter_app. Qed.

  Lemma agent_actions_same t actions :
    agent_actions t (agent_actions t actions) = agent_actions t actions.
  Proof. unfold agent_actions. apply list_filter_filter_l. done. Qed.

  Lemma agent_actions_other t other actions :
    t <> other -> agent_actions t (agent_actions other actions) = [].
  Proof.
    intros Hne. apply elem_of_nil_inv. intros a Hin.
    apply list_elem_of_filter in Hin as [Ht Hin].
    apply list_elem_of_filter in Hin as [Hother _]. congruence.
  Qed.

  Lemma serial_actions_agent_absent agents actions t :
    t ∉ agents -> agent_actions t (serial_actions agents actions) = [].
  Proof.
    induction agents as [|other rest IH]; intros Hnotin; first done.
    simpl. rewrite agent_actions_app, agent_actions_other by set_solver.
    simpl. apply IH. set_solver.
  Qed.

  (** Serialization changes only the interleaving.  Every agent keeps exactly
      its original actions, including all observed values and silent steps. *)
  Theorem serial_actions_agent agents actions t :
    NoDup agents -> t ∈ agents ->
    agent_actions t (serial_actions agents actions) = agent_actions t actions.
  Proof.
    intros Hnodup. induction Hnodup as [|other rest Hnotin Hnodup IH]; intros Hin;
      first set_solver.
    simpl. rewrite agent_actions_app. destruct (decide (t = other)) as [-> | Hne].
    - rewrite agent_actions_same, serial_actions_agent_absent by done.
      by rewrite app_nil_r.
    - rewrite agent_actions_other by done. simpl. apply IH. set_solver.
  Qed.

  (** The list contains precisely the program's agents, each exactly once. *)
  Definition program_agent_enumeration (P : core_program) (agents : list agent_id) : Prop :=
    NoDup agents /\ forall t, t ∈ agents <-> is_Some (P.(program_agents) !! t).

  Definition program_agents_list (P : core_program) : list agent_id :=
    elements (dom P.(program_agents) : gset agent_id).

  Lemma program_agents_list_enumeration P : program_agent_enumeration P (program_agents_list P).
  Proof.
    unfold program_agent_enumeration, program_agents_list. split; first apply NoDup_elements.
    intros t. rewrite elem_of_elements. apply elem_of_dom.
  Qed.

  Inductive serial_replay (P : core_program) (actions : list core_action)
      (source : core_state) : list agent_id -> core_state -> core_state -> Prop :=
  | SerialReplayNil base : serial_replay P actions source [] base base
  | SerialReplayCons t rest base next final :
      core_run P base (agent_actions t actions) next ->
      replay_state (replay_id source.(core_events) t base.(core_next_id))
        source.(core_events) t base source next ->
      serial_replay P actions source rest next final ->
      serial_replay P actions source (t :: rest) base final.

  Lemma serial_replay_run P actions source agents base final :
    serial_replay P actions source agents base final ->
    core_run P base (serial_actions agents actions) final.
  Proof.
    intros Hreplay. induction Hreplay; simpl; first constructor.
    by eapply core_run_append.
  Qed.

  (** Induction invariant: remaining agents are initial, while agents outside
      the remaining list have already completed.  Replaying the head moves
      exactly one agent from the former group to the latter. *)
  Lemma complete_core_run_replay_remaining P actions source agents base :
    complete_core_run P actions source -> NoDup agents -> core_allocation_wf base ->
    (forall t, t ∈ agents ->
      base.(core_threads) !! t = (core_initial_state P).(core_threads) !! t /\
      next_agent_index base t = 0) ->
    (forall t th, t ∉ agents -> base.(core_threads) !! t = Some th -> thread_complete th) ->
    exists final, serial_replay P actions source agents base final /\ core_complete final.
  Proof.
    intros Hsource Hnodup. revert base.
    induction Hnodup as [|t rest Hnotin Hnodup IH]; intros base Halloc Hinitial Hfinished.
    - exists base. split; first constructor. intros other th Hlookup.
      eapply (Hfinished other th); [set_solver | done].
    - destruct (Hinitial t ltac:(set_solver)) as [Hthread Hindex].
      destruct (complete_core_run_replay_agent _ _ _ _ _ Hsource Halloc Hthread Hindex)
        as (next & Hrun & Hmatch & Hcomplete).
      assert (core_allocation_wf next) as Hnext.
      { by eapply core_run_preserves_allocation. }
      assert (forall other, other ∈ rest ->
        next.(core_threads) !! other = (core_initial_state P).(core_threads) !! other /\
        next_agent_index next other = 0) as Hrest_initial.
      { intros other Hin. assert (other <> t) as Hne by set_solver.
        destruct (Hinitial other ltac:(set_solver)) as [Hth Hidx]. split.
        - rewrite (replay_other_threads _ _ _ _ _ _ Hmatch other Hne). done.
        - rewrite (agent_replay_other_index _ _ _ _ _ _ Hrun Hne). done. }
      assert (forall other th, other ∉ rest -> next.(core_threads) !! other = Some th ->
        thread_complete th) as Hrest_finished.
      { intros other th Hout Hlookup. destruct (decide (other = t)) as [-> | Hne].
        - by apply Hcomplete.
        - rewrite (replay_other_threads _ _ _ _ _ _ Hmatch other Hne) in Hlookup.
          eapply (Hfinished other th); [set_solver | done]. }
      destruct (IH next Hnext Hrest_initial Hrest_finished) as (final & Hserial & Hfinal).
      exists final. split; last done. by econstructor.
  Qed.

  (** Any enumeration of the program's agents, with no repetitions, gives
      a completed serialized Core run with the original per-agent actions. *)
  Local Lemma complete_core_run_replay_order_certificate P actions source agents :
    complete_core_run P actions source -> program_agent_enumeration P agents ->
    exists final,
      complete_core_run P (serial_actions agents actions) final /\
      serial_replay P actions source agents (core_initial_state P) final.
  Proof.
    intros Hsource [Hnodup Hcover].
    destruct (complete_core_run_replay_remaining P actions source agents (core_initial_state P)
      Hsource Hnodup (core_initial_allocation_wf P)) as (final & Hserial & Hfinal).
    - intros t Hin. split; done.
    - intros t th Hout Hlookup. simpl in Hlookup.
      apply lookup_fmap_Some in Hlookup as (body & Hth & Hbody).
      exfalso. apply Hout, Hcover. by exists body.
    - exists final. split; last done. split; last done. by apply serial_replay_run in Hserial.
  Qed.

  Fixpoint agent_replay_base (source : core_state) (agents : list agent_id)
      (start : event_id) (t : agent_id) : event_id :=
    match agents with
    | [] => start
    | owner :: rest => if decide (t = owner) then start
        else agent_replay_base source rest (start + next_agent_index source owner) t
    end.

  (** Locate an original event's agent and local position, then assign its
      ID in that agent's serialized block. Initial and absent IDs are fixed.
      This function describes the proof correspondence, not a program rewrite. *)
  Definition whole_replay_id source agents start i : event_id :=
    match source.(core_events) !! i with
    | Some (EAgent t n _) => agent_replay_base source agents start t + n
    | _ => i
    end.

  Fixpoint gathered_events (f : event_id -> event_id) (E : event_structure) (agents : list agent_id) : gset (event_id * event) :=
    match agents with
    | [] => ∅
    | t :: rest => replay_events f t E ∪ gathered_events f E rest
    end.
  Fixpoint gathered_edges (f : event_id -> event_id) (E : event_structure) (edges : edge_set) (agents : list agent_id) : edge_set :=
    match agents with
    | [] => ∅
    | t :: rest => replay_edges f E t edges ∪ gathered_edges f E edges rest
    end.
  Fixpoint agent_event_count source (agents : list agent_id) : nat :=
    match agents with
    | [] => 0
    | t :: rest => next_agent_index source t + agent_event_count source rest
    end.

  Record serial_replay_fields f source agents base final : Prop := {
    serial_events : event_entries final.(core_events) =
      event_entries base.(core_events) ∪ gathered_events f source.(core_events) agents;
    serial_threads : forall t, t ∈ agents ->
      final.(core_threads) !! t = rename_thread f <$> source.(core_threads) !! t;
    serial_other_threads : forall t, t ∉ agents ->
      final.(core_threads) !! t = base.(core_threads) !! t;
    serial_indices : forall t, t ∈ agents -> next_agent_index final t = next_agent_index source t;
    serial_other_indices : forall t, t ∉ agents -> next_agent_index final t = next_agent_index base t;
    serial_next : final.(core_next_id) = base.(core_next_id) + agent_event_count source agents;
    serial_rmw : final.(core_rmw) = base.(core_rmw) ∪ gathered_edges f source.(core_events) source.(core_rmw) agents;
    serial_addr : final.(core_direct_addr) = base.(core_direct_addr) ∪
      gathered_edges f source.(core_events) source.(core_direct_addr) agents;
    serial_data : final.(core_direct_data) = base.(core_direct_data) ∪
      gathered_edges f source.(core_events) source.(core_direct_data) agents;
    serial_ctrl : final.(core_direct_ctrl) = base.(core_direct_ctrl) ∪
      gathered_edges f source.(core_events) source.(core_direct_ctrl) agents
  }.

  Lemma serial_replay_fields_sound P actions source agents base final f :
    serial_replay P actions source agents base final -> NoDup agents ->
    core_generated_wf source ->
    (forall t i n label, t ∈ agents -> source.(core_events) !! i = Some (EAgent t n label) ->
      f i = agent_replay_base source agents base.(core_next_id) t + n) ->
    serial_replay_fields f source agents base final.
  Proof.
    intros Hserial. induction Hserial as [base | t rest base next final Hrun Hmatch Hserial IH];
      intros Hnodup Hgenerated Hagree.
    - constructor; simpl; try (intros; done); try set_solver; lia.
    - inversion Hnodup as [|? ? Hnotin Hrest]; subst.
      assert (forall i, owned source.(core_events) t i ->
        replay_id source.(core_events) t base.(core_next_id) i = f i) as Hhead.
      { intros i Howned. unfold owned in Howned.
        destruct (core_events source !! i) as [[loc val | owner n label] |] eqn:Hlookup;
          simpl in Howned; try discriminate. injection Howned as ->.
        rewrite (replay_id_lookup _ _ _ _ _ _ Hlookup),
          (Hagree t i n label ltac:(set_solver) Hlookup). simpl. by rewrite decide_True. }
      assert (serial_replay_fields f source rest next final) as Htail.
      { apply IH; try done. intros other i n label Hin Hlookup.
        rewrite (Hagree other i n label ltac:(set_solver) Hlookup).
        simpl. rewrite decide_False by set_solver.
        by rewrite (replay_next _ _ _ _ _ _ Hmatch). }
      destruct Htail. destruct (generated_edges_local source Hgenerated)
        as (Hrmw & Haddr & Hdata & Hctrl).
      constructor; simpl.
      + rewrite serial_events0, (replay_event_map _ _ _ _ _ _ Hmatch),
          (replay_events_agree _ _ _ _ Hhead). set_solver.
      + intros other Hin. destruct (decide (other = t)) as [-> | Hne].
        * rewrite serial_other_threads0 by done.
          rewrite (replay_thread _ _ _ _ _ _ Hmatch).
          destruct (core_threads source !! t) as [th |] eqn:Hth; simpl; last done.
          f_equal. eapply rename_thread_agree; [exact (proj1 (proj2 Hgenerated)) | done | done].
        * apply serial_threads0. set_solver.
      + intros other Hout. rewrite serial_other_threads0 by set_solver.
        apply (replay_other_threads _ _ _ _ _ _ Hmatch). set_solver.
      + intros other Hin. destruct (decide (other = t)) as [-> | Hne].
        * rewrite serial_other_indices0 by done. exact (replay_index _ _ _ _ _ _ Hmatch).
        * apply serial_indices0. set_solver.
      + intros other Hout. rewrite serial_other_indices0 by set_solver.
        eapply agent_replay_other_index; first done. set_solver.
      + rewrite serial_next0, (replay_next _ _ _ _ _ _ Hmatch). lia.
      + rewrite serial_rmw0, (replay_rmw _ _ _ _ _ _ Hmatch),
          (replay_edges_agree _ _ _ _ _ Hrmw Hhead). set_solver.
      + rewrite serial_addr0, (replay_addr _ _ _ _ _ _ Hmatch),
          (replay_edges_agree _ _ _ _ _ Haddr Hhead). set_solver.
      + rewrite serial_data0, (replay_data _ _ _ _ _ _ Hmatch),
          (replay_edges_agree _ _ _ _ _ Hdata Hhead). set_solver.
      + rewrite serial_ctrl0, (replay_ctrl _ _ _ _ _ _ Hmatch),
          (replay_edges_agree _ _ _ _ _ Hctrl Hhead). set_solver.
  Qed.


  Lemma gathered_events_spec f E agents i ev :
    (i,ev) ∈ gathered_events f E agents <->
    exists old t, t ∈ agents /\ E !! old = Some ev /\ agent_of ev = Some t /\ f old = i.
  Proof.
    induction agents as [|t rest IH]; simpl; first set_solver.
    rewrite elem_of_union, IH. unfold replay_events. rewrite elem_of_map.
    split.
    - intros [(p & Heq & Hp) | (old & owner & Hin & Hlookup & Hagent & Hf)].
      + destruct p as [old original]. simpl in Heq. injection Heq as Hi Hev.
        subst original i. apply elem_of_filter in Hp as [Hagent Hp].
        apply elem_of_map_to_set_pair in Hp. exists old, t. split_and!; try done; set_solver.
      + exists old, owner. split_and!; try done; set_solver.
    - intros (old & owner & Hin & Hlookup & Hagent & Hf).
      apply elem_of_cons in Hin as [-> | Hin].
      + left. exists (old,ev). split; first (simpl; by rewrite Hf).
        apply elem_of_filter. split; first done. by apply elem_of_map_to_set_pair.
      + right. exists old, owner. done.
  Qed.

  Lemma gathered_edges_spec f E edges agents i j :
    (i,j) ∈ gathered_edges f E edges agents <->
    exists x y t, t ∈ agents /\ (x,y) ∈ edges /\ owned E t y /\ f x = i /\ f y = j.
  Proof.
    induction agents as [|t rest IH]; simpl; first set_solver.
    rewrite elem_of_union, IH. unfold replay_edges. rewrite elem_of_map.
    split.
    - intros [([x y] & Heq & Hp) | (x & y & owner & Hin & Hedge & Howned & Hx & Hy)].
      + simpl in Heq. injection Heq as Hi Hj. apply elem_of_filter in Hp as [Howned Hp].
        exists x, y, t. split_and!; try done; set_solver.
      + exists x, y, owner. split_and!; try done; set_solver.
    - intros (x & y & owner & Hin & Hedge & Howned & Hx & Hy).
      apply elem_of_cons in Hin as [-> | Hin].
      + left. exists (x,y). split; first (simpl; by rewrite Hx, Hy).
        apply elem_of_filter. done.
      + right. exists x, y, owner. done.
  Qed.

  Lemma gathered_edges_all P actions source agents f edges :
    core_run P (core_initial_state P) actions source -> program_agent_enumeration P agents ->
    agent_local_edges source.(core_events) edges ->
    gathered_edges f source.(core_events) edges agents = rename_edges f edges.
  Proof.
    intros Hrun [_ Hcover] Hlocal. apply set_eq. intros [i j].
    rewrite gathered_edges_spec. unfold rename_edges. rewrite elem_of_map.
    split.
    - intros (x & y & t & Hin & Hedge & Howned & Hx & Hy).
      exists (x,y). split; last done. simpl. by rewrite Hx, Hy.
    - intros ([x y] & Heq & Hedge). simpl in Heq. injection Heq as Hi Hj.
      destruct (Hlocal x y Hedge) as (t & nx & ny & lx & ly & Hx & Hy & Hlt).
      exists x, y, t. split_and!; try done.
      + apply Hcover. by eapply core_run_agent_in_program.
      + unfold owned. unfold lookup_event in Hy. by rewrite Hy.
  Qed.

  Lemma serial_fields_event_renaming P actions source agents final :
    core_run P (core_initial_state P) actions source -> program_agent_enumeration P agents ->
    serial_replay_fields
      (whole_replay_id source agents (core_next_id (core_initial_state P)))
      source agents (core_initial_state P) final ->
    event_renaming (whole_replay_id source agents (core_next_id (core_initial_state P)))
      source.(core_events) final.(core_events).
  Proof.
    intros Hrun Horder Hfields.
    set (f := whole_replay_id source agents (core_next_id (core_initial_state P))).
    assert (forall i loc val, lookup_event source.(core_events) i = Some (EInitWrite loc val) ->
      f i = i) as Hinit.
    { intros i loc val Hlookup. unfold f, whole_replay_id. unfold lookup_event in Hlookup.
      by rewrite Hlookup. }
    assert (forall i ev, lookup_event source.(core_events) i = Some ev ->
      lookup_event final.(core_events) (f i) = Some ev) as Hforward.
    { intros i ev Hlookup. apply (elem_of_map_to_set_pair (C:=gset (event_id * event))).
      change ((f i, ev) ∈ event_entries final.(core_events)).
      rewrite (serial_events _ _ _ _ _ Hfields). apply elem_of_union.
      destruct ev as [loc val | t n label].
      - left. rewrite (Hinit i loc val Hlookup).
        apply elem_of_map_to_set_pair. by apply (core_run_initial_events _ _ _ _ _ _ Hrun).
      - right. apply gathered_events_spec. exists i, t. split_and!; try done.
        apply (proj2 Horder). by eapply core_run_agent_in_program. }
    constructor; try done.
    - intros x y ex ey Hx Hy Hf.
      pose proof (Hforward x ex Hx) as Hfx. pose proof (Hforward y ey Hy) as Hfy.
      rewrite Hf in Hfx. assert (ex = ey) as -> by congruence.
      destruct ey as [loc val | t n label].
      + rewrite (Hinit x loc val Hx), (Hinit y loc val Hy) in Hf. done.
      + destruct (core_run_allocation_wf _ _ _ Hrun) as [HE _]. by eapply HE.
    - intros j ev Hj. apply (elem_of_map_to_set_pair (C:=gset (event_id * event)) (core_events final) j ev) in Hj.
      change ((j,ev) ∈ event_entries final.(core_events)) in Hj.
      rewrite (serial_events _ _ _ _ _ Hfields) in Hj.
      apply elem_of_union in Hj as [Hinitial | Hagent].
      + apply elem_of_map_to_set_pair in Hinitial.
        assert (lookup_event source.(core_events) j = Some ev) as Hsource.
        { apply (core_run_events_included _ _ _ _ Hrun (core_initial_allocation_wf P)). done. }
        assert (forall i original, lookup_event (∅ : event_structure) i = Some original ->
          exists loc val, original = EInitWrite loc val) as Hempty.
        { intros i original Hbad. discriminate Hbad. }
        destruct (insert_initial_events_shape (initial_entries P) 0 (∅ : event_structure) j ev
          Hempty Hinitial) as (loc & val & ->).
        exists j. split; first done. by apply Hinit with loc val.
      + apply gathered_events_spec in Hagent as (old & t & Hin & Hlookup & Hagent & Hf).
        by exists old.
  Qed.


  Lemma agent_event_count_ext s s' agents :
    (forall t, t ∈ agents -> next_agent_index s' t = next_agent_index s t) ->
    agent_event_count s' agents = agent_event_count s agents.
  Proof.
    induction agents as [|t rest IH]; intros Hsame; simpl; first done.
    rewrite (Hsame t ltac:(set_solver)), IH; first done.
    intros other Hin. apply Hsame. set_solver.
  Qed.

  Lemma agent_event_count_insert s s' agents t n :
    NoDup agents -> t ∈ agents ->
    s'.(core_next_indices) = <[t := n]> s.(core_next_indices) ->
    agent_event_count s' agents + next_agent_index s t = agent_event_count s agents + n.
  Proof.
    intros Hnodup. induction Hnodup as [|other rest Hnotin Hnodup IH];
      intros Hin Hindices; first set_solver.
    simpl. destruct (decide (t = other)) as [-> | Hne].
    - assert (next_agent_index s' other = n) as Hindex.
      { unfold next_agent_index. rewrite Hindices, lookup_insert_eq. done. }
      assert (agent_event_count s' rest = agent_event_count s rest) as Hrest.
      { apply agent_event_count_ext. intros t Ht. unfold next_agent_index.
        rewrite Hindices, lookup_insert_ne; [done | set_solver]. }
      rewrite Hindex, Hrest. lia.
    - assert (next_agent_index s' other = next_agent_index s other) as Hindex.
      { unfold next_agent_index. rewrite Hindices, lookup_insert_ne; [done | congruence]. }
      specialize (IH ltac:(set_solver) Hindices). rewrite Hindex. lia.
  Qed.

  Lemma core_step_event_count P s a s' agents :
    core_step P s a s' -> NoDup agents ->
    (forall t, is_Some (s.(core_threads) !! t) -> t ∈ agents) ->
    s'.(core_next_id) + agent_event_count s agents =
      s.(core_next_id) + agent_event_count s' agents.
  Proof.
    intros Hstep Hnodup Hcover.
    pose proof (Hcover _ (core_step_actor _ _ _ _ Hstep)) as Hin.
    destruct Hstep; simpl in Hin.
    all: match goal with |- core_next_id ?dst + agent_event_count ?src ?ts = _ =>
      first [assert (agent_event_count dst ts = agent_event_count src ts) as Heq
          by (apply agent_event_count_ext; intros; reflexivity);
        rewrite Heq; reflexivity |
        pose proof (agent_event_count_insert src dst ts _ _ Hnodup Hin eq_refl) as Hcount;
        simpl in Hcount |- *; lia]
      end.
  Qed.

  Lemma core_run_event_count P s actions s' agents :
    core_run P s actions s' -> NoDup agents ->
    (forall t, is_Some (s.(core_threads) !! t) -> t ∈ agents) ->
    s'.(core_next_id) + agent_event_count s agents =
      s.(core_next_id) + agent_event_count s' agents.
  Proof.
    intros Hrun Hnodup. induction Hrun; intros Hcover; first done.
    pose proof (core_step_event_count _ _ _ _ _ H Hnodup Hcover) as Hstep.
    assert (forall t, is_Some (core_threads state2 !! t) -> t ∈ agents) as Hcover'.
    { intros t Ht. apply Hcover. by apply (core_step_threads_dom _ _ _ _ _ H). }
    specialize (IHHrun Hcover'). lia.
  Qed.

  Lemma core_run_next_total P actions source agents :
    core_run P (core_initial_state P) actions source -> program_agent_enumeration P agents ->
    source.(core_next_id) = (core_initial_state P).(core_next_id) + agent_event_count source agents.
  Proof.
    intros Hrun [Hnodup Hcover].
    assert (agent_event_count (core_initial_state P) agents = 0) as Hzero.
    { clear. induction agents; simpl; done. }
    pose proof (core_run_event_count _ _ _ _ _ Hrun Hnodup) as Hcount.
    specialize (Hcount ltac:(intros t [th Hth]; apply Hcover;
      apply lookup_fmap_Some in Hth as (body & _ & Hbody); by exists body)).
    rewrite Hzero in Hcount. lia.
  Qed.

  Theorem serial_replay_core_state_renaming P actions source agents final :
    core_run P (core_initial_state P) actions source -> program_agent_enumeration P agents ->
    serial_replay P actions source agents (core_initial_state P) final ->
    core_state_renaming
      (whole_replay_id source agents (core_next_id (core_initial_state P))) source final.
  Proof.
    intros Hrun Horder Hserial.
    pose proof (core_run_generated_wf _ _ _ Hrun) as Hgenerated.
    set (f := whole_replay_id source agents (core_next_id (core_initial_state P))).
    assert (serial_replay_fields f source agents (core_initial_state P) final) as Hfields.
    { eapply serial_replay_fields_sound; [done | exact (proj1 Horder) | done |].
      intros t i n label Hin Hlookup. unfold f, whole_replay_id. by rewrite Hlookup. }
    assert (forall t, t ∉ agents ->
      source.(core_threads) !! t = None /\ (core_initial_state P).(core_threads) !! t = None) as Habsent.
    { intros t Hout.
      assert ((core_initial_state P).(core_threads) !! t = None) as Hinitial.
      { simpl. rewrite lookup_fmap. destruct (program_agents P !! t) as [body |] eqn:Hbody;
          last done. exfalso. apply Hout, (proj2 Horder). by exists body. }
      split; last done. destruct (core_threads source !! t) as [th |] eqn:Hth; last done.
      exfalso. assert (is_Some ((core_initial_state P).(core_threads) !! t)) as [old Hold].
      { apply (core_run_threads_dom _ _ _ _ _ Hrun). by exists th. } congruence. }
    destruct (generated_edges_local _ Hgenerated) as (Hrmw & Haddr & Hdata & Hctrl).
    constructor.
    - by eapply serial_fields_event_renaming.
    - apply map_eq. intros t. rewrite lookup_fmap.
      destruct (decide (t ∈ agents)) as [Hin | Hout].
      + by apply (serial_threads _ _ _ _ _ Hfields).
      + destruct (Habsent t Hout) as [Hsource Hinitial].
        rewrite (serial_other_threads _ _ _ _ _ Hfields t Hout), Hsource, Hinitial. done.
    - intros t. destruct (decide (t ∈ agents)) as [Hin | Hout].
      + by apply (serial_indices _ _ _ _ _ Hfields).
      + destruct (Habsent t Hout) as [_ Hinitial].
        rewrite (serial_other_indices _ _ _ _ _ Hfields t Hout).
        symmetry. by eapply core_run_absent_index.
    - rewrite (serial_next _ _ _ _ _ Hfields).
      symmetry. by eapply core_run_next_total.
    - rewrite (serial_rmw _ _ _ _ _ Hfields). simpl. rewrite union_empty_l_L.
      by eapply gathered_edges_all.
    - rewrite (serial_addr _ _ _ _ _ Hfields). simpl. rewrite union_empty_l_L.
      by eapply gathered_edges_all.
    - rewrite (serial_data _ _ _ _ _ Hfields). simpl. rewrite union_empty_l_L.
      by eapply gathered_edges_all.
    - rewrite (serial_ctrl _ _ _ _ _ Hfields). simpl. rewrite union_empty_l_L.
      by eapply gathered_edges_all.
  Qed.

  (** Whole-program replay now returns one common renaming for the complete
      final Core state, in addition to the individual replay certificates. *)
  Theorem complete_core_run_replay_order P actions source agents :
    complete_core_run P actions source -> program_agent_enumeration P agents ->
    exists final f,
      complete_core_run P (serial_actions agents actions) final /\
      serial_replay P actions source agents (core_initial_state P) final /\
      core_state_renaming f source final.
  Proof.
    intros Hrun Horder.
    destruct (complete_core_run_replay_order_certificate _ _ _ _ Hrun Horder)
      as (final & Hfinal & Hserial).
    exists final, (whole_replay_id source agents (core_next_id (core_initial_state P))).
    split; first done. split; first done.
    eapply serial_replay_core_state_renaming; [exact (proj1 Hrun) | done | done].
  Qed.

  Theorem complete_core_run_replay P actions source :
    complete_core_run P actions source ->
    exists final f,
      complete_core_run P (serial_actions (program_agents_list P) actions) final /\
      serial_replay P actions source (program_agents_list P) (core_initial_state P) final /\
      core_state_renaming f source final.
  Proof.
    intros Hrun. apply complete_core_run_replay_order; first done.
    apply program_agents_list_enumeration.
  Qed.

End LkmmCoreReplay.
