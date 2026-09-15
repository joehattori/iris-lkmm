From Stdlib Require Import List Lia.
From stdpp Require Import gmap fin_sets tactics list.
From iris_lkmm.lang Require Import program_graph.
Import ListNotations.

(** Per-agent replay of Core executions.  The final source event map is used
    only to name the correspondence in the proof; it is never an argument of
    [core_step] or a field of the replayed state. *)
Module LkmmCoreAgentReplay.
  Export LkmmProgramGraph.

  Definition core_action_agent (a : core_action) : agent_id :=
    match a with CoreSilent t | CoreEmit t | CoreObserve t _ => t end.

  Definition agent_actions (t : agent_id) (actions : list core_action) :=
    filter (fun a => core_action_agent a = t) actions.

  Definition rename_origins (f : event_id -> event_id) (xs : origins) : origins :=
    set_map f xs.

  Definition rename_value f (v : reg_value) : reg_value :=
    RegValue v.(reg_integer) (rename_origins f v.(reg_origins)).

  Definition rename_frame f (k : frame) : frame :=
    match k with KSeq s => KSeq s | KControl xs => KControl (rename_origins f xs) end.

  Definition rename_thread f (th : thread_state) : thread_state :=
    ThreadState th.(thread_statement) (map (rename_frame f) th.(thread_continuation))
      (rename_value f <$> th.(thread_registers)).

  Lemma rename_origins_empty f : rename_origins f ∅ = ∅.
  Proof. apply set_map_empty. Qed.

  Lemma rename_origins_singleton f x : rename_origins f {[x]} = {[f x]}.
  Proof. apply set_map_singleton_L. Qed.

  Lemma rename_origins_union f xs ys :
    rename_origins f (xs ∪ ys) = rename_origins f xs ∪ rename_origins f ys.
  Proof. apply set_map_union_L. Qed.

  Lemma eval_expr_rename f regs e :
    eval_expr (rename_value f <$> regs) e = rename_value f <$> eval_expr regs e.
  Proof.
    induction e as [z | r | op e1 IH1 e2 IH2]; simpl.
    - unfold rename_value. simpl. by rewrite rename_origins_empty.
    - apply lookup_fmap.
    - rewrite IH1, IH2. destruct (eval_expr regs e1), (eval_expr regs e2); simpl; try done.
      unfold rename_value. simpl. by rewrite rename_origins_union.
  Qed.

  Lemma eval_location_rename f regs e loc xs :
    eval_location regs e = Some (loc, xs) ->
    eval_location (rename_value f <$> regs) e = Some (loc, rename_origins f xs).
  Proof.
    unfold eval_location. rewrite eval_expr_rename.
    destruct (eval_expr regs e) as [v |]; simpl; last done.
    destruct (decide (0 <= reg_integer v)%Z); simpl; last done.
    intros H; simplify_eq. done.
  Qed.

  Lemma control_origins_rename f ks :
    control_origins (map (rename_frame f) ks) = rename_origins f (control_origins ks).
  Proof.
    induction ks as [|[s|xs] ks IH]; simpl.
    - by rewrite rename_origins_empty.
    - done.
    - by rewrite IH, rename_origins_union.
  Qed.

  Lemma thread_control_origins_rename f th :
    thread_control_origins (rename_thread f th) = rename_origins f (thread_control_origins th).
  Proof. apply control_origins_rename. Qed.

  Lemma rename_thread_complete f th :
    thread_complete th -> thread_complete (rename_thread f th).
  Proof. intros [Hs Hk]. split; simpl; by rewrite ?Hs, ?Hk. Qed.

  Definition replay_id (E : event_structure) (t : agent_id) (base : nat) (i : event_id) :=
    match E !! i with
    | Some (EAgent owner index _) => if decide (owner = t) then base + index else i
    | _ => i
    end.

  Definition owned (E : event_structure) (t : agent_id) (i : event_id) : Prop :=
    (E !! i ≫= agent_of) = Some t.

  Global Instance owned_dec E t i : Decision (owned E t i).
  Proof. unfold owned. apply _. Defined.

  Definition event_entries (E : event_structure) : gset (event_id * event) :=
    map_to_set pair E.

  Definition replay_events (f : event_id -> event_id) (t : agent_id) (E : event_structure) : gset (event_id * event) :=
    set_map (fun p : event_id * event => (f p.1, p.2))
      (filter (fun p : event_id * event => agent_of p.2 = Some t) (event_entries E)).

  (** Generated RMW and dependency edges are agent-local.  Selecting their
      destination selects the agent's edges, while renaming both endpoints. *)
  Definition replay_edges (f : event_id -> event_id) (E : event_structure)
      (t : agent_id) (edges : edge_set) : edge_set :=
    set_map (fun p => (f p.1, f p.2)) (filter (fun p => owned E t p.2) edges).

  Lemma replay_id_lookup E t base i index label :
    E !! i = Some (EAgent t index label) -> replay_id E t base i = base + index.
  Proof. intros H. unfold replay_id. by rewrite H, decide_True. Qed.

  Lemma owned_lookup E t i owner index label :
    E !! i = Some (EAgent owner index label) -> (owned E t i <-> owner = t).
  Proof. intros H. unfold owned. rewrite H. simpl. naive_solver. Qed.

  Lemma replay_id_injective E t base i j :
    event_structure_wf E -> owned E t i -> owned E t j ->
    replay_id E t base i = replay_id E t base j -> i = j.
  Proof.
    intros Hwf Hi Hj. unfold owned in Hi, Hj.
    destruct (E !! i) as [[loc val|owner index label]|] eqn:Hi'; simpl in Hi; try done.
    destruct (E !! j) as [[loc' val'|owner' index' label']|] eqn:Hj'; simpl in Hj; try done.
    simplify_eq. rewrite (replay_id_lookup _ _ _ _ _ _ Hi'),
      (replay_id_lookup _ _ _ _ _ _ Hj'). intros Hindex.
    assert (index = index') by lia. subst index'. by eapply Hwf.
  Qed.

  Lemma event_entries_insert E i ev :
    E !! i = None -> event_entries (<[i := ev]> E) = {[(i, ev)]} ∪ event_entries E.
  Proof. apply map_to_set_insert_L. Qed.

  Lemma replay_events_insert f t E i owner index label :
    E !! i = None ->
    replay_events f t (<[i := EAgent owner index label]> E) =
      (if decide (owner = t) then {[(f i, EAgent owner index label)]} else ∅) ∪
      replay_events f t E.
  Proof.
    intros Hfresh. unfold replay_events. rewrite event_entries_insert by done.
    rewrite filter_union_L, set_map_union_L by typeclasses eauto.
    destruct (decide (owner = t)) as [-> | Hne].
    - rewrite filter_singleton_True_L by (try done; typeclasses eauto).
      by rewrite set_map_singleton_L by typeclasses eauto.
    - rewrite filter_singleton_False_L by (try typeclasses eauto; simpl; congruence).
      by rewrite set_map_empty.
  Qed.

  Lemma replay_edges_empty f E t : replay_edges f E t ∅ = ∅.
  Proof. unfold replay_edges. by rewrite filter_empty_L, set_map_empty by typeclasses eauto. Qed.

  Lemma replay_edges_union f E t xs ys :
    replay_edges f E t (xs ∪ ys) = replay_edges f E t xs ∪ replay_edges f E t ys.
  Proof. unfold replay_edges. by rewrite filter_union_L, set_map_union_L by typeclasses eauto. Qed.

  Lemma replay_edges_singleton f E t x y :
    replay_edges f E t {[(x,y)]} = if decide (owned E t y) then {[(f x,f y)]} else ∅.
  Proof.
    unfold replay_edges. destruct (decide (owned E t y)).
    - rewrite filter_singleton_True_L by (try done; typeclasses eauto).
      by rewrite set_map_singleton_L by typeclasses eauto.
    - rewrite filter_singleton_False_L by (try done; typeclasses eauto). by rewrite set_map_empty.
  Qed.

  Lemma replay_origin_edges f E t xs y :
    replay_edges f E t (origin_edges xs y) =
      if decide (owned E t y) then origin_edges (rename_origins f xs) (f y) else ∅.
  Proof.
    apply set_eq. intros [a b]. unfold replay_edges.
    rewrite elem_of_map. setoid_rewrite elem_of_filter.
    setoid_rewrite origin_edges_spec.
    destruct (decide (owned E t y)); simpl.
    - change ((exists x : edge, (a,b) = (f x.1,f x.2) /\
        (owned E t x.2 /\ (x.1 ∈ xs /\ x.2 = y))) <->
        edge_relation (origin_edges (rename_origins f xs) (f y)) a b).
      rewrite origin_edges_spec. unfold rename_origins. rewrite elem_of_map.
      split; [intros ([x z] & Heq & Hown & Hx & Hz); simpl in *; naive_solver |
        intros ((x & -> & Hx) & ->); exists (x,y); naive_solver].
    - rewrite elem_of_empty. split; last done. intros ([x z] & Heq & Hown & Hx & Hz).
      simpl in *. naive_solver.
  Qed.

  (** Exact projection of a source prefix into a replay context.  Existing
      context events and edges are retained; only the selected agent runs. *)
  Record replay_state (f : event_id -> event_id) (E : event_structure)
      (t : agent_id) (base src dst : core_state) : Prop := ReplayState {
    replay_thread : dst.(core_threads) !! t = rename_thread f <$> src.(core_threads) !! t;
    replay_other_threads : forall other, other <> t ->
      dst.(core_threads) !! other = base.(core_threads) !! other;
    replay_index : next_agent_index dst t = next_agent_index src t;
    replay_next : dst.(core_next_id) = (base.(core_next_id) + next_agent_index src t)%nat;
    replay_event_map : event_entries dst.(core_events) =
      event_entries base.(core_events) ∪ replay_events f t src.(core_events);
    replay_rmw : dst.(core_rmw) = base.(core_rmw) ∪ replay_edges f E t src.(core_rmw);
    replay_addr : dst.(core_direct_addr) =
      base.(core_direct_addr) ∪ replay_edges f E t src.(core_direct_addr);
    replay_data : dst.(core_direct_data) =
      base.(core_direct_data) ∪ replay_edges f E t src.(core_direct_data);
    replay_ctrl : dst.(core_direct_ctrl) =
      base.(core_direct_ctrl) ∪ replay_edges f E t src.(core_direct_ctrl)
  }.

  Lemma replay_event_lookup f E t base src dst i index label :
    replay_state f E t base src dst ->
    (dst.(core_events) !! i = Some (EAgent t index label) <->
      base.(core_events) !! i = Some (EAgent t index label) \/
      exists old, src.(core_events) !! old = Some (EAgent t index label) /\ f old = i).
  Proof.
    intros Hmatch. rewrite <- (elem_of_map_to_set_pair (C:=gset (event_id * event))
      (core_events dst) i (EAgent t index label)).
    change ((i, EAgent t index label) ∈ event_entries (core_events dst) <->
      base.(core_events) !! i = Some (EAgent t index label) \/
      exists old, src.(core_events) !! old = Some (EAgent t index label) /\ f old = i).
    rewrite (replay_event_map _ _ _ _ _ _ Hmatch), elem_of_union.
    unfold event_entries, replay_events.
    rewrite (elem_of_map_to_set_pair (C:=gset (event_id * event))
      (core_events base) i (EAgent t index label)), elem_of_map.
    split.
    - intros [Hbase | ([old ev] & Heq & Hentry)]; first by left.
      simpl in Heq. injection Heq as Hid Hev. subst ev i. apply elem_of_filter in Hentry as [_ Hentry].
      apply elem_of_map_to_set_pair in Hentry. right. by exists old.
    - intros [Hbase | (old & Hsrc & <-)]; first by left.
      right. exists (old, EAgent t index label). split; first done.
      apply elem_of_filter. split; first done. by apply elem_of_map_to_set_pair.
  Qed.

  Lemma replay_update f E t base src dst th :
    replay_state f E t base src dst ->
    replay_state f E t base (update_thread src t th)
      (update_thread dst t (rename_thread f th)).
  Proof.
    intros H. destruct H. constructor; simpl; try done.
    - by rewrite !lookup_insert_eq.
    - intros other Hne. rewrite lookup_insert_ne by done. auto.
  Qed.

  Lemma replay_update_other f E t base src dst owner th :
    replay_state f E t base src dst -> owner <> t ->
    replay_state f E t base (update_thread src owner th) dst.
  Proof.
    intros H Hne. destruct H. constructor; simpl; try done.
    by rewrite lookup_insert_ne by congruence.
  Qed.

  Local Lemma union_interleave {A} `{Countable A} (X Y Z : gset A) :
    X ∪ (Y ∪ Z) = Y ∪ (X ∪ Z).
  Proof. set_solver. Qed.

  Lemma replay_single f E t base src dst th label regs addr data ctrl :
    replay_state f E t base src dst ->
    src.(core_events) !! src.(core_next_id) = None ->
    dst.(core_events) !! dst.(core_next_id) = None ->
    owned E t src.(core_next_id) -> f src.(core_next_id) = dst.(core_next_id) ->
    replay_state f E t base
      (add_single_event src t th label regs addr data ctrl)
      (add_single_event dst t (rename_thread f th) label (rename_value f <$> regs)
        (rename_origins f addr) (rename_origins f data) (rename_origins f ctrl)).
  Proof.
    intros H Hsrc Hdst Howned Hf. destruct H.
    constructor; simpl.
    - by rewrite !lookup_insert_eq.
    - intros other Hne. rewrite lookup_insert_ne by done. auto.
    - unfold next_agent_index in *. simpl. rewrite !lookup_insert_eq. simpl. unfold next_agent_index. congruence.
    - unfold next_agent_index. simpl. rewrite lookup_insert_eq. simpl. unfold next_agent_index in *. lia.
    - rewrite event_entries_insert by done.
      rewrite replay_events_insert by done.
      rewrite decide_True by done. rewrite <-replay_index0, Hf, replay_event_map0. apply union_interleave.
    - done.
    - unfold add_origin_edges. rewrite replay_edges_union, replay_origin_edges.
      rewrite decide_True by done. rewrite Hf, replay_addr0. by rewrite union_assoc_L.
    - unfold add_origin_edges. rewrite replay_edges_union, replay_origin_edges.
      rewrite decide_True by done. rewrite Hf, replay_data0. by rewrite union_assoc_L.
    - unfold add_origin_edges. rewrite replay_edges_union, replay_origin_edges.
      rewrite decide_True by done. rewrite Hf, replay_ctrl0. by rewrite union_assoc_L.
  Qed.

  Lemma replay_single_other f E t base src dst owner th label regs addr data ctrl :
    replay_state f E t base src dst -> owner <> t ->
    src.(core_events) !! src.(core_next_id) = None ->
    ~ owned E t src.(core_next_id) ->
    replay_state f E t base
      (add_single_event src owner th label regs addr data ctrl) dst.
  Proof.
    intros H Hne Hfresh Howned. destruct H. constructor; simpl; try done.
    - rewrite lookup_insert_ne by congruence. done.
    - unfold next_agent_index in *. simpl. rewrite lookup_insert_ne by congruence. done.
    - unfold next_agent_index in *. simpl. rewrite lookup_insert_ne by congruence. done.
    - rewrite replay_events_insert by done. rewrite decide_False by done.
      by rewrite union_empty_l_L.
    - unfold add_origin_edges. rewrite replay_edges_union, replay_origin_edges.
      rewrite decide_False by done. by rewrite union_empty_r_L.
    - unfold add_origin_edges. rewrite replay_edges_union, replay_origin_edges.
      rewrite decide_False by done. by rewrite union_empty_r_L.
    - unfold add_origin_edges. rewrite replay_edges_union, replay_origin_edges.
      rewrite decide_False by done. by rewrite union_empty_r_L.
  Qed.

  Lemma allocated_successor_fresh s :
    core_allocation_wf s -> s.(core_events) !! S s.(core_next_id) = None.
  Proof.
    intros (_ & Hids & _). destruct (core_events s !! S (core_next_id s)) eqn:Hlookup;
      last done. specialize (Hids _ _ Hlookup). lia.
  Qed.

  Local Lemma union_interleave_two {A} `{Countable A} (X Y B Z : gset A) :
    X ∪ (Y ∪ (B ∪ Z)) = B ∪ (X ∪ (Y ∪ Z)).
  Proof. set_solver. Qed.

  Lemma replay_rmw_events f E t base src dst th mode loc old new regs addr data ctrl :
    replay_state f E t base src dst ->
    core_allocation_wf src -> core_allocation_wf dst ->
    owned E t src.(core_next_id) -> owned E t (S src.(core_next_id)) ->
    f src.(core_next_id) = dst.(core_next_id) ->
    f (S src.(core_next_id)) = S dst.(core_next_id) ->
    replay_state f E t base
      (add_rmw_events src t th mode loc old new regs addr data ctrl)
      (add_rmw_events dst t (rename_thread f th) mode loc old new (rename_value f <$> regs)
        (rename_origins f addr) (rename_origins f data) (rename_origins f ctrl)).
  Proof.
    intros H Hsrc Hdst Howned Howned' Hf Hf'.
    pose proof (core_next_id_fresh _ Hsrc) as Hfresh.
    pose proof (core_next_id_fresh _ Hdst) as Hfresh'.
    unfold lookup_event in Hfresh, Hfresh'.
    pose proof (allocated_successor_fresh _ Hsrc) as Hsucc.
    pose proof (allocated_successor_fresh _ Hdst) as Hsucc'.
    destruct H. constructor; simpl.
    - by rewrite !lookup_insert_eq.
    - intros other Hne. rewrite lookup_insert_ne by done. auto.
    - unfold next_agent_index. simpl. rewrite !lookup_insert_eq. simpl. congruence.
    - unfold next_agent_index. simpl. rewrite lookup_insert_eq. simpl.
      change (S (S (core_next_id dst)) = core_next_id base + S (S (next_agent_index src t))). lia.
    - rewrite !event_entries_insert.
      2: { exact Hfresh'. }
      2: { apply lookup_insert_None. split; [exact Hsucc' | lia]. }
      rewrite !replay_events_insert by (try done; apply lookup_insert_None; split; [done | lia]).
      rewrite !decide_True by done.
      rewrite replay_events_insert by done. rewrite decide_True by done.
      rewrite <-replay_index0, Hf, Hf', replay_event_map0.
      apply union_interleave_two.
    - rewrite replay_edges_union, replay_edges_singleton.
      rewrite decide_True by done. rewrite Hf, Hf', replay_rmw0. apply union_interleave.
    - unfold add_origin_edges. rewrite !replay_edges_union, !replay_origin_edges.
      rewrite !decide_True by done. rewrite Hf, Hf', replay_addr0. by rewrite !union_assoc_L.
    - unfold add_origin_edges. rewrite replay_edges_union, replay_origin_edges.
      rewrite decide_True by done. rewrite Hf', replay_data0. by rewrite union_assoc_L.
    - unfold add_origin_edges. rewrite replay_edges_union, replay_origin_edges.
      rewrite decide_True by done. rewrite Hf', replay_ctrl0. by rewrite union_assoc_L.
  Qed.

  Lemma replay_rmw_other f E t base src dst owner th mode loc old new regs addr data ctrl :
    replay_state f E t base src dst -> owner <> t -> core_allocation_wf src ->
    ~ owned E t src.(core_next_id) -> ~ owned E t (S src.(core_next_id)) ->
    replay_state f E t base
      (add_rmw_events src owner th mode loc old new regs addr data ctrl) dst.
  Proof.
    intros H Hne Halloc Howned Howned'.
    pose proof (core_next_id_fresh _ Halloc) as Hfresh.
    unfold lookup_event in Hfresh.
    pose proof (allocated_successor_fresh _ Halloc) as Hsucc.
    destruct H. constructor; simpl; try done.
    - rewrite lookup_insert_ne by congruence. done.
    - unfold next_agent_index in *. simpl. rewrite lookup_insert_ne by congruence. done.
    - unfold next_agent_index in *. simpl. rewrite lookup_insert_ne by congruence. done.
    - rewrite !replay_events_insert by (try done; apply lookup_insert_None; split; [done | lia]).
      rewrite !decide_False by done.
      rewrite replay_events_insert by done. rewrite decide_False by done.
      by rewrite !union_empty_l_L.
    - rewrite replay_edges_union, replay_edges_singleton.
      rewrite decide_False by done. by rewrite union_empty_l_L.
    - unfold add_origin_edges. rewrite !replay_edges_union, !replay_origin_edges.
      rewrite !decide_False by done. by rewrite !union_empty_r_L.
    - unfold add_origin_edges. rewrite replay_edges_union, replay_origin_edges.
      rewrite decide_False by done. by rewrite union_empty_r_L.
    - unfold add_origin_edges. rewrite replay_edges_union, replay_origin_edges.
      rewrite decide_False by done. by rewrite union_empty_r_L.
  Qed.

  Lemma included_insert_lookup E E' i ev :
    event_structure_included (<[i := ev]> E) E' -> E' !! i = Some ev.
  Proof. intros H. apply H. apply lookup_insert_eq. Qed.

  Lemma included_double_insert_lookup E E' i j ev ev' :
    i <> j -> event_structure_included (<[j := ev']> (<[i := ev]> E)) E' ->
    E' !! i = Some ev.
  Proof.
    intros Hne H. apply H. unfold lookup_event.
    rewrite (lookup_insert_ne (<[i := ev]> E) j i ev') by congruence. apply lookup_insert_eq.
  Qed.

  Local Ltac remember_emissions :=
    match goal with
    | Hinc : event_structure_included (<[?j := ?ev']> (<[?i := ?ev]> ?es)) ?E |- _ =>
        let Hw := fresh "Hwrite" in let Hr := fresh "Hread" in
        pose proof (included_insert_lookup _ _ _ _ Hinc) as Hw;
        pose proof (included_double_insert_lookup es E i j ev ev' ltac:(lia) Hinc) as Hr
    | Hinc : event_structure_included (<[?i := ?ev]> ?es) ?E |- _ =>
        let He := fresh "Hemitted" in
        pose proof (included_insert_lookup _ _ _ _ Hinc) as He
    | _ => idtac
    end.

  Local Ltac solve_ownership :=
    match goal with
    | H : ?E !! ?i = Some (EAgent ?owner ?idx ?label) |- owned ?E ?t ?i =>
        apply (proj2 (owned_lookup E t i owner idx label H)); congruence
    | H : ?E !! ?i = Some (EAgent ?owner ?idx ?label) |- ~ owned ?E ?t ?i =>
        rewrite (owned_lookup E t i owner idx label H); congruence
    end.

  Lemma rename_registers_empty f : (rename_value f <$> (∅ : registers)) = ∅.
  Proof. apply fmap_empty. Qed.

  Lemma rename_register_insert f (regs : registers) (r : reg) v :
    rename_value f <$> <[r := v]> regs = <[r := rename_value f v]> (rename_value f <$> regs).
  Proof. apply fmap_insert. Qed.

  Lemma rename_read_value f z i :
    rename_value f (RegValue z {[i]}) = RegValue z {[f i]}.
  Proof. unfold rename_value. simpl. by rewrite rename_origins_singleton. Qed.

  Local Ltac solve_replay_name :=
    match goal with
    | H : ?E !! ?i = Some (EAgent ?t ?idx ?label) |- replay_id ?E ?t ?base ?i = _ =>
        rewrite (replay_id_lookup E t base i idx label H); lia
    end.

  Local Ltac start_emission :=
    cbv zeta in *;
    eexists; split; [ | first [eapply replay_single | eapply replay_rmw_events];
      try eassumption; try (apply core_next_id_fresh; assumption);
      first [solve_ownership | solve_replay_name] ];
    rewrite ?rename_register_insert, ?rename_read_value,
      ?rename_origins_union, ?rename_origins_singleton, ?rename_origins_empty,
      <-?thread_control_origins_rename;
    repeat match goal with
    | H : ?E !! ?i = Some (EAgent ?t ?idx ?label) |- _ =>
        progress rewrite (replay_id_lookup E t _ i idx label H)
    end;
    try match goal with Hnext : core_next_id _ = (_ + next_agent_index _ _)%nat |- _ =>
      rewrite <-Hnext end;
    econstructor; last constructor.

  Lemma replay_step P src a src' E t base dst :
    core_step P src a src' -> core_allocation_wf src -> core_allocation_wf dst ->
    event_structure_included src'.(core_events) E ->
    replay_state (replay_id E t base.(core_next_id)) E t base src dst ->
    exists dst', core_run P dst (agent_actions t [a]) dst' /\
      replay_state (replay_id E t base.(core_next_id)) E t base src' dst'.
  Proof.
    intros Hstep Hsrc Hdst Hinc Hreplay.
    pose proof (replay_thread _ _ _ _ _ _ Hreplay) as Hthread.
    pose proof (replay_next _ _ _ _ _ _ Hreplay) as Hnext.
    destruct Hstep; simpl in Hinc; remember_emissions;
      unfold agent_actions; rewrite filter_cons, filter_nil; cbn [core_action_agent];
      destruct (decide (agent = t)) as [-> | Hother].
    all: try (exists dst; split; [constructor |
      first [eapply replay_update_other | eapply replay_single_other | eapply replay_rmw_other];
        eauto using core_next_id_fresh; solve_ownership]).
    all: try (rewrite H in Hthread; simpl in Hthread).
    all: try (match goal with |- exists _, core_run _ _ [CoreSilent _] _ /\ _ =>
      eexists; split; last (apply replay_update; exact Hreplay) end).
    all: try (econstructor; [eapply StepSequence; [exact Hthread | exact H0] | constructor]).
    - econstructor; last constructor.
      eapply StepSkipSequence with
        (thread := rename_thread (replay_id E t (core_next_id base)) thread);
        [exact Hthread | exact H0 |].
      simpl. by rewrite H1.
    - econstructor; last constructor.
      eapply StepSkipControl with
        (thread := rename_thread (replay_id E t (core_next_id base)) thread);
        [exact Hthread | exact H0 |].
      simpl. by rewrite H1.
    - unfold rename_thread. simpl. rewrite rename_register_insert.
      econstructor; last constructor.
      eapply StepAssign with
        (thread := rename_thread (replay_id E t (core_next_id base)) thread);
        [exact Hthread | exact H0 |].
      simpl. by rewrite eval_expr_rename, H1.
    - econstructor; last constructor.
      eapply StepIfTrue with (thread := rename_thread (replay_id E t (core_next_id base)) thread)
        (result := rename_value (replay_id E t (core_next_id base)) result);
        [exact Hthread | exact H0 | | exact H2].
      simpl. by rewrite eval_expr_rename, H1.
    - econstructor; last constructor.
      eapply StepIfFalse with (thread := rename_thread (replay_id E t (core_next_id base)) thread)
        (result := rename_value (replay_id E t (core_next_id base)) result);
        [exact Hthread | exact H0 | | exact H2].
      simpl. by rewrite eval_expr_rename, H1.
    - start_emission.
      eapply StepLoad with (thread := rename_thread (replay_id E t (core_next_id base)) thread);
        [exact Hthread | exact H0 | | exact H2].
      by apply eval_location_rename.
    - start_emission.
      eapply StepStore with (thread := rename_thread (replay_id E t (core_next_id base)) thread)
        (result := rename_value (replay_id E t (core_next_id base)) result);
        [exact Hthread | exact H0 | | | exact H3].
      + by apply eval_location_rename.
      + simpl. by rewrite eval_expr_rename, H2.
    - start_emission.
      eapply StepXchg with (thread := rename_thread (replay_id E t (core_next_id base)) thread)
        (result := rename_value (replay_id E t (core_next_id base)) result);
        [exact Hthread | exact H0 | | | exact H3].
      + by apply eval_location_rename.
      + simpl. by rewrite eval_expr_rename, H2.
    - start_emission.
      eapply StepCmpxchgSuccess with
        (thread := rename_thread (replay_id E t (core_next_id base)) thread)
        (expected_result := rename_value (replay_id E t (core_next_id base)) expected_result)
        (desired_result := rename_value (replay_id E t (core_next_id base)) desired_result);
        [exact Hthread | exact H0 | | | | exact H4 | exact H5].
      + by apply eval_location_rename.
      + simpl. by rewrite eval_expr_rename, H2.
      + simpl. by rewrite eval_expr_rename, H3.
    - start_emission.
      eapply StepCmpxchgFailure with
        (thread := rename_thread (replay_id E t (core_next_id base)) thread)
        (expected_result := rename_value (replay_id E t (core_next_id base)) expected_result)
        (desired_result := rename_value (replay_id E t (core_next_id base)) desired_result);
        [exact Hthread | exact H0 | | | | exact H4 | exact H5].
      + by apply eval_location_rename.
      + simpl. by rewrite eval_expr_rename, H2.
      + simpl. by rewrite eval_expr_rename, H3.
    - start_emission.
      eapply StepAtomicFetch with
        (thread := rename_thread (replay_id E t (core_next_id base)) thread)
        (argument_result := rename_value (replay_id E t (core_next_id base)) argument_result);
        [exact Hthread | exact H0 | | | exact H3].
      + by apply eval_location_rename.
      + simpl. by rewrite eval_expr_rename, H2.
    - start_emission.
      eapply StepAtomicReturn with
        (thread := rename_thread (replay_id E t (core_next_id base)) thread)
        (argument_result := rename_value (replay_id E t (core_next_id base)) argument_result);
        [exact Hthread | exact H0 | | | exact H3].
      + by apply eval_location_rename.
      + simpl. by rewrite eval_expr_rename, H2.
    - start_emission.
      eapply StepAtomicNoReturn with
        (thread := rename_thread (replay_id E t (core_next_id base)) thread)
        (argument_result := rename_value (replay_id E t (core_next_id base)) argument_result);
        [exact Hthread | exact H0 | | | exact H3].
      + by apply eval_location_rename.
      + simpl. by rewrite eval_expr_rename, H2.
    - start_emission. eapply StepFence; [exact Hthread | exact H0].
    - start_emission. eapply StepRcuReadLock; [exact Hthread | exact H0].
    - start_emission. eapply StepRcuReadUnlock; [exact Hthread | exact H0].
    - start_emission. eapply StepSynchronizeRcu; [exact Hthread | exact H0].
  Qed.

  Lemma core_step_events_included P s a s' :
    core_step P s a s' -> core_allocation_wf s ->
    event_structure_included s.(core_events) s'.(core_events).
  Proof.
    intros Hstep Halloc. destruct Hstep;
      try (intros i ev Hlookup; exact Hlookup).
    all: match goal with
    | |- event_structure_included _ (core_events (add_single_event ?s ?t ?th ?l ?r ?a ?d ?c)) =>
        exact (proj1 (add_single_event_extends s t th l r a d c Halloc))
    | |- event_structure_included _ (core_events (add_rmw_events ?s ?t ?th ?m ?l ?o ?n ?r ?a ?d ?c)) =>
        exact (proj1 (add_rmw_events_extends s t th m l o n r a d c Halloc))
    end.
  Qed.

  Lemma core_run_events_included P s actions s' :
    core_run P s actions s' -> core_allocation_wf s ->
    event_structure_included s.(core_events) s'.(core_events).
  Proof.
    intros Hrun. induction Hrun; intros Halloc; first (intros i ev Hlookup; exact Hlookup).
    pose proof (core_step_events_included _ _ _ _ H Halloc) as Hstep.
    specialize (IHHrun (core_step_preserves_allocation _ _ _ _ H Halloc)).
    intros i ev Hlookup. apply IHHrun, Hstep, Hlookup.
  Qed.

  Lemma core_step_other_index P src a dst other :
    core_step P src a dst -> core_action_agent a <> other ->
    next_agent_index dst other = next_agent_index src other.
  Proof.
    intros Hstep Hother. destruct Hstep; simpl in Hother; try done;
      unfold next_agent_index; simpl; rewrite lookup_insert_ne by congruence; done.
  Qed.

  Lemma core_run_other_index P src actions dst other :
    core_run P src actions dst ->
    Forall (fun a => core_action_agent a <> other) actions ->
    next_agent_index dst other = next_agent_index src other.
  Proof.
    intros Hrun. induction Hrun; intros Hactions; first done.
    inversion Hactions; subst. rewrite IHHrun by done.
    by eapply core_step_other_index.
  Qed.

  Corollary agent_replay_other_index P src actions dst t other :
    core_run P src (agent_actions t actions) dst -> other <> t ->
    next_agent_index dst other = next_agent_index src other.
  Proof.
    intros Hrun Hother. eapply core_run_other_index; first done.
    apply Forall_forall. intros a Hin.
    apply list_elem_of_filter in Hin as [Hagent _]. congruence.
  Qed.

  Lemma core_run_append P s xs mid ys last :
    core_run P s xs mid -> core_run P mid ys last -> core_run P s (xs ++ ys) last.
  Proof.
    intros Hrun Hrest. induction Hrun; simpl; first done.
    econstructor; [done | by apply IHHrun].
  Qed.

  Lemma replay_run P src actions final E t base dst :
    core_run P src actions final -> core_allocation_wf src -> core_allocation_wf dst ->
    event_structure_included final.(core_events) E ->
    replay_state (replay_id E t base.(core_next_id)) E t base src dst ->
    exists dst', core_run P dst (agent_actions t actions) dst' /\
      replay_state (replay_id E t base.(core_next_id)) E t base final dst'.
  Proof.
    intros Hrun. revert dst. induction Hrun as [src | src mid final a actions Hstep Hrun IH];
      intros dst Hsrc Hdst Hfinal Hreplay.
    - exists dst. split; last done. constructor.
    - pose proof (core_step_preserves_allocation _ _ _ _ Hstep Hsrc) as Hmid.
      assert (event_structure_included (core_events mid) E) as Hinc.
      { pose proof (core_run_events_included _ _ _ _ Hrun Hmid) as Hmono.
        intros i ev Hlookup. apply Hfinal, Hmono, Hlookup. }
      destruct (replay_step _ _ _ _ _ _ _ _ Hstep Hsrc Hdst Hinc Hreplay)
        as (next & Hnext & Hmatch).
      destruct (IH next Hmid (core_run_preserves_allocation _ _ _ _ Hnext Hdst)
        Hfinal Hmatch) as (last & Hrest & Hlast).
      exists last. split; last done.
      change (core_run P dst (agent_actions t ([a] ++ actions)) last).
      unfold agent_actions. rewrite filter_app. by eapply core_run_append.
  Qed.

  Lemma replay_initial_events f t P : replay_events f t (core_initial_events P) = ∅.
  Proof.
    apply set_eq. intros [i ev]. rewrite elem_of_empty.
    unfold replay_events. rewrite elem_of_map. split; last done.
    intros ([old original] & Heq & Hentry). apply elem_of_filter in Hentry as [Howner Hentry].
    apply elem_of_map_to_set_pair in Hentry.
    pose proof (insert_initial_events_shape (initial_entries P) 0 (∅ : event_structure)
      old original) as Hshape.
    assert (forall x e, lookup_event (∅ : event_structure) x = Some e ->
      exists loc val, e = EInitWrite loc val) as Hempty.
    { intros x e Hbad. discriminate Hbad. }
    destruct (Hshape Hempty Hentry) as (loc & val & ->). discriminate.
  Qed.

  Lemma replay_initial P E t base :
    base.(core_threads) !! t = (core_initial_state P).(core_threads) !! t ->
    next_agent_index base t = 0 ->
    replay_state (replay_id E t base.(core_next_id)) E t base (core_initial_state P) base.
  Proof.
    intros Hthread Hindex. constructor; simpl.
    - rewrite Hthread. simpl. rewrite lookup_fmap.
      destruct (program_agents P !! t); simpl; last done.
      unfold rename_thread, initial_thread. simpl. by rewrite rename_registers_empty.
    - done.
    - exact Hindex.
    - change (core_next_id base = (core_next_id base + 0)%nat). lia.
    - rewrite replay_initial_events. by rewrite union_empty_r_L.
    - rewrite replay_edges_empty. by rewrite union_empty_r_L.
    - rewrite replay_edges_empty. by rewrite union_empty_r_L.
    - rewrite replay_edges_empty. by rewrite union_empty_r_L.
    - rewrite replay_edges_empty. by rewrite union_empty_r_L.
  Qed.

  (** Replay just [t]'s actions, including the original observed values and
      silent steps, in any allocation-well-formed context where [t] is still
      initial. Other agents' events may already be present. The final source
      map determines the proof's ID renaming, not an operational read guard. *)
  Theorem core_run_replay_agent P actions final t base :
    core_run P (core_initial_state P) actions final ->
    core_allocation_wf base ->
    base.(core_threads) !! t = (core_initial_state P).(core_threads) !! t ->
    next_agent_index base t = 0 ->
    exists replayed,
      core_run P base (agent_actions t actions) replayed /\
      replay_state (replay_id final.(core_events) t base.(core_next_id))
        final.(core_events) t base final replayed.
  Proof.
    intros Hrun Hbase Hthread Hindex.
    eapply replay_run; [exact Hrun | apply core_initial_allocation_wf | exact Hbase | |].
    - intros i ev Hlookup. exact Hlookup.
    - by apply replay_initial.
  Qed.

  (** Completion is established only for [t]; other agents in the replay
      context need not have finished. *)
  Theorem complete_core_run_replay_agent P actions final t base :
    complete_core_run P actions final ->
    core_allocation_wf base ->
    base.(core_threads) !! t = (core_initial_state P).(core_threads) !! t ->
    next_agent_index base t = 0 ->
    exists replayed,
      core_run P base (agent_actions t actions) replayed /\
      replay_state (replay_id final.(core_events) t base.(core_next_id))
        final.(core_events) t base final replayed /\
      (forall th, replayed.(core_threads) !! t = Some th -> thread_complete th).
  Proof.
    intros [Hrun Hcomplete] Hbase Hthread Hindex.
    destruct (core_run_replay_agent _ _ _ _ _ Hrun Hbase Hthread Hindex)
      as (replayed & Hreplayed & Hmatch).
    exists replayed. split; first done. split; first done.
    intros th Hlookup. rewrite (replay_thread _ _ _ _ _ _ Hmatch) in Hlookup.
    destruct (core_threads final !! t) as [original |] eqn:Horiginal; simpl in Hlookup;
      last discriminate. simplify_eq. apply rename_thread_complete. by eapply Hcomplete.
  Qed.

  Corollary complete_core_run_replay_agent_initial P actions final t :
    complete_core_run P actions final ->
    exists replayed,
      core_run P (core_initial_state P) (agent_actions t actions) replayed /\
      replay_state (replay_id final.(core_events) t (core_next_id (core_initial_state P)))
        final.(core_events) t (core_initial_state P) final replayed /\
      (forall th, replayed.(core_threads) !! t = Some th -> thread_complete th).
  Proof.
    intros Hrun. apply complete_core_run_replay_agent; try done.
    apply core_initial_allocation_wf.
  Qed.

  (** Direct entry point for candidate graphs.  No LKMM-consistency premise
      is needed for Core replay itself; RCU-machine reconstruction is separate. *)
  Corollary program_graph_replay_agent P C t base :
    program_graph P C -> core_allocation_wf base ->
    base.(core_threads) !! t = (core_initial_state P).(core_threads) !! t ->
    next_agent_index base t = 0 ->
    let f := replay_id C.(candidate_events) t base.(core_next_id) in
    exists actions replayed,
      core_run P base (agent_actions t actions) replayed /\
      (forall th, replayed.(core_threads) !! t = Some th -> thread_complete th) /\
      (forall other, other <> t -> replayed.(core_threads) !! other = base.(core_threads) !! other) /\
      event_entries replayed.(core_events) =
        event_entries base.(core_events) ∪ replay_events f t C.(candidate_events) /\
      replayed.(core_rmw) = base.(core_rmw) ∪ replay_edges f C.(candidate_events) t C.(candidate_rmw) /\
      replayed.(core_direct_addr) = base.(core_direct_addr) ∪
        replay_edges f C.(candidate_events) t C.(candidate_direct_addr) /\
      replayed.(core_direct_data) = base.(core_direct_data) ∪
        replay_edges f C.(candidate_events) t C.(candidate_direct_data) /\
      replayed.(core_direct_ctrl) = base.(core_direct_ctrl) ∪
        replay_edges f C.(candidate_events) t C.(candidate_direct_ctrl).
  Proof.
    intros [(actions & final & Hrun & Hev & Hrmw & Haddr & Hdata & Hctrl) Hwf]
      Hbase Hthread Hindex f.
    destruct (complete_core_run_replay_agent _ _ _ _ _ Hrun Hbase Hthread Hindex)
      as (replayed & Hreplayed & Hmatch & Hcomplete).
    destruct Hmatch. rewrite Hev, Hrmw, Haddr, Hdata, Hctrl in *.
    exists actions, replayed. split_and!; done.
  Qed.

End LkmmCoreAgentReplay.
