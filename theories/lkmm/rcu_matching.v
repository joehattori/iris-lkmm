From Stdlib Require Import Arith Lia List.
From stdpp Require Import fin_maps gmap sorting tactics.
From iris_lkmm.lkmm Require Import execution.
Import ListNotations.

(** Executable matching for nested normal-RCU read-side critical sections.

    Linux v6.18 computes [rcu-rscs] by repeatedly pairing adjacent unmatched
    RCU lock/unlock events in program order.  The executable view below scans
    the same finite per-agent order with a stack. *)
Module RcuMatching.
  Export LkmmExecution.

  Record critical_section := CriticalSection {
    cs_lock : event_id;
    cs_unlock : event_id
  }.

  Inductive rcu_token_kind := RcuTokenLock | RcuTokenUnlock.

  Record rcu_token := RcuToken {
    token_id : event_id;
    token_agent : agent_id;
    token_index : event_index;
    token_kind : rcu_token_kind
  }.

  Global Instance rcu_token_kind_eq_dec : EqDecision rcu_token_kind.
  Proof. solve_decision. Defined.

  Global Instance rcu_token_eq_dec : EqDecision rcu_token.
  Proof. solve_decision. Defined.

  Global Instance critical_section_eq_dec : EqDecision critical_section.
  Proof. solve_decision. Defined.

  (** Lexicographic order by agent, local program index, and finally event ID.
      The final component is relevant only on malformed structures with two
      identifiers at one agent-local position. *)
  Definition rcu_token_kind_rank (kind : rcu_token_kind) : nat :=
    match kind with RcuTokenLock => 0 | RcuTokenUnlock => 1 end.

  Definition rcu_token_le (x y : rcu_token) : Prop :=
    token_agent x < token_agent y \/
    (token_agent x = token_agent y /\
      (token_index x < token_index y \/
        (token_index x = token_index y /\
          (token_id x < token_id y \/
            (token_id x = token_id y /\
              rcu_token_kind_rank (token_kind x) <=
                rcu_token_kind_rank (token_kind y)))))).

  Global Instance rcu_token_le_dec x y : Decision (rcu_token_le x y).
  Proof. solve_decision. Defined.

  Global Instance rcu_token_le_total : Total rcu_token_le.
  Proof.
    intros [xid xa xi xk] [yid ya yi yk].
    unfold rcu_token_le. simpl. lia.
  Qed.

  Global Instance rcu_token_le_transitive : Transitive rcu_token_le.
  Proof.
    intros [xid xa xi xk] [yid ya yi yk] [zid za zi zk].
    unfold rcu_token_le. simpl. intros Hxy Hyz. naive_solver lia.
  Qed.

  Global Instance rcu_token_le_antisymmetric : AntiSymm (=) rcu_token_le.
  Proof.
    intros [xid xa xi xk] [yid ya yi yk].
    unfold rcu_token_le. simpl. intros Hxy Hyx.
    assert (xa = ya /\ xi = yi /\ xid = yid) as (-> & -> & ->) by naive_solver lia.
    destruct xk, yk; simpl in *; f_equal; lia.
  Qed.

  Definition rcu_token_of_entry (entry : event_id * event) : option rcu_token :=
    match entry with
    | (eid, EAgent agent index (LBarrier BarrierRcuLock)) =>
        Some (RcuToken eid agent index RcuTokenLock)
    | (eid, EAgent agent index (LBarrier BarrierRcuUnlock)) =>
        Some (RcuToken eid agent index RcuTokenUnlock)
    | _ => None
    end.

  Fixpoint collect_rcu_tokens (entries : list (event_id * event)) : list rcu_token :=
    match entries with
    | [] => []
    | entry :: entries =>
        match rcu_token_of_entry entry with
        | Some token => token :: collect_rcu_tokens entries
        | None => collect_rcu_tokens entries
        end
    end.

  Definition event_of_rcu_token (token : rcu_token) : event :=
    EAgent token.(token_agent) token.(token_index)
      (LBarrier
        match token.(token_kind) with
        | RcuTokenLock => BarrierRcuLock
        | RcuTokenUnlock => BarrierRcuUnlock
        end).

  Lemma rcu_token_of_entry_Some entry token :
    rcu_token_of_entry entry = Some token ->
    entry = (token.(token_id), event_of_rcu_token token).
  Proof.
    destruct entry as [eid ev]. destruct ev as [loc val | agent index label];
      try done. destruct label as [kind mode mark loc val | barrier]; try done.
    destruct barrier; try done; intros Htoken; injection Htoken as <-; done.
  Qed.

  Lemma collect_rcu_tokens_spec entries token :
    In token (collect_rcu_tokens entries) ->
    In (token.(token_id), event_of_rcu_token token) entries.
  Proof.
    induction entries as [|entry entries IH]; simpl; first done.
    destruct (rcu_token_of_entry entry) as [head |] eqn:Hentry.
    - intros [-> | Hin].
      + left. by apply rcu_token_of_entry_Some.
      + right. by apply IH.
    - intros Hin. right. by apply IH.
  Qed.

  Lemma collect_rcu_tokens_complete entries entry token :
    In entry entries -> rcu_token_of_entry entry = Some token ->
    In token (collect_rcu_tokens entries).
  Proof.
    induction entries as [|head entries IH]; simpl; first done.
    intros [-> | Hin] Htoken.
    - rewrite Htoken. by left.
    - destruct (rcu_token_of_entry head); simpl; [right |]; by eapply IH.
  Qed.

  Definition rcu_token_trace (E : event_structure) : list rcu_token :=
    merge_sort rcu_token_le (collect_rcu_tokens (map_to_list E)).

  Lemma collect_rcu_tokens_permutation entries1 entries2 :
    entries1 ≡ₚ entries2 ->
    collect_rcu_tokens entries1 ≡ₚ collect_rcu_tokens entries2.
  Proof.
    intros Hperm. induction Hperm; simpl.
    - constructor.
    - destruct (rcu_token_of_entry x); simpl; [constructor; done | done].
    - destruct (rcu_token_of_entry x), (rcu_token_of_entry y); simpl;
        apply Permutation_refl || apply perm_swap.
    - by etrans.
  Qed.

  Lemma rcu_token_trace_sorted E :
    StronglySorted rcu_token_le (rcu_token_trace E).
  Proof. apply StronglySorted_merge_sort; typeclasses eauto. Qed.

  Lemma rcu_token_trace_permutation E :
    rcu_token_trace E ≡ₚ collect_rcu_tokens (map_to_list E).
  Proof. apply merge_sort_Permutation. Qed.

  Definition rcu_agent_token_trace (E : event_structure) (agent : agent_id) : list rcu_token :=
    merge_sort rcu_token_le
      (filter (fun token => token.(token_agent) = agent)
        (collect_rcu_tokens (map_to_list E))).

  Lemma rcu_agent_token_trace_sorted E agent :
    StronglySorted rcu_token_le (rcu_agent_token_trace E agent).
  Proof. apply StronglySorted_merge_sort; typeclasses eauto. Qed.

  Lemma rcu_agent_token_trace_permutation E agent :
    rcu_agent_token_trace E agent ≡ₚ
      filter (fun token => token.(token_agent) = agent)
        (collect_rcu_tokens (map_to_list E)).
  Proof. apply merge_sort_Permutation. Qed.

  Lemma rcu_agent_token_trace_lookup E agent token :
    In token (rcu_agent_token_trace E agent) ->
    token.(token_agent) = agent /\
    lookup_event E token.(token_id) = Some (event_of_rcu_token token).
  Proof.
    intros Hin. rewrite <- list_elem_of_In in Hin.
    rewrite rcu_agent_token_trace_permutation in Hin.
    apply list_elem_of_filter in Hin as [Hagent Hin].
    rewrite list_elem_of_In in Hin. split; first done.
    unfold lookup_event. apply elem_of_map_to_list.
    rewrite list_elem_of_In.
    by apply collect_rcu_tokens_spec.
  Qed.

  Lemma rcu_agent_token_trace_of_lookup E eid agent index kind :
    lookup_event E eid = Some (EAgent agent index (LBarrier kind)) ->
    kind = BarrierRcuLock \/ kind = BarrierRcuUnlock ->
    exists token,
      In token (rcu_agent_token_trace E agent) /\ token.(token_id) = eid /\
      token.(token_kind) =
        match kind with
        | BarrierRcuLock => RcuTokenLock
        | _ => RcuTokenUnlock
        end.
  Proof.
    intros Hlookup [-> | ->].
    - exists (RcuToken eid agent index RcuTokenLock). split_and!; try done.
      rewrite <- list_elem_of_In, rcu_agent_token_trace_permutation.
      apply list_elem_of_filter. split; first done.
      rewrite list_elem_of_In.
      eapply collect_rcu_tokens_complete with
        (entry := (eid, EAgent agent index (LBarrier BarrierRcuLock)));
        last reflexivity.
      rewrite <- list_elem_of_In. apply elem_of_map_to_list. exact Hlookup.
    - exists (RcuToken eid agent index RcuTokenUnlock). split_and!; try done.
      rewrite <- list_elem_of_In, rcu_agent_token_trace_permutation.
      apply list_elem_of_filter. split; first done.
      rewrite list_elem_of_In.
      eapply collect_rcu_tokens_complete with
        (entry := (eid, EAgent agent index (LBarrier BarrierRcuUnlock)));
        last reflexivity.
      rewrite <- list_elem_of_In. apply elem_of_map_to_list. exact Hlookup.
  Qed.

  Definition rcu_trace_tail (E : event_structure) (eid : event_id) (ev : event) : Prop :=
    lookup_event E eid = None /\
    match rcu_token_of_entry (eid, ev) with
    | Some token => Forall (fun old => rcu_token_le old token) (rcu_token_trace E)
    | None => True
    end.

  Definition rcu_agent_tail (E : event_structure) (eid : event_id) (ev : event) : Prop :=
    lookup_event E eid = None /\
    match rcu_token_of_entry (eid, ev) with
    | Some token =>
        Forall (fun old => rcu_token_le old token)
          (rcu_agent_token_trace E token.(token_agent))
    | None => True
    end.

  Lemma collect_rcu_tokens_insert E eid ev :
    lookup_event E eid = None ->
    collect_rcu_tokens (map_to_list (<[eid := ev]> E)) ≡ₚ
      match rcu_token_of_entry (eid, ev) with
      | Some token => token :: collect_rcu_tokens (map_to_list E)
      | None => collect_rcu_tokens (map_to_list E)
      end.
  Proof.
    intros Hfresh.
    pose proof (map_to_list_insert E eid ev Hfresh) as Hentries.
    pose proof (collect_rcu_tokens_permutation _ _ Hentries) as Htokens.
    simpl in Htokens. done.
  Qed.

  Lemma rcu_token_trace_insert_non_rcu E eid ev :
    lookup_event E eid = None ->
    rcu_token_of_entry (eid, ev) = None ->
    rcu_token_trace (<[eid := ev]> E) = rcu_token_trace E.
  Proof.
    intros Hfresh Hnone.
    apply (StronglySorted_unique rcu_token_le).
    - apply rcu_token_trace_sorted.
    - apply rcu_token_trace_sorted.
    - etrans; first apply rcu_token_trace_permutation.
      rewrite (collect_rcu_tokens_insert E eid ev Hfresh), Hnone.
      symmetry. apply rcu_token_trace_permutation.
  Qed.

  Lemma rcu_token_trace_insert_tail E eid ev token :
    rcu_trace_tail E eid ev ->
    rcu_token_of_entry (eid, ev) = Some token ->
    rcu_token_trace (<[eid := ev]> E) = rcu_token_trace E ++ [token].
  Proof.
    intros [Hfresh Htail] Htoken. rewrite Htoken in Htail.
    apply (StronglySorted_unique rcu_token_le).
    - apply rcu_token_trace_sorted.
    - apply StronglySorted_app_2.
      + intros old last Hold Hlast.
        apply list_elem_of_singleton in Hlast. subst last.
        apply list_elem_of_In in Hold. rewrite Forall_forall in Htail. by apply Htail.
      + apply rcu_token_trace_sorted.
      + repeat constructor.
    - etrans; first apply rcu_token_trace_permutation.
      rewrite (collect_rcu_tokens_insert E eid ev Hfresh), Htoken.
      etrans; first apply Permutation_cons_append.
      apply Permutation_app_tail. symmetry. apply rcu_token_trace_permutation.
  Qed.

  Lemma rcu_agent_token_trace_insert_other E eid ev token agent :
    lookup_event E eid = None ->
    rcu_token_of_entry (eid, ev) = Some token ->
    token.(token_agent) <> agent ->
    rcu_agent_token_trace (<[eid := ev]> E) agent = rcu_agent_token_trace E agent.
  Proof.
    intros Hfresh Htoken Hneq.
    apply (StronglySorted_unique rcu_token_le).
    - apply rcu_agent_token_trace_sorted.
    - apply rcu_agent_token_trace_sorted.
    - etrans; first apply rcu_agent_token_trace_permutation.
      rewrite (collect_rcu_tokens_insert E eid ev Hfresh), Htoken.
      rewrite filter_cons_False by done.
      symmetry. apply rcu_agent_token_trace_permutation.
  Qed.

  Lemma rcu_agent_token_trace_insert_non_rcu E eid ev agent :
    lookup_event E eid = None ->
    rcu_token_of_entry (eid, ev) = None ->
    rcu_agent_token_trace (<[eid := ev]> E) agent = rcu_agent_token_trace E agent.
  Proof.
    intros Hfresh Hnone.
    apply (StronglySorted_unique rcu_token_le).
    - apply rcu_agent_token_trace_sorted.
    - apply rcu_agent_token_trace_sorted.
    - etrans; first apply rcu_agent_token_trace_permutation.
      rewrite (collect_rcu_tokens_insert E eid ev Hfresh), Hnone.
      symmetry. apply rcu_agent_token_trace_permutation.
  Qed.

  Lemma rcu_agent_token_trace_insert_tail E eid ev token :
    rcu_agent_tail E eid ev ->
    rcu_token_of_entry (eid, ev) = Some token ->
    rcu_agent_token_trace (<[eid := ev]> E) token.(token_agent) =
      rcu_agent_token_trace E token.(token_agent) ++ [token].
  Proof.
    intros [Hfresh Htail] Htoken. rewrite Htoken in Htail.
    apply (StronglySorted_unique rcu_token_le).
    - apply rcu_agent_token_trace_sorted.
    - apply StronglySorted_app_2.
      + intros old last Hold Hlast. apply list_elem_of_singleton in Hlast. subst last.
        apply list_elem_of_In in Hold. rewrite Forall_forall in Htail. by apply Htail.
      + apply rcu_agent_token_trace_sorted.
      + repeat constructor.
    - etrans; first apply rcu_agent_token_trace_permutation.
      rewrite (collect_rcu_tokens_insert E eid ev Hfresh), Htoken.
      rewrite filter_cons_True by done.
      etrans; first apply Permutation_cons_append.
      apply Permutation_app_tail. symmetry. apply rcu_agent_token_trace_permutation.
  Qed.

  Lemma rcu_trace_tail_agent_tail E eid ev :
    rcu_trace_tail E eid ev -> rcu_agent_tail E eid ev.
  Proof.
    intros [Hfresh Htail]. split; first done.
    destruct (rcu_token_of_entry (eid, ev)) as [token |] eqn:Htoken; last done.
    rewrite Forall_forall in Htail |- *.
    intros old Hold. apply Htail.
    apply list_elem_of_In.
    rewrite rcu_token_trace_permutation.
    rewrite <- list_elem_of_In in Hold.
    rewrite rcu_agent_token_trace_permutation in Hold.
    apply list_elem_of_filter in Hold as [_ Hold]. done.
  Qed.

  Record rcu_match_state := RcuMatchState {
    match_stacks : gmap agent_id (list rcu_token);
    match_sections : list critical_section;
    match_unmatched_unlocks : list event_id
  }.

  Definition token_stack (st : rcu_match_state) (agent : agent_id) : list rcu_token :=
    default [] (st.(match_stacks) !! agent).

  Definition match_token (st : rcu_match_state) (token : rcu_token) : rcu_match_state :=
    match token.(token_kind) with
    | RcuTokenLock =>
        RcuMatchState
          (<[token.(token_agent) := token :: token_stack st token.(token_agent)]>
            st.(match_stacks))
          st.(match_sections) st.(match_unmatched_unlocks)
    | RcuTokenUnlock =>
        match token_stack st token.(token_agent) with
        | [] =>
            RcuMatchState st.(match_stacks) st.(match_sections)
              (token.(token_id) :: st.(match_unmatched_unlocks))
        | lock :: rest =>
            RcuMatchState
              (<[token.(token_agent) := rest]> st.(match_stacks))
              (CriticalSection lock.(token_id) token.(token_id) :: st.(match_sections))
              st.(match_unmatched_unlocks)
        end
    end.

  Fixpoint match_tokens (tokens : list rcu_token) (st : rcu_match_state) : rcu_match_state :=
    match tokens with
    | [] => st
    | token :: tokens => match_tokens tokens (match_token st token)
    end.

  Lemma match_tokens_app tokens1 tokens2 st :
    match_tokens (tokens1 ++ tokens2) st =
      match_tokens tokens2 (match_tokens tokens1 st).
  Proof. induction tokens1 in st |- *; simpl; first done. by rewrite IHtokens1. Qed.

  Definition empty_match_state : rcu_match_state := RcuMatchState ∅ [] [].

  Definition stacked_tokens (stacks : gmap agent_id (list rcu_token)) : list rcu_token :=
    concat (snd <$> map_to_list stacks).

  Record rcu_match_result := RcuMatchResult {
    matched_sections : list critical_section;
    unmatched_locks : list event_id;
    unmatched_unlocks : list event_id
  }.

  Definition result_of_state (st : rcu_match_state) : rcu_match_result :=
    RcuMatchResult st.(match_sections)
      (token_id <$> stacked_tokens st.(match_stacks))
      st.(match_unmatched_unlocks).

  Definition compute_agent_match_state (E : event_structure) (agent : agent_id) : rcu_match_state :=
    match_tokens (rcu_agent_token_trace E agent) empty_match_state.

  Definition compute_agent_matching (E : event_structure) (agent : agent_id) : rcu_match_result :=
    result_of_state (compute_agent_match_state E agent).

  Definition computed_agent_stack (E : event_structure) (agent : agent_id) : list event_id :=
    token_id <$> token_stack (compute_agent_match_state E agent) agent.

  Definition rcu_agents (E : event_structure) : list agent_id :=
    nodup Nat.eq_dec (token_agent <$> rcu_token_trace E).

  Fixpoint combine_agent_matchings
      (E : event_structure) (agents : list agent_id) : rcu_match_result :=
    match agents with
    | [] => RcuMatchResult [] [] []
    | agent :: agents =>
        let current := compute_agent_matching E agent in
        let rest := combine_agent_matchings E agents in
        RcuMatchResult
          (current.(matched_sections) ++ rest.(matched_sections))
          (current.(unmatched_locks) ++ rest.(unmatched_locks))
          (current.(unmatched_unlocks) ++ rest.(unmatched_unlocks))
    end.

  Definition compute_rcu_matching (E : event_structure) : rcu_match_result :=
    combine_agent_matchings E (rcu_agents E).

  Lemma combine_agent_matchings_sections E agents agent section :
    In agent agents ->
    In section (compute_agent_matching E agent).(matched_sections) ->
    In section (combine_agent_matchings E agents).(matched_sections).
  Proof.
    induction agents as [|head agents IH]; simpl; first done.
    intros [-> | Hin] Hsection.
    - apply in_or_app. by left.
    - apply in_or_app. right. by eapply IH.
  Qed.

  Lemma combine_agent_matchings_sections_inv E agents section :
    In section (combine_agent_matchings E agents).(matched_sections) ->
    exists agent,
      In agent agents /\
      In section (compute_agent_matching E agent).(matched_sections).
  Proof.
    induction agents as [|head agents IH]; simpl; first done.
    intros Hsection. apply in_app_or in Hsection as [Hsection | Hsection].
    - exists head. split; [by left | done].
    - destruct (IH Hsection) as (agent & Hagent & Hsection_agent).
      exists agent. split; [by right | done].
  Qed.

  Lemma combine_agent_matchings_complete E agents :
    (combine_agent_matchings E agents).(unmatched_locks) = [] ->
    (combine_agent_matchings E agents).(unmatched_unlocks) = [] ->
    forall agent, In agent agents ->
      (compute_agent_matching E agent).(unmatched_locks) = [] /\
      (compute_agent_matching E agent).(unmatched_unlocks) = [].
  Proof.
    induction agents as [|head agents IH]; simpl; first done.
    intros Hlocks Hunlocks agent [-> | Hin].
    - apply app_eq_nil in Hlocks as [Hlocks _].
      apply app_eq_nil in Hunlocks as [Hunlocks _]. done.
    - apply app_eq_nil in Hlocks as [_ Hlocks].
      apply app_eq_nil in Hunlocks as [_ Hunlocks]. by eapply IH.
  Qed.

  Lemma combine_agent_matchings_empty E agents :
    (forall agent, In agent agents ->
      (compute_agent_matching E agent).(unmatched_locks) = [] /\
      (compute_agent_matching E agent).(unmatched_unlocks) = []) ->
    (combine_agent_matchings E agents).(unmatched_locks) = [] /\
    (combine_agent_matchings E agents).(unmatched_unlocks) = [].
  Proof.
    induction agents as [|head agents IH]; simpl; first done.
    intros Hempty. assert (In head (head :: agents)) as Hhead by (simpl; auto).
    destruct (Hempty head Hhead) as [Hlocks Hunlocks].
    destruct IH as [Hrest_locks Hrest_unlocks].
    { intros agent Hagent. apply Hempty. by right. }
    by rewrite Hlocks, Hunlocks, Hrest_locks, Hrest_unlocks.
  Qed.

  Lemma rcu_agent_token_trace_in_global E agent token :
    In token (rcu_agent_token_trace E agent) -> In token (rcu_token_trace E).
  Proof.
    intros Hin. rewrite <- list_elem_of_In in Hin |- *.
    rewrite rcu_agent_token_trace_permutation in Hin.
    apply list_elem_of_filter in Hin as [_ Hin].
    rewrite rcu_token_trace_permutation. done.
  Qed.

  Lemma rcu_agent_in_rcu_agents E agent token :
    In token (rcu_agent_token_trace E agent) -> In agent (rcu_agents E).
  Proof.
    intros Hin. pose proof (rcu_agent_token_trace_lookup E agent token Hin)
      as [Hagent _]. unfold rcu_agents. apply nodup_In. apply in_map_iff.
    exists token. split; first by symmetry. by eapply rcu_agent_token_trace_in_global.
  Qed.

  Definition rcu_matching_complete (E : event_structure) : Prop :=
    (compute_rcu_matching E).(unmatched_locks) = [] /\
    (compute_rcu_matching E).(unmatched_unlocks) = [].

  Definition compute_rcu_sections (E : event_structure) : option (list critical_section) :=
    if decide (rcu_matching_complete E)
    then Some (compute_rcu_matching E).(matched_sections)
    else None.

  Definition rcu_rscs (E : event_structure) : relation :=
    fun lock unlock =>
      exists agent,
        In (CriticalSection lock unlock) (compute_agent_matching E agent).(matched_sections).

  Definition rcu_rscsi (E : event_structure) : relation := rel_inverse (rcu_rscs E).

  Definition rcu_section_wf (E : event_structure) (section : critical_section) : Prop :=
    exists agent lock_index unlock_index,
      lookup_event E section.(cs_lock) =
        Some (EAgent agent lock_index (LBarrier BarrierRcuLock)) /\
      lookup_event E section.(cs_unlock) =
        Some (EAgent agent unlock_index (LBarrier BarrierRcuUnlock)) /\
      lock_index < unlock_index.

  Definition rcu_token_valid (E : event_structure) (token : rcu_token) : Prop :=
    lookup_event E token.(token_id) = Some (event_of_rcu_token token).

  Definition match_stacks_wf (E : event_structure) (seen : list rcu_token)
      (st : rcu_match_state) : Prop :=
    forall agent stack,
      st.(match_stacks) !! agent = Some stack ->
      forall token, In token stack ->
        In token seen /\ token.(token_agent) = agent /\
        token.(token_kind) = RcuTokenLock /\ rcu_token_valid E token.

  Definition match_state_wf (E : event_structure) (seen : list rcu_token)
      (st : rcu_match_state) : Prop :=
    match_stacks_wf E seen st /\
    (forall section, In section st.(match_sections) -> rcu_section_wf E section) /\
    (forall section, In section st.(match_sections) ->
      exists lock unlock,
        In lock seen /\ In unlock seen /\
        section.(cs_lock) = lock.(token_id) /\
        section.(cs_unlock) = unlock.(token_id)).

  Lemma token_stack_lookup st agent token :
    In token (token_stack st agent) ->
    exists stack, st.(match_stacks) !! agent = Some stack /\ In token stack.
  Proof.
    unfold token_stack. destruct (match_stacks st !! agent) as [stack |] eqn:Hlookup;
      simpl; first eauto. done.
  Qed.

  Lemma token_stack_in_stacked_tokens st agent token :
    In token (token_stack st agent) -> In token (stacked_tokens st.(match_stacks)).
  Proof.
    intros Hin. destruct (token_stack_lookup st agent token Hin)
      as (stack & Hlookup & Htoken).
    unfold stacked_tokens. apply in_concat.
    exists stack. split; last done. apply in_map_iff.
    exists (agent, stack). split; first done.
    rewrite <- list_elem_of_In. by apply elem_of_map_to_list.
  Qed.

  Lemma stacked_tokens_spec stacks token :
    In token (stacked_tokens stacks) ->
    exists agent stack,
      stacks !! agent = Some stack /\ In token stack.
  Proof.
    intros Hin. unfold stacked_tokens in Hin. apply in_concat in Hin as (stack & Hstack & Hin).
    apply in_map_iff in Hstack as ([agent values] & Hvalues & Hentry). cbn in Hvalues.
    subst values. exists agent, stack. split; last done.
    rewrite <- list_elem_of_In in Hentry. by apply elem_of_map_to_list.
  Qed.

  Lemma rcu_token_le_same_agent_index_lt E lock unlock :
    event_structure_wf E ->
    rcu_token_valid E lock -> rcu_token_valid E unlock ->
    lock.(token_agent) = unlock.(token_agent) ->
    lock.(token_kind) = RcuTokenLock ->
    unlock.(token_kind) = RcuTokenUnlock ->
    rcu_token_le lock unlock ->
    lock.(token_index) < unlock.(token_index).
  Proof.
    destruct lock as [lock_id lock_agent lock_index lock_kind].
    destruct unlock as [unlock_id unlock_agent unlock_index unlock_kind].
    simpl. intros Hwf Hlock Hunlock Hagent Hlock_kind Hunlock_kind Hle.
    subst unlock_agent. unfold rcu_token_le in Hle. simpl in Hle.
    destruct Hle as [Hlt | (_ & [Hlt | (Hindex & _)])]; try lia.
    assert (lock_id = unlock_id) as ->.
    { eapply Hwf; [exact Hlock |]. rewrite Hindex. exact Hunlock. }
    unfold rcu_token_valid, event_of_rcu_token in Hlock, Hunlock.
    simpl in Hlock, Hunlock. rewrite Hlock_kind in Hlock.
    rewrite Hunlock_kind in Hunlock. congruence.
  Qed.

  Lemma rcu_tokens_po E first second :
    event_structure_wf E ->
    rcu_token_valid E first -> rcu_token_valid E second ->
    first.(token_agent) = second.(token_agent) ->
    first.(token_id) <> second.(token_id) ->
    rcu_token_le first second ->
    po E first.(token_id) second.(token_id).
  Proof.
    destruct first as [first_id first_agent first_index first_kind].
    destruct second as [second_id second_agent second_index second_kind].
    cbn. intros HE Hfirst Hsecond Hagent Hid Hle. subst second_agent.
    assert (Hindex : first_index < second_index).
    { unfold rcu_token_le in Hle. cbn in Hle.
      destruct Hle as [Hlt | (_ & [Hlt | (Heq & _)])]; try lia.
      exfalso. apply Hid. eapply HE; [exact Hfirst |]. by rewrite Heq. }
    exists first_agent, first_index, second_index,
      (LBarrier match first_kind with
        | RcuTokenLock => BarrierRcuLock
        | RcuTokenUnlock => BarrierRcuUnlock
        end),
      (LBarrier match second_kind with
        | RcuTokenLock => BarrierRcuLock
        | RcuTokenUnlock => BarrierRcuUnlock
        end).
    unfold rcu_token_valid, event_of_rcu_token in Hfirst, Hsecond. done.
  Qed.

  Lemma strongly_sorted_prefix_le {A} (R : A -> A -> Prop) prefix x suffix :
    StronglySorted R (prefix ++ x :: suffix) ->
    forall old, In old prefix -> R old x.
  Proof.
    induction prefix as [|head prefix IH]; simpl; first done.
    intros Hsorted old [-> | Hold].
    - inversion Hsorted as [|? ? _ Hall]. rewrite Forall_forall in Hall.
      apply Hall. apply in_or_app. right. by left.
    - apply IH; last done. inversion Hsorted. done.
  Qed.

  Lemma match_stacks_wf_token_stack E seen st agent token :
    match_stacks_wf E seen st ->
    In token (token_stack st agent) ->
    In token seen /\ token.(token_agent) = agent /\
      token.(token_kind) = RcuTokenLock /\ rcu_token_valid E token.
  Proof.
    intros Hwf Hin. destruct (token_stack_lookup st agent token Hin)
      as (stack & Hlookup & Htoken). by eapply Hwf.
  Qed.

  Lemma match_token_state_wf E seen st token :
    event_structure_wf E ->
    match_state_wf E seen st ->
    rcu_token_valid E token ->
    (forall old, In old seen -> rcu_token_le old token) ->
    match_state_wf E (seen ++ [token]) (match_token st token).
  Proof.
    intros HE (Hstacks & Hsections & Hprovenance) Htoken Hle. split_and!.
    - intros agent stack Hlookup old Hold.
      unfold match_token in Hlookup. destruct (token_kind token) eqn:Hkind.
      + cbn in Hlookup.
        apply lookup_insert_Some in Hlookup as [[Heq Hstack_eq] | [Hneq Hlookup]].
        * subst agent. subst stack. simpl in Hold. destruct Hold as [-> | Hold].
          -- split_and!; try done. apply in_or_app. by right; left.
          -- destruct (match_stacks_wf_token_stack E seen st
                (token_agent token) old Hstacks Hold) as (Hin & Hagent & Hlock & Hvalid).
             split_and!; try done. apply in_or_app. by left.
        * destruct (Hstacks agent stack Hlookup old Hold)
            as (Hin & Hagent & Hlock & Hvalid).
          split_and!; try done. apply in_or_app. by left.
      + destruct (token_stack st (token_agent token)) as [|lock rest] eqn:Hstack.
        * cbn in Hlookup. destruct (Hstacks agent stack Hlookup old Hold)
            as (Hin & Hagent & Hlock & Hvalid).
          split_and!; try done. apply in_or_app. by left.
        * cbn in Hlookup.
          apply lookup_insert_Some in Hlookup as [[Heq Hstack_eq] | [Hneq Hlookup]].
          -- subst agent. subst stack.
             destruct (match_stacks_wf_token_stack E seen st
                (token_agent token) old Hstacks) as (Hin & Hagent & Hlock & Hvalid).
             { rewrite Hstack. by right. }
             split_and!; try done. apply in_or_app. by left.
          -- destruct (Hstacks agent stack Hlookup old Hold)
               as (Hin & Hagent & Hlock & Hvalid).
             split_and!; try done. apply in_or_app. by left.
    - intros section Hsection. unfold match_token in Hsection.
      destruct (token_kind token) eqn:Hkind; cbn in Hsection;
        first by apply Hsections.
      destruct (token_stack st (token_agent token)) as [|lock rest] eqn:Hstack;
        cbn in Hsection; first by apply Hsections.
      destruct Hsection as [Hnew | Hold]; last by apply Hsections.
      subst section.
      destruct (match_stacks_wf_token_stack E seen st (token_agent token) lock Hstacks)
        as (Hseen & Hagent & Hlock_kind & Hlock).
      { rewrite Hstack. by left. }
      assert (Hindex : token_index lock < token_index token).
      { eapply rcu_token_le_same_agent_index_lt; try done. by apply Hle. }
      exists (token_agent token), (token_index lock), (token_index token).
      unfold rcu_token_valid, event_of_rcu_token in Hlock, Htoken. simpl in Hlock, Htoken.
      rewrite Hagent, Hlock_kind in Hlock. rewrite Hkind in Htoken. done.
    - intros section Hsection. unfold match_token in Hsection.
      destruct (token_kind token) eqn:Hkind; cbn in Hsection.
      + destruct (Hprovenance section Hsection) as
          (lock & unlock & Hlock & Hunlock & Hlock_id & Hunlock_id).
        exists lock, unlock. split_and!; try done;
          apply in_or_app; by left.
      + destruct (token_stack st (token_agent token)) as [|lock rest] eqn:Hstack;
          cbn in Hsection.
        * destruct (Hprovenance section Hsection) as
            (old_lock & old_unlock & Hlock & Hunlock & Hlock_id & Hunlock_id).
          exists old_lock, old_unlock. split_and!; try done;
            apply in_or_app; by left.
        * destruct Hsection as [Hnew | Hold].
          -- subst section. exists lock, token. split_and!; try reflexivity.
             ++ apply in_or_app. left.
                destruct (match_stacks_wf_token_stack E seen st
                  (token_agent token) lock Hstacks) as [Hin _]; first by rewrite Hstack; left.
                done.
             ++ apply in_or_app. by right; left.
          -- destruct (Hprovenance section Hold) as
               (old_lock & old_unlock & Hlock & Hunlock & Hlock_id & Hunlock_id).
             exists old_lock, old_unlock. split_and!; try done;
               apply in_or_app; by left.
  Qed.

  Lemma match_tokens_state_wf E seen tokens st :
    event_structure_wf E ->
    StronglySorted rcu_token_le (seen ++ tokens) ->
    (forall token, In token (seen ++ tokens) -> rcu_token_valid E token) ->
    match_state_wf E seen st ->
    match_state_wf E (seen ++ tokens) (match_tokens tokens st).
  Proof.
    induction tokens as [|token tokens IH] in seen, st |- *.
    - simpl. intros. by rewrite app_nil_r.
    - intros HE Hsorted Hvalid Hstate. simpl.
      assert (Htoken : rcu_token_valid E token).
      { apply Hvalid. apply in_or_app. right. by left. }
      assert (Hle : forall old, In old seen -> rcu_token_le old token).
      { by eapply strongly_sorted_prefix_le. }
      pose proof (match_token_state_wf E seen st token HE Hstate Htoken Hle) as Hnext.
      replace (seen ++ token :: tokens) with ((seen ++ [token]) ++ tokens)
        in Hsorted, Hvalid |- * by (rewrite <- app_assoc; done).
      by eapply IH.
  Qed.

  Lemma empty_match_state_wf E : match_state_wf E [] empty_match_state.
  Proof.
    split_and!.
    - intros agent stack Hlookup. unfold empty_match_state in Hlookup. simpl in Hlookup.
      change ((∅ : gmap agent_id (list rcu_token)) !! agent = Some stack) in Hlookup.
      change (None = Some stack) in Hlookup. discriminate.
    - intros section Hsection. inversion Hsection.
    - intros section Hsection. inversion Hsection.
  Qed.

  Lemma compute_agent_match_state_wf E agent :
    event_structure_wf E ->
    match_state_wf E (rcu_agent_token_trace E agent)
      (compute_agent_match_state E agent).
  Proof.
    intros HE.
    assert (Hvalid : forall token,
        In token ([] ++ rcu_agent_token_trace E agent) -> rcu_token_valid E token).
    { intros token Hin. apply rcu_agent_token_trace_lookup in Hin as [_ Hlookup]. done. }
    pose proof (match_tokens_state_wf E [] (rcu_agent_token_trace E agent)
      empty_match_state HE (rcu_agent_token_trace_sorted E agent) Hvalid
      (empty_match_state_wf E)) as Hstate.
    unfold compute_agent_match_state. by rewrite app_nil_l in Hstate.
  Qed.

  Lemma compute_agent_matching_sections_wf E agent section :
    event_structure_wf E ->
    In section (compute_agent_matching E agent).(matched_sections) ->
    rcu_section_wf E section.
  Proof.
    intros HE Hsection.
    assert (Hvalid : forall token,
        In token ([] ++ rcu_agent_token_trace E agent) -> rcu_token_valid E token).
    { intros token Hin. apply rcu_agent_token_trace_lookup in Hin as [_ Hlookup]. done. }
    pose proof (match_tokens_state_wf E [] (rcu_agent_token_trace E agent)
      empty_match_state HE (rcu_agent_token_trace_sorted E agent) Hvalid
      (empty_match_state_wf E)) as (_ & Hsections & _).
    unfold compute_agent_matching, compute_agent_match_state, result_of_state in Hsection.
    by apply Hsections.
  Qed.

  Lemma compute_agent_matching_section_provenance E agent section :
    event_structure_wf E ->
    In section (compute_agent_matching E agent).(matched_sections) ->
    exists lock unlock,
      In lock (rcu_agent_token_trace E agent) /\
      In unlock (rcu_agent_token_trace E agent) /\
      section.(cs_lock) = lock.(token_id) /\
      section.(cs_unlock) = unlock.(token_id).
  Proof.
    intros HE Hsection.
    assert (Hvalid : forall token,
        In token ([] ++ rcu_agent_token_trace E agent) -> rcu_token_valid E token).
    { intros token Hin. apply rcu_agent_token_trace_lookup in Hin as [_ Hlookup]. done. }
    pose proof (match_tokens_state_wf E [] (rcu_agent_token_trace E agent)
      empty_match_state HE (rcu_agent_token_trace_sorted E agent) Hvalid
      (empty_match_state_wf E)) as (_ & _ & Hprovenance).
    unfold compute_agent_matching, compute_agent_match_state, result_of_state in Hsection.
    destruct (Hprovenance section Hsection) as
      (lock & unlock & Hlock & Hunlock & Hlock_id & Hunlock_id).
    exists lock, unlock. done.
  Qed.

  Lemma compute_agent_matching_section_agent E agent section :
    event_structure_wf E ->
    In section (compute_agent_matching E agent).(matched_sections) ->
    exists lock_index unlock_index,
      lookup_event E section.(cs_lock) =
        Some (EAgent agent lock_index (LBarrier BarrierRcuLock)) /\
      lookup_event E section.(cs_unlock) =
        Some (EAgent agent unlock_index (LBarrier BarrierRcuUnlock)).
  Proof.
    intros HE Hsection.
    destruct (compute_agent_matching_sections_wf E agent section HE Hsection)
      as (section_agent & lock_index & unlock_index & Hlock & Hunlock & Hindex).
    destruct (compute_agent_matching_section_provenance E agent section HE Hsection)
      as (lock & unlock & Hlock_in & Hunlock_in & Hlock_id & Hunlock_id).
    apply rcu_agent_token_trace_lookup in Hlock_in as [Hlock_agent Hlock_lookup].
    apply rcu_agent_token_trace_lookup in Hunlock_in as [Hunlock_agent Hunlock_lookup].
    rewrite <- Hlock_id in Hlock_lookup. rewrite <- Hunlock_id in Hunlock_lookup.
    assert (section_agent = agent) as ->.
    { unfold event_of_rcu_token in Hlock_lookup.
      destruct (token_kind lock); simpl in Hlock_lookup; congruence. }
    by exists lock_index, unlock_index.
  Qed.

  Lemma rcu_rscs_compute_rcu_matching E lock unlock :
    event_structure_wf E ->
    (rcu_rscs E lock unlock <->
      In (CriticalSection lock unlock)
        (compute_rcu_matching E).(matched_sections)).
  Proof.
    intros HE. split.
    - intros (agent & Hsection).
      destruct (compute_agent_matching_section_provenance E agent
        (CriticalSection lock unlock) HE Hsection) as
        (lock_token & unlock_token & Hlock & Hunlock & _).
      pose proof (rcu_agent_in_rcu_agents E agent lock_token Hlock) as Hagent.
      unfold compute_rcu_matching. by eapply combine_agent_matchings_sections.
    - unfold compute_rcu_matching. intros Hsection.
      destruct (combine_agent_matchings_sections_inv E (rcu_agents E)
        (CriticalSection lock unlock) Hsection) as (agent & _ & Hsection_agent).
      by exists agent.
  Qed.

  Lemma NoDup_fmap_key_injective {A B} (f : A -> B) xs x y :
    NoDup (f <$> xs) -> In x xs -> In y xs -> f x = f y -> x = y.
  Proof.
    induction xs as [|head xs IH]; first done.
    intros Hnodup Hx Hy Hkey.
    pose proof (NoDup_cons_1_1 _ _ Hnodup) as Hfresh.
    pose proof (NoDup_cons_1_2 _ _ Hnodup) as Htail.
    destruct Hx as [Hx | Hx], Hy as [Hy | Hy]; subst; try done.
    - exfalso. apply Hfresh. rewrite list_elem_of_In. apply in_map_iff.
      exists y. split; [symmetry; done | done].
    - exfalso. apply Hfresh. rewrite list_elem_of_In. apply in_map_iff.
      exists x. split; [done | done].
    - by eapply IH.
  Qed.

  Theorem rcu_rscs_edge_wf E lock unlock :
    event_structure_wf E -> rcu_rscs E lock unlock ->
    rcu_section_wf E (CriticalSection lock unlock).
  Proof.
    intros HE (agent & Hsection). by eapply compute_agent_matching_sections_wf.
  Qed.

  Corollary rcu_rscs_endpoints E lock unlock :
    event_structure_wf E -> rcu_rscs E lock unlock ->
    in_event_structure E lock /\ in_event_structure E unlock.
  Proof.
    intros HE Hsection.
    destruct (rcu_rscs_edge_wf E lock unlock HE Hsection)
      as (agent & lock_index & unlock_index & Hlock & Hunlock & Hindex).
    split; eapply lookup_event_in; eauto.
  Qed.

  Corollary rcu_rscs_tags_agent_po E lock unlock :
    event_structure_wf E -> rcu_rscs E lock unlock ->
    event_has_barrier_kind E BarrierRcuLock lock /\
    event_has_barrier_kind E BarrierRcuUnlock unlock /\
    same_agent E lock unlock /\ po E lock unlock.
  Proof.
    intros HE Hsection.
    destruct (rcu_rscs_edge_wf E lock unlock HE Hsection)
      as (agent & lock_index & unlock_index & Hlock & Hunlock & Hindex).
    assert (Hpo : po E lock unlock).
    { exists agent, lock_index, unlock_index,
        (LBarrier BarrierRcuLock), (LBarrier BarrierRcuUnlock). done. }
    split_and!.
    - apply event_has_barrier_kind_lookup. eauto.
    - apply event_has_barrier_kind_lookup. eauto.
    - by apply po_same_agent.
    - done.
  Qed.

  Definition agent_lock_ids (st : rcu_match_state) (agent : agent_id) : list event_id :=
    (cs_lock <$> st.(match_sections)) ++ (token_id <$> token_stack st agent).

  Definition agent_unlock_ids (st : rcu_match_state) : list event_id :=
    (cs_unlock <$> st.(match_sections)) ++ st.(match_unmatched_unlocks).

  Definition agent_state_unique (seen : list rcu_token)
      (agent : agent_id) (st : rcu_match_state) : Prop :=
    NoDup (agent_lock_ids st agent) /\
    NoDup (agent_unlock_ids st) /\
    (forall eid, In eid (agent_lock_ids st agent) -> In eid (token_id <$> seen)) /\
    (forall eid, In eid (agent_unlock_ids st) -> In eid (token_id <$> seen)).

  Lemma NoDup_insert_middle {A} (prefix suffix : list A) x :
    NoDup (prefix ++ suffix) -> ~ In x (prefix ++ suffix) ->
    NoDup (prefix ++ x :: suffix).
  Proof.
    intros Hnodup Hfresh. apply NoDup_ListNoDup in Hnodup.
    apply NoDup_ListNoDup.
    eapply Permutation_NoDup.
    - apply Permutation_middle.
    - by constructor.
  Qed.

  Lemma match_token_agent_state_unique seen agent st token :
    token.(token_agent) = agent ->
    ~ In token.(token_id) (token_id <$> seen) ->
    agent_state_unique seen agent st ->
    agent_state_unique (seen ++ [token]) agent (match_token st token).
  Proof.
    intros Hagent Hfresh (Hlocks & Hunlocks & Hlocks_in & Hunlocks_in).
    unfold agent_state_unique, agent_lock_ids, agent_unlock_ids in *.
    assert (Hseen_mono : forall eid,
        In eid (token_id <$> seen) -> In eid (token_id <$> (seen ++ [token]))).
    { intros eid Hin. rewrite map_app. apply in_or_app. by left. }
    destruct (token_kind token) eqn:Hkind.
    - unfold match_token. rewrite Hkind. cbn. unfold token_stack. cbn.
      rewrite Hagent, lookup_insert_eq.
      split_and!.
      + apply NoDup_insert_middle; first done. intros Hin. apply Hfresh.
        by apply Hlocks_in.
      + done.
      + intros eid Hin. apply in_app_or in Hin as [Hin | Hin].
        * apply Hseen_mono, Hlocks_in. apply in_or_app. by left.
        * simpl in Hin. destruct Hin as [Heq | Hin].
          subst eid.
          -- rewrite map_app. apply in_or_app. by right; left.
          -- apply Hseen_mono, Hlocks_in. apply in_or_app. by right.
      + intros eid Hin. apply Hseen_mono. by apply Hunlocks_in.
    - unfold match_token. rewrite Hkind.
      destruct (token_stack st (token_agent token)) as [|lock rest] eqn:Hstack.
      + cbn. unfold token_stack. cbn. fold (token_stack st agent). split_and!; try done.
        * apply NoDup_insert_middle; first done. intros Hin. apply Hfresh.
          by apply Hunlocks_in.
        * intros eid Hin. apply Hseen_mono. by apply Hlocks_in.
        * intros eid Hin.
          apply in_app_or in Hin as [Hin | [Heq | Hin]].
          -- apply Hseen_mono, Hunlocks_in. apply in_or_app. by left.
          -- subst eid. rewrite map_app. apply in_or_app. by right; left.
          -- apply Hseen_mono, Hunlocks_in. apply in_or_app. by right.
      + cbn. unfold token_stack. cbn. rewrite Hagent, lookup_insert_eq.
        rewrite <- Hagent in Hlocks, Hlocks_in.
        assert (Hlocks_shape :
          NoDup ((cs_lock <$> match_sections st) ++ token_id lock :: (token_id <$> rest))).
        { rewrite Hstack in Hlocks. done. }
        split_and!.
        * apply NoDup_ListNoDup in Hlocks_shape. apply NoDup_ListNoDup.
          eapply Permutation_NoDup; last exact Hlocks_shape.
          symmetry. apply Permutation_middle.
        * constructor.
          -- intros Hin. rewrite list_elem_of_In in Hin. apply Hfresh.
             by apply Hunlocks_in.
          -- done.
        * intros eid [Heq | Hin].
          -- subst eid. apply Hseen_mono, Hlocks_in. rewrite Hstack.
             apply in_or_app. right. by left.
          -- apply in_app_or in Hin as [Hin | Hin].
             ++ apply Hseen_mono, Hlocks_in. apply in_or_app. by left.
             ++ apply Hseen_mono, Hlocks_in. rewrite Hstack.
                apply in_or_app. right. by right.
        * intros eid [Heq | Hin].
          -- subst eid. rewrite map_app. apply in_or_app. by right; left.
          -- apply Hseen_mono. by apply Hunlocks_in.
  Qed.

  Lemma collect_rcu_token_ids_nodup entries :
    NoDup (fst <$> entries) ->
    NoDup (token_id <$> collect_rcu_tokens entries).
  Proof.
    induction entries as [|entry entries IH]; simpl; first done.
    intros Hnodup. pose proof (NoDup_cons_1_1 _ _ Hnodup) as Hfresh.
    pose proof (NoDup_cons_1_2 _ _ Hnodup) as Hnodup_tail.
    destruct (rcu_token_of_entry entry) as [token |] eqn:Hentry; last by apply IH.
    pose proof (rcu_token_of_entry_Some entry token Hentry) as Hentry_shape.
    subst entry. simpl in Hfresh.
    apply NoDup_cons_2; last by apply IH.
    intros Hin. rewrite list_elem_of_In in Hin.
    apply in_map_iff in Hin as (old & Hid & Hold). apply Hfresh.
    rewrite list_elem_of_In. apply in_map_iff.
    exists (token_id old, event_of_rcu_token old). split; first (simpl; congruence).
    by apply collect_rcu_tokens_spec.
  Qed.

  Lemma filter_rcu_token_ids_nodup tokens agent :
    NoDup (token_id <$> tokens) ->
    NoDup (token_id <$>
      filter (fun token => token.(token_agent) = agent) tokens).
  Proof.
    induction tokens as [|token tokens IH]; simpl; first done.
    intros Hnodup. pose proof (NoDup_cons_1_1 _ _ Hnodup) as Hfresh.
    pose proof (NoDup_cons_1_2 _ _ Hnodup) as Hnodup_tail.
    destruct (decide (token_agent token = agent)) as [Heq | Hneq].
    - rewrite filter_cons_True by done. simpl. apply NoDup_cons_2; last by apply IH.
      intros Hin. apply Hfresh. rewrite list_elem_of_In in Hin |- *.
      apply in_map_iff in Hin as (old & <- & Hold).
      apply in_map_iff. exists old. split; first done.
      rewrite <- list_elem_of_In in Hold.
      apply list_elem_of_filter in Hold as [_ Hold]. by rewrite list_elem_of_In in Hold.
    - rewrite filter_cons_False by done. by apply IH.
  Qed.

  Lemma rcu_agent_token_ids_nodup E agent :
    NoDup (token_id <$> rcu_agent_token_trace E agent).
  Proof.
    pose proof (collect_rcu_token_ids_nodup (map_to_list E)
      (NoDup_fst_map_to_list E)) as Hcollect.
    pose proof (filter_rcu_token_ids_nodup
      (collect_rcu_tokens (map_to_list E)) agent Hcollect) as Hfilter.
    apply NoDup_ListNoDup in Hfilter. apply NoDup_ListNoDup.
    eapply Permutation_NoDup; last exact Hfilter.
    apply Permutation_map. symmetry. apply rcu_agent_token_trace_permutation.
  Qed.

  Lemma match_tokens_agent_state_unique seen tokens agent st :
    (forall token, In token (seen ++ tokens) -> token.(token_agent) = agent) ->
    NoDup (token_id <$> (seen ++ tokens)) ->
    agent_state_unique seen agent st ->
    agent_state_unique (seen ++ tokens) agent (match_tokens tokens st).
  Proof.
    induction tokens as [|token tokens IH] in seen, st |- *.
    - simpl. intros. by rewrite app_nil_r.
    - intros Hagents Hnodup Hstate. simpl.
      assert (Hagent : token_agent token = agent).
      { apply Hagents. apply in_or_app. right. by left. }
      assert (Hfresh : ~ In (token_id token) (token_id <$> seen)).
      { rewrite map_app in Hnodup.
        apply (proj1 (stdpp.list_relations.list.NoDup_app _ _)) in Hnodup
          as (_ & Hdisjoint & _).
        intros Hin. apply (Hdisjoint (token_id token)); first by rewrite list_elem_of_In.
        rewrite list_elem_of_In. simpl. by left. }
      pose proof (match_token_agent_state_unique seen agent st token
        Hagent Hfresh Hstate) as Hnext.
      replace (seen ++ token :: tokens) with ((seen ++ [token]) ++ tokens)
        in Hagents, Hnodup |- * by (rewrite <- app_assoc; done).
      by eapply IH.
  Qed.

  Lemma empty_agent_state_unique agent :
    agent_state_unique [] agent empty_match_state.
  Proof.
    unfold agent_state_unique, agent_lock_ids, agent_unlock_ids,
      empty_match_state, token_stack. cbn.
    change (default [] ((∅ : gmap agent_id (list rcu_token)) !! agent)) with
      ([] : list rcu_token). split_and!; try constructor; done.
  Qed.

  Lemma compute_agent_match_state_unique E agent :
    agent_state_unique (rcu_agent_token_trace E agent) agent
      (compute_agent_match_state E agent).
  Proof.
    assert (Hagents : forall token,
        In token ([] ++ rcu_agent_token_trace E agent) -> token_agent token = agent).
    { intros token Hin. by apply rcu_agent_token_trace_lookup in Hin as [Hagent _]. }
    pose proof (match_tokens_agent_state_unique [] (rcu_agent_token_trace E agent)
      agent empty_match_state Hagents (rcu_agent_token_ids_nodup E agent)
      (empty_agent_state_unique agent)) as Hunique.
    unfold compute_agent_match_state. by rewrite app_nil_l in Hunique.
  Qed.

  Lemma compute_agent_matching_unique E agent :
    NoDup (cs_lock <$> (compute_agent_matching E agent).(matched_sections)) /\
    NoDup (cs_unlock <$> (compute_agent_matching E agent).(matched_sections)).
  Proof.
    assert (Hagents : forall token,
        In token ([] ++ rcu_agent_token_trace E agent) -> token_agent token = agent).
    { intros token Hin. by apply rcu_agent_token_trace_lookup in Hin as [Hagent _]. }
    pose proof (match_tokens_agent_state_unique [] (rcu_agent_token_trace E agent)
      agent empty_match_state Hagents (rcu_agent_token_ids_nodup E agent)
      (empty_agent_state_unique agent)) as (Hlocks & Hunlocks & _).
    unfold compute_agent_matching, compute_agent_match_state, result_of_state,
      agent_lock_ids, agent_unlock_ids in *.
    apply (proj1 (stdpp.list_relations.list.NoDup_app _ _)) in Hlocks as [Hlocks _].
    apply (proj1 (stdpp.list_relations.list.NoDup_app _ _)) in Hunlocks
      as [Hunlocks _]. done.
  Qed.

  Definition agent_state_covers (seen : list rcu_token)
      (agent : agent_id) (st : rcu_match_state) : Prop :=
    forall token, In token seen ->
      match token.(token_kind) with
      | RcuTokenLock => In token.(token_id) (agent_lock_ids st agent)
      | RcuTokenUnlock => In token.(token_id) (agent_unlock_ids st)
      end.

  Lemma agent_lock_ids_match_lock st token agent :
    token.(token_kind) = RcuTokenLock -> token.(token_agent) = agent ->
    agent_lock_ids (match_token st token) agent =
      (cs_lock <$> st.(match_sections)) ++
        token.(token_id) :: (token_id <$> token_stack st agent).
  Proof.
    intros Hkind Hagent. unfold agent_lock_ids, match_token. rewrite Hkind. cbn.
    unfold token_stack. cbn. rewrite <- Hagent, lookup_insert_eq. done.
  Qed.

  Lemma agent_unlock_ids_match_lock st token :
    token.(token_kind) = RcuTokenLock ->
    agent_unlock_ids (match_token st token) = agent_unlock_ids st.
  Proof. intros Hkind. unfold agent_unlock_ids, match_token. by rewrite Hkind. Qed.

  Lemma agent_lock_ids_match_unmatched_unlock st token agent :
    token.(token_kind) = RcuTokenUnlock ->
    token_stack st token.(token_agent) = [] ->
    agent_lock_ids (match_token st token) agent = agent_lock_ids st agent.
  Proof.
    intros Hkind Hstack. unfold agent_lock_ids, match_token. rewrite Hkind, Hstack. done.
  Qed.

  Lemma agent_unlock_ids_match_unmatched_unlock st token :
    token.(token_kind) = RcuTokenUnlock ->
    token_stack st token.(token_agent) = [] ->
    agent_unlock_ids (match_token st token) =
      (cs_unlock <$> st.(match_sections)) ++
        token.(token_id) :: st.(match_unmatched_unlocks).
  Proof.
    intros Hkind Hstack. unfold agent_unlock_ids, match_token.
    rewrite Hkind, Hstack. done.
  Qed.

  Lemma agent_lock_ids_match_unlock st token agent lock rest :
    token.(token_kind) = RcuTokenUnlock -> token.(token_agent) = agent ->
    token_stack st token.(token_agent) = lock :: rest ->
    agent_lock_ids (match_token st token) agent =
      lock.(token_id) :: (cs_lock <$> st.(match_sections)) ++
        (token_id <$> rest).
  Proof.
    intros Hkind Hagent Hstack. unfold agent_lock_ids, match_token.
    rewrite Hkind, Hstack. cbn. unfold token_stack. cbn.
    rewrite <- Hagent, lookup_insert_eq. done.
  Qed.

  Lemma agent_unlock_ids_match_unlock st token lock rest :
    token.(token_kind) = RcuTokenUnlock ->
    token_stack st token.(token_agent) = lock :: rest ->
    agent_unlock_ids (match_token st token) =
      token.(token_id) :: (cs_unlock <$> st.(match_sections)) ++
        st.(match_unmatched_unlocks).
  Proof.
    intros Hkind Hstack. unfold agent_unlock_ids, match_token.
    rewrite Hkind, Hstack. done.
  Qed.

  Lemma match_token_agent_state_covers seen agent st token :
    token.(token_agent) = agent ->
    agent_state_covers seen agent st ->
    agent_state_covers (seen ++ [token]) agent (match_token st token).
  Proof.
    intros Hagent Hcovers old Hold. apply in_app_or in Hold as [Hold | [Heq | []]].
    - specialize (Hcovers old Hold).
      destruct old as [old_id old_agent old_index old_kind]. cbn in Hcovers |- *.
      destruct (token_kind token) eqn:Hkind.
      + rewrite (agent_lock_ids_match_lock st token agent Hkind Hagent),
          (agent_unlock_ids_match_lock st token Hkind).
        destruct old_kind; cbn in Hcovers |- *; last done.
        apply in_app_or in Hcovers as [Hsection | Hstack].
        * apply in_or_app. by left.
        * apply in_or_app. right. by right.
      + destruct (token_stack st (token_agent token)) as [|lock rest] eqn:Hstack.
        * rewrite (agent_lock_ids_match_unmatched_unlock st token agent Hkind Hstack),
            (agent_unlock_ids_match_unmatched_unlock st token Hkind Hstack).
          destruct old_kind; cbn in Hcovers |- *; first done.
          apply in_app_or in Hcovers as [Hsection | Hunmatched].
          -- apply in_or_app. by left.
          -- apply in_or_app. right. by right.
        * rewrite (agent_lock_ids_match_unlock st token agent lock rest
              Hkind Hagent Hstack),
            (agent_unlock_ids_match_unlock st token lock rest Hkind Hstack).
          destruct old_kind; cbn in Hcovers |- *.
          -- unfold agent_lock_ids in Hcovers.
             rewrite <- Hagent, Hstack in Hcovers. cbn in Hcovers.
             apply in_app_or in Hcovers as [Hsection | [<- | Hrest]].
             ++ by right; apply in_or_app; left.
             ++ by left.
             ++ by right; apply in_or_app; right.
          -- unfold agent_unlock_ids in Hcovers.
             apply in_app_or in Hcovers as [Hsection | Hunmatched].
             ++ right. by apply in_or_app; left.
             ++ right. by apply in_or_app; right.
    - subst old. destruct (token_kind token) eqn:Hkind.
      + rewrite (agent_lock_ids_match_lock st token agent Hkind Hagent).
        apply in_or_app. right. by left.
      + destruct (token_stack st (token_agent token)) as [|lock rest] eqn:Hstack.
        * rewrite (agent_unlock_ids_match_unmatched_unlock st token Hkind Hstack).
          apply in_or_app. right. by left.
        * rewrite (agent_unlock_ids_match_unlock st token lock rest Hkind Hstack).
          by left.
  Qed.

  Lemma match_tokens_agent_state_covers seen tokens agent st :
    (forall token, In token (seen ++ tokens) -> token.(token_agent) = agent) ->
    agent_state_covers seen agent st ->
    agent_state_covers (seen ++ tokens) agent (match_tokens tokens st).
  Proof.
    induction tokens as [|token tokens IH] in seen, st |- *.
    - simpl. intros. by rewrite app_nil_r.
    - intros Hagents Hcovers. simpl.
      assert (Hagent : token_agent token = agent).
      { apply Hagents. apply in_or_app. right. by left. }
      pose proof (match_token_agent_state_covers seen agent st token Hagent Hcovers) as Hnext.
      replace (seen ++ token :: tokens) with ((seen ++ [token]) ++ tokens)
        in Hagents |- * by (rewrite <- app_assoc; done).
      by eapply IH.
  Qed.

  Lemma empty_agent_state_covers agent :
    agent_state_covers [] agent empty_match_state.
  Proof. intros token Hfalse. inversion Hfalse. Qed.

  Lemma compute_agent_matching_covers E agent token :
    In token (rcu_agent_token_trace E agent) ->
    match token.(token_kind) with
    | RcuTokenLock =>
        In token.(token_id)
          (agent_lock_ids (compute_agent_match_state E agent) agent)
    | RcuTokenUnlock =>
        In token.(token_id)
          (agent_unlock_ids (compute_agent_match_state E agent))
    end.
  Proof.
    intros Htoken.
    assert (Hagents : forall old,
        In old ([] ++ rcu_agent_token_trace E agent) -> token_agent old = agent).
    { intros old Hold. by apply rcu_agent_token_trace_lookup in Hold as [Hagent _]. }
    pose proof (match_tokens_agent_state_covers [] (rcu_agent_token_trace E agent)
      agent empty_match_state Hagents (empty_agent_state_covers agent)) as Hcovers.
    unfold compute_agent_match_state. by apply Hcovers.
  Qed.

  Definition unmatched_unlocks_provenance
      (seen : list rcu_token) (st : rcu_match_state) : Prop :=
    forall eid, In eid st.(match_unmatched_unlocks) ->
      exists token,
        In token seen /\ token.(token_id) = eid /\
        token.(token_kind) = RcuTokenUnlock.

  Lemma match_token_unmatched_unlocks_provenance seen st token :
    unmatched_unlocks_provenance seen st ->
    unmatched_unlocks_provenance (seen ++ [token]) (match_token st token).
  Proof.
    intros Hprovenance eid Hin. unfold match_token in Hin.
    destruct (token_kind token) eqn:Hkind.
    - destruct (Hprovenance eid Hin) as (old & Hold & Hid & Hold_kind).
      exists old. split_and!; try done. apply in_or_app. by left.
    - destruct (token_stack st (token_agent token)) as [|lock rest] eqn:Hstack.
      + cbn in Hin. destruct Hin as [<- | Hin].
        * exists token. split_and!; try done. apply in_or_app. by right; left.
        * destruct (Hprovenance eid Hin) as (old & Hold & Hid & Hold_kind).
          exists old. split_and!; try done. apply in_or_app. by left.
      + destruct (Hprovenance eid Hin) as (old & Hold & Hid & Hold_kind).
        exists old. split_and!; try done. apply in_or_app. by left.
  Qed.

  Lemma match_tokens_unmatched_unlocks_provenance seen tokens st :
    unmatched_unlocks_provenance seen st ->
    unmatched_unlocks_provenance (seen ++ tokens) (match_tokens tokens st).
  Proof.
    induction tokens as [|token tokens IH] in seen, st |- *; simpl.
    - intros. by rewrite app_nil_r.
    - intros Hprovenance.
      pose proof (match_token_unmatched_unlocks_provenance seen st token Hprovenance)
        as Hnext.
      replace (seen ++ token :: tokens) with ((seen ++ [token]) ++ tokens)
        by (rewrite <- app_assoc; done).
      by apply IH.
  Qed.

  Lemma compute_agent_matching_unmatched_unlock_provenance E agent eid :
    In eid (compute_agent_matching E agent).(unmatched_unlocks) ->
    exists token,
      In token (rcu_agent_token_trace E agent) /\
      token.(token_id) = eid /\ token.(token_kind) = RcuTokenUnlock.
  Proof.
    intros Hin.
    pose proof (match_tokens_unmatched_unlocks_provenance []
      (rcu_agent_token_trace E agent) empty_match_state) as Hprovenance.
    assert (unmatched_unlocks_provenance [] empty_match_state) as Hempty.
    { intros old Hfalse. inversion Hfalse. }
    specialize (Hprovenance Hempty).
    unfold compute_agent_matching, compute_agent_match_state, result_of_state in Hin.
    destruct (Hprovenance eid Hin) as (token & Htoken & Hid & Hkind).
    exists token. rewrite app_nil_l in Htoken. done.
  Qed.

  Lemma compute_agent_matching_locks_empty_of_covered E agent :
    event_structure_wf E ->
    (forall lock,
      event_has_barrier_kind E BarrierRcuLock lock ->
      exists unlock, rcu_rscs E lock unlock) ->
    (compute_agent_matching E agent).(unmatched_locks) = [].
  Proof.
    intros HE Hcovered.
    destruct (compute_agent_matching E agent).(unmatched_locks)
      as [|lock unmatched] eqn:Hunmatched; first done.
    exfalso.
    assert (Hlock : In lock (compute_agent_matching E agent).(unmatched_locks)).
    { rewrite Hunmatched. by left. }
    unfold compute_agent_matching, result_of_state in Hlock. cbn in Hlock.
    apply in_map_iff in Hlock as (token & <- & Htoken_stacked).
    apply stacked_tokens_spec in Htoken_stacked as
      (stack_agent & stack & Hstack & Htoken_stack).
    destruct (compute_agent_match_state_wf E agent HE) as (Hstacks & _).
    destruct (Hstacks stack_agent stack Hstack token Htoken_stack) as
      (Htoken & Htoken_agent & Hkind & Hvalid).
    pose proof (rcu_agent_token_trace_lookup E agent token Htoken) as [Hagent _].
    assert (stack_agent = agent) as -> by congruence.
    assert (Htag : event_has_barrier_kind E BarrierRcuLock (token_id token)).
    { apply event_has_barrier_kind_lookup. exists (event_of_rcu_token token).
      split; first done. unfold event_of_rcu_token. rewrite Hkind. done. }
    destruct (Hcovered (token_id token) Htag) as (unlock & matched_agent & Hsection).
    destruct (compute_agent_matching_section_agent E matched_agent
      (CriticalSection (token_id token) unlock) HE Hsection) as
      (lock_index & unlock_index & Hlookup & _).
    cbn in Hlookup.
    unfold rcu_token_valid, event_of_rcu_token in Hvalid. rewrite Hkind in Hvalid.
    unfold lookup_event in Hvalid.
    assert (matched_agent = token_agent token) as Hmatched_agent by congruence.
    assert (matched_agent = agent) as -> by congruence.
    destruct (compute_agent_match_state_unique E agent) as (Hlocks & _).
    unfold agent_lock_ids in Hlocks.
    apply (proj1 (stdpp.list_relations.list.NoDup_app _ _)) in Hlocks
      as (_ & Hdisjoint & _).
    apply (Hdisjoint (token_id token)).
    - rewrite list_elem_of_In. apply in_map_iff.
      exists (CriticalSection (token_id token) unlock). done.
    - rewrite list_elem_of_In. apply in_map_iff. exists token. split; first done.
      unfold token_stack. rewrite Hstack. done.
  Qed.

  Lemma compute_agent_matching_unlocks_empty_of_covered E agent :
    event_structure_wf E ->
    (forall unlock,
      event_has_barrier_kind E BarrierRcuUnlock unlock ->
      exists lock, rcu_rscs E lock unlock) ->
    (compute_agent_matching E agent).(unmatched_unlocks) = [].
  Proof.
    intros HE Hcovered.
    destruct (compute_agent_matching E agent).(unmatched_unlocks)
      as [|unlock unmatched] eqn:Hunmatched; first done.
    exfalso.
    assert (Hunlock : In unlock (compute_agent_matching E agent).(unmatched_unlocks)).
    { rewrite Hunmatched. by left. }
    destruct (compute_agent_matching_unmatched_unlock_provenance E agent unlock Hunlock)
      as (token & Htoken & <- & Hkind).
    pose proof (rcu_agent_token_trace_lookup E agent token Htoken) as [Hagent Hvalid].
    assert (Htag : event_has_barrier_kind E BarrierRcuUnlock (token_id token)).
    { apply event_has_barrier_kind_lookup. exists (event_of_rcu_token token).
      split; first done. unfold event_of_rcu_token. rewrite Hkind. done. }
    destruct (Hcovered (token_id token) Htag) as (lock & matched_agent & Hsection).
    destruct (compute_agent_matching_section_agent E matched_agent
      (CriticalSection lock (token_id token)) HE Hsection) as
      (lock_index & unlock_index & _ & Hlookup).
    cbn in Hlookup. unfold event_of_rcu_token in Hvalid. rewrite Hkind in Hvalid.
    unfold lookup_event in Hvalid.
    assert (matched_agent = token_agent token) as Hmatched_agent by congruence.
    assert (matched_agent = agent) as -> by congruence.
    destruct (compute_agent_match_state_unique E agent) as (_ & Hunlocks & _).
    unfold agent_unlock_ids in Hunlocks.
    apply (proj1 (stdpp.list_relations.list.NoDup_app _ _)) in Hunlocks
      as (_ & Hdisjoint & _).
    apply (Hdisjoint (token_id token)).
    - rewrite list_elem_of_In. apply in_map_iff.
      exists (CriticalSection lock (token_id token)). done.
    - rewrite list_elem_of_In.
      unfold compute_agent_matching, result_of_state in Hunmatched. cbn in Hunmatched.
      rewrite Hunmatched. by left.
  Qed.

  Theorem rcu_matching_complete_covers_lock E lock :
    rcu_matching_complete E -> event_has_barrier_kind E BarrierRcuLock lock ->
    exists unlock, rcu_rscs E lock unlock.
  Proof.
    intros [Hall_locks Hall_unlocks] Hlock.
    apply event_has_barrier_kind_lookup in Hlock as (ev & Hlookup & Hkind).
    destruct ev as [loc value | agent index label]; first done.
    destruct label as [kind mode mark loc value | barrier]; first done.
    destruct barrier; try done. clear Hkind.
    destruct (rcu_agent_token_trace_of_lookup E lock agent index BarrierRcuLock
      Hlookup (or_introl eq_refl)) as (token & Htoken & Hid & Htoken_kind).
    cbn in Hid, Htoken_kind. subst lock.
    pose proof (rcu_agent_in_rcu_agents E agent token Htoken) as Hagent.
    destruct (combine_agent_matchings_complete E (rcu_agents E)
      Hall_locks Hall_unlocks agent Hagent) as [Hunmatched _].
    pose proof (compute_agent_matching_covers E agent token Htoken) as Hcovers.
    rewrite Htoken_kind in Hcovers. unfold agent_lock_ids in Hcovers.
    apply in_app_or in Hcovers as [Hsection | Hstack].
    - apply in_map_iff in Hsection as (section & Hsection_lock & Hsection).
      exists section.(cs_unlock), agent. destruct section. cbn in Hsection_lock |- *.
      by subst.
    - exfalso. apply in_map_iff in Hstack as (old & Hold_id & Hold).
      unfold compute_agent_matching, result_of_state in Hunmatched. cbn in Hunmatched.
      assert (In (token_id old)
        (token_id <$> stacked_tokens
          (match_stacks (compute_agent_match_state E agent)))) as Hin.
      { apply in_map_iff. exists old. split; first done.
        by eapply token_stack_in_stacked_tokens. }
      rewrite Hunmatched in Hin. done.
  Qed.

  Theorem rcu_matching_complete_covers_unlock E unlock :
    rcu_matching_complete E -> event_has_barrier_kind E BarrierRcuUnlock unlock ->
    exists lock, rcu_rscs E lock unlock.
  Proof.
    intros [Hall_locks Hall_unlocks] Hunlock.
    apply event_has_barrier_kind_lookup in Hunlock as (ev & Hlookup & Hkind).
    destruct ev as [loc value | agent index label]; first done.
    destruct label as [kind mode mark loc value | barrier]; first done.
    destruct barrier; try done. clear Hkind.
    destruct (rcu_agent_token_trace_of_lookup E unlock agent index BarrierRcuUnlock
      Hlookup (or_intror eq_refl)) as (token & Htoken & Hid & Htoken_kind).
    cbn in Hid, Htoken_kind. subst unlock.
    pose proof (rcu_agent_in_rcu_agents E agent token Htoken) as Hagent.
    destruct (combine_agent_matchings_complete E (rcu_agents E)
      Hall_locks Hall_unlocks agent Hagent) as [_ Hunmatched].
    pose proof (compute_agent_matching_covers E agent token Htoken) as Hcovers.
    rewrite Htoken_kind in Hcovers. unfold agent_unlock_ids in Hcovers.
    apply in_app_or in Hcovers as [Hsection | Hunmatched_id].
    - apply in_map_iff in Hsection as (section & Hsection_unlock & Hsection).
      exists section.(cs_lock), agent. destruct section. cbn in Hsection_unlock |- *.
      by subst.
    - unfold compute_agent_matching, result_of_state in Hunmatched. cbn in Hunmatched.
      rewrite Hunmatched in Hunmatched_id. done.
  Qed.

  Theorem rcu_rscs_functional E lock unlock1 unlock2 :
    event_structure_wf E ->
    rcu_rscs E lock unlock1 -> rcu_rscs E lock unlock2 ->
    unlock1 = unlock2.
  Proof.
    intros HE (agent1 & Hsection1) (agent2 & Hsection2).
    destruct (compute_agent_matching_section_agent E agent1
      (CriticalSection lock unlock1) HE Hsection1) as
      (lock_index1 & unlock_index1 & Hlock1 & Hunlock1).
    destruct (compute_agent_matching_section_agent E agent2
      (CriticalSection lock unlock2) HE Hsection2) as
      (lock_index2 & unlock_index2 & Hlock2 & Hunlock2).
    cbn in Hlock1, Hlock2, Hunlock1, Hunlock2.
    assert (agent1 = agent2) as -> by congruence.
    destruct (compute_agent_matching_unique E agent2) as [Hlocks _].
    pose proof (NoDup_fmap_key_injective cs_lock _
      (CriticalSection lock unlock1) (CriticalSection lock unlock2)
      Hlocks Hsection1 Hsection2 eq_refl) as Hsection.
    by injection Hsection.
  Qed.

  Theorem rcu_rscs_injective E lock1 lock2 unlock :
    event_structure_wf E ->
    rcu_rscs E lock1 unlock -> rcu_rscs E lock2 unlock ->
    lock1 = lock2.
  Proof.
    intros HE (agent1 & Hsection1) (agent2 & Hsection2).
    destruct (compute_agent_matching_section_agent E agent1
      (CriticalSection lock1 unlock) HE Hsection1) as
      (lock_index1 & unlock_index1 & Hlock1 & Hunlock1).
    destruct (compute_agent_matching_section_agent E agent2
      (CriticalSection lock2 unlock) HE Hsection2) as
      (lock_index2 & unlock_index2 & Hlock2 & Hunlock2).
    cbn in Hlock1, Hlock2, Hunlock1, Hunlock2.
    assert (agent1 = agent2) as -> by congruence.
    destruct (compute_agent_matching_unique E agent2) as [_ Hunlocks].
    pose proof (NoDup_fmap_key_injective cs_unlock _
      (CriticalSection lock1 unlock) (CriticalSection lock2 unlock)
      Hunlocks Hsection1 Hsection2 eq_refl) as Hsection.
    by injection Hsection.
  Qed.

  Definition rcu_sections_compatible (E : event_structure)
      (first second : critical_section) : Prop :=
    first = second \/
    po E first.(cs_unlock) second.(cs_lock) \/
    po E second.(cs_unlock) first.(cs_lock) \/
    (po E first.(cs_lock) second.(cs_lock) /\
      po E second.(cs_unlock) first.(cs_unlock)) \/
    (po E second.(cs_lock) first.(cs_lock) /\
      po E first.(cs_unlock) second.(cs_unlock)).

  Lemma rcu_sections_compatible_symmetric E first second :
    rcu_sections_compatible E first second ->
    rcu_sections_compatible E second first.
  Proof. unfold rcu_sections_compatible. naive_solver. Qed.

  Definition agent_state_nested (E : event_structure) (seen : list rcu_token)
      (agent : agent_id) (st : rcu_match_state) : Prop :=
    StronglySorted (fun inner outer => rcu_token_le outer inner)
      (token_stack st agent) /\
    (forall first second,
      In first st.(match_sections) -> In second st.(match_sections) ->
      rcu_sections_compatible E first second) /\
    (forall open section,
      In open (token_stack st agent) -> In section st.(match_sections) ->
      po E section.(cs_unlock) open.(token_id) \/
      po E open.(token_id) section.(cs_lock)).

  Lemma matched_section_unlock_before E seen st agent section token :
    event_structure_wf E ->
    match_state_wf E seen st ->
    In section st.(match_sections) ->
    (forall old, In old seen -> old.(token_agent) = agent) ->
    (forall old, In old seen -> rcu_token_valid E old) ->
    token.(token_agent) = agent -> rcu_token_valid E token ->
    ~ In token.(token_id) (token_id <$> seen) ->
    (forall old, In old seen -> rcu_token_le old token) ->
    po E section.(cs_unlock) token.(token_id).
  Proof.
    intros HE (_ & _ & Hprovenance) Hsection Hagents Hvalid Hagent Htoken Hfresh Hle.
    destruct (Hprovenance section Hsection) as
      (lock & unlock & Hlock & Hunlock & Hlock_id & Hunlock_id).
    rewrite Hunlock_id. eapply rcu_tokens_po; try done.
    - by apply Hvalid.
    - by rewrite Hagents, Hagent.
    - intros Heq. apply Hfresh. rewrite <- Heq. apply in_map_iff.
      exists unlock. done.
    - by apply Hle.
  Qed.

  Lemma match_token_agent_state_nested E seen agent st token :
    event_structure_wf E ->
    match_state_wf E seen st ->
    agent_state_unique seen agent st ->
    agent_state_nested E seen agent st ->
    (forall old, In old seen -> old.(token_agent) = agent) ->
    (forall old, In old seen -> rcu_token_valid E old) ->
    token.(token_agent) = agent -> rcu_token_valid E token ->
    ~ In token.(token_id) (token_id <$> seen) ->
    (forall old, In old seen -> rcu_token_le old token) ->
    agent_state_nested E (seen ++ [token]) agent (match_token st token).
  Proof.
    intros HE Hstate Hunique (Hsorted & Hcompatible & Hopen)
      Hagents Hvalid Hagent Htoken Hfresh Hle.
    destruct Hstate as (Hstacks & Hsections & Hprovenance).
    destruct (token_kind token) eqn:Hkind.
    - unfold agent_state_nested, match_token. rewrite Hkind. cbn.
      unfold token_stack at 1. cbn. rewrite <- Hagent, lookup_insert_eq.
      fold (token_stack st agent). split_and!.
      + cbn. rewrite Hagent. constructor; first done.
        rewrite Forall_forall. intros old Hold.
        apply Hle. destruct (match_stacks_wf_token_stack E seen st agent old Hstacks Hold)
          as [Hin _]. done.
      + exact Hcompatible.
      + unfold token_stack. cbn. rewrite lookup_insert_eq. cbn. rewrite Hagent.
        intros open section [-> | Hold] Hsection.
        * left. by eapply matched_section_unlock_before.
        * by apply Hopen.
    - unfold match_token. rewrite Hkind.
      destruct (token_stack st (token_agent token)) as [|lock rest] eqn:Hstack.
      + exact (conj Hsorted (conj Hcompatible Hopen)).
      + unfold agent_state_nested. cbn. unfold token_stack at 1. cbn.
        rewrite <- Hagent, lookup_insert_eq.
        assert (Hstack_agent : token_stack st agent = lock :: rest).
        { by rewrite <- Hagent. }
        assert (Hlock_valid : rcu_token_valid E lock).
        { destruct (match_stacks_wf_token_stack E seen st agent lock Hstacks)
            as (_ & _ & _ & Hvalid_lock); first by rewrite Hstack_agent; left. done. }
        assert (Hlock_agent : token_agent lock = agent).
        { destruct (match_stacks_wf_token_stack E seen st agent lock Hstacks)
            as (_ & Hagent_lock & _); first by rewrite Hstack_agent; left. done. }
        assert (Hlock_seen : In lock seen).
        { destruct (match_stacks_wf_token_stack E seen st agent lock Hstacks)
            as (Hin & _); first by rewrite Hstack_agent; left. done. }
        assert (Hlock_stack : In lock (token_stack st agent)).
        { rewrite Hstack_agent. by left. }
        assert (Hnew_unlock : forall section,
            In section st.(match_sections) ->
            po E section.(cs_unlock) token.(token_id)).
        { intros section Hsection. by eapply matched_section_unlock_before. }
        split_and!.
        * rewrite Hstack_agent in Hsorted. by inversion Hsorted.
        * intros first second [Hfirst | Hfirst] [Hsecond | Hsecond].
          -- subst first second. by left.
          -- subst first. pose proof (Hopen lock second Hlock_stack Hsecond)
               as [Hbefore | Hinside].
             ++ right. right. left. exact Hbefore.
             ++ right. right. right. left. split; first exact Hinside.
                by apply Hnew_unlock.
          -- apply rcu_sections_compatible_symmetric. subst second.
             pose proof (Hopen lock first Hlock_stack Hfirst) as [Hbefore | Hinside].
             ++ right. right. left. exact Hbefore.
             ++ right. right. right. left. split; first exact Hinside.
                by apply Hnew_unlock.
          -- by apply Hcompatible.
        * intros open section Hopen_rest Hsection.
          unfold token_stack in Hopen_rest. cbn in Hopen_rest.
          rewrite lookup_insert_eq in Hopen_rest. cbn in Hopen_rest.
          destruct Hsection as [Hnew | Hold].
          -- subst section. right. cbn.
             rewrite Hstack_agent in Hsorted. inversion Hsorted as [|? ? Hrest Hall].
             rewrite Forall_forall in Hall.
             assert (Hopen_stack : In open (token_stack st agent)).
             { rewrite Hstack_agent. simpl. right. exact Hopen_rest. }
             destruct (match_stacks_wf_token_stack E seen st agent open Hstacks)
               as (_ & Hopen_agent & _ & Hopen_valid); first exact Hopen_stack.
             eapply rcu_tokens_po; [exact HE | exact Hopen_valid | exact Hlock_valid | | |].
             ++ by rewrite Hopen_agent, Hlock_agent.
             ++ intros Hid. destruct Hunique as (Hlocks & _).
                unfold agent_lock_ids in Hlocks. rewrite Hstack_agent in Hlocks.
                apply (NoDup_cons_1_1 (token_id lock) (token_id <$> rest)).
                { apply (proj1 (stdpp.list_relations.list.NoDup_app _ _)) in Hlocks
                    as (_ & _ & Hstack_ids). exact Hstack_ids. }
                rewrite list_elem_of_In. apply in_map_iff. exists open. split; last done.
                by symmetry.
             ++ by apply Hall.
          -- apply Hopen.
             ++ rewrite Hstack_agent. cbn. right. exact Hopen_rest.
             ++ exact Hold.
  Qed.

  Lemma match_tokens_agent_state_nested E seen tokens agent st :
    event_structure_wf E ->
    StronglySorted rcu_token_le (seen ++ tokens) ->
    (forall token, In token (seen ++ tokens) -> token.(token_agent) = agent) ->
    (forall token, In token (seen ++ tokens) -> rcu_token_valid E token) ->
    NoDup (token_id <$> (seen ++ tokens)) ->
    match_state_wf E seen st ->
    agent_state_unique seen agent st ->
    agent_state_nested E seen agent st ->
    agent_state_nested E (seen ++ tokens) agent (match_tokens tokens st).
  Proof.
    induction tokens as [|token tokens IH] in seen, st |- *.
    - simpl. intros. by rewrite app_nil_r.
    - intros HE Hsorted Hagents Hvalid Hnodup Hstate Hunique Hnested. simpl.
      assert (Htoken_agent : token_agent token = agent).
      { apply Hagents. apply in_or_app. right. by left. }
      assert (Htoken_valid : rcu_token_valid E token).
      { apply Hvalid. apply in_or_app. right. by left. }
      assert (Hfresh : ~ In (token_id token) (token_id <$> seen)).
      { rewrite map_app in Hnodup.
        apply (proj1 (stdpp.list_relations.list.NoDup_app _ _)) in Hnodup
          as (_ & Hdisjoint & _).
        intros Hin. apply (Hdisjoint (token_id token)); first by rewrite list_elem_of_In.
        rewrite list_elem_of_In. simpl. by left. }
      assert (Hle : forall old, In old seen -> rcu_token_le old token).
      { by eapply strongly_sorted_prefix_le. }
      assert (Hstate_next : match_state_wf E (seen ++ [token]) (match_token st token)).
      { eapply match_token_state_wf; try done. }
      assert (Hunique_next :
          agent_state_unique (seen ++ [token]) agent (match_token st token)).
      { eapply match_token_agent_state_unique; try done. }
      assert (Hnested_next :
          agent_state_nested E (seen ++ [token]) agent (match_token st token)).
      { eapply match_token_agent_state_nested; try done.
        - intros old Hold. apply Hagents. apply in_or_app. by left.
        - intros old Hold. apply Hvalid. apply in_or_app. by left. }
      replace (seen ++ token :: tokens) with ((seen ++ [token]) ++ tokens)
        in Hsorted, Hagents, Hvalid, Hnodup |- * by (rewrite <- app_assoc; done).
      by eapply IH.
  Qed.

  Lemma empty_agent_state_nested E agent :
    agent_state_nested E [] agent empty_match_state.
  Proof.
    split_and!.
    - unfold token_stack, empty_match_state. cbn.
      change (default [] ((∅ : gmap agent_id (list rcu_token)) !! agent)) with
        ([] : list rcu_token). constructor.
    - intros first second Hfirst. inversion Hfirst.
    - intros open section Hopen. unfold token_stack, empty_match_state in Hopen. cbn in Hopen.
      change (In open (default [] ((∅ : gmap agent_id (list rcu_token)) !! agent)))
        in Hopen. inversion Hopen.
  Qed.

  Lemma compute_agent_matching_nested E agent first second :
    event_structure_wf E ->
    In first (compute_agent_matching E agent).(matched_sections) ->
    In second (compute_agent_matching E agent).(matched_sections) ->
    rcu_sections_compatible E first second.
  Proof.
    intros HE Hfirst Hsecond.
    assert (Hagents : forall token,
        In token ([] ++ rcu_agent_token_trace E agent) -> token_agent token = agent).
    { intros token Hin. by apply rcu_agent_token_trace_lookup in Hin as [Hagent _]. }
    assert (Hvalid : forall token,
        In token ([] ++ rcu_agent_token_trace E agent) -> rcu_token_valid E token).
    { intros token Hin. by apply rcu_agent_token_trace_lookup in Hin as [_ Hlookup]. }
    pose proof (match_tokens_agent_state_nested E [] (rcu_agent_token_trace E agent)
      agent empty_match_state HE (rcu_agent_token_trace_sorted E agent) Hagents Hvalid
      (rcu_agent_token_ids_nodup E agent) (empty_match_state_wf E)
      (empty_agent_state_unique agent) (empty_agent_state_nested E agent))
      as (_ & Hcompatible & _).
    unfold compute_agent_matching, compute_agent_match_state, result_of_state
      in Hfirst, Hsecond. by eapply Hcompatible.
  Qed.

  Theorem rcu_rscs_noncrossing E lock1 unlock1 lock2 unlock2 :
    event_structure_wf E ->
    rcu_rscs E lock1 unlock1 -> rcu_rscs E lock2 unlock2 ->
    same_agent E lock1 lock2 ->
    rcu_sections_compatible E (CriticalSection lock1 unlock1)
      (CriticalSection lock2 unlock2).
  Proof.
    intros HE (agent1 & Hfirst) (agent2 & Hsecond) Hsame.
    destruct (compute_agent_matching_section_agent E agent1
      (CriticalSection lock1 unlock1) HE Hfirst) as
      (lock_index1 & unlock_index1 & Hlock1 & Hunlock1).
    destruct (compute_agent_matching_section_agent E agent2
      (CriticalSection lock2 unlock2) HE Hsecond) as
      (lock_index2 & unlock_index2 & Hlock2 & Hunlock2).
    cbn in Hlock1, Hlock2.
    destruct Hsame as (agent & Hagent1 & Hagent2).
    change (lookup_event E lock1 ≫= agent_of = Some agent) in Hagent1.
    change (lookup_event E lock2 ≫= agent_of = Some agent) in Hagent2.
    unfold lookup_event in Hagent1, Hagent2.
    rewrite Hlock1 in Hagent1. cbn in Hagent1.
    rewrite Hlock2 in Hagent2. cbn in Hagent2.
    assert (agent1 = agent2) as -> by congruence.
    by eapply compute_agent_matching_nested.
  Qed.

  Lemma match_token_sections_mono st token cs :
    In cs st.(match_sections) -> In cs (match_token st token).(match_sections).
  Proof.
    intros Hcs. unfold match_token. destruct (token_kind token); first done.
    destruct (token_stack st (token_agent token)); simpl; by right || done.
  Qed.

  Lemma compute_agent_state_insert_other E eid ev token agent :
    lookup_event E eid = None ->
    rcu_token_of_entry (eid, ev) = Some token ->
    token.(token_agent) <> agent ->
    compute_agent_match_state (<[eid := ev]> E) agent = compute_agent_match_state E agent.
  Proof.
    intros Hfresh Htoken Hneq. unfold compute_agent_match_state.
    by rewrite (rcu_agent_token_trace_insert_other E eid ev token agent
      Hfresh Htoken Hneq).
  Qed.

  Lemma compute_agent_state_insert_non_rcu E eid ev agent :
    lookup_event E eid = None ->
    rcu_token_of_entry (eid, ev) = None ->
    compute_agent_match_state (<[eid := ev]> E) agent = compute_agent_match_state E agent.
  Proof.
    intros Hfresh Hnone. unfold compute_agent_match_state.
    by rewrite (rcu_agent_token_trace_insert_non_rcu E eid ev agent Hfresh Hnone).
  Qed.

  Lemma compute_agent_state_insert_tail E eid ev token :
    rcu_agent_tail E eid ev ->
    rcu_token_of_entry (eid, ev) = Some token ->
    compute_agent_match_state (<[eid := ev]> E) token.(token_agent) =
      match_token (compute_agent_match_state E token.(token_agent)) token.
  Proof.
    intros Htail Htoken. unfold compute_agent_match_state.
    rewrite (rcu_agent_token_trace_insert_tail E eid ev token Htail Htoken),
      match_tokens_app. done.
  Qed.

  Lemma rcu_rscs_agent_tail_mono E eid ev :
    rcu_agent_tail E eid ev ->
    rel_included (rcu_rscs E) (rcu_rscs (<[eid := ev]> E)).
  Proof.
    intros Htail lock unlock (agent & Hsection). exists agent.
    destruct (rcu_token_of_entry (eid, ev)) as [token |] eqn:Htoken.
    - destruct (decide (token.(token_agent) = agent)) as [Heq | Hneq].
      + subst agent.
        unfold compute_agent_matching, result_of_state in Hsection |- *.
        rewrite (compute_agent_state_insert_tail E eid ev token Htail Htoken).
        by apply match_token_sections_mono.
      + unfold compute_agent_matching, result_of_state in Hsection |- *.
        rewrite (compute_agent_state_insert_other E eid ev token agent
          (proj1 Htail) Htoken Hneq). done.
    - unfold compute_agent_matching, result_of_state in Hsection |- *.
      rewrite (compute_agent_state_insert_non_rcu E eid ev agent
        (proj1 Htail) Htoken). done.
  Qed.

  Lemma rcu_rscs_agent_tail_lock E eid ev token lock unlock :
    rcu_agent_tail E eid ev ->
    rcu_token_of_entry (eid, ev) = Some token ->
    token.(token_kind) = RcuTokenLock ->
    (rcu_rscs (<[eid := ev]> E) lock unlock <-> rcu_rscs E lock unlock).
  Proof.
    intros Htail Htoken Hkind. split; last by eapply rcu_rscs_agent_tail_mono.
    intros (agent & Hsection). exists agent.
    destruct (decide (token.(token_agent) = agent)) as [Heq | Hneq].
    - subst agent. unfold compute_agent_matching, result_of_state in Hsection |- *.
      rewrite (compute_agent_state_insert_tail E eid ev token Htail Htoken) in Hsection.
      unfold match_token in Hsection. rewrite Hkind in Hsection. done.
    - unfold compute_agent_matching, result_of_state in Hsection |- *.
      by rewrite (compute_agent_state_insert_other E eid ev token agent
        (proj1 Htail) Htoken Hneq) in Hsection.
  Qed.

  Lemma rcu_rscs_insert_non_rcu E eid ev lock unlock :
    lookup_event E eid = None ->
    rcu_token_of_entry (eid, ev) = None ->
    (rcu_rscs (<[eid := ev]> E) lock unlock <-> rcu_rscs E lock unlock).
  Proof.
    intros Hfresh Hnone. split; intros (agent & Hsection); exists agent;
      unfold compute_agent_matching, result_of_state in Hsection |- *.
    - rewrite (compute_agent_state_insert_non_rcu E eid ev agent Hfresh Hnone)
        in Hsection. done.
    - rewrite (compute_agent_state_insert_non_rcu E eid ev agent Hfresh Hnone). done.
  Qed.

  Lemma rcu_rscs_agent_tail_unlock E eid ev token lock_token rest lock unlock :
    rcu_agent_tail E eid ev ->
    rcu_token_of_entry (eid, ev) = Some token ->
    token.(token_kind) = RcuTokenUnlock ->
    token_stack (compute_agent_match_state E token.(token_agent)) token.(token_agent) =
      lock_token :: rest ->
    (rcu_rscs (<[eid := ev]> E) lock unlock <->
      (lock = lock_token.(token_id) /\ unlock = token.(token_id)) \/
      rcu_rscs E lock unlock).
  Proof.
    intros Htail Htoken Hkind Hstack. split.
    - intros (agent & Hsection).
      destruct (decide (token.(token_agent) = agent)) as [Heq | Hneq].
      + subst agent. unfold compute_agent_matching, result_of_state in Hsection.
        rewrite (compute_agent_state_insert_tail E eid ev token Htail Htoken) in Hsection.
        unfold match_token in Hsection. rewrite Hkind, Hstack in Hsection. simpl in Hsection.
        destruct Hsection as [Hnew | Hold].
        * injection Hnew as <- <-. by left.
        * right. exists (token_agent token). done.
      + right. exists agent. unfold compute_agent_matching, result_of_state in Hsection |- *.
        by rewrite (compute_agent_state_insert_other E eid ev token agent
          (proj1 Htail) Htoken Hneq) in Hsection.
    - intros [[-> ->] | Hold].
      + exists token.(token_agent). unfold compute_agent_matching, result_of_state.
        rewrite (compute_agent_state_insert_tail E eid ev token Htail Htoken).
        unfold match_token. rewrite Hkind, Hstack. simpl. by left.
      + by eapply rcu_rscs_agent_tail_mono.
  Qed.

  Lemma computed_agent_stack_insert_lock E eid ev token :
    rcu_agent_tail E eid ev ->
    rcu_token_of_entry (eid, ev) = Some token ->
    token.(token_kind) = RcuTokenLock ->
    computed_agent_stack (<[eid := ev]> E) token.(token_agent) =
      token.(token_id) :: computed_agent_stack E token.(token_agent).
  Proof.
    intros Htail Htoken Hkind. unfold computed_agent_stack.
    rewrite (compute_agent_state_insert_tail E eid ev token Htail Htoken).
    unfold match_token. rewrite Hkind. simpl. unfold token_stack.
    cbn. rewrite lookup_insert_eq. done.
  Qed.

  Lemma computed_agent_stack_insert_unlock E eid ev token lock_token rest :
    rcu_agent_tail E eid ev ->
    rcu_token_of_entry (eid, ev) = Some token ->
    token.(token_kind) = RcuTokenUnlock ->
    token_stack (compute_agent_match_state E token.(token_agent)) token.(token_agent) =
      lock_token :: rest ->
    computed_agent_stack (<[eid := ev]> E) token.(token_agent) = token_id <$> rest.
  Proof.
    intros Htail Htoken Hkind Hstack. unfold computed_agent_stack.
    rewrite (compute_agent_state_insert_tail E eid ev token Htail Htoken).
    unfold match_token. rewrite Hkind, Hstack. simpl. unfold token_stack.
    cbn. rewrite lookup_insert_eq. done.
  Qed.

  Lemma computed_agent_stack_insert_other E eid ev token agent :
    lookup_event E eid = None ->
    rcu_token_of_entry (eid, ev) = Some token ->
    token.(token_agent) <> agent ->
    computed_agent_stack (<[eid := ev]> E) agent = computed_agent_stack E agent.
  Proof.
    intros Hfresh Htoken Hneq. unfold computed_agent_stack.
    by rewrite (compute_agent_state_insert_other E eid ev token agent Hfresh Htoken Hneq).
  Qed.

  Lemma computed_agent_stack_insert_non_rcu E eid ev agent :
    lookup_event E eid = None ->
    rcu_token_of_entry (eid, ev) = None ->
    computed_agent_stack (<[eid := ev]> E) agent = computed_agent_stack E agent.
  Proof.
    intros Hfresh Hnone. unfold computed_agent_stack.
    by rewrite (compute_agent_state_insert_non_rcu E eid ev agent Hfresh Hnone).
  Qed.

  Lemma rcu_rscs_tail_mono E eid ev :
    rcu_trace_tail E eid ev ->
    rel_included (rcu_rscs E) (rcu_rscs (<[eid := ev]> E)).
  Proof.
    intros Htail. apply rcu_rscs_agent_tail_mono.
    by apply rcu_trace_tail_agent_tail.
  Qed.

  Lemma rcu_rscsi_tail_mono E eid ev :
    rcu_trace_tail E eid ev ->
    rel_included (rcu_rscsi E) (rcu_rscsi (<[eid := ev]> E)).
  Proof. intros Htail unlock lock Hsection. by eapply rcu_rscs_tail_mono. Qed.

  (** One round of the Bell fixed point.  A candidate connects an unmatched
      lock to an unmatched unlock in [po] when no unmatched RCU event lies
      strictly between them. *)
  Definition bell_endpoint_matched (sections : list critical_section) (eid : event_id) : Prop :=
    Exists (fun cs => cs.(cs_lock) = eid \/ cs.(cs_unlock) = eid) sections.

  Global Instance bell_endpoint_matched_dec sections eid :
      Decision (bell_endpoint_matched sections eid).
  Proof. solve_decision. Defined.

  Definition bell_between (middle lock unlock : rcu_token) : Prop :=
    token_agent middle = token_agent lock /\
    token_agent middle = token_agent unlock /\
    token_index lock < token_index middle /\
    token_index middle < token_index unlock.

  Global Instance bell_between_dec middle lock unlock :
      Decision (bell_between middle lock unlock).
  Proof. solve_decision. Defined.

  Definition bell_addable (tokens : list rcu_token)
      (sections : list critical_section) (lock unlock : rcu_token) : Prop :=
    lock.(token_kind) = RcuTokenLock /\
    unlock.(token_kind) = RcuTokenUnlock /\
    lock.(token_agent) = unlock.(token_agent) /\
    lock.(token_index) < unlock.(token_index) /\
    ~ bell_endpoint_matched sections lock.(token_id) /\
    ~ bell_endpoint_matched sections unlock.(token_id) /\
    ~ Exists
        (fun middle =>
          ~ bell_endpoint_matched sections middle.(token_id) /\
          bell_between middle lock unlock)
        tokens.

  Global Instance bell_addable_dec tokens sections lock unlock :
      Decision (bell_addable tokens sections lock unlock).
  Proof. solve_decision. Defined.

  Fixpoint bell_pairs_from (tokens all : list rcu_token)
      (sections : list critical_section) : list critical_section :=
    match tokens with
    | [] => []
    | lock :: tokens =>
        let pairs :=
          fold_right
            (fun unlock pairs =>
              if decide (bell_addable all sections lock unlock)
              then CriticalSection lock.(token_id) unlock.(token_id) :: pairs
              else pairs)
            [] all in
        pairs ++ bell_pairs_from tokens all sections
    end.

  Definition bell_round (tokens : list rcu_token)
      (sections : list critical_section) : list critical_section :=
    bell_pairs_from tokens tokens sections ++ sections.

  Fixpoint bell_iter (rounds : nat) (tokens : list rcu_token)
      (sections : list critical_section) : list critical_section :=
    match rounds with
    | 0 => sections
    | S rounds => bell_iter rounds tokens (bell_round tokens sections)
    end.

  Definition bell_iterated_sections (E : event_structure) : list critical_section :=
    let tokens := rcu_token_trace E in bell_iter (length tokens) tokens [].

  (** Relational view of the selected Bell matching.  The theorem below
      identifies this aggregate view with the per-agent executable relation;
      [bell_iterated_sections] is the direct bounded transcription of Bell's
      recursive adjacent-unmatched construction. *)
  Definition bell_rcu_rscs (E : event_structure) : relation :=
    fun lock unlock =>
      In (CriticalSection lock unlock)
        (compute_rcu_matching E).(matched_sections).

  Theorem rcu_rscs_bell_rcu_rscs E :
    event_structure_wf E ->
    forall lock unlock, rcu_rscs E lock unlock <-> bell_rcu_rscs E lock unlock.
  Proof. intros HE lock unlock. apply rcu_rscs_compute_rcu_matching. done. Qed.

  Definition unmatched_rcu_locks_empty (E : event_structure) : Prop :=
    forall lock,
      event_has_barrier_kind E BarrierRcuLock lock ->
      rel_domain (bell_rcu_rscs E) lock.

  Definition unmatched_rcu_unlocks_empty (E : event_structure) : Prop :=
    forall unlock,
      event_has_barrier_kind E BarrierRcuUnlock unlock ->
      rel_range (bell_rcu_rscs E) unlock.

  Theorem rcu_matching_complete_iff_unmatched_flags_empty E :
    event_structure_wf E ->
    (rcu_matching_complete E <->
      unmatched_rcu_locks_empty E /\ unmatched_rcu_unlocks_empty E).
  Proof.
    intros HE. split.
    - intros Hcomplete. split.
      + intros lock Hlock. destruct (rcu_matching_complete_covers_lock E lock
          Hcomplete Hlock) as (unlock & Hsection).
        exists unlock. apply (proj1 (rcu_rscs_bell_rcu_rscs E HE lock unlock)). done.
      + intros unlock Hunlock. destruct (rcu_matching_complete_covers_unlock E unlock
          Hcomplete Hunlock) as (lock & Hsection).
        exists lock. apply (proj1 (rcu_rscs_bell_rcu_rscs E HE lock unlock)). done.
    - intros [Hlocks Hunlocks]. unfold rcu_matching_complete, compute_rcu_matching.
      apply combine_agent_matchings_empty. intros agent Hagent.
      split.
      + apply compute_agent_matching_locks_empty_of_covered; first done.
        intros lock Hlock. destruct (Hlocks lock Hlock) as (unlock & Hsection).
        exists unlock. apply (proj2 (rcu_rscs_bell_rcu_rscs E HE lock unlock)). done.
      + apply compute_agent_matching_unlocks_empty_of_covered; first done.
        intros unlock Hunlock. destruct (Hunlocks unlock Hunlock) as (lock & Hsection).
        exists lock. apply (proj2 (rcu_rscs_bell_rcu_rscs E HE lock unlock)). done.
  Qed.

  Lemma compute_rcu_sections_complete E sections :
    compute_rcu_sections E = Some sections <->
    rcu_matching_complete E /\ sections = (compute_rcu_matching E).(matched_sections).
  Proof.
    unfold compute_rcu_sections. case_decide; last naive_solver.
    split; intros Hsome; first (injection Hsome as <-; done).
    destruct Hsome as [_ ->]. done.
  Qed.

  Lemma compute_rcu_sections_incomplete E :
    compute_rcu_sections E = None <-> ~ rcu_matching_complete E.
  Proof. unfold compute_rcu_sections. by case_decide. Qed.

  Module Tests.
    Definition sample_events : event_structure := {[
      0 := EAgent 0 0 (LBarrier BarrierRcuLock);
      1 := EAgent 0 1 (LMemory AccessRead AccessOnce NotRmw 0 0%Z);
      2 := EAgent 0 2 (LBarrier BarrierRcuLock);
      3 := EAgent 0 3 (LBarrier BarrierRcuUnlock);
      4 := EAgent 0 4 (LBarrier BarrierRcuUnlock);
      5 := EAgent 0 5 (LBarrier BarrierRcuLock);
      6 := EAgent 0 6 (LBarrier BarrierRcuUnlock);
      7 := EAgent 1 0 (LBarrier BarrierRcuLock);
      8 := EAgent 1 1 (LBarrier BarrierRcuUnlock);
      9 := EAgent 1 2 (LMemory AccessRead AccessOnce NotRmw 0 0%Z)
    ]}.

    Example nested_sequential_and_independent_sections :
      compute_rcu_sections sample_events = Some [
        CriticalSection 5 6;
        CriticalSection 0 4;
        CriticalSection 2 3;
        CriticalSection 7 8].
    Proof. vm_compute. reflexivity. Qed.

    Example unmatched_events_reject_complete_sections :
      compute_rcu_sections {[0 := EAgent 0 0 (LBarrier BarrierRcuUnlock)]} = None /\
      compute_rcu_sections {[0 := EAgent 0 0 (LBarrier BarrierRcuLock)]} = None.
    Proof. vm_compute. split; reflexivity. Qed.

    Example finite_bell_iteration_matches_stack :
      bell_iterated_sections sample_events ≡ₚ
        (compute_rcu_matching sample_events).(matched_sections).
    Proof.
      apply NoDup_Permutation; vm_compute.
      - repeat constructor; set_solver.
      - repeat constructor; set_solver.
      - intros [lock unlock]. set_solver.
    Qed.
  End Tests.

End RcuMatching.
