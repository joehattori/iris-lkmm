From Stdlib Require Import Arith Lia List.
From stdpp Require Import gmap sorting tactics list.
From iris_lkmm.lkmm Require Import event_renaming rcu_replay.
Import ListNotations.

Module RcuRenaming.
  Export EventRenaming RcuReplay.

  Definition rename_token f (t : rcu_token) : rcu_token :=
    RcuToken (f t.(token_id)) t.(token_agent) t.(token_index) t.(token_kind).
  Definition rename_section f (s : critical_section) : critical_section :=
    CriticalSection (f s.(cs_lock)) (f s.(cs_unlock)).
  Definition rename_match_state f (s : rcu_match_state) : rcu_match_state :=
    RcuMatchState ((map (rename_token f)) <$> s.(match_stacks))
      (map (rename_section f) s.(match_sections)) (map f s.(match_unmatched_unlocks)).

  Lemma collect_tokens_rename f entries :
    collect_rcu_tokens ((fun p : event_id * event => (f p.1, p.2)) <$> entries) =
    rename_token f <$> collect_rcu_tokens entries.
  Proof.
    induction entries as [|[i [loc val | t n [k m r loc val | b]]] entries IH];
      simpl; try done. destruct b; simpl; try done; f_equal; done.
  Qed.

  Lemma filter_tokens_rename f (tokens : list rcu_token) t :
    filter (fun x => token_agent x = t) (rename_token f <$> tokens) =
    rename_token f <$> filter (fun x => token_agent x = t) tokens.
  Proof.
    induction tokens as [|x xs IH]; simpl; first done.
    rewrite !filter_cons. change (token_agent (rename_token f x)) with (token_agent x).
    case_decide; simpl; try done; f_equal; done.
  Qed.

  Lemma rename_token_le f E x y :
    event_structure_wf E -> rcu_token_valid E x -> rcu_token_valid E y ->
    rcu_token_le x y -> rcu_token_le (rename_token f x) (rename_token f y).
  Proof.
    intros HE Hx Hy Hle.
    destruct x as [ix tx nx kx], y as [iy ty ny ky].
    unfold rcu_token_valid, event_of_rcu_token in Hx, Hy; simpl in Hx, Hy.
    unfold rcu_token_le in *. simpl in *.
    destruct (decide (tx = ty /\ nx = ny)) as [[-> ->] | Hne]; last naive_solver lia.
    assert (ix = iy) as -> by (eapply HE; eauto). naive_solver lia.
  Qed.

  Lemma rename_tokens_sorted f E tokens :
    event_structure_wf E -> StronglySorted rcu_token_le tokens ->
    (forall x, In x tokens -> rcu_token_valid E x) ->
    StronglySorted rcu_token_le (rename_token f <$> tokens).
  Proof.
    intros HE Hsorted. induction Hsorted as [|x xs Hsorted IH Hall]; intros Hvalid;
      simpl; first constructor. constructor.
    - apply IH. intros y Hy. apply Hvalid. by right.
    - rewrite List.Forall_forall in Hall |- *. intros y Hy.
      apply in_map_iff in Hy as (old & <- & Hold).
      eapply rename_token_le; [done | apply Hvalid; by left | apply Hvalid; by right | by apply Hall].
  Qed.

  Lemma rcu_agent_token_trace_rename f E F t :
    event_renaming f E F -> event_structure_wf E ->
    rcu_agent_token_trace F t = rename_token f <$> rcu_agent_token_trace E t.
  Proof.
    intros Hren HE. apply (StronglySorted_unique rcu_token_le).
    - apply rcu_agent_token_trace_sorted.
    - eapply rename_tokens_sorted; [done | apply rcu_agent_token_trace_sorted |].
      intros x Hx. by apply rcu_agent_token_trace_lookup in Hx as [_ Hx].
    - etrans; first apply rcu_agent_token_trace_permutation.
      rewrite (event_renaming_entries f E F Hren), collect_tokens_rename, filter_tokens_rename.
      apply Permutation_map. symmetry. apply rcu_agent_token_trace_permutation.
  Qed.

  Lemma token_stack_rename f s t :
    token_stack (rename_match_state f s) t = rename_token f <$> token_stack s t.
  Proof.
    unfold token_stack, rename_match_state. simpl. rewrite lookup_fmap.
    destruct (match_stacks s !! t); done.
  Qed.

  Lemma match_token_rename f s token :
    match_token (rename_match_state f s) (rename_token f token) =
    rename_match_state f (match_token s token).
  Proof.
    unfold match_token. simpl. rewrite token_stack_rename.
    destruct (token_kind token); simpl.
    - unfold rename_match_state. simpl. by rewrite fmap_insert.
    - destruct (token_stack s (token_agent token)) as [|lock rest]; simpl; first done.
      unfold rename_match_state. simpl. by rewrite fmap_insert.
  Qed.

  Lemma match_tokens_rename f tokens s :
    match_tokens (rename_token f <$> tokens) (rename_match_state f s) =
    rename_match_state f (match_tokens tokens s).
  Proof.
    induction tokens in s |- *; simpl; first done.
    rewrite match_token_rename. apply IHtokens.
  Qed.

  Lemma compute_agent_match_state_rename f E F t :
    event_renaming f E F -> event_structure_wf E ->
    compute_agent_match_state F t = rename_match_state f (compute_agent_match_state E t).
  Proof.
    intros Hren HE. unfold compute_agent_match_state.
    rewrite (rcu_agent_token_trace_rename f E F t Hren HE).
    rewrite <- match_tokens_rename. unfold rename_match_state, empty_match_state.
    done.
  Qed.

  Lemma rcu_rscs_rename_forward f E F lock unlock :
    event_renaming f E F -> event_structure_wf E ->
    rcu_rscs E lock unlock -> rcu_rscs F (f lock) (f unlock).
  Proof.
    intros Hren HE (t & Hsection). exists t.
    unfold compute_agent_matching, result_of_state in *.
    rewrite (compute_agent_match_state_rename f E F t Hren HE). simpl.
    change (In (rename_section f (CriticalSection lock unlock))
      (map (rename_section f) (match_sections (compute_agent_match_state E t)))).
    by apply in_map.
  Qed.

  Lemma rcu_rscs_rename_backward f E F lock unlock :
    event_renaming f E F -> event_structure_wf E -> rcu_rscs F lock unlock ->
    exists old_lock old_unlock,
      rcu_rscs E old_lock old_unlock /\ f old_lock = lock /\ f old_unlock = unlock.
  Proof.
    intros Hren HE (t & Hsection).
    unfold compute_agent_matching, result_of_state in Hsection.
    rewrite (compute_agent_match_state_rename f E F t Hren HE) in Hsection. simpl in Hsection.
    apply in_map_iff in Hsection as ([l u] & Heq & Hin).
    injection Heq as Hl Hu. exists l, u. split; last done. by exists t.
  Qed.

  Theorem rcu_rscs_rename f E F lock unlock :
    event_renaming f E F -> event_structure_wf E ->
    in_event_structure E lock -> in_event_structure E unlock ->
    (rcu_rscs F (f lock) (f unlock) <-> rcu_rscs E lock unlock).
  Proof.
    intros Hren HE Hl Hu. split; last by apply rcu_rscs_rename_forward.
    intros Hsection. destruct (rcu_rscs_rename_backward f E F _ _ Hren HE Hsection)
      as (l & u & Hsection' & Hfl & Hfu).
    destruct (rcu_rscs_endpoints E l u HE Hsection') as [Hl' Hu'].
    apply in_event_structure_lookup_iff in Hl as [el Hl], Hu as [eu Hu],
      Hl' as [el' Hl'], Hu' as [eu' Hu'].
    assert (l = lock) as -> by (eapply (renaming_injective _ _ _ Hren); eauto).
    assert (u = unlock) as -> by (eapply (renaming_injective _ _ _ Hren); eauto). done.
  Qed.

  Theorem rcu_matching_complete_rename f E F :
    event_renaming f E F -> event_structure_wf E ->
    rcu_matching_complete E -> rcu_matching_complete F.
  Proof.
    intros Hren HE Hcomplete.
    assert (event_structure_wf F) as HF by (eapply event_renaming_wf; eauto).
    unfold rcu_matching_complete, compute_rcu_matching.
    apply combine_agent_matchings_empty. intros t Ht. split.
    - apply compute_agent_matching_locks_empty_of_covered; first done.
      intros lock Hlock. apply event_has_barrier_kind_lookup in Hlock as (ev & Hlookup & Hkind).
      destruct (renaming_surjective _ _ _ Hren _ _ Hlookup) as (old & Hold & <-).
      assert (event_has_barrier_kind E BarrierRcuLock old) as Htag.
      { apply event_has_barrier_kind_lookup. by exists ev. }
      destruct (rcu_matching_complete_covers_lock E old Hcomplete Htag) as (unlock & Hsection).
      exists (f unlock). by eapply rcu_rscs_rename_forward.
    - apply compute_agent_matching_unlocks_empty_of_covered; first done.
      intros unlock Hunlock. apply event_has_barrier_kind_lookup in Hunlock as (ev & Hlookup & Hkind).
      destruct (renaming_surjective _ _ _ Hren _ _ Hlookup) as (old & Hold & <-).
      assert (event_has_barrier_kind E BarrierRcuUnlock old) as Htag.
      { apply event_has_barrier_kind_lookup. by exists ev. }
      destruct (rcu_matching_complete_covers_unlock E old Hcomplete Htag) as (lock & Hsection).
      exists (f lock). by eapply rcu_rscs_rename_forward.
  Qed.

  Theorem no_gp_in_read_section_rename f E F :
    event_renaming f E F -> event_structure_wf E ->
    no_gp_in_read_section E -> no_gp_in_read_section F.
  Proof.
    intros Hren HE Hno lock unlock gp Hsection Hgp Hbefore Hafter.
    destruct (rcu_rscs_rename_backward f E F _ _ Hren HE Hsection)
      as (l & u & Hsection' & <- & <-).
    apply event_has_barrier_kind_lookup in Hgp as (ev & Hlookup & Hkind).
    destruct (renaming_surjective _ _ _ Hren _ _ Hlookup) as (g & Hg & <-).
    destruct (rcu_rscs_endpoints E l u HE Hsection') as [Hl Hu].
    assert (in_event_structure E g) as Hin by (eapply lookup_event_in; eauto).
    apply (Hno l u g Hsection').
    - apply event_has_barrier_kind_lookup. by exists ev.
    - by apply (event_renaming_po f E F l g Hren Hl Hin).
    - by apply (event_renaming_po f E F g u Hren Hin Hu).
  Qed.

  Corollary rcu_replay_wf_rename f E F :
    event_renaming f E F -> event_structure_wf E -> rcu_replay_wf E -> rcu_replay_wf F.
  Proof.
    intros Hren HE [Hmatching Hno]. split.
    - by eapply rcu_matching_complete_rename.
    - by eapply no_gp_in_read_section_rename.
  Qed.
End RcuRenaming.
