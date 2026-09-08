From Stdlib Require Import List.
From stdpp Require Import gmap fin_sets sorting tactics.
From iris_lkmm.lkmm Require Import memory_relations rcu_graph.
From iris_lkmm.lang Require Import program_graph.
From iris_lkmm.operational Require Import rcu_builder rcu_candidate.
Import ListNotations.

(** Convert map/set candidates to the builder's list representation.
    Sorting chooses a loading order only; it does not rename event IDs or
    change the graph. The builder stores events in reverse loading order. *)
Module LkmmCandidateEncoding.
  Export LkmmProgramGraph.
  Import RcuBuilder RcuCandidate RcuGraph LkmmMemoryRelations.

  Local Definition loading_le (x y : labeled_event) : Prop :=
    match rcu_token_of_entry (x.(le_id), x.(le_event)),
          rcu_token_of_entry (y.(le_id), y.(le_event)) with
    | None, _ => True
    | Some _, None => False
    | Some tx, Some ty => rcu_token_le ty tx
    end.

  Local Instance loading_le_dec x y : Decision (loading_le x y).
  Proof. unfold loading_le. repeat case_match; apply _. Defined.

  Local Instance loading_le_total : Total loading_le.
  Proof.
    intros x y. unfold loading_le. repeat case_match; try tauto.
    apply rcu_token_le_total.
  Qed.

  Local Instance loading_le_transitive : Transitive loading_le.
  Proof.
    intros x y z. unfold loading_le. repeat case_match; try tauto.
    intros Hxy Hyz. by etrans.
  Qed.

  Definition canonical_events (E : event_structure) : list labeled_event :=
    merge_sort loading_le ((fun p => LabeledEvent p.1 p.2) <$> map_to_list E).

  Local Lemma canonical_events_permutation E :
    canonical_events E ≡ₚ (fun p => LabeledEvent p.1 p.2) <$> map_to_list E.
  Proof. apply merge_sort_Permutation. Qed.

  Lemma canonical_events_nodup E : NoDup (map le_id (canonical_events E)).
  Proof.
    rewrite canonical_events_permutation, <-list_fmap_compose.
    change (NoDup (fst <$> map_to_list E)). apply NoDup_fst_map_to_list.
  Qed.

  Local Lemma load_events_map evs :
    (load_events evs).(raw_events) =
      list_to_map ((fun e => (e.(le_id), e.(le_event))) <$> evs).
  Proof. induction evs; simpl; [done | by rewrite IHevs]. Qed.

  Lemma canonical_events_exact E : (load_events (canonical_events E)).(raw_events) = E.
  Proof.
    rewrite load_events_map. symmetry. apply list_to_map_flip.
    rewrite canonical_events_permutation, <-list_fmap_compose.
    rewrite (list_fmap_ext _ id _); first by rewrite list_fmap_id.
    intros i [eid ev] Hlookup. done.
  Qed.

  Local Lemma load_events_lookup_in evs eid ev :
    lookup_event (load_events evs).(raw_events) eid = Some ev ->
    LabeledEvent eid ev ∈ evs.
  Proof.
    induction evs as [|[i e] evs IH]; simpl; first discriminate.
    intros Hlookup. unfold lookup_event in Hlookup.
    apply lookup_insert_Some in Hlookup as [[<- <-] | [_ Hlookup]].
    - by left.
    - right. by apply IH.
  Qed.

  Local Lemma sorted_events_canonical evs :
    StronglySorted loading_le evs -> NoDup (map le_id evs) -> events_in_canonical_order evs.
  Proof.
    intros Hsort. induction Hsort as [|e evs Hsort IH Hall]; first done.
    intros Hdup. pose proof (NoDup_cons_1_1 _ _ Hdup) as Hfresh.
    split; first by apply IH, (NoDup_cons_1_2 _ _ Hdup).
    split.
    - apply eq_None_not_Some. intros [ev Hlookup]. apply Hfresh.
      apply list_elem_of_fmap. exists (LabeledEvent e.(le_id) ev). split; first done.
      by apply load_events_lookup_in.
    - destruct (rcu_token_of_entry (e.(le_id), e.(le_event))) as [token |] eqn:He; last done.
      apply List.Forall_forall. intros old Hold.
      rewrite <-list_elem_of_In, rcu_token_trace_permutation in Hold.
      rewrite list_elem_of_In in Hold. apply collect_rcu_tokens_spec in Hold.
      rewrite <-list_elem_of_In in Hold. apply elem_of_map_to_list in Hold.
      apply load_events_lookup_in in Hold.
      rewrite List.Forall_forall in Hall.
      specialize (Hall (LabeledEvent old.(token_id) (event_of_rcu_token old))
        (proj1 (list_elem_of_In _ _) Hold)).
      unfold loading_le in Hall. cbn [le_id le_event] in Hall. rewrite He in Hall.
      destruct old as [i t n k]. destruct k; exact Hall.
  Qed.

  Lemma canonical_events_order E : events_in_canonical_order (canonical_events E).
  Proof.
    apply sorted_events_canonical; [|apply canonical_events_nodup].
    unfold canonical_events. apply StronglySorted_merge_sort; apply _.
  Qed.

  Local Lemma load_rf_raw edges E co0 rmw0 addr0 data0 ctrl0 :
    load_rf edges (RawGraph E [] co0 rmw0 addr0 data0 ctrl0) =
      RawGraph E edges co0 rmw0 addr0 data0 ctrl0.
  Proof. induction edges; simpl; [done | by rewrite IHedges]. Qed.

  Local Lemma load_co_raw edges E rf0 rmw0 addr0 data0 ctrl0 :
    load_co edges (RawGraph E rf0 [] rmw0 addr0 data0 ctrl0) =
      RawGraph E rf0 edges rmw0 addr0 data0 ctrl0.
  Proof. induction edges; simpl; [done | by rewrite IHedges]. Qed.

  Local Lemma load_rmw_raw edges E rf0 co0 addr0 data0 ctrl0 :
    load_rmw edges (RawGraph E rf0 co0 [] addr0 data0 ctrl0) =
      RawGraph E rf0 co0 edges addr0 data0 ctrl0.
  Proof. induction edges; simpl; [done | by rewrite IHedges]. Qed.

  Local Lemma load_direct_addr_raw edges E rf0 co0 rmw0 data0 ctrl0 :
    load_direct_addr edges (RawGraph E rf0 co0 rmw0 [] data0 ctrl0) =
      RawGraph E rf0 co0 rmw0 edges data0 ctrl0.
  Proof. induction edges; simpl; [done | by rewrite IHedges]. Qed.

  Local Lemma load_direct_data_raw edges E rf0 co0 rmw0 addr0 ctrl0 :
    load_direct_data edges (RawGraph E rf0 co0 rmw0 addr0 [] ctrl0) =
      RawGraph E rf0 co0 rmw0 addr0 edges ctrl0.
  Proof. induction edges; simpl; [done | by rewrite IHedges]. Qed.

  Local Lemma load_direct_ctrl_raw edges E rf0 co0 rmw0 addr0 data0 :
    load_direct_ctrl edges (RawGraph E rf0 co0 rmw0 addr0 data0 []) =
      RawGraph E rf0 co0 rmw0 addr0 data0 edges.
  Proof. induction edges; simpl; [done | by rewrite IHedges]. Qed.

  Local Lemma candidate_raw_data C :
    candidate_raw C = RawGraph (load_events C.(fc_events)).(raw_events)
      C.(fc_rf) C.(fc_co) C.(fc_rmw) C.(fc_direct_addr) C.(fc_direct_data) C.(fc_direct_ctrl).
  Proof.
    unfold candidate_raw.
    pose proof (load_events_relations C.(fc_events)) as Hempty.
    destruct (load_events C.(fc_events)) as [E rf0 co0 rmw0 addr0 data0 ctrl0].
    cbn in Hempty |- *. destruct Hempty as (-> & -> & -> & -> & -> & ->).
    by rewrite load_rf_raw, load_co_raw, load_rmw_raw,
      load_direct_addr_raw, load_direct_data_raw, load_direct_ctrl_raw.
  Qed.

  Definition finite_candidate_of_core (C : core_candidate) : finite_candidate :=
    FiniteCandidate (canonical_events C.(candidate_events))
      (elements C.(candidate_rf)) (elements C.(candidate_co)) (elements C.(candidate_rmw))
      (elements C.(candidate_direct_addr)) (elements C.(candidate_direct_data))
      (elements C.(candidate_direct_ctrl)).

  Lemma finite_candidate_of_core_wf C :
    core_candidate_wf C -> candidate_well_formed (finite_candidate_of_core C).
  Proof.
    intros (HE & Hrf & Hco & Hrmw & Haddr & Hdata & Hctrl & Hmatching).
    unfold candidate_well_formed, finite_candidate_of_core. cbn.
    rewrite canonical_events_exact, !list_to_set_elements_L.
    split; first apply canonical_events_nodup.
    split; first apply canonical_events_order.
    split; first done. split; first done.
    split; first by apply rf_wf_prefix.
    split; first by apply co_wf_prefix.
    split; first by apply rmw_wf_prefix.
    done.
  Qed.

  Lemma finite_candidate_of_core_raw C :
    candidate_raw (finite_candidate_of_core C) =
      RawGraph C.(candidate_events) (elements C.(candidate_rf)) (elements C.(candidate_co))
        (elements C.(candidate_rmw)) (elements C.(candidate_direct_addr))
        (elements C.(candidate_direct_data)) (elements C.(candidate_direct_ctrl)).
  Proof. rewrite candidate_raw_data. cbn. by rewrite canonical_events_exact. Qed.

  Lemma finite_candidate_of_core_graph C :
    candidate_graph (finite_candidate_of_core C) = core_candidate_graph C.
  Proof.
    unfold candidate_graph. rewrite finite_candidate_of_core_raw.
    unfold graph_of_raw. cbn. by rewrite !list_to_set_elements_L.
  Qed.
End LkmmCandidateEncoding.
