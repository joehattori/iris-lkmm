From Stdlib Require Import Relations.Relation_Operators Lia.
From stdpp Require Import tactics.
From iris_lkmm.lkmm Require Import memory_relations.

(** A reusable LKMM publication law, independent of Core programs and Iris.
    It forbids a stale data read after observing a release with an acquire.
    Event identities, locations, values, and agent indices are unrestricted. *)
Module LkmmPublication.
  Export LkmmMemoryRelations.

  Lemma release_acquire_no_stale E rmw_edges rf_edges co_edges
      data_edges addr_edges ctrl_edges a b c d :
    marked E a -> marked E b -> marked E c -> marked E d ->
    event_is_memory E a -> event_is_memory E d ->
    po E a b -> po E c d -> same_agent E d c -> d <> c ->
    release E rmw_edges b -> acquire E rmw_edges c ->
    rfe E rf_edges b c -> fre E rf_edges co_edges d a ->
    happens_before E rmw_edges rf_edges co_edges data_edges addr_edges ctrl_edges ->
    False.
  Proof.
    intros Hma Hmb Hmc Hmd Hmem_a Hmem_d Hab Hcd Hsame Hne
      Hrelease Hacquire Hrfe Hfre Hacyclic.
    assert (po_rel E rmw_edges a b) as Hrel.
    { exists b. split; last by split.
      exists a. split; last done. by split. }
    assert (cumul_fence E rmw_edges rf_edges a b) as Hcumul.
    { exists b. split; last apply rt_refl.
      exists b. split; last by split.
      exists a. split; first by split. left.
      exists a. split; [by left|by right]. }
    assert (prop E rmw_edges rf_edges co_edges d c) as Hprop.
    { exists c. split; last by split.
      exists b. split; last by right.
      exists b. split; last by split.
      exists a. split; last by apply rt_step.
      exists d. split; first by split.
      right. destruct Hfre as [Hfr Hext]. split; [by right|done]. }
    assert (hb E rmw_edges rf_edges co_edges data_edges addr_edges ctrl_edges d c) as Hback.
    { exists c. split; last by split. exists d. split; first by split.
      right. right. split; last done. split; done. }
    assert (hb E rmw_edges rf_edges co_edges data_edges addr_edges ctrl_edges c d) as Hforward.
    { exists d. split; last by split. exists c. split; first by split.
      left. right. right. split.
      - left. right. right. exists d. split.
        + exists c. split; [by split|done].
        + by split.
      - unfold same_agent, same_attribute in *. naive_solver. }
    apply (Hacyclic c). eapply t_trans; apply t_step; eassumption.
  Qed.

  (** The location protocol permits initialization and one publishing write.
      This is a restriction on writes, not an assumed property of reads. *)
  Definition publication_write initial writer index mode loc published ev : Prop :=
    ev = EInitWrite loc initial \/
    ev = EAgent writer index (LMemory AccessWrite mode NotRmw loc published).

  Definition writes_satisfy E loc (allowed : event -> Prop) : Prop :=
    forall eid ev, lookup_event E eid = Some ev ->
      is_write ev -> location_of ev = Some loc -> allowed ev.

  Lemma publication_read_source E edges r t n mode loc val :
    rf_wf E edges ->
    lookup_event E r = Some (EAgent t n (LMemory AccessRead mode NotRmw loc val)) ->
    exists w ev, lookup_event E w = Some ev /\ is_write ev /\
      location_of ev = Some loc /\ value_of ev = Some val /\ rf edges w r.
  Proof.
    intros Hrf Hr.
    destruct (rf_wf_total _ _ Hrf r _ Hr eq_refl) as [w Hwr].
    destruct (rf_wf_edge _ _ _ _ Hrf Hwr) as (ev & rev & v & Hw & Hread & Hwrite & _ & Hloc & Hv & Hrv).
    rewrite Hr in Hread. injection Hread as <-. cbn in Hrv. injection Hrv as <-.
    unfold same_location, same_attribute, execution.LkmmExecution.event_attribute in Hloc.
    rewrite Hw, Hr in Hloc. cbn in Hloc.
    exists w, ev. split_and!; try done. naive_solver.
  Qed.

  Lemma publication_memory_marked E i t n kind mode loc val :
    lookup_event E i = Some (EAgent t n (LMemory kind mode NotRmw loc val)) ->
    mode <> AccessPlain -> marked E i.
  Proof.
    intros Hi Hmode. split; first by eapply lookup_event_in.
    intros [Hplain _]. apply event_has_access_mode_lookup in Hplain as (ev & Hev & Hplain).
    rewrite Hi in Hev. injection Hev as <-. cbn in Hplain. congruence.
  Qed.

  (** Publication is a value guarantee. It does not transfer ownership or
      assume that the source write has already been emitted at a load. *)
  Lemma publication_reads E rmw_edges rf_edges co_edges data_edges addr_edges ctrl_edges
      writer reader wi wj ri rj data flag data0 flag0 published flag_value
      a b c d observed_flag observed_data :
    writer <> reader -> wi < wj -> ri < rj -> flag0 <> flag_value ->
    event_structure_wf E -> rf_wf E rf_edges -> co_wf E co_edges ->
    writes_satisfy E data (publication_write data0 writer wi AccessOnce data published) ->
    writes_satisfy E flag (publication_write flag0 writer wj AccessRelease flag flag_value) ->
    lookup_event E a = Some (EAgent writer wi (LMemory AccessWrite AccessOnce NotRmw data published)) ->
    lookup_event E b = Some (EAgent writer wj (LMemory AccessWrite AccessRelease NotRmw flag flag_value)) ->
    lookup_event E c = Some (EAgent reader ri (LMemory AccessRead AccessAcquire NotRmw flag observed_flag)) ->
    lookup_event E d = Some (EAgent reader rj (LMemory AccessRead AccessOnce NotRmw data observed_data)) ->
    happens_before E rmw_edges rf_edges co_edges data_edges addr_edges ctrl_edges ->
    observed_flag = flag_value -> observed_data = published.
  Proof.
    intros Hthreads Hwi Hri Hflag HE HRF HCO Hdata Hflagwrites Ha Hb Hc Hd Hhb ->.
    destruct (decide (observed_data = published)) as [Heq|Hneval]; first done.
    exfalso.
    assert (rf rf_edges b c) as Hbc.
    { destruct (publication_read_source _ _ _ _ _ _ _ _ HRF Hc)
        as (w & ev & Hw & Hwrite & Hloc & Hval & Hrf).
      destruct (Hflagwrites w ev Hw Hwrite Hloc) as [-> | ->]; first (cbn in Hval; congruence).
      assert (w = b) as -> by (eapply HE; [exact Hw|exact Hb]). done. }
    assert (exists i, lookup_event E i = Some (EInitWrite data data0) /\
      rf rf_edges i d) as (i & Hi & Hid).
    { destruct (publication_read_source _ _ _ _ _ _ _ _ HRF Hd)
        as (w & ev & Hw & Hwrite & Hloc & Hval & Hrf).
      destruct (Hdata w ev Hw Hwrite Hloc) as [-> | ->]; last (cbn in Hval; congruence).
      exists w. done. }
    assert (co co_edges i a) as Hia.
    { eapply (co_wf_initial_first _ _ HCO i a data
        (EAgent writer wi (LMemory AccessWrite AccessOnce NotRmw data published))).
      - exists data0. done.
      - done.
      - reflexivity.
      - eapply same_attribute_from_lookup; [exact Hi|exact Ha|reflexivity|reflexivity].
      - intros ->. rewrite Ha in Hi. discriminate. }
    assert (rfe E rf_edges b c) as Hrfe.
    { split; first done. unfold ext, same_agent, same_attribute, execution.LkmmExecution.event_attribute.
      rewrite Hb, Hc. cbn. naive_solver. }
    assert (fre E rf_edges co_edges d a) as Hfre.
    { split; first by exists i.
      unfold ext, same_agent, same_attribute, execution.LkmmExecution.event_attribute.
      rewrite Hd, Ha. cbn. naive_solver. }
    assert (marked E a) as Hma by (eapply publication_memory_marked; [exact Ha|discriminate]).
    assert (marked E b) as Hmb by (eapply publication_memory_marked; [exact Hb|discriminate]).
    assert (marked E c) as Hmc by (eapply publication_memory_marked; [exact Hc|discriminate]).
    assert (marked E d) as Hmd by (eapply publication_memory_marked; [exact Hd|discriminate]).
    assert (event_is_memory E a) as Hmem_a by (eexists; split; [exact Ha|done]).
    assert (event_is_memory E d) as Hmem_d by (eexists; split; [exact Hd|done]).
    assert (po E a b) as Hab by (do 5 eexists; split_and!; eassumption).
    assert (po E c d) as Hcd by (do 5 eexists; split_and!; eassumption).
    assert (same_agent E d c) as Hsame.
    { eapply same_attribute_from_lookup; [exact Hd|exact Hc|reflexivity|reflexivity]. }
    assert (d <> c) as Hne.
    { intros ->. rewrite Hc in Hd. injection Hd. intros. lia. }
    assert (release E rmw_edges b) as Hrelease.
    { unfold release, failed_rmw, event_has_access_mode, event_has_access_kind,
        event_is_rmw_marked, execution.LkmmExecution.event_attribute.
      rewrite Hb. cbn. intuition discriminate. }
    assert (acquire E rmw_edges c) as Hacquire.
    { unfold acquire, failed_rmw, event_has_access_mode, event_has_access_kind,
        event_is_rmw_marked, execution.LkmmExecution.event_attribute.
      rewrite Hc. cbn. intuition discriminate. }
    eapply (release_acquire_no_stale E rmw_edges rf_edges co_edges
      data_edges addr_edges ctrl_edges a b c d); eassumption.
  Qed.
End LkmmPublication.
