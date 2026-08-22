From Stdlib Require Import Relations.Relation_Operators ZArith.
From stdpp Require Import gmap tactics.
From iris_lkmm.lkmm Require Import execution.

(** Finite candidate relations for the relational LKMM model.

    Reads-from and coherence order are candidate choices rather than
    relations derived uniquely from the event structure.  Their
    well-formedness is stated separately so that partial operational states
    may carry incomplete edge sets later. *)
Module LkmmMemoryRelations.
  Export LkmmExecution.

  Definition edge := (event_id * event_id)%type.
  Definition edge_set := gset edge.

  Definition edge_relation (edges : edge_set) : relation :=
    fun source target => (source, target) ∈ edges.

  Definition rf (edges : edge_set) : relation := edge_relation edges.

  (** The finite edge set stores the complete transitive coherence order,
      rather than only its immediate-successor edges. *)
  Definition co (edges : edge_set) : relation := edge_relation edges.

  (** Read-modify-write pairing is supplied by the candidate execution.
      Successful operations contribute a marked read-to-write edge; failed
      conditional operations contribute only their marked read event. *)
  Definition rmw (edges : edge_set) : relation := edge_relation edges.

  (** From-read is derived from reads-from and coherence order: a read is
      before every write that is coherence-later than its source write. *)
  Definition fr (rf_edges co_edges : edge_set) : relation :=
    rel_seq (rel_inverse (rf rf_edges)) (co co_edges).

  (** Linux v6.18: [com = rf | co | fr]. *)
  Definition com (rf_edges co_edges : edge_set) : relation :=
    rel_union (rf rf_edges) (rel_union (co co_edges) (fr rf_edges co_edges)).

  (** Linux v6.18: [acyclic (po-loc | com) as coherence].  Candidate
      well-formedness remains separate from this consistency constraint. *)
  Definition coherence (E : event_structure) (rf_edges co_edges : edge_set) : Prop :=
    rel_acyclic (rel_union (po_loc E) (com rf_edges co_edges)).

  Definition rf_edge_wf (E : event_structure) (write read : event_id) : Prop :=
    exists write_event read_event val,
      lookup_event E write = Some write_event /\
      lookup_event E read = Some read_event /\
      is_write write_event /\ is_read read_event /\
      same_location E write read /\
      value_of write_event = Some val /\
      value_of read_event = Some val.

  Definition rf_functional (edges : edge_set) : Prop :=
    forall write1 write2 read,
      rf edges write1 read -> rf edges write2 read -> write1 = write2.

  Definition rf_total (E : event_structure) (edges : edge_set) : Prop :=
    forall read read_event,
      lookup_event E read = Some read_event ->
      is_read read_event ->
      exists write, rf edges write read.

  Definition rf_wf (E : event_structure) (edges : edge_set) : Prop :=
    (forall write read, rf edges write read -> rf_edge_wf E write read) /\
    rf_functional edges /\
    rf_total E edges.

  Lemma rf_wf_edge E edges write read :
    rf_wf E edges -> rf edges write read -> rf_edge_wf E write read.
  Proof. intros (Hedges & _ & _) Hrf. by eapply Hedges. Qed.

  Lemma rf_wf_functional E edges :
    rf_wf E edges -> rf_functional edges.
  Proof. intros (_ & Hfunctional & _). exact Hfunctional. Qed.

  Lemma rf_wf_total E edges :
    rf_wf E edges -> rf_total E edges.
  Proof. intros (_ & _ & Htotal). exact Htotal. Qed.

  Lemma rf_wf_endpoints E edges write read :
    rf_wf E edges -> rf edges write read ->
    in_event_structure E write /\ in_event_structure E read.
  Proof.
    intros Hwf Hrf.
    destruct (rf_wf_edge E edges write read Hwf Hrf)
      as (write_event & read_event & val &
        Hwrite & Hread & Hwrite_kind & Hread_kind &
        Hsame_loc & Hwrite_val & Hread_val).
    split; eapply lookup_event_in; eauto.
  Qed.

  Lemma rf_wf_same_location E edges write read :
    rf_wf E edges -> rf edges write read ->
    same_location E write read.
  Proof.
    intros Hwf Hrf.
    destruct (rf_wf_edge E edges write read Hwf Hrf)
      as (write_event & read_event & val &
        Hwrite & Hread & Hwrite_kind & Hread_kind &
        Hsame_loc & Hwrite_val & Hread_val).
    exact Hsame_loc.
  Qed.

  Lemma rf_wf_same_value E edges write read :
    rf_wf E edges -> rf edges write read ->
    exists write_event read_event val,
      lookup_event E write = Some write_event /\
      lookup_event E read = Some read_event /\
      value_of write_event = Some val /\
      value_of read_event = Some val.
  Proof.
    intros Hwf Hrf.
    destruct (rf_wf_edge E edges write read Hwf Hrf)
      as (write_event & read_event & val &
        Hwrite & Hread & Hwrite_kind & Hread_kind &
        Hsame_loc & Hwrite_val & Hread_val).
    exists write_event, read_event, val. done.
  Qed.

  Definition rmw_edge_wf (E : event_structure)
      (read write : event_id) : Prop :=
    exists read_event write_event,
      lookup_event E read = Some read_event /\
      lookup_event E write = Some write_event /\
      is_read read_event /\ is_write write_event /\
      is_rmw_marked read_event /\ is_rmw_marked write_event /\
      po E read write /\
      same_location E read write /\
      same_attribute access_mode_of E read write.

  Definition rmw_functional (edges : edge_set) : Prop :=
    forall read write1 write2,
      rmw edges read write1 -> rmw edges read write2 -> write1 = write2.

  Definition rmw_injective (edges : edge_set) : Prop :=
    forall read1 read2 write,
      rmw edges read1 write -> rmw edges read2 write -> read1 = read2.

  (** Every marked write is the write half of a successful RMW.  Marked
      reads are intentionally not total because a failed conditional RMW
      has no write half. *)
  Definition rmw_write_total (E : event_structure) (edges : edge_set) : Prop :=
    forall write write_event,
      lookup_event E write = Some write_event ->
      is_write write_event -> is_rmw_marked write_event ->
      exists read, rmw edges read write.

  Definition rmw_wf (E : event_structure) (edges : edge_set) : Prop :=
    (forall read write, rmw edges read write -> rmw_edge_wf E read write) /\
    rmw_functional edges /\
    rmw_injective edges /\
    rmw_write_total E edges.

  Lemma rmw_wf_edge E edges read write :
    rmw_wf E edges -> rmw edges read write -> rmw_edge_wf E read write.
  Proof. intros (Hedges & _ & _ & _) Hrmw. by eapply Hedges. Qed.

  Lemma rmw_wf_functional E edges :
    rmw_wf E edges -> rmw_functional edges.
  Proof. intros (_ & Hfunctional & _ & _). exact Hfunctional. Qed.

  Lemma rmw_wf_injective E edges :
    rmw_wf E edges -> rmw_injective edges.
  Proof. intros (_ & _ & Hinjective & _). exact Hinjective. Qed.

  Lemma rmw_wf_write_total E edges :
    rmw_wf E edges -> rmw_write_total E edges.
  Proof. intros (_ & _ & _ & Htotal). exact Htotal. Qed.

  Lemma rmw_wf_endpoints E edges read write :
    rmw_wf E edges -> rmw edges read write ->
    in_event_structure E read /\ in_event_structure E write.
  Proof.
    intros Hwf Hrmw.
    destruct (rmw_wf_edge E edges read write Hwf Hrmw)
      as (read_event & write_event & Hread & Hwrite &
        Hread_kind & Hwrite_kind & Hread_marked & Hwrite_marked &
        Hpo & Hsame_loc & Hsame_mode).
    by eapply po_endpoints.
  Qed.

  Lemma rmw_wf_kinds E edges read write :
    rmw_wf E edges -> rmw edges read write ->
    exists read_event write_event,
      lookup_event E read = Some read_event /\
      lookup_event E write = Some write_event /\
      is_read read_event /\ is_write write_event.
  Proof.
    intros Hwf Hrmw.
    destruct (rmw_wf_edge E edges read write Hwf Hrmw)
      as (read_event & write_event & Hread & Hwrite &
        Hread_kind & Hwrite_kind & Hread_marked & Hwrite_marked &
        Hpo & Hsame_loc & Hsame_mode).
    exists read_event, write_event. done.
  Qed.

  Lemma rmw_wf_marked E edges read write :
    rmw_wf E edges -> rmw edges read write ->
    exists read_event write_event,
      lookup_event E read = Some read_event /\
      lookup_event E write = Some write_event /\
      is_rmw_marked read_event /\ is_rmw_marked write_event.
  Proof.
    intros Hwf Hrmw.
    destruct (rmw_wf_edge E edges read write Hwf Hrmw)
      as (read_event & write_event & Hread & Hwrite &
        Hread_kind & Hwrite_kind & Hread_marked & Hwrite_marked &
        Hpo & Hsame_loc & Hsame_mode).
    exists read_event, write_event. done.
  Qed.

  Lemma rmw_wf_po E edges read write :
    rmw_wf E edges -> rmw edges read write -> po E read write.
  Proof.
    intros Hwf Hrmw.
    destruct (rmw_wf_edge E edges read write Hwf Hrmw)
      as (read_event & write_event & Hread & Hwrite &
        Hread_kind & Hwrite_kind & Hread_marked & Hwrite_marked &
        Hpo & Hsame_loc & Hsame_mode).
    exact Hpo.
  Qed.

  Lemma rmw_wf_same_agent E edges read write :
    rmw_wf E edges -> rmw edges read write -> same_agent E read write.
  Proof.
    intros Hwf Hrmw. apply po_same_agent.
    by eapply rmw_wf_po.
  Qed.

  Lemma rmw_wf_same_location E edges read write :
    rmw_wf E edges -> rmw edges read write ->
    same_location E read write.
  Proof.
    intros Hwf Hrmw.
    destruct (rmw_wf_edge E edges read write Hwf Hrmw)
      as (read_event & write_event & Hread & Hwrite &
        Hread_kind & Hwrite_kind & Hread_marked & Hwrite_marked &
        Hpo & Hsame_loc & Hsame_mode).
    exact Hsame_loc.
  Qed.

  Lemma rmw_wf_same_mode E edges read write :
    rmw_wf E edges -> rmw edges read write ->
    same_attribute access_mode_of E read write.
  Proof.
    intros Hwf Hrmw.
    destruct (rmw_wf_edge E edges read write Hwf Hrmw)
      as (read_event & write_event & Hread & Hwrite &
        Hread_kind & Hwrite_kind & Hread_marked & Hwrite_marked &
        Hpo & Hsame_loc & Hsame_mode).
    exact Hsame_mode.
  Qed.

  Definition location_used (E : event_structure) (loc : location) : Prop :=
    exists eid, event_attribute location_of E eid = Some loc.

  Definition initial_write_at (E : event_structure)
      (loc : location) (write : event_id) : Prop :=
    exists val, lookup_event E write = Some (EInitWrite loc val).

  Definition initial_writes_exist (E : event_structure) : Prop :=
    forall loc, location_used E loc ->
      exists write, initial_write_at E loc write.

  Definition initial_writes_unique (E : event_structure) : Prop :=
    forall loc write1 write2,
      initial_write_at E loc write1 ->
      initial_write_at E loc write2 ->
      write1 = write2.

  Definition co_edge_wf (E : event_structure)
      (write1 write2 : event_id) : Prop :=
    exists write_event1 write_event2,
      lookup_event E write1 = Some write_event1 /\
      lookup_event E write2 = Some write_event2 /\
      is_write write_event1 /\ is_write write_event2 /\
      same_location E write1 write2.

  Definition fr_edge_wf (E : event_structure) (read write : event_id) : Prop :=
    exists read_event write_event,
      lookup_event E read = Some read_event /\
      lookup_event E write = Some write_event /\
      is_read read_event /\ is_write write_event /\
      same_location E read write.

  Definition co_irreflexive (edges : edge_set) : Prop :=
    forall write, ~ co edges write write.

  Definition co_transitive (edges : edge_set) : Prop :=
    forall write1 write2 write3,
      co edges write1 write2 -> co edges write2 write3 ->
      co edges write1 write3.

  Definition co_total (E : event_structure) (edges : edge_set) : Prop :=
    forall write1 write2 write_event1 write_event2,
      lookup_event E write1 = Some write_event1 ->
      lookup_event E write2 = Some write_event2 ->
      is_write write_event1 -> is_write write_event2 ->
      same_location E write1 write2 ->
      write1 <> write2 ->
      co edges write1 write2 \/ co edges write2 write1.

  Definition co_initial_first (E : event_structure) (edges : edge_set) : Prop :=
    forall initial write loc write_event,
      initial_write_at E loc initial ->
      lookup_event E write = Some write_event ->
      is_write write_event ->
      same_location E initial write ->
      initial <> write ->
      co edges initial write.

  Definition co_wf (E : event_structure) (edges : edge_set) : Prop :=
    (forall write1 write2, co edges write1 write2 -> co_edge_wf E write1 write2) /\
      co_irreflexive edges /\
      co_transitive edges /\
      co_total E edges /\
      initial_writes_exist E /\
      initial_writes_unique E /\
      co_initial_first E edges.

  Lemma co_wf_edge E edges write1 write2 :
    co_wf E edges -> co edges write1 write2 ->
    co_edge_wf E write1 write2.
  Proof. intros (Hedges & _ & _ & _ & _ & _ & _) Hco. by eapply Hedges. Qed.

  Lemma co_wf_irreflexive E edges :
    co_wf E edges -> co_irreflexive edges.
  Proof. intros (_ & Hirreflexive & _ & _ & _ & _ & _). exact Hirreflexive. Qed.

  Lemma co_wf_transitive E edges :
    co_wf E edges -> co_transitive edges.
  Proof. intros (_ & _ & Htransitive & _ & _ & _ & _). exact Htransitive. Qed.

  Lemma co_wf_total E edges :
    co_wf E edges -> co_total E edges.
  Proof. intros (_ & _ & _ & Htotal & _ & _ & _). exact Htotal. Qed.

  Lemma co_wf_initial_exists E edges :
    co_wf E edges -> initial_writes_exist E.
  Proof. intros (_ & _ & _ & _ & Hexists & _ & _). exact Hexists. Qed.

  Lemma co_wf_initial_unique E edges :
    co_wf E edges -> initial_writes_unique E.
  Proof. intros (_ & _ & _ & _ & _ & Hunique & _). exact Hunique. Qed.

  Lemma co_wf_initial_first E edges :
    co_wf E edges -> co_initial_first E edges.
  Proof. intros (_ & _ & _ & _ & _ & _ & Hfirst). exact Hfirst. Qed.

  Lemma co_wf_endpoints E edges write1 write2 :
    co_wf E edges -> co edges write1 write2 ->
    in_event_structure E write1 /\ in_event_structure E write2.
  Proof.
    intros Hwf Hco.
    destruct (co_wf_edge E edges write1 write2 Hwf Hco)
      as (write_event1 & write_event2 &
        Hwrite1 & Hwrite2 & Hkind1 & Hkind2 & Hsame_loc).
    split; eapply lookup_event_in; eauto.
  Qed.

  Lemma co_wf_same_location E edges write1 write2 :
    co_wf E edges -> co edges write1 write2 ->
    same_location E write1 write2.
  Proof.
    intros Hwf Hco.
    destruct (co_wf_edge E edges write1 write2 Hwf Hco)
      as (write_event1 & write_event2 &
        Hwrite1 & Hwrite2 & Hkind1 & Hkind2 & Hsame_loc).
    exact Hsame_loc.
  Qed.

  Lemma fr_wf_edge E rf_edges co_edges read write :
    rf_wf E rf_edges -> co_wf E co_edges ->
    fr rf_edges co_edges read write -> fr_edge_wf E read write.
  Proof.
    intros Hrf_wf Hco_wf Hfr.
    unfold fr, rel_seq in Hfr.
    destruct Hfr as (source & Hrf & Hco).
    unfold rel_inverse in Hrf.
    destruct (rf_wf_edge E rf_edges source read Hrf_wf Hrf)
      as (source_event & read_event & val &
        Hsource & Hread & Hsource_kind & Hread_kind &
        Hsource_read_loc & Hsource_val & Hread_val).
    destruct (co_wf_edge E co_edges source write Hco_wf Hco)
      as (source_event' & write_event &
        Hsource' & Hwrite & Hsource_kind' & Hwrite_kind &
        Hsource_write_loc).
    exists read_event, write_event.
    repeat split; try done.
    eapply same_location_transitive.
    - by apply same_location_symmetric.
    - exact Hsource_write_loc.
  Qed.

  Lemma fr_wf_endpoints E rf_edges co_edges read write :
    rf_wf E rf_edges -> co_wf E co_edges ->
    fr rf_edges co_edges read write ->
    in_event_structure E read /\ in_event_structure E write.
  Proof.
    intros Hrf_wf Hco_wf Hfr.
    destruct (fr_wf_edge E rf_edges co_edges read write
      Hrf_wf Hco_wf Hfr)
      as (read_event & write_event &
        Hread & Hwrite & Hread_kind & Hwrite_kind & Hsame_loc).
    split; eapply lookup_event_in; eauto.
  Qed.

  Lemma fr_wf_kinds E rf_edges co_edges read write :
    rf_wf E rf_edges -> co_wf E co_edges ->
    fr rf_edges co_edges read write ->
    exists read_event write_event,
      lookup_event E read = Some read_event /\
      lookup_event E write = Some write_event /\
      is_read read_event /\ is_write write_event.
  Proof.
    intros Hrf_wf Hco_wf Hfr.
    destruct (fr_wf_edge E rf_edges co_edges read write
      Hrf_wf Hco_wf Hfr)
      as (read_event & write_event &
        Hread & Hwrite & Hread_kind & Hwrite_kind & Hsame_loc).
    exists read_event, write_event. done.
  Qed.

  Lemma fr_wf_same_location E rf_edges co_edges read write :
    rf_wf E rf_edges -> co_wf E co_edges ->
    fr rf_edges co_edges read write ->
    same_location E read write.
  Proof.
    intros Hrf_wf Hco_wf Hfr.
    destruct (fr_wf_edge E rf_edges co_edges read write
      Hrf_wf Hco_wf Hfr)
      as (read_event & write_event &
        Hread & Hwrite & Hread_kind & Hwrite_kind & Hsame_loc).
    exact Hsame_loc.
  Qed.

  Module ReadsFromTests.
    Definition init_write : event := EInitWrite 0 0%Z.
    Definition once_read : event := EAgent 0 0 (LMemory AccessRead AccessOnce NotRmw 0 0%Z).
    Definition second_write : event := EAgent 1 0 (LMemory AccessWrite AccessOnce NotRmw 0 0%Z).

    Definition sample_events : event_structure :=
      <[1 := once_read]> ({[0 := init_write]} : event_structure).

    Definition sample_rf : edge_set := {[(0, 1)]}.

    Example sample_rf_wf : rf_wf sample_events sample_rf.
    Proof.
      split.
      - intros write read Hrf.
        unfold rf, edge_relation, sample_rf in Hrf.
        assert (write = 0 /\ read = 1) as [-> ->] by set_solver.
        exists init_write, once_read, 0%Z.
        repeat split; try reflexivity.
        exists 0. split; reflexivity.
      - split.
        + intros write1 write2 read Hrf1 Hrf2.
          unfold rf, edge_relation, sample_rf in Hrf1, Hrf2.
          set_solver.
        + intros read read_event Hlookup Hread.
          unfold lookup_event, sample_events in Hlookup.
          apply lookup_insert_Some in Hlookup.
          destruct Hlookup as [[Hread_id Hread_event] | [Hne Hlookup]].
          * subst read. subst read_event.
            exists 0. unfold rf, edge_relation, sample_rf. set_solver.
          * apply lookup_singleton_Some in Hlookup as [Hread_id Hread_event].
            subst read. subst read_event.
            unfold is_read, init_write, access_kind_of in Hread.
            discriminate Hread.
    Qed.

    Definition two_source_events : event_structure := <[2 := second_write]> sample_events.

    Definition two_source_rf : edge_set := {[(0, 1); (2, 1)]}.

    Example two_sources_are_not_well_formed :
      ~ rf_wf two_source_events two_source_rf.
    Proof.
      intros Hwf.
      pose proof (rf_wf_functional two_source_events two_source_rf Hwf)
        as Hfunctional.
      assert (0 = 2) as Heq.
      { eapply Hfunctional with (read := 1); unfold rf, edge_relation, two_source_rf; set_solver. }
      lia.
    Qed.
  End ReadsFromTests.

  Module ReadModifyWriteTests.
    Definition marked_read : event :=
      EAgent 0 0 (LMemory AccessRead AccessMb RmwMarked 0 7%Z).
    Definition marked_write : event :=
      EAgent 0 1 (LMemory AccessWrite AccessMb RmwMarked 0 8%Z).

    Definition sample_events : event_structure :=
      <[1 := marked_write]> ({[0 := marked_read]} : event_structure).

    Definition sample_rmw : edge_set := {[(0, 1)]}.

    Local Lemma sample_lookup_cases eid ev :
      lookup_event sample_events eid = Some ev ->
      (eid = 0 /\ ev = marked_read) \/
      (eid = 1 /\ ev = marked_write).
    Proof.
      intros Hlookup.
      unfold lookup_event, sample_events in Hlookup.
      apply lookup_insert_Some in Hlookup.
      destruct Hlookup as [[-> Hevent] | [Hne Hlookup]].
      - right. naive_solver.
      - apply lookup_singleton_Some in Hlookup.
        left. naive_solver.
    Qed.

    Local Lemma singleton_rmw_edge read write :
      rmw ({[(read, write)]} : edge_set) read write.
    Proof. unfold rmw, edge_relation. set_solver. Qed.

    Example successful_rmw_is_well_formed :
      rmw_wf sample_events sample_rmw.
    Proof.
      repeat split.
      - intros read write Hrmw.
        unfold rmw, edge_relation, sample_rmw in Hrmw.
        assert (read = 0 /\ write = 1) as [-> ->] by set_solver.
        exists marked_read, marked_write.
        repeat split; try reflexivity.
        + exists 0, 0, 1,
            (LMemory AccessRead AccessMb RmwMarked 0 7%Z),
            (LMemory AccessWrite AccessMb RmwMarked 0 8%Z).
          repeat split; try reflexivity. lia.
        + exists 0. split; reflexivity.
        + exists AccessMb. split; reflexivity.
      - intros read write1 write2 Hrmw1 Hrmw2.
        unfold rmw, edge_relation, sample_rmw in Hrmw1, Hrmw2.
        set_solver.
      - intros read1 read2 write Hrmw1 Hrmw2.
        unfold rmw, edge_relation, sample_rmw in Hrmw1, Hrmw2.
        set_solver.
      - intros write write_event Hlookup Hwrite Hmarked.
        destruct (sample_lookup_cases write write_event Hlookup)
          as [(-> & ->) | (-> & ->)].
        + discriminate Hwrite.
        + exists 0. unfold rmw, edge_relation, sample_rmw. set_solver.
    Qed.

    Definition failed_events : event_structure :=
      ({[0 := marked_read]} : event_structure).

    Example failed_rmw_read_may_be_unpaired :
      rmw_wf failed_events (∅ : edge_set).
    Proof.
      repeat split.
      - intros read write Hrmw.
        unfold rmw, edge_relation in Hrmw. set_solver.
      - intros read write1 write2 Hrmw1 Hrmw2.
        unfold rmw, edge_relation in Hrmw1. set_solver.
      - intros read1 read2 write Hrmw1 Hrmw2.
        unfold rmw, edge_relation in Hrmw1. set_solver.
      - intros write write_event Hlookup Hwrite Hmarked.
        unfold lookup_event, failed_events in Hlookup.
        apply lookup_singleton_Some in Hlookup as [Hwrite_id Hevent].
        subst write. subst write_event.
        discriminate Hwrite.
    Qed.

    Definition write_only_events : event_structure :=
      ({[1 := marked_write]} : event_structure).

    Example marked_write_must_be_paired :
      ~ rmw_wf write_only_events (∅ : edge_set).
    Proof.
      intros Hwf.
      pose proof (rmw_wf_write_total write_only_events
        (∅ : edge_set) Hwf) as Htotal.
      destruct (Htotal 1 marked_write) as (read & Hrmw).
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - unfold rmw, edge_relation in Hrmw. set_solver.
    Qed.

    Example reversed_kinds_are_not_well_formed :
      ~ rmw_wf sample_events ({[(1, 0)]} : edge_set).
    Proof.
      intros Hwf.
      destruct (rmw_wf_kinds sample_events ({[(1, 0)]} : edge_set)
        1 0 Hwf (singleton_rmw_edge 1 0))
        as (read_event & write_event & Hread & Hwrite &
          Hread_kind & Hwrite_kind).
      assert (read_event = marked_write) as ->.
      { change (Some marked_write = Some read_event) in Hread. congruence. }
      discriminate Hread_kind.
    Qed.

    Definition unmarked_read : event :=
      EAgent 0 0 (LMemory AccessRead AccessMb NotRmw 0 7%Z).
    Definition unmarked_source_events : event_structure :=
      <[1 := marked_write]> ({[0 := unmarked_read]} : event_structure).

    Example unmarked_read_is_not_a_valid_rmw_source :
      ~ rmw_wf unmarked_source_events ({[(0, 1)]} : edge_set).
    Proof.
      intros Hwf.
      destruct (rmw_wf_marked unmarked_source_events
        ({[(0, 1)]} : edge_set) 0 1 Hwf (singleton_rmw_edge 0 1))
        as (read_event & write_event & Hread & Hwrite &
          Hread_marked & Hwrite_marked).
      assert (read_event = unmarked_read) as ->.
      { change (Some unmarked_read = Some read_event) in Hread. congruence. }
      discriminate Hread_marked.
    Qed.

    Definition unmarked_write : event :=
      EAgent 0 1 (LMemory AccessWrite AccessMb NotRmw 0 8%Z).
    Definition unmarked_target_events : event_structure :=
      <[1 := unmarked_write]> ({[0 := marked_read]} : event_structure).

    Example unmarked_write_is_not_a_valid_rmw_target :
      ~ rmw_wf unmarked_target_events ({[(0, 1)]} : edge_set).
    Proof.
      intros Hwf.
      destruct (rmw_wf_marked unmarked_target_events
        ({[(0, 1)]} : edge_set) 0 1 Hwf (singleton_rmw_edge 0 1))
        as (read_event & write_event & Hread & Hwrite &
          Hread_marked & Hwrite_marked).
      assert (write_event = unmarked_write) as ->.
      { change (Some unmarked_write = Some write_event) in Hwrite. congruence. }
      discriminate Hwrite_marked.
    Qed.

    Definition other_location_write : event :=
      EAgent 0 1 (LMemory AccessWrite AccessMb RmwMarked 1 8%Z).
    Definition different_location_events : event_structure :=
      <[1 := other_location_write]> ({[0 := marked_read]} : event_structure).

    Example different_locations_are_not_well_formed :
      ~ rmw_wf different_location_events ({[(0, 1)]} : edge_set).
    Proof.
      intros Hwf.
      pose proof (rmw_wf_same_location different_location_events
        ({[(0, 1)]} : edge_set) 0 1 Hwf (singleton_rmw_edge 0 1))
        as (loc & Hread_loc & Hwrite_loc).
      change (Some 0 = Some loc) in Hread_loc.
      change (Some 1 = Some loc) in Hwrite_loc.
      congruence.
    Qed.

    Definition other_mode_write : event :=
      EAgent 0 1 (LMemory AccessWrite AccessOnce RmwMarked 0 8%Z).
    Definition different_mode_events : event_structure :=
      <[1 := other_mode_write]> ({[0 := marked_read]} : event_structure).

    Example different_modes_are_not_well_formed :
      ~ rmw_wf different_mode_events ({[(0, 1)]} : edge_set).
    Proof.
      intros Hwf.
      pose proof (rmw_wf_same_mode different_mode_events
        ({[(0, 1)]} : edge_set) 0 1 Hwf (singleton_rmw_edge 0 1))
        as (mode & Hread_mode & Hwrite_mode).
      change (Some AccessMb = Some mode) in Hread_mode.
      change (Some AccessOnce = Some mode) in Hwrite_mode.
      congruence.
    Qed.

    Definition other_agent_write : event :=
      EAgent 1 1 (LMemory AccessWrite AccessMb RmwMarked 0 8%Z).
    Definition different_agent_events : event_structure :=
      <[1 := other_agent_write]> ({[0 := marked_read]} : event_structure).

    Example different_agents_are_not_well_formed :
      ~ rmw_wf different_agent_events ({[(0, 1)]} : edge_set).
    Proof.
      intros Hwf.
      pose proof (rmw_wf_po different_agent_events
        ({[(0, 1)]} : edge_set) 0 1 Hwf (singleton_rmw_edge 0 1))
        as (agent & index1 & index2 & label1 & label2 &
          Hread & Hwrite & Hlt).
      change (Some marked_read = Some (EAgent agent index1 label1)) in Hread.
      change (Some other_agent_write = Some (EAgent agent index2 label2)) in Hwrite.
      unfold marked_read, other_agent_write in Hread, Hwrite.
      congruence.
    Qed.

    Definition late_read : event :=
      EAgent 0 2 (LMemory AccessRead AccessMb RmwMarked 0 7%Z).
    Definition reversed_po_events : event_structure :=
      <[1 := marked_write]> ({[0 := late_read]} : event_structure).

    Example reversed_program_order_is_not_well_formed :
      ~ rmw_wf reversed_po_events ({[(0, 1)]} : edge_set).
    Proof.
      intros Hwf.
      pose proof (rmw_wf_po reversed_po_events
        ({[(0, 1)]} : edge_set) 0 1 Hwf (singleton_rmw_edge 0 1))
        as (agent & index1 & index2 & label1 & label2 &
          Hread & Hwrite & Hlt).
      change (Some late_read = Some (EAgent agent index1 label1)) in Hread.
      change (Some marked_write = Some (EAgent agent index2 label2)) in Hwrite.
      unfold late_read in Hread. unfold marked_write in Hwrite.
      assert (index1 = 2) as -> by congruence.
      assert (index2 = 1) as -> by congruence.
      lia.
    Qed.

    Definition second_write : event :=
      EAgent 0 2 (LMemory AccessWrite AccessMb RmwMarked 0 9%Z).
    Definition two_write_events : event_structure :=
      <[2 := second_write]> sample_events.
    Definition one_read_two_writes : edge_set := {[(0, 1); (0, 2)]}.

    Example one_read_cannot_pair_with_two_writes :
      ~ rmw_wf two_write_events one_read_two_writes.
    Proof.
      intros Hwf.
      pose proof (rmw_wf_functional two_write_events
        one_read_two_writes Hwf) as Hfunctional.
      assert (1 = 2) as Heq.
      { eapply Hfunctional with (read := 0);
          unfold rmw, edge_relation, one_read_two_writes; set_solver. }
      lia.
    Qed.

    Definition second_read : event :=
      EAgent 0 1 (LMemory AccessRead AccessMb RmwMarked 0 7%Z).
    Definition late_write : event :=
      EAgent 0 2 (LMemory AccessWrite AccessMb RmwMarked 0 8%Z).
    Definition two_read_events : event_structure :=
      <[2 := second_read]>
        (<[1 := late_write]> ({[0 := marked_read]} : event_structure)).
    Definition two_reads_one_write : edge_set := {[(0, 1); (2, 1)]}.

    Example one_write_cannot_pair_with_two_reads :
      ~ rmw_wf two_read_events two_reads_one_write.
    Proof.
      intros Hwf.
      pose proof (rmw_wf_injective two_read_events
        two_reads_one_write Hwf) as Hinjective.
      assert (0 = 2) as Heq.
      { eapply Hinjective with (write := 1);
          unfold rmw, edge_relation, two_reads_one_write; set_solver. }
      lia.
    Qed.
  End ReadModifyWriteTests.

  Module CoherenceOrderTests.
    Definition init_write : event := EInitWrite 0 0%Z.
    Definition first_write : event :=
      EAgent 0 0 (LMemory AccessWrite AccessOnce NotRmw 0 1%Z).
    Definition second_write : event :=
      EAgent 1 0 (LMemory AccessWrite AccessOnce NotRmw 0 2%Z).

    Definition sample_events : event_structure :=
      <[2 := second_write]>
        (<[1 := first_write]> ({[0 := init_write]} : event_structure)).

    Definition sample_co : edge_set := {[(0, 1); (0, 2); (1, 2)]}.

    Local Lemma sample_lookup_cases eid ev :
      lookup_event sample_events eid = Some ev ->
      (eid = 0 /\ ev = init_write) \/
      (eid = 1 /\ ev = first_write) \/
      (eid = 2 /\ ev = second_write).
    Proof.
      intros Hlookup.
      unfold lookup_event, sample_events in Hlookup.
      apply lookup_insert_Some in Hlookup.
      destruct Hlookup as [[-> Hevent] | [Hne Hlookup]].
      - right. right. naive_solver.
      - apply lookup_insert_Some in Hlookup.
        destruct Hlookup as [[-> Hevent] | [Hne' Hlookup]].
        + right. left. naive_solver.
        + apply lookup_singleton_Some in Hlookup.
          left. naive_solver.
    Qed.

    Example sample_co_wf : co_wf sample_events sample_co.
    Proof.
      repeat split.
      - intros write1 write2 Hco.
        unfold co, edge_relation, sample_co in Hco.
        assert ((write1 = 0 /\ write2 = 1) \/
          (write1 = 0 /\ write2 = 2) \/
          (write1 = 1 /\ write2 = 2)) as
            [(-> & ->) | [(-> & ->) | (-> & ->)]] by set_solver.
        + exists init_write, first_write.
          repeat split; try reflexivity.
          exists 0. split; reflexivity.
        + exists init_write, second_write.
          repeat split; try reflexivity.
          exists 0. split; reflexivity.
        + exists first_write, second_write.
          repeat split; try reflexivity.
          exists 0. split; reflexivity.
      - intros write Hco.
        unfold co, edge_relation, sample_co in Hco. set_solver.
      - intros write1 write2 write3 Hco12 Hco23.
        unfold co, edge_relation, sample_co in Hco12, Hco23.
        unfold co, edge_relation, sample_co. set_solver.
      - intros write1 write2 write_event1 write_event2
          Hlookup1 Hlookup2 Hkind1 Hkind2 Hsame_loc Hneq.
        destruct (sample_lookup_cases write1 write_event1 Hlookup1)
          as [(-> & ->) | [(-> & ->) | (-> & ->)]];
        destruct (sample_lookup_cases write2 write_event2 Hlookup2)
          as [(-> & ->) | [(-> & ->) | (-> & ->)]];
        unfold co, edge_relation, sample_co; set_solver.
      - intros loc (eid & Hloc).
        apply event_attribute_Some in Hloc as (ev & Hlookup & Hloc).
        destruct (sample_lookup_cases eid ev Hlookup)
          as [(-> & ->) | [(-> & ->) | (-> & ->)]];
        simpl in Hloc; assert (loc = 0) as -> by congruence;
        exists 0, 0%Z; reflexivity.
      - intros loc write1 write2
          (val1 & Hlookup1) (val2 & Hlookup2).
        destruct (sample_lookup_cases write1 (EInitWrite loc val1) Hlookup1)
          as [(-> & Hevent1) | [(-> & Hevent1) | (-> & Hevent1)]];
        destruct (sample_lookup_cases write2 (EInitWrite loc val2) Hlookup2)
          as [(-> & Hevent2) | [(-> & Hevent2) | (-> & Hevent2)]];
        try discriminate; done.
      - intros initial write loc write_event
          (val & Hinitial) Hwrite Hkind Hsame_loc Hneq.
        destruct (sample_lookup_cases initial (EInitWrite loc val) Hinitial)
          as [(-> & Hevent) | [(-> & Hevent) | (-> & Hevent)]];
          try discriminate.
        destruct (sample_lookup_cases write write_event Hwrite)
          as [(-> & ->) | [(-> & ->) | (-> & ->)]];
        unfold co, edge_relation, sample_co; set_solver.
    Qed.

    Definition cyclic_co : edge_set :=
      {[(0, 1); (0, 2); (1, 2); (2, 1)]}.

    Example coherence_cycle_is_not_well_formed :
      ~ co_wf sample_events cyclic_co.
    Proof.
      intros Hwf.
      pose proof (co_wf_irreflexive sample_events cyclic_co Hwf)
        as Hirreflexive.
      pose proof (co_wf_transitive sample_events cyclic_co Hwf)
        as Htransitive.
      apply (Hirreflexive 1).
      eapply Htransitive with (write2 := 2);
        unfold co, edge_relation, cyclic_co; set_solver.
    Qed.

    Definition missing_initial_events : event_structure :=
      ({[1 := first_write]} : event_structure).

    Example missing_initial_write_is_not_well_formed :
      ~ co_wf missing_initial_events (∅ : edge_set).
    Proof.
      intros Hwf.
      pose proof (co_wf_initial_exists missing_initial_events
        (∅ : edge_set) Hwf) as Hexists.
      assert (location_used missing_initial_events 0) as Hused.
      { exists 1. reflexivity. }
      destruct (Hexists 0 Hused) as (initial & val & Hlookup).
      unfold lookup_event, missing_initial_events in Hlookup.
      apply lookup_singleton_Some in Hlookup as [Heid Hevent].
      discriminate Hevent.
    Qed.

    Definition duplicate_initial_events : event_structure :=
      <[3 := EInitWrite 0 7%Z]>
        ({[0 := init_write]} : event_structure).

    Example duplicate_initial_writes_are_not_well_formed :
      ~ co_wf duplicate_initial_events (∅ : edge_set).
    Proof.
      intros Hwf.
      pose proof (co_wf_initial_unique duplicate_initial_events
        (∅ : edge_set) Hwf) as Hunique.
      assert (0 = 3) as Heq.
      { eapply Hunique with (loc := 0).
        - exists 0%Z. reflexivity.
        - exists 7%Z. reflexivity. }
      lia.
    Qed.

    Definition late_initial_events : event_structure :=
      <[1 := first_write]> ({[0 := init_write]} : event_structure).

    Definition late_initial_co : edge_set := {[(1, 0)]}.

    Example initial_write_not_first_is_not_well_formed :
      ~ co_wf late_initial_events late_initial_co.
    Proof.
      intros Hwf.
      pose proof (co_wf_initial_first late_initial_events
        late_initial_co Hwf) as Hfirst.
      assert (co late_initial_co 0 1) as Hco.
      { eapply Hfirst with (loc := 0) (write_event := first_write).
        - exists 0%Z. reflexivity.
        - reflexivity.
        - reflexivity.
        - exists 0. split; reflexivity.
        - lia. }
      unfold co, edge_relation, late_initial_co in Hco. set_solver.
    Qed.
  End CoherenceOrderTests.

  Module FromReadTests.
    (** Writes [0], [1], and [2] form a coherence chain.  Read [3] reads
        from [0], while read [4] reads from [1]. *)
    Definition sample_rf : edge_set := {[(0, 3); (1, 4)]}.
    Definition sample_co : edge_set := {[(0, 1); (0, 2); (1, 2)]}.

    Example read_is_fr_before_next_write :
      fr sample_rf sample_co 3 1.
    Proof.
      unfold fr, rel_seq, rel_inverse, rf, co, edge_relation,
        sample_rf, sample_co. set_solver.
    Qed.

    Example read_is_fr_before_indirect_later_write :
      fr sample_rf sample_co 3 2.
    Proof.
      unfold fr, rel_seq, rel_inverse, rf, co, edge_relation,
        sample_rf, sample_co. set_solver.
    Qed.

    Example read_from_middle_is_fr_before_later_write :
      fr sample_rf sample_co 4 2.
    Proof.
      unfold fr, rel_seq, rel_inverse, rf, co, edge_relation,
        sample_rf, sample_co. set_solver.
    Qed.

    Example read_is_not_fr_before_source_write :
      ~ fr sample_rf sample_co 3 0.
    Proof.
      unfold fr, rel_seq, rel_inverse, rf, co, edge_relation,
        sample_rf, sample_co. set_solver.
    Qed.

    Example read_is_not_fr_before_coherence_earlier_write :
      ~ fr sample_rf sample_co 4 0.
    Proof.
      unfold fr, rel_seq, rel_inverse, rf, co, edge_relation,
        sample_rf, sample_co. set_solver.
    Qed.
  End FromReadTests.

  Module BaseCoherenceTests.
    Definition first_write : event :=
      EAgent 0 0 (LMemory AccessWrite AccessOnce NotRmw 0 1%Z).
    Definition second_write : event :=
      EAgent 0 1 (LMemory AccessWrite AccessOnce NotRmw 0 2%Z).

    Definition sample_events : event_structure :=
      <[2 := second_write]> ({[1 := first_write]} : event_structure).

    Example empty_execution_is_coherent :
      coherence empty_event_structure (∅ : edge_set) (∅ : edge_set).
    Proof.
      unfold coherence, rel_acyclic, rel_irreflexive.
      intros eid Hcycle.
      induction Hcycle as [source target Hedge |
        source middle target Hleft IHleft Hright IHright].
      - destruct Hedge as [Hpo_loc | Hcom].
        + destruct Hpo_loc as [Hpo Hsame_loc].
          destruct Hpo as (agent & index1 & index2 & label1 & label2 &
            Hlookup1 & Hlookup2 & Hlt).
          unfold lookup_event, empty_event_structure in Hlookup1.
          discriminate Hlookup1.
        + unfold com, rel_union in Hcom.
          destruct Hcom as [Hrf | [Hco | Hfr]].
          * unfold rf, edge_relation in Hrf. set_solver.
          * unfold co, edge_relation in Hco. set_solver.
          * unfold fr, rel_seq in Hfr.
            destruct Hfr as (write & Hrf & Hco).
            unfold rel_inverse, rf, edge_relation in Hrf. set_solver.
      - exact IHleft.
    Qed.

    Definition reversed_co : edge_set := {[(2, 1)]}.

    Example reversed_co_creates_a_coherence_cycle :
      ~ coherence sample_events (∅ : edge_set) reversed_co.
    Proof.
      intros Hcoherence.
      unfold coherence, rel_acyclic, rel_irreflexive in Hcoherence.
      apply (Hcoherence 1).
      eapply t_trans with (y := 2).
      - apply t_step. left. split.
        + exists 0, 0, 1,
            (LMemory AccessWrite AccessOnce NotRmw 0 1%Z),
            (LMemory AccessWrite AccessOnce NotRmw 0 2%Z).
          repeat split; try reflexivity. lia.
        + exists 0. split; reflexivity.
      - apply t_step. right. unfold com, rel_union. right. left.
        unfold co, edge_relation, reversed_co. set_solver.
    Qed.
  End BaseCoherenceTests.

End LkmmMemoryRelations.
