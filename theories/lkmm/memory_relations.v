From Stdlib Require Import ZArith.
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

  Definition rf_edge_wf (E : event_structure) (write read : event_id) : Prop :=
    exists write_event read_event loc val,
      lookup_event E write = Some write_event /\
      lookup_event E read = Some read_event /\
      is_write write_event /\ is_read read_event /\
      location_of write_event = Some loc /\
      location_of read_event = Some loc /\
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
      as (write_event & read_event & loc & val &
        Hwrite & Hread & Hwrite_kind & Hread_kind &
        Hwrite_loc & Hread_loc & Hwrite_val & Hread_val).
    split; eapply lookup_event_in; eauto.
  Qed.

  Lemma rf_wf_same_location E edges write read :
    rf_wf E edges -> rf edges write read ->
    exists write_event read_event loc,
      lookup_event E write = Some write_event /\
      lookup_event E read = Some read_event /\
      location_of write_event = Some loc /\
      location_of read_event = Some loc.
  Proof.
    intros Hwf Hrf.
    destruct (rf_wf_edge E edges write read Hwf Hrf)
      as (write_event & read_event & loc & val &
        Hwrite & Hread & Hwrite_kind & Hread_kind &
        Hwrite_loc & Hread_loc & Hwrite_val & Hread_val).
    exists write_event, read_event, loc. done.
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
      as (write_event & read_event & loc & val &
        Hwrite & Hread & Hwrite_kind & Hread_kind &
        Hwrite_loc & Hread_loc & Hwrite_val & Hread_val).
    exists write_event, read_event, val. done.
  Qed.

  Definition location_used (E : event_structure) (loc : location) : Prop :=
    exists eid ev,
      lookup_event E eid = Some ev /\ location_of ev = Some loc.

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
    exists write_event1 write_event2 loc,
      lookup_event E write1 = Some write_event1 /\
      lookup_event E write2 = Some write_event2 /\
      is_write write_event1 /\ is_write write_event2 /\
      location_of write_event1 = Some loc /\
      location_of write_event2 = Some loc.

  Definition co_irreflexive (edges : edge_set) : Prop :=
    forall write, ~ co edges write write.

  Definition co_transitive (edges : edge_set) : Prop :=
    forall write1 write2 write3,
      co edges write1 write2 -> co edges write2 write3 ->
      co edges write1 write3.

  Definition co_total (E : event_structure) (edges : edge_set) : Prop :=
    forall write1 write2 write_event1 write_event2 loc,
      lookup_event E write1 = Some write_event1 ->
      lookup_event E write2 = Some write_event2 ->
      is_write write_event1 -> is_write write_event2 ->
      location_of write_event1 = Some loc ->
      location_of write_event2 = Some loc ->
      write1 <> write2 ->
      co edges write1 write2 \/ co edges write2 write1.

  Definition co_initial_first (E : event_structure)
      (edges : edge_set) : Prop :=
    forall initial write loc write_event,
      initial_write_at E loc initial ->
      lookup_event E write = Some write_event ->
      is_write write_event ->
      location_of write_event = Some loc ->
      initial <> write ->
      co edges initial write.

  Definition co_wf (E : event_structure) (edges : edge_set) : Prop :=
    (forall write1 write2, co edges write1 write2 ->
      co_edge_wf E write1 write2) /\
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
      as (write_event1 & write_event2 & loc &
        Hwrite1 & Hwrite2 & Hkind1 & Hkind2 & Hloc1 & Hloc2).
    split; eapply lookup_event_in; eauto.
  Qed.

  Lemma co_wf_same_location E edges write1 write2 :
    co_wf E edges -> co edges write1 write2 ->
    exists write_event1 write_event2 loc,
      lookup_event E write1 = Some write_event1 /\
      lookup_event E write2 = Some write_event2 /\
      is_write write_event1 /\ is_write write_event2 /\
      location_of write_event1 = Some loc /\
      location_of write_event2 = Some loc.
  Proof. intros Hwf Hco. by eapply co_wf_edge. Qed.

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
        exists init_write, once_read, 0, 0%Z.
        repeat split; reflexivity.
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
        + exists init_write, first_write, 0.
          repeat split; reflexivity.
        + exists init_write, second_write, 0.
          repeat split; reflexivity.
        + exists first_write, second_write, 0.
          repeat split; reflexivity.
      - intros write Hco.
        unfold co, edge_relation, sample_co in Hco. set_solver.
      - intros write1 write2 write3 Hco12 Hco23.
        unfold co, edge_relation, sample_co in Hco12, Hco23.
        unfold co, edge_relation, sample_co. set_solver.
      - intros write1 write2 write_event1 write_event2 loc
          Hlookup1 Hlookup2 Hkind1 Hkind2 Hloc1 Hloc2 Hneq.
        destruct (sample_lookup_cases write1 write_event1 Hlookup1)
          as [(-> & ->) | [(-> & ->) | (-> & ->)]];
        destruct (sample_lookup_cases write2 write_event2 Hlookup2)
          as [(-> & ->) | [(-> & ->) | (-> & ->)]];
        unfold co, edge_relation, sample_co; set_solver.
      - intros loc (eid & ev & Hlookup & Hloc).
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
          (val & Hinitial) Hwrite Hkind Hloc Hneq.
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
      { exists 1, first_write. split; reflexivity. }
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
        - reflexivity.
        - lia. }
      unfold co, edge_relation, late_initial_co in Hco. set_solver.
    Qed.
  End CoherenceOrderTests.

End LkmmMemoryRelations.
