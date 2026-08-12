From Stdlib Require Import ZArith.
From stdpp Require Import gmap tactics.
From iris_lkmm.lkmm Require Import execution.

(** Finite candidate relations for the relational LKMM model.

    Reads-from is a candidate choice rather than a relation derived uniquely
    from the event structure.  Its well-formedness is stated separately so
    that partial operational states may carry incomplete edge sets later. *)
Module LkmmMemoryRelations.
  Export LkmmExecution.

  Definition edge := (event_id * event_id)%type.
  Definition edge_set := gset edge.

  Definition edge_relation (edges : edge_set) : relation :=
    fun source target => (source, target) ∈ edges.

  Definition rf (edges : edge_set) : relation := edge_relation edges.

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

End LkmmMemoryRelations.
