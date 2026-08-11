From Stdlib Require Import ZArith.
From stdpp Require Import fin_map_dom gmap tactics.
From iris_lkmm.lkmm Require Import prelude events.

(** Raw finite event structures for the relational LKMM model.

    Event identifiers are external keys into the finite map.  Structural
    well-formedness is kept as a separate predicate so that later operational
    states may contain partial structures without carrying proof fields. *)
Module LkmmExecution.
  Export LkmmPrelude LkmmEvents.

  Definition event_structure := gmap event_id event.

  Definition empty_event_structure : event_structure := ∅.

  Definition lookup_event (E : event_structure) (eid : event_id) : option event :=
    E !! eid.

  Definition event_ids (E : event_structure) : gset event_id :=
    dom E.

  Definition in_event_structure (E : event_structure) (eid : event_id) : Prop :=
    eid ∈ event_ids E.

  (** Agent-local positions identify generated events uniquely.  Initial
      writes have no agent-local position and are deliberately unconstrained
      here. *)
  Definition event_structure_wf (E : event_structure) : Prop :=
    forall eid1 eid2 agent index label1 label2,
      lookup_event E eid1 = Some (EAgent agent index label1) ->
      lookup_event E eid2 = Some (EAgent agent index label2) ->
      eid1 = eid2.

  Lemma in_event_structure_lookup_iff E eid :
    in_event_structure E eid <-> exists ev, lookup_event E eid = Some ev.
  Proof.
    unfold in_event_structure.
    change (eid ∈ dom E <-> exists ev, E !! eid = Some ev).
    split.
    - intros Hin.
      apply (proj1 (elem_of_dom E eid)) in Hin. exact Hin.
    - intros Hlookup.
      apply (proj2 (elem_of_dom E eid)). exact Hlookup.
  Qed.

  Lemma lookup_event_in E eid ev :
    lookup_event E eid = Some ev -> in_event_structure E eid.
  Proof.
    intros Hlookup. apply in_event_structure_lookup_iff.
    by exists ev.
  Qed.

  Lemma not_in_lookup_event E eid :
    ~ in_event_structure E eid -> lookup_event E eid = None.
  Proof.
    intros Hnot.
    destruct (lookup_event E eid) as [ev |] eqn:Hlookup; last done.
    exfalso. apply Hnot. by eapply lookup_event_in.
  Qed.

  Lemma event_structure_wf_agent_position_injective E :
    event_structure_wf E ->
    forall eid1 eid2 agent index label1 label2,
      lookup_event E eid1 = Some (EAgent agent index label1) ->
      lookup_event E eid2 = Some (EAgent agent index label2) ->
      eid1 = eid2.
  Proof. done. Qed.

  Lemma empty_event_structure_wf :
    event_structure_wf empty_event_structure.
  Proof.
    intros eid1 eid2 agent index label1 label2 Hlookup.
    unfold lookup_event, empty_event_structure in Hlookup.
    discriminate Hlookup.
  Qed.

  Lemma singleton_event_structure_wf eid ev :
    event_structure_wf ({[eid := ev]} : event_structure).
  Proof.
    intros eid1 eid2 agent index label1 label2 Hlookup1 Hlookup2.
    unfold lookup_event in Hlookup1, Hlookup2.
    apply lookup_singleton_Some in Hlookup1 as [-> _].
    apply lookup_singleton_Some in Hlookup2 as [-> _].
    done.
  Qed.

  Module EventStructureTests.
    Definition init_write : event := EInitWrite 0 0%Z.
    Definition once_read : event :=
      EAgent 0 0 (LMemory AccessRead AccessOnce NotRmw 0 0%Z).
    Definition once_write_at_two : event :=
      EAgent 0 2 (LMemory AccessWrite AccessOnce NotRmw 0 1%Z).
    Definition other_agent_write : event :=
      EAgent 1 0 (LMemory AccessWrite AccessOnce NotRmw 0 1%Z).

    Definition sample_structure : event_structure :=
      <[1 := once_read]> ({[0 := init_write]} : event_structure).

    Example sample_lookup :
      lookup_event sample_structure 1 = Some once_read.
    Proof. reflexivity. Qed.
    Example sample_membership :
      in_event_structure sample_structure 1.
    Proof. apply (lookup_event_in sample_structure 1 once_read), sample_lookup. Qed.

    Local Lemma two_agent_events_wf agent1 index1 label1 agent2 index2 label2 :
      (agent1 <> agent2 \/ index1 <> index2) ->
      event_structure_wf
        (<[2 := EAgent agent2 index2 label2]>
          ({[1 := EAgent agent1 index1 label1]} : event_structure)).
    Proof.
      intros Hposition eid1 eid2 agent index label1' label2'
        Hlookup1 Hlookup2.
      change
        ((<[2 := EAgent agent2 index2 label2]>
          ({[1 := EAgent agent1 index1 label1]} : event_structure)) !! eid1 =
          Some (EAgent agent index label1')) in Hlookup1.
      change
        ((<[2 := EAgent agent2 index2 label2]>
          ({[1 := EAgent agent1 index1 label1]} : event_structure)) !! eid2 =
          Some (EAgent agent index label2')) in Hlookup2.
      apply lookup_insert_Some in Hlookup1.
      apply lookup_insert_Some in Hlookup2.
      destruct Hlookup1 as [[Heid1 Hevent1] | [Hne1 Hlookup1]].
      - destruct Hlookup2 as [[Heid2 Hevent2] | [Hne2 Hlookup2]].
        + naive_solver.
        + apply lookup_singleton_Some in Hlookup2
            as [Heid2 Hevent2].
          naive_solver.
      - apply lookup_singleton_Some in Hlookup1 as [Heid1 Hevent1].
        destruct Hlookup2 as [[Heid2 Hevent2] | [Hne2 Hlookup2]].
        + naive_solver.
        + apply lookup_singleton_Some in Hlookup2
            as [Heid2 Hevent2].
          naive_solver.
    Qed.

    Example distinct_positions_wf :
      event_structure_wf (<[2 := once_write_at_two]> ({[1 := once_read]} : event_structure)).
    Proof. apply two_agent_events_wf. by right. Qed.

    Example equal_indices_on_different_agents_wf :
      event_structure_wf (<[2 := other_agent_write]> ({[1 := once_read]} : event_structure)).
    Proof. apply two_agent_events_wf. by left. Qed.

    Definition duplicate_position_structure : event_structure :=
      <[2 := EAgent 0 0 (LMemory AccessWrite AccessOnce NotRmw 0 1%Z)]>
        ({[1 := once_read]} : event_structure).

    Example duplicate_position_not_wf :
      ~ event_structure_wf duplicate_position_structure.
    Proof.
      intros Hwf.
      assert (1 = 2) as Heq.
      { eapply Hwf with
          (agent := 0) (index := 0)
          (label1 := LMemory AccessRead AccessOnce NotRmw 0 0%Z)
          (label2 := LMemory AccessWrite AccessOnce NotRmw 0 1%Z);
          reflexivity. }
      lia.
    Qed.

    Definition duplicate_initial_writes : event_structure :=
      <[2 := EInitWrite 0 0%Z]> ({[1 := EInitWrite 0 0%Z]} : event_structure).

    Example initial_writes_have_no_agent_position :
      event_structure_wf duplicate_initial_writes.
    Proof.
      intros eid1 eid2 agent index label1 label2 Hlookup1 Hlookup2.
      change
        ((<[2 := EInitWrite 0 0%Z]>
          ({[1 := EInitWrite 0 0%Z]} : event_structure)) !! eid1 =
          Some (EAgent agent index label1)) in Hlookup1.
      apply lookup_insert_Some in Hlookup1.
      destruct Hlookup1 as [[Heid Hevent] | [Hne Hlookup1]].
      - discriminate Hevent.
      - apply lookup_singleton_Some in Hlookup1 as [Heid Hevent].
        discriminate Hevent.
    Qed.
  End EventStructureTests.

End LkmmExecution.
