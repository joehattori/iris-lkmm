From Stdlib Require Import ZArith.
From stdpp Require Import fin_map_dom gmap option tactics.
From iris_lkmm.lkmm Require Import prelude events.

(** Raw finite event structures for the relational LKMM model.

    Event identifiers are external keys into the finite map.  Structural
    well-formedness is kept as a separate predicate so that later operational
    states may contain partial structures without carrying proof fields. *)
Module LkmmExecution.
  Export LkmmPrelude LkmmEvents.
  Open Scope stdpp_scope.

  Definition event_structure := gmap event_id event.

  Definition edge := (event_id * event_id)%type.
  Definition edge_set := gset edge.

  Definition edge_relation (edges : edge_set) : relation :=
    fun source target => (source, target) ∈ edges.

  Definition empty_event_structure : event_structure := ∅.

  Definition lookup_event (E : event_structure) (eid : event_id) : option event := E !! eid.

  Definition event_ids (E : event_structure) : gset event_id := dom E.

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

  Definition event_structure_included (E1 E2 : event_structure) : Prop :=
    forall eid ev, lookup_event E1 eid = Some ev -> lookup_event E2 eid = Some ev.

  Local Definition event_satisfies (pred : event -> Prop)
      (E : event_structure) (eid : event_id) : Prop :=
    exists ev, lookup_event E eid = Some ev /\ pred ev.

  Local Lemma event_satisfies_mono pred E1 E2 eid :
    event_structure_included E1 E2 ->
    event_satisfies pred E1 eid -> event_satisfies pred E2 eid.
  Proof.
    intros HE (ev & Hlookup & Hpred). exists ev. split; [by eapply HE | done].
  Qed.

  Definition event_is_read (E : event_structure) (eid : event_id) : Prop :=
    event_satisfies is_read E eid.

  Definition event_is_write (E : event_structure) (eid : event_id) : Prop :=
    event_satisfies is_write E eid.

  Definition event_is_memory (E : event_structure) (eid : event_id) : Prop :=
    event_satisfies is_memory E eid.

  (** Compose event lookup with any partial event projection. *)
  Local Definition event_attribute {A} (project : event -> option A)
      (E : event_structure) (eid : event_id) : option A :=
    lookup_event E eid ≫= project.

  Local Lemma event_attribute_mono {A} (project : event -> option A)
      E1 E2 eid (value : A) :
    event_structure_included E1 E2 ->
    event_attribute project E1 eid = Some value ->
    event_attribute project E2 eid = Some value.
  Proof.
    intros HE Hattribute. unfold event_attribute in Hattribute |- *.
    destruct (lookup_event E1 eid) as [ev |] eqn:Hlookup; last discriminate.
    rewrite (HE eid ev Hlookup). done.
  Qed.

  Definition event_has_access_kind (E : event_structure) (kind : access_kind)
      (eid : event_id) : Prop :=
    event_attribute access_kind_of E eid = Some kind.

  Definition event_has_access_mode (E : event_structure) (mode : access_mode)
      (eid : event_id) : Prop :=
    event_attribute access_mode_of E eid = Some mode.

  Definition event_is_rmw_marked (E : event_structure) (eid : event_id) : Prop :=
    event_attribute rmw_mark_of E eid = Some RmwMarked.

  Definition event_has_barrier_kind (E : event_structure) (kind : barrier_kind)
      (eid : event_id) : Prop :=
    event_attribute barrier_kind_of E eid = Some kind.

  Definition event_has_location (E : event_structure) (loc : location) (eid : event_id) : Prop :=
    event_attribute location_of E eid = Some loc.

  (** Two identifiers have the same attribute when both projections are
      defined and return the same value. *)
  Definition same_attribute {A} (project : event -> option A) (E : event_structure) : relation :=
    fun eid1 eid2 =>
      exists value,
        event_attribute project E eid1 = Some value /\
        event_attribute project E eid2 = Some value.

  Lemma same_attribute_mono {A} (project : event -> option A) E1 E2 :
    event_structure_included E1 E2 ->
    rel_included (same_attribute project E1) (same_attribute project E2).
  Proof.
    intros HE eid1 eid2 (value & Hvalue1 & Hvalue2). exists value.
    split; by eapply event_attribute_mono.
  Qed.

  Global Instance same_attribute_decision {A} `{EqDecision A}
      (project : event -> option A) E eid1 eid2 :
      Decision (same_attribute project E eid1 eid2).
  Proof.
    unfold same_attribute.
    destruct (event_attribute project E eid1) as [value1 |] eqn:Hattribute1;
      destruct (event_attribute project E eid2) as [value2 |] eqn:Hattribute2.
    - destruct (decide (value1 = value2)) as [-> | Hneq].
      + left. by exists value2.
      + right. intros (value & Hvalue1 & Hvalue2). apply Hneq. congruence.
    - right. intros (value & Hvalue1 & Hvalue2). congruence.
    - right. intros (value & Hvalue1 & Hvalue2). congruence.
    - right. intros (value & Hvalue1 & Hvalue2). congruence.
  Defined.

  Definition same_location (E : event_structure) : relation := same_attribute location_of E.

  Definition same_agent (E : event_structure) : relation := same_attribute agent_of E.

  Lemma same_attribute_from_lookup {A} (project : event -> option A)
      E eid1 eid2 event1 event2 value :
    lookup_event E eid1 = Some event1 ->
    lookup_event E eid2 = Some event2 ->
    project event1 = Some value -> project event2 = Some value ->
    same_attribute project E eid1 eid2.
  Proof.
    intros Hlookup1 Hlookup2 Hvalue1 Hvalue2. exists value.
    unfold event_attribute. by rewrite Hlookup1, Hlookup2.
  Qed.

  (** Herd's [ext]: endpoints that do not belong to the same program agent. *)
  Definition ext (E : event_structure) : relation := fun eid1 eid2 => ~ same_agent E eid1 eid2.

  (** Program order is the full strict order between generated events of one
      agent.  Local indices need not be contiguous.  Initial writes are
      excluded because they have no agent-local position. *)
  Definition po (E : event_structure) : relation :=
    fun eid1 eid2 =>
      exists agent index1 index2 label1 label2,
        lookup_event E eid1 = Some (EAgent agent index1 label1) /\
        lookup_event E eid2 = Some (EAgent agent index2 label2) /\
        index1 < index2.

  Definition po_loc (E : event_structure) : relation := rel_intersection (po E) (same_location E).

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

  Lemma in_event_structure_mono E1 E2 :
    event_structure_included E1 E2 ->
    forall eid, in_event_structure E1 eid -> in_event_structure E2 eid.
  Proof.
    intros HE eid Hin. apply in_event_structure_lookup_iff in Hin as (ev & Hlookup).
    apply in_event_structure_lookup_iff. exists ev. by eapply HE.
  Qed.

  Local Lemma event_satisfies_reflect pred E1 E2 eid :
    event_structure_included E1 E2 ->
    in_event_structure E1 eid ->
    event_satisfies pred E2 eid -> event_satisfies pred E1 eid.
  Proof.
    intros HE Hin (ev2 & Hlookup2 & Hpred).
    apply in_event_structure_lookup_iff in Hin as (ev1 & Hlookup1).
    pose proof (HE eid ev1 Hlookup1) as Hlookup1'.
    assert (ev2 = ev1) as -> by congruence. by exists ev1.
  Qed.

  Lemma event_is_read_mono E1 E2 eid :
    event_structure_included E1 E2 -> event_is_read E1 eid -> event_is_read E2 eid.
  Proof. apply event_satisfies_mono. Qed.

  Lemma event_is_read_reflect E1 E2 eid :
    event_structure_included E1 E2 -> in_event_structure E1 eid ->
    event_is_read E2 eid -> event_is_read E1 eid.
  Proof. apply event_satisfies_reflect. Qed.

  Lemma event_is_write_mono E1 E2 eid :
    event_structure_included E1 E2 -> event_is_write E1 eid -> event_is_write E2 eid.
  Proof. apply event_satisfies_mono. Qed.

  Lemma event_is_write_reflect E1 E2 eid :
    event_structure_included E1 E2 -> in_event_structure E1 eid ->
    event_is_write E2 eid -> event_is_write E1 eid.
  Proof. apply event_satisfies_reflect. Qed.

  Lemma event_is_memory_mono E1 E2 eid :
    event_structure_included E1 E2 -> event_is_memory E1 eid -> event_is_memory E2 eid.
  Proof. apply event_satisfies_mono. Qed.

  Lemma event_is_memory_reflect E1 E2 eid :
    event_structure_included E1 E2 -> in_event_structure E1 eid ->
    event_is_memory E2 eid -> event_is_memory E1 eid.
  Proof. apply event_satisfies_reflect. Qed.

  Local Lemma event_attribute_reflect {A} (project : event -> option A)
      E1 E2 eid (value : A) :
    event_structure_included E1 E2 ->
    in_event_structure E1 eid ->
    event_attribute project E2 eid = Some value ->
    event_attribute project E1 eid = Some value.
  Proof.
    intros HE Hin Hattribute.
    apply in_event_structure_lookup_iff in Hin as (ev & Hlookup).
    unfold event_attribute in Hattribute |- *.
    rewrite Hlookup. rewrite (HE eid ev Hlookup) in Hattribute. done.
  Qed.

  Lemma event_has_access_kind_mono E1 E2 kind eid :
    event_structure_included E1 E2 ->
    event_has_access_kind E1 kind eid -> event_has_access_kind E2 kind eid.
  Proof. apply event_attribute_mono. Qed.

  Lemma event_has_access_kind_reflect E1 E2 kind eid :
    event_structure_included E1 E2 -> in_event_structure E1 eid ->
    event_has_access_kind E2 kind eid -> event_has_access_kind E1 kind eid.
  Proof. apply event_attribute_reflect. Qed.

  Lemma event_has_access_mode_mono E1 E2 mode eid :
    event_structure_included E1 E2 ->
    event_has_access_mode E1 mode eid -> event_has_access_mode E2 mode eid.
  Proof. apply event_attribute_mono. Qed.

  Lemma event_has_access_mode_reflect E1 E2 mode eid :
    event_structure_included E1 E2 -> in_event_structure E1 eid ->
    event_has_access_mode E2 mode eid -> event_has_access_mode E1 mode eid.
  Proof. apply event_attribute_reflect. Qed.

  Lemma event_is_rmw_marked_mono E1 E2 eid :
    event_structure_included E1 E2 ->
    event_is_rmw_marked E1 eid -> event_is_rmw_marked E2 eid.
  Proof. apply event_attribute_mono. Qed.

  Lemma event_is_rmw_marked_reflect E1 E2 eid :
    event_structure_included E1 E2 -> in_event_structure E1 eid ->
    event_is_rmw_marked E2 eid -> event_is_rmw_marked E1 eid.
  Proof. apply event_attribute_reflect. Qed.

  Lemma event_has_barrier_kind_mono E1 E2 kind eid :
    event_structure_included E1 E2 ->
    event_has_barrier_kind E1 kind eid -> event_has_barrier_kind E2 kind eid.
  Proof. apply event_attribute_mono. Qed.

  Lemma event_has_barrier_kind_reflect E1 E2 kind eid :
    event_structure_included E1 E2 -> in_event_structure E1 eid ->
    event_has_barrier_kind E2 kind eid -> event_has_barrier_kind E1 kind eid.
  Proof. apply event_attribute_reflect. Qed.

  Lemma same_attribute_reflect {A} (project : event -> option A) E1 E2 eid1 eid2 :
    event_structure_included E1 E2 ->
    in_event_structure E1 eid1 -> in_event_structure E1 eid2 ->
    same_attribute project E2 eid1 eid2 -> same_attribute project E1 eid1 eid2.
  Proof.
    intros HE Hin1 Hin2 (value & Hvalue1 & Hvalue2). exists value.
    split; eapply event_attribute_reflect; done.
  Qed.

  Lemma same_agent_reflect E1 E2 eid1 eid2 :
    event_structure_included E1 E2 ->
    in_event_structure E1 eid1 -> in_event_structure E1 eid2 ->
    same_agent E2 eid1 eid2 -> same_agent E1 eid1 eid2.
  Proof. apply same_attribute_reflect. Qed.

  Lemma ext_mono E1 E2 eid1 eid2 :
    event_structure_included E1 E2 ->
    in_event_structure E1 eid1 -> in_event_structure E1 eid2 ->
    ext E1 eid1 eid2 -> ext E2 eid1 eid2.
  Proof.
    intros HE Hin1 Hin2 Hext Hsame. apply Hext.
    by eapply same_agent_reflect.
  Qed.

  Lemma po_mono E1 E2 :
    event_structure_included E1 E2 -> rel_included (po E1) (po E2).
  Proof.
    intros HE eid1 eid2
      (agent & index1 & index2 & label1 & label2 & Hlookup1 & Hlookup2 & Hlt).
    exists agent, index1, index2, label1, label2.
    split_and!; try done; by eapply HE.
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

  Local Lemma event_attribute_Some {A} (project : event -> option A) E eid (value : A) :
    event_attribute project E eid = Some value <->
    exists ev,
      lookup_event E eid = Some ev /\ project ev = Some value.
  Proof. apply bind_Some. Qed.

  Lemma event_has_access_mode_lookup E mode eid :
    event_has_access_mode E mode eid <->
    exists ev, lookup_event E eid = Some ev /\ access_mode_of ev = Some mode.
  Proof. apply event_attribute_Some. Qed.

  Lemma event_is_rmw_marked_lookup E eid :
    event_is_rmw_marked E eid <->
    exists ev, lookup_event E eid = Some ev /\ rmw_mark_of ev = Some RmwMarked.
  Proof. apply event_attribute_Some. Qed.

  Lemma event_has_barrier_kind_lookup E kind eid :
    event_has_barrier_kind E kind eid <->
    exists ev, lookup_event E eid = Some ev /\ barrier_kind_of ev = Some kind.
  Proof. apply event_attribute_Some. Qed.

  Lemma same_attribute_endpoints {A} (project : event -> option A) E eid1 eid2 :
    same_attribute project E eid1 eid2 ->
    in_event_structure E eid1 /\ in_event_structure E eid2.
  Proof.
    intros (value & Hattribute1 & Hattribute2).
    apply event_attribute_Some in Hattribute1
      as (event1 & Hlookup1 & Hproject1).
    apply event_attribute_Some in Hattribute2
      as (event2 & Hlookup2 & Hproject2).
    split; eapply lookup_event_in; eauto.
  Qed.

  Lemma same_attribute_symmetric {A} (project : event -> option A) E eid1 eid2 :
    same_attribute project E eid1 eid2 ->
    same_attribute project E eid2 eid1.
  Proof. intros (value & Hattribute1 & Hattribute2). by exists value. Qed.

  Lemma same_attribute_transitive {A} (project : event -> option A) E eid1 eid2 eid3 :
    same_attribute project E eid1 eid2 ->
    same_attribute project E eid2 eid3 ->
    same_attribute project E eid1 eid3.
  Proof.
    intros (value12 & Hattribute1 & Hattribute2)
      (value23 & Hattribute2' & Hattribute3).
    assert (value12 = value23) as -> by congruence.
    by exists value23.
  Qed.

  Lemma same_location_endpoints E eid1 eid2 :
    same_location E eid1 eid2 ->
    in_event_structure E eid1 /\ in_event_structure E eid2.
  Proof. apply same_attribute_endpoints. Qed.

  Lemma same_location_symmetric E eid1 eid2 :
    same_location E eid1 eid2 -> same_location E eid2 eid1.
  Proof. apply same_attribute_symmetric. Qed.

  Lemma same_location_transitive E eid1 eid2 eid3 :
    same_location E eid1 eid2 -> same_location E eid2 eid3 ->
    same_location E eid1 eid3.
  Proof. apply same_attribute_transitive. Qed.

  Lemma same_agent_endpoints E eid1 eid2 :
    same_agent E eid1 eid2 ->
    in_event_structure E eid1 /\ in_event_structure E eid2.
  Proof. apply same_attribute_endpoints. Qed.

  Lemma same_agent_symmetric E eid1 eid2 :
    same_agent E eid1 eid2 -> same_agent E eid2 eid1.
  Proof. apply same_attribute_symmetric. Qed.

  Lemma same_agent_transitive E eid1 eid2 eid3 :
    same_agent E eid1 eid2 -> same_agent E eid2 eid3 ->
    same_agent E eid1 eid3.
  Proof. apply same_attribute_transitive. Qed.

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
    event_structure_wf {[eid := ev]}.
  Proof.
    intros eid1 eid2 agent index label1 label2 Hlookup1 Hlookup2.
    unfold lookup_event in Hlookup1, Hlookup2.
    apply lookup_singleton_Some in Hlookup1 as [-> _].
    apply lookup_singleton_Some in Hlookup2 as [-> _].
    done.
  Qed.

  Lemma po_endpoints E eid1 eid2 :
    po E eid1 eid2 ->
    in_event_structure E eid1 /\ in_event_structure E eid2.
  Proof.
    intros (agent & index1 & index2 & label1 & label2 &
      Hlookup1 & Hlookup2 & Hlt).
    split; eapply lookup_event_in; eauto.
  Qed.

  Lemma po_same_agent E eid1 eid2 :
    po E eid1 eid2 ->
    same_agent E eid1 eid2.
  Proof.
    intros (agent & index1 & index2 & label1 & label2 &
      Hlookup1 & Hlookup2 & Hlt).
    exists agent. unfold event_attribute.
    rewrite Hlookup1, Hlookup2. done.
  Qed.

  Lemma po_irreflexive E eid :
    ~ po E eid eid.
  Proof.
    intros (agent & index1 & index2 & label1 & label2 &
      Hlookup1 & Hlookup2 & Hlt).
    assert (index1 = index2) by congruence. lia.
  Qed.

  Lemma po_transitive E eid1 eid2 eid3 :
    po E eid1 eid2 -> po E eid2 eid3 -> po E eid1 eid3.
  Proof.
    intros (agent1 & index1 & index2 & label1 & label2 &
      Hlookup1 & Hlookup2 & Hlt12)
      (agent2 & index2' & index3 & label2' & label3 &
      Hlookup2' & Hlookup3 & Hlt23).
    assert (agent1 = agent2) as -> by congruence.
    assert (index2 = index2') as -> by congruence.
    exists agent2, index1, index3, label1, label3.
    split_and!; try done. lia.
  Qed.

  Lemma po_loc_po E eid1 eid2 :
    po_loc E eid1 eid2 -> po E eid1 eid2.
  Proof. intros [Hpo _]. exact Hpo. Qed.

  Lemma po_loc_same_location E eid1 eid2 :
    po_loc E eid1 eid2 -> same_location E eid1 eid2.
  Proof. intros [_ Hloc]. exact Hloc. Qed.

  Lemma po_loc_endpoints E eid1 eid2 :
    po_loc E eid1 eid2 ->
    in_event_structure E eid1 /\ in_event_structure E eid2.
  Proof. intros [Hpo _]. by eapply po_endpoints. Qed.

  Lemma po_loc_same_agent E eid1 eid2 :
    po_loc E eid1 eid2 ->
    same_agent E eid1 eid2.
  Proof. intros [Hpo _]. by eapply po_same_agent. Qed.

  Lemma po_loc_irreflexive E eid :
    ~ po_loc E eid eid.
  Proof. intros [Hpo _]. by eapply po_irreflexive. Qed.

  Lemma po_loc_transitive E eid1 eid2 eid3 :
    po_loc E eid1 eid2 -> po_loc E eid2 eid3 -> po_loc E eid1 eid3.
  Proof.
    intros [Hpo12 Hloc12] [Hpo23 Hloc23]. split.
    - by eapply po_transitive.
    - by eapply same_location_transitive.
  Qed.

  Lemma po_total_same_agent E :
    event_structure_wf E ->
    forall eid1 eid2,
      same_agent E eid1 eid2 ->
      eid1 <> eid2 ->
      po E eid1 eid2 \/ po E eid2 eid1.
  Proof.
    intros Hwf eid1 eid2 (agent & Hagent1 & Hagent2) Hneq.
    apply event_attribute_Some in Hagent1
      as (event1 & Hlookup1 & Hagent1).
    apply event_attribute_Some in Hagent2
      as (event2 & Hlookup2 & Hagent2).
    destruct event1 as [loc1 val1 | agent1 index1 label1];
      first discriminate Hagent1.
    destruct event2 as [loc2 val2 | agent2 index2 label2];
      first discriminate Hagent2.
    simpl in Hagent1, Hagent2.
    assert (agent1 = agent) as -> by congruence.
    assert (agent2 = agent) as -> by congruence.
    destruct (Nat.lt_trichotomy index1 index2) as [Hlt | [Heq | Hlt]].
    - left. exists agent, index1, index2, label1, label2. done.
    - exfalso. apply Hneq. subst index2. by eapply Hwf.
    - right. exists agent, index2, index1, label2, label1. done.
  Qed.

  Lemma initial_write_not_po_source E eid1 eid2 loc val :
    lookup_event E eid1 = Some (EInitWrite loc val) ->
    ~ po E eid1 eid2.
  Proof.
    intros Hinit (agent & index1 & index2 & label1 & label2 &
      Hlookup1 & Hlookup2 & Hlt).
    congruence.
  Qed.

  Lemma initial_write_not_po_target E eid1 eid2 loc val :
    lookup_event E eid2 = Some (EInitWrite loc val) ->
    ~ po E eid1 eid2.
  Proof.
    intros Hinit (agent & index1 & index2 & label1 & label2 &
      Hlookup1 & Hlookup2 & Hlt).
    congruence.
  Qed.

  Module EventStructureTests.
    Definition init_write : event := EInitWrite 0 0%Z.
    Definition once_read : event := EAgent 0 0 (LMemory AccessRead AccessOnce NotRmw 0 0%Z).
    Definition once_write_at_two : event :=
      EAgent 0 2 (LMemory AccessWrite AccessOnce NotRmw 0 1%Z).
    Definition other_agent_write : event :=
      EAgent 1 0 (LMemory AccessWrite AccessOnce NotRmw 0 1%Z).
    Definition other_location_write : event :=
      EAgent 0 2 (LMemory AccessWrite AccessOnce NotRmw 1 1%Z).
    Definition mb_at_two : event := EAgent 0 2 (LBarrier BarrierMb).

    Definition sample_structure : event_structure := {[0 := init_write; 1 := once_read]}.

    Definition duplicate_position_structure : event_structure :=
      {[1 := once_read; 2 := EAgent 0 0 (LMemory AccessWrite AccessOnce NotRmw 0 1%Z)]}.

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
      {[1 := EInitWrite 0 0%Z; 2 := EInitWrite 0 0%Z]}.

    Example initial_writes_have_no_agent_position :
      event_structure_wf duplicate_initial_writes.
    Proof.
      intros eid1 eid2 agent index label1 label2 Hlookup1 Hlookup2.
      unfold lookup_event, duplicate_initial_writes in Hlookup1.
      apply lookup_insert_Some in Hlookup1.
      destruct Hlookup1 as [[Heid Hevent] | [Hne Hlookup1]].
      - discriminate Hevent.
      - apply lookup_singleton_Some in Hlookup1 as [Heid Hevent].
        discriminate Hevent.
    Qed.

    Definition same_agent_structure : event_structure := {[1 := once_read; 2 := once_write_at_two]}.

    Example same_agent_same_location_is_in_po_loc :
      po_loc same_agent_structure 1 2.
    Proof.
      split.
      - exists 0, 0, 2,
          (LMemory AccessRead AccessOnce NotRmw 0 0%Z),
          (LMemory AccessWrite AccessOnce NotRmw 0 1%Z).
        split_and!; try reflexivity. lia.
      - exists 0. split; reflexivity.
    Qed.

    Definition different_location_structure : event_structure :=
      {[1 := once_read; 2 := other_location_write]}.

    Example same_agent_different_location_is_not_in_po_loc :
      po different_location_structure 1 2 /\
      ~ po_loc different_location_structure 1 2.
    Proof.
      split.
      - exists 0, 0, 2,
          (LMemory AccessRead AccessOnce NotRmw 0 0%Z),
          (LMemory AccessWrite AccessOnce NotRmw 1 1%Z).
        split_and!; try reflexivity. lia.
      - intros [_ (loc & Hloc1 & Hloc2)].
        change (Some 0 = Some loc) in Hloc1.
        change (Some 1 = Some loc) in Hloc2. congruence.
    Qed.

    Definition cross_agent_structure : event_structure :=
      {[1 := once_read; 2 := other_agent_write]}.

    Example different_agents_are_not_in_program_order :
      ~ po cross_agent_structure 1 2.
    Proof.
      intros (agent & index1 & index2 & label1 & label2 &
        Hlookup1 & Hlookup2 & Hlt).
      change (Some once_read = Some (EAgent agent index1 label1)) in Hlookup1.
      change (Some other_agent_write =
        Some (EAgent agent index2 label2)) in Hlookup2.
      unfold once_read, other_agent_write in Hlookup1, Hlookup2.
      congruence.
    Qed.

    Definition barrier_structure : event_structure := {[1 := once_read; 2 := mb_at_two]}.

    Example barrier_is_not_in_po_loc :
      ~ po_loc barrier_structure 1 2.
    Proof.
      intros [_ (loc & Hloc1 & Hloc2)].
      change (None = Some loc) in Hloc2. discriminate Hloc2.
    Qed.

    Example initial_write_is_not_in_program_order :
      ~ po sample_structure 0 1 /\ ~ po sample_structure 1 0.
    Proof.
      split.
      - eapply initial_write_not_po_source. reflexivity.
      - eapply initial_write_not_po_target. reflexivity.
    Qed.
  End EventStructureTests.

End LkmmExecution.
