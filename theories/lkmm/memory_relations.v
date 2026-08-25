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

  (** Direct dependency edges are finite provenance supplied by the candidate
      program graph.  Bell carrying is defined separately below. *)
  Definition direct_addr (edges : edge_set) : relation := edge_relation edges.

  Definition direct_data (edges : edge_set) : relation := edge_relation edges.

  Definition direct_ctrl (edges : edge_set) : relation := edge_relation edges.

  (** Linux v6.18 [linux-kernel.bell]: semantic event classes obtained by
      filtering the syntactic access and barrier annotations. *)
  Definition failed_rmw (E : event_structure) (rmw_edges : edge_set) (eid : event_id) : Prop :=
    event_is_rmw_marked E eid /\
    ~ (rel_domain (rmw rmw_edges) eid \/ rel_range (rmw rmw_edges) eid).

  Definition acquire (E : event_structure) (rmw_edges : edge_set) (eid : event_id) : Prop :=
    event_has_access_mode E eid AccessAcquire /\
    ~ event_has_access_kind E eid AccessWrite /\
    ~ failed_rmw E rmw_edges eid.

  Definition release (E : event_structure) (rmw_edges : edge_set) (eid : event_id) : Prop :=
    event_has_access_mode E eid AccessRelease /\
    ~ event_has_access_kind E eid AccessRead /\
    ~ failed_rmw E rmw_edges eid.

  Definition mb_event (E : event_structure) (rmw_edges : edge_set) (eid : event_id) : Prop :=
    (event_has_access_mode E eid AccessMb \/ event_has_barrier_kind E eid BarrierMb) /\
    ~ failed_rmw E rmw_edges eid.

  Definition noreturn (E : event_structure) (eid : event_id) : Prop :=
    event_has_access_mode E eid AccessNoreturn /\
    ~ event_has_access_kind E eid AccessWrite.

  (** Upstream derives [Plain = M \ Marked].  In the canonical vocabulary,
      an [AccessPlain], [NotRmw] access is exactly such an event.  An
      independently RMW-marked access remains [Marked]. *)
  Definition plain (E : event_structure) (eid : event_id) : Prop :=
    event_has_access_mode E eid AccessPlain /\
    ~ event_is_rmw_marked E eid.

  Definition marked (E : event_structure) (eid : event_id) : Prop :=
    in_event_structure E eid /\ ~ plain E eid.

  (** Linux v6.18: [acq-po = [Acquire] ; po ; [M]] *)
  Definition acq_po (E : event_structure) (rmw_edges : edge_set) : relation :=
    fun source target =>
      acquire E rmw_edges source /\ po E source target /\ event_is_memory E target.

  (** Linux v6.18: [po-rel = [M] ; po ; [Release]] *)
  Definition po_rel (E : event_structure) (rmw_edges : edge_set) : relation :=
    fun source target =>
      event_is_memory E source /\ po E source target /\ release E rmw_edges target.

  (** Herd7's standard library defines
      [fencerel(B) = (po & (_ * B)) ; po]. *)
  Definition fencerel (E : event_structure) (kind : barrier_kind) : relation :=
    fun source target =>
      exists barrier,
        po E source barrier /\
        event_has_barrier_kind E barrier kind /\
        po E barrier target.

  (** Linux v6.18: [R4rmb = R \ Noreturn]. *)
  Definition r4_rmb (E : event_structure) (eid : event_id) : Prop :=
    event_is_read E eid /\ ~ noreturn E eid.

  (** Linux v6.18: [rmb = [R4rmb] ; fencerel(Rmb) ; [R4rmb]]. *)
  Definition rmb (E : event_structure) : relation :=
    fun source target =>
      r4_rmb E source /\ fencerel E BarrierRmb source target /\ r4_rmb E target.

  (** Linux v6.18: [wmb = [W] ; fencerel(Wmb) ; [W]]. *)
  Definition wmb (E : event_structure) : relation :=
    fun source target =>
      event_is_write E source /\ fencerel E BarrierWmb source target /\
      event_is_write E target.

  (** Selected Linux v6.18 [mb] branches: explicit full barriers and the
      virtual barriers on either side of a successful full-barrier RMW. *)
  Definition mb (E : event_structure) (rmw_edges : edge_set) : relation :=
    rel_union
      (fun source target =>
        event_is_memory E source /\ fencerel E BarrierMb source target /\
        event_is_memory E target)
      (rel_union
        (fun source target =>
          event_is_memory E source /\ po E source target /\
          mb_event E rmw_edges target /\ event_is_read E target)
        (fun source target =>
          mb_event E rmw_edges source /\ event_is_write E source /\
          po E source target /\ event_is_memory E target)).

  (** Selected normal-RCU branch of [gp = po ; [Sync-rcu | Sync-srcu] ; po?]. *)
  Definition gp (E : event_structure) : relation :=
    fun source target =>
      exists sync,
        po E source sync /\
        event_has_barrier_kind E sync BarrierSyncRcu /\
        optional (po E) sync target.

  Definition strong_fence (E : event_structure) (rmw_edges : edge_set) : relation :=
    rel_union (mb E rmw_edges) (gp E).

  Definition nonrw_fence (E : event_structure) (rmw_edges : edge_set) : relation :=
    rel_union (strong_fence E rmw_edges)
      (rel_union (po_rel E rmw_edges) (acq_po E rmw_edges)).

  Definition fence (E : event_structure) (rmw_edges : edge_set) : relation :=
    rel_union (nonrw_fence E rmw_edges) (rel_union (wmb E) (rmb E)).

  (** From-read is derived from reads-from and coherence order: a read is
      before every write that is coherence-later than its source write. *)
  Definition fr (rf_edges co_edges : edge_set) : relation :=
    rel_seq (rel_inverse (rf rf_edges)) (co co_edges).

  (** Internal and external communication are the same-agent and
      not-same-agent parts of the candidate relations.  Initial writes have
      no agent and therefore occur only in the external parts. *)
  Definition rfi (E : event_structure) (rf_edges : edge_set) : relation :=
    rel_intersection (rf rf_edges) (same_agent E).

  Definition rfe (E : event_structure) (rf_edges : edge_set) : relation :=
    rel_difference (rf rf_edges) (same_agent E).

  Definition coi (E : event_structure) (co_edges : edge_set) : relation :=
    rel_intersection (co co_edges) (same_agent E).

  Definition coe (E : event_structure) (co_edges : edge_set) : relation :=
    rel_difference (co co_edges) (same_agent E).

  (** [fri] and [fre] classify the endpoints of the already-derived [fr]
      relation; they are not reconstructed from partitions of [rf] and [co]. *)
  Definition fri (E : event_structure) (rf_edges co_edges : edge_set) : relation :=
    rel_intersection (fr rf_edges co_edges) (same_agent E).

  Definition fre (E : event_structure) (rf_edges co_edges : edge_set) : relation :=
    rel_difference (fr rf_edges co_edges) (same_agent E).

  Lemma rf_internal_external E edges write read :
    rf edges write read <->
    rel_union (rfi E edges) (rfe E edges) write read.
  Proof.
    split.
    - intros Hrf. destruct (decide (same_agent E write read)) as [Hint | Hext].
      + by left.
      + by right.
    - intros [[Hrf _] | [Hrf _]]; exact Hrf.
  Qed.

  Lemma co_internal_external E edges write1 write2 :
    co edges write1 write2 <->
    rel_union (coi E edges) (coe E edges) write1 write2.
  Proof.
    split.
    - intros Hco. destruct (decide (same_agent E write1 write2)) as [Hint | Hext].
      + by left.
      + by right.
    - intros [[Hco _] | [Hco _]]; exact Hco.
  Qed.

  Lemma fr_internal_external E rf_edges co_edges read write :
    fr rf_edges co_edges read write <->
    rel_union (fri E rf_edges co_edges) (fre E rf_edges co_edges) read write.
  Proof.
    split.
    - intros Hfr. destruct (decide (same_agent E read write)) as [Hint | Hext].
      + by left.
      + by right.
    - intros [[Hfr _] | [Hfr _]]; exact Hfr.
  Qed.

  (** Linux v6.18 [linux-kernel.bell]: with SRCU excluded, dependency
      carrying is [(direct_data ; rfi)*]. *)
  Definition carry_dep (E : event_structure) (rf_edges data_edges : edge_set) : relation :=
    rtc (rel_seq (direct_data data_edges) (rfi E rf_edges)).

  Definition addr (E : event_structure) (rf_edges data_edges addr_edges : edge_set) : relation :=
    rel_seq (carry_dep E rf_edges data_edges) (direct_addr addr_edges).

  Definition data (E : event_structure) (rf_edges data_edges : edge_set) : relation :=
    rel_seq (carry_dep E rf_edges data_edges) (direct_data data_edges).

  Definition ctrl (E : event_structure) (rf_edges data_edges ctrl_edges : edge_set) : relation :=
    rel_seq (carry_dep E rf_edges data_edges) (direct_ctrl ctrl_edges).

  (** Linux v6.18: [dep = addr | data]. *)
  Definition dep (E : event_structure) (rf_edges data_edges addr_edges : edge_set) : relation :=
    rel_union (addr E rf_edges data_edges addr_edges) (data E rf_edges data_edges).

  (** Linux v6.18: [rwdep = (dep | ctrl) ; [W]]. *)
  Definition rwdep (E : event_structure)
      (rf_edges data_edges addr_edges ctrl_edges : edge_set) : relation :=
    fun source target =>
      rel_union (dep E rf_edges data_edges addr_edges)
        (ctrl E rf_edges data_edges ctrl_edges) source target /\
      event_is_write E target.

  (** Linux v6.18: [overwrite = co | fr]. *)
  Definition overwrite (rf_edges co_edges : edge_set) : relation :=
    rel_union (co co_edges) (fr rf_edges co_edges).

  (** Selected fragment of Linux v6.18 [to-w = rwdep | (overwrite & int)].
      The [addr ; [Plain] ; wmb] branch is deferred to a separate change. *)
  Definition to_w (E : event_structure)
      (rf_edges co_edges data_edges addr_edges ctrl_edges : edge_set) : relation :=
    rel_union (rwdep E rf_edges data_edges addr_edges ctrl_edges)
      (rel_intersection (overwrite rf_edges co_edges) (same_agent E)).

  (** Linux v6.18: [to-r = (addr ; [R]) | (dep ; [Marked] ; rfi)]. *)
  Definition to_r (E : event_structure) (rf_edges data_edges addr_edges : edge_set) : relation :=
    rel_union
      (fun source target =>
        addr E rf_edges data_edges addr_edges source target /\
        event_is_read E target)
      (fun source target =>
        exists middle,
          dep E rf_edges data_edges addr_edges source middle /\
          marked E middle /\ rfi E rf_edges middle target).

  (** Selected fragment of Linux v6.18 [ppo].  Lock ordering is outside the
      event vocabulary, and [fence] is the current base fence relation. *)
  Definition ppo (E : event_structure)
      (rmw_edges rf_edges co_edges data_edges addr_edges ctrl_edges : edge_set) : relation :=
    rel_union (to_r E rf_edges data_edges addr_edges)
      (rel_union (to_w E rf_edges co_edges data_edges addr_edges ctrl_edges)
        (rel_intersection (fence E rmw_edges) (same_agent E))).

  (** Linux v6.18: [com = rf | co | fr]. *)
  Definition com (rf_edges co_edges : edge_set) : relation :=
    rel_union (rf rf_edges) (rel_union (co co_edges) (fr rf_edges co_edges)).

  (** Linux v6.18: [acyclic (po-loc | com) as coherence].  Candidate
      well-formedness remains separate from this consistency constraint. *)
  Definition coherence (E : event_structure) (rf_edges co_edges : edge_set) : Prop :=
    rel_acyclic (rel_union (po_loc E) (com rf_edges co_edges)).

  (** Linux v6.18: [empty (rmw & (fre ; coe)) as atomic]. *)
  Definition atomicity (E : event_structure) (rmw_edges rf_edges co_edges : edge_set) : Prop :=
    rel_is_empty
      (rel_intersection (rmw rmw_edges) (rel_seq (fre E rf_edges co_edges) (coe E co_edges))).

  Definition direct_addr_edge_wf (E : event_structure) (read access : event_id) : Prop :=
    event_is_read E read /\
    event_is_memory E access /\
    po E read access.

  Definition direct_data_edge_wf (E : event_structure) (read write : event_id) : Prop :=
    event_is_read E read /\
    event_is_write E write /\
    po E read write.

  Definition direct_ctrl_edge_wf (E : event_structure) (read write : event_id) : Prop :=
    event_is_read E read /\
    event_is_write E write /\
    po E read write.

  Definition direct_addr_wf (E : event_structure) (edges : edge_set) : Prop :=
    forall read access,
      direct_addr edges read access -> direct_addr_edge_wf E read access.

  Definition direct_data_wf (E : event_structure) (edges : edge_set) : Prop :=
    forall read write,
      direct_data edges read write -> direct_data_edge_wf E read write.

  Definition direct_ctrl_wf (E : event_structure) (edges : edge_set) : Prop :=
    forall read write,
      direct_ctrl edges read write -> direct_ctrl_edge_wf E read write.

  Lemma direct_addr_wf_edge E edges read access :
    direct_addr_wf E edges ->
    direct_addr edges read access -> direct_addr_edge_wf E read access.
  Proof. intros Hedges Haddr. by eapply Hedges. Qed.

  Lemma direct_data_wf_edge E edges read write :
    direct_data_wf E edges ->
    direct_data edges read write -> direct_data_edge_wf E read write.
  Proof. intros Hedges Hdata. by eapply Hedges. Qed.

  Lemma direct_ctrl_wf_edge E edges read write :
    direct_ctrl_wf E edges ->
    direct_ctrl edges read write -> direct_ctrl_edge_wf E read write.
  Proof. intros Hedges Hctrl. by eapply Hedges. Qed.

  Definition rf_edge_wf (E : event_structure) (write read : event_id) : Prop :=
    exists write_event read_event val,
      lookup_event E write = Some write_event /\
      lookup_event E read = Some read_event /\
      is_write write_event /\ is_read read_event /\
      same_location E write read /\
      value_of write_event = Some val /\
      value_of read_event = Some val.

  Definition rf_functional (edges : edge_set) : Prop :=
    forall write1 write2 read, rf edges write1 read -> rf edges write2 read -> write1 = write2.

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

  Definition rmw_edge_wf (E : event_structure) (read write : event_id) : Prop :=
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
    exists eid, event_has_location E eid loc.

  Definition initial_write_at (E : event_structure) (loc : location) (write : event_id) : Prop :=
    exists val, lookup_event E write = Some (EInitWrite loc val).

  Definition initial_writes_exist (E : event_structure) : Prop :=
    forall loc, location_used E loc ->
      exists write, initial_write_at E loc write.

  Definition initial_writes_unique (E : event_structure) : Prop :=
    forall loc write1 write2,
      initial_write_at E loc write1 ->
      initial_write_at E loc write2 ->
      write1 = write2.

  Definition co_edge_wf (E : event_structure) (write1 write2 : event_id) : Prop :=
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

  Definition co_irreflexive (edges : edge_set) : Prop := forall write, ~ co edges write write.

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
    split_and!; try done.
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

  Module DependencyTests.
    Definition source_read : event := EAgent 0 0 (LMemory AccessRead AccessOnce NotRmw 0 0%Z).
    Definition relay_write : event := EAgent 0 1 (LMemory AccessWrite AccessOnce NotRmw 0 1%Z).
    Definition relay_read : event := EAgent 0 2 (LMemory AccessRead AccessOnce NotRmw 0 1%Z).
    Definition addr_target : event := EAgent 0 3 (LMemory AccessRead AccessPlain NotRmw 1 0%Z).
    Definition data_target : event := EAgent 0 4 (LMemory AccessWrite AccessOnce NotRmw 1 1%Z).
    Definition ctrl_target : event := EAgent 0 5 (LMemory AccessWrite AccessOnce NotRmw 2 1%Z).

    Definition sample_events : event_structure := {[
      0 := source_read;
      1 := relay_write;
      2 := relay_read;
      3 := addr_target;
      4 := data_target;
      5 := ctrl_target
    ]}.
    Definition sample_rf : edge_set := {[(1, 2)]}.
    Definition sample_addr : edge_set := {[(2, 3)]}.
    Definition sample_data : edge_set := {[(0, 1); (2, 4)]}.
    Definition sample_ctrl : edge_set := {[(2, 5)]}.

    Local Lemma sample_addr_wf : direct_addr_wf sample_events sample_addr.
    Proof.
      intros read access Haddr.
      unfold direct_addr, edge_relation, sample_addr in Haddr.
      assert (read = 2 /\ access = 3) as [-> ->] by set_solver.
      repeat split.
      - exists relay_read. split; reflexivity.
      - exists addr_target. split; done.
      - exists 0, 2, 3,
          (LMemory AccessRead AccessOnce NotRmw 0 1%Z),
          (LMemory AccessRead AccessPlain NotRmw 1 0%Z).
        repeat split; reflexivity || lia.
    Qed.

    Local Lemma sample_data_wf : direct_data_wf sample_events sample_data.
    Proof.
      intros read write Hdata.
      unfold direct_data, edge_relation, sample_data in Hdata.
      assert ((read = 0 /\ write = 1) \/ (read = 2 /\ write = 4))
        as [[-> ->] | [-> ->]] by set_solver.
      - repeat split.
        + exists source_read. split; reflexivity.
        + exists relay_write. split; reflexivity.
        + exists 0, 0, 1,
          (LMemory AccessRead AccessOnce NotRmw 0 0%Z),
          (LMemory AccessWrite AccessOnce NotRmw 0 1%Z).
          repeat split; reflexivity || lia.
      - repeat split.
        + exists relay_read. split; reflexivity.
        + exists data_target. split; reflexivity.
        + exists 0, 2, 4,
          (LMemory AccessRead AccessOnce NotRmw 0 1%Z),
          (LMemory AccessWrite AccessOnce NotRmw 1 1%Z).
          repeat split; reflexivity || lia.
    Qed.

    Local Lemma sample_ctrl_wf : direct_ctrl_wf sample_events sample_ctrl.
    Proof.
      intros read write Hctrl.
      unfold direct_ctrl, edge_relation, sample_ctrl in Hctrl.
      assert (read = 2 /\ write = 5) as [-> ->] by set_solver.
      repeat split.
      - exists relay_read. split; reflexivity.
      - exists ctrl_target. split; reflexivity.
      - exists 0, 2, 5,
          (LMemory AccessRead AccessOnce NotRmw 0 1%Z),
          (LMemory AccessWrite AccessOnce NotRmw 2 1%Z).
        repeat split; reflexivity || lia.
    Qed.

    Local Lemma sample_carrier : carry_dep sample_events sample_rf sample_data 0 2.
    Proof.
      apply rt_step. exists 1. split.
      - unfold direct_data, edge_relation, sample_data. set_solver.
      - split.
        + unfold rf, edge_relation, sample_rf. set_solver.
        + exists 0. split; reflexivity.
    Qed.

    Example address_dependency_carries :
      direct_addr_wf sample_events sample_addr /\
      addr sample_events sample_rf sample_data sample_addr 0 3.
    Proof.
      split; first apply sample_addr_wf.
      exists 2. split; first apply sample_carrier.
      unfold direct_addr, edge_relation, sample_addr. set_solver.
    Qed.

    Example data_dependency_carries :
      direct_data_wf sample_events sample_data /\
      data sample_events sample_rf sample_data 0 4.
    Proof.
      split; first apply sample_data_wf.
      exists 2. split; first apply sample_carrier.
      unfold direct_data, edge_relation, sample_data. set_solver.
    Qed.

    Example control_dependency_carries :
      direct_ctrl_wf sample_events sample_ctrl /\
      ctrl sample_events sample_rf sample_data sample_ctrl 0 5.
    Proof.
      split; first apply sample_ctrl_wf.
      exists 2. split; first apply sample_carrier.
      unfold direct_ctrl, edge_relation, sample_ctrl. set_solver.
    Qed.

    Example preserved_program_order_dependency_paths :
      ppo sample_events ∅ sample_rf ∅ sample_data sample_addr sample_ctrl 0 3 /\
      ppo sample_events ∅ sample_rf ∅ sample_data sample_addr sample_ctrl 0 4 /\
      ppo sample_events ∅ sample_rf ∅ sample_data sample_addr sample_ctrl 0 5 /\
      ppo sample_events ∅ sample_rf ∅ sample_data sample_addr sample_ctrl 0 2.
    Proof.
      destruct address_dependency_carries as [_ Haddr].
      destruct data_dependency_carries as [_ Hdata].
      destruct control_dependency_carries as [_ Hctrl].
      assert (data sample_events sample_rf sample_data 0 1) as Hdata_direct.
      { exists 0. split; first apply rt_refl.
        unfold direct_data, edge_relation, sample_data. set_solver. }
      assert (marked sample_events 1) as Hmarked.
      { split.
        - apply in_event_structure_lookup_iff. exists relay_write. reflexivity.
        - intros [Hmode _].
          change (Some AccessOnce = Some AccessPlain) in Hmode. discriminate. }
      assert (rfi sample_events sample_rf 1 2) as Hrfi.
      { split.
        - unfold rf, edge_relation, sample_rf. set_solver.
        - exists 0. split; reflexivity. }
      split_and!.
      - left. left. split; first done.
        exists addr_target. split; reflexivity.
      - right. left. left. split.
        + left. right. exact Hdata.
        + exists data_target. split; reflexivity.
      - right. left. left. split.
        + right. exact Hctrl.
        + exists ctrl_target. split; reflexivity.
      - left. right. exists 1. split.
        + right. exact Hdata_direct.
        + split; done.
    Qed.

    Example plain_access_classification :
      plain sample_events 3 /\ ~ marked sample_events 3 /\ marked sample_events 1.
    Proof.
      assert (plain sample_events 3) as Hplain.
      { split; first reflexivity.
        unfold event_is_rmw_marked.
        change (Some NotRmw <> Some RmwMarked). discriminate. }
      assert (marked sample_events 1) as Hmarked.
      { split.
        - apply in_event_structure_lookup_iff. exists relay_write. reflexivity.
        - intros [Hmode _].
          change (Some AccessOnce = Some AccessPlain) in Hmode. discriminate. }
      split_and!; try done.
      intros [_ Hnot_plain]. exact (Hnot_plain Hplain).
    Qed.
  End DependencyTests.

  Module BellEventClassTests.
    Definition acquire_read : event :=
      EAgent 0 0 (LMemory AccessRead AccessAcquire RmwMarked 0 0%Z).
    Definition acquire_write : event :=
      EAgent 0 1 (LMemory AccessWrite AccessAcquire RmwMarked 0 1%Z).
    Definition failed_acquire_read : event :=
      EAgent 0 2 (LMemory AccessRead AccessAcquire RmwMarked 0 0%Z).
    Definition release_read : event :=
      EAgent 0 3 (LMemory AccessRead AccessRelease RmwMarked 0 1%Z).
    Definition release_write : event :=
      EAgent 0 4 (LMemory AccessWrite AccessRelease RmwMarked 0 2%Z).
    Definition failed_release_write : event :=
      EAgent 0 5 (LMemory AccessWrite AccessRelease RmwMarked 0 2%Z).
    Definition mb_read : event := EAgent 0 6 (LMemory AccessRead AccessMb RmwMarked 0 2%Z).
    Definition mb_write : event := EAgent 0 7 (LMemory AccessWrite AccessMb RmwMarked 0 3%Z).
    Definition mb_barrier : event := EAgent 0 8 (LBarrier BarrierMb).
    Definition failed_mb_read : event := EAgent 0 9 (LMemory AccessRead AccessMb RmwMarked 0 3%Z).
    Definition failed_noreturn_read : event :=
      EAgent 0 10 (LMemory AccessRead AccessNoreturn RmwMarked 0 3%Z).
    Definition noreturn_write : event :=
      EAgent 0 11 (LMemory AccessWrite AccessNoreturn RmwMarked 0 4%Z).

    Definition sample_events : event_structure := {[
      0 := acquire_read;
      1 := acquire_write;
      2 := failed_acquire_read;
      3 := release_read;
      4 := release_write;
      5 := failed_release_write;
      6 := mb_read;
      7 := mb_write;
      8 := mb_barrier;
      9 := failed_mb_read;
      10 := failed_noreturn_read;
      11 := noreturn_write
    ]}.
    Definition sample_rmw : edge_set := {[(0, 1); (3, 4); (6, 7)]}.

    Example semantic_event_classification :
      failed_rmw sample_events sample_rmw 2 /\
      failed_rmw sample_events sample_rmw 5 /\
      ~ (failed_rmw sample_events sample_rmw 0 \/
          failed_rmw sample_events sample_rmw 1) /\
      acquire sample_events sample_rmw 0 /\
      ~ (acquire sample_events sample_rmw 1 \/
          acquire sample_events sample_rmw 2) /\
      release sample_events sample_rmw 4 /\
      ~ (release sample_events sample_rmw 3 \/
          release sample_events sample_rmw 5) /\
      mb_event sample_events sample_rmw 6 /\
      mb_event sample_events sample_rmw 8 /\
      failed_rmw sample_events sample_rmw 9 /\
      ~ mb_event sample_events sample_rmw 9 /\
      failed_rmw sample_events sample_rmw 10 /\
      noreturn sample_events 10 /\
      ~ noreturn sample_events 11 /\
      ~ (failed_rmw sample_events sample_rmw 99 \/
          acquire sample_events sample_rmw 99 \/
          release sample_events sample_rmw 99 \/
          mb_event sample_events sample_rmw 99 \/
          noreturn sample_events 99).
    Proof.
      repeat split;
        unfold failed_rmw, acquire, release, mb_event, noreturn,
          rel_domain, rel_range, rmw, edge_relation,
          event_is_rmw_marked, event_has_access_mode, event_has_access_kind,
          event_has_barrier_kind, lookup_event, sample_events, sample_rmw,
          acquire_read, acquire_write, failed_acquire_read,
          release_read, release_write, failed_release_write,
          mb_read, mb_write, mb_barrier, failed_mb_read,
          failed_noreturn_read, noreturn_write;
        simpl; try unfold failed_rmw;
        unfold rel_domain, rel_range, rmw, edge_relation;
        simpl; set_solver.
    Qed.
  End BellEventClassTests.

  Module AcquireReleaseOrderingTests.
    Definition acquire_read : event :=
      EAgent 0 0 (LMemory AccessRead AccessAcquire NotRmw 0 0%Z).
    Definition barrier : event := EAgent 0 1 (LBarrier BarrierMb).
    Definition middle_write : event :=
      EAgent 0 2 (LMemory AccessWrite AccessOnce NotRmw 0 1%Z).
    Definition release_write : event :=
      EAgent 0 3 (LMemory AccessWrite AccessRelease NotRmw 0 2%Z).

    Definition sample_events : event_structure := {[
      0 := acquire_read;
      1 := barrier;
      2 := middle_write;
      3 := release_write
    ]}.
    Definition no_rmw : edge_set := ∅.

    Example acquire_release_ordering :
      acq_po sample_events no_rmw 0 2 /\
      po_rel sample_events no_rmw 2 3 /\
      ~ acq_po sample_events no_rmw 0 1 /\
      ~ po_rel sample_events no_rmw 1 3.
    Proof.
      assert (event_is_memory sample_events 2) as Hmemory.
      { exists middle_write. split; reflexivity. }
      assert (~ event_is_memory sample_events 1) as Hbarrier.
      { intros (ev & Hlookup & Hmemory').
        change (Some barrier = Some ev) in Hlookup.
        injection Hlookup as <-. done. }
      repeat split;
        unfold acq_po, po_rel, acquire, release, failed_rmw,
          rel_domain, rel_range, rmw, edge_relation, event_is_memory,
          event_has_access_mode, event_has_access_kind, event_is_rmw_marked,
          po, lookup_event, sample_events, no_rmw, acquire_read, barrier,
          middle_write, release_write;
        simpl; try set_solver; naive_solver.
    Qed.
  End AcquireReleaseOrderingTests.

  Module FenceOrderingTests.
    Definition noreturn_read : event :=
      EAgent 0 0 (LMemory AccessRead AccessNoreturn NotRmw 0 0%Z).
    Definition before_read : event :=
      EAgent 0 1 (LMemory AccessRead AccessOnce NotRmw 0 0%Z).
    Definition rmb_barrier : event := EAgent 0 2 (LBarrier BarrierRmb).
    Definition after_read : event :=
      EAgent 0 3 (LMemory AccessRead AccessOnce NotRmw 0 0%Z).
    Definition before_write : event :=
      EAgent 0 4 (LMemory AccessWrite AccessOnce NotRmw 0 1%Z).
    Definition wmb_barrier : event := EAgent 0 5 (LBarrier BarrierWmb).
    Definition after_write : event :=
      EAgent 0 6 (LMemory AccessWrite AccessOnce NotRmw 0 2%Z).
    Definition mb_barrier : event := EAgent 0 7 (LBarrier BarrierMb).
    Definition before_rmw : event :=
      EAgent 0 8 (LMemory AccessRead AccessOnce NotRmw 0 2%Z).
    Definition sync_rcu : event := EAgent 0 9 (LBarrier BarrierSyncRcu).
    Definition rmw_read : event :=
      EAgent 0 10 (LMemory AccessRead AccessMb RmwMarked 0 2%Z).
    Definition rmw_write : event :=
      EAgent 0 11 (LMemory AccessWrite AccessMb RmwMarked 0 3%Z).
    Definition after_rmw : event :=
      EAgent 0 12 (LMemory AccessRead AccessOnce NotRmw 0 3%Z).

    Definition sample_events : event_structure := {[
      0 := noreturn_read;
      1 := before_read;
      2 := rmb_barrier;
      3 := after_read;
      4 := before_write;
      5 := wmb_barrier;
      6 := after_write;
      7 := mb_barrier;
      8 := before_rmw;
      9 := sync_rcu;
      10 := rmw_read;
      11 := rmw_write;
      12 := after_rmw
    ]}.
    Definition sample_rmw : edge_set := {[(10, 11)]}.

    Local Lemma sample_po eid1 eid2 index1 index2 label1 label2 :
      lookup_event sample_events eid1 = Some (EAgent 0 index1 label1) ->
      lookup_event sample_events eid2 = Some (EAgent 0 index2 label2) ->
      index1 < index2 ->
      po sample_events eid1 eid2.
    Proof.
      intros Hlookup1 Hlookup2 Hlt.
      exists 0, index1, index2, label1, label2. done.
    Qed.

    Local Ltac solve_sample_po :=
      eapply sample_po; [reflexivity | reflexivity | lia].

    Local Lemma sample_rmb : rmb sample_events 1 3.
    Proof.
      unfold rmb, r4_rmb. repeat split.
      - eexists. split; done.
      - unfold noreturn, event_has_access_mode, event_has_access_kind.
        intros [Hmode _].
        change (Some AccessOnce = Some AccessNoreturn) in Hmode. discriminate.
      - unfold fencerel. exists 2. repeat split; try solve_sample_po.
      - eexists. split; done.
      - unfold noreturn, event_has_access_mode, event_has_access_kind.
        intros [Hmode _].
        change (Some AccessOnce = Some AccessNoreturn) in Hmode. discriminate.
    Qed.

    Local Lemma sample_not_rmb : ~ rmb sample_events 0 3.
    Proof.
      unfold rmb, r4_rmb. intros ((_ & Hnot_noreturn) & _). apply Hnot_noreturn.
      unfold noreturn, event_has_access_mode, event_has_access_kind. split; first done.
      intros Hkind.
      change (Some AccessRead = Some AccessWrite) in Hkind. discriminate.
    Qed.

    Local Lemma sample_wmb : wmb sample_events 4 6.
    Proof.
      unfold wmb. repeat split.
      - eexists. split; done.
      - unfold fencerel. exists 5. repeat split; try solve_sample_po.
      - eexists. split; done.
    Qed.

    Local Lemma sample_not_wmb : ~ wmb sample_events 3 6.
    Proof.
      intros ((ev & Hlookup & Hwrite) & _).
      change (Some after_read = Some ev) in Hlookup.
      injection Hlookup as <-. done.
    Qed.

    Local Lemma sample_mb_event_read : mb_event sample_events sample_rmw 10.
    Proof.
      unfold mb_event, failed_rmw, rel_domain, rel_range, rmw, edge_relation,
        event_has_access_mode, event_is_rmw_marked, sample_rmw.
      simpl. set_solver.
    Qed.

    Local Lemma sample_mb_event_write : mb_event sample_events sample_rmw 11.
    Proof.
      unfold mb_event, failed_rmw, rel_domain, rel_range, rmw, edge_relation,
        event_has_access_mode, event_is_rmw_marked, sample_rmw.
      simpl. set_solver.
    Qed.

    Local Lemma sample_mb_explicit : mb sample_events sample_rmw 6 8.
    Proof.
      left. repeat split.
      - eexists. split; done.
      - unfold fencerel. exists 7. repeat split; try solve_sample_po.
      - eexists. split; done.
    Qed.

    Local Lemma sample_mb_before_rmw : mb sample_events sample_rmw 8 10.
    Proof.
      right. left. split.
      - eexists. split; done.
      - split; first solve_sample_po. split.
        + apply sample_mb_event_read.
        + eexists. split; done.
    Qed.

    Local Lemma sample_mb_after_rmw : mb sample_events sample_rmw 11 12.
    Proof.
      right. right. split; first apply sample_mb_event_write.
      split.
      - eexists. split; done.
      - split; first solve_sample_po.
        eexists. split; done.
    Qed.

    Local Lemma sample_gp_at_sync : gp sample_events 8 9.
    Proof.
      exists 9. split; first solve_sample_po. split.
      - unfold event_has_barrier_kind. reflexivity.
      - left. done.
    Qed.

    Local Lemma sample_gp_after : gp sample_events 8 10.
    Proof.
      exists 9. split; first solve_sample_po. split.
      - unfold event_has_barrier_kind. reflexivity.
      - right. solve_sample_po.
    Qed.

    Example primitive_fence_ordering :
      rmb sample_events 1 3 /\
      ~ rmb sample_events 0 3 /\
      wmb sample_events 4 6 /\
      ~ wmb sample_events 3 6 /\
      mb sample_events sample_rmw 6 8 /\
      mb sample_events sample_rmw 8 10 /\
      mb sample_events sample_rmw 11 12 /\
      gp sample_events 8 9 /\
      gp sample_events 8 10.
    Proof.
      split_and!;
        [ apply sample_rmb
        | apply sample_not_rmb
        | apply sample_wmb
        | apply sample_not_wmb
        | apply sample_mb_explicit
        | apply sample_mb_before_rmw
        | apply sample_mb_after_rmw
        | apply sample_gp_at_sync
        | apply sample_gp_after ].
    Qed.

  End FenceOrderingTests.

  Module ReadsFromTests.
    Definition init_write : event := EInitWrite 0 0%Z.
    Definition once_read : event := EAgent 0 0 (LMemory AccessRead AccessOnce NotRmw 0 0%Z).
    Definition second_write : event := EAgent 1 0 (LMemory AccessWrite AccessOnce NotRmw 0 0%Z).

    Definition sample_events : event_structure := {[0 := init_write; 1 := once_read]}.

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
            unfold is_read, init_write, access_kind_of in Hread.
            discriminate Hread.
          * apply lookup_singleton_Some in Hlookup as [Hread_id Hread_event].
            subst read. subst read_event.
            exists 0. unfold rf, edge_relation, sample_rf. set_solver.
    Qed.

    Definition two_source_events : event_structure :=
      {[0 := init_write; 1 := once_read; 2 := second_write]}.

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
    Definition marked_read : event := EAgent 0 0 (LMemory AccessRead AccessMb RmwMarked 0 7%Z).
    Definition marked_write : event := EAgent 0 1 (LMemory AccessWrite AccessMb RmwMarked 0 8%Z).
    Definition sample_events : event_structure := {[0 := marked_read; 1 := marked_write]}.
    Definition sample_rmw : edge_set := {[(0, 1)]}.

    Definition failed_events : event_structure := {[0 := marked_read]}.
    Definition write_only_events : event_structure := {[1 := marked_write]}.

    Definition unmarked_read : event := EAgent 0 0 (LMemory AccessRead AccessMb NotRmw 0 7%Z).
    Definition unmarked_source_events : event_structure :=
      {[0 := unmarked_read; 1 := marked_write]}.
    Definition unmarked_write : event := EAgent 0 1 (LMemory AccessWrite AccessMb NotRmw 0 8%Z).
    Definition unmarked_target_events : event_structure :=
      {[0 := marked_read; 1 := unmarked_write]}.

    Definition other_location_write : event :=
      EAgent 0 1 (LMemory AccessWrite AccessMb RmwMarked 1 8%Z).
    Definition different_location_events : event_structure :=
      {[0 := marked_read; 1 := other_location_write]}.
    Definition other_mode_write : event :=
      EAgent 0 1 (LMemory AccessWrite AccessOnce RmwMarked 0 8%Z).
    Definition different_mode_events : event_structure :=
      {[0 := marked_read; 1 := other_mode_write]}.
    Definition other_agent_write : event :=
      EAgent 1 1 (LMemory AccessWrite AccessMb RmwMarked 0 8%Z).
    Definition different_agent_events : event_structure :=
      {[0 := marked_read; 1 := other_agent_write]}.
    Definition late_read : event := EAgent 0 2 (LMemory AccessRead AccessMb RmwMarked 0 7%Z).
    Definition reversed_po_events : event_structure := {[0 := late_read; 1 := marked_write]}.

    Definition second_write : event := EAgent 0 2 (LMemory AccessWrite AccessMb RmwMarked 0 9%Z).
    Definition two_write_events : event_structure :=
      {[0 := marked_read; 1 := marked_write; 2 := second_write]}.
    Definition one_read_two_writes : edge_set := {[(0, 1); (0, 2)]}.

    Definition second_read : event := EAgent 0 1 (LMemory AccessRead AccessMb RmwMarked 0 7%Z).
    Definition late_write : event := EAgent 0 2 (LMemory AccessWrite AccessMb RmwMarked 0 8%Z).
    Definition two_read_events : event_structure :=
      {[0 := marked_read; 1 := late_write; 2 := second_read]}.
    Definition two_reads_one_write : edge_set := {[(0, 1); (2, 1)]}.

    Definition intervening_write : event := EAgent 1 0 (LMemory AccessWrite AccessMb NotRmw 0 9%Z).
    Definition atomicity_events : event_structure :=
      {[0 := marked_read;
        1 := marked_write;
        2 := intervening_write;
        3 := EInitWrite 0 7%Z]}.
    Definition atomicity_rf : edge_set := {[(3, 0)]}.
    Definition intervened_co : edge_set := {[(3, 2); (3, 1); (2, 1)]}.

    Local Lemma sample_lookup_cases eid ev :
      lookup_event sample_events eid = Some ev ->
      (eid = 0 /\ ev = marked_read) \/
      (eid = 1 /\ ev = marked_write).
    Proof.
      intros Hlookup.
      unfold lookup_event, sample_events in Hlookup.
      apply lookup_insert_Some in Hlookup.
      destruct Hlookup as [[-> Hevent] | [Hne Hlookup]].
      - left. naive_solver.
      - apply lookup_singleton_Some in Hlookup.
        right. naive_solver.
    Qed.

    Local Lemma singleton_rmw_edge read write :
      rmw ({[(read, write)]} : edge_set) read write.
    Proof. unfold rmw, edge_relation. set_solver. Qed.

    Example valid_rmw_candidates :
      rmw_wf sample_events sample_rmw /\
      rmw_wf failed_events (∅ : edge_set).
    Proof.
      split.
      - repeat split.
        + intros read write Hrmw.
          unfold rmw, edge_relation, sample_rmw in Hrmw.
          assert (read = 0 /\ write = 1) as [-> ->] by set_solver.
          exists marked_read, marked_write.
          repeat split; try reflexivity.
          * exists 0, 0, 1,
              (LMemory AccessRead AccessMb RmwMarked 0 7%Z),
              (LMemory AccessWrite AccessMb RmwMarked 0 8%Z).
            repeat split; try reflexivity. lia.
          * exists 0. split; reflexivity.
          * exists AccessMb. split; reflexivity.
        + intros read write1 write2 Hrmw1 Hrmw2.
          unfold rmw, edge_relation, sample_rmw in Hrmw1, Hrmw2.
          set_solver.
        + intros read1 read2 write Hrmw1 Hrmw2.
          unfold rmw, edge_relation, sample_rmw in Hrmw1, Hrmw2.
          set_solver.
        + intros write write_event Hlookup Hwrite Hmarked.
          destruct (sample_lookup_cases write write_event Hlookup)
            as [(-> & ->) | (-> & ->)].
          * discriminate Hwrite.
          * exists 0. unfold rmw, edge_relation, sample_rmw. set_solver.
      - repeat split.
        + intros read write Hrmw.
          unfold rmw, edge_relation in Hrmw. set_solver.
        + intros read write1 write2 Hrmw1 Hrmw2.
          unfold rmw, edge_relation in Hrmw1. set_solver.
        + intros read1 read2 write Hrmw1 Hrmw2.
          unfold rmw, edge_relation in Hrmw1. set_solver.
        + intros write write_event Hlookup Hwrite Hmarked.
          unfold lookup_event, failed_events in Hlookup.
          apply lookup_singleton_Some in Hlookup as [Hwrite_id Hevent].
          subst write. subst write_event.
          discriminate Hwrite.
    Qed.

    Example malformed_rmw_candidates :
      ~ rmw_wf write_only_events (∅ : edge_set) /\
      ~ rmw_wf sample_events ({[(1, 0)]} : edge_set) /\
      ~ rmw_wf unmarked_source_events ({[(0, 1)]} : edge_set) /\
      ~ rmw_wf unmarked_target_events ({[(0, 1)]} : edge_set) /\
      ~ rmw_wf different_location_events ({[(0, 1)]} : edge_set) /\
      ~ rmw_wf different_mode_events ({[(0, 1)]} : edge_set) /\
      ~ rmw_wf different_agent_events ({[(0, 1)]} : edge_set) /\
      ~ rmw_wf reversed_po_events ({[(0, 1)]} : edge_set).
    Proof.
      assert (~ rmw_wf write_only_events (∅ : edge_set)) as Hunpaired.
      { intros Hwf.
        pose proof (rmw_wf_write_total write_only_events
          (∅ : edge_set) Hwf) as Htotal.
        destruct (Htotal 1 marked_write) as (read & Hrmw);
          try reflexivity.
        unfold rmw, edge_relation in Hrmw. set_solver. }
      assert (~ rmw_wf sample_events ({[(1, 0)]} : edge_set)) as Hkinds.
      { intros Hwf.
        destruct (rmw_wf_kinds sample_events ({[(1, 0)]} : edge_set)
          1 0 Hwf (singleton_rmw_edge 1 0))
          as (read_event & write_event & Hread & Hwrite &
            Hread_kind & Hwrite_kind).
        assert (read_event = marked_write) as ->.
        { change (Some marked_write = Some read_event) in Hread. congruence. }
        discriminate Hread_kind. }
      assert (~ rmw_wf unmarked_source_events ({[(0, 1)]} : edge_set)) as Hsource_marked.
      { intros Hwf.
        destruct (rmw_wf_marked unmarked_source_events
          ({[(0, 1)]} : edge_set) 0 1 Hwf (singleton_rmw_edge 0 1))
          as (read_event & write_event & Hread & Hwrite &
            Hread_marked & Hwrite_marked).
        assert (read_event = unmarked_read) as ->.
        { change (Some unmarked_read = Some read_event) in Hread. congruence. }
        discriminate Hread_marked. }
      assert (~ rmw_wf unmarked_target_events ({[(0, 1)]} : edge_set)) as Htarget_marked.
      { intros Hwf.
        destruct (rmw_wf_marked unmarked_target_events
          ({[(0, 1)]} : edge_set) 0 1 Hwf (singleton_rmw_edge 0 1))
          as (read_event & write_event & Hread & Hwrite &
            Hread_marked & Hwrite_marked).
        assert (write_event = unmarked_write) as ->.
        { change (Some unmarked_write = Some write_event) in Hwrite. congruence. }
        discriminate Hwrite_marked. }
      assert (~ rmw_wf different_location_events ({[(0, 1)]} : edge_set)) as Hlocation.
      { intros Hwf.
        pose proof (rmw_wf_same_location different_location_events
          ({[(0, 1)]} : edge_set) 0 1 Hwf (singleton_rmw_edge 0 1))
          as (loc & Hread_loc & Hwrite_loc).
        change (Some 0 = Some loc) in Hread_loc.
        change (Some 1 = Some loc) in Hwrite_loc.
        congruence. }
      assert (~ rmw_wf different_mode_events ({[(0, 1)]} : edge_set)) as Hmode.
      { intros Hwf.
        pose proof (rmw_wf_same_mode different_mode_events
          ({[(0, 1)]} : edge_set) 0 1 Hwf (singleton_rmw_edge 0 1))
          as (mode & Hread_mode & Hwrite_mode).
        change (Some AccessMb = Some mode) in Hread_mode.
        change (Some AccessOnce = Some mode) in Hwrite_mode.
        congruence. }
      assert (~ rmw_wf different_agent_events ({[(0, 1)]} : edge_set)) as Hagent.
      { intros Hwf.
        pose proof (rmw_wf_po different_agent_events
          ({[(0, 1)]} : edge_set) 0 1 Hwf (singleton_rmw_edge 0 1))
          as (agent & index1 & index2 & label1 & label2 &
            Hread & Hwrite & Hlt).
        change (Some marked_read = Some (EAgent agent index1 label1)) in Hread.
        change (Some other_agent_write =
          Some (EAgent agent index2 label2)) in Hwrite.
        unfold marked_read, other_agent_write in Hread, Hwrite.
        congruence. }
      assert (~ rmw_wf reversed_po_events ({[(0, 1)]} : edge_set)) as Hpo.
      { intros Hwf.
        pose proof (rmw_wf_po reversed_po_events
          ({[(0, 1)]} : edge_set) 0 1 Hwf (singleton_rmw_edge 0 1))
          as (agent & index1 & index2 & label1 & label2 &
            Hread & Hwrite & Hlt).
        change (Some late_read = Some (EAgent agent index1 label1)) in Hread.
        change (Some marked_write = Some (EAgent agent index2 label2)) in Hwrite.
        unfold late_read in Hread. unfold marked_write in Hwrite.
        assert (index1 = 2) as -> by congruence.
        assert (index2 = 1) as -> by congruence.
        lia. }
      tauto.
    Qed.

    Example rmw_pairing_is_a_partial_bijection :
      ~ rmw_wf two_write_events one_read_two_writes /\
      ~ rmw_wf two_read_events two_reads_one_write.
    Proof.
      split.
      - intros Hwf.
        pose proof (rmw_wf_functional two_write_events
          one_read_two_writes Hwf) as Hfunctional.
        assert (1 = 2) as Heq.
        { eapply Hfunctional with (read := 0);
            unfold rmw, edge_relation, one_read_two_writes; set_solver. }
        lia.
      - intros Hwf.
        pose proof (rmw_wf_injective two_read_events
          two_reads_one_write Hwf) as Hinjective.
        assert (0 = 2) as Heq.
        { eapply Hinjective with (write := 1);
            unfold rmw, edge_relation, two_reads_one_write; set_solver. }
        lia.
    Qed.

    Example intervening_external_write_violates_atomicity :
      ~ atomicity atomicity_events sample_rmw atomicity_rf intervened_co.
    Proof.
      unfold atomicity, rel_is_empty.
      intros Hatomic. apply (Hatomic 0 1). split.
      - unfold rmw, edge_relation, sample_rmw. set_solver.
      - exists 2. split.
        + split.
          * unfold fr, rel_seq, rel_inverse, rf, co, edge_relation,
              atomicity_rf, intervened_co.
            exists 3. split; set_solver.
          * intros (agent & Hread_agent & Hwrite_agent).
            change (Some 0 = Some agent) in Hread_agent.
            change (Some 1 = Some agent) in Hwrite_agent. congruence.
        + split.
          * unfold co, edge_relation, intervened_co. set_solver.
          * intros (agent & Hwrite1_agent & Hwrite2_agent).
            change (Some 1 = Some agent) in Hwrite1_agent.
            change (Some 0 = Some agent) in Hwrite2_agent. congruence.
    Qed.
  End ReadModifyWriteTests.

  Module CoherenceOrderTests.
    Definition init_write : event := EInitWrite 0 0%Z.
    Definition first_write : event := EAgent 0 0 (LMemory AccessWrite AccessOnce NotRmw 0 1%Z).
    Definition second_write : event := EAgent 1 0 (LMemory AccessWrite AccessOnce NotRmw 0 2%Z).

    Definition sample_events : event_structure :=
      {[0 := init_write; 1 := first_write; 2 := second_write]}.

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
      - left. naive_solver.
      - apply lookup_insert_Some in Hlookup.
        destruct Hlookup as [[-> Hevent] | [Hne' Hlookup]].
        + right. left. naive_solver.
        + apply lookup_singleton_Some in Hlookup.
          right. right. naive_solver.
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
        unfold event_has_location in Hloc.
        apply bind_Some in Hloc as (ev & Hlookup & Hloc).
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

    Definition cyclic_co : edge_set := {[(0, 1); (0, 2); (1, 2); (2, 1)]}.
    Definition missing_initial_events : event_structure := {[1 := first_write]}.
    Definition duplicate_initial_events : event_structure :=
      {[0 := init_write; 3 := EInitWrite 0 7%Z]}.
    Definition late_initial_events : event_structure := {[0 := init_write; 1 := first_write]}.
    Definition late_initial_co : edge_set := {[(1, 0)]}.

    Example malformed_coherence_orders :
      ~ co_wf sample_events cyclic_co /\
      ~ co_wf missing_initial_events (∅ : edge_set) /\
      ~ co_wf duplicate_initial_events (∅ : edge_set) /\
      ~ co_wf late_initial_events late_initial_co.
    Proof.
      assert (~ co_wf sample_events cyclic_co) as Hcycle.
      { intros Hwf.
        pose proof (co_wf_irreflexive sample_events cyclic_co Hwf)
          as Hirreflexive.
        pose proof (co_wf_transitive sample_events cyclic_co Hwf)
          as Htransitive.
        apply (Hirreflexive 1).
        eapply Htransitive with (write2 := 2);
          unfold co, edge_relation, cyclic_co; set_solver. }
      assert (~ co_wf missing_initial_events (∅ : edge_set)) as Hmissing.
      { intros Hwf.
        pose proof (co_wf_initial_exists missing_initial_events
          (∅ : edge_set) Hwf) as Hexists.
        assert (location_used missing_initial_events 0) as Hused.
        { exists 1. reflexivity. }
        destruct (Hexists 0 Hused) as (initial & val & Hlookup).
        unfold lookup_event, missing_initial_events in Hlookup.
        apply lookup_singleton_Some in Hlookup as [Heid Hevent].
        discriminate Hevent. }
      assert (~ co_wf duplicate_initial_events (∅ : edge_set)) as Hduplicate.
      { intros Hwf.
        pose proof (co_wf_initial_unique duplicate_initial_events
          (∅ : edge_set) Hwf) as Hunique.
        assert (0 = 3) as Heq.
        { eapply Hunique with (loc := 0).
          - exists 0%Z. reflexivity.
          - exists 7%Z. reflexivity. }
        lia. }
      assert (~ co_wf late_initial_events late_initial_co) as Hlate.
      { intros Hwf.
        pose proof (co_wf_initial_first late_initial_events
          late_initial_co Hwf) as Hfirst.
        assert (co late_initial_co 0 1) as Hco.
        { eapply Hfirst with (loc := 0) (write_event := first_write).
          - exists 0%Z. reflexivity.
          - reflexivity.
          - reflexivity.
          - exists 0. split; reflexivity.
          - lia. }
        unfold co, edge_relation, late_initial_co in Hco. set_solver. }
      tauto.
    Qed.
  End CoherenceOrderTests.

  Module FromReadTests.
    (** Writes [0], [1], and [2] form a coherence chain.  Read [3] reads
        from [0], while read [4] reads from [1]. *)
    Definition sample_rf : edge_set := {[(0, 3); (1, 4)]}.
    Definition sample_co : edge_set := {[(0, 1); (0, 2); (1, 2)]}.

    Example from_read_classification :
      fr sample_rf sample_co 3 1 /\
      fr sample_rf sample_co 3 2 /\
      fr sample_rf sample_co 4 2 /\
      ~ fr sample_rf sample_co 3 0 /\
      ~ fr sample_rf sample_co 4 0.
    Proof.
      unfold fr, rel_seq, rel_inverse, rf, co, edge_relation,
        sample_rf, sample_co. set_solver.
    Qed.
  End FromReadTests.

  Module InternalExternalTests.
    Definition init_write : event := EInitWrite 0 0%Z.
    Definition agent0_write : event := EAgent 0 1 (LMemory AccessWrite AccessOnce NotRmw 0 1%Z).
    Definition agent0_read : event := EAgent 0 2 (LMemory AccessRead AccessOnce NotRmw 0 1%Z).
    Definition agent0_later_write : event :=
      EAgent 0 3 (LMemory AccessWrite AccessOnce NotRmw 0 2%Z).
    Definition agent1_read : event := EAgent 1 0 (LMemory AccessRead AccessOnce NotRmw 0 1%Z).
    Definition agent1_write : event := EAgent 1 1 (LMemory AccessWrite AccessOnce NotRmw 0 3%Z).
    Definition agent0_initial_read : event :=
      EAgent 0 0 (LMemory AccessRead AccessOnce NotRmw 0 0%Z).

    Definition sample_events : event_structure := {[
      0 := init_write;
      1 := agent0_write;
      2 := agent0_read;
      3 := agent0_later_write;
      4 := agent1_read;
      5 := agent1_write;
      6 := agent0_initial_read
    ]}.

    Definition sample_rf : edge_set := {[(0, 6); (1, 2); (1, 4)]}.
    Definition sample_co : edge_set := {[(0, 1); (0, 3); (0, 5); (1, 3); (1, 5); (3, 5)]}.

    Example ordinary_internal_external_classification :
      rfi sample_events sample_rf 1 2 /\
      rfe sample_events sample_rf 1 4 /\
      coi sample_events sample_co 1 3 /\
      coe sample_events sample_co 3 5.
    Proof.
      assert (rfi sample_events sample_rf 1 2) as Hrfi.
      { split.
        - unfold rf, edge_relation, sample_rf. set_solver.
        - exists 0. split; reflexivity. }
      assert (rfe sample_events sample_rf 1 4) as Hrfe.
      { split.
        - unfold rf, edge_relation, sample_rf. set_solver.
        - intros (agent & Hagent0 & Hagent1).
          change (Some 0 = Some agent) in Hagent0.
          change (Some 1 = Some agent) in Hagent1. congruence. }
      assert (coi sample_events sample_co 1 3) as Hcoi.
      { split.
        - unfold co, edge_relation, sample_co. set_solver.
        - exists 0. split; reflexivity. }
      assert (coe sample_events sample_co 3 5) as Hcoe.
      { split.
        - unfold co, edge_relation, sample_co. set_solver.
        - intros (agent & Hagent0 & Hagent1).
          change (Some 0 = Some agent) in Hagent0.
          change (Some 1 = Some agent) in Hagent1. congruence. }
      split_and!; done.
    Qed.

    (** Although read [6] reads from the initial write, [fri] classifies the
        endpoints of [fr]: read [6] and write [1] both belong to agent 0. *)
    Example initial_write_and_fr_endpoint_classification :
      rfe sample_events sample_rf 0 6 /\
      coe sample_events sample_co 0 1 /\
      fri sample_events sample_rf sample_co 6 1 /\
      fre sample_events sample_rf sample_co 6 5.
    Proof.
      assert (rfe sample_events sample_rf 0 6) as Hrfe.
      { split.
        - unfold rf, edge_relation, sample_rf. set_solver.
        - intros (agent & Hinitial & Hagent).
          change (None = Some agent) in Hinitial. discriminate Hinitial. }
      assert (coe sample_events sample_co 0 1) as Hcoe.
      { split.
        - unfold co, edge_relation, sample_co. set_solver.
        - intros (agent & Hinitial & Hagent).
          change (None = Some agent) in Hinitial. discriminate Hinitial. }
      assert (fri sample_events sample_rf sample_co 6 1) as Hfri.
      { split.
        - unfold fr, rel_seq, rel_inverse, rf, co, edge_relation,
            sample_rf, sample_co.
          exists 0. split; set_solver.
        - exists 0. split; reflexivity. }
      assert (fre sample_events sample_rf sample_co 6 5) as Hfre.
      { split.
        - unfold fr, rel_seq, rel_inverse, rf, co, edge_relation,
            sample_rf, sample_co.
          exists 0. split; set_solver.
        - intros (agent & Hagent0 & Hagent1).
          change (Some 0 = Some agent) in Hagent0.
          change (Some 1 = Some agent) in Hagent1. congruence. }
      split_and!; done.
    Qed.
  End InternalExternalTests.

  Module BaseCoherenceTests.
    Definition first_write : event := EAgent 0 0 (LMemory AccessWrite AccessOnce NotRmw 0 1%Z).
    Definition second_write : event := EAgent 0 1 (LMemory AccessWrite AccessOnce NotRmw 0 2%Z).

    Definition sample_events : event_structure := {[1 := first_write; 2 := second_write]}.

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
          split_and!; try done. lia.
        + exists 0. split; reflexivity.
      - apply t_step. right. unfold com, rel_union. right. left.
        unfold co, edge_relation, reversed_co. set_solver.
    Qed.
  End BaseCoherenceTests.

End LkmmMemoryRelations.
