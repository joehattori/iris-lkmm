From Stdlib Require Import ZArith.
From stdpp Require Import base gmap tactics.
From iris_lkmm.lkmm Require Import prelude.

(** Canonical event vocabulary for the selected LKMM fragment.

    Access modes and RMW marking encode the selected syntactic vocabulary
    from [linux-kernel.bell].  [AccessPlain] is the Rocq representation of a
    memory access with no named Bell access annotation; upstream [Plain]
    remains a derived class.  The semantic [Acquire], [Release], [Mb],
    [Noreturn], and [FailedRMW] sets depend on execution relations, including
    [rmw], and are therefore defined in [memory_relations.v] rather than this
    event-vocabulary layer. *)
Module LkmmEvents.
  Import LkmmPrelude.

  Definition agent_id := nat.
  Definition event_index := nat.
  Definition location := nat.
  Definition value := Z.

  Inductive access_kind :=
  | AccessRead
  | AccessWrite.

  Inductive access_mode :=
  | AccessOnce
  | AccessRelease
  | AccessAcquire
  | AccessNoreturn
  | AccessMb
  | AccessPlain.

  (** [RmwMarked] records the syntactic RMW classification.  A successful
      RMW consists of marked read and write events connected by an
      [rmw] edge.  A failed conditional RMW has only the marked read event. *)
  Inductive rmw_mark :=
  | NotRmw
  | RmwMarked.

  Inductive barrier_kind :=
  | BarrierMb
  | BarrierRmb
  | BarrierWmb
  | BarrierRcuLock
  | BarrierRcuUnlock
  | BarrierSyncRcu.

  Inductive event_label :=
  | LMemory (kind : access_kind) (mode : access_mode)
      (mark : rmw_mark) (loc : location) (val : value)
  | LBarrier (barrier : barrier_kind).

  (** Initial writes have no agent or program-order position.  All other
      events belong to a fixed agent and carry a local event index. *)
  Inductive event :=
  | EInitWrite (loc : location) (val : value)
  | EAgent (agent : agent_id) (index : event_index) (label : event_label).

  Global Instance access_kind_eq_dec : EqDecision access_kind.
  Proof. solve_decision. Defined.

  Global Instance access_kind_countable : Countable access_kind.
  Proof.
    refine (inj_countable'
      (fun kind => match kind with AccessRead => 0 | AccessWrite => 1 end)
      (fun n => match n with 0 => AccessRead | _ => AccessWrite end) _).
    by intros [].
  Qed.

  Global Instance access_mode_eq_dec : EqDecision access_mode.
  Proof. solve_decision. Defined.

  Global Instance access_mode_countable : Countable access_mode.
  Proof.
    refine (inj_countable'
      (fun mode =>
        match mode with
        | AccessOnce => 0
        | AccessRelease => 1
        | AccessAcquire => 2
        | AccessNoreturn => 3
        | AccessMb => 4
        | AccessPlain => 5
        end)
      (fun n =>
        match n with
        | 0 => AccessOnce
        | 1 => AccessRelease
        | 2 => AccessAcquire
        | 3 => AccessNoreturn
        | 4 => AccessMb
        | _ => AccessPlain
        end) _).
    by intros [].
  Qed.

  Global Instance rmw_mark_eq_dec : EqDecision rmw_mark.
  Proof. solve_decision. Defined.

  Global Instance rmw_mark_countable : Countable rmw_mark.
  Proof.
    refine (inj_countable'
      (fun mark => match mark with NotRmw => 0 | RmwMarked => 1 end)
      (fun n => match n with 0 => NotRmw | _ => RmwMarked end) _).
    by intros [].
  Qed.

  Global Instance barrier_kind_eq_dec : EqDecision barrier_kind.
  Proof. solve_decision. Defined.

  Global Instance barrier_kind_countable : Countable barrier_kind.
  Proof.
    refine (inj_countable'
      (fun barrier =>
        match barrier with
        | BarrierMb => 0
        | BarrierRmb => 1
        | BarrierWmb => 2
        | BarrierRcuLock => 3
        | BarrierRcuUnlock => 4
        | BarrierSyncRcu => 5
        end)
      (fun n =>
        match n with
        | 0 => BarrierMb
        | 1 => BarrierRmb
        | 2 => BarrierWmb
        | 3 => BarrierRcuLock
        | 4 => BarrierRcuUnlock
        | _ => BarrierSyncRcu
        end) _).
    by intros [].
  Qed.

  Global Instance event_label_eq_dec : EqDecision event_label.
  Proof. solve_decision. Defined.

  Local Definition event_label_repr :=
    (access_kind * (access_mode * (rmw_mark * (location * value))) + barrier_kind)%type.

  Local Definition event_label_encode (label : event_label) : event_label_repr :=
    match label with
    | LMemory kind mode mark loc val => inl (kind, (mode, (mark, (loc, val))))
    | LBarrier barrier => inr barrier
    end.

  Local Definition event_label_decode (repr : event_label_repr) : event_label :=
    match repr with
    | inl (kind, (mode, (mark, (loc, val)))) => LMemory kind mode mark loc val
    | inr barrier => LBarrier barrier
    end.

  Global Instance event_label_countable : Countable event_label.
  Proof.
    refine (inj_countable' event_label_encode event_label_decode _).
    by intros [].
  Qed.

  Global Instance event_eq_dec : EqDecision event.
  Proof. solve_decision. Defined.

  Local Definition event_repr :=
    ((location * value) + (agent_id * (event_index * event_label)))%type.

  Local Definition event_encode (ev : event) : event_repr :=
    match ev with
    | EInitWrite loc val => inl (loc, val)
    | EAgent agent index label => inr (agent, (index, label))
    end.

  Local Definition event_decode (repr : event_repr) : event :=
    match repr with
    | inl (loc, val) => EInitWrite loc val
    | inr (agent, (index, label)) => EAgent agent index label
    end.

  Global Instance event_countable : Countable event.
  Proof.
    refine (inj_countable' event_encode event_decode _).
    by intros [].
  Qed.

  Definition agent_of (ev : event) : option agent_id :=
    match ev with
    | EInitWrite _ _ => None
    | EAgent agent _ _ => Some agent
    end.

  Definition index_of (ev : event) : option event_index :=
    match ev with
    | EInitWrite _ _ => None
    | EAgent _ index _ => Some index
    end.

  Definition access_kind_of (ev : event) : option access_kind :=
    match ev with
    | EInitWrite _ _ => Some AccessWrite
    | EAgent _ _ (LMemory kind _ _ _ _) => Some kind
    | EAgent _ _ (LBarrier _) => None
    end.

  Definition access_mode_of (ev : event) : option access_mode :=
    match ev with
    | EAgent _ _ (LMemory _ mode _ _ _) => Some mode
    | _ => None
    end.

  Definition rmw_mark_of (ev : event) : option rmw_mark :=
    match ev with
    | EAgent _ _ (LMemory _ _ mark _ _) => Some mark
    | _ => None
    end.

  Definition barrier_kind_of (ev : event) : option barrier_kind :=
    match ev with
    | EAgent _ _ (LBarrier barrier) => Some barrier
    | _ => None
    end.

  Definition location_of (ev : event) : option location :=
    match ev with
    | EInitWrite loc _ => Some loc
    | EAgent _ _ (LMemory _ _ _ loc _) => Some loc
    | EAgent _ _ (LBarrier _) => None
    end.

  Definition value_of (ev : event) : option value :=
    match ev with
    | EInitWrite _ val => Some val
    | EAgent _ _ (LMemory _ _ _ _ val) => Some val
    | EAgent _ _ (LBarrier _) => None
    end.

  Definition is_initial (ev : event) : Prop :=
    match ev with
    | EInitWrite _ _ => True
    | _ => False
    end.

  Definition is_read (ev : event) : Prop := access_kind_of ev = Some AccessRead.

  Definition is_write (ev : event) : Prop := access_kind_of ev = Some AccessWrite.

  Definition is_memory (ev : event) : Prop :=
    match ev with
    | EInitWrite _ _ | EAgent _ _ (LMemory _ _ _ _ _) => True
    | EAgent _ _ (LBarrier _) => False
    end.

  Definition is_barrier (ev : event) : Prop :=
    match ev with
    | EAgent _ _ (LBarrier _) => True
    | _ => False
    end.

  Definition is_rmw_marked (ev : event) : Prop := rmw_mark_of ev = Some RmwMarked.

  Definition is_rcu_lock (ev : event) : Prop := barrier_kind_of ev = Some BarrierRcuLock.

  Definition is_rcu_unlock (ev : event) : Prop := barrier_kind_of ev = Some BarrierRcuUnlock.

  Definition is_sync_rcu (ev : event) : Prop := barrier_kind_of ev = Some BarrierSyncRcu.

  Module EventTests.
    Definition init_write : event := EInitWrite 0 0%Z.
    Definition once_read : event := EAgent 0 0 (LMemory AccessRead AccessOnce NotRmw 1 7%Z).
    Definition rmw_read : event := EAgent 0 1 (LMemory AccessRead AccessMb RmwMarked 1 7%Z).
    Definition rmw_write : event := EAgent 0 2 (LMemory AccessWrite AccessMb RmwMarked 1 8%Z).
    Definition rcu_lock : event := EAgent 1 0 (LBarrier BarrierRcuLock).
    Definition rcu_unlock : event := EAgent 1 1 (LBarrier BarrierRcuUnlock).
    Definition sync_rcu : event := EAgent 2 0 (LBarrier BarrierSyncRcu).

    Example init_write_classification :
      is_initial init_write /\ is_write init_write /\ is_memory init_write /\ ~ is_read init_write.
    Proof. done. Qed.

    Example once_read_observers :
      access_mode_of once_read = Some AccessOnce /\
      location_of once_read = Some 1 /\
      value_of once_read = Some 7%Z.
    Proof. done. Qed.

    Example rmw_annotations_are_syntactic :
      is_rmw_marked rmw_read /\ is_read rmw_read /\ is_rmw_marked rmw_write /\ is_write rmw_write.
    Proof. done. Qed.

    (** A lone marked read is a valid event value.  The execution's [rmw]
        relation determines whether it is a failed conditional RMW. *)
    Example lone_rmw_read_is_representable : is_rmw_marked rmw_read.
    Proof. done. Qed.

    Example rcu_barriers_are_distinct :
      is_rcu_lock rcu_lock /\ is_rcu_unlock rcu_unlock /\ is_sync_rcu sync_rcu.
    Proof. done. Qed.

    Definition event_set_smoke : gset event :=
      {[init_write; once_read; rmw_read; rmw_write; rcu_lock; rcu_unlock; sync_rcu]}.

    Example once_read_in_event_set : once_read ∈ event_set_smoke.
    Proof. set_solver. Qed.
  End EventTests.

End LkmmEvents.
