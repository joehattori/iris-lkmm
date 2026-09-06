From Stdlib Require Import List ZArith.
From stdpp Require Import fin_maps gmap sorting tactics.
From iris_lkmm.lkmm Require Import execution.
Import ListNotations.

(** A finite, loop-free core language for the selected LKMM fragment.

    It records dependency provenance while it executes and leaves [rf] and
    [co] to the candidate-execution layer. *)
Module LkmmCore.
  Export LkmmExecution.
  Open Scope Z_scope.
  Open Scope stdpp_scope.

  Definition reg := nat.
  Definition origins := gset event_id.

  Record reg_value := RegValue {
    reg_integer : Z;
    reg_origins : origins
  }.

  Definition registers := gmap reg reg_value.

  Inductive binop :=
  | OpAdd
  | OpSub
  | OpXor
  | OpAnd
  | OpOr.

  Inductive expr :=
  | EConst (z : Z)
  | EReg (r : reg)
  | EBin (op : binop) (left right : expr).

  Definition eval_binop (op : binop) (lhs rhs : Z) : Z :=
    match op with
    | OpAdd => lhs + rhs
    | OpSub => lhs - rhs
    | OpXor => Z.lxor lhs rhs
    | OpAnd => Z.land lhs rhs
    | OpOr => Z.lor lhs rhs
    end.

  Fixpoint eval_expr (regs : registers) (expression : expr) : option reg_value :=
    match expression with
    | EConst z => Some (RegValue z ∅)
    | EReg r => regs !! r
    | EBin op lhs rhs =>
        match eval_expr regs lhs, eval_expr regs rhs with
        | Some left_value, Some right_value =>
            Some (RegValue
              (eval_binop op left_value.(reg_integer) right_value.(reg_integer))
              (left_value.(reg_origins) ∪ right_value.(reg_origins)))
        | _, _ => None
        end
    end.

  Definition eval_location (regs : registers) (expression : expr) : option (location * origins) :=
    match eval_expr regs expression with
    | Some result =>
        if decide (0 <= result.(reg_integer))
        then Some (Z.to_nat result.(reg_integer), result.(reg_origins))
        else None
    | None => None
    end.

  Inductive load_mode := LoadOnce | LoadAcquire.

  Inductive store_mode := StoreOnce | StoreRelease.

  Inductive rmw_mode :=
  | RmwRelaxed
  | RmwAcquire
  | RmwRelease
  | RmwFull.

  Inductive atomic_op :=
  | AtomicAdd
  | AtomicSub
  | AtomicAnd
  | AtomicOr
  | AtomicXor.

  Inductive fence_kind :=
  | FenceMb
  | FenceRmb
  | FenceWmb
  | FenceBeforeAtomic
  | FenceAfterAtomic.

  Inductive stmt :=
  | SSkip
  | SSeq (first second : stmt)
  | SAssign (dst : reg) (value : expr)
  | SIf (condition : expr) (then_branch else_branch : stmt)
  | SLoad (dst : reg) (mode : load_mode) (address : expr)
  | SStore (mode : store_mode) (address value : expr)
  | SXchg (dst : reg) (mode : rmw_mode) (address value : expr)
  | SCmpxchg (dst : reg) (mode : rmw_mode) (address expected desired : expr)
  | SAtomicFetch (dst : reg) (mode : rmw_mode) (op : atomic_op) (address argument : expr)
  | SAtomicReturn (dst : reg) (mode : rmw_mode) (op : atomic_op) (address argument : expr)
  | SAtomicNoReturn (op : atomic_op) (address argument : expr)
  | SFence (kind : fence_kind)
  | SRcuReadLock
  | SRcuReadUnlock
  | SSynchronizeRcu.

  Definition smp_store_mb (address value : expr) : stmt :=
    SSeq (SStore StoreOnce address value) (SFence FenceMb).

  Record core_program := CoreProgram {
    program_initial_memory : gmap location value;
    program_agents : gmap agent_id stmt
  }.

  Inductive frame :=
  | KSeq (next : stmt)
  | KControl (condition_origins : origins).

  Record thread_state := ThreadState {
    thread_statement : stmt;
    thread_continuation : list frame;
    thread_registers : registers
  }.

  Definition initial_thread (body : stmt) : thread_state := ThreadState body [] ∅.

  Fixpoint control_origins (continuation : list frame) : origins :=
    match continuation with
    | [] => ∅
    | KSeq _ :: continuation => control_origins continuation
    | KControl condition :: continuation => condition ∪ control_origins continuation
    end.

  Definition thread_control_origins (thread : thread_state) : origins :=
    control_origins thread.(thread_continuation).

  Definition load_access_mode (mode : load_mode) : access_mode :=
    match mode with LoadOnce => AccessOnce | LoadAcquire => AccessAcquire end.

  Definition store_access_mode (mode : store_mode) : access_mode :=
    match mode with StoreOnce => AccessOnce | StoreRelease => AccessRelease end.

  Definition rmw_access_mode (mode : rmw_mode) : access_mode :=
    match mode with
    | RmwRelaxed => AccessOnce
    | RmwAcquire => AccessAcquire
    | RmwRelease => AccessRelease
    | RmwFull => AccessMb
    end.

  Definition fence_barrier_kind (kind : fence_kind) : barrier_kind :=
    match kind with
    | FenceMb => BarrierMb
    | FenceRmb => BarrierRmb
    | FenceWmb => BarrierWmb
    | FenceBeforeAtomic => BarrierBeforeAtomic
    | FenceAfterAtomic => BarrierAfterAtomic
    end.

  Definition apply_atomic_op (op : atomic_op) (old argument : Z) : Z :=
    match op with
    | AtomicAdd => old + argument
    | AtomicSub => old - argument
    | AtomicAnd => Z.land old argument
    | AtomicOr => Z.lor old argument
    | AtomicXor => Z.lxor old argument
    end.

  Definition origin_edges (sources : origins) (target : event_id) : edge_set :=
    list_to_set ((fun source => (source, target)) <$> elements sources).

  Definition add_origin_edges (edges : edge_set) (sources : origins)
      (target : event_id) : edge_set :=
    edges ∪ origin_edges sources target.

  Definition add_control_edges (edges : edge_set) (thread : thread_state)
      (target : event_id) : edge_set :=
    add_origin_edges edges (thread_control_origins thread) target.

  Record core_state := CoreState {
    core_threads : gmap agent_id thread_state;
    core_next_id : event_id;
    core_next_indices : gmap agent_id event_index;
    core_events : event_structure;
    core_rmw : edge_set;
    core_direct_addr : edge_set;
    core_direct_data : edge_set;
    core_direct_ctrl : edge_set
  }.

  Definition next_agent_index (state : core_state) (agent : agent_id) : event_index :=
    default 0%nat (state.(core_next_indices) !! agent).

  Definition location_initialized (P : core_program) (loc : location) : Prop :=
    is_Some (P.(program_initial_memory) !! loc).

  Fixpoint insert_initial_events (entries : list (location * value))
      (next : event_id) (events : event_structure) : event_structure :=
    match entries with
    | [] => events
    | (loc, val) :: entries =>
        insert_initial_events entries (S next) (<[next := EInitWrite loc val]> events)
    end.

  Definition initial_entry_le (left right : location * value) : Prop :=
    (fst left <= fst right)%nat.

  Global Instance initial_entry_le_dec left right : Decision (initial_entry_le left right).
  Proof. unfold initial_entry_le. apply _. Defined.

  Global Instance initial_entry_le_total : Total initial_entry_le.
  Proof. intros [left left_value] [right right_value]. unfold initial_entry_le. simpl. lia. Qed.

  Global Instance initial_entry_le_transitive : Transitive initial_entry_le.
  Proof.
    intros [x xv] [y yv] [z zv]. unfold initial_entry_le. simpl. lia.
  Qed.

  Definition initial_entries (P : core_program) : list (location * value) :=
    merge_sort initial_entry_le (map_to_list P.(program_initial_memory)).

  Lemma initial_entries_sorted P :
    StronglySorted initial_entry_le (initial_entries P).
  Proof. apply StronglySorted_merge_sort; typeclasses eauto. Qed.

  Lemma initial_entries_permutation P :
    initial_entries P ≡ₚ map_to_list P.(program_initial_memory).
  Proof. apply merge_sort_Permutation. Qed.

  Definition core_initial_events (P : core_program) : event_structure :=
    insert_initial_events (initial_entries P) 0%nat ∅.

  Definition core_initial_state (P : core_program) : core_state :=
    CoreState
      (initial_thread <$> P.(program_agents))
      (length (initial_entries P))
      ∅
      (core_initial_events P)
      ∅ ∅ ∅ ∅.

  Definition update_thread (state : core_state) (agent : agent_id)
      (thread : thread_state) : core_state :=
    CoreState
      (<[agent := thread]> state.(core_threads))
      state.(core_next_id)
      state.(core_next_indices)
      state.(core_events)
      state.(core_rmw)
      state.(core_direct_addr)
      state.(core_direct_data)
      state.(core_direct_ctrl).

  Definition emitted_thread (thread : thread_state) (regs : registers) : thread_state :=
    ThreadState SSkip thread.(thread_continuation) regs.

  Definition add_single_event (state : core_state) (agent : agent_id)
      (thread : thread_state) (label : event_label) (regs : registers)
      (address_sources data_sources control_sources : origins) : core_state :=
    let eid := state.(core_next_id) in
    let index := next_agent_index state agent in
    CoreState
      (<[agent := emitted_thread thread regs]> state.(core_threads))
      (S eid)
      (<[agent := S index]> state.(core_next_indices))
      (<[eid := EAgent agent index label]> state.(core_events))
      state.(core_rmw)
      (add_origin_edges state.(core_direct_addr) address_sources eid)
      (add_origin_edges state.(core_direct_data) data_sources eid)
      (add_origin_edges state.(core_direct_ctrl) control_sources eid).

  Definition add_rmw_events (state : core_state) (agent : agent_id)
      (thread : thread_state) (mode : access_mode) (loc : location)
      (old new : value) (regs : registers) (address_sources data_sources
        control_sources : origins) : core_state :=
    let read := state.(core_next_id) in
    let write := S read in
    let index := next_agent_index state agent in
    CoreState
      (<[agent := emitted_thread thread regs]> state.(core_threads))
      (S write)
      (<[agent := S (S index)]> state.(core_next_indices))
      (<[write := EAgent agent (S index)
          (LMemory AccessWrite mode RmwMarked loc new)]>
        (<[read := EAgent agent index
          (LMemory AccessRead mode RmwMarked loc old)]> state.(core_events)))
      ({[(read, write)]} ∪ state.(core_rmw))
      (add_origin_edges
        (add_origin_edges state.(core_direct_addr) address_sources read)
        address_sources write)
      (add_origin_edges state.(core_direct_data) data_sources write)
      (add_origin_edges state.(core_direct_ctrl) control_sources write).

  Inductive core_action :=
  | CoreSilent (agent : agent_id)
  | CoreEmit (agent : agent_id)
  | CoreObserve (agent : agent_id) (observed : value).

  Inductive core_step (P : core_program) : core_state -> core_action -> core_state -> Prop :=
  | StepSequence state agent thread first second :
      state.(core_threads) !! agent = Some thread ->
      thread.(thread_statement) = SSeq first second ->
      core_step P state (CoreSilent agent)
        (update_thread state agent
          (ThreadState first (KSeq second :: thread.(thread_continuation))
            thread.(thread_registers)))
  | StepSkipSequence state agent thread next continuation :
      state.(core_threads) !! agent = Some thread ->
      thread.(thread_statement) = SSkip ->
      thread.(thread_continuation) = KSeq next :: continuation ->
      core_step P state (CoreSilent agent)
        (update_thread state agent
          (ThreadState next continuation thread.(thread_registers)))
  | StepSkipControl state agent thread condition continuation :
      state.(core_threads) !! agent = Some thread ->
      thread.(thread_statement) = SSkip ->
      thread.(thread_continuation) = KControl condition :: continuation ->
      core_step P state (CoreSilent agent)
        (update_thread state agent
          (ThreadState SSkip continuation thread.(thread_registers)))
  | StepAssign state agent thread dst expression result :
      state.(core_threads) !! agent = Some thread ->
      thread.(thread_statement) = SAssign dst expression ->
      eval_expr thread.(thread_registers) expression = Some result ->
      core_step P state (CoreSilent agent)
        (update_thread state agent
          (ThreadState SSkip thread.(thread_continuation)
            (<[dst := result]> thread.(thread_registers))))
  | StepIfTrue state agent thread condition then_branch else_branch result :
      state.(core_threads) !! agent = Some thread ->
      thread.(thread_statement) = SIf condition then_branch else_branch ->
      eval_expr thread.(thread_registers) condition = Some result ->
      result.(reg_integer) <> 0 ->
      core_step P state (CoreSilent agent)
        (update_thread state agent
          (ThreadState then_branch
            (KControl result.(reg_origins) :: thread.(thread_continuation))
            thread.(thread_registers)))
  | StepIfFalse state agent thread condition then_branch else_branch result :
      state.(core_threads) !! agent = Some thread ->
      thread.(thread_statement) = SIf condition then_branch else_branch ->
      eval_expr thread.(thread_registers) condition = Some result ->
      result.(reg_integer) = 0 ->
      core_step P state (CoreSilent agent)
        (update_thread state agent
          (ThreadState else_branch
            (KControl result.(reg_origins) :: thread.(thread_continuation))
            thread.(thread_registers)))
  | StepLoad state agent thread dst mode address loc address_sources observed :
      state.(core_threads) !! agent = Some thread ->
      thread.(thread_statement) = SLoad dst mode address ->
      eval_location thread.(thread_registers) address = Some (loc, address_sources) ->
      location_initialized P loc ->
      let read := state.(core_next_id) in
      core_step P state (CoreObserve agent observed)
        (add_single_event state agent thread
          (LMemory AccessRead (load_access_mode mode) NotRmw loc observed)
          (<[dst := RegValue observed {[read]}]> thread.(thread_registers))
          address_sources ∅ ∅)
  | StepStore state agent thread mode address expression loc address_sources result :
      state.(core_threads) !! agent = Some thread ->
      thread.(thread_statement) = SStore mode address expression ->
      eval_location thread.(thread_registers) address = Some (loc, address_sources) ->
      eval_expr thread.(thread_registers) expression = Some result ->
      location_initialized P loc ->
      core_step P state (CoreEmit agent)
        (add_single_event state agent thread
          (LMemory AccessWrite (store_access_mode mode) NotRmw loc result.(reg_integer))
          thread.(thread_registers) address_sources result.(reg_origins)
          (thread_control_origins thread))
  | StepXchg state agent thread dst mode address expression loc address_sources result observed :
      state.(core_threads) !! agent = Some thread ->
      thread.(thread_statement) = SXchg dst mode address expression ->
      eval_location thread.(thread_registers) address = Some (loc, address_sources) ->
      eval_expr thread.(thread_registers) expression = Some result ->
      location_initialized P loc ->
      let read := state.(core_next_id) in
      core_step P state (CoreObserve agent observed)
        (add_rmw_events state agent thread (rmw_access_mode mode) loc
          observed result.(reg_integer)
          (<[dst := RegValue observed {[read]}]> thread.(thread_registers))
          address_sources result.(reg_origins) (thread_control_origins thread))
  | StepCmpxchgSuccess state agent thread dst mode address expected desired
      loc address_sources expected_result desired_result observed :
      state.(core_threads) !! agent = Some thread ->
      thread.(thread_statement) = SCmpxchg dst mode address expected desired ->
      eval_location thread.(thread_registers) address = Some (loc, address_sources) ->
      eval_expr thread.(thread_registers) expected = Some expected_result ->
      eval_expr thread.(thread_registers) desired = Some desired_result ->
      observed = expected_result.(reg_integer) ->
      location_initialized P loc ->
      let read := state.(core_next_id) in
      core_step P state (CoreObserve agent observed)
        (add_rmw_events state agent thread (rmw_access_mode mode) loc
          observed desired_result.(reg_integer)
          (<[dst := RegValue observed {[read]}]> thread.(thread_registers))
          address_sources desired_result.(reg_origins)
          ({[read]} ∪ expected_result.(reg_origins) ∪ thread_control_origins thread))
  | StepCmpxchgFailure state agent thread dst mode address expected desired
      loc address_sources expected_result desired_result observed :
      state.(core_threads) !! agent = Some thread ->
      thread.(thread_statement) = SCmpxchg dst mode address expected desired ->
      eval_location thread.(thread_registers) address = Some (loc, address_sources) ->
      eval_expr thread.(thread_registers) expected = Some expected_result ->
      eval_expr thread.(thread_registers) desired = Some desired_result ->
      observed <> expected_result.(reg_integer) ->
      location_initialized P loc ->
      let read := state.(core_next_id) in
      core_step P state (CoreObserve agent observed)
        (add_single_event state agent thread
          (LMemory AccessRead (rmw_access_mode mode) RmwMarked loc observed)
          (<[dst := RegValue observed {[read]}]> thread.(thread_registers))
          address_sources ∅ ∅)
  | StepAtomicFetch state agent thread dst mode op address argument loc
      address_sources argument_result observed :
      state.(core_threads) !! agent = Some thread ->
      thread.(thread_statement) = SAtomicFetch dst mode op address argument ->
      eval_location thread.(thread_registers) address = Some (loc, address_sources) ->
      eval_expr thread.(thread_registers) argument = Some argument_result ->
      location_initialized P loc ->
      let read := state.(core_next_id) in
      core_step P state (CoreObserve agent observed)
        (add_rmw_events state agent thread (rmw_access_mode mode) loc observed
          (apply_atomic_op op observed argument_result.(reg_integer))
          (<[dst := RegValue observed {[read]}]> thread.(thread_registers))
          address_sources ({[read]} ∪ argument_result.(reg_origins))
          (thread_control_origins thread))
  | StepAtomicReturn state agent thread dst mode op address argument loc
      address_sources argument_result observed :
      state.(core_threads) !! agent = Some thread ->
      thread.(thread_statement) = SAtomicReturn dst mode op address argument ->
      eval_location thread.(thread_registers) address = Some (loc, address_sources) ->
      eval_expr thread.(thread_registers) argument = Some argument_result ->
      location_initialized P loc ->
      let read := state.(core_next_id) in
      let new := apply_atomic_op op observed argument_result.(reg_integer) in
      core_step P state (CoreObserve agent observed)
        (add_rmw_events state agent thread (rmw_access_mode mode) loc observed new
          (<[dst := RegValue new {[read]}]> thread.(thread_registers))
          address_sources ({[read]} ∪ argument_result.(reg_origins))
          (thread_control_origins thread))
  | StepAtomicNoReturn state agent thread op address argument loc
      address_sources argument_result observed :
      state.(core_threads) !! agent = Some thread ->
      thread.(thread_statement) = SAtomicNoReturn op address argument ->
      eval_location thread.(thread_registers) address = Some (loc, address_sources) ->
      eval_expr thread.(thread_registers) argument = Some argument_result ->
      location_initialized P loc ->
      let read := state.(core_next_id) in
      core_step P state (CoreObserve agent observed)
        (add_rmw_events state agent thread AccessNoreturn loc observed
          (apply_atomic_op op observed argument_result.(reg_integer))
          thread.(thread_registers)
          address_sources ({[read]} ∪ argument_result.(reg_origins))
          (thread_control_origins thread))
  | StepFence state agent thread kind :
      state.(core_threads) !! agent = Some thread ->
      thread.(thread_statement) = SFence kind ->
      core_step P state (CoreEmit agent)
        (add_single_event state agent thread (LBarrier (fence_barrier_kind kind))
          thread.(thread_registers) ∅ ∅ ∅)
  | StepRcuReadLock state agent thread :
      state.(core_threads) !! agent = Some thread ->
      thread.(thread_statement) = SRcuReadLock ->
      core_step P state (CoreEmit agent)
        (add_single_event state agent thread (LBarrier BarrierRcuLock)
          thread.(thread_registers) ∅ ∅ ∅)
  | StepRcuReadUnlock state agent thread :
      state.(core_threads) !! agent = Some thread ->
      thread.(thread_statement) = SRcuReadUnlock ->
      core_step P state (CoreEmit agent)
        (add_single_event state agent thread (LBarrier BarrierRcuUnlock)
          thread.(thread_registers) ∅ ∅ ∅)
  | StepSynchronizeRcu state agent thread :
      state.(core_threads) !! agent = Some thread ->
      thread.(thread_statement) = SSynchronizeRcu ->
      core_step P state (CoreEmit agent)
        (add_single_event state agent thread (LBarrier BarrierSyncRcu)
          thread.(thread_registers) ∅ ∅ ∅).

  Inductive core_run (P : core_program) :
      core_state -> list core_action -> core_state -> Prop :=
  | CoreRunNil state : core_run P state [] state
  | CoreRunCons state1 state2 state3 action actions :
      core_step P state1 action state2 ->
      core_run P state2 actions state3 ->
      core_run P state1 (action :: actions) state3.

  Definition thread_complete (thread : thread_state) : Prop :=
    thread.(thread_statement) = SSkip /\ thread.(thread_continuation) = [].

  Definition core_complete (state : core_state) : Prop :=
    forall agent thread,
      state.(core_threads) !! agent = Some thread -> thread_complete thread.

  Definition complete_core_run (P : core_program) (actions : list core_action)
      (state : core_state) : Prop :=
    core_run P (core_initial_state P) actions state /\ core_complete state.

  Definition allocated_ids_below (state : core_state) : Prop :=
    forall eid ev,
      lookup_event state.(core_events) eid = Some ev ->
      (eid < state.(core_next_id))%nat.

  Definition allocated_indices_below (state : core_state) : Prop :=
    forall eid agent index label,
      lookup_event state.(core_events) eid = Some (EAgent agent index label) ->
      (index < next_agent_index state agent)%nat.

  Definition core_allocation_wf (state : core_state) : Prop :=
    event_structure_wf state.(core_events) /\
    allocated_ids_below state /\
    allocated_indices_below state.

  Lemma core_next_id_fresh state :
    core_allocation_wf state ->
    lookup_event state.(core_events) state.(core_next_id) = None.
  Proof.
    intros (_ & Hids & _). apply eq_None_not_Some. intros [ev Hlookup].
    specialize (Hids _ _ Hlookup). lia.
  Qed.

  Lemma insert_initial_events_shape entries next events eid ev :
    (forall old_id old_event,
      lookup_event events old_id = Some old_event ->
      exists loc val, old_event = EInitWrite loc val) ->
    lookup_event (insert_initial_events entries next events) eid = Some ev ->
    exists loc val, ev = EInitWrite loc val.
  Proof.
    revert next events eid ev. induction entries as [|[loc val] entries IH];
      intros next events eid ev Hshape Hlookup; simpl in *.
    - by eapply Hshape.
    - eapply IH; last exact Hlookup.
      intros old_id old_event Hlookup_old. unfold lookup_event in Hlookup_old.
      apply lookup_insert_Some in Hlookup_old as
        [[Hold_id Hold_event] | [_ Hlookup_old]].
      + subst old_id. subst old_event. by exists loc, val.
      + by eapply Hshape.
  Qed.

  Lemma insert_initial_events_ids_below entries next events :
    (forall eid ev,
      lookup_event events eid = Some ev -> (eid < next)%nat) ->
    forall eid ev,
      lookup_event (insert_initial_events entries next events) eid = Some ev ->
      (eid < next + length entries)%nat.
  Proof.
    revert next events. induction entries as [|[loc val] entries IH];
      intros next events Hbelow eid ev Hlookup; simpl in *.
    - specialize (Hbelow eid ev Hlookup). lia.
    - assert (forall old_id old_event,
          lookup_event (<[next := EInitWrite loc val]> events) old_id = Some old_event ->
          (old_id < S next)%nat) as Hbelow_insert.
      { intros old_id old_event Hlookup_old. unfold lookup_event in Hlookup_old.
        apply lookup_insert_Some in Hlookup_old as
          [[Hold_id Hold_event] | [_ Hlookup_old]].
        - subst old_id. lia.
        - specialize (Hbelow old_id old_event Hlookup_old). lia. }
      pose proof (IH (S next) (<[next := EInitWrite loc val]> events)
        Hbelow_insert eid ev Hlookup) as Hresult.
      lia.
  Qed.

  Lemma core_initial_allocation_wf P : core_allocation_wf (core_initial_state P).
  Proof.
    split_and!.
    - intros eid1 eid2 agent index label1 label2 Hlookup1.
      pose proof (insert_initial_events_shape (initial_entries P) 0%nat ∅
        eid1 (EAgent agent index label1)) as Hshape.
      specialize (Hshape ltac:(intros; simplify_map_eq) Hlookup1).
      destruct Hshape as (loc & val & Hshape). discriminate Hshape.
    - intros eid ev Hlookup. simpl in *.
      assert (forall empty_id empty_event,
          lookup_event (∅ : event_structure) empty_id = Some empty_event ->
          (empty_id < 0)%nat) as Hempty.
      { intros empty_id empty_event Hempty. simpl in Hempty. discriminate. }
      pose proof (insert_initial_events_ids_below
        (initial_entries P) 0%nat ∅ Hempty
        eid ev Hlookup) as Hbelow.
      lia.
    - intros eid agent index label Hlookup. simpl in *.
      pose proof (insert_initial_events_shape (initial_entries P) 0%nat ∅
        eid (EAgent agent index label)) as Hshape.
      specialize (Hshape ltac:(intros; simplify_map_eq) Hlookup).
      destruct Hshape as (loc & val & Hshape). discriminate Hshape.
  Qed.

  Lemma add_single_event_allocation_wf state agent thread label regs
      address_sources data_sources control_sources :
    core_allocation_wf state ->
    core_allocation_wf
      (add_single_event state agent thread label regs
        address_sources data_sources control_sources).
  Proof.
    intros (Hevents & Hids & Hindices).
    split_and!.
    - intros eid1 eid2 event_agent index label1 label2 Hlookup1 Hlookup2.
      simpl in Hlookup1, Hlookup2. unfold lookup_event in Hlookup1, Hlookup2.
      apply lookup_insert_Some in Hlookup1 as [[Heid1 Hevent1] | [Hne1 Hlookup1]];
        apply lookup_insert_Some in Hlookup2 as [[Heid2 Hevent2] | [Hne2 Hlookup2]].
      + congruence.
      + subst eid1. injection Hevent1 as <- <- <-.
        specialize (Hindices _ _ _ _ Hlookup2). unfold next_agent_index in Hindices.
        lia.
      + subst eid2. injection Hevent2 as <- <- <-.
        specialize (Hindices _ _ _ _ Hlookup1). unfold next_agent_index in Hindices.
        lia.
      + by eapply Hevents.
    - intros eid ev Hlookup. simpl in Hlookup |- *. unfold lookup_event in Hlookup.
      apply lookup_insert_Some in Hlookup as [[Heid Hevent] | [_ Hlookup]].
      + subst eid. lia.
      + specialize (Hids _ _ Hlookup). lia.
    - intros eid event_agent index event_label Hlookup. simpl in Hlookup |- *.
      unfold lookup_event in Hlookup.
      apply lookup_insert_Some in Hlookup as [[Heid Hevent] | [_ Hlookup]].
      + subst eid. injection Hevent as <- <- <-.
        unfold next_agent_index. simplify_map_eq. unfold next_agent_index. lia.
      + specialize (Hindices _ _ _ _ Hlookup).
        unfold next_agent_index in Hindices |- *.
        destruct (decide (event_agent = agent)) as [-> | Hne].
        * simplify_map_eq. unfold next_agent_index. lia.
        * simplify_map_eq. unfold next_agent_index. done.
  Qed.

  Lemma add_rmw_events_allocation_wf state agent thread mode loc old new regs
      address_sources data_sources control_sources :
    core_allocation_wf state ->
    core_allocation_wf
      (add_rmw_events state agent thread mode loc old new regs
        address_sources data_sources control_sources).
  Proof.
    intros (Hevents & Hids & Hindices).
    split_and!.
    - intros eid1 eid2 event_agent index label1 label2 Hlookup1 Hlookup2.
      simpl in Hlookup1, Hlookup2. unfold lookup_event in Hlookup1, Hlookup2.
      assert (forall eid ev,
          (<[S (core_next_id state) :=
              EAgent agent (S (next_agent_index state agent))
                (LMemory AccessWrite mode RmwMarked loc new)]>
            (<[core_next_id state :=
              EAgent agent (next_agent_index state agent)
                (LMemory AccessRead mode RmwMarked loc old)]>
              state.(core_events))) !! eid = Some ev ->
          (eid = S state.(core_next_id) /\
            ev = EAgent agent (S (next_agent_index state agent))
              (LMemory AccessWrite mode RmwMarked loc new)) \/
          (eid = state.(core_next_id) /\
            ev = EAgent agent (next_agent_index state agent)
              (LMemory AccessRead mode RmwMarked loc old)) \/
          lookup_event state.(core_events) eid = Some ev) as Hcases.
      { intros eid ev Hlookup.
        apply lookup_insert_Some in Hlookup as [Hwrite | [_ Hlookup]].
        - left. naive_solver.
        - apply lookup_insert_Some in Hlookup as [Hread | [_ Hlookup]].
          + right. left. naive_solver.
          + right. right. done. }
      specialize (Hcases _ _ Hlookup1) as Hlookup1'.
      specialize (Hcases _ _ Hlookup2) as Hlookup2'.
      destruct Hlookup1' as
        [[Heid1 Hevent1] | [[Heid1 Hevent1] | Hlookup1_old]];
        destruct Hlookup2' as
        [[Heid2 Hevent2] | [[Heid2 Hevent2] | Hlookup2_old]].
      + congruence.
      + naive_solver lia.
      + specialize (Hindices _ _ _ _ Hlookup2_old).
        naive_solver lia.
      + naive_solver lia.
      + congruence.
      + specialize (Hindices _ _ _ _ Hlookup2_old).
        naive_solver lia.
      + specialize (Hindices _ _ _ _ Hlookup1_old).
        naive_solver lia.
      + specialize (Hindices _ _ _ _ Hlookup1_old).
        naive_solver lia.
      + by eapply Hevents.
    - intros eid ev Hlookup. simpl in Hlookup |- *. unfold lookup_event in Hlookup.
      apply lookup_insert_Some in Hlookup as [[Heid Hevent] | [_ Hlookup]].
      + subst eid. lia.
      + apply lookup_insert_Some in Hlookup as [[Heid Hevent] | [_ Hlookup]].
        * subst eid. lia.
        * specialize (Hids _ _ Hlookup). lia.
    - intros eid event_agent index event_label Hlookup. simpl in Hlookup |- *.
      unfold lookup_event in Hlookup.
      apply lookup_insert_Some in Hlookup as [[Heid Hevent] | [_ Hlookup]].
      + subst eid. injection Hevent as <- <- <-.
        unfold next_agent_index. simplify_map_eq. unfold next_agent_index. lia.
      + apply lookup_insert_Some in Hlookup as [[Heid Hevent] | [_ Hlookup]].
        * subst eid. injection Hevent as <- <- <-.
          unfold next_agent_index. simplify_map_eq. unfold next_agent_index. lia.
        * specialize (Hindices _ _ _ _ Hlookup).
          unfold next_agent_index in Hindices |- *.
          destruct (decide (event_agent = agent)) as [-> | Hne].
          -- simplify_map_eq. unfold next_agent_index. lia.
          -- simplify_map_eq. unfold next_agent_index. done.
  Qed.

  Theorem core_step_preserves_allocation P state action state' :
    core_step P state action state' ->
    core_allocation_wf state ->
    core_allocation_wf state'.
  Proof.
    intros Hstep Hwf. destruct Hstep; simpl;
      try (apply add_single_event_allocation_wf; exact Hwf);
      try (apply add_rmw_events_allocation_wf; exact Hwf);
      exact Hwf.
  Qed.

  Lemma core_run_preserves_allocation P state actions state' :
    core_run P state actions state' ->
    core_allocation_wf state ->
    core_allocation_wf state'.
  Proof.
    intros Hrun Hwf. induction Hrun; first done.
    apply IHHrun. by eapply core_step_preserves_allocation.
  Qed.

  Theorem core_run_allocation_wf P actions state :
    core_run P (core_initial_state P) actions state ->
    core_allocation_wf state.
  Proof.
    intros Hrun. eapply core_run_preserves_allocation; first exact Hrun.
    apply core_initial_allocation_wf.
  Qed.

  Lemma eval_expr_constant regs z : eval_expr regs (EConst z) = Some (RegValue z ∅).
  Proof. done. Qed.

  Lemma eval_location_negative regs expression result :
    eval_expr regs expression = Some result ->
    result.(reg_integer) < 0 ->
    eval_location regs expression = None.
  Proof.
    intros Heval Hnegative. unfold eval_location. rewrite Heval.
    destruct (decide (0 <= reg_integer result)) as [Hnonnegative |]; last done.
    exfalso. lia.
  Qed.

  Lemma uninitialized_register_blocks r expression :
    (∅ : registers) !! r = None ->
    eval_expr ∅ (EBin OpAdd (EReg r) expression) = None.
  Proof. intros Hlookup. simpl. by rewrite Hlookup. Qed.

  Close Scope Z_scope.

  Module CoreDependencyTests.
    Definition body : stmt :=
      SSeq (SLoad 0 LoadOnce (EConst 0))
        (SSeq (SAssign 1 (EBin OpAdd (EReg 0) (EConst (-1))))
          (SSeq
            (SIf (EReg 0)
              (SIf (EReg 0)
                (SStore StoreOnce (EReg 1) (EReg 0))
                SSkip)
              SSkip)
            (SStore StoreOnce (EConst 0) (EConst 0)))).

    Definition program : core_program := CoreProgram {[0%nat := 0%Z]} {[0%nat := body]}.

    Definition actions : list core_action :=
      [CoreSilent 0; CoreObserve 0 1%Z; CoreSilent 0; CoreSilent 0;
       CoreSilent 0; CoreSilent 0; CoreSilent 0; CoreSilent 0;
       CoreSilent 0; CoreEmit 0; CoreSilent 0; CoreSilent 0;
       CoreSilent 0; CoreEmit 0].

    Example dependency_provenance_run :
      exists state,
        complete_core_run program actions state /\
        state.(core_direct_addr) = {[(1, 2)]} /\
        state.(core_direct_data) = {[(1, 2)]} /\
        state.(core_direct_ctrl) = {[(1, 2)]}.
    Proof.
      eexists. split.
      - split.
        + eapply CoreRunCons.
          { eapply StepSequence; reflexivity. }
          eapply CoreRunCons.
          { eapply StepLoad; try reflexivity. by eexists. }
          eapply CoreRunCons.
          { eapply StepSkipSequence; reflexivity. }
          eapply CoreRunCons.
          { eapply StepSequence; reflexivity. }
          eapply CoreRunCons.
          { eapply StepAssign; reflexivity. }
          eapply CoreRunCons.
          { eapply StepSkipSequence; reflexivity. }
          eapply CoreRunCons.
          { eapply StepSequence; reflexivity. }
          eapply CoreRunCons.
          { eapply StepIfTrue; try reflexivity; discriminate. }
          eapply CoreRunCons.
          { eapply StepIfTrue; try reflexivity; discriminate. }
          eapply CoreRunCons.
          { eapply StepStore; try reflexivity. by eexists. }
          eapply CoreRunCons.
          { eapply StepSkipControl; reflexivity. }
          eapply CoreRunCons.
          { eapply StepSkipControl; reflexivity. }
          eapply CoreRunCons.
          { eapply StepSkipSequence; reflexivity. }
          eapply CoreRunCons.
          { eapply StepStore; try reflexivity. by eexists. }
          constructor.
        + intros agent thread Hlookup. unfold thread_complete.
          destruct (decide (agent = 0)) as [-> | Hne].
          * simpl in Hlookup. injection Hlookup as <-. done.
          * simpl in Hlookup. simplify_map_eq.
      - simpl. split_and!; apply set_eq; intros edge; set_solver.
    Qed.

    Example blocked_expressions :
      eval_location ∅ (EConst (-1)) = None /\
      eval_expr ∅ (EReg 0) = None.
    Proof. split; reflexivity. Qed.
  End CoreDependencyTests.

  Module CoreRmwTests.
    Definition program : core_program := CoreProgram {[0%nat := 0%Z]} ∅.

    Definition state_for (body : stmt) : core_state :=
      CoreState {[0%nat := initial_thread body]} 0 ∅ ∅ ∅ ∅ ∅ ∅.

    Example rmw_instruction_steps :
      (exists state,
        core_step program
          (state_for (SXchg 0 RmwRelaxed (EConst 0) (EConst 5)))
          (CoreObserve 0 0%Z) state /\
        state.(core_rmw) = {[(0, 1)]} /\
        lookup_event state.(core_events) 1 =
          Some (EAgent 0 1 (LMemory AccessWrite AccessOnce RmwMarked 0 5%Z))) /\
      (exists state,
        core_step program
          (state_for (SCmpxchg 0 RmwAcquire (EConst 0) (EConst 5) (EConst 6)))
          (CoreObserve 0 5%Z) state /\
        state.(core_rmw) = {[(0, 1)]} /\
        state.(core_direct_ctrl) = {[(0, 1)]}) /\
      (exists state,
        core_step program
          (state_for (SCmpxchg 0 RmwRelease (EConst 0) (EConst 5) (EConst 6)))
          (CoreObserve 0 7%Z) state /\
        state.(core_rmw) = ∅ /\
        lookup_event state.(core_events) 0 =
          Some (EAgent 0 0 (LMemory AccessRead AccessRelease RmwMarked 0 7%Z))) /\
      (exists state,
        core_step program
          (state_for (SAtomicReturn 0 RmwFull AtomicAdd (EConst 0) (EConst 1)))
          (CoreObserve 0 6%Z) state /\
        state.(core_rmw) = {[(0, 1)]} /\
        state.(core_direct_data) = {[(0, 1)]} /\
        lookup_event state.(core_events) 1 =
          Some (EAgent 0 1 (LMemory AccessWrite AccessMb RmwMarked 0 7%Z))).
    Proof.
      split_and!.
      - eexists. split; first by eapply StepXchg; try reflexivity; eexists.
        split; reflexivity.
      - eexists. split; first by eapply StepCmpxchgSuccess; try reflexivity; eexists.
        split; [reflexivity | apply set_eq; intros edge; set_solver].
      - eexists. split; first by eapply StepCmpxchgFailure;
          try reflexivity; [discriminate | eexists].
        split; reflexivity.
      - eexists. split; first by eapply StepAtomicReturn; try reflexivity; eexists.
        split_and!; reflexivity.
    Qed.
  End CoreRmwTests.

End LkmmCore.
