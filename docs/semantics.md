# Incremental RCU prototype semantics

The prototype language has fixed agents and five instructions: `read`,
`write`, `rcu_read_lock`, `rcu_read_unlock`, and `synchronize_rcu`.
Its syntax and canonical event-label translation live in `lkmm_lang.v`; the
operational state and transitions in `rcu_machine.v` consume that language.
It remains intentionally smaller than the LKMM-Core language in
`lkmm_core.v`.

## LKMM-Core and concrete program graphs

`lkmm_core.v` adds a separate finite, loop-free language with registers,
structured sequencing and conditionals, memory accesses, RMW operations,
fences, and normal-RCU operations.  Expressions evaluate to an integer and
the set of read-event origins that contributed to it.  Those origins generate
the finite direct address, data, and control dependency relations; an active
structured-control frame contributes only while its selected branch executes.

The core small-step machine assigns every emitted event a fresh global ID and
a fresh per-agent index.  Loads and RMW reads nondeterministically choose an
observed value.  Successful RMWs emit their marked read and write together and
record the pairing; failed `cmpxchg` emits only its marked read.  Initial writes
are generated from the finite initial-memory map in ascending location order.
The allocation invariant proves unique per-agent positions and globally fresh
event IDs for every core run.

`program_graph.v` defines the base-only `core_candidate` and the declarative
`program_graph` relation.  A program graph contains a complete core run whose
events, RMW pairs, and direct dependencies exactly equal the candidate fields.
The candidate's `rf` and `co` relations are not machine state: they range over
all finite choices satisfying their relational well-formedness predicates.
This connects nondeterministically observed read values to writes while still
allowing future writes to justify earlier observations.

`lkmm_consistent` is deliberately separate from `program_graph`.  It conjoins
coherence, atomicity, happens-before acyclicity, propagation acyclicity, and
normal-RCU consistency over an adapter whose `hb` and `pb` are derived from the
candidate's dependency edges.  The existing abstract-`hb`/`pb` feasibility
graph remains intact for the already-proved gate results.

Each ordinary instruction appends a fresh event.  Lock events are pushed onto
a per-agent stack; unlock events pop the stack and append a matched critical
section.  This handles nested read-side sections syntactically, without alias
analysis.

`synchronize_rcu` has two internal transitions:

1. **Begin** snapshots the lock-event identifiers currently open on the fixed
   agent set.  It emits no graph event and does not advance the program
   counter.
2. **Finish** is enabled when every identifier in that immutable snapshot has
   appeared as the lock endpoint of a closed critical section.  It emits the
   grace-period event, advances the program counter, and stores a certificate.

A reader that starts after Begin is not in the snapshot and therefore cannot
delay that grace period.  A nested reader already open at Begin is a separate
captured obligation.

The proved invariant `operational_soundness` says that every stored
grace-period certificate refers only to sections that have closed.
`finish_gp_complete` proves that discharging the captured obligations is
sufficient to take the finish transition.  Neither theorem invokes
`rcu_consistent` or inspects a completed graph.

## Independent graph-chain invariant

`execution_graph.v` defines the RCU-independent feasibility graph containing
canonical events, finite candidate `rf`, `co`, and `rmw` edge sets, and abstract
`hb` and `pb` relations.  Its `prop` relation is derived from the canonical events
and finite candidate edges.  It is a minimal shared graph view, not yet the final
LKMM candidate-execution type.  `rcu_graph.v` adds the normal-RCU classifications
and consistency condition.

The graph kernel also has an operationally useful, nonrecursive
characterization of `rcu-order`.  An RCU chain is a nonempty list whose atoms
are either:

- a grace-period event, with identical start and end and balance `+1`; or
- an inverse matched critical section, from unlock to lock, with balance
  `-1`.

Every adjacent pair must be connected by `rcu-link`.  A completed chain is
accepted when the sum of its atom balances is nonnegative.  This is a final
balance condition, not a prefix condition: the valid
`inverse-RSCS ; rcu-link ; GP` chain has balances `[-1, +1]`.

Append composes both the link witnesses and balances.  The mechanized theorem
`rcu_order_chain_equiv` proves that this invariant recognizes exactly the
normal-RCU recursive `rcu-order` relation.

## Machine-to-chain refinement

`event_integrity` records that every lock on an open stack, both endpoints
of every closed section, and every completed GP certificate are backed by
events emitted by the machine.  It also states that the operational stack
and closed-section cache agree with the canonical stack matcher.
`operational_event_integrity` proves this for every reachable state.

`graph_of_state` uses the machine's canonical event map directly.  Program
order, GP classification, `Marked`, and inverse critical-section matching are
derived from that map; the finite `rf`, `co`, and `rmw` candidates and abstract
`hb` and `pb` relations are supplied by the `abstract_relations` parameter.
Propagation is derived from the event map and candidate `rf`, `co`, and `rmw` edges.

`certificate_covers s cert cs` says that:

- `cert` is a completed GP certificate;
- `cs` is a completed critical section; and
- the lock endpoint of `cs` occurred in the GP's immutable begin snapshot.

`completed_run_snapshot_chain_bridge` proves that every captured lock in
every completed certificate resolves to such a section.  It proves the GP
and inverse-RSCS atoms valid in the extracted graph and provides both
implications:

```text
rcu-link(lock, gp)   -> chain [RSCS(unlock, lock), GP(gp)]
rcu-link(gp, unlock) -> chain [GP(gp), RSCS(unlock, lock)]
```

The theorem does not assume or synthesize those links.  Their incremental
construction is handled by the graph builder below.

## Incremental graph builder

`rcu_builder.v` represents the finite graph as a canonical event map and
explicit `rf`, `co`, `rmw`, `hb`, and `pb` edge lists.  A raw mutation
adds exactly one of:

- a fresh canonical event at a per-agent tail position; or
- one `rf`, `co`, `rmw`, `hb`, or `pb` edge.

Program order, propagation, and RCU matching are derived from the graph and are
not builder transitions.

A `rcu_link_commitment` records all four intermediate events witnessing
`po? ; hb* ; pb* ; prop ; po`.  `rcu_link_commitment_sound` proves that a
valid commitment denotes `rcu_link`; `rcu_link_commitment_complete` proves
that every `rcu_link` has such a record; and `commit_ready_rcu_link` permits
the commitment only after all of its component paths are present.  Graph
monotonicity proves that an already committed link remains valid as later
facts are added.

For a raw mutation, the builder also supplies an `rb` delta satisfying:

```text
rb(new graph) = seen-rb ∪ delta
irreflexive(delta)
```

The transition refers only to the current state, the one-step successor, and
the delta.  It has no final candidate and no `rcu_consistent` premise.
`builder_invariant` proves that `seen-rb` is exactly the current graph's `rb`,
that it is irreflexive, and that all stored link witnesses remain valid.
Consequently, `completed_builder_run_rb_irreflexive` proves
`rcu_consistent` for every finite builder run from `initial_builder`.

## Independent candidates and finite scheduling

`finite_candidate` is a declarative record of event-ID/canonical-event pairs
and five edge lists.  It contains no operational state,
delta, transition list, or schedule.  `candidate_well_formed` requires unique
event identifiers, canonical per-agent ordering, `event_structure_wf`,
complete RCU matching, and relation endpoints in the event set.

`candidate_has_raw_schedule` enumerates those finite components one at a
time.  `lift_safe_raw_schedule` turns that enumeration into builder steps by
partitioning each successor's `rb` relation into previously seen and new
pairs.  Monotonicity of `rb` and consistency of the final candidate prove
that each new delta is locally irreflexive.

The resulting completeness theorem is:

```text
candidate_well_formed(C) /\ rcu_consistent(candidate_graph(C))
->
exists s,
  builder_run(initial_builder, s) /\
  graph(s) = candidate_graph(C)
```

The initial builder is one fixed empty constant and has no field in which a
candidate or its future choices could be preloaded.  The proof is a
candidate-directed existence proof, as operational completeness normally is;
the transition relation itself never receives the final candidate.

## Coupled delayed-commitment execution

`rcu_coupled.v` combines program-machine steps and graph-builder steps as an
asynchronous product.  A machine step changes only the machine state; a
builder step changes only the graph state.  A completed execution requires
the builder and machine canonical event maps to agree and requires the
computed RCU matching to contain no unmatched lock or unlock event.

This makes delayed commitment explicit: execution need not guess its final
graph initially, and graph facts need not be committed in lockstep with
instruction execution.  `coupled_operational_soundness` projects any
completed product run to:

- a run of the minimal program (`minimal_program_graph`);
- an `rcu_consistent` committed graph;
- sound GP certificates;
- emitted-event integrity; and
- unique, disjoint reader-stack safety.

Conversely, `consistent_program_candidate_is_schedulable` combines any
machine-compatible, well-formed, RCU-consistent finite candidate with its
machine run and builder schedule to obtain a completed coupled run.  The
initial coupled state contains neither that candidate nor its choices.

## Iris reader and grace-period protocol

`rcu_ghost.v` uses three ghost components:

- an authoritative ghost map of open reader IDs, with an exclusive token for
  each reader;
- an authoritative GP map whose entries change from an exact pending snapshot
  to a persistent done certificate; and
- an authoritative MaxNat epoch with persistent lower bounds.

Reader entry allocates a fresh exclusive map entry; reader exit consumes it
and deletes the entry.  GP begin registers `dom(open)` as an immutable
snapshot.  GP completion requires that snapshot to be disjoint from the
current open domain, updates the registered GP entry to done, advances the
MaxNat epoch, and returns a persistent certificate.  `rcu_gp_finish_frame`
proves the update while preserving an arbitrary client resource `R`.

`rcu_machine_safety.v` proves that reachable stacks have globally unique
reader IDs and are disjoint from completed sections.  Therefore every stored
machine GP certificate satisfies the exact snapshot/current-open
disjointness premise used by the Iris rule.
`completed_machine_gp_reclamation_frame` in `rcu_machine_ghost.v` composes
the operational theorem and Iris update directly.

## Deliberate limitations

- The feasibility-gate machine still emits only its five minimal labels.  The
  separate LKMM-Core machine handles values, generated RMW pairs, and direct
  dependency provenance but is not yet integrated with the incremental graph
  builder or Iris WP.
- `program_graph` accepts finite well-formed `rf` and `co` choices; it does not
  compute a single choice from the program.  Quantification over candidates is
  therefore required when stating a property for every allowed execution.
- The completeness proof uses propositional excluded middle to partition an
  `rb` relation into old and new pairs.  A reflected finite checker could
  later replace this classical proof step.
- Grace-period liveness is out of scope; a pending grace period may remain
  pending forever.
