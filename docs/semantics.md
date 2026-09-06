# Incremental RCU prototype semantics

The prototype language has fixed agents and five instructions: `read`,
`write`, `rcu_read_lock`, `rcu_read_unlock`, and `synchronize_rcu`.
Its syntax and canonical event-label translation live in `lkmm_lang.v`; the
operational state and transitions in `rcu_machine.v` consume that language.
It is intentionally smaller than the LKMM-Core language in `lkmm_core.v`.

## LKMM-Core and concrete program graphs

`lkmm_core.v` defines a separate finite, loop-free language with registers,
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
The Core generation invariant proves unique per-agent positions, globally
fresh event IDs, well-formed RMW pairing, and well-formed direct address, data,
and control dependencies for every run.  Its provenance component states that
every origin retained in a register or active control frame is an earlier read
of the same agent.

`program_graph.v` defines the base-only `core_candidate` and the declarative
`program_graph` relation.  A program graph contains a complete core run whose
events, RMW pairs, and direct dependencies exactly equal the candidate fields.
The candidate's `rf` and `co` relations are not machine state: they range over
all finite choices satisfying their relational well-formedness predicates.
This connects nondeterministically observed read values to writes while still
allowing future writes to justify earlier observations.

`lkmm_consistent` is deliberately separate from `program_graph`. It applies
coherence, atomicity, happens-before acyclicity, propagation acyclicity, and
normal-RCU consistency to `core_candidate_graph`; its `hb` and `pb` are derived
from the candidate's dependency edges.

## Core-driven RCU machine

`operational/lkmm_machine.v` executes LKMM-Core with the gate's snapshot-based
RCU waiting protocol.  Its state contains the Core execution state, a finite
map of pending grace-period snapshots, and completion certificates.  Open
reader stacks and completed sections are obtained from the canonical matcher
over the generated events; they are not independently maintained caches.

Ordinary instructions reuse `core_step`, including silent control-flow steps,
register provenance, and two-event RMW emission.  RCU lock and unlock steps
emit the corresponding Core events, with unlock requiring a nonempty reader
stack for that agent.  Synchronization begins by capturing all currently
unmatched lock IDs, without advancing Core execution.  It finishes only after
each captured lock has a matched unlock, then emits Core's synchronization
event and records a certificate.  A pending agent can only finish its GP;
other agents may continue, without changing that agent's snapshot.  An empty
snapshot is still a pending GP and must take its finish step.

`run_core_projection` erases GP-begin actions and proves that every machine
run projects to a Core run.  `run_rcu_safety` proves the absence of unmatched
unlocks and the persistence of closed-section witnesses for every completed
certificate.  `completed_snapshot_clear` proves that captured readers of
completed GPs are absent from the current open-reader snapshot.  Completion
also requires all Core threads to finish, no pending GPs, and complete RCU
matching; execution prefixes may still contain open readers.

This is an event-generating operational component, not yet the full LKMM
operational semantics.  It does not choose `rf` or `co`, enforce memory-model
consistency, or maintain Iris resources.  `lkmm_coupled.v` connects it to the
incremental builder; `lkmm_machine_ghost.v` connects completed GP certificates
to the Iris completion update, as described below.

## Gate machine waiting protocol

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
canonical events and finite candidate `rf`, `co`, `rmw`, and direct dependency
edge sets.  Its `prop`, `hb`, and `pb` relations are derived from those fields.
It is a minimal shared graph view, not yet the final LKMM candidate-execution
type.  `rcu_graph.v` defines the normal-RCU classifications and consistency
condition.

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
derived from that map; the finite `rf`, `co`, `rmw`, and direct dependency
relations are supplied by the `candidate_relations` parameter.
Propagation, `hb`, and `pb` are derived from the event map and those candidate
relations.

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
explicit `rf`, `co`, `rmw`, and direct address/data/control edge lists.  A raw
mutation adds exactly one of:

- a fresh canonical event at a per-agent tail position; or
- one base-relation or direct-dependency edge.

Program order, propagation, `hb`, `pb`, and RCU matching are derived from the
graph and are not builder transitions.

A `rcu_link_commitment` records all four intermediate events witnessing
`po? ; hb* ; pb* ; prop ; po`.  `rcu_link_commitment_sound` proves that a
valid commitment denotes `rcu_link`; `rcu_link_commitment_complete` proves
that every `rcu_link` has such a record; and `commit_ready_rcu_link` permits
the commitment only after all of its component paths are present.  Graph
monotonicity proves that an already committed link remains valid as later
facts are added.

For a raw mutation, the builder supplies exact deltas for the five selected
consistency relations. It tracks transitive-closure paths for coherence,
`hb`, and `pb`, forbidden pairs for atomicity, and direct `rb` pairs:

```text
relations(new graph) = seen-relations ∪ delta
irreflexive(delta.coherence-paths)
empty(delta.atomicity-violations)
irreflexive(delta.hb-paths)
irreflexive(delta.pb-paths)
irreflexive(delta.rb)
```

Every relation mutation must leave the resulting partial relation structurally
well formed.  An `rf` prefix has well-formed edges and is functional; an `rmw`
prefix has well-formed edges and is functional and injective; a `co` prefix has
well-formed edges and is acyclic.  Direct dependency prefixes require their
read/access shape and program-order provenance.  These properties are preserved
by every builder run from `initial_builder`.
Read-from totality, marked-write totality, and the total/transitive coherence
order remain completion properties of a full LKMM candidate.

The transition refers only to the current state, the one-step successor, and
the delta. It has no final candidate or completed-graph consistency premise.
`builder_invariant` proves that `bs_seen_consistency` is exactly the current
graph's five monitored relations, that each required local safety property
holds, and that all stored link witnesses remain valid. Consequently,
`completed_builder_run_consistent` proves coherence, atomicity,
happens-before, propagation, and RCU consistency for every finite builder run
from `initial_builder`.

## Independent candidates and finite scheduling

`finite_candidate` is a declarative record of event-ID/canonical-event pairs
and six edge lists.  It contains no operational state,
delta, transition list, or schedule.  `candidate_well_formed` requires unique
event identifiers, canonical per-agent ordering, `event_structure_wf`,
complete RCU matching, structurally well-formed `rf`/`co`/`rmw` prefixes, and
well-formed direct address/data/control dependencies.

`candidate_has_raw_schedule` enumerates those finite components one at a
time. `lift_safe_raw_schedule` turns that enumeration into builder steps by
partitioning each successor's five monitored relations into previously seen
and new pairs. Monotonicity and consistency of the final candidate prove that
each new delta satisfies its local cycle or emptiness obligation.

The resulting completeness theorem is:

```text
candidate_well_formed(C) /\ graph_consistent(candidate_graph(C))
->
exists s,
  builder_run(initial_builder, s) /\
  graph(s) = candidate_graph(C)
```

The initial builder is one fixed empty constant and has no field in which a
candidate or its future choices could be preloaded.  The proof is a
candidate-directed existence proof, as operational completeness normally is;
the transition relation itself never receives the final candidate.

## Core-aware delayed commitments

`lkmm_coupled.v` couples `LkmmMachine.state` to `builder_state`.
A machine action advances Core execution or its snapshot-waiting protocol;
a builder action performs the five local consistency-delta checks and requires
`generated_prefix` for its successor.  This guard requires every
committed event to occur unchanged in the generated map and every committed
RMW or dependency edge to belong to its Core-generated set.
`coupled_run_generated_prefix` proves that these conditions hold throughout
every reachable run, including after later machine actions.

The machine starts from `initial_state P`, including the program's initial
writes; the builder starts empty.  Commitments may lag behind emission.
In particular, the builder can load events in canonical RCU trace order rather
than global emission order.  `rf` and `co` are independent builder choices,
not machine-generated edges.  Direct dependencies are generated by Core and
committed by the builder; `hb` and `pb` are derived from the committed graph.

`coupled_complete` requires completed Core threads, no pending GPs, complete
RCU matching, exact event-map agreement, and exact agreement for RMW and all
three direct-dependency sets.  Its
`coupled_operational_soundness` theorem gives a complete Core run, those exact
agreements, the builder's LKMM consistency, allocation well-formedness, no
unmatched unlocks, and sound completion certificates.  The coupled
snapshot-clear theorem preserves the captured-reader guarantee under arbitrary
interleaving of machine and builder actions.

`consistent_program_candidate_is_schedulable` proves relative scheduling:
given a complete snapshot-machine run and a well-formed, LKMM-consistent finite
candidate with the same events, RMW pairs, and direct dependencies, there is a
completed coupled run.
The proof may execute the machine first and then commit the graph.  Neither
the initial state nor the step rules contain the candidate.  This does not
prove that every consistent `program_graph` admits a snapshot-machine run.

`coupled_candidate` extracts every event and relation field from the builder.
`coupled_run_program_graph` proves that a completed coupled run yields a
`program_graph` when `coupled_program_graph_obligations` supplies well-formed
`rf` and `co`.  Event-structure, generated `rmw`, and direct-dependency
well-formedness follow from Core execution; complete RCU matching follows from
coupled completion.  The two remaining obligations are not transition guards.

`coupled_candidate_lkmm_consistent` transfers all five builder consistency
constraints directly to the extracted candidate because they contain the same
committed fields and derive the same relations. `coupled_run_soundness`
combines that result with `coupled_run_program_graph`; only completion-time
well-formedness of the independently chosen `rf` and `co` remains an explicit
premise.

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

`lkmm_machine_ghost.v` defines `open_reader_map` from the Core-driven machine's
current canonical snapshot.  `completed_certificate_enables_iris_finish`
converts `completed_snapshot_clear` into disjointness between a completed GP's
captured set and that map's domain.  `completed_machine_gp_reclamation_frame`
and `completed_coupled_gp_reclamation_frame` compose this fact with the Iris
update, preserving an arbitrary client frame.  A completed GP certificate is
enough; the whole program need not have finished, and later readers may remain
active.

Both rules require ownership of the authoritative current-open map and the
registered pending-GP token for the captured snapshot.  A machine certificate
does not create those resources.  A ghost-state interpretation maintained by
all execution steps, primitive WP rules, and adequacy remain to be developed.

## Deliberate limitations

- The feasibility-gate machine emits only its five minimal labels.  The
  separate LKMM-Core machine handles values, generated RMW pairs, and direct
  dependency provenance. Its builder supplies finite operational soundness,
  while Iris WP and unrestricted operational completeness remain deferred.
- `program_graph` accepts finite well-formed `rf` and `co` choices; it does not
  compute a single choice from the program.  Quantification over candidates is
  therefore required when stating a property for every allowed execution.
- The completeness proof uses propositional excluded middle to partition the
  five monitored relations into old and new pairs. A reflected finite checker could
  later replace this classical proof step.
- Grace-period liveness is out of scope; a pending grace period may remain
  pending forever.
