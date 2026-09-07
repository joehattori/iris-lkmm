# LKMM-Core operational semantics

LKMM-Core programs execute through `lkmm_machine.v`, which implements
normal-RCU snapshot waiting. `lkmm_coupled.v` interleaves that execution with
the incremental graph builder. The relational model and Iris ghost protocol
remain separate layers.

## LKMM-Core and concrete program graphs

`lkmm_core.v` defines a finite, loop-free language with registers,
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

## Per-agent Core replay

`lang/core_agent_replay.v` proves `core_run_replay_agent`: the subsequence of a
Core run belonging to one agent can execute independently in any
allocation-well-formed context where that agent still has its initial thread
state and local event index zero. The context may already contain other
agents' events. `complete_core_run_replay_agent` additionally proves that the
selected agent finishes; it does not assert completion of the other agents.
`program_graph_replay_agent` exposes the generated-graph correspondence
directly for `program_graph` candidates.

The replay keeps the original observed read values and per-agent action
order, including silent branch and continuation steps. Expression evaluation
commutes with renaming read origins in registers and control frames. An event
at local index `index` receives ID `base.core_next_id + index`; the
correspondence is injective on the selected agent's source events by canonical
event-position uniqueness. `replay_state` records exact equality of the
replayed events, RMW pairs, and three direct-dependency sets with their renamed
source projections plus the existing context. Other agents' thread states
are preserved; `agent_replay_other_index` also preserves their local event
indices, allowing subsequent replays in the resulting context.

`lang/core_replay.v` composes those replays for all program agents.
`complete_core_run_replay_order` accepts any list satisfying
`program_agent_enumeration`: it contains precisely the program agents,
each exactly once. Its conclusion is a `complete_core_run` whose
actions concatenate the agents' original subsequences in that order.
`complete_core_run_replay` supplies a finite enumeration automatically.
Both theorems return the replayed state, one event-ID renaming, and a
`core_state_renaming` proof for the entire final Core state.
`serial_actions_agent` proves that each agent retains exactly its original
action subsequence. The construction also returns a `serial_replay`
certificate containing the intermediate Core runs and their exact per-agent
`replay_state` correspondences; these are proof witnesses, not new semantics.
The induction keeps unreplayed agents initial and previously replayed agents
complete, so the final completion covers every agent. This does not assert
that arbitrary schedules terminate.

The source's final event map defines the naming correspondence in the proof
only. Core transitions and states are unchanged, and reads do not require
their eventual source writes to have executed. This result needs neither
LKMM consistency nor a completed RCU-machine run and adds no axioms. It is
the Core replay component of the conditional Core-to-machine completeness
theorem below; full coupled completeness remains open.
Regressions exercise nested control/address/data provenance, successful
and failed `cmpxchg`, replay after another agent has already executed,
whole-program completion in either two-agent order, and the empty program.

`lang/core_renaming.v` defines the whole-state correspondence. The event
renaming is a bijection between allocated events, preserves their values
(including labels, agents and local positions), and fixes initial-write IDs.
All thread states are renamed using the same function, including register and
control-frame provenance. The generated RMW and dependency sets are exactly
the images of the source sets under renaming of both endpoints. Global and
per-agent next-event counters agree. `serial_replay_core_state_renaming`
assembles this correspondence from the individual replay certificates;
the IDs assigned to each agent occupy a block starting after the preceding
agents' events.

The graph-only parts live in `lkmm/event_renaming.v` and
`lkmm/rcu_renaming.v`, independently of Core and the machine. They prove
preservation of program order, event classifications, per-agent RCU token
traces, matched sections, and complete RCU matching. A renaming need not
preserve numeric ID order: the matcher sorts by agent and local position,
and event-structure well-formedness rules out duplicate positions.

## RCU replay premises

The event-level premises for machine reconstruction are defined in
`lkmm/rcu_replay.v`. `rcu_replay_wf E` combines `rcu_matching_complete E`
with `no_gp_in_read_section E`: no `BarrierSyncRcu` event lies strictly
between a matched lock and unlock in program order. Since program order
relates events of the same agent, this permits other agents' grace periods.
Every matched section is checked, including outer sections around nested
ones. These premises describe a completed event structure, not a prefix;
they do not assume a machine run, change the transition rules, or add a new
LKMM consistency constraint. `rcu_replay_wf_rename` transfers these premises
through event renaming, and `core_state_renaming_rcu` specializes this to
Core states. The renaming regression reverses numeric event IDs while
preserving both nested matching pairs.

`program_graph_rcu_replay_wf` derives the replay premises from a consistent
program graph:

```text
program_graph P C -> lkmm_consistent C -> rcu_replay_wf C.candidate_events
```

Complete matching comes from `program_graph` well-formedness.
`rcu_consistent_no_gp_in_read_section` supplies the other conjunct: if
`lock -> gp -> unlock` holds in program order for a matched section,
`gp_in_read_section_rb` constructs `rb gp gp`, contradicting RCU consistency.
The construction uses `rcu_link lock gp`, then `rcu_order unlock gp`, then
`rcu_fence gp gp`; barriers are marked, so the reflexive cases of `prop`,
`hb*`, and `pb*` complete the self-edge. Regressions cover both a single
section and a still-open outer section after its inner section closes,
with no memory edges in either graph.

`lang/core_rcu.v` proves the local prefix guards in
`core_step_rcu_local_guards`: if a Core step extends to events satisfying
`rcu_replay_wf`, an unlock has a nonempty stack and a synchronization has an
empty stack for its own agent. An unmatched unlock cannot disappear during
later execution. An open lock's eventual matching unlock must occur later,
so synchronizing before it would violate `no_gp_in_read_section`. These facts
apply to any Core schedule with such a continuation, including nested sections.

`lang/core_replay_rcu.v` strengthens this for serialized replay.
`complete_core_run_replay_rcu_order` accepts any enumeration of whole agent
blocks; `complete_core_run_replay_rcu` supplies the enumeration. Both return
a completed Core run, its whole-state renaming, the preserved RCU premises,
and a `core_run_rcu_guards` certificate. Every unlock has an open reader, and
every synchronization has an empty global snapshot: other agents' stacks
remain empty during the active block, and each block ends with all stacks
empty. The certificate records these properties of existing Core steps;
it does not change Core semantics or construct a machine run. A regression
starts with an interleaved reader/GP execution whose GP snapshot is nonempty
and proves that both serialized agent orders satisfy the guards. The machine
lifting below consumes this certificate, and the composed theorem constructs
a completed machine run from the original execution's final RCU premises.

## Core-driven RCU machine

`operational/lkmm_machine.v` executes LKMM-Core with a snapshot-based
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

`operational/core_to_machine.v` proves the converse construction for Core
runs carrying `core_run_rcu_guards`. `lift_core_action` translates ordinary
steps to `Execute`, locks/unlocks to their machine actions, and each
synchronization to `BeginGp` followed immediately by `FinishGp`.
`empty_snapshot_gp_run` proves that this pair captures an empty snapshot,
records its completion certificate, and clears the pending entry.

`core_step_machine_lift` proves the translation for one step, preserving its
resulting Core state and restoring an empty pending map.
`core_run_machine_lift` composes these translations for any guarded Core
prefix, starting from any machine state with the same Core state and no
pending GPs. Its result has exactly the requested final Core state, no
pending GPs, and an action projection equal to the original Core actions.
`complete_core_run_machine_lift` adds Core completion and complete final RCU
matching to obtain `complete_machine_run`. The matching premise is essential: Core
threads can finish with an open reader even when every executed step meets
the guards. Regressions cover nested sections, RMW/register provenance, two
successive GPs, and that final-matching distinction.

This stepwise lifting preserves the supplied Core schedule, performs no event
renaming, and adds no transition rules or axioms.

`complete_core_run_machine_replay` composes serialized replay with lifting
to prove conditional Core-to-machine completeness:

```text
complete_core_run P actions source
-> rcu_replay_wf source.core_events
-> exists machine_actions s f,
     complete_machine_run P machine_actions s /\
     core_state_renaming f source s.machine_core /\
     project_actions machine_actions = serial_actions (program_agents_list P) actions
```

The original run need not satisfy `core_run_rcu_guards`: those guards are
proved for the constructed replay and discharged inside the theorem.
`complete_core_run_machine_replay_order` accepts any enumeration of whole
agent blocks; the canonical theorem supplies that enumeration. The projected
machine actions retain every agent's original action subsequence, including
observed values and silent steps. The final correspondence preserves all
Core state components under one event-ID renaming. A regression constructs
machine executions in both block orders from the interleaved reader/GP
example whose original GP has a nonempty snapshot.

Full coupled completeness remains open. It still requires transporting the
complete candidate (including `rf` and `co`) through renaming and using the
constructed machine run in coupled scheduling to establish the final
candidate correspondence.

This is an event-generating operational component, not yet the full LKMM
operational semantics.  It does not choose `rf` or `co`, enforce memory-model
consistency, or maintain Iris resources.  `lkmm_coupled.v` connects it to the
incremental builder; `lkmm_machine_ghost.v` connects completed GP certificates
to the Iris completion update, as described below.

## Independent graph-chain invariant

`execution_graph.v` defines the shared relation graph containing
canonical events and finite candidate `rf`, `co`, `rmw`, and direct dependency
edge sets.  Its `prop`, `hb`, and `pb` relations are derived from those fields.
`core_candidate_graph` and the builder's `graph_of_raw` both use this graph
type. `rcu_graph.v` defines the normal-RCU classifications and consistency
condition, and combines it with the four memory consistency conditions.

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

The chain equivalence is a theorem about graphs, independent of the machine's
waiting protocol. Coupled LKMM consistency follows from the builder's
consistency invariant; the Iris completion bridge uses the machine's
snapshot-clear theorem. Neither proof requires a machine-to-chain bridge.

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

- Coupled operational soundness requires completion-time `rf`/`co`
  well-formedness. Unrestricted operational completeness and Iris WP/adequacy
  remain deferred.
- `program_graph` accepts finite well-formed `rf` and `co` choices; it does not
  compute a single choice from the program.  Quantification over candidates is
  therefore required when stating a property for every allowed execution.
- The completeness proof uses propositional excluded middle to partition the
  five monitored relations into old and new pairs. A reflected finite checker could
  later replace this classical proof step.
- Grace-period liveness is out of scope; a pending grace period may remain
  pending forever.
