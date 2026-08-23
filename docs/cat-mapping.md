# LKMM source mapping

This is the manual mapping for the selected LKMM fragment.  Upstream line
numbers refer to Linux v6.18 at commit
`7d0a66e4bb9081d75c82ec4957c50034cb0ea449`.

## Canonical event vocabulary

`theories/lkmm/events.v` defines only the syntactic event vocabulary; execution
relations are kept in the graph layers.  The capitalized semantic Bell sets
`Acquire`, `Release`, `Mb`, `Noreturn`, and `FailedRMW` are represented by
lowercase unary predicates in `memory_relations.v`, where the syntactic tags
can be filtered using the candidate `rmw` relation.

| Upstream source | Definition | Rocq definition | Treatment |
| --- | --- | --- | --- |
| `linux-kernel.bell:16-23` | `ONCE`, `RELEASE`, `ACQUIRE`, `NORETURN`, and `MB` access annotations; `R`, `W`, and `RMW` instruction classes | `access_mode`, `access_kind`, `rmw_mark`, `LMemory` | Direct finite syntactic vocabulary. RMW marking is orthogonal to read/write direction because successful operations will be represented by paired read and write events. |
| `linux-kernel.bell:25-37` | barrier annotations | `barrier_kind`, `LBarrier` | Includes only `MB`, `rmb`, `wmb`, `rcu-lock`, `rcu-unlock`, and `sync-rcu`, as selected by the project scope. |
| `linux-kernel.bell:40-48` | filtering of syntactic tags into semantic `FailedRMW`, `Acquire`, `Release`, `Mb`, and `Noreturn` sets | `failed_rmw`, `acquire`, `release`, `mb`, `noreturn` | Direct execution-dependent unary predicates. `Mb` includes both MB-tagged memory accesses and full `MB` barriers before subtracting `FailedRMW`. |
| `linux-kernel.def:9-17` | `READ_ONCE`, `WRITE_ONCE`, release/acquire accesses, and `smp_store_mb` | `LMemory` with the corresponding `access_kind` and `access_mode` | `smp_store_mb` will generate an `ONCE` write followed by an `MB` barrier when the language layer is added. |
| `linux-kernel.def:20-22` | `smp_mb`, `smp_rmb`, and `smp_wmb` | `BarrierMb`, `BarrierRmb`, `BarrierWmb` | Direct barrier constructors. |
| `linux-kernel.def:31-38` | relaxed, acquire, release, and full-barrier `xchg`/`cmpxchg` | `RmwMarked` memory events with the corresponding `access_mode` | The `rmw` relation pairs the read and write of a successful operation; a failed conditional RMW has only its marked read event. |
| `linux-kernel.def:47-50` | `rcu_read_lock`, `rcu_read_unlock`, and `synchronize_rcu` | `BarrierRcuLock`, `BarrierRcuUnlock`, `BarrierSyncRcu` | Direct normal-RCU barrier constructors. `synchronize_rcu_expedited` has the same upstream tag but remains outside the selected language. |
| `linux-kernel.def:66-70` | examples of non-returning atomic RMW operations | `AccessNoreturn`, `noreturn` | Records the syntactic annotation and applies Bell's semantic exclusion of writes. |

Initial writes are represented explicitly by `EInitWrite`.  Locations are
abstract natural-number identifiers and values are mathematical integers;
machine-word overflow is not modeled at this layer.  Plain accesses, compiler
`barrier`, before/after-atomic barriers, lock operations, and SRCU have no
constructors.  Address, data, and control dependencies are graph relations,
not event labels, and will be introduced with the execution graph.

The existing feasibility kernel retains its five-label graph vocabulary until
the later RCU compatibility-view commit.

## Canonical event structures and program order

`theories/lkmm/execution.v` represents a finite execution's events as a map
from event identifiers to canonical events.  Its `po` relation is a herd
execution-structure relation rather than a definition transcribed from
`linux-kernel.cat`: two events are in `po` exactly when they belong to the
same agent and their local indices are strictly increasing.  Indices need not
be contiguous, and initial writes are excluded because they have no agent or
local index.  `event_structure_wf` ensures that an agent-local position
identifies at most one event.

The same file defines `event_attribute` by composing event lookup with an
option-valued event projection, and lifts it to the binary `same_attribute`
relation.  The canonical `same_location` and `same_agent` relations specialize
this construction with `location_of` and `agent_of`.  It then defines `po_loc`
as `po & same_location`.  Consequently barriers are excluded because they
have no location, while initial writes are excluded by `po`.  The `rf`, `co`,
and `fr` edge well-formedness predicates in
`theories/lkmm/memory_relations.v` reuse `same_location`, as do coherence
totality, initial-write ordering, and the `location_used` projection.

The feasibility kernel continues to accept an abstract `RcuGraph.po`; the
later RCU compatibility view will connect it to this canonical relation.

## Reads-from candidates

`theories/lkmm/memory_relations.v` represents `rf` as a finite set of event-ID
edges and exposes it through a relational view.  Like `po`, `rf` is supplied
by the herd candidate execution rather than defined in `linux-kernel.cat`.
The predicate `rf_wf` requires every edge to connect a write to a read at the
same location and value, and requires every read to have exactly one source.
Initial writes are ordinary `rf` sources; uniqueness of initial writes and
their placement in coherence order are enforced by `co_wf` below.

## Coherence-order candidates

`theories/lkmm/memory_relations.v` represents `co` as a finite set of
event-ID edges and exposes it through a relational view.  The set contains
the complete transitive order, not only immediate-successor edges.  Like
`rf`, `co` is supplied by the herd candidate execution and consumed by
the LKMM CAT model.

The predicate `co_wf` requires `co` to be a strict total order on the
writes to each location, with no edges between locations.  Every location
used by a memory event has exactly one initial write, and that initial write
precedes every other write to the location.  These are candidate-graph
well-formedness conditions rather than LKMM consistency axioms.

## From-read relation

`theories/lkmm/memory_relations.v` defines `fr` as the derived relation
`rf^-1 ; co`.  Thus a read is `fr`-before exactly those writes that are
coherence-later than the write it reads from.  It is not an independent
candidate choice and has no separate edge set or well-formedness predicate.
Under `rf_wf` and `co_wf`, every `fr` edge runs from a read to a write at the
same location.

## Internal and external communication

`theories/lkmm/memory_relations.v` partitions each communication relation by
its endpoints' agents.  The internal variants are `rfi = rf & same_agent`,
`coi = co & same_agent`, and `fri = fr & same_agent`; the external variants
subtract `same_agent` from the corresponding base relation.  Each pair is
disjoint and exhaustively covers its base relation.

This matches herd's same-CPU/different-CPU classification while remaining
defined over the canonical event structure.  Initial writes have no program
agent, so well-formed `rf` and `co` edges from an initial write are external.
The `fri`/`fre` split examines the read and final-write endpoints of the
already-derived `fr`; it does not depend on whether the intermediate `rf`
source is internal or external.  These six relations have no independent edge
sets or well-formedness predicates.

## Base consistency constraints

`theories/lkmm/memory_relations.v` defines `com` as `rf | co | fr` and
transcribes the Linux v6.18 constraint at `linux-kernel.cat:69-70` as
`coherence = acyclic (po-loc | com)`.  This consistency predicate remains
separate from `event_structure_wf`, `rf_wf`, and `co_wf`: those predicates
establish that the candidate relations have the required shape, while
`coherence` rejects cycles through the otherwise well-formed relations.

The same file transcribes the constraint at `linux-kernel.cat:73`,
`empty (rmw & (fre ; coe)) as atomic`, as the `atomicity` predicate.  It remains
separate from candidate well-formedness.

## Read-modify-write candidates

`theories/lkmm/memory_relations.v` represents `rmw` as a finite set of
read-to-write event-ID edges supplied by the candidate execution.  Every
well-formed edge connects marked accesses from one successful RMW operation:
the read is `po`-before the write, and both endpoints have the same location
and syntactic access mode.  The `po` premise also ensures that the endpoints
belong to the same agent.

The predicate `rmw_wf` makes this pairing functional and injective, and
requires every marked write to have a read partner.  It deliberately does not
require every marked read to have a write partner, so a lone marked read can
represent a failed conditional RMW.  The event vocabulary does not retain the
operation or operand needed to validate the written value, nor does it
distinguish conditional from unconditional RMW syntax; those checks belong to
the later LKMM-Core program-graph correspondence.

The separate `atomicity` consistency predicate rejects an `rmw` edge when its
read-to-write endpoints are also related by `fre ; coe`; it is not folded into
`rmw_wf`.

## Feasibility-kernel RCU mapping

| Upstream source | Definition | Rocq definition | Treatment |
| --- | --- | --- | --- |
| `linux-kernel.bell:56-68` | nested `rcu-rscs` matching | `critical_section`, `rcu_rscsi` | The graph stores already-matched, nested pairs; reproducing Bell's matching algorithm is future work. |
| `linux-kernel.cat:134` | `rcu-gp = [Sync-rcu]` | `is_gp` | Direct label test, additionally requiring membership in the finite event set. |
| `linux-kernel.cat:136` | `rcu-rscsi = rcu-rscs^-1` | `rcu_rscsi` | Direct inverse orientation: unlock to matching lock. |
| `linux-kernel.cat:144` | `po? ; hb* ; pb* ; prop ; po` | `rcu_link` | Direct relational decomposition using reflexive-transitive closures. |
| `linux-kernel.cat:154-163` | recursive `rcu-order` | `rcu_order` | The six normal-RCU disjuncts are constructors. All SRCU disjuncts are excluded. |
| `linux-kernel.cat:164` | `po ; rcu-order ; po?` | `rcu_fence` | Direct relational decomposition. |
| `linux-kernel.cat:169` | `prop ; rcu-fence ; hb* ; pb* ; [Marked]` | `rb` | Direct relational decomposition. Since plain accesses are excluded, every prototype graph event is `Marked`. |
| `linux-kernel.cat:171` | `irreflexive rb` | `rcu_consistent` | Direct predicate. |

The operational graph layer does not redefine these relations.
`rcu_link_commitment` stores the four intermediate event identifiers of the
existing `rcu_link` decomposition, and `rcu_link_commitment_sound`/
`rcu_link_commitment_complete` prove correspondence in both directions.  The
builder's `bs_seen_rb` monitor is proved extensionally equal to the existing
`rb` at every reachable state; `completed_builder_run_rb_irreflexive`
therefore establishes the same `rcu_consistent` predicate rather than a
separate operational approximation.

`rcu_segment` is an early proof-oriented certificate that retains CAT's
recursive composition structure.  The independent formulation is
`rcu_chain_order` in `theories/lkmm/rcu_obligations.v`.  It contains:

- a nonempty finite list of valid GP or inverse-RSCS atoms;
- an `rcu-link` edge between every pair of adjacent atoms; and
- a signed final balance, with GP worth `+1` and inverse RSCS worth `-1`,
  required to be nonnegative.

`rcu_order_chain_equiv` proves this list/counter predicate equivalent to
`rcu_order`.  Its proof uses a generic word theorem showing that CAT's six
normal-RCU recursive cases recognize exactly the nonempty words whose final
balance is nonnegative.

This mapping has been compiler-checked only as Rocq code.  It has not yet been
differentially tested with `herd7` and has not received independent review.
