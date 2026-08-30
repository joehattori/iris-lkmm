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

CAT restricted identities `[S]` are represented uniformly by
`rel_id_on S` from the relational prelude.

| Upstream source | Definition | Rocq definition | Treatment |
| --- | --- | --- | --- |
| `linux-kernel.bell:16-23` | `ONCE`, `RELEASE`, `ACQUIRE`, `NORETURN`, and `MB` access annotations; `R`, `W`, and `RMW` instruction classes | `access_mode`, `access_kind`, `rmw_mark`, `LMemory` | Direct finite syntactic vocabulary. `AccessPlain` is the Rocq representation of a memory access with no named Bell access annotation; it is not itself an upstream annotation. RMW marking remains orthogonal to read/write direction. |
| `linux-kernel.bell:25-37` | barrier annotations | `barrier_kind`, `LBarrier` | Includes `MB`, `rmb`, `wmb`, `before-atomic`, `after-atomic`, and the selected normal-RCU annotations. |
| `linux-kernel.bell:40-48` | filtering of syntactic tags into semantic `FailedRMW`, `Acquire`, `Release`, `Mb`, and `Noreturn` sets | `failed_rmw`, `acquire`, `release`, `mb_event`, `noreturn` | Direct execution-dependent unary predicates. `Mb` includes both MB-tagged memory accesses and full `MB` barriers before subtracting `FailedRMW`. |
| `linux-kernel.bell:89-91` | `Marked` and `Plain = M \ Marked` | `marked`, `plain` | In the canonical vocabulary, `AccessPlain`/`NotRmw` accesses are exactly `Plain`; every other represented event is `Marked`, including independently RMW-marked accesses. |
| `linux-kernel.bell:93-96` | `(data ; [~ Srcu-unlock] ; rfi)*` carrying into `addr`, `data`, and `ctrl` | `carry_dep`, `addr`, `data`, `ctrl` | The selected fragment has no SRCU events, so the filter is omitted and the closure uses `direct_data ; rfi`. |
| Herd7 `stdlib.cat:29` | `fencerel(B) = (po & (_ * B)) ; po` | `fencerel` | Equivalent `po ; [B] ; po` composition using `rel_id_on` for the barrier witness. |
| `linux-kernel.cat:28-29` | `[Acquire] ; po ; [M]` and `[M] ; po ; [Release]` | `acq_po`, `po_rel` | Direct derived relations using the semantic Bell classes and consumed by `nonrw_fence`. |
| `linux-kernel.cat:33-63` | `R4rmb`, `rmb`, `wmb`, selected `mb`, normal-RCU `gp`, `strong-fence`, `nonrw-fence`, and `fence` | `r4_rmb`, `rmb`, `wmb`, `mb`, `gp`, `strong_fence`, `nonrw_fence`, `fence` | Includes explicit full barriers, full-barrier RMWs, and before/after-atomic augmentation. Lock and SRCU branches remain outside the selected vocabulary; the later generalized `rcu-fence` extension remains deferred. |
| `linux-kernel.cat:78-84` | `dep`, `rwdep`, `overwrite`, `to-w`, `to-r`, and `ppo` | `dep`, `rwdep`, `overwrite`, `to_w`, `to_r`, `ppo` | Uses `same_agent` for `int` and the base `fence`, and includes `addr ; [Plain] ; wmb`. Lock ordering remains outside the vocabulary. |
| `linux-kernel.cat:97-103` | `A-cumul`, `rmw-sequence`, `cumul-fence`, and `prop` | `a_cumul`, `rmw_sequence`, `cumul_fence`, `prop` | Direct relational translation using restricted identities, optional relations, and reflexive-transitive closures. `ext` is the complement of `same_agent`; the lock-only `po-unlock-lock-po` branch is omitted. |
| `linux-kernel.def:9-17` | `READ_ONCE`, `WRITE_ONCE`, release/acquire accesses, and `smp_store_mb` | `LMemory` with the corresponding `access_kind` and `access_mode` | `smp_store_mb` will generate an `ONCE` write followed by an `MB` barrier when the language layer is added. |
| `linux-kernel.def:20-22` | `smp_mb`, `smp_rmb`, and `smp_wmb` | `BarrierMb`, `BarrierRmb`, `BarrierWmb` | Direct barrier constructors. |
| `linux-kernel.def:23-24` | `smp_mb__before_atomic` and `smp_mb__after_atomic` | `BarrierBeforeAtomic`, `BarrierAfterAtomic` | Direct barrier constructors; program-layer generation remains deferred. |
| `linux-kernel.def:31-38` | relaxed, acquire, release, and full-barrier `xchg`/`cmpxchg` | `RmwMarked` memory events with the corresponding `access_mode` | The `rmw` relation pairs the read and write of a successful operation; a failed conditional RMW has only its marked read event. |
| `linux-kernel.def:47-50` | `rcu_read_lock`, `rcu_read_unlock`, and `synchronize_rcu` | `BarrierRcuLock`, `BarrierRcuUnlock`, `BarrierSyncRcu` | Direct normal-RCU barrier constructors. `synchronize_rcu_expedited` has the same upstream tag but remains outside the selected language. |
| `linux-kernel.def:66-70` | examples of non-returning atomic RMW operations | `AccessNoreturn`, `noreturn` | Records the syntactic annotation and applies Bell's semantic exclusion of writes. |

Initial writes are represented explicitly by `EInitWrite`.  Locations are
abstract natural-number identifiers and values are mathematical integers;
machine-word overflow is not modeled at this layer.  Unannotated memory
accesses use `AccessPlain`; compiler `barrier`, lock operations, and SRCU have
no constructors.  Before/after-atomic barriers are represented in the
relational vocabulary, while program-layer generation remains deferred.
Address, data, and control dependencies are graph relations, not event labels;
`direct_addr`, `direct_data`, and `direct_ctrl` expose their finite provenance
edge sets through relational views.

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

The same file uses a local lookup-and-projection helper to define the public
`event_has_access_kind`, `event_has_access_mode`, `event_is_rmw_marked`,
`event_has_barrier_kind`, and `event_has_location` predicates, as well as the
binary `same_attribute` relation.  The canonical `same_location` and
`same_agent` relations specialize the latter with `location_of` and
`agent_of`; `ext` is the complement of `same_agent`.  It then defines
`po_loc` as `po & same_location`.  Consequently
barriers are excluded because they have no location, while initial writes are
excluded by `po`.  The `rf`, `co`, and `fr` edge well-formedness predicates in
`theories/lkmm/memory_relations.v` reuse `same_location`, as do coherence
totality, initial-write ordering, and the `location_used` projection.

The feasibility kernel continues to accept an abstract `RcuGraph.po`; the
later RCU compatibility view will connect it to this canonical relation.

## Dependency candidates and Bell carrying

`theories/lkmm/memory_relations.v` represents `direct_addr`, `direct_data`,
and `direct_ctrl` provenance as three distinct finite edge sets.  Their
well-formedness predicates require a program-order source read and
respectively a memory, write, or write target.  Edge membership records
provenance explicitly; the later LKMM-Core program-graph correspondence must
justify that provenance from syntactic data and control flow rather than
reconstructing it by alias analysis.

The public `addr`, `data`, and `ctrl` relations are the extended Bell views,
each prepending `carry_dep = (direct_data ; rfi)*` to the corresponding direct
relation.  The upstream `[~ Srcu-unlock]` filter is absent because SRCU is
outside the selected event vocabulary.

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
