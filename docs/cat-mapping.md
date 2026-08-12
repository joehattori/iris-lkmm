# LKMM source mapping

This is the manual mapping for the selected LKMM fragment.  Upstream line
numbers refer to Linux v6.18 at commit
`7d0a66e4bb9081d75c82ec4957c50034cb0ea449`.

## Canonical event vocabulary

`theories/lkmm/events.v` defines the syntactic event vocabulary.  It does not
yet define an execution graph or any graph relation.  In particular, the
capitalized semantic Bell sets `Acquire`, `Release`, `Mb`, `Noreturn`, and
`FailedRMW` are deferred because their definitions inspect event direction
and, for failed RMWs, the future `rmw` relation.

| Upstream source | Definition | Rocq definition | Treatment |
| --- | --- | --- | --- |
| `linux-kernel.bell:16-23` | `ONCE`, `RELEASE`, `ACQUIRE`, `NORETURN`, and `MB` access annotations; `R`, `W`, and `RMW` instruction classes | `access_mode`, `access_kind`, `rmw_mark`, `LMemory` | Direct finite syntactic vocabulary. RMW marking is orthogonal to read/write direction because successful operations will be represented by paired read and write events. |
| `linux-kernel.bell:25-37` | barrier annotations | `barrier_kind`, `LBarrier` | Includes only `MB`, `rmb`, `wmb`, `rcu-lock`, `rcu-unlock`, and `sync-rcu`, as selected by the project scope. |
| `linux-kernel.bell:40-48` | filtering of syntactic tags into semantic `FailedRMW`, `Acquire`, `Release`, `Mb`, and `Noreturn` sets | deferred | Requires the execution graph and `rmw` relation; no event-only approximation is introduced. |
| `linux-kernel.def:9-17` | `READ_ONCE`, `WRITE_ONCE`, release/acquire accesses, and `smp_store_mb` | `LMemory` with the corresponding `access_kind` and `access_mode` | `smp_store_mb` will generate an `ONCE` write followed by an `MB` barrier when the language layer is added. |
| `linux-kernel.def:20-22` | `smp_mb`, `smp_rmb`, and `smp_wmb` | `BarrierMb`, `BarrierRmb`, `BarrierWmb` | Direct barrier constructors. |
| `linux-kernel.def:31-38` | relaxed, acquire, release, and full-barrier `xchg`/`cmpxchg` | `RmwMarked` memory events with the corresponding `access_mode` | The future `rmw` relation pairs the read and write of a successful operation; a failed conditional RMW has only its marked read event. |
| `linux-kernel.def:47-50` | `rcu_read_lock`, `rcu_read_unlock`, and `synchronize_rcu` | `BarrierRcuLock`, `BarrierRcuUnlock`, `BarrierSyncRcu` | Direct normal-RCU barrier constructors. `synchronize_rcu_expedited` has the same upstream tag but remains outside the selected language. |
| `linux-kernel.def:66-70` | examples of non-returning atomic RMW operations | `AccessNoreturn` | Records the syntactic annotation only; its read-only semantic filtering is deferred. |

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

The feasibility kernel continues to accept an abstract `RcuGraph.po`; the
later RCU compatibility view will connect it to this canonical relation.

## Feasibility-kernel RCU mapping

| Upstream source | Definition | Rocq definition | Treatment |
| --- | --- | --- | --- |
| `linux-kernel.bell:56-68` | nested `rcu-rscs` matching | `critical_section`, `rcu_rscsi` | The graph stores already-matched, nested pairs; reproducing Bell's matching algorithm is future work. |
| `linux-kernel.cat:134` | `rcu-gp = [Sync-rcu]` | `is_gp` | Direct label test, additionally requiring membership in the finite event set. |
| `linux-kernel.cat:136` | `rcu-rscsi = rcu-rscs^-1` | `rcu_rscsi` | Direct inverse orientation: unlock to matching lock. |
| `linux-kernel.cat:144` | `po? ; hb* ; pb* ; prop ; po` | `rcu_link` | Direct relational decomposition using reflexive-transitive closures. |
| `linux-kernel.cat:154-163` | recursive `rcu-order` | `rcu_order` | The six normal-RCU disjuncts are constructors. All SRCU disjuncts are excluded. |
| `linux-kernel.cat:164` | `po ; rcu-order ; po?` | `rcu_fence` | Direct relational decomposition. |
| `linux-kernel.cat:169` | `prop ; rcu-fence ; hb* ; pb* ; [Marked]` | `rb` | Direct relational decomposition. The prototype's `Marked` is restricted to its read/write labels. |
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
