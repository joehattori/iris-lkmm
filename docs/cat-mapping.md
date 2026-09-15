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
| `linux-kernel.cat:69-70` | `acyclic (po-loc | com) as coherence` | `coherence` | Separate from candidate well-formedness. |
| `linux-kernel.cat:73` | `empty (rmw & (fre ; coe)) as atomic` | `atomicity` | Separate from RMW pairing well-formedness. |
| `linux-kernel.cat:78-84` | `dep`, `rwdep`, `overwrite`, `to-w`, `to-r`, and `ppo` | `dep`, `rwdep`, `overwrite`, `to_w`, `to_r`, `ppo` | Uses `same_agent` for `int` and the base `fence`, and includes `addr ; [Plain] ; wmb`. Lock ordering remains outside the vocabulary. |
| `linux-kernel.cat:97-103` | `A-cumul`, `rmw-sequence`, `cumul-fence`, and `prop` | `a_cumul`, `rmw_sequence`, `cumul_fence`, `prop` | Direct relational translation using restricted identities, optional relations, and reflexive-transitive closures. `ext` is the complement of `same_agent`; the lock-only `po-unlock-lock-po` branch is omitted. |
| `linux-kernel.cat:105-110` | `hb` and `acyclic hb as happens-before` | `hb`, `happens_before` | Uses `same_agent` for `int`; the internal `prop` branch removes identity edges before contributing to happens-before. |
| `linux-kernel.cat:112-118` | `pb` and `acyclic pb as propagation` | `pb`, `propagation` | Direct composition of `prop`, `strong_fence`, the reflexive-transitive closure of `hb`, and a final `Marked` restriction. |
| `linux-kernel.def:9-17` | `READ_ONCE`, `WRITE_ONCE`, release/acquire accesses, and `smp_store_mb` | `SLoad`, `SStore`, and `smp_store_mb` | LKMM-Core emits `LMemory` events with the corresponding access modes; `smp_store_mb` elaborates to an ONCE store followed by an MB fence. |
| `linux-kernel.def:20-22` | `smp_mb`, `smp_rmb`, and `smp_wmb` | `BarrierMb`, `BarrierRmb`, `BarrierWmb` | Direct barrier constructors. |
| `linux-kernel.def:23-24` | `smp_mb__before_atomic` and `smp_mb__after_atomic` | `SFence FenceBeforeAtomic`, `SFence FenceAfterAtomic` | LKMM-Core emits the corresponding barrier event. |
| `linux-kernel.def:31-38` | relaxed, acquire, release, and full-barrier `xchg`/`cmpxchg` | `SXchg`, `SCmpxchg` | A successful operation emits paired marked events; failed `cmpxchg` emits only its marked read. |
| `linux-kernel.def:47-50` | `rcu_read_lock`, `rcu_read_unlock`, and `synchronize_rcu` | `SRcuReadLock`, `SRcuReadUnlock`, `SSynchronizeRcu` | Direct normal-RCU instructions. `synchronize_rcu_expedited` remains outside the selected language. |
| `linux-kernel.def:66-70` | examples of non-returning atomic RMW operations | `SAtomicNoReturn`, `AccessNoreturn`, `noreturn` | The core instruction emits a paired update; Bell's semantic class excludes its write endpoint. |

Initial writes are represented explicitly by `EInitWrite`.  Locations are
abstract natural-number identifiers and values are mathematical integers;
machine-word overflow is not modeled at this layer. The relational vocabulary
represents unannotated memory accesses with `AccessPlain`; LKMM-Core has no
plain-load or plain-store instruction. Compiler `barrier`, lock operations,
and SRCU have no constructors. Before/after-atomic barriers are represented
in the relational vocabulary and LKMM-Core.
Address, data, and control dependencies are graph relations, not event labels;
`direct_addr`, `direct_data`, and `direct_ctrl` expose their finite provenance
edge sets through relational views.

The relational RCU model, Core candidates, and graph builder share the same
canonical event vocabulary and derived memory relations.

## Candidate boundary

Program order, reads-from, coherence, and RMW pairing are herd execution
structure inputs rather than definitions supplied by the CAT file.
[Event structures](../theories/lkmm/execution.v) and
[memory relations](../theories/lkmm/memory_relations.v) give them explicit
well-formedness conditions. These are separate from the selected consistency
constraints.

[Core execution](../theories/lang/program_graph.v) generates RMW pairing and
dependency provenance; reads-from and coherence remain independent candidate
choices. The [coupled semantics](semantics.md#coupled-execution) requires
committed provenance to come from Core. The standalone graph builder has no
program-execution premise.

## Normal-RCU mapping

| Upstream source | Definition | Rocq definition | Treatment |
| --- | --- | --- | --- |
| `linux-kernel.bell:56-70` | nested `rcu-rscs` matching | `compute_rcu_matching`, `rcu_rscs`, `bell_rcu_rscs` | Canonical per-agent stack matching, with a bounded adjacent-unmatched Bell iteration as a transcription regression. Final candidates reject unmatched locks and unlocks. |
| `linux-kernel.cat:134` | `rcu-gp = [Sync-rcu]` | `is_gp` | Direct label test, additionally requiring membership in the finite event set. |
| `linux-kernel.cat:136` | `rcu-rscsi = rcu-rscs^-1` | `rcu_rscsi` | Direct inverse of the computed matching: unlock to matching lock. |
| `linux-kernel.cat:144` | `po? ; hb* ; pb* ; prop ; po` | `rcu_link` | Direct relational decomposition using reflexive-transitive closures. |
| `linux-kernel.cat:154-163` | recursive `rcu-order` | `rcu_order` | The six normal-RCU disjuncts are constructors. All SRCU disjuncts are excluded. |
| `linux-kernel.cat:164` | `po ; rcu-order ; po?` | `rcu_fence` | Direct relational decomposition. |
| `linux-kernel.cat:169` | `prop ; rcu-fence ; hb* ; pb* ; [Marked]` | `rb` | Direct relational decomposition using the canonical Bell `marked` predicate. |
| `linux-kernel.cat:171` | `irreflexive rb` | `rcu_consistent` | Direct predicate. |

This mapping has been compiler-checked only as Rocq code.  It has not yet been
differentially tested with `herd7` and has not received independent review.
