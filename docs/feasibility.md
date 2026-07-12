# Feasibility gate assessment

## Verdict

**HOLD: the feasibility gate is not passed.  Do not begin the full language
or Iris logic yet.**

The experiment found a viable incremental representation of grace-period
waiting, and no negative result shows that a sound design is impossible.
However, the required bridge from that representation to the CAT-style
`rcu-order`/`rb` graph condition is still missing.  Whole-graph
operational soundness and completeness would currently be claims rather than
theorems.

## Mechanized evidence

| Gate question | Evidence | Result |
| --- | --- | --- |
| Can the normal-RCU CAT recursion be represented constructively? | `rcu_law_equivalence` proves equivalence between `rcu_order` and counted `rcu_segment` certificates; `rcu_segment_balance` proves that certificates use at least as many grace periods as critical sections. | **Prototype pass**, but the certificate still mirrors CAT's recursive decomposition and is not yet the machine snapshot law. |
| Can grace periods be incremental? | `ABeginGp` captures open lock identifiers; `AFinishGp` consumes only that finite snapshot. Later readers do not change it. | **Pass for waiting semantics.** |
| Does soundness avoid embedding final consistency in every step? | `step` mentions only program counters, stacks, pending snapshots, and closed sections. `operational_soundness` is an invariant proof. | **Pass.** |
| Is operational soundness proved against the graph kernel? | The current theorem proves certificate closure, not `ProgramGraph /\ rcu_consistent`. | **Fail / open.** |
| Is finite operational completeness proved without choosing the final graph up front? | `finish_gp_complete` is exact local completeness for a pending GP. There is no theorem for every finite permitted graph. | **Fail / open.** |
| Does the state support a compositional Iris reclamation rule? | The immutable snapshot suggests a finite family of reader obligations that could be represented by authoritative ghost state. No Iris rule or frame-preserving update is proved. | **Fail / unvalidated.** |

All checked proofs contain no `Admitted`, `admit`, or new axiom.

## Why a vacuous soundness proof was rejected

The prototype could extract a graph with empty `prop`; then `rcu-link` and
`rb` would be empty and consistency would be immediate.  That would make
soundness true by construction while providing no evidence about RCU chains.
The implementation deliberately does not claim this theorem.

## Required next experiment

Before reversing the HOLD verdict:

1. Give an independent chain/obligation semantics for `rcu-order` (rather
   than a derivation tree with the same constructors), and prove it equivalent
   to the CAT-style recursion.
2. Relate machine snapshots and completed critical sections to that chain
   semantics.
3. Add incremental commitments for the `po?;hb*;pb*;prop;po` links and prove
   `rb` irreflexivity for every completed run.
4. State a declarative finite candidate graph independently of runs and prove
   that every consistent candidate can be scheduled without selecting all
   choices in the initial state.
5. Instantiate snapshot obligations with Iris ghost state and prove the
   intended reclamation update.

If step 3 or 4 forces a final-graph oracle, pivot to a hybrid
operational-axiomatic/AxSL-style design in which local execution is
operational and memory/RCU link obligations are discharged by a separate
finite graph judgment.

## Reproduction

```sh
make clean
make check
rg -n 'Admitted\.|admit\.|Axiom ' theories
```
