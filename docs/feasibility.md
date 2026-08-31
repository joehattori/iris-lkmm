# Feasibility gate assessment

## Verdict

**FEASIBLE.  The feasibility gate is passed.**

Proceed with the incremental operational architecture, using explicit delayed
graph commitments.  A pivot to an AxSL-style operational-axiomatic design is
not required by the normal-RCU prototype.

This verdict is about the project architecture in `AGENTS.md`: it establishes
that the difficult normal-RCU recursion admits an independent constructive
representation, finite graph consistency can be maintained incrementally,
consistent program candidates can be scheduled without a final graph in the
initial state, and completed grace periods support a compositional Iris
reclamation update.  It is not a claim that the full LKMM model, full
LKMM-Core language, Iris WP, or `percpu_ref` verification is already built.

## Gate results

| Gate question | Mechanized evidence | Result |
| --- | --- | --- |
| Does normal-RCU `rcu-order` admit an independent constructive representation? | `rcu_order_chain_equiv` relates the CAT-style recursion to a nonempty linked list of GP/inverse-RSCS atoms with signed final balance. `obligation_derivation_iff` proves the generic list/counter characterization. | **Pass.** |
| Can grace-period waiting be represented incrementally? | `ABeginGp` snapshots exactly the currently open nested reader IDs. `AFinishGp` requires exactly those captured IDs to have closed; readers opened later do not mutate the snapshot. | **Pass.** |
| Do machine snapshots and completed critical sections refine the chain semantics? | `operational_event_integrity` proves the machine's stack and closed-section cache agree with matching computed from canonical events. `completed_run_snapshot_chain_bridge` resolves captured IDs and constructs either valid two-atom chain orientation when its graph link is present. | **Pass.** |
| Can `po?;hb*;pb*;prop;po` links be committed incrementally? | `rcu_link_commitment` stores the four intermediate events. `rcu_link_commitment_sound`/`rcu_link_commitment_complete` prove exact correspondence with `rcu_link`; `commit_ready_rcu_link` and monotonicity make commitments local and persistent under graph extension. | **Pass.** |
| Is `rb` irreflexive for completed executions without embedding final consistency in each step? | Each raw mutation contributes one fact and an exact current-graph `rb` delta. It checks only delta irreflexivity. `builder_step` has no final candidate and no `rcu_consistent` premise. `completed_builder_run_rb_irreflexive` proves the final CAT-style predicate. | **Pass.** |
| Can every finite consistent candidate be generated without preloading the final graph? | `finite_candidate` contains graph data but no run, schedule, or operational state. `consistent_candidate_is_incrementally_schedulable` starts from the single constant `initial_builder` and adds one component at a time. | **Pass.** |
| Does the result extend to the minimal program machine? | `rcu_coupled.v` defines an interleaving product of machine steps and delayed builder commitments. `coupled_operational_soundness` proves minimal `ProgramGraph`, CAT-style RCU consistency, certificate soundness, event integrity, and stack safety. `consistent_program_candidate_is_schedulable` proves program-scoped completeness. | **Pass.** |
| Does the operational state support a compositional Iris reclamation rule? | `rcu_ghost.v` gives readers exclusive ghost-map entries, registers immutable GP snapshots, and advances an authoritative MaxNat epoch on completion. `rcu_gp_finish_frame` preserves an arbitrary client frame and returns a persistent done certificate. | **Pass.** |
| Is the Iris completion premise related to actual completed machine GPs? | `machine_run_stack_safe` proves unique open IDs and disjoint open/closed sections. `completed_run_certificate_enables_iris_finish` derives snapshot/current-open disjointness. `completed_machine_gp_reclamation_frame` composes that fact directly with the framed Iris update. | **Pass.** |

## Why the result is non-vacuous

- Graph extraction does not force `prop`, `rcu_link`, or `rb` to be empty.
  The builder admits explicit nonempty base relations and stores actual link
  witnesses.
- Soundness is an invariant over current facts and new `rb` deltas.  No step
  receives a final candidate or assumes `rcu_consistent`.
- Completeness is target-directed at the meta-level, as expected, but the
  target is absent from `initial_builder` and from `builder_step`.
- The coupled semantics permits delayed commitments explicitly.  Machine
  execution can proceed while the graph builder catches up; completion
  requires exact agreement on canonical event maps and complete computed matching.
- The Iris GP token is registered in an authoritative ghost map.  Completion
  changes it from pending to a persistent done entry, rather than manufacturing
  an unrelated certificate.  Reader exit consumes the reader's exclusive
  token.

## Architectural decision

Use the following design for the next phase:

1. Keep the relational LKMM model independent of Iris.
2. Let the operational machine emit program events and immutable RCU
   snapshots.
3. Let a monotone graph builder commit finite memory relations, RCU links,
   and `rb` deltas asynchronously.
4. Define completed executions by agreement between the emitted-event log and
   committed graph; derive consistency from the builder invariant.
5. Interpret open reader IDs with exclusive Iris ghost-map tokens, pending GPs
   with registered snapshot entries, and completed epochs with persistent
   MaxNat lower bounds.

The prototype therefore supports the intended operational design.  A hybrid
fallback remains a contingency if later, non-RCU LKMM relations defeat local
commitment, but normal RCU does not force that pivot.

## Explicit assumptions and limits

- The CAT/Bell definitions are manually transcribed from Linux v6.18; no
  verified CAT translation is claimed.
- `po` is derived from canonical agent/index positions.  `hb`, `prop`, and
  `pb` remain selected abstract graph-kernel relations rather than the full
  LKMM derivation.
- Candidate completeness uses propositional excluded middle to partition
  successor `rb` pairs into old and new pairs.  This is a proof-level choice,
  not operational state or a final-graph oracle.  A reflected finite checker
  can later remove the classical dependency.
- Grace-period liveness remains out of scope.
- Full WP adequacy, full LKMM operational soundness/completeness, litmus
  differential testing, and the `percpu_ref` case study are next-phase work,
  not feasibility-gate requirements.

## Reproduction

```sh
opam exec -- make clean
opam exec -- make check
rg -n 'Admitted\.|admit\.|Abort\.|Axiom ' theories
```
