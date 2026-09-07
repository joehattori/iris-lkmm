# Trusted boundary

For the current LKMM-Core prototype, the trusted boundary includes:

- the manual reading and transcription of the cited Linux v6.18 CAT/Bell
  definitions;
- the claim that LKMM-Core represents the intended client operations;
- the mapping from LKMM-Core constructors to the selected Linux v6.18
  operations, pending differential testing and a later source-to-core
  refinement;
- propositional excluded middle in the finite candidate completeness proof,
  used only to partition the five successor relations into already-seen and new
  pairs.  The builder soundness theorem is constructive and closed under
  Rocq's global context.

Rocq computes normal-RCU matching from the canonical event map and proves
endpoint tags, agent/order shape, endpoint uniqueness, non-crossing nesting,
and total lock/unlock coverage for complete candidates.  The per-agent
relation is equivalent to its aggregate Bell view, and completeness is
equivalent to both Bell unmatched-event flags being empty.  Rocq also checks
the recursive/independent-chain equivalence and the generic
list/counter characterization independently of operational executions.
It also checks monotonicity of the RCU graph relations, persistence and
soundness of incremental link commitments, monotonicity of derived propagation,
the five-relation consistency monitor invariant, structural validity of every
committed base and direct-dependency prefix, full consistency for every builder
run, and finite candidate scheduling completeness. Iris checks exclusive reader entry/exit,
registered pending/done GP transitions, monotone epoch advancement,
persistence of completion certificates, and arbitrary-frame preservation.
Rocq also checks LKMM-Core event allocation and provenance, proves generated
RMW and direct-dependency relations well formed for every Core run, and checks
their exact agreement in `program_graph`.  The `rf` and `co` relations remain
finite candidate choices rather than trusted program inputs.
Per-agent Core replay is also mechanized: the original action subsequence
executes with preserved values, branch behavior, RMW pairing, and dependency
origins under an injective renaming of that agent's events. The contextual
replay theorem preserves existing events and edges and other agents' thread
states. Whole-program serialization composes these replays in any enumeration
of all program agents and proves completion of every agent, retaining the
per-agent correspondence certificates and a single renaming for the entire
final Core state. Event renaming preserves program order, computed RCU
matching, and the RCU replay premises. Under those premises, serialized Core
replay also has a nonempty reader stack at every unlock and an empty global
snapshot at every synchronization. These guards are proved from execution
prefixes and final event properties, without changing the transition rules.
These proofs add no axioms and do not yet establish snapshot-machine
reconstruction or full operational completeness.
For the Core-driven RCU machine, Rocq checks run projection into Core,
absence of unmatched unlocks, preservation of completed-section witnesses,
and snapshot-clear safety for completed GP certificates.  Reader bookkeeping
uses the canonical matcher. The Core-aware coupling connects these results
to the builder's LKMM consistency invariant. Every reachable committed event,
RMW pair, and dependency edge comes from the machine; completion requires exact
agreement.
Its scheduling theorem assumes a complete snapshot-machine run
and inherits the candidate scheduler's excluded-middle dependency.  Its
soundness proof adds no axioms.  `coupled_run_program_graph` proves the
`program_graph` connection under explicit `rf`/`co` well-formedness premises;
RMW and direct-dependency well-formedness are derived from the projected Core
run.  The remaining premises are obligations for callers, not new axioms or
transition guards.
LKMM consistency transfers to the extracted candidate because the builder and
candidate share the same fields and derive the same coherence, atomicity,
`hb`, `pb`, and `rb` relations.

`lkmm_machine_ghost.v` derives the Iris snapshot-clear premise from completed
Core-driven GP certificates, including certificates in coupled executions.
The reclamation rules require authoritative ownership of the current open
readers and a registered pending-GP token for the captured snapshot.  They do
not manufacture either from a pure certificate.  No per-step ghost-state
interpretation or full WP adequacy is established by this bridge.

The finite adjacent-unmatched Bell iteration remains a manual Rocq
transcription; its regression agrees with the stack matcher, but this is not
a verified CAT interpreter.  Rocq does **not** establish equivalence with CAT
syntax, select a unique `rf` or `co` relation, establish correspondence with
Linux C, show `herd7` agreement, or prove full Iris WP adequacy.
