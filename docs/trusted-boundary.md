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

The mechanized results, proof constructions, and regression coverage are
documented in [semantics.md](semantics.md). Core replay, the derivation of its
[RCU premises](semantics.md#rcu-replay-premises), machine lifting, and coupled
soundness add no axioms.

Coupled soundness and the `program_graph` connection require explicit `rf`/`co`
well-formedness obligations. These relations remain finite candidate choices;
RMW and direct-dependency well-formedness follow from Core execution. The
obligations are premises for callers, not new axioms or transition guards.

The graph-relative [WP domain](wp-design.md) adds no axioms or operational
transition guards. Its adequacy and prefix-safety obligations remain open.

[Coupled completeness](semantics.md#coupled-operational-completeness)
constructs the compatible machine run and inherits only the candidate
scheduler's existing excluded-middle dependency. Candidate encoding and
renaming add no axioms.

The [Iris completion bridge](semantics.md#iris-reader-and-grace-period-protocol)
assumes ghost ownership supplied by its caller; it does not yet establish a
state interpretation maintained across execution steps.

The finite adjacent-unmatched Bell iteration remains a manual Rocq
transcription; its regression agrees with the stack matcher, but this is not
a verified CAT interpreter.  Rocq does **not** establish equivalence with CAT
syntax, select a unique `rf` or `co` relation, establish correspondence with
Linux C, show `herd7` agreement, or prove full Iris WP adequacy.
