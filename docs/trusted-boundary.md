# Trusted boundary

For the feasibility prototype, the trusted boundary includes:

- the manual reading and transcription of the cited Linux v6.18 CAT/Bell
  definitions;
- the input graph's finite event list, abstract `po`, `hb`, `prop`, and
  `pb` relations;
- the precomputed list of correctly matched, properly nested normal-RCU
  critical sections;
- the claim that the small instruction language represents the intended
  client operations;
- propositional excluded middle in the finite candidate completeness proof,
  used only to partition successor `rb` pairs into already-seen and new
  pairs.  The builder soundness theorem is constructive and closed under
  Rocq's global context.

Rocq checks the recursive/independent-chain equivalence, the generic
list/counter characterization, operational event integrity, and the
snapshot-to-chain refinement conditional on explicit `rcu-link` witnesses.
It also checks monotonicity of the RCU graph relations, persistence and
soundness of incremental link commitments, the `rb` monitor invariant,
irreflexivity for every builder run, and finite candidate scheduling
completeness.  The coupled layer checks program-machine projection,
program-scoped soundness/completeness, reader-stack uniqueness, and the
snapshot-clear premise for completed GP certificates.  Iris checks exclusive
reader entry/exit, registered pending/done GP transitions, monotone epoch
advancement, persistence of completion certificates, arbitrary-frame
preservation, and the direct completed-machine-GP reclamation rule.
It does **not** establish equivalence with CAT syntax, construct the abstract
memory relations, prove correct Bell matching, establish correspondence with
Linux C, show `herd7` agreement, or prove full Iris WP adequacy.
