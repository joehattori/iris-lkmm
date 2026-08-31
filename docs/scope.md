# Prototype scope

The feasibility kernel includes finite event identifiers, read/write labels,
normal-RCU lock/unlock and grace-period labels, canonical program order,
finite candidate `rf`, abstract `hb`/`prop`/`pb`, computed nested critical
sections, `rcu-link`, `rcu-order`, `rcu-fence`, `rb`, and `rb` irreflexivity.
It also includes finite GP/inverse-RSCS chains, signed obligation balances,
and their proved equivalence to recursive `rcu-order`.
The operational scope includes emitted-event integrity, a finite graph view
over canonical events and abstract `hb`/`prop`/`pb`, completed snapshot
coverage, and the proved coverage-to-chain refinement.  It now also includes an incremental
finite graph builder with explicit `rcu-link` witnesses and `rb` deltas, a
proof of `rb` irreflexivity for every builder run, an independent declarative
candidate type, and finite candidate scheduling completeness from a fixed
empty initial builder.  The program machine and builder are combined by an
asynchronous delayed-commitment semantics with program-scoped soundness and
completeness theorems.

The Iris feasibility scope includes exclusive reader tokens, authoritative
pending/done GP registrations, a MaxNat completion epoch, a framed
reclamation update, and a proved bridge from completed machine certificates
to that update's snapshot-clear premise.

The incremental prototype includes fixed concurrent agents and the five
gate-language instructions.  It carries finite `rf` candidates but does not
yet generate or validate them.  It deliberately excludes values, locations,
`co`, `fr`, barriers, dependencies, RMWs, SRCU, locks, the full LKMM
consistency predicate, Iris WP/adequacy, and the `percpu_ref` case study.
The coupled theorem is the gate-language result, not yet the final full
LKMM-Core `ProgramGraph` theorem.
