# Prototype scope

The feasibility kernel includes finite event identifiers, read/write labels,
normal-RCU lock/unlock and grace-period labels, canonical program order,
finite candidate `rf`, `co`, and `rmw`, derived `prop`, abstract `hb`/`pb`, computed
nested critical sections, `rcu-link`, `rcu-order`, `rcu-fence`, `rb`, and
`rb` irreflexivity.
It also includes finite GP/inverse-RSCS chains, signed obligation balances,
and their proved equivalence to recursive `rcu-order`.
The operational scope includes emitted-event integrity, a finite graph view
over canonical events, derived `prop`, and abstract `hb`/`pb`, completed snapshot
coverage, and the proved coverage-to-chain refinement.  It now also includes an incremental
finite graph builder with explicit `rcu-link` witnesses and `rb` deltas, a
proof of `rb` irreflexivity for every builder run, an independent declarative
candidate type, and finite candidate scheduling completeness from a fixed
empty initial builder.  The Core-driven machine and builder are combined by
an asynchronous delayed-commitment semantics with RCU soundness and relative
candidate scheduling theorems.

The Iris feasibility scope includes exclusive reader tokens, authoritative
pending/done GP registrations, a MaxNat completion epoch, a framed
reclamation update, and a proved bridge from completed machine certificates
to that update's snapshot-clear premise.  This bridge applies to Core-driven
machine and coupled runs, with explicit authoritative ownership and a
registered pending-GP token.

The incremental prototype includes fixed concurrent agents and the five
gate-language instructions.  It carries finite `rf`, `co`, and `rmw`
candidates but does not yet generate or validate them.  It deliberately
excludes values, locations, graph-level `fr`, barriers, dependencies, RMW
instruction semantics, SRCU, locks, the full LKMM consistency predicate, Iris
WP/adequacy, and the `percpu_ref` case study.

The separate LKMM-Core milestone now includes finite structured programs,
register-origin dependency provenance, memory and RMW event generation, a
base-only `core_candidate`, and the declarative `program_graph` relation.
`lkmm_consistent` derives the selected relational consistency constraints from
that candidate.  `lkmm_machine.v` adds Core-driven execution with normal-RCU
snapshot waiting, a projection into Core runs, and reader/certificate safety
proofs.  `lkmm_coupled.v` connects this machine to the incremental RCU builder
with generated-event/RMW provenance guards and exact agreement at completion.
It proves Core-run projection, RCU consistency, snapshot safety, and relative
scheduling for candidates backed by complete snapshot-machine runs.
`coupled_run_program_graph` connects completed runs to `program_graph` under
explicit relation well-formedness obligations.  The extracted candidate uses
machine-generated direct dependencies; the builder does not commit those
sets.  RCU consistency transfers to the candidate when the builder covers its
derived `hb`/`pb`.  Discharging these obligations generally, full LKMM
operational soundness/completeness, Iris WP/adequacy, and source-language
refinement remain outside this coupling.  The existing gate machine remains
separate.
