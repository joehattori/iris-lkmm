# Prototype scope

The feasibility kernel includes finite event identifiers, read/write labels,
normal-RCU lock/unlock and grace-period labels, canonical program order,
finite candidate `rf`, `co`, `rmw`, and direct dependencies, derived `prop`,
`hb`, and `pb`, computed nested critical sections, `rcu-link`, `rcu-order`,
`rcu-fence`, `rb`, and `rb` irreflexivity.
It also includes finite GP/inverse-RSCS chains, signed obligation balances,
and their proved equivalence to recursive `rcu-order`.
The operational scope includes emitted-event integrity, a finite graph view
over canonical events, derived `prop`/`hb`/`pb`, completed snapshot coverage,
and the proved coverage-to-chain refinement.  It includes an
incremental finite graph builder with explicit `rcu-link` witnesses and deltas
for all five selected consistency checks, a proof of full relational
consistency and structural `rf`/`co`/`rmw` prefix validity for every builder
run, an independent declarative candidate type, and finite
candidate scheduling completeness from a fixed empty initial builder.  The
Core-driven machine and builder are combined by an asynchronous
delayed-commitment semantics with RCU soundness and relative candidate
scheduling theorems.

The Iris feasibility scope includes exclusive reader tokens, authoritative
pending/done GP registrations, a MaxNat completion epoch, a framed
reclamation update, and a proved bridge from completed machine certificates
to that update's snapshot-clear premise.  This bridge applies to Core-driven
machine and coupled runs, with explicit authoritative ownership and a
registered pending-GP token.

The incremental prototype includes fixed concurrent agents and the five
gate-language instructions.  It carries finite `rf`, `co`, and `rmw`
candidates and generated direct dependencies, and validates structural prefix
obligations at each commitment.
It does not choose those relations or enforce their completion-only totality
conditions.  The five-instruction gate language itself excludes values,
locations, barriers, dependency-producing expressions, RMW instructions,
SRCU, and locks.  Full LKMM operational consistency, Iris WP/adequacy, and the
`percpu_ref` case study remain outside the prototype.

The LKMM-Core scope includes finite structured programs,
register-origin dependency provenance, memory and RMW event generation, a
base-only `core_candidate`, and the declarative `program_graph` relation.
`lkmm_consistent` derives the selected relational consistency constraints from
that candidate.  `lkmm_machine.v` defines Core-driven execution with normal-RCU
snapshot waiting, a projection into Core runs, and reader/certificate safety
proofs.  `lkmm_coupled.v` connects this machine to the incremental RCU builder
with generated-event/relation provenance guards and exact agreement at
completion.
It proves Core-run projection, LKMM consistency, snapshot safety, and relative
scheduling for candidates backed by complete snapshot-machine runs.
`coupled_run_program_graph` connects completed runs to `program_graph` under
explicit `rf`/`co` well-formedness obligations.  Core execution proves
well-formedness of its generated RMW and direct-dependency relations.  The
builder commits those generated relations and derives `hb`/`pb` from them.
Validating the base choices generally, unrestricted operational completeness,
Iris WP/adequacy, and source-language refinement remain outside this coupling. The
gate machine is separate.
