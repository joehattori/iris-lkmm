# Current scope

The relational model uses canonical finite events, program order, candidate
`rf`, `co`, `rmw`, and direct dependencies, and derived `prop`, `hb`, and `pb`.
It includes computed nested RCU critical sections, `rcu-link`, `rcu-order`,
`rcu-fence`, and `rb`. `graph_consistent` combines coherence, atomicity,
happens-before, propagation, and normal-RCU consistency for the selected
Linux v6.18 fragment. Finite GP/inverse-RSCS chains and signed obligation
balances are proved equivalent to recursive `rcu-order` independently of
program execution.

LKMM-Core provides finite, loop-free structured programs with fixed agents,
registers, values, locations, memory accesses, RMWs, fences, and normal-RCU
instructions. Register-origin provenance generates direct dependencies.
`core_candidate` records graph data, while `program_graph` relates a candidate
to Core execution and structural well-formedness. `lkmm_consistent` applies
the selected relational consistency constraints separately.

`lkmm_machine.v` executes Core programs with normal-RCU snapshot waiting.
Reader stacks and matched sections are computed from canonical events.
Its proofs establish projection into Core runs, allocation well-formedness,
absence of unmatched unlocks, and closure of captured readers for completed
GP certificates. Nested readers and readers entering after GP begin are
covered by the machine regressions.

The incremental graph builder commits events, base relations, dependencies,
and explicit `rcu-link` witnesses. Exact deltas maintain all five consistency
conditions, while relation mutations preserve structural prefix validity.
Finite well-formed, consistent candidates admit a schedule from the fixed
empty builder. `lkmm_coupled.v` interleaves the machine and builder, requiring
generated-event/relation provenance and exact agreement at completion.
`coupled_run_soundness` establishes both `program_graph` and `lkmm_consistent`
under explicit completion-time `rf`/`co` well-formedness obligations.
[Coupled completeness](semantics.md#coupled-operational-completeness)
constructs a completed run for every consistent program graph, up to event-ID
renaming, and proves its completion obligations.

The Iris protocol supplies exclusive reader tokens, authoritative pending/done
GP registrations, a MaxNat completion epoch, and a framed completion update.
Completed Core-machine and coupled GP certificates justify that update's
snapshot-clear premise. Authoritative ownership and a registered pending-GP
token remain explicit resource premises.

A ghost-state interpretation maintained by every step, Iris WP/adequacy,
differential testing against `herd7`,
source-language refinement, and the `percpu_ref` case study remain future
work. SRCU, kernel locks, and grace-period liveness remain outside the selected
fragment.
