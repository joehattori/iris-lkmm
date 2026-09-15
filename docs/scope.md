# Current scope

The selected Linux v6.18 fragment covers finite executions with ONCE and
acquire/release accesses, memory fences, address/data/control dependencies,
relaxed and ordered RMWs, failed conditional RMWs, and normal RCU with nested
reader sections and synchronization. The relational model includes coherence,
happens-before, propagation, and RCU ordering constraints. Recursive RCU
ordering is proved equivalent to a finite chain characterization.

LKMM-Core has fixed agents, registers, mathematical integer values, and
loop-free structured programs. Memory locations come from a finite initial
map. Dependency provenance is retained syntactically. The relational vocabulary
can represent unannotated accesses, but Core has no plain-access instructions
or race diagnostics.

The operational semantics combines RCU snapshot waiting with incremental graph
construction. Completed runs satisfy the relational model under explicit
reads-from and coherence well-formedness obligations. Conversely, every
consistent program graph admits a completed run up to event-ID renaming.
See the [semantic architecture](semantics.md) for the design.

The [Iris logic](wp-design.md) has a state interpretation, a guarded per-agent
WP, primitive RCU rules, and parallel composition over accepted executions.
Initial resources come from the program; memory ownership tracks emitted write
histories. A client RCU protocol recovers protected ownership after retirement
and a grace period. External adequacy and safety for arbitrary execution
prefixes remain open.

Differential testing against `herd7`, source-language refinement, and the
`percpu_ref` case study remain future work. SRCU, kernel locks, verification of
the kernel's RCU implementation, and grace-period liveness are outside the
selected fragment.
