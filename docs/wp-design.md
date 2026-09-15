# Graph-relative WP

## Design

The logic reasons about one complete candidate graph `G` at a time. The
program-level quantifier interface ranges over candidates satisfying
`program_graph P G` and `lkmm_consistent G`. Local thread judgments and
successive statements share the same `G`, so their assumptions about an
execution remain compatible throughout a proof.

The candidate is a proof parameter; operational states and transition rules
remain unchanged. Its `rf` and `co` relations are available independently of
builder progress. Knowing a read's source does not itself transfer Iris
ownership from that write, especially when the write is emitted later.

## Architecture

The [execution domain](../theories/logic/graph_domain.v) describes positions
within complete candidate executions. Its
[coupled correspondence](../theories/logic/graph_correspondence.v) connects
these positions to the machine and incremental builder, retaining the actual
schedule and event IDs as well as the RCU state that Core projection omits.
Completeness supplies coverage of permitted graphs up to event-ID renaming.
The [candidate](../theories/logic/graph_judgment.v) and
[coupled](../theories/logic/coupled_graph_judgment.v) quantifier interfaces make
this domain available to Iris assertions; the execution domain is separate
from the recursive WP and its eventual adequacy proof.

The [state interpretation](../theories/logic/state_interp.v) connects Iris
resources to the current execution prefix. It accounts for thread state,
emitted events, and the reader/grace-period protocol, with initial resources
allocated from the program independently of a final candidate. This provides
the resource foundation for primitive rules. Memory ownership and client
reclamation protocols must be built on that foundation.

The [guarded WP](../theories/logic/wp.v) is a per-agent judgment over this shared
domain. Its lifting interface connects operational steps to resource
preservation, including the [primitive RCU rules](../theories/logic/wp_rcu.v).
All machine-step kinds are covered. The
[parallel composition](../theories/logic/wp_parallel.v) combines the fixed
agents' WPs and thread tokens around one shared state interpretation. It follows
the supplied execution schedule, preserving other agents' local views and
handling builder steps separately. At completion it collects all postconditions
by separating conjunction. The resulting Iris assertion retains a guarded
update for each coupled action; extracting an external guarantee belongs to
adequacy.

Consequence allows clients to weaken postconditions without revisiting the
operational proof, and framing carries separately owned resources through that
proof. Preconditions are ordinary Iris assertions, so strengthening them uses
Iris entailment. Sequencing follows the thread's explicit continuation, keeping
the remaining statements and surrounding control context in the local judgment.
Register assignments carry expression values and their dependency provenance
through this continuation. Branching scopes the condition's origins to the
chosen branch while retaining any enclosing control scopes, so later operations
see the dependency context for their location in the program.

## Remaining work

- **Memory rules:** design the ownership assertions and specifications for
  initialization, read-only loads, and stores, then extend to the selected
  access modes, fences, dependencies, and RMWs. Prove the initialized-load WP
  example while retaining permitted reads from writes emitted later.
- **RCU ownership protocol:** connect the primitive RCU rules to a client
  protocol that justifies reclamation.
- **Adequacy and prefix safety:** connect resource initialization and the guarded
  parallel-execution result to external guarantees. Current domain positions have
  complete execution witnesses; safety for arbitrary raw prefixes still needs
  a separate argument. No termination or grace-period liveness claim is intended.
