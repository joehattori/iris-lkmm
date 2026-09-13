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
All machine-step kinds are covered. Builder steps have their own preservation
result; scheduling and composition of the per-agent judgments belong to the
surrounding execution proof. This separation keeps primitive reasoning local
while leaving the shared execution graph fixed.

Consequence allows clients to weaken postconditions without revisiting the
operational proof. Preconditions are ordinary Iris assertions, so strengthening
them uses Iris entailment.

## Remaining work

- **Structural rules:** derive framing, sequencing, assignment, branching,
  and fixed-agent parallel composition.
- **Memory rules:** design the ownership assertions and specifications for
  initialization, read-only loads, and stores, then extend to the selected
  access modes, fences, dependencies, and RMWs. Prove the initialized-load WP
  example while retaining permitted reads from writes emitted later.
- **RCU ownership protocol:** connect the primitive RCU rules to a client
  protocol that justifies reclamation.
- **Adequacy and prefix safety:** combine resource initialization and per-agent
  WPs into guarantees for coupled executions. Current domain positions have
  complete execution witnesses; safety for arbitrary raw prefixes still needs
  a separate argument. No termination or grace-period liveness claim is intended.
