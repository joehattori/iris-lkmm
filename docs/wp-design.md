# Graph-relative WP

## Design

The logic reasons about one complete candidate graph at a time. All agents
share that graph, and program-level reasoning quantifies over the consistent
candidates. The candidate is a proof parameter outside the operational state.
It can justify a read from a write emitted later, without transferring ownership
from that write.

The [execution domain](../theories/logic/graph_correspondence.v) retains the
actual schedule and RCU protocol state. It covers positions in complete
executions satisfying the final reads-from and coherence obligations.

## Resources and composition

Initial resources come from the program independently of the candidate. The
[state interpretation](../theories/logic/state_interp.v) connects those resources
to the current execution prefix. Agents carry thread and RCU protocol tokens;
shared invariants coordinate access to memory ownership.

[Memory ownership](../theories/logic/memory_ghost.v) describes emitted write
histories. Reads retain a fractional share; writes require full ownership to
extend the history. A read's value comes from the complete candidate and may
be absent from the owned history.

The [client RCU protocol](../theories/logic/wp_rcu_client.v) keeps protected
resources in a shared invariant. Admission lends access to a reader until it
returns its loan before unlocking. Retirement closes admission; a subsequent
grace period covers the outstanding readers and recovers the protected
resources on completion. Clients must justify admission through their
publication protocol: observing a pointer alone does not grant access.

The [WP](../theories/logic/wp.v) retains continuations and dependency provenance.
[Parallel composition](../theories/logic/wp_parallel.v) follows the supplied
schedule around one state interpretation. Postconditions remain inside Iris
under guarded updates; extracting an external guarantee requires adequacy.

## Remaining work

- External adequacy and safety for arbitrary execution prefixes. Termination
  and grace-period liveness are outside the intended guarantee.
