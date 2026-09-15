# Graph-relative WP

## Design

The logic reasons about one complete candidate graph at a time. All agents
and successive statements share that graph, and program-level reasoning
quantifies over the consistent candidates. This keeps local assumptions about
reads, coherence, and dependencies compatible throughout a proof.

The candidate is a proof parameter, outside the operational state. Its
reads-from relation may refer to a write emitted later. Knowing that source
provides a graph fact, not ownership transferred from the write.

## Resources and composition

The [execution domain](../theories/logic/graph_correspondence.v) retains the
actual coupled schedule and RCU protocol state. Local judgments use positions
within complete executions satisfying the final reads-from and coherence
obligations. This supports reasoning about accepted executions, but leaves
safety for arbitrary raw prefixes as a separate problem.

The [state interpretation](../theories/logic/state_interp.v) connects Iris
resources to the current prefix. Initial resources come from the program
independently of the candidate. Authoritative state is shared by the execution;
individual agents carry their thread and RCU protocol tokens. Event facts
record emission without granting ownership of memory locations.

The [WP](../theories/logic/wp.v) follows each agent's continuation, retaining
register and control-dependency provenance. Its rules derive resource updates
from operational steps. [Parallel composition](../theories/logic/wp_parallel.v)
combines the agents around one state interpretation and follows the supplied
schedule, including builder actions. Its postconditions remain inside Iris
under guarded updates; extracting an external guarantee requires adequacy.

## Remaining work

- Memory ownership rules that accommodate reads from later-emitted writes.
- A client RCU protocol that connects grace-period completion to reclamation.
- External adequacy and safety for arbitrary execution prefixes. Termination
  and grace-period liveness are outside the intended guarantee.
