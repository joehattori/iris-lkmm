# Graph-relative WP

## Design

Use a custom graph-relative Iris WP, universally quantified over complete
candidates satisfying `program_graph P G` and `lkmm_consistent G`. All local
thread judgments and successive statements share the same `G`.

The candidate is a proof parameter; operational states and transition rules
remain unchanged. Its `rf` and `co` relations are available independently of
builder progress. Knowing a read's source does not itself transfer Iris
ownership from that write, especially when the write is emitted later.

## Implemented

Stage 1 provides the [execution domain](../theories/logic/graph_domain.v) and
[Iris quantifier interface](../theories/logic/graph_judgment.v). Definitions
and their invariants are documented in those files. The guarded WP and its
resource interpretation remain to be implemented.

[Domain regressions](../theories/examples/graph_domain_examples.v) include
rejection of the initialized-load value `42` and an LKMM-consistent read from
a write emitted later. These are graph-level results; WP load rules still
require resource reasoning.

## Remaining stages

2. **Correspondence:** cover every accepted coupled execution, preserving its
   actions, intermediate machine information, and event-ID correspondence.
   Core positions omit pending-GP snapshots, certificates, and builder actions.
   A replay of the same final graph is insufficient for trace-sensitive claims;
   reverse graph coverage need only establish existence up to renaming.
3. **State interpretation and WP:** allocate the initial Iris resources,
   maintain them across steps, and define the guarded WP.
4. **Structural rules:** consequence, framing, sequencing, assignment,
   branching, and fixed-agent parallel composition.
5. **Memory rules:** begin with initialization, read-only loads, and stores,
   then extend to the selected access modes, fences, dependencies, and RMWs.
   Prove the initialized-load WP example while retaining permitted future sources.
6. **RCU rules:** connect the reader/GP protocol to WP and establish the client
   ownership protocol needed for reclamation.
7. **Adequacy and prefix safety:** justify the initial resources and prove the
   claims for coupled executions. Current positions have complete Core witnesses;
   their domain lemmas do not establish safety for arbitrary raw prefixes.
