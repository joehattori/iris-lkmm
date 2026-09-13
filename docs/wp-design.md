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
[Iris quantifier interface](../theories/logic/graph_judgment.v).

Stage 2 proves [coupled correspondence](../theories/logic/graph_correspondence.v):
every accepted run and each of its cuts project to the Core domain, preserving
the actual schedule and event IDs. Coupled witnesses retain pending-GP snapshots,
certificates, and builder state. Reverse graph coverage uses existing completeness
up to renaming; it does not prescribe a schedule. The
[coupled quantifier interface](../theories/logic/coupled_graph_judgment.v)
specializes Core assertions to these witnesses.

Stage 3 starts with the [state interpretation](../theories/logic/state_interp.v):
authoritative thread and emitted-event maps, the builder's generated-prefix
invariant, and RCU resources matching current readers, pending GPs, and completed
certificates. Its allocation theorem supplies initial thread tokens and persistent
initialization-event facts for any program, without a final-graph premise.
The final graph remains in the execution domain. Ordinary machine steps preserve
the interpretation, update the acting thread's token, and supply persistent facts
for newly emitted events. They use allocation well-formedness from the execution
prefix. Builder steps preserve the interpretation without changing ghost resources.
Read-lock steps allocate a fresh reader token; read-unlock steps consume the
innermost token while preserving outer readers and captured GP snapshots.
GP-begin steps register the captured reader set and supply a pending token.
GP-finish steps consume that token, advance the completion epoch, and supply
persistent completion and synchronization-event facts. Their additional
`certificate_events_allocated` premise follows from machine runs. Preservation
now covers every step kind.

The [WP body](../theories/logic/wp.v) takes its recursive continuation as a
parameter. Its local view includes the Core view and pending-GP snapshot, so
GP begin and finish remain distinct. It handles the scheduled agent's steps
along every accepted execution witness, keeping `G` fixed; recursion is under
`▷` and mask-changing updates. The execution supplies `state_interp` and the
thread token, while reader and GP tokens come from the proof's resources.
Contractiveness is proved; `wp` is its guarded fixed point, with `wp_unfold`
exposing one layer. Step-lifting rules remain to be implemented.

[Domain regressions](../theories/examples/graph_domain_examples.v) include
rejection of the initialized-load value `42` and an LKMM-consistent read from
a write emitted later. These are graph-level results; WP load rules still
require resource reasoning.
[Correspondence regressions](../theories/examples/graph_correspondence_examples.v)
cover the read-before-write trace, GP state omitted by Core projection, and renaming.

## Remaining stages

3. **State interpretation and WP:** connect the resource-preservation lemmas
   to the guarded WP through step-lifting rules.
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
