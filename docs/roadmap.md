# Project roadmap

This document records the project goals, theorem targets, and development
plan. See the [README](../README.md) for implemented results.

## Project Goal

Build a Rocq/Iris foundation for compositional reasoning about Linux-kernel concurrency under an upstream-aligned fragment of the Linux Kernel Memory Model (LKMM), including normal RCU.

The final project should combine:

- A manually transcribed Rocq model of the selected LKMM fragment
- An incremental operational semantics for that fragment
- A sound Iris program logic
- A mechanized model of a kernel data structure such as `percpu_ref`

## Scope

### Included

- `READ_ONCE`, `WRITE_ONCE`
- Acquire and release accesses
- `smp_mb`, `smp_rmb`, `smp_wmb`
- Address, data, and control dependencies
- Relaxed and ordered RMWs, including failed conditional RMWs
- Coherence, `hb`, propagation, and `pb` relations required by the fragment
- `rcu_read_lock`, `rcu_read_unlock`, and nested read-side critical sections
- `synchronize_rcu` and the normal-RCU `rb` constraint
- Finite executions

### Excluded

- Verification of the Tree RCU implementation
- SRCU and specialized RCU variants
- Plain accesses and LKMM race diagnostics
- Kernel lock semantics unless later required
- Scheduler, CPU-hotplug, interrupt, workqueue, and callback implementations
- Grace-period liveness
- General C or Rust source semantics in the first phase

The project verifies clients of the abstract RCU contract. The kernel RCU implementation remains outside the verification boundary.

## Model Boundary

Use Linux Git tag `v6.18`.

Record the relevant definitions and source from:

- `tools/memory-model/linux-kernel.def`
- `tools/memory-model/linux-kernel.bell`
- `tools/memory-model/linux-kernel.cat`
- `include/linux/percpu-refcount.h`
- `lib/percpu-refcount.c`

Define the supported graph and program fragment precisely.

`LKMMConsistent(G)` is the Rocq predicate obtained by manually translating the selected upstream LKMM definitions. The correctness of this transcription is initially part of the trusted boundary.

Validate the transcription through:

- A line-by-line mapping to the pinned upstream files
- Rocq outcome proofs for official and project-specific litmus tests
- Independent review of translated relations

Automated checks compile the Rocq proofs without running `herd7`. Document
the pinned upstream source links and litmus-to-Core mappings. Proofs about
the transcribed model do not establish its correspondence with upstream.

Do not claim machine-checked equivalence with the upstream CAT file unless a formal CAT semantics or verified translation is later added.

## Semantic Architecture

Keep these layers separate:

1. **Relational LKMM model**
   - Events, labels, `po`, `rf`, `co`, `fr`, dependencies, and RMW pairing
   - Derived LKMM relations and consistency constraints
   - RCU critical-section matching and grace-period ordering

2. **LKMM-Core language**
   - Small register-based, event-generating IR
   - Fixed concurrent agents rather than Linux `fork`
   - Explicit dependency provenance
   - No general C- or Rust-specific undefined behavior initially

3. **Incremental operational semantics**
   - Each run constructs one finite execution graph
   - Nondeterminism produces multiple possible runs and graphs for a program
   - May use partial graphs, symbolic obligations, or delayed commitment
   - Must not define steps by directly invoking final-graph consistency

4. **Iris logic**
   - WP and primitive rules derived from the operational semantics
   - No axiomatized Hoare triples for LKMM operations
   - Adequacy proved against operational executions

5. **Case-study model**
   - Relevant kernel methods manually transcribed into LKMM-Core/Rocq
   - Refinement proved against an abstract data-structure specification
   - Source-to-core correspondence remains trusted until separately verified

## Main Theorems

Use the existing predicates from `LkmmProgramGraph` and `LkmmOperational`
directly (unqualified below):

- `program_graph P G`: `G` is a well-formed candidate execution graph of program `P`
- `lkmm_consistent G`: `G` satisfies the manually transcribed Rocq LKMM fragment
- `lkmm_run P (initial_lkmm P) actions s`: machine and builder steps reach `s` from the initial operational state
- `lkmm_complete s`: the machine has completed and the builder agrees with its generated events and relations
- `lkmm_program_graph_obligations s`: the extracted `rf` and `co` satisfy their completion-time well-formedness conditions
- `lkmm_candidate s`: the candidate graph extracted from the builder in `s`

### RCU-law equivalence

Prove that the constructive operational formulation of grace-period ordering is equivalent to the Rocq CAT-style RCU condition.

### Operational soundness

```text
lkmm_run P (initial_lkmm P) actions s
->
lkmm_complete s
->
lkmm_program_graph_obligations s
->
program_graph P (lkmm_candidate s) /\ lkmm_consistent (lkmm_candidate s)
```

Every completed operational execution satisfying the explicit `rf`/`co`
obligations is permitted by the Rocq LKMM model. This is the existing
`LkmmOperational.lkmm_run_soundness` theorem.

### Operational completeness

```text
program_graph P G /\ lkmm_consistent G
->
exists actions s,
  lkmm_run P (initial_lkmm P) actions s /\
  lkmm_complete s /\
  lkmm_program_graph_obligations s /\
  lkmm_candidate s ~= G
```

Every finite graph permitted by the Rocq LKMM model can be generated by at
least one completed operational run, up to event-ID renaming (`~=`). This is
`LkmmOperational.lkmm_run_completeness`, where the correspondence is stated as
`candidate_renaming f G (lkmm_candidate s)` for an existentially chosen `f`.

### Iris adequacy

```text
WP(P, Phi)
->
forall actions s,
  lkmm_run P (initial_lkmm P) actions s ->
  lkmm_complete s ->
  lkmm_program_graph_obligations s ->
  Phi(actions, s)
```

Every proved program satisfies its postcondition on every completed operational
execution meeting the completion obligations. `WP` and `Phi(actions, s)` are
schematic goals for the future logic, with its initial resources justified;
execution-prefix safety must also be established. No termination or
grace-period liveness claim is intended.

### Optional checker reflection

```text
check(G) = true <-> lkmm_consistent G
```

This validates an executable checker against the Rocq predicate. It does not validate the manual CAT-to-Rocq transcription.

## Feasibility Gate

Do not build the full language or Iris logic before completing the following prototype.

### RCU graph kernel

Formalize finite graphs containing:

- Program order
- Abstract `hb`, `prop`, and `pb`
- Matched read-side critical sections
- Grace-period events
- The CAT-style RCU ordering and `rb` condition

Mechanize equivalence between the recursive RCU condition and a constructive grace-period law.

### Incremental RCU prototype

Use a minimal language with:

```text
read
write
rcu_read_lock
rcu_read_unlock
synchronize_rcu
parallel agents
```

Attempt finite operational soundness and completeness.

Proceed with the operational design only if:

- The RCU law admits a constructive incremental representation
- Soundness does not follow merely by embedding `LKMMConsistent` into each step
- Completeness does not require choosing the entire final graph up front
- The operational state supports a compositional Iris reclamation rule

If these conditions fail, evaluate a hybrid or AxSL-style operational-axiomatic design.

## Validation

Maintain examples covering:

- Release/acquire message passing
- Store buffering
- Address, data, and control dependencies
- Successful and failed `cmpxchg`
- One reader and one grace period
- Multiple readers and grace periods
- Nested RCU read-side sections
- RCU chains involving propagation

Check finite outcomes with Rocq existential and forbidden-outcome proofs as
part of `make check`. Keep the Linux `v6.18` litmus-to-Core mappings explicit;
automated validation does not execute `herd7`.

## Case Study Direction

The initial mechanized case study is a manual LKMM-Core/Rocq transcription of the relevant `percpu_ref` C methods from Linux `v6.18`.

The initial formal claim is:

```text
ConcretePerCpuRefModel ⊑ AbstractPerCpuRef
```

It applies to the transcribed core-language model, not automatically to the upstream C source or a Rust reimplementation.

Include the nontrivial implementation paths needed for a coherent lifecycle proof, such as:

- Reference acquisition and release
- Live-reference checks
- Per-CPU and atomic modes
- Mode switching and count aggregation
- Kill confirmation
- Final release
- Reinitialization if used by the selected client

The abstract specification should cover:

- Reference accounting
- Lifecycle transitions
- Shutdown and reclamation guarantees
- Mode-switch transparency
- A realistic client protocol

A Rust implementation or safe Rust API is a possible later extension. It requires a separate source-to-core or semantic-typing argument and is not assumed in the initial case-study theorem.
