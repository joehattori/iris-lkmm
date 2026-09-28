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
under guarded updates; [adequacy](../theories/logic/adequacy.v) extracts a pure
external guarantee for accepted completed executions.

## Hoare-triple notation

[`hoare.v`](../theories/logic/hoare.v) connects this WP to Iris's existing
`WP` and `{{{ ... }}}` (Texan triple) notation:

```coq
From iris_lkmm.logic Require Import hoare.
Import LkmmHoare.

(* In a section with the usual invGS/stateG instances: *)
Let c := WpContext P G γ agent.

(* For a statement body: *)
(* {{{ Pre }}} body @ c; E {{{ v, RET v; Post v }}} *)
(* WP body @ c; E {{ v, Post v }} *)
```

`c` groups the program, candidate graph, ghost names, and agent. `E` is the
invariant mask (usually `⊤`). The explicit context ensures the graph used by
each agent remains visible. These notations have exactly the existing WP's
completed-execution guarantee; the context is not Iris's stuckness flag.

For a `stmt`, the notation starts at `initial_thread_view body`: empty
registers and continuation, event index zero, empty action history, and no
pending grace period. For an intermediate position, supply an
`lkmm_thread_view` instead of a statement. That form keeps the entire view,
including dependency provenance and pending RCU state.

`RET v` denotes a final thread view. This register-based language has no
HeapLang function-call or `#()` value syntax. A fixed view can be specified
with `{{{ RET final_view; Post }}}`; binders such as `v, RET v` allow the
postcondition to describe final registers and operation receipts.

For example, the message-passing producer now has the proved specification:

```coq
Lemma producer_spec sm lm G γ :
  {{{ shared γ sm }}}
    producer sm @ producer_context sm lm G γ; ⊤
  {{{ v, RET v; producer_post γ sm v }}}.
```

Proofs start with `iIntros (Φ) "Hpre HΦ"`, apply the existing instruction
rules, and finish by applying `HΦ` to the postcondition. Callers can use
`iApply (producer_spec with "Hshared")`. As in Iris, the callback is guarded
by `▷`; execution steps discharge that guard. A terminal `SSkip` has no
step, so use the direct `WP` terminal rule rather than assuming a delayed
callback can be used immediately. In an Iris assertion (`%I`), the triple
also has Iris's usual outer persistence modality.

The [notation examples](../theories/examples/hoare_examples.v) cover fixed
returns, arbitrary masks, owned resources retained by callers, copying with
dependency provenance, and the zero-step terminal case. Both message-passing
thread specifications feed the existing parallel-composition and adequacy
proofs. This layer adds no semantic rules or trust assumptions.

### Whole-program triples

[`program_hoare.v`](../theories/logic/program_hoare.v) also instantiates the
notation for a `core_program`, covering all its agents together:

```coq
From iris_lkmm.logic Require Import program_hoare.
Import LkmmProgramHoare.

(* {{{ Pre }}} P @ WholeProgram; ⊤
   {{{ result, RET result; Post result }}} *)
```

Here `result : program_result` contains the complete action trace and final
machine state. `final_register result agent reg` reads a final register's
integer value and returns `None` if the agent or register is absent. The
program itself specifies initial memory and the fixed concurrent agents;
`True` as the precondition needs no additional client resources. Initial
memory ownership is still allocated by adequacy, and all agents use the same
candidate, universally quantified after setup.

The underlying `program_wp P E Q` factors the existing completed-program
proof interface to accept an Iris postcondition and an explicit mask. The
old `completed_program_wp P Q` is definitionally its instance at `⊤` with a
pure postcondition, so the existing adequacy theorem and its assumptions are
unchanged. The external result continues to concern accepted completed runs.

`program_wp_spec` turns a closed pure-outcome proof into a specification
with Iris's delayed callback. It requires a designated agent whose initial
statement is not `SSkip`; `wp_frame_later` carries the callback through that
agent's first step and retains it until completion. This is necessary even
for callbacks that own resources. Programs with no active agent use the
direct whole-program `WP`, without claiming a step that eliminates `▷`.

The [whole-test message-passing triples](../theories/tests/message_passing_hoare.v)
cover all four message-passing variants. Their `registers_are result r0 r1`
assertion describes agent 1's registers 0 and 1. The existential triples below
witness `(1:r0=1 /\ 1:r1=0)` for the three weaker variants. The existing
`mp_release_acquire_adequate` Iris theorem proves `r0 = 1 -> r1 = 1` for
every accepted completed release/acquire execution; it directly refutes the
corresponding existential triple. No separate per-variant universal triple
wrappers are needed for these outcome claims.

### Existential execution triples

`program_hoare.v` defines a separate, pure reachability judgment with `?`
after the entire triple:

```coq
Theorem mp_once_once_possible :
  {{{ True }}} program StoreOnce LoadOnce
  {{{ result, RET result; registers_are result 1%Z 0%Z }}}?.
```

This asserts that an accepted completed operational execution exists with
the specified final registers. The underlying definition is:

```coq
Definition program_may P (Pre : Prop) (Post : program_result -> Prop) : Prop :=
  Pre -> exists actions final,
    lkmm_run P (initial_lkmm P) actions final /\
    lkmm_complete final /\ lkmm_program_graph_obligations final /\
    Post (ProgramResult actions final).
```

The program fixes initial memory and agent bodies. `Pre` is a pure premise
about its parameters, not ownership supplied to Iris; a false precondition
makes the conditional judgment vacuous. With `True`, the proof must supply
an actual run. `Post` is also a Rocq proposition, so it uses neither Iris's
`⌜...⌝` embedding nor separating conjunction. There is no invariant mask.
The ordinary Iris triples retain their universal meaning and resource rules.

Postcondition binders are existential. `result, RET result; Q` binds the
actual result, and multiple binders can introduce further witnesses. The
fixed form `RET result; Q` requires the witnessed trace and final state to
equal the supplied result. The final `?` is distinct from Iris's
`e ? {{{ ... }}}` notation for `MaybeStuck`.

The three `mp_*_possible` proofs use the existing consistent-graph witnesses
and `lkmm_run_completeness`. The `reads_closed` Iris proof and its adequacy
corollary connect final register values to read receipts. `bad_outcome_registers`
then uses unique agent-local event positions to identify the witnessed values
after event-ID renaming. These proofs inherit completeness's existing
excluded-middle dependency and introduce no axioms or semantic rules.

`mp_release_acquire_not_possible` refutes the same `(1,0)` existential triple
using the existing universal release/acquire adequacy theorem. The regression
file also exercises fixed returns and multiple existential binders.

## Completed-execution adequacy

The first external theorem is partial correctness for accepted completed
operational executions. Let `Q : list lkmm_action -> lkmm_state -> Prop`
be the external property of the actual trace and final state. The proved
theorem `LkmmAdequacy.wp_adequacy` is:

```coq
Theorem wp_adequacy {Σ : gFunctors} `{!invGpreS Σ, !stateG Σ}
    P (Q : list lkmm_action -> lkmm_state -> Prop) :
  (forall `{!invGS Σ}, ⊢ completed_program_wp P Q) ->
  forall actions final,
    lkmm_run P (initial_lkmm P) actions final ->
    lkmm_complete final ->
    lkmm_program_graph_obligations final ->
    Q actions final.
```

The helper definitions below specify its Iris premise and are implemented in
[`adequacy.v`](../theories/logic/adequacy.v). They use the existing
`all_candidates`, `wp`, `state_interp`, and execution-position definitions.
Their Iris context is `{!invGS Σ, !stateG Σ}`. The definitions below show the
expanded pure specialization; the implementation shares `agent_wps_at` and
`program_wp` with the whole-program triple interface.

### Initial resources

The client receives the initial event facts and full ownership of each
initialized location's write history:

```coq
Definition initial_resources P γ : iProp Σ :=
  ([∗ map] eid ↦ ev ∈ core_initial_events P, event_fact γ eid ev) ∗
  ([∗ map] loc ↦ val ∈ P.(program_initial_memory),
    memory_own γ.(memory_names_of) loc 1
      (write_history (core_initial_events P) loc)).
```

The adequacy proof allocates these resources using `state_interp_alloc_memory`.
It retains `state_interp γ (initial_lkmm P)` and the initial thread tokens
for `wp_parallel_init`. The client may split memory ownership, establish shared
invariants, and allocate additional ghost resources using Iris allocation rules.
The ambient `Σ` may include the client's additional ghost resource functors.
There is no assumed, separately supplied client resource assertion.

### Agent proofs and final assertions

Each agent starts at its actual initial view, at the full invariant mask `⊤`.
The postconditions `Φ` are Iris assertions and may depend on the candidate and
on ghost names allocated during setup:

```coq
Definition agent_wps P G γ
    (Φ : agent_id -> lkmm_thread_view -> iProp Σ) : iProp Σ :=
  [∗ map] agent ↦ body ∈ P.(program_agents),
    wp P G γ ⊤ agent (initial_thread_view body) (Φ agent).

Definition final_posts P
    (Φ : agent_id -> lkmm_thread_view -> iProp Σ) actions final : iProp Σ :=
  [∗ map] agent ↦ body ∈ P.(program_agents),
    ∃ v, ⌜lookup_lkmm_thread_view
      (LkmmExecutionPosition actions final [] final) agent = Some v⌝ ∗
      Φ agent v.
```

These are the initial WP collection and final assertions already used by
`wp_parallel_init` and `wp_parallel_run_post`.

### Closed program proof

```coq
Definition completed_program_wp P
    (Q : list lkmm_action -> lkmm_state -> Prop) : iProp Σ :=
  (∀ γ, initial_resources P γ ={⊤}=∗
    all_candidates P (fun G =>
      ∃ Φ : agent_id -> lkmm_thread_view -> iProp Σ,
        agent_wps P G γ Φ ∗
        (∀ actions final,
          ⌜lkmm_position P G
            (LkmmExecutionPosition actions final [] final)⌝ -∗
          state_interp γ final ∗ final_posts P Φ actions final
            ={⊤,∅}=∗ ⌜Q actions final⌝)))%I.
```

The quantifier order is intentional:

- The client accepts the names `γ` allocated by the adequacy proof and performs
  its initial resource setup before the candidate is supplied.
- `all_candidates` requires proofs for every consistent program graph, with
  one shared candidate for all agents. It does not select a favorable graph.
- `Φ` and the final extraction rule are established before a schedule or final
  state is supplied. The extraction rule may retain resources alongside the
  agent proofs through the separating conjunction.
- At completion, the extraction rule consumes the final state interpretation
  and agent postconditions to establish the pure `Q actions final`. Its position
  premise supplies the actual accepted run and equality of its candidate with
  `G`; it is a premise only of final extraction.
- The theorem requires a closed proof for every fresh `invGS` instance. An
  assertion that holds only under assumed invariant ownership is insufficient.

The proof allocates the initial resources, specializes the client
proof at `G := lkmm_candidate final`, applies `wp_parallel_run_post`, and
uses the final extraction rule. Iris's generic fancy-update and step-update
soundness then yield the ordinary Rocq proposition `Q actions final`.
The proof preserves one guard per operational action and handles the empty trace
separately when eliminating the final update. It adds no axioms.

The [adequacy regressions](../theories/examples/adequacy_examples.v) extract
pure results for a zero-step execution and interleaved assignments, exercise
client ghost resources retained across execution, and connect a store's
returned event fact to the final state using initialized memory ownership.

This theorem assumes completion and the final `rf`/`co` obligations. It does
not establish safety for arbitrary raw prefixes, existence of an accepted
execution, termination, or eventual grace-period completion. Prefix safety
needs its own execution domain and theorem.

## Publication example

`theories/logic/wp_publication.v` defines shared-location protocols that own
emitted write histories and restrict permitted writes. `wp_load_protocol`
and `wp_store_protocol` open and restore the invariant around an operation,
returning persistent load/store receipts. Neither rule assumes that a load
observes the most recently emitted write.

At completion, `publication_observed` combines two location protocols and
four receipts. Its value guarantee follows from the generic relational
`publication_reads` lemma. The initial flag value must differ from the
published flag value; writer and reader agents must differ, and their two
accesses must be in the stated program order. The final `rf`/`co` obligations
and consistency come from the accepted execution domain.

The client in `theories/examples/message_passing_wp.v` supplies protocol
ownership, proves both threads through instruction rules, and closes the
program proof before applying adequacy. It contains no `rf`, `co`, or cycle
proof. This is a single-writer value-publication protocol, not a general
release/acquire ownership-transfer interface.

## Remaining work

- Define and prove safety for arbitrary execution prefixes. Termination and
  grace-period liveness are outside the intended guarantee.
