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
Their Iris context is `{!invGS Σ, !stateG Σ}`.

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
