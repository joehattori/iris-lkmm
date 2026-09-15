# Semantic architecture

The project separates the relational LKMM model, event-generating Core
language, incremental operational semantics, and Iris logic. They share
canonical events and dependency provenance, while the relational model remains
independent of Iris. The [source mapping](cat-mapping.md) records the selected
Linux v6.18 definitions and omissions.

## Core execution and candidate graphs

[LKMM-Core](../theories/lang/lkmm_core.v) is a finite, loop-free language with
fixed agents and structured control flow. Expressions carry read-event origins
alongside integer values. Register assignments and active branch scopes retain
that provenance, so dependencies are generated syntactically.

Execution emits events with fresh global IDs and per-agent positions. Reads
choose observed values nondeterministically; successful RMWs emit paired read
and write events together, while failed conditional RMWs emit only a read.
Locations come from the program's finite initial-memory map.

[Candidate graphs](../theories/lang/program_graph.v) combine the generated
events, RMW pairs, and dependencies with independent reads-from and coherence
choices. Well-formedness connects observed values to source writes; consistency
separately imposes the selected LKMM constraints. Source writes may be emitted
after their reads. This separation avoids imposing execution-order restrictions
that would exclude permitted weak-memory graphs.

## Core-driven RCU machine

The [machine](../theories/operational/lkmm_machine.v) extends Core with
normal-RCU snapshot waiting. Reader stacks and matched sections are computed
from generated events. A grace period begins by capturing the currently open
readers and finishes only after every captured reader has closed. Readers
entering later do not extend that snapshot. Nested sections are tracked by
their individual lock events.

Beginning a grace period leaves Core execution unchanged; finishing emits the
synchronization event and records a certificate. Even an empty snapshot needs
a finish step. Completion requires finished threads, no pending grace periods,
and balanced reader sections. The machine constrains the RCU protocol; memory
consistency is enforced by the graph builder.

## Constructive RCU ordering

The [graph kernel](../theories/lkmm/rcu_obligations.v) characterizes recursive
RCU ordering through finite chains of grace periods and inverse critical
sections connected by RCU links. Grace periods contribute positive balance
and inverse sections negative balance. Acceptance requires a nonnegative final
balance, so a valid chain can begin with a negative prefix.

The chain characterization is proved equivalent to the transcribed recursive
relation independently of program execution. It exposes the graph constraint's
constructive structure. Operational consistency comes from the builder's
invariant; the Iris completion protocol uses the machine's captured-reader
guarantee. These are separate proof paths.

## Incremental graph builder

The [builder](../theories/operational/rcu_builder.v) starts empty and adds events
and base edges incrementally. Program order, matching, and the derived memory
relations come from the committed graph. Stored RCU-link witnesses remain valid
as the graph grows.

Each mutation supplies the newly introduced consistency paths or violations.
Exactness checks and local cycle/emptiness checks maintain coherence,
atomicity, happens-before, propagation, and RCU consistency. Structural checks
permit incomplete relation prefixes; total reads-from and complete coherence
orders remain completion obligations.

A step refers only to the current graph, its successor, and their difference.
It receives neither a final candidate nor a final-consistency premise.
Completeness schedules the components of a finite consistent candidate and
uses monotonicity to justify each local check. The existence proof uses the
candidate, while the operational state and transitions do not preload it.

## Coupled execution

The [coupled semantics](../theories/operational/lkmm_coupled.v) interleaves
machine and builder steps. The builder may commit only events and generated
RMW/dependency edges already supplied by Core. Reads-from and coherence remain
independent builder choices. Commitments may lag behind emission, allowing RCU
events to be loaded in canonical trace order rather than global emission order.

At completion, machine and builder agree exactly on generated events and
relations. Soundness combines that agreement with the builder's consistency
invariant. The resulting graph is a well-formed, consistent program graph
under explicit completion-time reads-from and coherence obligations.

## Coupled operational completeness

Every consistent program graph admits a completed coupled execution up to
event-ID renaming. The construction separates replay from graph commitment:

1. Replay each agent's Core actions as a whole block, preserving observed
   values, local order, and dependency provenance under a common renaming.
2. Lift the replay into the RCU machine. Candidate well-formedness gives
   balanced reader sections; consistency excludes synchronization inside an
   agent's own section.
   Serialized agent blocks therefore allow each grace period to capture an
   empty snapshot.
3. Transport the candidate's relations through the renaming and commit the
   graph after machine execution. The candidate's well-formedness supplies
   the completion obligations.

[Core replay](../theories/lang/core_replay.v) changes the schedule but preserves
the candidate's meaning. [Machine lifting](../theories/operational/core_to_machine.v)
uses the existing transition rules. This is an existence construction, with no
claim that arbitrary schedules terminate or grace periods make progress.

## Iris logic

The [graph-relative WP design](wp-design.md) uses the operational semantics
without changing its transitions. A shared candidate keeps local proofs
compatible, and a state interpretation connects resources to execution
prefixes. The reader/grace-period protocol supports completion updates while
later readers remain active. Memory ownership tracks emitted write histories.
The client RCU protocol recovers protected ownership after closing admission
and completing a grace period. External adequacy and safety for arbitrary raw
prefixes remain open.
