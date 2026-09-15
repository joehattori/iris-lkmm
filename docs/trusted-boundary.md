# Trusted boundary

The project trusts the manual transcription of the selected Linux v6.18
CAT/Bell definitions and the mapping from Linux operations to LKMM-Core.
[The source mapping](cat-mapping.md) records that correspondence. Differential
testing and independent review remain outstanding; there is no verified CAT
interpreter or source-to-Core refinement.

The finite candidate completeness construction uses propositional excluded
middle to partition successor relations into old and new pairs. Coupled
completeness and reverse graph coverage inherit that dependency. Builder and
coupled soundness, Core replay, renaming, and machine lifting add no axioms.
The relational model is independent of Iris.

Coupled soundness requires explicit completion-time reads-from and coherence
well-formedness obligations. These are premises about candidate choices;
generated RMW and dependency well-formedness follow from execution. The
obligations are not new axioms or operational transition guards.

The [Iris logic](wp-design.md) derives its resource updates and WP rules from
the existing semantics without additional axioms. Initial resources are
allocated from the program, and operational facts justify updates only when
the required ghost ownership is available. Knowing that an event occurs in a
candidate does not grant memory ownership.

The current WP domain has complete execution witnesses and final reads-from
and coherence obligations. Its parallel-execution result remains guarded
inside Iris, as does the client RCU rule for recovering protected ownership.
Clients must separately justify publication and admission to the protected
resource. External adequacy and safety for arbitrary raw prefixes remain
unproved. No Linux C correspondence, termination, or grace-period liveness
claim is made.
