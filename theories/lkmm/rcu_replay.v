From iris_lkmm.lkmm Require Import rcu_matching.

(** Event-level premises for reconstructing a completed Core execution in
    the snapshot machine.  These predicates do not refer to a machine run,
    a schedule, or final LKMM consistency. *)
Module RcuReplay.
  Export RcuMatching.

  (** Program order keeps this condition local to the section's agent.
      Every matched section is checked, including enclosing sections when
      read-side critical sections are nested. *)
  Definition no_gp_in_read_section (E : event_structure) : Prop :=
    forall lock unlock gp,
      rcu_rscs E lock unlock ->
      event_has_barrier_kind E BarrierSyncRcu gp ->
      po E lock gp -> ~ po E gp unlock.

  (** This is a condition on a completed event structure: open prefixes may
      fail complete matching even when they extend to an admissible run.
      Event allocation well-formedness remains a separate Core invariant. *)
  Definition rcu_replay_wf (E : event_structure) : Prop :=
    rcu_matching_complete E /\ no_gp_in_read_section E.
End RcuReplay.
