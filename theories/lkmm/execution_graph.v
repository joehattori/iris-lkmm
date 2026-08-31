From iris_lkmm.lkmm Require Import execution.

(** Minimal relation graph shared by the feasibility prototype.

    This record is independent of RCU, but it is not yet the final LKMM
    candidate-execution type: [hb], [prop], and [pb] are supplied abstractly
    rather than derived from finite base relations. *)
Module LkmmExecutionGraph.
  Export LkmmExecution.

  Record graph := Graph {
    events : event_structure;
    hb : relation;
    prop : relation;
    pb : relation
  }.

  Definition in_graph (G : graph) (eid : event_id) : Prop :=
    in_event_structure G.(events) eid.
End LkmmExecutionGraph.
