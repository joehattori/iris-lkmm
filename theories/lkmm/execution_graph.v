From iris_lkmm.lkmm Require Import execution.

(** Minimal relation graph shared by the feasibility prototype.

    This record is independent of RCU, but it is not yet the final LKMM
    candidate-execution type.  [rf_edges], [co_edges], and [rmw_edges] are
    finite candidate choices; [hb], [prop], and [pb] remain supplied
    abstractly rather than derived from all required finite base relations. *)
Module LkmmExecutionGraph.
  Export LkmmExecution.

  Record graph := Graph {
    events : event_structure;
    rf_edges : edge_set;
    co_edges : edge_set;
    rmw_edges : edge_set;
    hb : relation;
    prop : relation;
    pb : relation
  }.

  Definition in_graph (G : graph) (eid : event_id) : Prop := in_event_structure G.(events) eid.

  Definition graph_po (G : graph) : relation := po G.(events).
End LkmmExecutionGraph.
