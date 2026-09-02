From iris_lkmm.lkmm Require Import execution memory_relations.

(** Minimal relation graph shared by the feasibility prototype.

    This record is independent of RCU, but it is not yet the final LKMM
    candidate-execution type.  [rf_edges], [co_edges], and [rmw_edges] are
    finite candidate choices.  [prop] is derived from them; [hb] and [pb]
    remain supplied abstractly until the graph carries dependency edges. *)
Module LkmmExecutionGraph.
  Export LkmmExecution.

  Record graph := Graph {
    events : event_structure;
    rf_edges : edge_set;
    co_edges : edge_set;
    rmw_edges : edge_set;
    hb : relation;
    pb : relation
  }.

  Definition in_graph (G : graph) (eid : event_id) : Prop := in_event_structure G.(events) eid.

  Definition graph_po (G : graph) : relation := po G.(events).

  Definition graph_prop (G : graph) : relation :=
    LkmmMemoryRelations.prop G.(events) G.(rmw_edges) G.(rf_edges) G.(co_edges).
End LkmmExecutionGraph.
