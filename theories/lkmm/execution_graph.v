From iris_lkmm.lkmm Require Import execution memory_relations.

(** Minimal relation graph shared by the feasibility prototype.

    This record is independent of RCU, but it is not yet the final LKMM
    candidate-execution type.  Base memory relations and direct dependency
    provenance are finite candidate data; [prop], [hb], and [pb] are derived. *)
Module LkmmExecutionGraph.
  Export LkmmExecution.

  Record graph := Graph {
    events : event_structure;
    rf_edges : edge_set;
    co_edges : edge_set;
    rmw_edges : edge_set;
    direct_addr_edges : edge_set;
    direct_data_edges : edge_set;
    direct_ctrl_edges : edge_set
  }.

  Definition in_graph (G : graph) (eid : event_id) : Prop := in_event_structure G.(events) eid.

  Definition graph_po (G : graph) : relation := po G.(events).

  Definition graph_prop (G : graph) : relation :=
    LkmmMemoryRelations.prop G.(events) G.(rmw_edges) G.(rf_edges) G.(co_edges).

  Definition graph_hb (G : graph) : relation :=
    LkmmMemoryRelations.hb G.(events) G.(rmw_edges) G.(rf_edges) G.(co_edges)
      G.(direct_data_edges) G.(direct_addr_edges) G.(direct_ctrl_edges).

  Definition graph_pb (G : graph) : relation :=
    LkmmMemoryRelations.pb G.(events) G.(rmw_edges) G.(rf_edges) G.(co_edges)
      G.(direct_data_edges) G.(direct_addr_edges) G.(direct_ctrl_edges).
End LkmmExecutionGraph.
