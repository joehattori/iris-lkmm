From iris_lkmm.lkmm Require Import execution memory_relations.

(** Relation graph shared by the relational model and operational builder.

    This record contains graph data independently of program execution.
    The language layer connects candidates to Core runs via [program_graph].
    Base memory relations and direct dependency provenance are finite
    candidate data; [prop], [hb], and [pb] are derived. *)
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

  Definition graph_coherence_order (G : graph) : relation :=
    rel_union (po_loc G.(events)) (LkmmMemoryRelations.com G.(rf_edges) G.(co_edges)).

  Definition graph_atomicity_violation (G : graph) : relation :=
    rel_intersection (LkmmMemoryRelations.rmw G.(rmw_edges))
      (rel_seq
        (LkmmMemoryRelations.fre G.(events) G.(rf_edges) G.(co_edges))
        (LkmmMemoryRelations.coe G.(events) G.(co_edges))).

  Definition graph_coherence (G : graph) : Prop := rel_acyclic (graph_coherence_order G).

  Definition graph_atomicity (G : graph) : Prop :=
    rel_is_empty (graph_atomicity_violation G).

  Definition graph_happens_before (G : graph) : Prop := rel_acyclic (graph_hb G).

  Definition graph_propagation (G : graph) : Prop := rel_acyclic (graph_pb G).
End LkmmExecutionGraph.
