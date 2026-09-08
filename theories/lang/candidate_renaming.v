From stdpp Require Import tactics.
From iris_lkmm.lkmm Require Import event_renaming graph_renaming rcu_renaming.
From iris_lkmm.lang Require Import program_graph.

(** Structural correspondence for complete candidate data, including the
    [rf] and [co] choices that do not belong to the Core execution state. *)
Module LkmmCandidateRenaming.
  Export LkmmProgramGraph EventRenaming.
  Import GraphRenaming RcuRenaming.

  (** [f] bijects the allocated event IDs, preserves event values (including
      labels, agents, and local positions), and fixes initial-write IDs.
      Every base edge set is exactly the image of its source set: target
      edges may neither be omitted nor added. Well-formedness, consistency,
      and program execution are separate properties, not record fields. *)
  Record candidate_renaming (f : event_id -> event_id) (source target : core_candidate) : Prop := {
    candidate_renaming_events :
      event_renaming f source.(candidate_events) target.(candidate_events);
    candidate_renaming_rf :
      target.(candidate_rf) = rename_edges f source.(candidate_rf);
    candidate_renaming_co :
      target.(candidate_co) = rename_edges f source.(candidate_co);
    candidate_renaming_rmw :
      target.(candidate_rmw) = rename_edges f source.(candidate_rmw);
    candidate_renaming_addr :
      target.(candidate_direct_addr) = rename_edges f source.(candidate_direct_addr);
    candidate_renaming_data :
      target.(candidate_direct_data) = rename_edges f source.(candidate_direct_data);
    candidate_renaming_ctrl :
      target.(candidate_direct_ctrl) = rename_edges f source.(candidate_direct_ctrl)
  }.

  Theorem candidate_renaming_wf f source target :
    candidate_renaming f source target ->
    core_candidate_wf source -> core_candidate_wf target.
  Proof.
    intros [Hren Hrf_eq Hco_eq Hrmw_eq Haddr_eq Hdata_eq Hctrl_eq]
      (HE & Hrf & Hco & Hrmw & Haddr & Hdata & Hctrl & Hmatching).
    unfold core_candidate_wf.
    rewrite Hrf_eq, Hco_eq, Hrmw_eq, Haddr_eq, Hdata_eq, Hctrl_eq.
    split; first by eapply event_renaming_wf.
    split; first by eapply rf_wf_rename.
    split; first by eapply co_wf_rename.
    split; first by eapply rmw_wf_rename.
    split; first by eapply direct_addr_wf_rename.
    split; first by eapply direct_data_wf_rename.
    split; first by eapply direct_ctrl_wf_rename.
    by eapply rcu_matching_complete_rename.
  Qed.

  (** Consistency is separate from candidate well-formedness. The latter
      supplies allocated endpoints and unambiguous RCU matching, so a new
      target cycle or atomicity violation would reflect to the source. *)
  Theorem candidate_renaming_consistent f source target :
    candidate_renaming f source target ->
    core_candidate_wf source -> lkmm_consistent source -> lkmm_consistent target.
  Proof.
    intros [Hren Hrf_eq Hco_eq Hrmw_eq Haddr_eq Hdata_eq Hctrl_eq]
      (HE & Hrf & Hco & Hrmw & Haddr & Hdata & Hctrl & Hmatching) Hconsistent.
    eapply (graph_consistent_rename f (core_candidate_graph source)
      (core_candidate_graph target)); try done.
    - intros x y Hxy. by eapply rf_wf_endpoints.
    - intros x y Hxy. by eapply co_wf_endpoints.
    - intros x y Hxy. by eapply rmw_wf_endpoints.
    - intros x y Hxy. apply po_endpoints. exact (proj2 (proj2 (Haddr x y Hxy))).
    - intros x y Hxy. apply po_endpoints. exact (proj2 (proj2 (Hdata x y Hxy))).
    - intros x y Hxy. apply po_endpoints. exact (proj2 (proj2 (Hctrl x y Hxy))).
  Qed.
End LkmmCandidateRenaming.
