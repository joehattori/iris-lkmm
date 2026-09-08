From Stdlib Require Import Lia.
From stdpp Require Import gmap tactics.
From iris_lkmm.lang Require Import program_graph candidate_renaming.

Module CandidateRenamingExamples.
  Import LkmmCandidateRenaming.
  Module Sample := LkmmProgramGraph.ProgramGraphTests.

  (** Exchange the writer and reader IDs while fixing the initial write.
      Their agents, positions, labels, and observed values stay unchanged. *)
  Definition swap_id (eid : event_id) : event_id :=
    match eid with 1 => 2 | 2 => 1 | _ => eid end.

  Definition swapped_events : event_structure :=
    {[0 := Sample.init_write; 2 := Sample.write; 1 := Sample.read]}.

  Local Lemma swap_involutive eid : swap_id (swap_id eid) = eid.
  Proof. destruct eid as [|[|[|eid]]]; done. Qed.

  Local Lemma swapped_lookup eid :
    lookup_event swapped_events (swap_id eid) =
    lookup_event Sample.sample_events eid.
  Proof.
    destruct eid as [|[|[|eid]]]; try reflexivity.
    unfold swap_id, lookup_event, swapped_events, Sample.sample_events.
    transitivity (None : option event); [|symmetry];
      repeat (apply lookup_insert_None; split; last lia);
      apply lookup_empty.
  Qed.

  Local Lemma swapped_events_renaming :
    event_renaming swap_id Sample.sample_events swapped_events.
  Proof.
    constructor.
    - intros x y ex ey Hx Hy Heq.
      apply (f_equal swap_id) in Heq. by rewrite !swap_involutive in Heq.
    - intros x ev Hlookup. by rewrite swapped_lookup.
    - intros y ev Hlookup. exists (swap_id y). split; last apply swap_involutive.
      by rewrite <- swapped_lookup, swap_involutive.
    - intros x loc val Hlookup. destruct x as [|[|[|x]]];
        try reflexivity; discriminate.
  Qed.

  Example candidate_swap_wf_and_consistency :
    let swapped := CoreCandidate swapped_events {[(2, 1)]} {[(0, 2)]} ∅ ∅ ∅ ∅ in
    core_candidate_wf swapped /\
    (lkmm_consistent Sample.candidate -> lkmm_consistent swapped).
  Proof.
    intros swapped.
    assert (candidate_renaming swap_id Sample.candidate swapped) as Hrename.
    { constructor; first apply swapped_events_renaming.
      all: vm_compute; reflexivity. }
    pose proof (program_graph_wf _ _ Sample.two_agent_program_graph) as Hwf.
    split.
    - by eapply candidate_renaming_wf.
    - by eapply candidate_renaming_consistent.
  Qed.
End CandidateRenamingExamples.
