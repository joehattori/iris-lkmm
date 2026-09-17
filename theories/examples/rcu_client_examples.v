From Stdlib Require Import List.
From iris.base_logic.lib Require Import invariants.
From iris.proofmode Require Import proofmode.
From iris_lkmm.lkmm Require Import rcu_matching.
From iris_lkmm.operational Require Import lkmm_machine lkmm_operational.
From iris_lkmm.logic Require Import graph_correspondence rcu_ghost state_interp rcu_client
  wp wp_memory wp_rcu wp_rcu_client.
Import ListNotations.

Module RcuClientExamples.
  Import LkmmMachine LkmmOperational RcuMatching LkmmGraphCorrespondence.
  Import RcuGhost LkmmStateInterp RcuClient LkmmWp LkmmWpMemory LkmmWpRcu LkmmWpRcuClient.

  Definition reader_view index actions := LkmmThreadView
    (ThreadView (ThreadState (SSeq (SLoad 0 LoadOnce (EConst 0)) SRcuReadUnlock) [] ∅)
      index actions) None.

  Definition updater_view := LkmmThreadView
    (ThreadView (initial_thread SSynchronizeRcu) 0 []) None.

  Section example.
    Context `{!invGS Σ, !stateG Σ, !clientG Σ}.

    Local Lemma reader P G γ δ N E lock unlock index actions history :
      ↑N ⊆ E ->
      lookup_event G.(candidate_events) unlock =
        Some (EAgent 0 (S index) (LBarrier BarrierRcuUnlock)) ->
      rcu_rscs G.(candidate_events) lock unlock ->
      client_inv γ.(rcu_name) δ N (memory_own γ.(memory_names_of) 0 1 history) -∗
      client_loan δ lock -∗
      wp P G γ E 0 (reader_view index actions) (fun _ => True).
    Proof.
      iIntros (HN Hunlock Hpair) "#Hinv Hloan". iApply wp_seq. iNext.
      iApply (wp_load_acc _ _ _ _ (E ∖ ↑N)); first done.
      iNext. iMod (client_access_inv with "Hinv Hloan") as "[Hloc Hclose]"; first done.
      iModIntro. iExists 1%Qp, history. iFrame "Hloc".
      iIntros (read observed source Hsource) "Hloc #Hread".
      iMod ("Hclose" with "Hloc") as "Hloan". iModIntro.
      iApply wp_skip_seq. iNext. iApply fupd_wp.
      iMod (client_return_inv with "Hinv Hloan") as "Hreader"; first done.
      iModIntro. iApply (wp_read_unlock _ _ _ _ _ _ lock unlock with "Hreader"); try done.
      iNext. iIntros "_". rewrite wp_unfold /wp_body /rcu_next_view /=. done.
    Qed.

    (** One admitted reader and one updater share the same memory history.
        Admission starts with a real lock token and immediately returns the
        publisher's control, so the updater may retire before the load. The
        reader uses the protected memory and returns its loan before unlock;
        synchronization recovers full ownership in the updater's postcondition.
        The caller establishes this cut and the graph's matching unlock. *)
    Example reader_and_updater P G γ N E lock unlock sync index actions history :
      ↑N ⊆ E ->
      lookup_event G.(candidate_events) unlock =
        Some (EAgent 0 (S index) (LBarrier BarrierRcuUnlock)) ->
      rcu_rscs G.(candidate_events) lock unlock ->
      lookup_event G.(candidate_events) sync = Some (EAgent 1 0 (LBarrier BarrierSyncRcu)) ->
      memory_own γ.(memory_names_of) 0 1 history -∗ reader_token γ.(rcu_name) lock -∗
      |={E}=> wp P G γ E 0 (reader_view index actions) (fun _ => True) ∗
        wp P G γ E 1 updater_view (fun _ => memory_own γ.(memory_names_of) 0 1 history).
    Proof.
      iIntros (HN Hunlock Hpair Hsync) "Hloc Hreader".
      iMod (client_init γ.(rcu_name) N with "Hloc") as (δ) "[#Hinv Hcontrol]".
      iMod (client_borrow_inv with "Hinv Hcontrol Hreader") as "[Hcontrol Hloan]"; first done.
      iModIntro. iSplitL "Hloan".
      { iApply (reader with "Hinv Hloan"); done. }
      iApply (wp_synchronize_reclaim _ _ _ _ _ _ _ _ sync with "Hinv Hcontrol"); try done.
      iNext. iIntros "Hloc".
      rewrite wp_unfold /wp_body /rcu_next_view /updater_view /=. by iFrame.
    Qed.
  End example.
End RcuClientExamples.
