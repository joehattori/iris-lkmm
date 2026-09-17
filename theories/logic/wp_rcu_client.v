From iris.base_logic.lib Require Import invariants.
From iris.proofmode Require Import proofmode.
From iris_lkmm.operational Require Import lkmm_machine lkmm_operational.
From iris_lkmm.logic Require Import graph_correspondence rcu_ghost state_interp rcu_client wp wp_rcu.

Module LkmmWpRcuClient.
  Import LkmmMachine LkmmOperational LkmmGraphCorrespondence.
  Import RcuGhost LkmmStateInterp RcuClient LkmmWp LkmmWpRcu.

  Section rules.
    Context `{!invGS Σ, !stateG Σ, !clientG Σ}.

    Definition client_inv γ δ N R : iProp Σ := inv N (∃ phase, client_pool γ δ phase R).

    Global Instance client_inv_persistent γ δ N R : Persistent (client_inv γ δ N R).
    Proof. apply _. Qed.

    Lemma client_init γ N E R :
      R ={E}=∗ ∃ δ, client_inv γ δ N R ∗ client_control δ ClientLive.
    Proof.
      iIntros "HR". iMod (client_publish γ with "HR") as (δ) "[Hcontrol Hpool]".
      iMod (inv_alloc N _ (∃ phase, client_pool γ δ phase R) with "[Hpool]") as "#Hinv".
      { iNext. by iExists ClientLive. }
      iModIntro. iExists δ. by iFrame.
    Qed.

    (** The publisher's control token authorizes admission. A client must
        justify handing it to a reader; an observed pointer value is not such
        permission. The token is returned immediately, independently of the
        loan's lifetime, so retirement can overlap existing readers. *)
    Lemma client_borrow_inv γ δ N E rid R `{!Timeless R} :
      ↑N ⊆ E ->
      client_inv γ δ N R -∗ client_control δ ClientLive -∗
      reader_token γ rid ={E}=∗ client_control δ ClientLive ∗ client_loan δ rid.
    Proof.
      iIntros (HN) "#Hinv Hcontrol Hreader".
      iInv N as (phase) ">Hpool" "Hclose".
      iDestruct (client_pool_phase with "Hcontrol Hpool") as %<-.
      iMod (client_borrow with "Hpool Hreader") as "[Hpool Hloan]".
      iMod ("Hclose" with "[Hpool]") as "_"; first (iNext; by iExists ClientLive).
      by iFrame.
    Qed.

    Lemma client_return_inv γ δ N E rid R `{!Timeless R} :
      ↑N ⊆ E ->
      client_inv γ δ N R -∗ client_loan δ rid ={E}=∗ reader_token γ rid.
    Proof.
      iIntros (HN) "#Hinv Hloan". iInv N as (phase) ">Hpool" "Hclose".
      iMod (client_return with "Hpool Hloan") as "[Hpool Hreader]".
      iMod ("Hclose" with "[Hpool]") as "_"; first (iNext; by iExists phase).
      done.
    Qed.

    Lemma client_access_inv γ δ N E rid R `{!Timeless R} :
      ↑N ⊆ E ->
      client_inv γ δ N R -∗ client_loan δ rid -∗
      |={E,E∖↑N}=> R ∗ (R ={E∖↑N,E}=∗ client_loan δ rid).
    Proof.
      iIntros (HN) "#Hinv Hloan". iInv N as (phase) ">Hpool" "Hclose".
      iDestruct (client_access with "Hpool Hloan") as "(HR & Hrestore & Hloan)".
      iModIntro. iFrame "HR". iIntros "HR".
      iDestruct ("Hrestore" with "HR") as "Hpool".
      iMod ("Hclose" with "[Hpool]") as "_"; first (iNext; by iExists phase).
      done.
    Qed.

    Lemma client_retire_inv γ δ N E R `{!Timeless R} :
      ↑N ⊆ E ->
      client_inv γ δ N R -∗ client_control δ ClientLive ={E}=∗
        client_control δ ClientRetired.
    Proof.
      iIntros (HN) "#Hinv Hcontrol". iInv N as (phase) ">Hpool" "Hclose".
      iDestruct (client_pool_phase with "Hcontrol Hpool") as %<-.
      iMod (client_retire with "Hcontrol Hpool") as "[Hcontrol Hpool]".
      iMod ("Hclose" with "[Hpool]") as "_"; first (iNext; by iExists ClientRetired).
      done.
    Qed.

    (** Retirement precedes GP begin. The invariant is opened at begin to
        cover all loans and at finish to recover the protected resource. The
        updater carries only control between these steps; readers can still
        access the invariant and return their loans while the GP waits. *)
    Lemma wp_synchronize_reclaim P G γ δ N E agent v sync R Φ `{!Timeless R} :
      ↑N ⊆ E ->
      v.(lkmm_view_core).(view_thread).(thread_statement) = SSynchronizeRcu ->
      v.(lkmm_view_pending_gp) = None ->
      lookup_event G.(candidate_events) sync =
        Some (EAgent agent v.(lkmm_view_core).(view_event_index) (LBarrier BarrierSyncRcu)) ->
      client_inv γ.(rcu_name) δ N R -∗ client_control δ ClientLive -∗
      (▷ (R -∗ wp P G γ E agent (rcu_next_view agent v) Φ)) -∗
      wp P G γ E agent v Φ.
    Proof.
      iIntros (HN Hstmt Hpending Hevent) "#Hinv Hcontrol Hwp".
      iApply fupd_wp. iMod (client_retire_inv with "Hinv Hcontrol") as "Hcontrol"; first done.
      iModIntro. iApply wp_begin_gp_acc; try done.
      iNext. iIntros (s locks start Hlocks) "Hstate Hpending".
      iInv N as (phase) ">Hpool" "Hclose".
      iDestruct (client_pool_phase with "Hcontrol Hpool") as %<-.
      iMod (client_wait with "Hcontrol Hstate Hpool") as "(Hstate & Hcontrol & Hpool)".
      rewrite Hlocks.
      iMod ("Hclose" with "[Hpool]") as "_";
        first (iNext; by iExists (ClientWaiting (list_to_set locks))).
      iModIntro. iFrame "Hstate".
      iApply (wp_finish_gp_acc P G γ E agent (gp_wait_view v locks)
        locks start sync with "Hpending"); try done.
      iNext. iIntros (actions next finish Hrun) "Hstate #Hsync #Hdone".
      iInv N as (phase) ">Hpool" "Hclose".
      iDestruct (client_pool_phase with "Hcontrol Hpool") as %<-.
      iMod (client_reclaim _ _ _ _ _ _ _ _ _ _ Hrun
        with "Hcontrol Hstate Hdone Hpool") as "(Hstate & Hcontrol & Hpool & HR)".
      iMod ("Hclose" with "[Hpool]") as "_"; first (iNext; by iExists ClientReclaimed).
      iModIntro. iFrame "Hstate". iApply ("Hwp" with "HR").
    Qed.
  End rules.
End LkmmWpRcuClient.
