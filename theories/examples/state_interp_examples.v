From Stdlib Require Import List Lia.
From stdpp Require Import gmap tactics.
From iris.base_logic.lib Require Import iprop.
From iris.proofmode Require Import proofmode.
From iris_lkmm.operational Require Import lkmm_machine lkmm_coupled.
From iris_lkmm.logic Require Import rcu_ghost state_interp.
From iris_lkmm.examples Require Import graph_domain_examples graph_correspondence_examples.
Import ListNotations.

Module StateInterpExamples.
  Import LkmmMachine LkmmCoupled RcuGhost LkmmStateInterp.
  Module GP := GraphCorrespondenceExamples.GpState.

  Local Lemma waiting_pending gid captured :
    pending_gp_at GP.waiting.(coupled_machine) gid captured <->
    gid = gp_identity 0 0 /\ captured = ∅.
  Proof.
    split.
    - intros (agent & locks & Hlookup & Hgid & Hcaptured).
      change (({[0 := []]} : gmap agent_id (list event_id)) !! agent = Some locks) in Hlookup.
      apply lookup_singleton_Some in Hlookup as [<- <-]. done.
    - intros [-> ->]. exists 0, []. split_and!; reflexivity.
  Qed.

  Local Lemma finished_completed gid captured :
    completed_gp_at GP.finished.(coupled_machine) gid captured <->
    gid = gp_identity 0 0 /\ captured = ∅.
  Proof.
    split.
    - intros (cert & agent & index & Hcert & Hlookup & Hgid & Hcaptured).
      change (In cert [GpCertificate 0 []]) in Hcert. destruct Hcert as [<- | []].
      change (Some (EAgent 0 0 (LBarrier BarrierSyncRcu)) =
        Some (EAgent agent index (LBarrier BarrierSyncRcu))) in Hlookup.
      simplify_eq. done.
    - intros [-> ->]. exists (GpCertificate 0 []), 0, 0.
      split; first by left. split_and!; reflexivity.
  Qed.

  Example waiting_protocol_matches :
    rcu_state_matches GP.waiting.(coupled_machine)
      {[gp_identity 0 0 := GpPending ∅ 0]}.
  Proof.
    split.
    - intros gid captured. rewrite waiting_pending. split.
      + intros [-> ->]. exists 0. apply lookup_singleton_eq.
      + intros (start & Hlookup). apply lookup_singleton_Some in Hlookup.
        naive_solver.
    - split.
      + intros gid captured. split.
        * intros (cert & agent & index & Hcert & _). inversion Hcert.
        * intros (start & finish & Hlookup). apply lookup_singleton_Some in Hlookup.
          naive_solver.
      + intros gid status Hlookup. apply lookup_singleton_Some in Hlookup as [_ <-].
        simpl. lia.
  Qed.

  Example finished_protocol_matches :
    rcu_state_matches GP.finished.(coupled_machine)
      {[gp_identity 0 0 := GpDone ∅ 0 1]}.
  Proof.
    split.
    - intros gid captured. split.
      + intros (agent & locks & Hlookup & _).
        change ((∅ : gmap agent_id (list event_id)) !! agent = Some locks) in Hlookup.
        by rewrite lookup_empty in Hlookup.
      + intros (start & Hlookup). apply lookup_singleton_Some in Hlookup. naive_solver.
    - split.
      + intros gid captured. rewrite finished_completed. split.
        * intros [-> ->]. exists 0, 1. apply lookup_singleton_eq.
        * intros (start & finish & Hlookup). apply lookup_singleton_Some in Hlookup.
          naive_solver.
      + intros gid status Hlookup. apply lookup_singleton_Some in Hlookup as [_ <-].
        simpl. lia.
  Qed.

  (** An unchanged Core state does not allow us to omit the begun GP. *)
  Example begin_requires_pending_entry :
    GP.before.(coupled_machine).(machine_core) = GP.waiting.(coupled_machine).(machine_core) /\
    ~ rcu_state_matches GP.waiting.(coupled_machine) ∅.
  Proof.
    split; first reflexivity. intros [Hpending _].
    destruct (proj1 (Hpending (gp_identity 0 0) ∅)) as (start & Hlookup).
    - apply waiting_pending. done.
    - by rewrite lookup_empty in Hlookup.
  Qed.

  (** A permitted future source does not yet supply an emitted-event fact. *)
  Example future_source_has_no_event_fact `{!stateG Σ} γ b :
    ⊢ state_interp (Σ := Σ) γ (CoupledState
      (State GraphDomainExamples.FutureSource.after_read ∅ []) b) -∗
    event_fact γ 2 (EAgent 0 0 (LMemory AccessWrite AccessOnce NotRmw 0 1%Z)) -∗ False.
  Proof.
    iIntros "Hstate Hevent".
    iDestruct (state_interp_event with "Hstate Hevent") as %Hlookup.
    discriminate Hlookup.
  Qed.
End StateInterpExamples.
