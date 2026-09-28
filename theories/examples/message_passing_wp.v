From Stdlib Require Import List Lia.
From iris.base_logic.lib Require Import invariants fancy_updates.
From iris.proofmode Require Import proofmode.
From iris_lkmm.operational Require Import lkmm_machine.
From iris_lkmm.logic Require Import wp_publication adequacy.
From iris_lkmm.examples Require Import message_passing_program.
Import ListNotations.

(** Client proofs use location protocols and operation receipts for all four
    message-passing variants; both loads are unconditional. *)
Module MessagePassingWp.
  Import LkmmWpPublication LkmmAdequacy LkmmMachine.
  Import MessagePassingProgram.

  Definition Ndata := nroot .@ "mp-data".
  Definition Nflag := nroot .@ "mp-flag".
  Definition data_allowed := publication_write 0%Z 0 0 AccessOnce 0 1%Z.
  Definition flag_allowed sm := publication_write 0%Z 0 1 (store_access_mode sm) 1 1%Z.

  Definition result_registers (v : lkmm_thread_view) :=
    v.(lkmm_view_core).(view_thread).(thread_registers).

  Section proof.
    Context `{!invGS Σ, !stateG Σ}.

    Definition shared γ sm : iProp Σ :=
      location_protocol γ Ndata 0 data_allowed ∗
      location_protocol γ Nflag 1 (flag_allowed sm).

    Definition producer_post γ sm (_ : lkmm_thread_view) : iProp Σ :=
      store_receipt γ 0 0 StoreOnce 0 1%Z ∗
      store_receipt γ 0 1 sm 1 1%Z.

    Definition consumer_post G γ lm (v : lkmm_thread_view) : iProp Σ :=
      ∃ r0 r1,
        ⌜result_registers v !! 0 = Some r0 /\
          result_registers v !! 1 = Some r1⌝ ∗
        load_receipt G γ 1 0 lm 1 r0.(reg_integer) ∗
        load_receipt G γ 1 1 LoadOnce 0 r1.(reg_integer).

    Lemma producer_wp sm lm G γ :
      shared γ sm -∗
      wp (program sm lm) G γ ⊤ 0
        (initial_thread_view (producer sm)) (producer_post γ sm).
    Proof.
      iIntros "[#Hdata #Hflag]".
      iApply wp_seq. iNext.
      iApply (wp_store_protocol with "Hdata"); try reflexivity; try set_solver.
      { by right. }
      iNext. iIntros "#Hwrite_data".
      iApply wp_skip_seq. iNext.
      iApply (wp_store_protocol with "Hflag"); try reflexivity; try set_solver.
      { by right. }
      iNext. iIntros "#Hwrite_flag".
      rewrite wp_unfold /wp_body /memory_view /producer_post /=.
      iModIntro. by iFrame "Hwrite_data Hwrite_flag".
    Qed.

    Lemma consumer_wp sm lm G γ :
      shared γ sm -∗
      wp (program sm lm) G γ ⊤ 1
        (initial_thread_view (consumer lm)) (consumer_post G γ lm).
    Proof.
      iIntros "[#Hdata #Hflag]".
      iApply wp_seq. iNext.
      iApply (wp_load_protocol with "Hflag"); try reflexivity; try set_solver.
      iNext. iIntros (flag_read r0) "#Hread_flag".
      iApply wp_skip_seq. iNext.
      iApply (wp_load_protocol with "Hdata"); try reflexivity; try set_solver.
      iNext. iIntros (data_read r1) "#Hread_data".
      rewrite wp_unfold /wp_body /memory_view /consumer_post /result_registers /=.
      iModIntro. iExists (RegValue r0 {[flag_read]}), (RegValue r1 {[data_read]}).
      iFrame "Hread_flag Hread_data". iPureIntro.
      rewrite lookup_insert_ne; last done. rewrite !lookup_insert_eq. done.
    Qed.

    Definition post sm lm G γ agent :=
      if decide (agent = 0) then producer_post γ sm else consumer_post G γ lm.

    Lemma message_passing_wps sm lm G γ :
      shared γ sm -∗ agent_wps (program sm lm) G γ (post sm lm G γ).
    Proof.
      iIntros "#Hshared". iApply big_sepM_insert; first reflexivity. iSplitL.
      - iApply producer_wp. iExact "Hshared".
      - iApply big_sepM_singleton. iApply consumer_wp. iExact "Hshared".
    Qed.
  End proof.
End MessagePassingWp.
