From Stdlib Require Import List Lia.
From iris.base_logic.lib Require Import invariants fancy_updates.
From iris.proofmode Require Import proofmode.
From iris_lkmm.operational Require Import lkmm_machine.
From iris_lkmm.logic Require Import wp_publication adequacy hoare.
From iris_lkmm.examples Require Import message_passing_code.
Import ListNotations.

(** Client proofs use location protocols and operation receipts for all four
    message-passing variants; both loads are unconditional. *)
Module MessagePassingWp.
  Import LkmmWpPublication LkmmAdequacy LkmmMachine LkmmHoare.
  Import MessagePassingCode.

  Definition Ndata := nroot .@ "mp-data".
  Definition Nflag := nroot .@ "mp-flag".
  Definition data_allowed := publication_write 0%Z 0 0 AccessOnce 0 1%Z.
  Definition flag_allowed sm := publication_write 0%Z 0 1 (store_access_mode sm) 1 1%Z.

  Definition producer_context sm lm G γ := WpContext (program sm lm) G γ 0.
  Definition consumer_context sm lm G γ := WpContext (program sm lm) G γ 1.

  Definition result_registers (v : lkmm_thread_view) :=
    v.(lkmm_view_core).(view_thread).(thread_registers).

  Definition mp_result (_ : list lkmm_action) (final : lkmm_state) : Prop :=
    exists reader r0 r1,
      final.(lkmm_machine).(machine_core).(core_threads) !! 1 = Some reader /\
      reader.(thread_registers) !! 0 = Some r0 /\
      reader.(thread_registers) !! 1 = Some r1 /\
      (r0.(reg_integer) = 1%Z -> r1.(reg_integer) = 1%Z).

  Lemma initial_history_accepts sm lm loc (allowed : event -> Prop) :
    allowed (EInitWrite loc 0%Z) ->
    history_accepts allowed (write_history (core_initial_events (program sm lm)) loc).
  Proof.
    intros Hallowed eid ev Hlookup.
    apply write_history_lookup in Hlookup as [Hlookup [_ Hloc]].
    change (({[1 := EInitWrite 1 0%Z; 0 := EInitWrite 0 0%Z]} : event_structure) !! eid = Some ev) in Hlookup.
    apply lookup_insert_Some in Hlookup as [[_ <-]|[_ Hlookup]].
    - cbn in Hloc. injection Hloc as <-. done.
    - apply lookup_singleton_Some in Hlookup as [_ <-].
      cbn in Hloc. injection Hloc as <-. done.
  Qed.

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

    Lemma producer_spec sm lm G γ :
      {{{ shared γ sm }}}
        producer sm @ producer_context sm lm G γ; ⊤
      {{{ v, RET v; producer_post γ sm v }}}.
    Proof.
      iIntros (Φ) "[#Hdata #Hflag] HΦ".
      iApply wp_seq. iNext.
      iApply (wp_store_protocol with "Hdata"); try reflexivity; try set_solver.
      { by right. }
      iNext. iIntros "#Hwrite_data".
      iApply wp_skip_seq. iNext.
      iApply (wp_store_protocol with "Hflag"); try reflexivity; try set_solver.
      { by right. }
      iNext. iIntros "#Hwrite_flag".
      rewrite wp_unfold /wp_body /memory_view /=.
      iModIntro. iApply "HΦ". by iFrame "Hwrite_data Hwrite_flag".
    Qed.

    Lemma consumer_spec sm lm G γ :
      {{{ shared γ sm }}}
        consumer lm @ consumer_context sm lm G γ; ⊤
      {{{ v, RET v; consumer_post G γ lm v }}}.
    Proof.
      iIntros (Φ) "[#Hdata #Hflag] HΦ".
      iApply wp_seq. iNext.
      iApply (wp_load_protocol with "Hflag"); try reflexivity; try set_solver.
      iNext. iIntros (flag_read r0) "#Hread_flag".
      iApply wp_skip_seq. iNext.
      iApply (wp_load_protocol with "Hdata"); try reflexivity; try set_solver.
      iNext. iIntros (data_read r1) "#Hread_data".
      rewrite wp_unfold /wp_body /memory_view /=.
      iModIntro. iApply "HΦ".
      iExists (RegValue r0 {[flag_read]}), (RegValue r1 {[data_read]}).
      iFrame "Hread_flag Hread_data". iPureIntro.
      rewrite lookup_insert_ne; last done. rewrite !lookup_insert_eq. done.
    Qed.

    (** The triple specifications feed the existing parallel/adequacy API. *)
    Lemma producer_wp sm lm G γ :
      shared γ sm -∗
      wp (program sm lm) G γ ⊤ 0
        (initial_thread_view (producer sm)) (producer_post γ sm).
    Proof.
      iIntros "Hshared". iApply (producer_spec with "Hshared").
      iNext. iIntros (v) "Hpost". iExact "Hpost".
    Qed.

    Lemma consumer_wp sm lm G γ :
      shared γ sm -∗
      wp (program sm lm) G γ ⊤ 1
        (initial_thread_view (consumer lm)) (consumer_post G γ lm).
    Proof.
      iIntros "Hshared". iApply (consumer_spec with "Hshared").
      iNext. iIntros (v) "Hpost". iExact "Hpost".
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

    Lemma initial_shared sm lm γ :
      initial_resources (program sm lm) γ ={⊤}=∗ shared γ sm.
    Proof.
      iIntros "[_ Hmemory]".
      iDestruct (big_sepM_delete _ _ 0 with "Hmemory") as "[Hdata Hmemory]"; first reflexivity.
      iDestruct (big_sepM_lookup _ _ 1 with "Hmemory") as "Hflag".
      { rewrite lookup_delete_ne; done. }
      iMod (location_protocol_alloc γ Ndata 0 data_allowed with "Hdata") as "#Hdata".
      { apply initial_history_accepts. by left. }
      iMod (location_protocol_alloc γ Nflag 1 (flag_allowed sm) with "Hflag") as "#Hflag".
      { apply initial_history_accepts. by left. }
      iModIntro. by iFrame "Hdata Hflag".
    Qed.

    (** Allocate the protocol from the actual initial memory, before G is
        chosen. Both WPs must work for every consistent candidate. *)
    Lemma mp_closed :
      ⊢ completed_program_wp (program StoreRelease LoadAcquire) mp_result.
    Proof.
      iIntros (γ) "Hinit".
      iMod (initial_shared with "Hinit") as "[#Hdata #Hflag]".
      iModIntro. iIntros (G HG).
      iExists (post StoreRelease LoadAcquire G γ). iSplitL.
      - iApply message_passing_wps. by iFrame "Hdata Hflag".
      - iIntros (actions final) "%Hposition [Hstate Hposts]".
        iDestruct (big_sepM_delete _ _ 0 with "Hposts") as "[Hproducer Hposts]"; first reflexivity.
        iDestruct (big_sepM_lookup _ _ 1 with "Hposts") as "Hconsumer".
        { rewrite lookup_delete_ne; done. }
        iDestruct "Hproducer" as (producer_view) "[_ [Hwrite_data Hwrite_flag]]".
        iDestruct "Hconsumer" as (consumer_view) "[%Hview Hconsumer]".
        iDestruct "Hconsumer" as (r0 r1) "(%Hregisters & Hread_flag & Hread_data)".
        iMod (publication_observed with
          "Hstate Hdata Hflag Hwrite_data Hwrite_flag Hread_flag Hread_data") as %Hresult;
          try lia; try done.
        iModIntro. iPureIntro.
        exists consumer_view.(lkmm_view_core).(view_thread), r0, r1.
        split; first exact (lookup_lkmm_thread_view_lookup _ _ _ Hview).
        destruct Hregisters as [Hr0 Hr1]. split_and!; done.
    Qed.
  End proof.

  Definition mpΣ : gFunctors := #[invΣ; stateΣ].

  (** The public guarantee concerns actual final registers, and is obtained
      through Iris adequacy. No direct forbidden-outcome theorem is used. *)
  Theorem mp_release_acquire_adequate actions final :
    lkmm_run (program StoreRelease LoadAcquire)
      (initial_lkmm (program StoreRelease LoadAcquire)) actions final ->
    lkmm_complete final -> lkmm_program_graph_obligations final ->
    mp_result actions final.
  Proof.
    apply (wp_adequacy (Σ := mpΣ)). intros Hinv. apply mp_closed.
  Qed.

End MessagePassingWp.
