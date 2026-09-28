From Stdlib Require Import List.
From iris.base_logic.lib Require Import invariants fancy_updates.
From iris.proofmode Require Import proofmode.
From iris_lkmm.lkmm Require Import publication.
From iris_lkmm.operational Require Import lkmm_machine.
From iris_lkmm.logic Require Import wp_memory wp_parallel.
Import ListNotations.

(** Shared-location protocols and receipts for publication. The invariant
    constrains emitted writes; it never equates a load with a latest value.
    All graph reasoning is confined to the interpretation of receipts. *)
Module LkmmWpPublication.
  Export LkmmWpMemory LkmmWpParallel LkmmPublication.
  Import LkmmMachine.

  Definition history_accepts (allowed : event -> Prop) (history : event_structure) : Prop :=
    forall eid ev, history !! eid = Some ev -> allowed ev.

  Section rules.
    Context `{!invGS Σ, !stateG Σ}.

    Definition location_protocol γ N loc allowed : iProp Σ :=
      inv N (∃ history, ⌜history_accepts allowed history⌝ ∗
        memory_own γ.(memory_names_of) loc 1 history).

    Definition store_receipt γ agent index mode loc val : iProp Σ :=
      ∃ eid, event_fact γ eid
        (EAgent agent index (LMemory AccessWrite (store_access_mode mode) NotRmw loc val)).

    Definition load_receipt G γ agent index mode loc val : iProp Σ :=
      ∃ eid source, event_fact γ eid
        (EAgent agent index (LMemory AccessRead (load_access_mode mode) NotRmw loc val)) ∗
        ⌜read_from G eid source loc val⌝.

    Global Instance store_receipt_persistent γ agent index mode loc val :
      Persistent (store_receipt γ agent index mode loc val).
    Proof. apply _. Qed.
    Global Instance load_receipt_persistent G γ agent index mode loc val :
      Persistent (load_receipt G γ agent index mode loc val).
    Proof. apply _. Qed.
    Global Instance location_protocol_persistent γ N loc allowed :
      Persistent (location_protocol γ N loc allowed).
    Proof. apply _. Qed.

    Lemma location_protocol_alloc γ N loc allowed history :
      history_accepts allowed history ->
      memory_own γ.(memory_names_of) loc 1 history ={⊤}=∗
      location_protocol γ N loc allowed.
    Proof.
      iIntros (Hhistory) "Hloc". iApply (inv_alloc N with "[Hloc]").
      iNext. iExists history. by iFrame.
    Qed.

    Lemma wp_store_protocol P G γ E N agent mode address expression loc
        address_sources result ks regs index actions allowed Φ :
      ↑N ⊆ E ->
      eval_location regs address = Some (loc, address_sources) ->
      eval_expr regs expression = Some result ->
      allowed (EAgent agent index
        (LMemory AccessWrite (store_access_mode mode) NotRmw loc result.(reg_integer))) ->
      location_protocol γ N loc allowed -∗
      (▷ (store_receipt γ agent index mode loc result.(reg_integer) -∗
        wp P G γ E agent (memory_view (ThreadState SSkip ks regs)
          (S index) (actions ++ [CoreEmit agent])) Φ)) -∗
      wp P G γ E agent
        (memory_view (ThreadState (SStore mode address expression) ks regs) index actions) Φ.
    Proof.
      iIntros (Hmask Haddr Hexpr Hallowed) "#Hinv Hwp".
      iApply (wp_store_acc _ _ _ _ (E ∖ ↑N)); try done.
      iNext. iInv N as (history) ">[%Hhistory Hloc]" "Hclose".
      iModIntro. iExists history. iFrame "Hloc".
      iIntros (write) "Hloc #Hwrite".
      iMod ("Hclose" with "[Hloc]") as "_".
      { iNext. iExists _. iFrame "Hloc". iPureIntro.
        intros eid ev Hlookup. apply lookup_insert_Some in Hlookup as [[Heid Hev]|[_ Hlookup]].
        - subst eid. inversion Hev. subst ev. exact Hallowed.
        - by eapply Hhistory. }
      iModIntro. iApply "Hwp". iExists write. iExact "Hwrite".
    Qed.

    Lemma wp_load_protocol P G γ E N agent dst mode address loc address_sources
        ks regs index actions allowed Φ :
      ↑N ⊆ E ->
      eval_location regs address = Some (loc, address_sources) ->
      location_protocol γ N loc allowed -∗
      (▷ ∀ read observed,
        load_receipt G γ agent index mode loc observed -∗
        wp P G γ E agent
          (memory_view (ThreadState SSkip ks (<[dst := RegValue observed {[read]}]> regs))
            (S index) (actions ++ [CoreObserve agent observed])) Φ) -∗
      wp P G γ E agent
        (memory_view (ThreadState (SLoad dst mode address) ks regs) index actions) Φ.
    Proof.
      iIntros (Hmask Haddr) "#Hinv Hwp".
      iApply (wp_load_acc _ _ _ _ (E ∖ ↑N)); first done.
      iNext. iInv N as (history) ">[%Hhistory Hloc]" "Hclose".
      iModIntro. iExists 1%Qp, history. iFrame "Hloc".
      iIntros (read observed source) "%Hsource Hloc #Hread".
      iMod ("Hclose" with "[Hloc]") as "_".
      { iNext. iExists history. by iFrame. }
      iModIntro. iApply ("Hwp" $! read observed).
      iExists read, source. iFrame "Hread". done.
    Qed.

    Lemma location_protocol_writes γ E N loc allowed final :
      ↑N ⊆ E ->
      state_interp γ final -∗ location_protocol γ N loc allowed ={E}=∗
      state_interp γ final ∗
      ⌜writes_satisfy final.(lkmm_machine).(machine_core).(core_events) loc allowed⌝.
    Proof.
      iIntros (Hmask) "Hstate #Hinv".
      iInv N as (history) ">[%Hallowed Hloc]" "Hclose".
      iDestruct (state_interp_memory with "Hstate Hloc") as %Hhistory.
      iMod ("Hclose" with "[Hloc]") as "_".
      { iNext. iExists history. by iFrame. }
      iModIntro. iFrame "Hstate". iPureIntro.
      intros eid ev Hev Hwrite Hloc. eapply Hallowed.
      rewrite Hhistory. apply write_history_lookup. done.
    Qed.

    (** Interpret four operation receipts at completion. The client supplies
        ownership protocols, not a whole-program enumeration of writes.
        Namespaces are opened sequentially; no disjointness premise is needed. *)
    Lemma publication_observed P G γ Ndata Nflag actions final
        writer reader wi wj ri rj data flag data0 flag0 published flag_value
        observed_flag observed_data :
      writer <> reader -> wi < wj -> ri < rj -> flag0 <> flag_value ->
      lkmm_position P G (LkmmExecutionPosition actions final [] final) ->
      state_interp γ final -∗
      location_protocol γ Ndata data
        (publication_write data0 writer wi AccessOnce data published) -∗
      location_protocol γ Nflag flag
        (publication_write flag0 writer wj AccessRelease flag flag_value) -∗
      store_receipt γ writer wi StoreOnce data published -∗
      store_receipt γ writer wj StoreRelease flag flag_value -∗
      load_receipt G γ reader ri LoadAcquire flag observed_flag -∗
      load_receipt G γ reader rj LoadOnce data observed_data
      ={⊤,∅}=∗ ⌜observed_flag = flag_value -> observed_data = published⌝.
    Proof.
      iIntros (Hthreads Hwi Hri Hflag Hpos) "Hstate #Hdata #Hflag Hwa Hwb Hrc Hrd".
      iMod (location_protocol_writes with "Hstate Hdata") as "[Hstate %Hdatawrites]"; first set_solver.
      iMod (location_protocol_writes with "Hstate Hflag") as "[Hstate %Hflagwrites]"; first set_solver.
      iDestruct "Hwa" as (a) "Ha". iDestruct "Hwb" as (b) "Hb".
      iDestruct "Hrc" as (c sourcec) "[Hc _]".
      iDestruct "Hrd" as (d sourced) "[Hd _]".
      iDestruct (state_interp_event with "Hstate Ha") as %Ha.
      iDestruct (state_interp_event with "Hstate Hb") as %Hb.
      iDestruct (state_interp_event with "Hstate Hc") as %Hc.
      iDestruct (state_interp_event with "Hstate Hd") as %Hd.
      iApply fupd_mask_intro_discard; first set_solver. iPureIntro.
      destruct (lkmm_position_consistent_program_graph _ _ _ Hpos) as [Hgraph Hconsistent].
      destruct Hpos as (_ & _ & Hcomplete & _ & Heq).
      pose proof (lkmm_complete_generated_matches _ Hcomplete) as [Hevents _].
      rewrite Heq in Hevents.
      rewrite Hevents in Ha, Hb, Hc, Hd, Hdatawrites, Hflagwrites.
      destruct (program_graph_wf _ _ Hgraph) as (HE & HRF & HCO & _).
      destruct Hconsistent as (_ & _ & Hhb & _).
      eapply (publication_reads G.(candidate_events) G.(candidate_rmw)
        G.(candidate_rf) G.(candidate_co) G.(candidate_direct_data)
        G.(candidate_direct_addr) G.(candidate_direct_ctrl)
        writer reader wi wj ri rj data flag data0 flag0 published flag_value
        a b c d observed_flag observed_data); eassumption.
    Qed.
  End rules.
End LkmmWpPublication.
