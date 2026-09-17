From iris.base_logic.lib Require Import ghost_map ghost_var.
From iris.proofmode Require Import proofmode.
From iris_lkmm.operational Require Import lkmm_machine lkmm_operational.
From iris_lkmm.logic Require Import rcu_ghost lkmm_machine_ghost state_interp.

Module RcuClient.
  Import LkmmMachine LkmmOperational.
  Import RcuGhost LkmmMachineGhost LkmmStateInterp.
  Local Existing Instance rcu_open_G.

  Inductive client_phase :=
  | ClientLive
  | ClientRetired
  | ClientWaiting (snapshot : gset rscs_id)
  | ClientReclaimed.

  Global Instance client_phase_inhabited : Inhabited client_phase := populate ClientLive.

  Definition clientΣ := ghost_varΣ client_phase.
  Class clientG Σ := ClientG { #[local] client_phase_G :: ghost_varG Σ client_phase }.
  Global Instance subG_clientΣ Σ : subG clientΣ Σ -> clientG Σ.
  Proof. solve_inG. Qed.

  Record client_names := ClientNames { client_map_name : gname; client_phase_name : gname }.

  Section protocol.
    Context `{!stateG Σ, !clientG Σ}.

    (** The client places this pool in its publication invariant. Admission
        requires opening the live pool; neither an RCU lock nor a pointer read
        alone establishes that condition. Retirement closes admission.

        A loan escrows the reader's exclusive unlock token. The protected
        resource is accessible while the pool is open and must be restored
        before closing it. This supports memory-rule accessors without lending
        resources indefinitely across program steps. *)
    Definition client_payload phase (loans : gmap rscs_id unit) (R : iProp Σ) :=
      match phase with
      | ClientLive | ClientRetired => R
      | ClientWaiting snapshot => ⌜dom loans ⊆ snapshot⌝ ∗ R
      | ClientReclaimed => ⌜loans = ∅⌝
      end%I.

    Definition client_pool γ δ phase (R : iProp Σ) : iProp Σ :=
      ∃ loans : gmap rscs_id unit,
        ghost_var δ.(client_phase_name) (1/2) phase ∗
        ghost_map_auth δ.(client_map_name) 1 loans ∗
        ([∗ map] rid ↦ _ ∈ loans, reader_token γ rid) ∗
        client_payload phase loans R.

    Definition client_loan δ rid : iProp Σ := rid ↪[δ.(client_map_name)] tt.

    Definition client_control δ (phase : client_phase) : iProp Σ :=
      ghost_var δ.(client_phase_name) (1/2) phase.

    Global Instance client_pool_timeless γ δ phase R `{!Timeless R} :
      Timeless (client_pool γ δ phase R).
    Proof. rewrite /client_pool /client_payload. destruct phase; apply _. Qed.

    Lemma client_pool_phase γ δ phase phase' R :
      client_control δ phase -∗ client_pool γ δ phase' R -∗ ⌜phase = phase'⌝.
    Proof.
      iIntros "Hcontrol Hpool". iDestruct "Hpool" as (loans) "(Hphase & _)".
      iApply (ghost_var_agree with "Hcontrol Hphase").
    Qed.

    Global Instance client_loan_timeless δ rid : Timeless (client_loan δ rid).
    Proof. apply _. Qed.

    Lemma client_publish γ R :
      R ==∗ ∃ δ, client_control δ ClientLive ∗ client_pool γ δ ClientLive R.
    Proof.
      iIntros "HR". iMod (ghost_map_alloc_empty (K:=rscs_id) (V:=unit))
        as (δmap) "Hauth".
      iMod (ghost_var_alloc ClientLive) as (δphase) "[Hcontrol Hphase]".
      iModIntro. iExists (ClientNames δmap δphase). iFrame "Hcontrol".
      iExists ∅. by iFrame.
    Qed.

    Lemma client_borrow γ δ rid R :
      client_pool γ δ ClientLive R -∗ reader_token γ rid ==∗
        client_pool γ δ ClientLive R ∗ client_loan δ rid.
    Proof.
      iIntros "Hpool Hreader".
      iDestruct "Hpool" as (loans) "(Hphase & Hauth & Hreaders & HR)".
      iAssert (⌜loans !! rid = None⌝)%I as %Hfresh.
      { destruct (loans !! rid) as [[]|] eqn:Hlookup; try done.
        iDestruct (big_sepM_lookup with "Hreaders") as "Hother"; first done.
        iDestruct (ghost_map_elem_valid_2 with "Hreader Hother") as %[Hvalid _].
        done. }
      iMod (ghost_map_insert rid tt with "Hauth") as "[Hauth Hloan]"; first done.
      iModIntro. iFrame "Hloan". iExists (<[rid := tt]> loans).
      rewrite big_sepM_insert // /client_payload. by iFrame.
    Qed.

    Lemma client_access γ δ phase rid R :
      client_pool γ δ phase R -∗ client_loan δ rid -∗
        R ∗ (R -∗ client_pool γ δ phase R) ∗ client_loan δ rid.
    Proof.
      iIntros "Hpool Hloan".
      iDestruct "Hpool" as (loans) "(Hphase & Hauth & Hreaders & HR)".
      iDestruct (ghost_map_lookup with "Hauth Hloan") as %Hlookup.
      destruct phase; simpl.
      - iFrame "HR Hloan". iIntros "HR". iExists loans. by iFrame.
      - iFrame "HR Hloan". iIntros "HR". iExists loans. by iFrame.
      - iDestruct "HR" as "[%Hcovered HR]". iFrame "HR Hloan".
        iIntros "HR". iExists loans. by iFrame.
      - iDestruct "HR" as %->. done.
    Qed.

    Lemma client_loan_blocks_unlock γ δ phase rid R :
      client_pool γ δ phase R -∗ client_loan δ rid -∗ reader_token γ rid -∗ False.
    Proof.
      iIntros "Hpool Hloan Hreader".
      iDestruct "Hpool" as (loans) "(_ & Hauth & Hreaders & _)".
      iDestruct (ghost_map_lookup with "Hauth Hloan") as %Hlookup.
      iDestruct (big_sepM_lookup with "Hreaders") as "Hother"; first done.
      iDestruct (ghost_map_elem_valid_2 with "Hreader Hother") as %[Hvalid _]. done.
    Qed.

    Lemma client_return γ δ phase rid R :
      client_pool γ δ phase R -∗ client_loan δ rid ==∗
        client_pool γ δ phase R ∗ reader_token γ rid.
    Proof.
      iIntros "Hpool Hloan".
      iDestruct "Hpool" as (loans) "(Hphase & Hauth & Hreaders & HR)".
      iDestruct (ghost_map_lookup with "Hauth Hloan") as %Hlookup.
      iDestruct (big_sepM_delete with "Hreaders") as "[Hreader Hreaders]"; first done.
      iMod (ghost_map_delete with "Hauth Hloan") as "Hauth".
      iModIntro. iFrame "Hreader". iExists (delete rid loans). iFrame.
      destruct phase; simpl; try done.
      - iDestruct "HR" as "[%Hcovered HR]". iFrame. iPureIntro.
        rewrite dom_delete_L. set_solver.
      - iDestruct "HR" as %->. by rewrite delete_empty.
    Qed.

    Lemma client_retire γ δ R :
      client_control δ ClientLive -∗ client_pool γ δ ClientLive R ==∗
        client_control δ ClientRetired ∗ client_pool γ δ ClientRetired R.
    Proof.
      iIntros "Hcontrol Hpool".
      iDestruct "Hpool" as (loans) "(Hphase & Hauth & Hreaders & HR)".
      iMod (ghost_var_update_halves ClientRetired with "Hcontrol Hphase")
        as "[Hcontrol Hphase]".
      iModIntro. iFrame "Hcontrol". iExists loans. by iFrame.
    Qed.

    (** Seal the loans at GP begin. Subsequent returns only shrink their
        domain; there is no admission rule for a retired or waiting pool. *)
    Lemma client_wait γ δ s R :
      client_control δ ClientRetired -∗
      state_interp γ s -∗ client_pool γ.(rcu_name) δ ClientRetired R -∗
      |==> let phase := ClientWaiting (list_to_set (all_open_readers s.(lkmm_machine))) in
        state_interp γ s ∗ client_control δ phase ∗ client_pool γ.(rcu_name) δ phase R.
    Proof.
      iIntros "Hcontrol Hstate Hpool".
      iDestruct "Hpool" as (loans) "(Hphase & Hauth & Hreaders & HR)".
      iAssert (⌜forall rid, rid ∈ dom loans ->
        rid ∈ (list_to_set (all_open_readers s.(lkmm_machine)) : gset rscs_id)⌝)%I
        as %Hcovered.
      { rewrite bi.pure_forall. iIntros (rid). rewrite bi.pure_impl.
        iIntros (Hrid). apply elem_of_dom in Hrid as [[] Hlookup].
        iDestruct (big_sepM_lookup with "Hreaders") as "Hreader"; first done.
        iDestruct (state_interp_reader with "Hstate Hreader") as %Hopen.
        iPureIntro. rewrite <- dom_open_reader_map. by apply elem_of_dom_2 in Hopen. }
      iMod (ghost_var_update_halves with "Hcontrol Hphase") as "[Hcontrol Hphase]".
      iModIntro. iFrame "Hstate Hcontrol". iExists loans. by iFrame.
    Qed.

    (** A done certificate rules out outstanding loans only in a reachable
        machine state: operational event freshness prevents reader-ID reuse.
        Raw RCU ghost state alone does not establish this fact. *)
    Lemma client_reclaim P actions s γ δ snapshot gid start finish R :
      lkmm_run P (initial_lkmm P) actions s ->
      client_control δ (ClientWaiting snapshot) -∗
      state_interp γ s -∗
      gp_done γ.(rcu_name) gid snapshot start finish -∗
      client_pool γ.(rcu_name) δ (ClientWaiting snapshot) R -∗
      |==> state_interp γ s ∗
        client_control δ ClientReclaimed ∗ client_pool γ.(rcu_name) δ ClientReclaimed R ∗ R.
    Proof.
      iIntros (Hrun) "Hcontrol Hstate Hdone Hpool".
      iDestruct (state_interp_done with "Hstate Hdone")
        as %(cert & agent & index & Hcert & Hevent & Hgid & Hsnapshot).
      iDestruct "Hpool" as (loans) "(Hphase & Hauth & Hreaders & %Hcovered & HR)".
      iAssert (⌜loans = ∅⌝)%I as %->.
      { rewrite map_empty bi.pure_forall. iIntros (rid).
        destruct (loans !! rid) as [[]|] eqn:Hlookup; try done.
        iDestruct (big_sepM_lookup with "Hreaders") as "Hreader"; first done.
        iDestruct (state_interp_reader with "Hstate Hreader") as %Hopen.
        iPureIntro. exfalso.
        apply elem_of_dom_2 in Hopen. rewrite dom_open_reader_map in Hopen.
        pose proof (Hcovered rid (elem_of_dom_2 loans rid tt Hlookup)) as Hcaptured.
        rewrite Hsnapshot elem_of_list_to_set list_elem_of_In in Hcaptured.
        rewrite elem_of_list_to_set list_elem_of_In in Hopen.
        by eapply lkmm_completed_certificate_snapshot_clear. }
      iMod (ghost_var_update_halves ClientReclaimed with "Hcontrol Hphase")
        as "[Hcontrol Hphase]".
      iModIntro. iFrame "Hstate Hcontrol HR". iExists ∅. by iFrame.
    Qed.
  End protocol.
End RcuClient.
