From Stdlib Require Import Arith.
From stdpp Require Import fin_map_dom gmap.
From iris.algebra Require Import auth.
From iris.base_logic.lib Require Import ghost_map mono_nat.
From iris.proofmode Require Import proofmode.

(** Iris ghost state for the normal-RCU reader and grace-period protocol.

    Readers own exclusive entries in [rg_open_name].  Grace periods are
    registered in [rg_gp_name] with the exact finite set of readers captured
    at begin.  Completion changes that entry from pending to a persistent
    done certificate and advances [rg_epoch_name], an authoritative MaxNat.
    The update is gated by disjointness of the captured snapshot and the
    current open-reader domain. *)
Module RcuGhost.

  Definition rscs_id := nat.
  Definition gp_id := nat.

  Inductive gp_status :=
  | GpPending (snapshot : gset rscs_id) (start_epoch : nat)
  | GpDone (snapshot : gset rscs_id) (start_epoch finish_epoch : nat).

  Definition rcuΣ : gFunctors :=
    #[ ghost_mapΣ rscs_id unit;
       ghost_mapΣ gp_id gp_status;
       mono_natΣ ].

  Class rcuG Σ := RcuG {
    #[local] rcu_open_G :: ghost_mapG Σ rscs_id unit;
    #[local] rcu_gp_G :: ghost_mapG Σ gp_id gp_status;
    #[local] rcu_epoch_G :: mono_natG Σ
  }.

  Global Instance subG_rcuΣ Σ : subG rcuΣ Σ -> rcuG Σ.
  Proof. solve_inG. Qed.

  Record rcu_names := RcuNames {
    rg_open_name : gname;
    rg_gp_name : gname;
    rg_epoch_name : gname
  }.

  Section definitions.
    Context `{!rcuG Σ}.

    Definition rcu_auth (γ : rcu_names) (open : gmap rscs_id unit)
        (gps : gmap gp_id gp_status) (epoch : nat) : iProp Σ :=
      ghost_map_auth γ.(rg_open_name) 1 open ∗
      ghost_map_auth γ.(rg_gp_name) 1 gps ∗
      mono_nat_auth_own γ.(rg_epoch_name) 1 epoch.

    Definition reader_token (γ : rcu_names) (rid : rscs_id) : iProp Σ :=
      rid ↪[γ.(rg_open_name)] tt.

    Definition gp_pending (γ : rcu_names) (gid : gp_id)
        (snapshot : gset rscs_id) (start : nat) : iProp Σ :=
      gid ↪[γ.(rg_gp_name)] GpPending snapshot start.

    Definition gp_done (γ : rcu_names) (gid : gp_id)
        (snapshot : gset rscs_id) (start finish : nat) : iProp Σ :=
      gid ↪[γ.(rg_gp_name)]□ GpDone snapshot start finish ∗
      mono_nat_lb_own γ.(rg_epoch_name) finish.
  End definitions.

  Section rules.
    Context `{!rcuG Σ}.
    Implicit Types (γ : rcu_names).

    Global Instance gp_done_persistent γ gid snapshot start finish :
      Persistent (gp_done γ gid snapshot start finish).
    Proof. apply _. Qed.

    Lemma rcu_ghost_alloc :
      ⊢ |==> ∃ γ, rcu_auth γ ∅ ∅ 0.
    Proof.
      iMod (ghost_map_alloc_empty (K:=rscs_id) (V:=unit))
        as (γopen) "Hopen".
      iMod (ghost_map_alloc_empty (K:=gp_id) (V:=gp_status))
        as (γgp) "Hgp".
      iMod (mono_nat_own_alloc 0) as (γepoch) "[Hepoch _]".
      iModIntro. iExists (RcuNames γopen γgp γepoch).
      rewrite /rcu_auth /=. iFrame.
    Qed.

    Lemma rcu_reader_enter γ open gps epoch rid :
      open !! rid = None ->
      rcu_auth γ open gps epoch ==∗
        rcu_auth γ (<[rid := tt]> open) gps epoch ∗
        reader_token γ rid.
    Proof.
      iIntros (Hfresh) "(Hopen & Hgps & Hepoch)".
      iMod (ghost_map_insert rid tt with "Hopen") as "[Hopen Hreader]"; first done.
      iModIntro. rewrite /rcu_auth /reader_token. iFrame.
    Qed.

    Lemma rcu_reader_exit γ open gps epoch rid :
      rcu_auth γ open gps epoch ∗ reader_token γ rid ==∗
        rcu_auth γ (delete rid open) gps epoch.
    Proof.
      iIntros "((Hopen & Hgps & Hepoch) & Hreader)".
      iMod (ghost_map_delete with "Hopen Hreader") as "Hopen".
      iModIntro. rewrite /rcu_auth. iFrame.
    Qed.

    Lemma rcu_gp_begin γ open gps epoch gid :
      gps !! gid = None ->
      rcu_auth γ open gps epoch ==∗
        rcu_auth γ open (<[gid := GpPending (dom open) epoch]> gps) epoch ∗
        gp_pending γ gid (dom open) epoch.
    Proof.
      iIntros (Hfresh) "(Hopen & Hgps & Hepoch)".
      iMod (ghost_map_insert gid (GpPending (dom open) epoch) with "Hgps")
        as "[Hgps Hpending]"; first done.
      iModIntro. rewrite /rcu_auth /gp_pending. iFrame.
    Qed.

    Lemma rcu_gp_finish γ open gps epoch gid snapshot start :
      snapshot ## dom open ->
      rcu_auth γ open gps epoch ∗ gp_pending γ gid snapshot start ==∗
        rcu_auth γ open (<[gid := GpDone snapshot start (S epoch)]> gps) (S epoch) ∗
        gp_done γ gid snapshot start (S epoch).
    Proof.
      iIntros (Hclear) "((Hopen & Hgps & Hepoch) & Hpending)".
      iMod (ghost_map_update (GpDone snapshot start (S epoch))
        with "Hgps Hpending") as "[Hgps Hdone]".
      iMod (ghost_map_elem_persist with "Hdone") as "#Hdone".
      iMod (mono_nat_own_update (S epoch) with "Hepoch")
        as "[Hepoch #Hlb]"; first lia.
      iModIntro. rewrite /rcu_auth /gp_done. iFrame "Hopen Hgps Hepoch".
      iFrame "#".
    Qed.

    (** The completion update is stable under an arbitrary client frame.
        This update supplies the compositional reclamation rule. *)
    Lemma rcu_gp_finish_frame γ open gps epoch gid snapshot start
        (R : iProp Σ) :
      snapshot ## dom open ->
      rcu_auth γ open gps epoch ∗ gp_pending γ gid snapshot start ∗ R ==∗
        rcu_auth γ open
          (<[gid := GpDone snapshot start (S epoch)]> gps) (S epoch) ∗
        gp_done γ gid snapshot start (S epoch) ∗ R.
    Proof.
      iIntros (Hclear) "(Hauth & Hpending & HR)".
      iMod (rcu_gp_finish with "[$Hauth $Hpending]") as "[Hauth #Hdone]";
        first done.
      iModIntro. iFrame "Hauth HR". iExact "Hdone".
    Qed.

    Lemma gp_done_epoch_valid γ gid snapshot start finish epoch q :
      mono_nat_auth_own γ.(rg_epoch_name) q epoch -∗
      gp_done γ gid snapshot start finish -∗
      ⌜finish ≤ epoch⌝.
    Proof.
      iIntros "Hepoch [_ Hlb]".
      iDestruct (mono_nat_lb_own_valid with "Hepoch Hlb") as %[_ Hle].
      done.
    Qed.

  End rules.

End RcuGhost.
