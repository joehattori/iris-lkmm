From stdpp Require Import gmap.
From iris.base_logic.lib Require Import ghost_map.
From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import proofmode.
From iris_lkmm.lkmm Require Import execution.

Module LkmmMemoryGhost.
  Export LkmmExecution.

  (** This is an emission history, not a coherence order or a current value. *)
  Definition write_history (events : event_structure) (loc : location) : event_structure :=
    filter (fun entry => is_write entry.2 /\ location_of entry.2 = Some loc) events.

  Lemma write_history_lookup events loc eid ev :
    write_history events loc !! eid = Some ev <->
    events !! eid = Some ev /\ is_write ev /\ location_of ev = Some loc.
  Proof. apply map_lookup_filter_Some. Qed.

  Lemma write_history_insert events loc eid ev :
    is_write ev -> location_of ev = Some loc ->
    write_history (<[eid := ev]> events) loc = <[eid := ev]> (write_history events loc).
  Proof. intros Hwrite Hloc. by apply map_filter_insert_True. Qed.

  Lemma write_history_insert_other events loc eid ev :
    events !! eid = None ->
    (~ is_write ev \/ location_of ev <> Some loc) ->
    write_history (<[eid := ev]> events) loc = write_history events loc.
  Proof.
    intros Hfresh Hother. apply map_filter_insert_not'; first naive_solver.
    intros old Hlookup. rewrite Hfresh in Hlookup. discriminate.
  Qed.

  Definition memoryΣ : gFunctors := ghost_mapΣ location event_structure.
  Class memoryG Σ := MemoryG {
    #[local] memory_map_G :: ghost_mapG Σ location event_structure
  }.
  Global Instance subG_memoryΣ Σ : subG memoryΣ Σ -> memoryG Σ.
  Proof. solve_inG. Qed.

  Record memory_names := MemoryNames {
    memory_name : gname;
    memory_initial : gmap location value
  }.

  Definition memory_histories (initial : gmap location value) (events : event_structure) :=
    map_imap (fun loc _ => Some (write_history events loc)) initial.

  Lemma memory_histories_lookup initial events loc history :
    memory_histories initial events !! loc = Some history <->
    is_Some (initial !! loc) /\ history = write_history events loc.
  Proof.
    rewrite /memory_histories map_lookup_imap. destruct (initial !! loc); naive_solver.
  Qed.

  Section resources.
    Context `{!memoryG Σ}.

    Definition memory_auth (γ : memory_names) (events : event_structure) : iProp Σ :=
      ghost_map_auth γ.(memory_name) 1 (memory_histories γ.(memory_initial) events).

    (** Fractions agree on the exact emitted writes. Only a full fraction
        permits the history to change; neither fraction carries a last value. *)
    Definition memory_own (γ : memory_names) (loc : location) (q : Qp)
        (history : event_structure) : iProp Σ := loc ↪[γ.(memory_name)]{#q} history.

    Global Instance memory_own_timeless γ loc q history : Timeless (memory_own γ loc q history).
    Proof. apply _. Qed.
    Global Instance memory_own_fractional γ loc history :
      Fractional (fun q => memory_own γ loc q history).
    Proof. apply _. Qed.
    Global Instance memory_own_as_fractional γ loc q history :
      AsFractional (memory_own γ loc q history) (fun q => memory_own γ loc q history) q.
    Proof. split; try done. apply _. Qed.

    Lemma memory_own_agree γ loc q1 q2 h1 h2 :
      memory_own γ loc q1 h1 -∗ memory_own γ loc q2 h2 -∗ ⌜h1 = h2⌝.
    Proof. apply ghost_map_elem_agree. Qed.

    Lemma memory_own_exclusive γ loc q h1 h2 :
      memory_own γ loc 1 h1 -∗ memory_own γ loc q h2 -∗ False.
    Proof.
      iIntros "H1 H2". iDestruct (ghost_map_elem_ne with "H1 H2") as %Hne. done.
    Qed.

    Lemma memory_auth_lookup γ events loc q history :
      memory_auth γ events -∗ memory_own γ loc q history -∗
      ⌜is_Some (γ.(memory_initial) !! loc) /\ history = write_history events loc⌝.
    Proof.
      iIntros "Hauth Hloc". iDestruct (ghost_map_lookup with "Hauth Hloc") as %Hlookup.
      iPureIntro. by apply memory_histories_lookup.
    Qed.

    Lemma memory_alloc initial events :
      ⊢ |==> ∃ γ, ⌜γ.(memory_initial) = initial⌝ ∗ memory_auth γ events ∗
        [∗ map] loc ↦ val ∈ initial, memory_own γ loc 1 (write_history events loc).
    Proof.
      iMod (ghost_map_alloc (memory_histories initial events)) as (name) "[Hauth Hlocs]".
      iModIntro. iExists (MemoryNames name initial). iSplit; first done.
      iFrame "Hauth". rewrite /memory_own /=.
      assert (([∗ map] loc ↦ history ∈ memory_histories initial events, loc ↪[name] history) ⊣⊢
        ([∗ map] loc ↦ val ∈ initial, loc ↪[name] (write_history events loc))) as ->.
      { induction initial as [|loc val initial Hfresh IH] using map_ind.
        - by rewrite /memory_histories map_imap_empty !big_sepM_empty.
        - rewrite /memory_histories map_imap_insert /= !big_sepM_insert //.
          + by rewrite -/(memory_histories initial events) IH.
          + by rewrite map_lookup_imap Hfresh. }
      done.
    Qed.

    Lemma memory_auth_preserve γ events events' :
      (forall loc, write_history events loc = write_history events' loc) ->
      memory_auth γ events ⊢ memory_auth γ events'.
    Proof.
      intros Hhist. rewrite /memory_auth. assert (memory_histories γ.(memory_initial) events =
        memory_histories γ.(memory_initial) events') as ->; last done.
      apply map_imap_ext. intros loc. destruct (γ.(memory_initial) !! loc); cbn; by rewrite ?Hhist.
    Qed.

    (** A store (including the write half of an RMW) needs the entire
        location resource. All other locations keep their owned histories. *)
    Lemma memory_auth_write γ events events' loc history :
      (forall other, other <> loc -> write_history events' other = write_history events other) ->
      memory_auth γ events ∗ memory_own γ loc 1 history ==∗
      memory_auth γ events' ∗ memory_own γ loc 1 (write_history events' loc).
    Proof.
      intros Hother. iIntros "[Hauth Hloc]".
      iDestruct (memory_auth_lookup with "Hauth Hloc") as %[Hloc Hhistory].
      rewrite /memory_auth /memory_own.
      assert (memory_histories γ.(memory_initial) events' =
        <[loc := write_history events' loc]> (memory_histories γ.(memory_initial) events)) as ->.
      { apply map_eq. intros other. destruct (decide (other = loc)) as [-> | Hne].
        - rewrite lookup_insert_eq. by apply memory_histories_lookup.
        - rewrite lookup_insert_ne // /memory_histories !map_lookup_imap.
          destruct (γ.(memory_initial) !! other); cbn; try done. by rewrite Hother. }
      by iApply (ghost_map_update with "Hauth Hloc").
    Qed.

    (** Non-writing events, including failed conditional RMWs, preserve shares. *)
    Lemma memory_auth_read γ events eid ev :
      events !! eid = None -> ~ is_write ev ->
      memory_auth γ events ⊢ memory_auth γ (<[eid := ev]> events).
    Proof.
      intros Hfresh Hread. apply memory_auth_preserve. intros loc. symmetry.
      apply write_history_insert_other; try done. by left.
    Qed.

    Lemma memory_auth_store γ events loc history eid ev :
      events !! eid = None -> is_write ev -> location_of ev = Some loc ->
      memory_auth γ events ∗ memory_own γ loc 1 history ==∗
      memory_auth γ (<[eid := ev]> events) ∗ memory_own γ loc 1 (<[eid := ev]> history).
    Proof.
      intros Hfresh Hwrite Hloc. iIntros "[Hauth Hloc]".
      iDestruct (memory_auth_lookup with "Hauth Hloc") as %[_ ->].
      rewrite -(write_history_insert events loc eid ev Hwrite Hloc).
      iApply (memory_auth_write with "[$Hauth $Hloc]").
      intros other Hne. apply write_history_insert_other; first done.
      right. congruence.
    Qed.

    (** A successful RMW appends only its write half to the owned history. *)
    Lemma memory_auth_rmw γ events loc history read write re we :
      events !! read = None -> events !! write = None -> read <> write ->
      ~ is_write re -> is_write we -> location_of we = Some loc ->
      memory_auth γ events ∗ memory_own γ loc 1 history ==∗
      memory_auth γ (<[write := we]> (<[read := re]> events)) ∗
        memory_own γ loc 1 (<[write := we]> history).
    Proof.
      intros Hread Hwrite Hne Hre Hwe Hloc. iIntros "[Hauth Hloc]".
      iDestruct (memory_auth_read _ _ _ _ Hread Hre with "Hauth") as "Hauth".
      iApply (memory_auth_store with "[$Hauth $Hloc]"); try done.
      by rewrite lookup_insert_ne.
    Qed.
  End resources.
End LkmmMemoryGhost.
