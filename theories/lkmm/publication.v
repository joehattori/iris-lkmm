From Stdlib Require Import Relations.Relation_Operators.
From stdpp Require Import tactics.
From iris_lkmm.lkmm Require Import memory_relations.

(** A reusable LKMM publication law, independent of Core programs and Iris.
    It forbids a stale data read after observing a release with an acquire.
    Event identities, locations, values, and agent indices are unrestricted. *)
Module LkmmPublication.
  Export LkmmMemoryRelations.

  Lemma release_acquire_no_stale E rmw_edges rf_edges co_edges
      data_edges addr_edges ctrl_edges a b c d :
    marked E a -> marked E b -> marked E c -> marked E d ->
    event_is_memory E a -> event_is_memory E d ->
    po E a b -> po E c d -> same_agent E d c -> d <> c ->
    release E rmw_edges b -> acquire E rmw_edges c ->
    rfe E rf_edges b c -> fre E rf_edges co_edges d a ->
    happens_before E rmw_edges rf_edges co_edges data_edges addr_edges ctrl_edges ->
    False.
  Proof.
    intros Hma Hmb Hmc Hmd Hmem_a Hmem_d Hab Hcd Hsame Hne
      Hrelease Hacquire Hrfe Hfre Hacyclic.
    assert (po_rel E rmw_edges a b) as Hrel.
    { exists b. split; last by split.
      exists a. split; last done. by split. }
    assert (cumul_fence E rmw_edges rf_edges a b) as Hcumul.
    { exists b. split; last apply rt_refl.
      exists b. split; last by split.
      exists a. split; first by split. left.
      exists a. split; [by left|by right]. }
    assert (prop E rmw_edges rf_edges co_edges d c) as Hprop.
    { exists c. split; last by split.
      exists b. split; last by right.
      exists b. split; last by split.
      exists a. split; last by apply rt_step.
      exists d. split; first by split.
      right. destruct Hfre as [Hfr Hext]. split; [by right|done]. }
    assert (hb E rmw_edges rf_edges co_edges data_edges addr_edges ctrl_edges d c) as Hback.
    { exists c. split; last by split. exists d. split; first by split.
      right. right. split; last done. split; done. }
    assert (hb E rmw_edges rf_edges co_edges data_edges addr_edges ctrl_edges c d) as Hforward.
    { exists d. split; last by split. exists c. split; first by split.
      left. right. right. split.
      - left. right. right. exists d. split.
        + exists c. split; [by split|done].
        + by split.
      - unfold same_agent, same_attribute in *. naive_solver. }
    apply (Hacyclic c). eapply t_trans; apply t_step; eassumption.
  Qed.
End LkmmPublication.
