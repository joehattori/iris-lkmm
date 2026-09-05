From Stdlib Require Import Lia.
From stdpp Require Import tactics.
From iris_lkmm.lkmm Require Import execution_graph memory_relations rcu_matching.

(** The finite, normal-RCU-only graph kernel used by the feasibility gate.
    The shared graph record derives [prop], [hb], and [pb]; this file adds only
    the normal-RCU classifications and consistency condition. *)
Module RcuGraph.
  Export LkmmExecutionGraph RcuMatching.

  Definition is_gp (G : graph) : event_id -> Prop :=
    event_has_barrier_kind G.(events) BarrierSyncRcu.

  (** [rcu-rscsi] is the inverse of the matching relation computed by the
      Bell file: it runs from the unlock back to its matching lock. *)
  Definition graph_rcu_rscsi (G : graph) : relation := RcuMatching.rcu_rscsi G.(events).

  (** Linux v6.18: [po? ; hb* ; pb* ; prop ; po]. *)
  Definition rcu_link (G : graph) : relation :=
    fun x y => exists a b c d,
      optional (graph_po G) x a /\
      rtc (graph_hb G) a b /\
      rtc (graph_pb G) b c /\
      graph_prop G c d /\
      graph_po G d y.

  (** Direct manual transcription of the normal-RCU disjuncts of the
      recursive [rcu-order] definition in Linux v6.18.  SRCU disjuncts are
      deliberately outside this project's selected fragment. *)
  Inductive rcu_order (G : graph) : relation :=
  | RO_gp g :
      is_gp G g ->
      rcu_order G g g
  | RO_gp_rscs g u l :
      is_gp G g -> rcu_link G g u -> graph_rcu_rscsi G u l ->
      rcu_order G g l
  | RO_rscs_gp u l g :
      graph_rcu_rscsi G u l -> rcu_link G l g -> is_gp G g ->
      rcu_order G u g
  | RO_gp_inner_rscs g x y u l :
      is_gp G g -> rcu_link G g x -> rcu_order G x y ->
      rcu_link G y u -> graph_rcu_rscsi G u l ->
      rcu_order G g l
  | RO_rscs_inner_gp u l x y g :
      graph_rcu_rscsi G u l -> rcu_link G l x -> rcu_order G x y ->
      rcu_link G y g -> is_gp G g ->
      rcu_order G u g
  | RO_join x y z w :
      rcu_order G x y -> rcu_link G y z -> rcu_order G z w ->
      rcu_order G x w.

  (** A constructive certificate for the same ordering.  In addition to its
      endpoints it records how many grace periods and read-side critical
      sections have been consumed.  This is suitable for an incremental
      implementation: certificates can be wrapped or joined without
      inspecting a completed execution graph. *)
  Inductive rcu_segment (G : graph) :
      event_id -> event_id -> nat -> nat -> Prop :=
  | RS_gp g :
      is_gp G g ->
      rcu_segment G g g 1 0
  | RS_gp_rscs g u l :
      is_gp G g -> rcu_link G g u -> graph_rcu_rscsi G u l ->
      rcu_segment G g l 1 1
  | RS_rscs_gp u l g :
      graph_rcu_rscsi G u l -> rcu_link G l g -> is_gp G g ->
      rcu_segment G u g 1 1
  | RS_gp_inner_rscs g x y u l ng nc :
      is_gp G g -> rcu_link G g x -> rcu_segment G x y ng nc ->
      rcu_link G y u -> graph_rcu_rscsi G u l ->
      rcu_segment G g l (S ng) (S nc)
  | RS_rscs_inner_gp u l x y g ng nc :
      graph_rcu_rscsi G u l -> rcu_link G l x -> rcu_segment G x y ng nc ->
      rcu_link G y g -> is_gp G g ->
      rcu_segment G u g (S ng) (S nc)
  | RS_join x y z w ng1 nc1 ng2 nc2 :
      rcu_segment G x y ng1 nc1 -> rcu_link G y z ->
      rcu_segment G z w ng2 nc2 ->
      rcu_segment G x w (ng1 + ng2) (nc1 + nc2).

  Lemma rcu_segment_balance G x y ng nc :
    rcu_segment G x y ng nc -> nc <= ng.
  Proof. induction 1; lia. Qed.

  Lemma rcu_segment_sound G x y ng nc :
    rcu_segment G x y ng nc -> rcu_order G x y.
  Proof. induction 1; by econstructor. Qed.

  Lemma rcu_order_complete G x y :
    rcu_order G x y ->
    exists ng nc, rcu_segment G x y ng nc.
  Proof.
    induction 1.
    - exists 1, 0. by constructor.
    - exists 1, 1. by econstructor.
    - exists 1, 1. by econstructor.
    - destruct IHrcu_order as (ng & nc & Hseg).
      exists (S ng), (S nc). by econstructor.
    - destruct IHrcu_order as (ng & nc & Hseg).
      exists (S ng), (S nc). by econstructor.
    - destruct IHrcu_order1 as (ng1 & nc1 & Hseg1).
      destruct IHrcu_order2 as (ng2 & nc2 & Hseg2).
      exists (ng1 + ng2), (nc1 + nc2). by econstructor.
  Qed.

  Theorem rcu_law_equivalence G x y :
    rcu_order G x y <->
    exists ng nc, rcu_segment G x y ng nc /\ nc <= ng.
  Proof.
    split.
    - intros Horder.
      destruct (rcu_order_complete G x y Horder) as (ng & nc & Hseg).
      exists ng, nc. split; first done.
      by apply (rcu_segment_balance G x y ng nc).
    - intros (ng & nc & Hseg & _). by apply (rcu_segment_sound G x y ng nc).
  Qed.

  (** Linux v6.18: [rcu-fence = po ; rcu-order ; po?]. *)
  Definition rcu_fence (G : graph) : relation :=
    fun x y => exists a b,
      graph_po G x a /\ rcu_order G a b /\ optional (graph_po G) b y.

  Definition graph_marked (G : graph) : event_id -> Prop := LkmmMemoryRelations.marked G.(events).

  (** Linux v6.18: [rb = prop ; rcu-fence ; hb* ; pb* ; [Marked]]. *)
  Definition rb (G : graph) : relation :=
    rel_seq
      (rel_seq
        (rel_seq (rel_seq (graph_prop G) (rcu_fence G)) (rtc (graph_hb G)))
        (rtc (graph_pb G)))
      (rel_id_on (graph_marked G)).

  Definition rcu_consistent (G : graph) : Prop := forall e, ~ rb G e e.

End RcuGraph.
