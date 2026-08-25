From Stdlib Require Import Arith Lia List.
From stdpp Require Import base tactics.
From iris_lkmm.lkmm Require Import prelude.
Import ListNotations.

(** The finite, normal-RCU-only graph kernel used by the feasibility gate.
    The memory-model relations are parameters of the graph on purpose: this
    file studies the RCU recursion without yet transcribing the rest of LKMM. *)
Module RcuGraph.
  Export LkmmPrelude.

  Inductive label :=
  | LRead | LWrite | LRcuLock | LRcuUnlock | LSyncRcu.

  Record critical_section := CriticalSection {
    cs_lock : event_id;
    cs_unlock : event_id
  }.

  Record graph := Graph {
    events : list event_id;
    label_of : event_id -> label;
    po : relation;
    hb : relation;
    prop : relation;
    pb : relation;
    critical_sections : list critical_section
  }.

  Definition in_graph (G : graph) (e : event_id) : Prop := In e G.(events).

  Definition is_gp (G : graph) (e : event_id) : Prop := in_graph G e /\ G.(label_of) e = LSyncRcu.

  (** [rcu-rscsi] is the inverse of the matching relation computed by the
      Bell file: it runs from the unlock back to its matching lock. *)
  Definition rcu_rscsi (G : graph) : relation :=
    fun u l => exists cs,
      In cs G.(critical_sections) /\
      cs.(cs_unlock) = u /\ cs.(cs_lock) = l.

  (** Linux v6.18: [po? ; hb* ; pb* ; prop ; po]. *)
  Definition rcu_link (G : graph) : relation :=
    fun x y => exists a b c d,
      optional G.(po) x a /\
      rtc G.(hb) a b /\
      rtc G.(pb) b c /\
      G.(prop) c d /\
      G.(po) d y.

  (** Direct manual transcription of the normal-RCU disjuncts of the
      recursive [rcu-order] definition in Linux v6.18.  SRCU disjuncts are
      deliberately outside this project's selected fragment. *)
  Inductive rcu_order (G : graph) : relation :=
  | RO_gp g :
      is_gp G g ->
      rcu_order G g g
  | RO_gp_rscs g u l :
      is_gp G g -> rcu_link G g u -> rcu_rscsi G u l ->
      rcu_order G g l
  | RO_rscs_gp u l g :
      rcu_rscsi G u l -> rcu_link G l g -> is_gp G g ->
      rcu_order G u g
  | RO_gp_inner_rscs g x y u l :
      is_gp G g -> rcu_link G g x -> rcu_order G x y ->
      rcu_link G y u -> rcu_rscsi G u l ->
      rcu_order G g l
  | RO_rscs_inner_gp u l x y g :
      rcu_rscsi G u l -> rcu_link G l x -> rcu_order G x y ->
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
      is_gp G g -> rcu_link G g u -> rcu_rscsi G u l ->
      rcu_segment G g l 1 1
  | RS_rscs_gp u l g :
      rcu_rscsi G u l -> rcu_link G l g -> is_gp G g ->
      rcu_segment G u g 1 1
  | RS_gp_inner_rscs g x y u l ng nc :
      is_gp G g -> rcu_link G g x -> rcu_segment G x y ng nc ->
      rcu_link G y u -> rcu_rscsi G u l ->
      rcu_segment G g l (S ng) (S nc)
  | RS_rscs_inner_gp u l x y g ng nc :
      rcu_rscsi G u l -> rcu_link G l x -> rcu_segment G x y ng nc ->
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
      G.(po) x a /\ rcu_order G a b /\ optional G.(po) b y.

  (** Plain accesses are outside the feasibility kernel, so every represented
      event belongs to upstream [Marked]. *)
  Definition marked (G : graph) (e : event_id) : Prop := in_graph G e.

  (** Linux v6.18: [rb = prop ; rcu-fence ; hb* ; pb* ; [Marked]]. *)
  Definition rb (G : graph) : relation :=
    rel_seq
      (rel_seq
        (rel_seq (rel_seq G.(prop) (rcu_fence G)) (rtc G.(hb)))
        (rtc G.(pb)))
      (rel_id_on (marked G)).

  Definition rcu_consistent (G : graph) : Prop := forall e, ~ rb G e e.

End RcuGraph.
