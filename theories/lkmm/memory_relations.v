From Stdlib Require Import Relations.Relation_Operators ZArith.
From stdpp Require Import gmap tactics.
From iris_lkmm.lkmm Require Import execution.

(** Finite candidate relations for the relational LKMM model.

    Reads-from and coherence order are candidate choices rather than
    relations derived uniquely from the event structure.  Their
    well-formedness is stated separately so that partial operational states
    may carry incomplete edge sets later. *)
Module LkmmMemoryRelations.
  Export LkmmExecution.

  Definition rf (edges : edge_set) : relation := edge_relation edges.

  (** The finite edge set stores the complete transitive coherence order,
      rather than only its immediate-successor edges. *)
  Definition co (edges : edge_set) : relation := edge_relation edges.

  (** Read-modify-write pairing is supplied by the candidate execution.
      Successful operations contribute a marked read-to-write edge; failed
      conditional operations contribute only their marked read event. *)
  Definition rmw (edges : edge_set) : relation := edge_relation edges.

  (** Direct dependency edges are finite provenance supplied by the candidate
      program graph.  Bell carrying is defined separately below. *)
  Definition direct_addr (edges : edge_set) : relation := edge_relation edges.

  Definition direct_data (edges : edge_set) : relation := edge_relation edges.

  Definition direct_ctrl (edges : edge_set) : relation := edge_relation edges.

  (** Linux v6.18 [linux-kernel.bell]: semantic event classes obtained by
      filtering the syntactic access and barrier annotations. *)
  Definition failed_rmw (E : event_structure) (rmw_edges : edge_set) (eid : event_id) : Prop :=
    event_is_rmw_marked E eid /\
    ~ (rel_domain (rmw rmw_edges) eid \/ rel_range (rmw rmw_edges) eid).

  Definition acquire (E : event_structure) (rmw_edges : edge_set) (eid : event_id) : Prop :=
    event_has_access_mode E AccessAcquire eid /\
    ~ event_has_access_kind E AccessWrite eid /\
    ~ failed_rmw E rmw_edges eid.

  Definition release (E : event_structure) (rmw_edges : edge_set) (eid : event_id) : Prop :=
    event_has_access_mode E AccessRelease eid /\
    ~ event_has_access_kind E AccessRead eid /\
    ~ failed_rmw E rmw_edges eid.

  Definition mb_event (E : event_structure) (rmw_edges : edge_set) (eid : event_id) : Prop :=
    (event_has_access_mode E AccessMb eid \/ event_has_barrier_kind E BarrierMb eid) /\
    ~ failed_rmw E rmw_edges eid.

  Definition noreturn (E : event_structure) (eid : event_id) : Prop :=
    event_has_access_mode E AccessNoreturn eid /\
    ~ event_has_access_kind E AccessWrite eid.

  (** Upstream derives [Plain = M \ Marked].  In the canonical vocabulary,
      an [AccessPlain], [NotRmw] access is exactly such an event.  An
      independently RMW-marked access remains [Marked]. *)
  Definition plain (E : event_structure) (eid : event_id) : Prop :=
    event_has_access_mode E AccessPlain eid /\
    ~ event_is_rmw_marked E eid.

  Definition marked (E : event_structure) (eid : event_id) : Prop :=
    in_event_structure E eid /\ ~ plain E eid.

  Lemma barrier_marked E kind eid :
    event_has_barrier_kind E kind eid -> marked E eid.
  Proof.
    intros Hbarrier.
    apply event_has_barrier_kind_lookup in Hbarrier as (ev & Hlookup & Hkind).
    split; first by eapply lookup_event_in.
    intros [Hplain _].
    apply event_has_access_mode_lookup in Hplain as (ev' & Hlookup' & Hmode).
    assert (ev' = ev) as -> by congruence.
    destruct ev as [loc val | agent index label]; first discriminate.
    destruct label; discriminate.
  Qed.

  (** Linux v6.18: [acq-po = [Acquire] ; po ; [M]] *)
  Definition acq_po (E : event_structure) (rmw_edges : edge_set) : relation :=
    rel_seq (rel_seq (rel_id_on (acquire E rmw_edges)) (po E))
      (rel_id_on (event_is_memory E)).

  (** Linux v6.18: [po-rel = [M] ; po ; [Release]] *)
  Definition po_rel (E : event_structure) (rmw_edges : edge_set) : relation :=
    rel_seq (rel_seq (rel_id_on (event_is_memory E)) (po E))
      (rel_id_on (release E rmw_edges)).

  (** Herd7's standard library defines
      [fencerel(B) = (po & (_ * B)) ; po]. *)
  Definition fencerel (E : event_structure) (kind : barrier_kind) : relation :=
    rel_seq (rel_seq (po E) (rel_id_on (event_has_barrier_kind E kind))) (po E).

  (** Linux v6.18: [R4rmb = R \ Noreturn]. *)
  Definition r4_rmb (E : event_structure) (eid : event_id) : Prop :=
    event_is_read E eid /\ ~ noreturn E eid.

  (** Linux v6.18: [rmb = [R4rmb] ; fencerel(Rmb) ; [R4rmb]]. *)
  Definition rmb (E : event_structure) : relation :=
    rel_seq (rel_seq (rel_id_on (r4_rmb E)) (fencerel E BarrierRmb))
      (rel_id_on (r4_rmb E)).

  (** Linux v6.18: [wmb = [W] ; fencerel(Wmb) ; [W]]. *)
  Definition wmb (E : event_structure) : relation :=
    rel_seq (rel_seq (rel_id_on (event_is_write E)) (fencerel E BarrierWmb))
      (rel_id_on (event_is_write E)).

  (** Selected Linux v6.18 branches:
      [mb =
        ([M] ; fencerel(Mb) ; [M]) |
        ([M] ; po ; [Mb & R]) |
        ([Mb & W] ; po ; [M]) |
        ([M] ; fencerel(Before-atomic) ; [RMW] ; po? ; [M]) |
        ([M] ; po? ; [RMW] ; fencerel(After-atomic) ; [M])].

      The first branch models explicit [smp_mb()] barriers.  The next two
      give successful full-barrier RMWs the ordering they would have if the
      operation were enclosed by [smp_mb()] barriers: Bell adds [Mb] tags to
      the read and write, and these branches supply the corresponding virtual
      program-order edges.  The final two branches model explicit
      [smp_mb__before_atomic()] and [smp_mb__after_atomic()] augmentation
      barriers around syntactically RMW-marked events. *)
  Definition mb (E : event_structure) (rmw_edges : edge_set) : relation :=
    rel_union
      (rel_seq
        (rel_seq (rel_id_on (event_is_memory E)) (fencerel E BarrierMb))
        (rel_id_on (event_is_memory E)))
      (rel_union
        (rel_seq
          (rel_seq (rel_id_on (event_is_memory E)) (po E))
          (rel_intersection
            (rel_id_on (mb_event E rmw_edges)) (rel_id_on (event_is_read E))))
        (rel_union
          (rel_seq
            (rel_seq
              (rel_intersection
                (rel_id_on (mb_event E rmw_edges))
                (rel_id_on (event_is_write E)))
              (po E))
            (rel_id_on (event_is_memory E)))
          (rel_union
            (rel_seq
              (rel_seq
                (rel_seq
                  (rel_seq
                    (rel_id_on (event_is_memory E))
                    (fencerel E BarrierBeforeAtomic))
                  (rel_id_on (event_is_rmw_marked E)))
                (optional (po E)))
              (rel_id_on (event_is_memory E)))
            (rel_seq
              (rel_seq
                (rel_seq
                  (rel_seq (rel_id_on (event_is_memory E)) (optional (po E)))
                  (rel_id_on (event_is_rmw_marked E)))
                (fencerel E BarrierAfterAtomic))
              (rel_id_on (event_is_memory E)))))).

  (** Selected normal-RCU branch of [gp = po ; [Sync-rcu | Sync-srcu] ; po?]. *)
  Definition gp (E : event_structure) : relation :=
    rel_seq
      (rel_seq (po E) (rel_id_on (event_has_barrier_kind E BarrierSyncRcu)))
      (optional (po E)).

  Definition strong_fence (E : event_structure) (rmw_edges : edge_set) : relation :=
    rel_union (mb E rmw_edges) (gp E).

  Definition nonrw_fence (E : event_structure) (rmw_edges : edge_set) : relation :=
    rel_union (strong_fence E rmw_edges)
      (rel_union (po_rel E rmw_edges) (acq_po E rmw_edges)).

  Definition fence (E : event_structure) (rmw_edges : edge_set) : relation :=
    rel_union (nonrw_fence E rmw_edges) (rel_union (wmb E) (rmb E)).

  (** From-read is derived from reads-from and coherence order: a read is
      before every write that is coherence-later than its source write. *)
  Definition fr (rf_edges co_edges : edge_set) : relation :=
    rel_seq (rel_inverse (rf rf_edges)) (co co_edges).

  (** Internal and external communication are the same-agent and
      not-same-agent parts of the candidate relations.  Initial writes have
      no agent and therefore occur only in the external parts. *)
  Definition rfi (E : event_structure) (rf_edges : edge_set) : relation :=
    rel_intersection (rf rf_edges) (same_agent E).

  Definition rfe (E : event_structure) (rf_edges : edge_set) : relation :=
    rel_intersection (rf rf_edges) (ext E).

  Definition coi (E : event_structure) (co_edges : edge_set) : relation :=
    rel_intersection (co co_edges) (same_agent E).

  Definition coe (E : event_structure) (co_edges : edge_set) : relation :=
    rel_intersection (co co_edges) (ext E).

  (** [fri] and [fre] classify the endpoints of the already-derived [fr]
      relation; they are not reconstructed from partitions of [rf] and [co]. *)
  Definition fri (E : event_structure) (rf_edges co_edges : edge_set) : relation :=
    rel_intersection (fr rf_edges co_edges) (same_agent E).

  Definition fre (E : event_structure) (rf_edges co_edges : edge_set) : relation :=
    rel_intersection (fr rf_edges co_edges) (ext E).

  Lemma rf_internal_external E edges write read :
    rf edges write read <->
    rel_union (rfi E edges) (rfe E edges) write read.
  Proof.
    split.
    - intros Hrf. destruct (decide (same_agent E write read)) as [Hint | Hext].
      + by left.
      + by right.
    - intros [[Hrf _] | [Hrf _]]; exact Hrf.
  Qed.

  Lemma co_internal_external E edges write1 write2 :
    co edges write1 write2 <->
    rel_union (coi E edges) (coe E edges) write1 write2.
  Proof.
    split.
    - intros Hco. destruct (decide (same_agent E write1 write2)) as [Hint | Hext].
      + by left.
      + by right.
    - intros [[Hco _] | [Hco _]]; exact Hco.
  Qed.

  Lemma fr_internal_external E rf_edges co_edges read write :
    fr rf_edges co_edges read write <->
    rel_union (fri E rf_edges co_edges) (fre E rf_edges co_edges) read write.
  Proof.
    split.
    - intros Hfr. destruct (decide (same_agent E read write)) as [Hint | Hext].
      + by left.
      + by right.
    - intros [[Hfr _] | [Hfr _]]; exact Hfr.
  Qed.

  (** Linux v6.18 [linux-kernel.bell]: with SRCU excluded, dependency
      carrying is [(direct_data ; rfi)*]. *)
  Definition carry_dep (E : event_structure) (rf_edges data_edges : edge_set) : relation :=
    rtc (rel_seq (direct_data data_edges) (rfi E rf_edges)).

  Definition addr (E : event_structure) (rf_edges data_edges addr_edges : edge_set) : relation :=
    rel_seq (carry_dep E rf_edges data_edges) (direct_addr addr_edges).

  Definition data (E : event_structure) (rf_edges data_edges : edge_set) : relation :=
    rel_seq (carry_dep E rf_edges data_edges) (direct_data data_edges).

  Definition ctrl (E : event_structure) (rf_edges data_edges ctrl_edges : edge_set) : relation :=
    rel_seq (carry_dep E rf_edges data_edges) (direct_ctrl ctrl_edges).

  (** Linux v6.18: [dep = addr | data]. *)
  Definition dep (E : event_structure) (rf_edges data_edges addr_edges : edge_set) : relation :=
    rel_union (addr E rf_edges data_edges addr_edges) (data E rf_edges data_edges).

  (** Linux v6.18: [rwdep = (dep | ctrl) ; [W]]. *)
  Definition rwdep (E : event_structure)
      (rf_edges data_edges addr_edges ctrl_edges : edge_set) : relation :=
    rel_seq
      (rel_union (dep E rf_edges data_edges addr_edges)
        (ctrl E rf_edges data_edges ctrl_edges))
      (rel_id_on (event_is_write E)).

  (** Linux v6.18: [overwrite = co | fr]. *)
  Definition overwrite (rf_edges co_edges : edge_set) : relation :=
    rel_union (co co_edges) (fr rf_edges co_edges).

  (** Linux v6.18:
      [to-w = rwdep | (overwrite & int) | (addr ; [Plain] ; wmb)]. *)
  Definition to_w (E : event_structure)
      (rf_edges co_edges data_edges addr_edges ctrl_edges : edge_set) : relation :=
    rel_union (rwdep E rf_edges data_edges addr_edges ctrl_edges)
      (rel_union (rel_intersection (overwrite rf_edges co_edges) (same_agent E))
        (rel_seq
          (rel_seq (addr E rf_edges data_edges addr_edges) (rel_id_on (plain E)))
          (wmb E))).

  (** Linux v6.18: [to-r = (addr ; [R]) | (dep ; [Marked] ; rfi)]. *)
  Definition to_r (E : event_structure) (rf_edges data_edges addr_edges : edge_set) : relation :=
    rel_union
      (rel_seq (addr E rf_edges data_edges addr_edges)
        (rel_id_on (event_is_read E)))
      (rel_seq
        (rel_seq (dep E rf_edges data_edges addr_edges) (rel_id_on (marked E)))
        (rfi E rf_edges)).

  (** Selected fragment of Linux v6.18 [ppo].  Lock ordering is outside the
      event vocabulary, and [fence] is the current base fence relation. *)
  Definition ppo (E : event_structure)
      (rmw_edges rf_edges co_edges data_edges addr_edges ctrl_edges : edge_set) : relation :=
    rel_union (to_r E rf_edges data_edges addr_edges)
      (rel_union (to_w E rf_edges co_edges data_edges addr_edges ctrl_edges)
        (rel_intersection (fence E rmw_edges) (same_agent E))).

  (** Linux v6.18: [A-cumul(r) = (rfe ; [Marked])? ; r]. *)
  Definition a_cumul (E : event_structure) (rf_edges : edge_set) (r : relation) : relation :=
    rel_seq (optional (rel_seq (rfe E rf_edges) (rel_id_on (marked E)))) r.

  (** Linux v6.18: [rmw-sequence = (rf ; rmw)*]. *)
  Definition rmw_sequence (rf_edges rmw_edges : edge_set) : relation :=
    rtc (rel_seq (rf rf_edges) (rmw rmw_edges)).

  (** Selected Linux v6.18:
      [cumul-fence = [Marked] ; (A-cumul(strong-fence | po-rel) | wmb) ; [Marked] ; rmw-sequence].
      The [po-unlock-lock-po] branch is omitted with lock events. *)
  Definition cumul_fence (E : event_structure) (rmw_edges rf_edges : edge_set) : relation :=
    rel_seq
      (rel_seq
        (rel_seq
          (rel_id_on (marked E))
          (rel_union
            (a_cumul E rf_edges
              (rel_union (strong_fence E rmw_edges) (po_rel E rmw_edges)))
            (wmb E)))
        (rel_id_on (marked E)))
      (rmw_sequence rf_edges rmw_edges).

  (** Linux v6.18:
      [prop = [Marked] ; (overwrite & ext)? ; cumul-fence* ; [Marked] ; rfe? ; [Marked]]. *)
  Definition prop (E : event_structure) (rmw_edges rf_edges co_edges : edge_set) : relation :=
    rel_seq
      (rel_seq
        (rel_seq
          (rel_seq
            (rel_seq
              (rel_id_on (marked E))
              (optional
                (rel_intersection (overwrite rf_edges co_edges) (ext E))))
            (rtc (cumul_fence E rmw_edges rf_edges)))
          (rel_id_on (marked E)))
        (optional (rfe E rf_edges)))
      (rel_id_on (marked E)).

  Lemma prop_marked_refl E rmw_edges rf_edges co_edges eid :
    marked E eid -> prop E rmw_edges rf_edges co_edges eid eid.
  Proof.
    intros Hmarked. unfold prop.
    apply rel_seq_id_on_r. split; last done.
    exists eid. split; last by left.
    apply rel_seq_id_on_r. split; last done.
    exists eid. split; last apply rt_refl.
    apply rel_seq_id_on_l. split; [done | by left].
  Qed.

  Section PropMonotonicity.
    Context (E1 E2 : event_structure) (rmw1 rmw2 rf1 rf2 co1 co2 : edge_set).
    Context (HE : event_structure_included E1 E2).
    Context (HRMW : rmw1 ⊆ rmw2) (HRF : rf1 ⊆ rf2) (HCO : co1 ⊆ co2).

    Local Lemma edge_relation_mono edges1 edges2 :
      edges1 ⊆ edges2 -> rel_included (edge_relation edges1) (edge_relation edges2).
    Proof. intros Hedges x y Hxy. by apply Hedges. Qed.

    Lemma marked_mono eid : marked E1 eid -> marked E2 eid.
    Proof.
      intros [Hin Hnot_plain]. split; first by eapply in_event_structure_mono.
      intros [Hmode Hnot_marked]. apply Hnot_plain. split.
      - by eapply event_has_access_mode_reflect.
      - intros Hmarked. apply Hnot_marked. by eapply event_is_rmw_marked_mono.
    Qed.

    Local Lemma not_failed_rmw_mono eid :
      in_event_structure E1 eid ->
      ~ failed_rmw E1 rmw1 eid -> ~ failed_rmw E2 rmw2 eid.
    Proof.
      intros Hin Hnot_failed [Hmarked Houtside]. apply Hnot_failed. split.
      - by eapply event_is_rmw_marked_reflect.
      - intros [Hdomain | Hrange]; apply Houtside.
        + left. destruct Hdomain as (target & Hedge). exists target. by apply HRMW.
        + right. destruct Hrange as (source & Hedge). exists source. by apply HRMW.
    Qed.

    Local Lemma acquire_mono eid :
      acquire E1 rmw1 eid -> acquire E2 rmw2 eid.
    Proof.
      intros (Hmode & Hnot_write & Hnot_failed).
      apply event_has_access_mode_lookup in Hmode as (ev & Hlookup & Hmode).
      assert (in_event_structure E1 eid) as Hin by eauto using lookup_event_in.
      split_and!.
      - apply event_has_access_mode_lookup. exists ev. split; [by eapply HE | done].
      - intros Hwrite. apply Hnot_write. by eapply event_has_access_kind_reflect.
      - by eapply not_failed_rmw_mono.
    Qed.

    Local Lemma release_mono eid :
      release E1 rmw1 eid -> release E2 rmw2 eid.
    Proof.
      intros (Hmode & Hnot_read & Hnot_failed).
      apply event_has_access_mode_lookup in Hmode as (ev & Hlookup & Hmode).
      assert (in_event_structure E1 eid) as Hin by eauto using lookup_event_in.
      split_and!.
      - apply event_has_access_mode_lookup. exists ev. split; [by eapply HE | done].
      - intros Hread. apply Hnot_read. by eapply event_has_access_kind_reflect.
      - by eapply not_failed_rmw_mono.
    Qed.

    Local Lemma mb_event_mono eid :
      mb_event E1 rmw1 eid -> mb_event E2 rmw2 eid.
    Proof.
      intros [Htag Hnot_failed].
      assert (in_event_structure E1 eid) as Hin.
      { destruct Htag as [Hmode | Hbarrier].
        - apply event_has_access_mode_lookup in Hmode as (ev & Hlookup & _).
          by eapply lookup_event_in.
        - apply event_has_barrier_kind_lookup in Hbarrier as (ev & Hlookup & _).
          by eapply lookup_event_in. }
      split.
      - destruct Htag as [Hmode | Hbarrier].
        + left. by eapply event_has_access_mode_mono.
        + right. by eapply event_has_barrier_kind_mono.
      - by eapply not_failed_rmw_mono.
    Qed.

    Local Lemma fencerel_mono kind :
      rel_included (fencerel E1 kind) (fencerel E2 kind).
    Proof.
      unfold fencerel. apply rel_seq_mono; last by apply po_mono.
      apply rel_seq_mono; first by apply po_mono.
      apply rel_id_on_mono. intros eid Hbarrier.
      by eapply event_has_barrier_kind_mono.
    Qed.

    Lemma wmb_mono : rel_included (wmb E1) (wmb E2).
    Proof.
      unfold wmb. apply rel_seq_mono.
      - apply rel_seq_mono.
        + apply rel_id_on_mono. intros eid Hwrite. by eapply event_is_write_mono.
        + apply fencerel_mono.
      - apply rel_id_on_mono. intros eid Hwrite. by eapply event_is_write_mono.
    Qed.

    Local Lemma po_rel_mono :
      rel_included (po_rel E1 rmw1) (po_rel E2 rmw2).
    Proof.
      unfold po_rel. apply rel_seq_mono.
      - apply rel_seq_mono.
        + apply rel_id_on_mono. intros eid Hmemory. by eapply event_is_memory_mono.
        + by apply po_mono.
      - apply rel_id_on_mono. apply release_mono.
    Qed.

    Local Lemma acq_po_mono :
      rel_included (acq_po E1 rmw1) (acq_po E2 rmw2).
    Proof.
      unfold acq_po. apply rel_seq_mono.
      - apply rel_seq_mono.
        + apply rel_id_on_mono. apply acquire_mono.
        + by apply po_mono.
      - apply rel_id_on_mono. intros eid Hmemory. by eapply event_is_memory_mono.
    Qed.

    Local Lemma gp_mono : rel_included (gp E1) (gp E2).
    Proof.
      unfold gp. apply rel_seq_mono.
      - apply rel_seq_mono; first by apply po_mono.
        apply rel_id_on_mono. intros eid Hbarrier.
        by eapply event_has_barrier_kind_mono.
      - apply optional_mono. by apply po_mono.
    Qed.

    Local Lemma mb_mono : rel_included (mb E1 rmw1) (mb E2 rmw2).
    Proof.
      unfold mb. apply rel_union_mono.
      {
        apply rel_seq_mono.
        - apply rel_seq_mono.
          + apply rel_id_on_mono. intros eid Hmemory. by eapply event_is_memory_mono.
          + apply fencerel_mono.
        - apply rel_id_on_mono. intros eid Hmemory. by eapply event_is_memory_mono.
      }
      apply rel_union_mono.
      {
        apply rel_seq_mono.
        - apply rel_seq_mono.
          + apply rel_id_on_mono. intros eid Hmemory. by eapply event_is_memory_mono.
          + by apply po_mono.
        - apply rel_intersection_mono.
          + apply rel_id_on_mono. apply mb_event_mono.
          + apply rel_id_on_mono. intros eid Hread. by eapply event_is_read_mono.
      }
      apply rel_union_mono.
      {
        apply rel_seq_mono.
        - apply rel_seq_mono.
          + apply rel_intersection_mono.
            * apply rel_id_on_mono. apply mb_event_mono.
            * apply rel_id_on_mono. intros eid Hwrite. by eapply event_is_write_mono.
          + by apply po_mono.
        - apply rel_id_on_mono. intros eid Hmemory. by eapply event_is_memory_mono.
      }
      apply rel_union_mono.
      {
        apply rel_seq_mono.
        {
          apply rel_seq_mono.
          {
            apply rel_seq_mono.
            {
              apply rel_seq_mono.
              - apply rel_id_on_mono. intros eid Hmemory.
                by eapply event_is_memory_mono.
              - apply fencerel_mono.
            }
            apply rel_id_on_mono. intros eid Hmarked.
            by eapply event_is_rmw_marked_mono.
          }
          apply optional_mono. by apply po_mono.
        }
        apply rel_id_on_mono. intros eid Hmemory. by eapply event_is_memory_mono.
      }
      apply rel_seq_mono.
      {
        apply rel_seq_mono.
        {
          apply rel_seq_mono.
          {
            apply rel_seq_mono.
            - apply rel_id_on_mono. intros eid Hmemory.
              by eapply event_is_memory_mono.
            - apply optional_mono. by apply po_mono.
          }
          apply rel_id_on_mono. intros eid Hmarked.
          by eapply event_is_rmw_marked_mono.
        }
        apply fencerel_mono.
      }
      apply rel_id_on_mono. intros eid Hmemory. by eapply event_is_memory_mono.
    Qed.

    Lemma strong_fence_mono :
      rel_included (strong_fence E1 rmw1) (strong_fence E2 rmw2).
    Proof. apply rel_union_mono; [apply mb_mono | apply gp_mono]. Qed.

    Local Lemma r4_rmb_mono :
      forall eid, r4_rmb E1 eid -> r4_rmb E2 eid.
    Proof.
      intros eid [Hread Hnot_noreturn]. split; first by eapply event_is_read_mono.
      destruct Hread as (read_event & Hlookup & Hread).
      assert (in_event_structure E1 eid) as Hin by eauto using lookup_event_in.
      intros [Hmode Hnot_write]. apply Hnot_noreturn. split.
      - by eapply event_has_access_mode_reflect.
      - intros Hwrite. apply Hnot_write. by eapply event_has_access_kind_mono.
    Qed.

    Local Lemma rmb_mono : rel_included (rmb E1) (rmb E2).
    Proof.
      unfold rmb. apply rel_seq_mono.
      - apply rel_seq_mono.
        + apply rel_id_on_mono. apply r4_rmb_mono.
        + apply fencerel_mono.
      - apply rel_id_on_mono. apply r4_rmb_mono.
    Qed.

    Lemma fence_mono :
      rel_included (fence E1 rmw1) (fence E2 rmw2).
    Proof.
      unfold fence, nonrw_fence. apply rel_union_mono.
      - apply rel_union_mono; first apply strong_fence_mono.
        apply rel_union_mono; [apply po_rel_mono | apply acq_po_mono].
      - apply rel_union_mono; [apply wmb_mono | apply rmb_mono].
    Qed.

    Local Lemma overwrite_mono :
      rel_included (overwrite rf1 co1) (overwrite rf2 co2).
    Proof.
      unfold overwrite, fr. apply rel_union_mono.
      - by apply edge_relation_mono.
      - apply rel_seq_mono.
        + apply rel_inverse_mono. by apply edge_relation_mono.
        + by apply edge_relation_mono.
    Qed.

    Local Lemma rmw_sequence_mono :
      rel_included (rmw_sequence rf1 rmw1) (rmw_sequence rf2 rmw2).
    Proof.
      apply rtc_mono, rel_seq_mono; by apply edge_relation_mono.
    Qed.

    Lemma rfe_mono eid1 eid2 :
      in_event_structure E1 eid1 -> in_event_structure E1 eid2 ->
      rfe E1 rf1 eid1 eid2 -> rfe E2 rf2 eid1 eid2.
    Proof.
      intros Hin1 Hin2 [Hrf Hext]. split.
      - by apply HRF.
      - by eapply ext_mono.
    Qed.

    Local Lemma a_cumul_mono_on (r1 r2 : relation) :
      rel_included r1 r2 ->
      forall eid1 eid2,
        in_event_structure E1 eid1 ->
        a_cumul E1 rf1 r1 eid1 eid2 -> a_cumul E2 rf2 r2 eid1 eid2.
    Proof.
      intros Hr eid1 eid2 Hin1 (middle & Hprefix & Hrelation).
      exists middle. split; last by apply Hr.
      destruct Hprefix as [-> | (target & Hrfe & [-> Hmarked])].
      - by left.
      - destruct Hmarked as [Hin_middle Hnot_plain].
        right. exists middle. split.
        + apply rfe_mono; done.
        + split; first done. apply marked_mono. by split.
    Qed.

    Local Lemma cumul_fence_mono :
      rel_included (cumul_fence E1 rmw1 rf1) (cumul_fence E2 rmw2 rf2).
    Proof.
      intros eid1 eid2 (middle & Hprefix & Hsequence). exists middle.
      split; last by apply rmw_sequence_mono.
      apply rel_seq_id_on_r in Hprefix as [Hfence Hmarked2].
      apply rel_seq_id_on_l in Hfence as [Hmarked1 Hfence].
      apply rel_seq_id_on_r. split; last by apply marked_mono.
      apply rel_seq_id_on_l. split; first by apply marked_mono.
      destruct Hfence as [Hcumul | Hwmb].
      - left. eapply a_cumul_mono_on; last done.
        + apply rel_union_mono; [apply strong_fence_mono | apply po_rel_mono].
        + destruct Hmarked1 as [Hin _]. done.
      - right. by apply wmb_mono.
    Qed.

    Local Lemma cumul_fence_source_marked eid1 eid2 :
      cumul_fence E1 rmw1 rf1 eid1 eid2 -> marked E1 eid1.
    Proof.
      intros (middle & Hprefix & _).
      apply rel_seq_id_on_r in Hprefix as [Hfence _].
      by apply rel_seq_id_on_l in Hfence as [Hmarked _].
    Qed.

    Local Lemma rtc_cumul_fence_source_marked eid1 eid2 :
      rtc (cumul_fence E1 rmw1 rf1) eid1 eid2 ->
      marked E1 eid2 -> marked E1 eid1.
    Proof.
      intros Hrtc. induction Hrtc.
      - intros _. by eapply cumul_fence_source_marked.
      - done.
      - intros Hmarked. apply IHHrtc1, IHHrtc2, Hmarked.
    Qed.

    Lemma prop_mono :
      rel_included (prop E1 rmw1 rf1 co1) (prop E2 rmw2 rf2 co2).
    Proof.
      intros source target Hprop.
      apply rel_seq_id_on_r in Hprop as [Hprop Hmarked_target].
      destruct Hprop as (after_cumul & Hbefore_rfe & Hrfe).
      apply rel_seq_id_on_r in Hbefore_rfe as [Hbefore_cumul Hmarked_after].
      destruct Hbefore_cumul as (before_cumul & Hbefore_overwrite & Hcumul).
      apply rel_seq_id_on_l in Hbefore_overwrite as [Hmarked_source Hoverwrite].
      assert (marked E1 before_cumul) as Hmarked_before.
      { by eapply rtc_cumul_fence_source_marked. }
      assert (in_event_structure E1 source) as Hin_source.
      { destruct Hmarked_source; done. }
      assert (in_event_structure E1 before_cumul) as Hin_before.
      { destruct Hmarked_before; done. }
      assert (in_event_structure E1 after_cumul) as Hin_after.
      { destruct Hmarked_after; done. }
      assert (in_event_structure E1 target) as Hin_target.
      { destruct Hmarked_target; done. }
      apply rel_seq_id_on_r. split; last by apply marked_mono.
      exists after_cumul. split.
      - apply rel_seq_id_on_r. split; last by apply marked_mono.
        exists before_cumul. split.
        + apply rel_seq_id_on_l. split; first by apply marked_mono.
          destruct Hoverwrite as [-> | [Hoverwrite Hext]].
          * by left.
          * right. split; first by apply overwrite_mono.
            by eapply ext_mono.
        + eapply rtc_mono; [apply cumul_fence_mono | done].
      - destruct Hrfe as [-> | Hrfe].
        + by left.
        + right. by apply rfe_mono.
    Qed.

  End PropMonotonicity.

  (** Linux v6.18: [hb = [Marked] ; (ppo | rfe | ((prop \ id) & int)) ; [Marked]]. *)
  Definition hb (E : event_structure)
      (rmw_edges rf_edges co_edges data_edges addr_edges ctrl_edges : edge_set) : relation :=
    rel_seq
      (rel_seq
        (rel_id_on (marked E))
        (rel_union
          (ppo E rmw_edges rf_edges co_edges data_edges addr_edges ctrl_edges)
          (rel_union
            (rfe E rf_edges)
            (rel_intersection
              (rel_difference (prop E rmw_edges rf_edges co_edges) rel_id)
              (same_agent E)))))
      (rel_id_on (marked E)).

  (** Linux v6.18: [acyclic hb as happens-before]. *)
  Definition happens_before (E : event_structure)
      (rmw_edges rf_edges co_edges data_edges addr_edges ctrl_edges : edge_set) : Prop :=
    rel_acyclic (hb E rmw_edges rf_edges co_edges data_edges addr_edges ctrl_edges).

  (** Linux v6.18: [pb = prop ; strong-fence ; hb* ; [Marked]]. *)
  Definition pb (E : event_structure)
      (rmw_edges rf_edges co_edges data_edges addr_edges ctrl_edges : edge_set) : relation :=
    rel_seq
      (rel_seq
        (rel_seq
          (prop E rmw_edges rf_edges co_edges)
          (strong_fence E rmw_edges))
        (rtc (hb E rmw_edges rf_edges co_edges data_edges addr_edges ctrl_edges)))
      (rel_id_on (marked E)).

  Section HbPbMonotonicity.
    Context (E1 E2 : event_structure).
    Context (rmw1 rmw2 rf1 rf2 co1 co2 data1 data2 addr1 addr2 ctrl1 ctrl2 : edge_set).
    Context (HE : event_structure_included E1 E2).
    Context (HRMW : rmw1 ⊆ rmw2) (HRF : rf1 ⊆ rf2) (HCO : co1 ⊆ co2).
    Context (HDATA : data1 ⊆ data2) (HADDR : addr1 ⊆ addr2) (HCTRL : ctrl1 ⊆ ctrl2).

    Local Lemma base_relation_mono edges1 edges2 :
      edges1 ⊆ edges2 -> rel_included (edge_relation edges1) (edge_relation edges2).
    Proof. intros Hedges source target Hedge. by apply Hedges. Qed.

    Local Lemma rfi_mono : rel_included (rfi E1 rf1) (rfi E2 rf2).
    Proof.
      intros source target [Hrf Hagent]. split; first by apply HRF.
      by eapply same_attribute_mono.
    Qed.

    Local Lemma carry_dep_mono :
      rel_included (carry_dep E1 rf1 data1) (carry_dep E2 rf2 data2).
    Proof.
      apply rtc_mono, rel_seq_mono; last apply rfi_mono.
      by apply base_relation_mono.
    Qed.

    Local Lemma addr_mono :
      rel_included (addr E1 rf1 data1 addr1) (addr E2 rf2 data2 addr2).
    Proof.
      apply rel_seq_mono; first apply carry_dep_mono.
      by apply base_relation_mono.
    Qed.

    Local Lemma data_mono :
      rel_included (data E1 rf1 data1) (data E2 rf2 data2).
    Proof.
      apply rel_seq_mono; first apply carry_dep_mono.
      by apply base_relation_mono.
    Qed.

    Local Lemma ctrl_mono :
      rel_included (ctrl E1 rf1 data1 ctrl1) (ctrl E2 rf2 data2 ctrl2).
    Proof.
      apply rel_seq_mono; first apply carry_dep_mono.
      by apply base_relation_mono.
    Qed.

    Local Lemma dep_mono :
      rel_included (dep E1 rf1 data1 addr1) (dep E2 rf2 data2 addr2).
    Proof. apply rel_union_mono; [apply addr_mono | apply data_mono]. Qed.

    Local Lemma plain_mono eid : plain E1 eid -> plain E2 eid.
    Proof.
      intros [Hmode Hnot_rmw].
      assert (in_event_structure E1 eid) as Hin.
      { apply event_has_access_mode_lookup in Hmode as (ev & Hlookup & _).
        by eapply lookup_event_in. }
      split; first by eapply event_has_access_mode_mono.
      intros Hrmw. apply Hnot_rmw. by eapply event_is_rmw_marked_reflect.
    Qed.

    Local Lemma rwdep_mono :
      rel_included (rwdep E1 rf1 data1 addr1 ctrl1)
        (rwdep E2 rf2 data2 addr2 ctrl2).
    Proof.
      apply rel_seq_mono.
      - apply rel_union_mono; [apply dep_mono | apply ctrl_mono].
      - apply rel_id_on_mono. intros eid Hwrite. by eapply event_is_write_mono.
    Qed.

    Local Lemma overwrite_all_mono :
      rel_included (overwrite rf1 co1) (overwrite rf2 co2).
    Proof.
      unfold overwrite, fr. apply rel_union_mono.
      - by apply base_relation_mono.
      - apply rel_seq_mono.
        + apply rel_inverse_mono. by apply base_relation_mono.
        + by apply base_relation_mono.
    Qed.

    Local Lemma to_w_mono :
      rel_included (to_w E1 rf1 co1 data1 addr1 ctrl1)
        (to_w E2 rf2 co2 data2 addr2 ctrl2).
    Proof.
      unfold to_w. apply rel_union_mono; first apply rwdep_mono.
      apply rel_union_mono.
      - apply rel_intersection_mono; first apply overwrite_all_mono.
        by apply same_attribute_mono.
      - apply rel_seq_mono; last by apply wmb_mono.
        apply rel_seq_mono; first apply addr_mono.
        apply rel_id_on_mono. apply plain_mono.
    Qed.

    Local Lemma to_r_mono :
      rel_included (to_r E1 rf1 data1 addr1) (to_r E2 rf2 data2 addr2).
    Proof.
      unfold to_r. apply rel_union_mono.
      - apply rel_seq_mono; first apply addr_mono.
        apply rel_id_on_mono. intros eid Hread. by eapply event_is_read_mono.
      - apply rel_seq_mono; last apply rfi_mono.
        apply rel_seq_mono; first apply dep_mono.
        apply rel_id_on_mono. intros eid Hmarked. by eapply marked_mono.
    Qed.

    Local Lemma ppo_mono :
      rel_included (ppo E1 rmw1 rf1 co1 data1 addr1 ctrl1)
        (ppo E2 rmw2 rf2 co2 data2 addr2 ctrl2).
    Proof.
      unfold ppo. apply rel_union_mono; first apply to_r_mono.
      apply rel_union_mono; first apply to_w_mono.
      apply rel_intersection_mono; first by apply fence_mono.
      by apply same_attribute_mono.
    Qed.

    Lemma hb_mono :
      rel_included (hb E1 rmw1 rf1 co1 data1 addr1 ctrl1)
        (hb E2 rmw2 rf2 co2 data2 addr2 ctrl2).
    Proof.
      intros source target Hhb.
      apply rel_seq_id_on_r in Hhb as [Hbody Hmarked_target].
      apply rel_seq_id_on_l in Hbody as [Hmarked_source Hbody].
      assert (in_event_structure E1 source) as Hin_source.
      { by destruct Hmarked_source. }
      assert (in_event_structure E1 target) as Hin_target.
      { by destruct Hmarked_target. }
      apply rel_seq_id_on_r. split; last by eapply marked_mono.
      apply rel_seq_id_on_l. split; first by eapply marked_mono.
      destruct Hbody as [Hppo | [Hrfe | Hprop]].
      - left. by apply ppo_mono.
      - right. left. by eapply rfe_mono.
      - right. right. destruct Hprop as [[Hprop Hnot_id] Hagent]. split.
        + split; [by eapply prop_mono | done].
        + by eapply same_attribute_mono.
    Qed.

    Lemma pb_mono :
      rel_included (pb E1 rmw1 rf1 co1 data1 addr1 ctrl1)
        (pb E2 rmw2 rf2 co2 data2 addr2 ctrl2).
    Proof.
      unfold pb. apply rel_seq_mono.
      {
        apply rel_seq_mono.
        - apply rel_seq_mono.
          + by eapply prop_mono.
          + by apply strong_fence_mono.
        - apply rtc_mono. apply hb_mono.
      }
      apply rel_id_on_mono. intros eid Hmarked. by eapply marked_mono.
    Qed.

  End HbPbMonotonicity.

  (** Linux v6.18: [acyclic pb as propagation]. *)
  Definition propagation (E : event_structure)
      (rmw_edges rf_edges co_edges data_edges addr_edges ctrl_edges : edge_set) : Prop :=
    rel_acyclic (pb E rmw_edges rf_edges co_edges data_edges addr_edges ctrl_edges).

  (** Linux v6.18: [com = rf | co | fr]. *)
  Definition com (rf_edges co_edges : edge_set) : relation :=
    rel_union (rf rf_edges) (rel_union (co co_edges) (fr rf_edges co_edges)).

  (** Linux v6.18: [acyclic (po-loc | com) as coherence].  Candidate
      well-formedness remains separate from this consistency constraint. *)
  Definition coherence (E : event_structure) (rf_edges co_edges : edge_set) : Prop :=
    rel_acyclic (rel_union (po_loc E) (com rf_edges co_edges)).

  (** Linux v6.18: [empty (rmw & (fre ; coe)) as atomic]. *)
  Definition atomicity (E : event_structure) (rmw_edges rf_edges co_edges : edge_set) : Prop :=
    rel_is_empty
      (rel_intersection (rmw rmw_edges) (rel_seq (fre E rf_edges co_edges) (coe E co_edges))).

  Definition direct_addr_edge_wf (E : event_structure) (read access : event_id) : Prop :=
    event_is_read E read /\
    event_is_memory E access /\
    po E read access.

  Definition direct_data_edge_wf (E : event_structure) (read write : event_id) : Prop :=
    event_is_read E read /\
    event_is_write E write /\
    po E read write.

  Definition direct_ctrl_edge_wf (E : event_structure) (read write : event_id) : Prop :=
    event_is_read E read /\
    event_is_write E write /\
    po E read write.

  Definition direct_addr_wf (E : event_structure) (edges : edge_set) : Prop :=
    forall read access,
      direct_addr edges read access -> direct_addr_edge_wf E read access.

  Definition direct_data_wf (E : event_structure) (edges : edge_set) : Prop :=
    forall read write,
      direct_data edges read write -> direct_data_edge_wf E read write.

  Definition direct_ctrl_wf (E : event_structure) (edges : edge_set) : Prop :=
    forall read write,
      direct_ctrl edges read write -> direct_ctrl_edge_wf E read write.

  Lemma direct_addr_wf_edge E edges read access :
    direct_addr_wf E edges ->
    direct_addr edges read access -> direct_addr_edge_wf E read access.
  Proof. intros Hedges Haddr. by eapply Hedges. Qed.

  Lemma direct_data_wf_edge E edges read write :
    direct_data_wf E edges ->
    direct_data edges read write -> direct_data_edge_wf E read write.
  Proof. intros Hedges Hdata. by eapply Hedges. Qed.

  Lemma direct_ctrl_wf_edge E edges read write :
    direct_ctrl_wf E edges ->
    direct_ctrl edges read write -> direct_ctrl_edge_wf E read write.
  Proof. intros Hedges Hctrl. by eapply Hedges. Qed.

  Lemma direct_addr_empty_wf E : direct_addr_wf E ∅.
  Proof. intros read access Hedge. set_solver. Qed.

  Lemma direct_data_empty_wf E : direct_data_wf E ∅.
  Proof. intros read write Hedge. set_solver. Qed.

  Lemma direct_ctrl_empty_wf E : direct_ctrl_wf E ∅.
  Proof. intros read write Hedge. set_solver. Qed.

  Lemma direct_addr_wf_subset E edges1 edges2 :
    edges1 ⊆ edges2 -> direct_addr_wf E edges2 -> direct_addr_wf E edges1.
  Proof. intros Hin Hwf read access Hedge. apply Hwf, Hin, Hedge. Qed.

  Lemma direct_data_wf_subset E edges1 edges2 :
    edges1 ⊆ edges2 -> direct_data_wf E edges2 -> direct_data_wf E edges1.
  Proof. intros Hin Hwf read write Hedge. apply Hwf, Hin, Hedge. Qed.

  Lemma direct_ctrl_wf_subset E edges1 edges2 :
    edges1 ⊆ edges2 -> direct_ctrl_wf E edges2 -> direct_ctrl_wf E edges1.
  Proof. intros Hin Hwf read write Hedge. apply Hwf, Hin, Hedge. Qed.

  Lemma direct_addr_wf_mono E1 E2 edges :
    event_structure_included E1 E2 -> direct_addr_wf E1 edges -> direct_addr_wf E2 edges.
  Proof.
    intros HE Hwf read access Hedge.
    destruct (Hwf read access Hedge) as (Hread & Hmemory & Hpo). split_and!.
    - by eapply event_is_read_mono.
    - by eapply event_is_memory_mono.
    - by eapply po_mono.
  Qed.

  Lemma direct_data_wf_mono E1 E2 edges :
    event_structure_included E1 E2 -> direct_data_wf E1 edges -> direct_data_wf E2 edges.
  Proof.
    intros HE Hwf read write Hedge.
    destruct (Hwf read write Hedge) as (Hread & Hwrite & Hpo). split_and!.
    - by eapply event_is_read_mono.
    - by eapply event_is_write_mono.
    - by eapply po_mono.
  Qed.

  Lemma direct_ctrl_wf_mono E1 E2 edges :
    event_structure_included E1 E2 -> direct_ctrl_wf E1 edges -> direct_ctrl_wf E2 edges.
  Proof.
    intros HE Hwf read write Hedge.
    destruct (Hwf read write Hedge) as (Hread & Hwrite & Hpo). split_and!.
    - by eapply event_is_read_mono.
    - by eapply event_is_write_mono.
    - by eapply po_mono.
  Qed.

  Definition rf_edge_wf (E : event_structure) (write read : event_id) : Prop :=
    exists write_event read_event val,
      lookup_event E write = Some write_event /\
      lookup_event E read = Some read_event /\
      is_write write_event /\ is_read read_event /\
      same_location E write read /\
      value_of write_event = Some val /\
      value_of read_event = Some val.

  Definition rf_functional (edges : edge_set) : Prop :=
    forall write1 write2 read, rf edges write1 read -> rf edges write2 read -> write1 = write2.

  Definition rf_total (E : event_structure) (edges : edge_set) : Prop :=
    forall read read_event,
      lookup_event E read = Some read_event ->
      is_read read_event ->
      exists write, rf edges write read.

  Definition rf_wf (E : event_structure) (edges : edge_set) : Prop :=
    (forall write read, rf edges write read -> rf_edge_wf E write read) /\
    rf_functional edges /\
    rf_total E edges.

  (** Structural obligations preserved by an incrementally constructed
      prefix of [rf].  Totality is meaningful only for a completed
      candidate and therefore remains in [rf_wf]. *)
  Definition rf_prefix_wf (E : event_structure) (edges : edge_set) : Prop :=
    (forall write read, rf edges write read -> rf_edge_wf E write read) /\
    rf_functional edges.

  Lemma rf_empty_prefix_wf E :
    rf_prefix_wf E ∅.
  Proof.
    unfold rf_prefix_wf, rf_functional, rf, edge_relation. split; set_solver.
  Qed.

  Lemma rf_wf_prefix E edges :
    rf_wf E edges -> rf_prefix_wf E edges.
  Proof. intros (Hedges & Hfunctional & _). split; done. Qed.

  Lemma rf_prefix_wf_subset E edges1 edges2 :
    edges1 ⊆ edges2 -> rf_prefix_wf E edges2 -> rf_prefix_wf E edges1.
  Proof.
    intros Hsubset [Hedges Hfunctional]. split.
    - intros write read Hrf. apply Hedges, Hsubset, Hrf.
    - intros write1 write2 read Hrf1 Hrf2.
      eapply Hfunctional; [apply Hsubset, Hrf1 | apply Hsubset, Hrf2].
  Qed.

  Lemma rf_prefix_wf_mono E1 E2 edges :
    event_structure_included E1 E2 ->
    rf_prefix_wf E1 edges -> rf_prefix_wf E2 edges.
  Proof.
    intros HE [Hedges Hfunctional]. split; last done.
    intros write read Hrf.
    destruct (Hedges write read Hrf) as
      (write_event & read_event & val & Hwrite & Hread & Hwrite_kind &
        Hread_kind & Hlocation & Hwrite_value & Hread_value).
    exists write_event, read_event, val. split_and!; try done.
    - by eapply HE.
    - by eapply HE.
    - by eapply same_attribute_mono.
  Qed.

  Lemma rf_wf_edge E edges write read :
    rf_wf E edges -> rf edges write read -> rf_edge_wf E write read.
  Proof. intros (Hedges & _ & _) Hrf. by eapply Hedges. Qed.

  Lemma rf_wf_functional E edges :
    rf_wf E edges -> rf_functional edges.
  Proof. intros (_ & Hfunctional & _). exact Hfunctional. Qed.

  Lemma rf_wf_total E edges :
    rf_wf E edges -> rf_total E edges.
  Proof. intros (_ & _ & Htotal). exact Htotal. Qed.

  Lemma rf_wf_endpoints E edges write read :
    rf_wf E edges -> rf edges write read ->
    in_event_structure E write /\ in_event_structure E read.
  Proof.
    intros Hwf Hrf.
    destruct (rf_wf_edge E edges write read Hwf Hrf)
      as (write_event & read_event & val &
        Hwrite & Hread & Hwrite_kind & Hread_kind &
        Hsame_loc & Hwrite_val & Hread_val).
    split; eapply lookup_event_in; eauto.
  Qed.

  Lemma rf_wf_same_location E edges write read :
    rf_wf E edges -> rf edges write read ->
    same_location E write read.
  Proof.
    intros Hwf Hrf.
    destruct (rf_wf_edge E edges write read Hwf Hrf)
      as (write_event & read_event & val &
        Hwrite & Hread & Hwrite_kind & Hread_kind &
        Hsame_loc & Hwrite_val & Hread_val).
    exact Hsame_loc.
  Qed.

  Lemma rf_wf_same_value E edges write read :
    rf_wf E edges -> rf edges write read ->
    exists write_event read_event val,
      lookup_event E write = Some write_event /\
      lookup_event E read = Some read_event /\
      value_of write_event = Some val /\
      value_of read_event = Some val.
  Proof.
    intros Hwf Hrf.
    destruct (rf_wf_edge E edges write read Hwf Hrf)
      as (write_event & read_event & val &
        Hwrite & Hread & Hwrite_kind & Hread_kind &
        Hsame_loc & Hwrite_val & Hread_val).
    exists write_event, read_event, val. done.
  Qed.

  Definition rmw_edge_wf (E : event_structure) (read write : event_id) : Prop :=
    exists read_event write_event,
      lookup_event E read = Some read_event /\
      lookup_event E write = Some write_event /\
      is_read read_event /\ is_write write_event /\
      is_rmw_marked read_event /\ is_rmw_marked write_event /\
      po E read write /\
      same_location E read write /\
      same_attribute access_mode_of E read write.

  Definition rmw_functional (edges : edge_set) : Prop :=
    forall read write1 write2,
      rmw edges read write1 -> rmw edges read write2 -> write1 = write2.

  Definition rmw_injective (edges : edge_set) : Prop :=
    forall read1 read2 write,
      rmw edges read1 write -> rmw edges read2 write -> read1 = read2.

  (** Every marked write is the write half of a successful RMW.  Marked
      reads are intentionally not total because a failed conditional RMW
      has no write half. *)
  Definition rmw_write_total (E : event_structure) (edges : edge_set) : Prop :=
    forall write write_event,
      lookup_event E write = Some write_event ->
      is_write write_event -> is_rmw_marked write_event ->
      exists read, rmw edges read write.

  Definition rmw_wf (E : event_structure) (edges : edge_set) : Prop :=
    (forall read write, rmw edges read write -> rmw_edge_wf E read write) /\
    rmw_functional edges /\
    rmw_injective edges /\
    rmw_write_total E edges.

  (** Structural obligations preserved by an incrementally constructed
      prefix of [rmw].  Marked-write totality remains a completion property. *)
  Definition rmw_prefix_wf (E : event_structure) (edges : edge_set) : Prop :=
    (forall read write, rmw edges read write -> rmw_edge_wf E read write) /\
    rmw_functional edges /\
    rmw_injective edges.

  Lemma rmw_empty_prefix_wf E :
    rmw_prefix_wf E ∅.
  Proof.
    unfold rmw_prefix_wf, rmw_functional, rmw_injective, rmw, edge_relation.
    split_and!; set_solver.
  Qed.

  Lemma rmw_wf_prefix E edges :
    rmw_wf E edges -> rmw_prefix_wf E edges.
  Proof. intros (Hedges & Hfunctional & Hinjective & _). split_and!; done. Qed.

  Lemma rmw_prefix_wf_subset E edges1 edges2 :
    edges1 ⊆ edges2 -> rmw_prefix_wf E edges2 -> rmw_prefix_wf E edges1.
  Proof.
    intros Hsubset (Hedges & Hfunctional & Hinjective). split_and!.
    - intros read write Hrmw. apply Hedges, Hsubset, Hrmw.
    - intros read write1 write2 Hrmw1 Hrmw2.
      eapply Hfunctional; [apply Hsubset, Hrmw1 | apply Hsubset, Hrmw2].
    - intros read1 read2 write Hrmw1 Hrmw2.
      eapply Hinjective; [apply Hsubset, Hrmw1 | apply Hsubset, Hrmw2].
  Qed.

  Lemma rmw_prefix_wf_mono E1 E2 edges :
    event_structure_included E1 E2 ->
    rmw_prefix_wf E1 edges -> rmw_prefix_wf E2 edges.
  Proof.
    intros HE (Hedges & Hfunctional & Hinjective). split_and!; try done.
    intros read write Hrmw.
    destruct (Hedges read write Hrmw) as
      (read_event & write_event & Hread & Hwrite & Hread_kind & Hwrite_kind &
        Hread_marked & Hwrite_marked & Hpo & Hlocation & Hmode).
    exists read_event, write_event. split_and!; try done.
    - by eapply HE.
    - by eapply HE.
    - by eapply po_mono.
    - by eapply same_attribute_mono.
    - by eapply same_attribute_mono.
  Qed.

  Lemma rmw_wf_edge E edges read write :
    rmw_wf E edges -> rmw edges read write -> rmw_edge_wf E read write.
  Proof. intros (Hedges & _ & _ & _) Hrmw. by eapply Hedges. Qed.

  Lemma rmw_wf_functional E edges :
    rmw_wf E edges -> rmw_functional edges.
  Proof. intros (_ & Hfunctional & _ & _). exact Hfunctional. Qed.

  Lemma rmw_wf_injective E edges :
    rmw_wf E edges -> rmw_injective edges.
  Proof. intros (_ & _ & Hinjective & _). exact Hinjective. Qed.

  Lemma rmw_wf_write_total E edges :
    rmw_wf E edges -> rmw_write_total E edges.
  Proof. intros (_ & _ & _ & Htotal). exact Htotal. Qed.

  Lemma rmw_wf_endpoints E edges read write :
    rmw_wf E edges -> rmw edges read write ->
    in_event_structure E read /\ in_event_structure E write.
  Proof.
    intros Hwf Hrmw.
    destruct (rmw_wf_edge E edges read write Hwf Hrmw)
      as (read_event & write_event & Hread & Hwrite &
        Hread_kind & Hwrite_kind & Hread_marked & Hwrite_marked &
        Hpo & Hsame_loc & Hsame_mode).
    by eapply po_endpoints.
  Qed.

  Lemma rmw_wf_kinds E edges read write :
    rmw_wf E edges -> rmw edges read write ->
    exists read_event write_event,
      lookup_event E read = Some read_event /\
      lookup_event E write = Some write_event /\
      is_read read_event /\ is_write write_event.
  Proof.
    intros Hwf Hrmw.
    destruct (rmw_wf_edge E edges read write Hwf Hrmw)
      as (read_event & write_event & Hread & Hwrite &
        Hread_kind & Hwrite_kind & Hread_marked & Hwrite_marked &
        Hpo & Hsame_loc & Hsame_mode).
    exists read_event, write_event. done.
  Qed.

  Lemma rmw_wf_marked E edges read write :
    rmw_wf E edges -> rmw edges read write ->
    exists read_event write_event,
      lookup_event E read = Some read_event /\
      lookup_event E write = Some write_event /\
      is_rmw_marked read_event /\ is_rmw_marked write_event.
  Proof.
    intros Hwf Hrmw.
    destruct (rmw_wf_edge E edges read write Hwf Hrmw)
      as (read_event & write_event & Hread & Hwrite &
        Hread_kind & Hwrite_kind & Hread_marked & Hwrite_marked &
        Hpo & Hsame_loc & Hsame_mode).
    exists read_event, write_event. done.
  Qed.

  Lemma rmw_wf_po E edges read write :
    rmw_wf E edges -> rmw edges read write -> po E read write.
  Proof.
    intros Hwf Hrmw.
    destruct (rmw_wf_edge E edges read write Hwf Hrmw)
      as (read_event & write_event & Hread & Hwrite &
        Hread_kind & Hwrite_kind & Hread_marked & Hwrite_marked &
        Hpo & Hsame_loc & Hsame_mode).
    exact Hpo.
  Qed.

  Lemma rmw_wf_same_agent E edges read write :
    rmw_wf E edges -> rmw edges read write -> same_agent E read write.
  Proof.
    intros Hwf Hrmw. apply po_same_agent.
    by eapply rmw_wf_po.
  Qed.

  Lemma rmw_wf_same_location E edges read write :
    rmw_wf E edges -> rmw edges read write ->
    same_location E read write.
  Proof.
    intros Hwf Hrmw.
    destruct (rmw_wf_edge E edges read write Hwf Hrmw)
      as (read_event & write_event & Hread & Hwrite &
        Hread_kind & Hwrite_kind & Hread_marked & Hwrite_marked &
        Hpo & Hsame_loc & Hsame_mode).
    exact Hsame_loc.
  Qed.

  Lemma rmw_wf_same_mode E edges read write :
    rmw_wf E edges -> rmw edges read write ->
    same_attribute access_mode_of E read write.
  Proof.
    intros Hwf Hrmw.
    destruct (rmw_wf_edge E edges read write Hwf Hrmw)
      as (read_event & write_event & Hread & Hwrite &
        Hread_kind & Hwrite_kind & Hread_marked & Hwrite_marked &
        Hpo & Hsame_loc & Hsame_mode).
    exact Hsame_mode.
  Qed.

  Definition location_used (E : event_structure) (loc : location) : Prop :=
    exists eid, event_has_location E loc eid.

  Definition initial_write_at (E : event_structure) (loc : location) (write : event_id) : Prop :=
    exists val, lookup_event E write = Some (EInitWrite loc val).

  Definition initial_writes_exist (E : event_structure) : Prop :=
    forall loc, location_used E loc ->
      exists write, initial_write_at E loc write.

  Definition initial_writes_unique (E : event_structure) : Prop :=
    forall loc write1 write2,
      initial_write_at E loc write1 ->
      initial_write_at E loc write2 ->
      write1 = write2.

  Definition co_edge_wf (E : event_structure) (write1 write2 : event_id) : Prop :=
    exists write_event1 write_event2,
      lookup_event E write1 = Some write_event1 /\
      lookup_event E write2 = Some write_event2 /\
      is_write write_event1 /\ is_write write_event2 /\
      same_location E write1 write2.

  Definition fr_edge_wf (E : event_structure) (read write : event_id) : Prop :=
    exists read_event write_event,
      lookup_event E read = Some read_event /\
      lookup_event E write = Some write_event /\
      is_read read_event /\ is_write write_event /\
      same_location E read write.

  Definition co_irreflexive (edges : edge_set) : Prop := forall write, ~ co edges write write.

  Definition co_transitive (edges : edge_set) : Prop :=
    forall write1 write2 write3,
      co edges write1 write2 -> co edges write2 write3 ->
      co edges write1 write3.

  Definition co_total (E : event_structure) (edges : edge_set) : Prop :=
    forall write1 write2 write_event1 write_event2,
      lookup_event E write1 = Some write_event1 ->
      lookup_event E write2 = Some write_event2 ->
      is_write write_event1 -> is_write write_event2 ->
      same_location E write1 write2 ->
      write1 <> write2 ->
      co edges write1 write2 \/ co edges write2 write1.

  Definition co_initial_first (E : event_structure) (edges : edge_set) : Prop :=
    forall initial write loc write_event,
      initial_write_at E loc initial ->
      lookup_event E write = Some write_event ->
      is_write write_event ->
      same_location E initial write ->
      initial <> write ->
      co edges initial write.

  Definition co_wf (E : event_structure) (edges : edge_set) : Prop :=
    (forall write1 write2, co edges write1 write2 -> co_edge_wf E write1 write2) /\
      co_irreflexive edges /\
      co_transitive edges /\
      co_total E edges /\
      initial_writes_exist E /\
      initial_writes_unique E /\
      co_initial_first E edges.

  (** A coherence prefix need not yet be transitive or total.  Acyclicity is
      hereditary under edge removal and prevents an incremental builder from
      committing a cycle that no completed coherence order can repair. *)
  Definition co_prefix_wf (E : event_structure) (edges : edge_set) : Prop :=
    (forall write1 write2, co edges write1 write2 -> co_edge_wf E write1 write2) /\
    rel_acyclic (co edges).

  Lemma co_empty_prefix_wf E :
    co_prefix_wf E ∅.
  Proof.
    unfold co_prefix_wf, rel_acyclic, rel_irreflexive, co, edge_relation. split.
    - set_solver.
    - intros write Hcycle. induction Hcycle; set_solver.
  Qed.

  Lemma co_wf_prefix E edges :
    co_wf E edges -> co_prefix_wf E edges.
  Proof.
    intros (Hedges & Hirreflexive & Htransitive & _). split; first done.
    assert (forall source target, tc (co edges) source target -> co edges source target) as Htc.
    { intros source target Hpath. induction Hpath; first done.
      by eapply Htransitive. }
    intros write Hcycle. apply (Hirreflexive write), Htc, Hcycle.
  Qed.

  Lemma co_prefix_wf_subset E edges1 edges2 :
    edges1 ⊆ edges2 -> co_prefix_wf E edges2 -> co_prefix_wf E edges1.
  Proof.
    intros Hsubset [Hedges Hacyclic]. split.
    - intros write1 write2 Hco. apply Hedges, Hsubset, Hco.
    - intros write Hcycle. apply (Hacyclic write).
      eapply tc_mono; last exact Hcycle.
      intros source target Hco. by apply Hsubset.
  Qed.

  Lemma co_prefix_wf_mono E1 E2 edges :
    event_structure_included E1 E2 ->
    co_prefix_wf E1 edges -> co_prefix_wf E2 edges.
  Proof.
    intros HE [Hedges Hacyclic]. split; last done.
    intros write1 write2 Hco.
    destruct (Hedges write1 write2 Hco) as
      (write_event1 & write_event2 & Hwrite1 & Hwrite2 & Hkind1 & Hkind2 & Hlocation).
    exists write_event1, write_event2. split_and!; try done.
    - by eapply HE.
    - by eapply HE.
    - by eapply same_attribute_mono.
  Qed.

  Lemma co_wf_edge E edges write1 write2 :
    co_wf E edges -> co edges write1 write2 ->
    co_edge_wf E write1 write2.
  Proof. intros (Hedges & _ & _ & _ & _ & _ & _) Hco. by eapply Hedges. Qed.

  Lemma co_wf_irreflexive E edges :
    co_wf E edges -> co_irreflexive edges.
  Proof. intros (_ & Hirreflexive & _ & _ & _ & _ & _). exact Hirreflexive. Qed.

  Lemma co_wf_transitive E edges :
    co_wf E edges -> co_transitive edges.
  Proof. intros (_ & _ & Htransitive & _ & _ & _ & _). exact Htransitive. Qed.

  Lemma co_wf_total E edges :
    co_wf E edges -> co_total E edges.
  Proof. intros (_ & _ & _ & Htotal & _ & _ & _). exact Htotal. Qed.

  Lemma co_wf_initial_exists E edges :
    co_wf E edges -> initial_writes_exist E.
  Proof. intros (_ & _ & _ & _ & Hexists & _ & _). exact Hexists. Qed.

  Lemma co_wf_initial_unique E edges :
    co_wf E edges -> initial_writes_unique E.
  Proof. intros (_ & _ & _ & _ & _ & Hunique & _). exact Hunique. Qed.

  Lemma co_wf_initial_first E edges :
    co_wf E edges -> co_initial_first E edges.
  Proof. intros (_ & _ & _ & _ & _ & _ & Hfirst). exact Hfirst. Qed.

  Lemma co_wf_endpoints E edges write1 write2 :
    co_wf E edges -> co edges write1 write2 ->
    in_event_structure E write1 /\ in_event_structure E write2.
  Proof.
    intros Hwf Hco.
    destruct (co_wf_edge E edges write1 write2 Hwf Hco)
      as (write_event1 & write_event2 &
        Hwrite1 & Hwrite2 & Hkind1 & Hkind2 & Hsame_loc).
    split; eapply lookup_event_in; eauto.
  Qed.

  Lemma co_wf_same_location E edges write1 write2 :
    co_wf E edges -> co edges write1 write2 ->
    same_location E write1 write2.
  Proof.
    intros Hwf Hco.
    destruct (co_wf_edge E edges write1 write2 Hwf Hco)
      as (write_event1 & write_event2 &
        Hwrite1 & Hwrite2 & Hkind1 & Hkind2 & Hsame_loc).
    exact Hsame_loc.
  Qed.

  Lemma fr_wf_edge E rf_edges co_edges read write :
    rf_wf E rf_edges -> co_wf E co_edges ->
    fr rf_edges co_edges read write -> fr_edge_wf E read write.
  Proof.
    intros Hrf_wf Hco_wf Hfr.
    unfold fr, rel_seq in Hfr.
    destruct Hfr as (source & Hrf & Hco).
    unfold rel_inverse in Hrf.
    destruct (rf_wf_edge E rf_edges source read Hrf_wf Hrf)
      as (source_event & read_event & val &
        Hsource & Hread & Hsource_kind & Hread_kind &
        Hsource_read_loc & Hsource_val & Hread_val).
    destruct (co_wf_edge E co_edges source write Hco_wf Hco)
      as (source_event' & write_event &
        Hsource' & Hwrite & Hsource_kind' & Hwrite_kind &
        Hsource_write_loc).
    exists read_event, write_event.
    split_and!; try done.
    eapply same_location_transitive.
    - by apply same_location_symmetric.
    - exact Hsource_write_loc.
  Qed.

  Lemma fr_wf_endpoints E rf_edges co_edges read write :
    rf_wf E rf_edges -> co_wf E co_edges ->
    fr rf_edges co_edges read write ->
    in_event_structure E read /\ in_event_structure E write.
  Proof.
    intros Hrf_wf Hco_wf Hfr.
    destruct (fr_wf_edge E rf_edges co_edges read write
      Hrf_wf Hco_wf Hfr)
      as (read_event & write_event &
        Hread & Hwrite & Hread_kind & Hwrite_kind & Hsame_loc).
    split; eapply lookup_event_in; eauto.
  Qed.

  Lemma fr_wf_kinds E rf_edges co_edges read write :
    rf_wf E rf_edges -> co_wf E co_edges ->
    fr rf_edges co_edges read write ->
    exists read_event write_event,
      lookup_event E read = Some read_event /\
      lookup_event E write = Some write_event /\
      is_read read_event /\ is_write write_event.
  Proof.
    intros Hrf_wf Hco_wf Hfr.
    destruct (fr_wf_edge E rf_edges co_edges read write
      Hrf_wf Hco_wf Hfr)
      as (read_event & write_event &
        Hread & Hwrite & Hread_kind & Hwrite_kind & Hsame_loc).
    exists read_event, write_event. done.
  Qed.

  Lemma fr_wf_same_location E rf_edges co_edges read write :
    rf_wf E rf_edges -> co_wf E co_edges ->
    fr rf_edges co_edges read write ->
    same_location E read write.
  Proof.
    intros Hrf_wf Hco_wf Hfr.
    destruct (fr_wf_edge E rf_edges co_edges read write
      Hrf_wf Hco_wf Hfr)
      as (read_event & write_event &
        Hread & Hwrite & Hread_kind & Hwrite_kind & Hsame_loc).
    exact Hsame_loc.
  Qed.

  Module DependencyTests.
    Definition source_read : event := EAgent 0 0 (LMemory AccessRead AccessOnce NotRmw 0 0%Z).
    Definition relay_write : event := EAgent 0 1 (LMemory AccessWrite AccessOnce NotRmw 0 1%Z).
    Definition relay_read : event := EAgent 0 2 (LMemory AccessRead AccessOnce NotRmw 0 1%Z).
    Definition addr_target : event := EAgent 0 3 (LMemory AccessRead AccessPlain NotRmw 1 0%Z).
    Definition data_target : event := EAgent 0 4 (LMemory AccessWrite AccessOnce NotRmw 1 1%Z).
    Definition ctrl_target : event := EAgent 0 5 (LMemory AccessWrite AccessOnce NotRmw 2 1%Z).

    Definition sample_events : event_structure := {[
      0 := source_read;
      1 := relay_write;
      2 := relay_read;
      3 := addr_target;
      4 := data_target;
      5 := ctrl_target
    ]}.
    Definition sample_rf : edge_set := {[(1, 2)]}.
    Definition sample_addr : edge_set := {[(2, 3)]}.
    Definition sample_data : edge_set := {[(0, 1); (2, 4)]}.
    Definition sample_ctrl : edge_set := {[(2, 5)]}.

    Local Lemma sample_addr_wf : direct_addr_wf sample_events sample_addr.
    Proof.
      intros read access Haddr.
      unfold direct_addr, edge_relation, sample_addr in Haddr.
      assert (read = 2 /\ access = 3) as [-> ->] by set_solver.
      split_and!.
      - exists relay_read. split; reflexivity.
      - exists addr_target. split; done.
      - exists 0, 2, 3,
          (LMemory AccessRead AccessOnce NotRmw 0 1%Z),
          (LMemory AccessRead AccessPlain NotRmw 1 0%Z).
        split_and!; reflexivity || lia.
    Qed.

    Local Lemma sample_data_wf : direct_data_wf sample_events sample_data.
    Proof.
      intros read write Hdata.
      unfold direct_data, edge_relation, sample_data in Hdata.
      assert ((read = 0 /\ write = 1) \/ (read = 2 /\ write = 4))
        as [[-> ->] | [-> ->]] by set_solver.
      - split_and!.
        + exists source_read. split; reflexivity.
        + exists relay_write. split; reflexivity.
        + exists 0, 0, 1,
          (LMemory AccessRead AccessOnce NotRmw 0 0%Z),
          (LMemory AccessWrite AccessOnce NotRmw 0 1%Z).
          split_and!; reflexivity || lia.
      - split_and!.
        + exists relay_read. split; reflexivity.
        + exists data_target. split; reflexivity.
        + exists 0, 2, 4,
          (LMemory AccessRead AccessOnce NotRmw 0 1%Z),
          (LMemory AccessWrite AccessOnce NotRmw 1 1%Z).
          split_and!; reflexivity || lia.
    Qed.

    Local Lemma sample_ctrl_wf : direct_ctrl_wf sample_events sample_ctrl.
    Proof.
      intros read write Hctrl.
      unfold direct_ctrl, edge_relation, sample_ctrl in Hctrl.
      assert (read = 2 /\ write = 5) as [-> ->] by set_solver.
      split_and!.
      - exists relay_read. split; reflexivity.
      - exists ctrl_target. split; reflexivity.
      - exists 0, 2, 5,
          (LMemory AccessRead AccessOnce NotRmw 0 1%Z),
          (LMemory AccessWrite AccessOnce NotRmw 2 1%Z).
        split_and!; reflexivity || lia.
    Qed.

    Local Lemma sample_carrier : carry_dep sample_events sample_rf sample_data 0 2.
    Proof.
      apply rt_step. exists 1. split.
      - unfold direct_data, edge_relation, sample_data. set_solver.
      - split.
        + unfold rf, edge_relation, sample_rf. set_solver.
        + exists 0. split; reflexivity.
    Qed.

    Example address_dependency_carries :
      direct_addr_wf sample_events sample_addr /\
      addr sample_events sample_rf sample_data sample_addr 0 3.
    Proof.
      split; first apply sample_addr_wf.
      exists 2. split; first apply sample_carrier.
      unfold direct_addr, edge_relation, sample_addr. set_solver.
    Qed.

    Example data_dependency_carries :
      direct_data_wf sample_events sample_data /\
      data sample_events sample_rf sample_data 0 4.
    Proof.
      split; first apply sample_data_wf.
      exists 2. split; first apply sample_carrier.
      unfold direct_data, edge_relation, sample_data. set_solver.
    Qed.

    Example control_dependency_carries :
      direct_ctrl_wf sample_events sample_ctrl /\
      ctrl sample_events sample_rf sample_data sample_ctrl 0 5.
    Proof.
      split; first apply sample_ctrl_wf.
      exists 2. split; first apply sample_carrier.
      unfold direct_ctrl, edge_relation, sample_ctrl. set_solver.
    Qed.

    Example preserved_program_order_dependency_paths :
      ppo sample_events ∅ sample_rf ∅ sample_data sample_addr sample_ctrl 0 3 /\
      ppo sample_events ∅ sample_rf ∅ sample_data sample_addr sample_ctrl 0 4 /\
      ppo sample_events ∅ sample_rf ∅ sample_data sample_addr sample_ctrl 0 5 /\
      ppo sample_events ∅ sample_rf ∅ sample_data sample_addr sample_ctrl 0 2.
    Proof.
      destruct address_dependency_carries as [_ Haddr].
      destruct data_dependency_carries as [_ Hdata].
      destruct control_dependency_carries as [_ Hctrl].
      assert (data sample_events sample_rf sample_data 0 1) as Hdata_direct.
      { exists 0. split; first apply rt_refl.
        unfold direct_data, edge_relation, sample_data. set_solver. }
      assert (marked sample_events 1) as Hmarked.
      { split.
        - apply in_event_structure_lookup_iff. exists relay_write. reflexivity.
        - intros [Hmode _].
          change (Some AccessOnce = Some AccessPlain) in Hmode. discriminate. }
      assert (rfi sample_events sample_rf 1 2) as Hrfi.
      { split.
        - unfold rf, edge_relation, sample_rf. set_solver.
        - exists 0. split; reflexivity. }
      split_and!.
      - left. left. apply rel_seq_id_on_r. split_and!; first done.
        exists addr_target. split; reflexivity.
      - right. left. left. apply rel_seq_id_on_r. split_and!.
        + left. right. exact Hdata.
        + exists data_target. split; reflexivity.
      - right. left. left. apply rel_seq_id_on_r. split_and!.
        + right. exact Hctrl.
        + exists ctrl_target. split; reflexivity.
      - left. right. exists 1. split.
        + apply rel_seq_id_on_r. split; [by right | done].
        + exact Hrfi.
    Qed.

    Example plain_access_classification :
      plain sample_events 3 /\ ~ marked sample_events 3 /\ marked sample_events 1.
    Proof.
      assert (plain sample_events 3) as Hplain.
      { split; first reflexivity.
        unfold event_is_rmw_marked.
        change (Some NotRmw <> Some RmwMarked). discriminate. }
      assert (marked sample_events 1) as Hmarked.
      { split.
        - apply in_event_structure_lookup_iff. exists relay_write. reflexivity.
        - intros [Hmode _].
          change (Some AccessOnce = Some AccessPlain) in Hmode. discriminate. }
      split_and!; try done.
      intros [_ Hnot_plain]. exact (Hnot_plain Hplain).
    Qed.
  End DependencyTests.

  Module BellEventClassTests.
    Definition acquire_read : event :=
      EAgent 0 0 (LMemory AccessRead AccessAcquire RmwMarked 0 0%Z).
    Definition acquire_write : event :=
      EAgent 0 1 (LMemory AccessWrite AccessAcquire RmwMarked 0 1%Z).
    Definition failed_acquire_read : event :=
      EAgent 0 2 (LMemory AccessRead AccessAcquire RmwMarked 0 0%Z).
    Definition release_read : event :=
      EAgent 0 3 (LMemory AccessRead AccessRelease RmwMarked 0 1%Z).
    Definition release_write : event :=
      EAgent 0 4 (LMemory AccessWrite AccessRelease RmwMarked 0 2%Z).
    Definition failed_release_write : event :=
      EAgent 0 5 (LMemory AccessWrite AccessRelease RmwMarked 0 2%Z).
    Definition mb_read : event := EAgent 0 6 (LMemory AccessRead AccessMb RmwMarked 0 2%Z).
    Definition mb_write : event := EAgent 0 7 (LMemory AccessWrite AccessMb RmwMarked 0 3%Z).
    Definition mb_barrier : event := EAgent 0 8 (LBarrier BarrierMb).
    Definition failed_mb_read : event := EAgent 0 9 (LMemory AccessRead AccessMb RmwMarked 0 3%Z).
    Definition failed_noreturn_read : event :=
      EAgent 0 10 (LMemory AccessRead AccessNoreturn RmwMarked 0 3%Z).
    Definition noreturn_write : event :=
      EAgent 0 11 (LMemory AccessWrite AccessNoreturn RmwMarked 0 4%Z).

    Definition sample_events : event_structure := {[
      0 := acquire_read;
      1 := acquire_write;
      2 := failed_acquire_read;
      3 := release_read;
      4 := release_write;
      5 := failed_release_write;
      6 := mb_read;
      7 := mb_write;
      8 := mb_barrier;
      9 := failed_mb_read;
      10 := failed_noreturn_read;
      11 := noreturn_write
    ]}.
    Definition sample_rmw : edge_set := {[(0, 1); (3, 4); (6, 7)]}.

    Example semantic_event_classification :
      failed_rmw sample_events sample_rmw 2 /\
      failed_rmw sample_events sample_rmw 5 /\
      ~ (failed_rmw sample_events sample_rmw 0 \/
          failed_rmw sample_events sample_rmw 1) /\
      acquire sample_events sample_rmw 0 /\
      ~ (acquire sample_events sample_rmw 1 \/
          acquire sample_events sample_rmw 2) /\
      release sample_events sample_rmw 4 /\
      ~ (release sample_events sample_rmw 3 \/
          release sample_events sample_rmw 5) /\
      mb_event sample_events sample_rmw 6 /\
      mb_event sample_events sample_rmw 8 /\
      failed_rmw sample_events sample_rmw 9 /\
      ~ mb_event sample_events sample_rmw 9 /\
      failed_rmw sample_events sample_rmw 10 /\
      noreturn sample_events 10 /\
      ~ noreturn sample_events 11 /\
      ~ (failed_rmw sample_events sample_rmw 99 \/
          acquire sample_events sample_rmw 99 \/
          release sample_events sample_rmw 99 \/
          mb_event sample_events sample_rmw 99 \/
          noreturn sample_events 99).
    Proof.
      split_and!;
        unfold failed_rmw, acquire, release, mb_event, noreturn,
          rel_domain, rel_range, rmw, edge_relation,
          event_is_rmw_marked, event_has_access_mode, event_has_access_kind,
          event_has_barrier_kind, lookup_event, sample_events, sample_rmw,
          acquire_read, acquire_write, failed_acquire_read,
          release_read, release_write, failed_release_write,
          mb_read, mb_write, mb_barrier, failed_mb_read,
          failed_noreturn_read, noreturn_write;
        simpl; try unfold failed_rmw;
        unfold rel_domain, rel_range, rmw, edge_relation;
        simpl; try split_and!; try (right; reflexivity);
        try (intros [Hmarked _]; unfold event_is_rmw_marked in Hmarked;
          discriminate Hmarked);
        set_solver.
    Qed.
  End BellEventClassTests.

  Module AcquireReleaseOrderingTests.
    Definition acquire_read : event :=
      EAgent 0 0 (LMemory AccessRead AccessAcquire NotRmw 0 0%Z).
    Definition barrier : event := EAgent 0 1 (LBarrier BarrierMb).
    Definition middle_write : event :=
      EAgent 0 2 (LMemory AccessWrite AccessOnce NotRmw 0 1%Z).
    Definition release_write : event :=
      EAgent 0 3 (LMemory AccessWrite AccessRelease NotRmw 0 2%Z).

    Definition sample_events : event_structure := {[
      0 := acquire_read;
      1 := barrier;
      2 := middle_write;
      3 := release_write
    ]}.
    Definition no_rmw : edge_set := ∅.

    Example acquire_release_ordering :
      acq_po sample_events no_rmw 0 2 /\
      po_rel sample_events no_rmw 2 3 /\
      ~ acq_po sample_events no_rmw 0 1 /\
      ~ po_rel sample_events no_rmw 1 3.
    Proof.
      assert (event_is_memory sample_events 2) as Hmemory.
      { exists middle_write. split; reflexivity. }
      assert (~ event_is_memory sample_events 1) as Hbarrier.
      { intros (ev & Hlookup & Hmemory').
        change (Some barrier = Some ev) in Hlookup.
        injection Hlookup as <-. done. }
      split_and!;
        unfold acq_po, po_rel, acquire, release, failed_rmw,
          rel_seq, rel_id_on, rel_domain, rel_range, rmw, edge_relation,
          event_is_memory,
          event_has_access_mode, event_has_access_kind, event_is_rmw_marked,
          po, lookup_event, sample_events, no_rmw, acquire_read, barrier,
          middle_write, release_write;
        simpl; try set_solver; naive_solver.
    Qed.
  End AcquireReleaseOrderingTests.

  Module FenceOrderingTests.
    Definition noreturn_read : event :=
      EAgent 0 0 (LMemory AccessRead AccessNoreturn NotRmw 0 0%Z).
    Definition before_read : event :=
      EAgent 0 1 (LMemory AccessRead AccessOnce NotRmw 0 0%Z).
    Definition rmb_barrier : event := EAgent 0 2 (LBarrier BarrierRmb).
    Definition after_read : event :=
      EAgent 0 3 (LMemory AccessRead AccessOnce NotRmw 0 0%Z).
    Definition before_write : event :=
      EAgent 0 4 (LMemory AccessWrite AccessPlain NotRmw 0 1%Z).
    Definition wmb_barrier : event := EAgent 0 5 (LBarrier BarrierWmb).
    Definition after_write : event :=
      EAgent 0 6 (LMemory AccessWrite AccessOnce NotRmw 0 2%Z).
    Definition mb_barrier : event := EAgent 0 7 (LBarrier BarrierMb).
    Definition before_rmw : event :=
      EAgent 0 8 (LMemory AccessRead AccessOnce NotRmw 0 2%Z).
    Definition sync_rcu : event := EAgent 0 9 (LBarrier BarrierSyncRcu).
    Definition rmw_read : event :=
      EAgent 0 10 (LMemory AccessRead AccessMb RmwMarked 0 2%Z).
    Definition rmw_write : event :=
      EAgent 0 11 (LMemory AccessWrite AccessMb RmwMarked 0 3%Z).
    Definition after_rmw : event :=
      EAgent 0 12 (LMemory AccessRead AccessOnce NotRmw 0 3%Z).
    Definition before_atomic_source : event :=
      EAgent 0 0 (LMemory AccessWrite AccessOnce NotRmw 1 0%Z).
    Definition before_atomic_barrier : event :=
      EAgent 0 1 (LBarrier BarrierBeforeAtomic).
    Definition atomic_read : event :=
      EAgent 0 2 (LMemory AccessRead AccessOnce RmwMarked 1 0%Z).
    Definition atomic_write : event :=
      EAgent 0 3 (LMemory AccessWrite AccessOnce RmwMarked 1 1%Z).
    Definition after_atomic_barrier : event :=
      EAgent 0 4 (LBarrier BarrierAfterAtomic).
    Definition after_atomic_target : event :=
      EAgent 0 5 (LMemory AccessRead AccessOnce NotRmw 1 1%Z).

    Definition sample_events : event_structure := {[
      0 := noreturn_read;
      1 := before_read;
      2 := rmb_barrier;
      3 := after_read;
      4 := before_write;
      5 := wmb_barrier;
      6 := after_write;
      7 := mb_barrier;
      8 := before_rmw;
      9 := sync_rcu;
      10 := rmw_read;
      11 := rmw_write;
      12 := after_rmw
    ]}.
    Definition sample_rmw : edge_set := {[(10, 11)]}.
    Definition sample_addr : edge_set := {[(3, 4)]}.

    Definition atomic_events : event_structure := {[
      0 := before_atomic_source;
      1 := before_atomic_barrier;
      2 := atomic_read;
      3 := atomic_write;
      4 := after_atomic_barrier;
      5 := after_atomic_target
    ]}.
    Definition atomic_rmw : edge_set := {[(2, 3)]}.

    Local Lemma agent0_po E eid1 eid2 index1 index2 label1 label2 :
      lookup_event E eid1 = Some (EAgent 0 index1 label1) ->
      lookup_event E eid2 = Some (EAgent 0 index2 label2) ->
      index1 < index2 ->
      po E eid1 eid2.
    Proof.
      intros Hlookup1 Hlookup2 Hlt.
      exists 0, index1, index2, label1, label2. done.
    Qed.

    Local Ltac solve_po :=
      eapply agent0_po; [reflexivity | reflexivity | lia].

    Local Ltac solve_fencerel barrier :=
      unfold fencerel; exists barrier; split_and!;
        [ apply rel_seq_id_on_r; split_and!; [solve_po | reflexivity]
        | solve_po ].

    Local Lemma sample_rmb : rmb sample_events 1 3.
    Proof.
      unfold rmb. rewrite rel_seq_id_on_r, rel_seq_id_on_l.
      unfold r4_rmb. split_and!.
      - eexists. split; done.
      - unfold noreturn, event_has_access_mode, event_has_access_kind.
        intros [Hmode _].
        change (Some AccessOnce = Some AccessNoreturn) in Hmode. discriminate.
      - solve_fencerel 2.
      - eexists. split; done.
      - unfold noreturn, event_has_access_mode, event_has_access_kind.
        intros [Hmode _].
        change (Some AccessOnce = Some AccessNoreturn) in Hmode. discriminate.
    Qed.

    Local Lemma sample_not_rmb : ~ rmb sample_events 0 3.
    Proof.
      unfold rmb. rewrite rel_seq_id_on_r, rel_seq_id_on_l.
      unfold r4_rmb. intros (((_ & Hnot_noreturn) & _) & _). apply Hnot_noreturn.
      unfold noreturn, event_has_access_mode, event_has_access_kind. split; first done.
      intros Hkind.
      change (Some AccessRead = Some AccessWrite) in Hkind. discriminate.
    Qed.

    Local Lemma sample_wmb : wmb sample_events 4 6.
    Proof.
      unfold wmb. rewrite rel_seq_id_on_r, rel_seq_id_on_l. split_and!.
      - eexists. split; done.
      - solve_fencerel 5.
      - eexists. split; done.
    Qed.

    Local Lemma sample_plain_to_w : to_w sample_events ∅ ∅ ∅ sample_addr ∅ 3 6.
    Proof.
      right. right. exists 4. split.
      - apply rel_seq_id_on_r. split.
        + exists 3. split; first apply rt_refl.
          unfold direct_addr, edge_relation, sample_addr. set_solver.
        + split; first reflexivity.
          unfold event_is_rmw_marked.
          change (Some NotRmw <> Some RmwMarked). discriminate.
      - apply sample_wmb.
    Qed.

    Local Lemma sample_not_wmb : ~ wmb sample_events 3 6.
    Proof.
      unfold wmb. rewrite rel_seq_id_on_r, rel_seq_id_on_l.
      intros (((ev & Hlookup & Hwrite) & _) & _).
      change (Some after_read = Some ev) in Hlookup.
      injection Hlookup as <-. done.
    Qed.

    Local Lemma sample_mb_event_read : mb_event sample_events sample_rmw 10.
    Proof.
      unfold mb_event, failed_rmw, rel_domain, rel_range, rmw, edge_relation,
        event_has_access_mode, event_is_rmw_marked, sample_rmw.
      simpl. set_solver.
    Qed.

    Local Lemma sample_mb_event_write : mb_event sample_events sample_rmw 11.
    Proof.
      unfold mb_event, failed_rmw, rel_domain, rel_range, rmw, edge_relation,
        event_has_access_mode, event_is_rmw_marked, sample_rmw.
      simpl. set_solver.
    Qed.

    Local Lemma sample_mb_explicit : mb sample_events sample_rmw 6 8.
    Proof.
      left. rewrite rel_seq_id_on_r, rel_seq_id_on_l. split_and!.
      - eexists. split; done.
      - solve_fencerel 7.
      - eexists. split; done.
    Qed.

    Local Lemma sample_mb_before_rmw : mb sample_events sample_rmw 8 10.
    Proof.
      right. left. exists 10. split.
      - apply rel_seq_id_on_l. split_and!.
        + eexists. split; done.
        + solve_po.
      - split_and!.
        + split; [done | apply sample_mb_event_read].
        + split; first done. eexists. split; done.
    Qed.

    Local Lemma sample_mb_after_rmw : mb sample_events sample_rmw 11 12.
    Proof.
      right. right. left. apply rel_seq_id_on_r. split.
      - exists 11. split.
        + split_and!.
          * split; [done | apply sample_mb_event_write].
          * split; first done. eexists. split; done.
        + solve_po.
      - eexists. split; done.
    Qed.

    Local Lemma sample_mb_before_atomic : mb atomic_events atomic_rmw 0 3.
    Proof.
      right. right. right. left. apply rel_seq_id_on_r. split.
      - exists 2. split.
        + apply rel_seq_id_on_r. split.
          * apply rel_seq_id_on_l. split.
            { eexists. split; done. }
            { solve_fencerel 1. }
          * unfold event_is_rmw_marked. reflexivity.
        + right. solve_po.
      - eexists. split; done.
    Qed.

    Local Lemma sample_mb_after_atomic : mb atomic_events atomic_rmw 2 5.
    Proof.
      right. right. right. right. apply rel_seq_id_on_r. split.
      - exists 3. split.
        + apply rel_seq_id_on_r. split.
          * apply rel_seq_id_on_l. split.
            { eexists. split; done. }
            { right. solve_po. }
          * unfold event_is_rmw_marked. reflexivity.
        + solve_fencerel 4.
      - eexists. split; done.
    Qed.

    Local Lemma sample_gp_at_sync : gp sample_events 8 9.
    Proof.
      exists 9. split.
      - apply rel_seq_id_on_r. split_and!; [solve_po | reflexivity].
      - left. done.
    Qed.

    Local Lemma sample_gp_after : gp sample_events 8 10.
    Proof.
      exists 9. split.
      - apply rel_seq_id_on_r. split_and!; [solve_po | reflexivity].
      - right. solve_po.
    Qed.

    Example primitive_fence_ordering :
      rmb sample_events 1 3 /\
      ~ rmb sample_events 0 3 /\
      wmb sample_events 4 6 /\
      ~ wmb sample_events 3 6 /\
      mb sample_events sample_rmw 6 8 /\
      mb sample_events sample_rmw 8 10 /\
      mb sample_events sample_rmw 11 12 /\
      mb atomic_events atomic_rmw 0 3 /\
      mb atomic_events atomic_rmw 2 5 /\
      gp sample_events 8 9 /\
      gp sample_events 8 10 /\
      to_w sample_events ∅ ∅ ∅ sample_addr ∅ 3 6.
    Proof.
      split_and!;
        [ apply sample_rmb
        | apply sample_not_rmb
        | apply sample_wmb
        | apply sample_not_wmb
        | apply sample_mb_explicit
        | apply sample_mb_before_rmw
        | apply sample_mb_after_rmw
        | apply sample_mb_before_atomic
        | apply sample_mb_after_atomic
        | apply sample_gp_at_sync
        | apply sample_gp_after
        | apply sample_plain_to_w ].
    Qed.

  End FenceOrderingTests.

  Module PropagationTests.
    Definition co_source : event :=
      EAgent 2 0 (LMemory AccessWrite AccessOnce NotRmw 0 0%Z).
    Definition rf_source : event :=
      EAgent 0 0 (LMemory AccessWrite AccessOnce NotRmw 0 1%Z).
    Definition remote_read : event :=
      EAgent 1 0 (LMemory AccessRead AccessOnce NotRmw 0 1%Z).
    Definition release_write : event :=
      EAgent 1 1 (LMemory AccessWrite AccessRelease NotRmw 0 2%Z).
    Definition rmw_read : event :=
      EAgent 1 2 (LMemory AccessRead AccessOnce RmwMarked 0 2%Z).
    Definition rmw_write : event :=
      EAgent 1 3 (LMemory AccessWrite AccessOnce RmwMarked 0 3%Z).
    Definition final_read : event :=
      EAgent 2 1 (LMemory AccessRead AccessOnce NotRmw 0 3%Z).
    Definition mb_barrier : event := EAgent 2 2 (LBarrier BarrierMb).
    Definition pb_target : event :=
      EAgent 2 3 (LMemory AccessRead AccessOnce NotRmw 0 3%Z).

    Definition sample_events : event_structure := {[
      0 := co_source;
      1 := rf_source;
      2 := remote_read;
      3 := release_write;
      4 := rmw_read;
      5 := rmw_write;
      6 := final_read;
      7 := mb_barrier;
      8 := pb_target
    ]}.
    Definition sample_rf : edge_set := {[(1, 2); (3, 4); (5, 6)]}.
    Definition sample_rmw : edge_set := {[(4, 5)]}.
    Definition sample_co : edge_set := {[(0, 1)]}.
    Definition cyclic_ctrl : edge_set := {[(0, 1); (1, 0); (8, 0)]}.

    Local Ltac solve_marked :=
      split;
        [ apply in_event_structure_lookup_iff; eexists; reflexivity
        | intros [Hmode _]; unfold event_has_access_mode in Hmode;
          discriminate Hmode ].

    Local Ltac solve_cyclic_hb :=
      apply rel_seq_id_on_r; split_and!;
        [ apply rel_seq_id_on_l; split_and!;
          [ solve_marked
          | left; right; left; left; apply rel_seq_id_on_r; split_and!;
            [ right; eexists; split;
              [ apply rt_refl
              | unfold direct_ctrl, edge_relation, cyclic_ctrl; set_solver ]
            | eexists; split; [reflexivity | done] ] ]
        | solve_marked ].

    Local Lemma sample_po_rel : po_rel sample_events sample_rmw 2 3.
    Proof.
      unfold po_rel. rewrite rel_seq_id_on_r, rel_seq_id_on_l. split_and!.
      - eexists. split; done.
      - exists 1, 0, 1,
          (LMemory AccessRead AccessOnce NotRmw 0 1%Z),
          (LMemory AccessWrite AccessRelease NotRmw 0 2%Z).
        split_and!; try done. lia.
      - unfold release, failed_rmw, rel_domain, rel_range, rmw, edge_relation,
          event_has_access_mode, event_has_access_kind, event_is_rmw_marked,
          sample_rmw.
        simpl. set_solver.
    Qed.

    Local Lemma sample_rfe_left : rfe sample_events sample_rf 1 2.
    Proof.
      split.
      - unfold rf, edge_relation, sample_rf. set_solver.
      - intros (agent & Hagent0 & Hagent1).
        change (Some 0 = Some agent) in Hagent0.
        change (Some 1 = Some agent) in Hagent1. congruence.
    Qed.

    Local Lemma sample_rfe_right : rfe sample_events sample_rf 5 6.
    Proof.
      split.
      - unfold rf, edge_relation, sample_rf. set_solver.
      - intros (agent & Hagent1 & Hagent2).
        change (Some 1 = Some agent) in Hagent1.
        change (Some 2 = Some agent) in Hagent2. congruence.
    Qed.

    Local Lemma sample_external_overwrite :
      rel_intersection (overwrite sample_rf sample_co) (ext sample_events) 0 1.
    Proof.
      split.
      - left. unfold co, edge_relation, sample_co. set_solver.
      - intros (agent & Hagent2 & Hagent0).
        change (Some 2 = Some agent) in Hagent2.
        change (Some 0 = Some agent) in Hagent0. congruence.
    Qed.

    Local Lemma sample_strong_fence : strong_fence sample_events sample_rmw 6 8.
    Proof.
      left. left. rewrite rel_seq_id_on_r, rel_seq_id_on_l. split_and!.
      - eexists. split; done.
      - unfold fencerel. exists 7. split.
        + apply rel_seq_id_on_r. split_and!.
          * exists 2, 1, 2,
              (LMemory AccessRead AccessOnce NotRmw 0 3%Z),
              (LBarrier BarrierMb).
            split_and!; try done. lia.
          * unfold event_has_barrier_kind. reflexivity.
        + exists 2, 2, 3,
            (LBarrier BarrierMb),
            (LMemory AccessRead AccessOnce NotRmw 0 3%Z).
          split_and!; try done. lia.
      - eexists. split; done.
    Qed.

    Example propagation_chain :
      a_cumul sample_events sample_rf
        (rel_union (strong_fence sample_events sample_rmw)
          (po_rel sample_events sample_rmw)) 1 3 /\
      rmw_sequence sample_rf sample_rmw 3 5 /\
      cumul_fence sample_events sample_rmw sample_rf 1 5 /\
      prop sample_events sample_rmw sample_rf sample_co 0 6 /\
      hb sample_events sample_rmw sample_rf sample_co ∅ ∅ ∅ 0 6 /\
      ~ happens_before sample_events sample_rmw sample_rf sample_co ∅ ∅ cyclic_ctrl /\
      pb sample_events sample_rmw sample_rf sample_co ∅ ∅ ∅ 0 8 /\
      ~ propagation sample_events sample_rmw sample_rf sample_co ∅ ∅ cyclic_ctrl.
    Proof.
      assert (marked sample_events 0) as Hmarked0 by solve_marked.
      assert (marked sample_events 1) as Hmarked1 by solve_marked.
      assert (marked sample_events 2) as Hmarked2 by solve_marked.
      assert (marked sample_events 3) as Hmarked3 by solve_marked.
      assert (marked sample_events 5) as Hmarked5 by solve_marked.
      assert (marked sample_events 6) as Hmarked6 by solve_marked.
      assert (marked sample_events 8) as Hmarked8 by solve_marked.
      assert (a_cumul sample_events sample_rf
        (rel_union (strong_fence sample_events sample_rmw)
          (po_rel sample_events sample_rmw)) 1 3) as Hacumul.
      { exists 2. split.
        - right. apply rel_seq_id_on_r. split_and!; [apply sample_rfe_left | done].
        - right. apply sample_po_rel. }
      assert (rmw_sequence sample_rf sample_rmw 3 5) as Hrmw_sequence.
      { apply rt_step. exists 4. split;
          unfold rf, rmw, edge_relation, sample_rf, sample_rmw; set_solver. }
      assert (cumul_fence sample_events sample_rmw sample_rf 1 5) as Hcumul_fence.
      { exists 3. split; last done.
        apply rel_seq_id_on_r. split; last done.
        apply rel_seq_id_on_l. split; first done.
        left. exact Hacumul. }
      assert (prop sample_events sample_rmw sample_rf sample_co 0 6) as Hprop.
      { apply rel_seq_id_on_r. split; last done.
        exists 5. split; last (right; apply sample_rfe_right).
        apply rel_seq_id_on_r. split; last done.
        exists 1. split.
        - apply rel_seq_id_on_l. split_and!; [done | right; apply sample_external_overwrite].
        - apply rt_step. exact Hcumul_fence. }
      assert (hb sample_events sample_rmw sample_rf sample_co ∅ ∅ ∅ 0 6) as Hhb.
      { apply rel_seq_id_on_r. split; last done.
        apply rel_seq_id_on_l. split; first done.
        right. right. split_and!.
        - split; [done | discriminate].
        - exists 2. split; reflexivity. }
      assert (hb sample_events sample_rmw sample_rf sample_co ∅ ∅ cyclic_ctrl 0 1)
        as Hhb01 by solve_cyclic_hb.
      assert (hb sample_events sample_rmw sample_rf sample_co ∅ ∅ cyclic_ctrl 1 0)
        as Hhb10 by solve_cyclic_hb.
      assert (~ happens_before sample_events sample_rmw sample_rf sample_co ∅ ∅ cyclic_ctrl)
        as Hnot_happens_before.
      { intros Hhappens_before.
        unfold happens_before, rel_acyclic, rel_irreflexive in Hhappens_before.
        apply (Hhappens_before 0).
        eapply t_trans with (y := 1); apply t_step; done. }
      assert (pb sample_events sample_rmw sample_rf sample_co ∅ ∅ ∅ 0 8) as Hpb.
      { apply rel_seq_id_on_r. split; last done.
        exists 8. split; last apply rt_refl.
        exists 6. split; [done | apply sample_strong_fence]. }
      assert (hb sample_events sample_rmw sample_rf sample_co ∅ ∅ cyclic_ctrl 8 0)
        as Hhb80 by solve_cyclic_hb.
      assert (pb sample_events sample_rmw sample_rf sample_co ∅ ∅ cyclic_ctrl 0 0)
        as Hpb00.
      { apply rel_seq_id_on_r. split; last done.
        exists 8. split; last (apply rt_step; done).
        exists 6. split; [done | apply sample_strong_fence]. }
      assert (~ propagation sample_events sample_rmw sample_rf sample_co ∅ ∅ cyclic_ctrl)
        as Hnot_propagation.
      { intros Hpropagation.
        unfold propagation, rel_acyclic, rel_irreflexive in Hpropagation.
        apply (Hpropagation 0). apply t_step. done. }
      split_and!; done.
    Qed.
  End PropagationTests.

  Module ReadsFromTests.
    Definition init_write : event := EInitWrite 0 0%Z.
    Definition once_read : event := EAgent 0 0 (LMemory AccessRead AccessOnce NotRmw 0 0%Z).
    Definition second_write : event := EAgent 1 0 (LMemory AccessWrite AccessOnce NotRmw 0 0%Z).

    Definition sample_events : event_structure := {[0 := init_write; 1 := once_read]}.

    Definition sample_rf : edge_set := {[(0, 1)]}.

    Example sample_rf_wf : rf_wf sample_events sample_rf.
    Proof.
      split.
      - intros write read Hrf.
        unfold rf, edge_relation, sample_rf in Hrf.
        assert (write = 0 /\ read = 1) as [-> ->] by set_solver.
        exists init_write, once_read, 0%Z.
        split_and!; try reflexivity.
        exists 0. split; reflexivity.
      - split.
        + intros write1 write2 read Hrf1 Hrf2.
          unfold rf, edge_relation, sample_rf in Hrf1, Hrf2.
          set_solver.
        + intros read read_event Hlookup Hread.
          unfold lookup_event, sample_events in Hlookup.
          apply lookup_insert_Some in Hlookup.
          destruct Hlookup as [[Hread_id Hread_event] | [Hne Hlookup]].
          * subst read. subst read_event.
            unfold is_read, init_write, access_kind_of in Hread.
            discriminate Hread.
          * apply lookup_singleton_Some in Hlookup as [Hread_id Hread_event].
            subst read. subst read_event.
            exists 0. unfold rf, edge_relation, sample_rf. set_solver.
    Qed.

    Definition two_source_events : event_structure :=
      {[0 := init_write; 1 := once_read; 2 := second_write]}.

    Definition two_source_rf : edge_set := {[(0, 1); (2, 1)]}.

    Example two_sources_are_not_well_formed :
      ~ rf_wf two_source_events two_source_rf.
    Proof.
      intros Hwf.
      pose proof (rf_wf_functional two_source_events two_source_rf Hwf)
        as Hfunctional.
      assert (0 = 2) as Heq.
      { eapply Hfunctional with (read := 1); unfold rf, edge_relation, two_source_rf; set_solver. }
      lia.
    Qed.
  End ReadsFromTests.

  Module ReadModifyWriteTests.
    Definition marked_read : event := EAgent 0 0 (LMemory AccessRead AccessMb RmwMarked 0 7%Z).
    Definition marked_write : event := EAgent 0 1 (LMemory AccessWrite AccessMb RmwMarked 0 8%Z).
    Definition sample_events : event_structure := {[0 := marked_read; 1 := marked_write]}.
    Definition sample_rmw : edge_set := {[(0, 1)]}.

    Definition failed_events : event_structure := {[0 := marked_read]}.
    Definition write_only_events : event_structure := {[1 := marked_write]}.

    Definition unmarked_read : event := EAgent 0 0 (LMemory AccessRead AccessMb NotRmw 0 7%Z).
    Definition unmarked_source_events : event_structure :=
      {[0 := unmarked_read; 1 := marked_write]}.
    Definition unmarked_write : event := EAgent 0 1 (LMemory AccessWrite AccessMb NotRmw 0 8%Z).
    Definition unmarked_target_events : event_structure :=
      {[0 := marked_read; 1 := unmarked_write]}.

    Definition other_location_write : event :=
      EAgent 0 1 (LMemory AccessWrite AccessMb RmwMarked 1 8%Z).
    Definition different_location_events : event_structure :=
      {[0 := marked_read; 1 := other_location_write]}.
    Definition other_mode_write : event :=
      EAgent 0 1 (LMemory AccessWrite AccessOnce RmwMarked 0 8%Z).
    Definition different_mode_events : event_structure :=
      {[0 := marked_read; 1 := other_mode_write]}.
    Definition other_agent_write : event :=
      EAgent 1 1 (LMemory AccessWrite AccessMb RmwMarked 0 8%Z).
    Definition different_agent_events : event_structure :=
      {[0 := marked_read; 1 := other_agent_write]}.
    Definition late_read : event := EAgent 0 2 (LMemory AccessRead AccessMb RmwMarked 0 7%Z).
    Definition reversed_po_events : event_structure := {[0 := late_read; 1 := marked_write]}.

    Definition second_write : event := EAgent 0 2 (LMemory AccessWrite AccessMb RmwMarked 0 9%Z).
    Definition two_write_events : event_structure :=
      {[0 := marked_read; 1 := marked_write; 2 := second_write]}.
    Definition one_read_two_writes : edge_set := {[(0, 1); (0, 2)]}.

    Definition second_read : event := EAgent 0 1 (LMemory AccessRead AccessMb RmwMarked 0 7%Z).
    Definition late_write : event := EAgent 0 2 (LMemory AccessWrite AccessMb RmwMarked 0 8%Z).
    Definition two_read_events : event_structure :=
      {[0 := marked_read; 1 := late_write; 2 := second_read]}.
    Definition two_reads_one_write : edge_set := {[(0, 1); (2, 1)]}.

    Definition intervening_write : event := EAgent 1 0 (LMemory AccessWrite AccessMb NotRmw 0 9%Z).
    Definition atomicity_events : event_structure :=
      {[0 := marked_read;
        1 := marked_write;
        2 := intervening_write;
        3 := EInitWrite 0 7%Z]}.
    Definition atomicity_rf : edge_set := {[(3, 0)]}.
    Definition intervened_co : edge_set := {[(3, 2); (3, 1); (2, 1)]}.

    Local Lemma sample_lookup_cases eid ev :
      lookup_event sample_events eid = Some ev ->
      (eid = 0 /\ ev = marked_read) \/
      (eid = 1 /\ ev = marked_write).
    Proof.
      intros Hlookup.
      unfold lookup_event, sample_events in Hlookup.
      apply lookup_insert_Some in Hlookup.
      destruct Hlookup as [[-> Hevent] | [Hne Hlookup]].
      - left. naive_solver.
      - apply lookup_singleton_Some in Hlookup.
        right. naive_solver.
    Qed.

    Local Lemma singleton_rmw_edge read write :
      rmw ({[(read, write)]} : edge_set) read write.
    Proof. unfold rmw, edge_relation. set_solver. Qed.

    Example valid_rmw_candidates :
      rmw_wf sample_events sample_rmw /\
      rmw_wf failed_events (∅ : edge_set).
    Proof.
      split.
      - split_and!.
        + intros read write Hrmw.
          unfold rmw, edge_relation, sample_rmw in Hrmw.
          assert (read = 0 /\ write = 1) as [-> ->] by set_solver.
          exists marked_read, marked_write.
          split_and!; try reflexivity.
          * exists 0, 0, 1,
              (LMemory AccessRead AccessMb RmwMarked 0 7%Z),
              (LMemory AccessWrite AccessMb RmwMarked 0 8%Z).
            split_and!; try reflexivity. lia.
          * exists 0. split; reflexivity.
          * exists AccessMb. split; reflexivity.
        + intros read write1 write2 Hrmw1 Hrmw2.
          unfold rmw, edge_relation, sample_rmw in Hrmw1, Hrmw2.
          set_solver.
        + intros read1 read2 write Hrmw1 Hrmw2.
          unfold rmw, edge_relation, sample_rmw in Hrmw1, Hrmw2.
          set_solver.
        + intros write write_event Hlookup Hwrite Hmarked.
          destruct (sample_lookup_cases write write_event Hlookup)
            as [(-> & ->) | (-> & ->)].
          * discriminate Hwrite.
          * exists 0. unfold rmw, edge_relation, sample_rmw. set_solver.
      - split_and!.
        + intros read write Hrmw.
          unfold rmw, edge_relation in Hrmw. set_solver.
        + intros read write1 write2 Hrmw1 Hrmw2.
          unfold rmw, edge_relation in Hrmw1. set_solver.
        + intros read1 read2 write Hrmw1 Hrmw2.
          unfold rmw, edge_relation in Hrmw1. set_solver.
        + intros write write_event Hlookup Hwrite Hmarked.
          unfold lookup_event, failed_events in Hlookup.
          apply lookup_singleton_Some in Hlookup as [Hwrite_id Hevent].
          subst write. subst write_event.
          discriminate Hwrite.
    Qed.

    Example malformed_rmw_candidates :
      ~ rmw_wf write_only_events (∅ : edge_set) /\
      ~ rmw_wf sample_events ({[(1, 0)]} : edge_set) /\
      ~ rmw_wf unmarked_source_events ({[(0, 1)]} : edge_set) /\
      ~ rmw_wf unmarked_target_events ({[(0, 1)]} : edge_set) /\
      ~ rmw_wf different_location_events ({[(0, 1)]} : edge_set) /\
      ~ rmw_wf different_mode_events ({[(0, 1)]} : edge_set) /\
      ~ rmw_wf different_agent_events ({[(0, 1)]} : edge_set) /\
      ~ rmw_wf reversed_po_events ({[(0, 1)]} : edge_set).
    Proof.
      assert (~ rmw_wf write_only_events (∅ : edge_set)) as Hunpaired.
      { intros Hwf.
        pose proof (rmw_wf_write_total write_only_events
          (∅ : edge_set) Hwf) as Htotal.
        destruct (Htotal 1 marked_write) as (read & Hrmw);
          try reflexivity.
        unfold rmw, edge_relation in Hrmw. set_solver. }
      assert (~ rmw_wf sample_events ({[(1, 0)]} : edge_set)) as Hkinds.
      { intros Hwf.
        destruct (rmw_wf_kinds sample_events ({[(1, 0)]} : edge_set)
          1 0 Hwf (singleton_rmw_edge 1 0))
          as (read_event & write_event & Hread & Hwrite &
            Hread_kind & Hwrite_kind).
        assert (read_event = marked_write) as ->.
        { change (Some marked_write = Some read_event) in Hread. congruence. }
        discriminate Hread_kind. }
      assert (~ rmw_wf unmarked_source_events ({[(0, 1)]} : edge_set)) as Hsource_marked.
      { intros Hwf.
        destruct (rmw_wf_marked unmarked_source_events
          ({[(0, 1)]} : edge_set) 0 1 Hwf (singleton_rmw_edge 0 1))
          as (read_event & write_event & Hread & Hwrite &
            Hread_marked & Hwrite_marked).
        assert (read_event = unmarked_read) as ->.
        { change (Some unmarked_read = Some read_event) in Hread. congruence. }
        discriminate Hread_marked. }
      assert (~ rmw_wf unmarked_target_events ({[(0, 1)]} : edge_set)) as Htarget_marked.
      { intros Hwf.
        destruct (rmw_wf_marked unmarked_target_events
          ({[(0, 1)]} : edge_set) 0 1 Hwf (singleton_rmw_edge 0 1))
          as (read_event & write_event & Hread & Hwrite &
            Hread_marked & Hwrite_marked).
        assert (write_event = unmarked_write) as ->.
        { change (Some unmarked_write = Some write_event) in Hwrite. congruence. }
        discriminate Hwrite_marked. }
      assert (~ rmw_wf different_location_events ({[(0, 1)]} : edge_set)) as Hlocation.
      { intros Hwf.
        pose proof (rmw_wf_same_location different_location_events
          ({[(0, 1)]} : edge_set) 0 1 Hwf (singleton_rmw_edge 0 1))
          as (loc & Hread_loc & Hwrite_loc).
        change (Some 0 = Some loc) in Hread_loc.
        change (Some 1 = Some loc) in Hwrite_loc.
        congruence. }
      assert (~ rmw_wf different_mode_events ({[(0, 1)]} : edge_set)) as Hmode.
      { intros Hwf.
        pose proof (rmw_wf_same_mode different_mode_events
          ({[(0, 1)]} : edge_set) 0 1 Hwf (singleton_rmw_edge 0 1))
          as (mode & Hread_mode & Hwrite_mode).
        change (Some AccessMb = Some mode) in Hread_mode.
        change (Some AccessOnce = Some mode) in Hwrite_mode.
        congruence. }
      assert (~ rmw_wf different_agent_events ({[(0, 1)]} : edge_set)) as Hagent.
      { intros Hwf.
        pose proof (rmw_wf_po different_agent_events
          ({[(0, 1)]} : edge_set) 0 1 Hwf (singleton_rmw_edge 0 1))
          as (agent & index1 & index2 & label1 & label2 &
            Hread & Hwrite & Hlt).
        change (Some marked_read = Some (EAgent agent index1 label1)) in Hread.
        change (Some other_agent_write =
          Some (EAgent agent index2 label2)) in Hwrite.
        unfold marked_read, other_agent_write in Hread, Hwrite.
        congruence. }
      assert (~ rmw_wf reversed_po_events ({[(0, 1)]} : edge_set)) as Hpo.
      { intros Hwf.
        pose proof (rmw_wf_po reversed_po_events
          ({[(0, 1)]} : edge_set) 0 1 Hwf (singleton_rmw_edge 0 1))
          as (agent & index1 & index2 & label1 & label2 &
            Hread & Hwrite & Hlt).
        change (Some late_read = Some (EAgent agent index1 label1)) in Hread.
        change (Some marked_write = Some (EAgent agent index2 label2)) in Hwrite.
        unfold late_read in Hread. unfold marked_write in Hwrite.
        assert (index1 = 2) as -> by congruence.
        assert (index2 = 1) as -> by congruence.
        lia. }
      tauto.
    Qed.

    Example rmw_pairing_is_a_partial_bijection :
      ~ rmw_wf two_write_events one_read_two_writes /\
      ~ rmw_wf two_read_events two_reads_one_write.
    Proof.
      split.
      - intros Hwf.
        pose proof (rmw_wf_functional two_write_events
          one_read_two_writes Hwf) as Hfunctional.
        assert (1 = 2) as Heq.
        { eapply Hfunctional with (read := 0);
            unfold rmw, edge_relation, one_read_two_writes; set_solver. }
        lia.
      - intros Hwf.
        pose proof (rmw_wf_injective two_read_events
          two_reads_one_write Hwf) as Hinjective.
        assert (0 = 2) as Heq.
        { eapply Hinjective with (write := 1);
            unfold rmw, edge_relation, two_reads_one_write; set_solver. }
        lia.
    Qed.

    Example intervening_external_write_violates_atomicity :
      ~ atomicity atomicity_events sample_rmw atomicity_rf intervened_co.
    Proof.
      unfold atomicity, rel_is_empty.
      intros Hatomic. apply (Hatomic 0 1). split.
      - unfold rmw, edge_relation, sample_rmw. set_solver.
      - exists 2. split.
        + split.
          * unfold fr, rel_seq, rel_inverse, rf, co, edge_relation,
              atomicity_rf, intervened_co.
            exists 3. split; set_solver.
          * intros (agent & Hread_agent & Hwrite_agent).
            change (Some 0 = Some agent) in Hread_agent.
            change (Some 1 = Some agent) in Hwrite_agent. congruence.
        + split.
          * unfold co, edge_relation, intervened_co. set_solver.
          * intros (agent & Hwrite1_agent & Hwrite2_agent).
            change (Some 1 = Some agent) in Hwrite1_agent.
            change (Some 0 = Some agent) in Hwrite2_agent. congruence.
    Qed.
  End ReadModifyWriteTests.

  Module CoherenceOrderTests.
    Definition init_write : event := EInitWrite 0 0%Z.
    Definition first_write : event := EAgent 0 0 (LMemory AccessWrite AccessOnce NotRmw 0 1%Z).
    Definition second_write : event := EAgent 1 0 (LMemory AccessWrite AccessOnce NotRmw 0 2%Z).

    Definition sample_events : event_structure :=
      {[0 := init_write; 1 := first_write; 2 := second_write]}.

    Definition sample_co : edge_set := {[(0, 1); (0, 2); (1, 2)]}.

    Local Lemma sample_lookup_cases eid ev :
      lookup_event sample_events eid = Some ev ->
      (eid = 0 /\ ev = init_write) \/
      (eid = 1 /\ ev = first_write) \/
      (eid = 2 /\ ev = second_write).
    Proof.
      intros Hlookup.
      unfold lookup_event, sample_events in Hlookup.
      apply lookup_insert_Some in Hlookup.
      destruct Hlookup as [[-> Hevent] | [Hne Hlookup]].
      - left. naive_solver.
      - apply lookup_insert_Some in Hlookup.
        destruct Hlookup as [[-> Hevent] | [Hne' Hlookup]].
        + right. left. naive_solver.
        + apply lookup_singleton_Some in Hlookup.
          right. right. naive_solver.
    Qed.

    Example sample_co_wf : co_wf sample_events sample_co.
    Proof.
      split_and!.
      - intros write1 write2 Hco.
        unfold co, edge_relation, sample_co in Hco.
        assert ((write1 = 0 /\ write2 = 1) \/
          (write1 = 0 /\ write2 = 2) \/
          (write1 = 1 /\ write2 = 2)) as
            [(-> & ->) | [(-> & ->) | (-> & ->)]] by set_solver.
        + exists init_write, first_write.
          split_and!; try reflexivity.
          exists 0. split; reflexivity.
        + exists init_write, second_write.
          split_and!; try reflexivity.
          exists 0. split; reflexivity.
        + exists first_write, second_write.
          split_and!; try reflexivity.
          exists 0. split; reflexivity.
      - intros write Hco.
        unfold co, edge_relation, sample_co in Hco. set_solver.
      - intros write1 write2 write3 Hco12 Hco23.
        unfold co, edge_relation, sample_co in Hco12, Hco23.
        unfold co, edge_relation, sample_co. set_solver.
      - intros write1 write2 write_event1 write_event2
          Hlookup1 Hlookup2 Hkind1 Hkind2 Hsame_loc Hneq.
        destruct (sample_lookup_cases write1 write_event1 Hlookup1)
          as [(-> & ->) | [(-> & ->) | (-> & ->)]];
        destruct (sample_lookup_cases write2 write_event2 Hlookup2)
          as [(-> & ->) | [(-> & ->) | (-> & ->)]];
        unfold co, edge_relation, sample_co; set_solver.
      - intros loc (eid & Hloc).
        unfold event_has_location in Hloc.
        apply bind_Some in Hloc as (ev & Hlookup & Hloc).
        destruct (sample_lookup_cases eid ev Hlookup)
          as [(-> & ->) | [(-> & ->) | (-> & ->)]];
        simpl in Hloc; assert (loc = 0) as -> by congruence;
        exists 0, 0%Z; reflexivity.
      - intros loc write1 write2
          (val1 & Hlookup1) (val2 & Hlookup2).
        destruct (sample_lookup_cases write1 (EInitWrite loc val1) Hlookup1)
          as [(-> & Hevent1) | [(-> & Hevent1) | (-> & Hevent1)]];
        destruct (sample_lookup_cases write2 (EInitWrite loc val2) Hlookup2)
          as [(-> & Hevent2) | [(-> & Hevent2) | (-> & Hevent2)]];
        try discriminate; done.
      - intros initial write loc write_event
          (val & Hinitial) Hwrite Hkind Hsame_loc Hneq.
        destruct (sample_lookup_cases initial (EInitWrite loc val) Hinitial)
          as [(-> & Hevent) | [(-> & Hevent) | (-> & Hevent)]];
          try discriminate.
        destruct (sample_lookup_cases write write_event Hwrite)
          as [(-> & ->) | [(-> & ->) | (-> & ->)]];
        unfold co, edge_relation, sample_co; set_solver.
    Qed.

    Definition cyclic_co : edge_set := {[(0, 1); (0, 2); (1, 2); (2, 1)]}.
    Definition missing_initial_events : event_structure := {[1 := first_write]}.
    Definition duplicate_initial_events : event_structure :=
      {[0 := init_write; 3 := EInitWrite 0 7%Z]}.
    Definition late_initial_events : event_structure := {[0 := init_write; 1 := first_write]}.
    Definition late_initial_co : edge_set := {[(1, 0)]}.

    Example malformed_coherence_orders :
      ~ co_wf sample_events cyclic_co /\
      ~ co_wf missing_initial_events (∅ : edge_set) /\
      ~ co_wf duplicate_initial_events (∅ : edge_set) /\
      ~ co_wf late_initial_events late_initial_co.
    Proof.
      assert (~ co_wf sample_events cyclic_co) as Hcycle.
      { intros Hwf.
        pose proof (co_wf_irreflexive sample_events cyclic_co Hwf)
          as Hirreflexive.
        pose proof (co_wf_transitive sample_events cyclic_co Hwf)
          as Htransitive.
        apply (Hirreflexive 1).
        eapply Htransitive with (write2 := 2);
          unfold co, edge_relation, cyclic_co; set_solver. }
      assert (~ co_wf missing_initial_events (∅ : edge_set)) as Hmissing.
      { intros Hwf.
        pose proof (co_wf_initial_exists missing_initial_events
          (∅ : edge_set) Hwf) as Hexists.
        assert (location_used missing_initial_events 0) as Hused.
        { exists 1. reflexivity. }
        destruct (Hexists 0 Hused) as (initial & val & Hlookup).
        unfold lookup_event, missing_initial_events in Hlookup.
        apply lookup_singleton_Some in Hlookup as [Heid Hevent].
        discriminate Hevent. }
      assert (~ co_wf duplicate_initial_events (∅ : edge_set)) as Hduplicate.
      { intros Hwf.
        pose proof (co_wf_initial_unique duplicate_initial_events
          (∅ : edge_set) Hwf) as Hunique.
        assert (0 = 3) as Heq.
        { eapply Hunique with (loc := 0).
          - exists 0%Z. reflexivity.
          - exists 7%Z. reflexivity. }
        lia. }
      assert (~ co_wf late_initial_events late_initial_co) as Hlate.
      { intros Hwf.
        pose proof (co_wf_initial_first late_initial_events
          late_initial_co Hwf) as Hfirst.
        assert (co late_initial_co 0 1) as Hco.
        { eapply Hfirst with (loc := 0) (write_event := first_write).
          - exists 0%Z. reflexivity.
          - reflexivity.
          - reflexivity.
          - exists 0. split; reflexivity.
          - lia. }
        unfold co, edge_relation, late_initial_co in Hco. set_solver. }
      tauto.
    Qed.
  End CoherenceOrderTests.

  Module FromReadTests.
    (** Writes [0], [1], and [2] form a coherence chain.  Read [3] reads
        from [0], while read [4] reads from [1]. *)
    Definition sample_rf : edge_set := {[(0, 3); (1, 4)]}.
    Definition sample_co : edge_set := {[(0, 1); (0, 2); (1, 2)]}.

    Example from_read_classification :
      fr sample_rf sample_co 3 1 /\
      fr sample_rf sample_co 3 2 /\
      fr sample_rf sample_co 4 2 /\
      ~ fr sample_rf sample_co 3 0 /\
      ~ fr sample_rf sample_co 4 0.
    Proof.
      unfold fr, rel_seq, rel_inverse, rf, co, edge_relation,
        sample_rf, sample_co. set_solver.
    Qed.
  End FromReadTests.

  Module InternalExternalTests.
    Definition init_write : event := EInitWrite 0 0%Z.
    Definition agent0_write : event := EAgent 0 1 (LMemory AccessWrite AccessOnce NotRmw 0 1%Z).
    Definition agent0_read : event := EAgent 0 2 (LMemory AccessRead AccessOnce NotRmw 0 1%Z).
    Definition agent0_later_write : event :=
      EAgent 0 3 (LMemory AccessWrite AccessOnce NotRmw 0 2%Z).
    Definition agent1_read : event := EAgent 1 0 (LMemory AccessRead AccessOnce NotRmw 0 1%Z).
    Definition agent1_write : event := EAgent 1 1 (LMemory AccessWrite AccessOnce NotRmw 0 3%Z).
    Definition agent0_initial_read : event :=
      EAgent 0 0 (LMemory AccessRead AccessOnce NotRmw 0 0%Z).

    Definition sample_events : event_structure := {[
      0 := init_write;
      1 := agent0_write;
      2 := agent0_read;
      3 := agent0_later_write;
      4 := agent1_read;
      5 := agent1_write;
      6 := agent0_initial_read
    ]}.

    Definition sample_rf : edge_set := {[(0, 6); (1, 2); (1, 4)]}.
    Definition sample_co : edge_set := {[(0, 1); (0, 3); (0, 5); (1, 3); (1, 5); (3, 5)]}.

    Example ordinary_internal_external_classification :
      rfi sample_events sample_rf 1 2 /\
      rfe sample_events sample_rf 1 4 /\
      coi sample_events sample_co 1 3 /\
      coe sample_events sample_co 3 5.
    Proof.
      assert (rfi sample_events sample_rf 1 2) as Hrfi.
      { split.
        - unfold rf, edge_relation, sample_rf. set_solver.
        - exists 0. split; reflexivity. }
      assert (rfe sample_events sample_rf 1 4) as Hrfe.
      { split.
        - unfold rf, edge_relation, sample_rf. set_solver.
        - intros (agent & Hagent0 & Hagent1).
          change (Some 0 = Some agent) in Hagent0.
          change (Some 1 = Some agent) in Hagent1. congruence. }
      assert (coi sample_events sample_co 1 3) as Hcoi.
      { split.
        - unfold co, edge_relation, sample_co. set_solver.
        - exists 0. split; reflexivity. }
      assert (coe sample_events sample_co 3 5) as Hcoe.
      { split.
        - unfold co, edge_relation, sample_co. set_solver.
        - intros (agent & Hagent0 & Hagent1).
          change (Some 0 = Some agent) in Hagent0.
          change (Some 1 = Some agent) in Hagent1. congruence. }
      split_and!; done.
    Qed.

    (** Although read [6] reads from the initial write, [fri] classifies the
        endpoints of [fr]: read [6] and write [1] both belong to agent 0. *)
    Example initial_write_and_fr_endpoint_classification :
      rfe sample_events sample_rf 0 6 /\
      coe sample_events sample_co 0 1 /\
      fri sample_events sample_rf sample_co 6 1 /\
      fre sample_events sample_rf sample_co 6 5.
    Proof.
      assert (rfe sample_events sample_rf 0 6) as Hrfe.
      { split.
        - unfold rf, edge_relation, sample_rf. set_solver.
        - intros (agent & Hinitial & Hagent).
          change (None = Some agent) in Hinitial. discriminate Hinitial. }
      assert (coe sample_events sample_co 0 1) as Hcoe.
      { split.
        - unfold co, edge_relation, sample_co. set_solver.
        - intros (agent & Hinitial & Hagent).
          change (None = Some agent) in Hinitial. discriminate Hinitial. }
      assert (fri sample_events sample_rf sample_co 6 1) as Hfri.
      { split.
        - unfold fr, rel_seq, rel_inverse, rf, co, edge_relation,
            sample_rf, sample_co.
          exists 0. split; set_solver.
        - exists 0. split; reflexivity. }
      assert (fre sample_events sample_rf sample_co 6 5) as Hfre.
      { split.
        - unfold fr, rel_seq, rel_inverse, rf, co, edge_relation,
            sample_rf, sample_co.
          exists 0. split; set_solver.
        - intros (agent & Hagent0 & Hagent1).
          change (Some 0 = Some agent) in Hagent0.
          change (Some 1 = Some agent) in Hagent1. congruence. }
      split_and!; done.
    Qed.
  End InternalExternalTests.

  Module BaseCoherenceTests.
    Definition first_write : event := EAgent 0 0 (LMemory AccessWrite AccessOnce NotRmw 0 1%Z).
    Definition second_write : event := EAgent 0 1 (LMemory AccessWrite AccessOnce NotRmw 0 2%Z).

    Definition sample_events : event_structure := {[1 := first_write; 2 := second_write]}.

    Example empty_execution_is_coherent :
      coherence empty_event_structure (∅ : edge_set) (∅ : edge_set).
    Proof.
      unfold coherence, rel_acyclic, rel_irreflexive.
      intros eid Hcycle.
      induction Hcycle as [source target Hedge |
        source middle target Hleft IHleft Hright IHright].
      - destruct Hedge as [Hpo_loc | Hcom].
        + destruct Hpo_loc as [Hpo Hsame_loc].
          destruct Hpo as (agent & index1 & index2 & label1 & label2 &
            Hlookup1 & Hlookup2 & Hlt).
          unfold lookup_event, empty_event_structure in Hlookup1.
          discriminate Hlookup1.
        + unfold com, rel_union in Hcom.
          destruct Hcom as [Hrf | [Hco | Hfr]].
          * unfold rf, edge_relation in Hrf. set_solver.
          * unfold co, edge_relation in Hco. set_solver.
          * unfold fr, rel_seq in Hfr.
            destruct Hfr as (write & Hrf & Hco).
            unfold rel_inverse, rf, edge_relation in Hrf. set_solver.
      - exact IHleft.
    Qed.

    Definition reversed_co : edge_set := {[(2, 1)]}.

    Example reversed_co_creates_a_coherence_cycle :
      ~ coherence sample_events (∅ : edge_set) reversed_co.
    Proof.
      intros Hcoherence.
      unfold coherence, rel_acyclic, rel_irreflexive in Hcoherence.
      apply (Hcoherence 1).
      eapply t_trans with (y := 2).
      - apply t_step. left. split.
        + exists 0, 0, 1,
            (LMemory AccessWrite AccessOnce NotRmw 0 1%Z),
            (LMemory AccessWrite AccessOnce NotRmw 0 2%Z).
          split_and!; try done. lia.
        + exists 0. split; reflexivity.
      - apply t_step. right. unfold com, rel_union. right. left.
        unfold co, edge_relation, reversed_co. set_solver.
    Qed.
  End BaseCoherenceTests.

End LkmmMemoryRelations.
