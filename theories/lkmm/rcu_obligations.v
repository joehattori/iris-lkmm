From Stdlib Require Import Lia List ZArith.
From stdpp Require Import base tactics.
From iris_lkmm.lkmm Require Import rcu_graph.
Import ListNotations.
Open Scope Z_scope.
Local Opaque Z.add Z.sub Z.opp.

(** An independent, finite chain semantics for normal RCU ordering.

    Unlike [RcuGraph.rcu_order], the public definition at the bottom of this
    file is not a recursive relation grammar.  It is a list of concrete GP or
    inverse-RSCS atoms, adjacent atoms are connected by [rcu_link], and a
    signed counter records the outstanding grace-period obligation:

      GP contributes +1; inverse RSCS contributes -1.

    A nonempty linked chain is accepted exactly when its final balance is
    nonnegative.  Prefixes may be negative; this is essential for the CAT
    [rcu-rscsi ; rcu-link ; rcu-gp] case. *)
Module RcuObligations.
  Import RcuGraph.

  Inductive atom_kind := KGP | KRscs.

  Section GenericObligations.
    Context {A : Type}.
    Variable kind : A -> atom_kind.

    Fixpoint obligation_balance (xs : list A) : Z :=
      match xs with
      | [] => 0
      | x :: xs =>
          match kind x with
          | KGP => 1 + obligation_balance xs
          | KRscs => -1 + obligation_balance xs
          end
      end.

    Lemma obligation_balance_app xs ys :
      obligation_balance (xs ++ ys) =
        obligation_balance xs + obligation_balance ys.
    Proof.
      induction xs as [|x xs IH]; first done.
      change
        ((match kind x with
          | KGP => 1 + obligation_balance (xs ++ ys)
          | KRscs => -1 + obligation_balance (xs ++ ys)
          end) =
         (match kind x with
          | KGP => 1 + obligation_balance xs
          | KRscs => -1 + obligation_balance xs
          end) + obligation_balance ys).
      rewrite IH. destruct (kind x); lia.
    Qed.

    (** If a walk starting at nonnegative level [q] ends below zero, it
        crosses level zero at a [KRscs] atom. *)
    Lemma cross_down (q : Z) xs :
      0 <= q ->
      q + obligation_balance xs < 0 ->
      exists pre a post,
        xs = pre ++ a :: post /\
        kind a = KRscs /\
        q + obligation_balance pre = 0.
    Proof.
      induction xs as [|x xs IH] in q |- *; first (simpl; lia).
      destruct (kind x) eqn:Hx.
      - intros Hq Hneg.
        cbn [obligation_balance] in Hneg.
        rewrite Hx in Hneg. cbn in Hneg.
        assert (Hq' : 0 <= q + 1) by lia.
        assert (Hneg' : q + 1 + obligation_balance xs < 0).
        { replace (q + 1 + obligation_balance xs)
            with (q + (1 + obligation_balance xs)) by ring.
          done. }
        destruct (IH (q + 1) Hq' Hneg') as
          (pre & a & post & -> & Ha & Hpre).
        exists (x :: pre), a, post. cbn [obligation_balance].
        rewrite Hx. cbn.
        repeat split; try done.
        change (q + (1 + obligation_balance pre) = 0).
        replace (q + (1 + obligation_balance pre))
          with (q + 1 + obligation_balance pre) by ring.
        done.
      - intros Hq Hneg.
        destruct (Z.eq_dec q 0) as [-> | Hq0].
        + exists [], x, xs. cbn [obligation_balance].
          rewrite Hx. cbn. by repeat split.
        + assert (0 <= q - 1) by lia.
          cbn [obligation_balance] in Hneg.
          rewrite Hx in Hneg. cbn in Hneg.
          assert (Hstep : q - 1 + obligation_balance xs < 0).
          { replace (q - 1 + obligation_balance xs)
              with (q + (-1 + obligation_balance xs)) by ring.
            done. }
          destruct (IH (q - 1) ltac:(done) Hstep) as
            (pre & a & post & -> & Ha & Hpre).
          exists (x :: pre), a, post. cbn [obligation_balance].
          rewrite Hx. cbn.
          repeat split; try done.
          change (q + (-1 + obligation_balance pre) = 0).
          replace (q + (-1 + obligation_balance pre))
            with (q - 1 + obligation_balance pre) by ring.
          done.
    Qed.

    (** The dual crossing lemma, with [q] representing initial debt. *)
    Lemma cross_up (q : Z) xs :
      0 <= q ->
      - q + obligation_balance xs > 0 ->
      exists pre a post,
        xs = pre ++ a :: post /\
        kind a = KGP /\
        - q + obligation_balance pre = 0.
    Proof.
      induction xs as [|x xs IH] in q |- *; first (simpl; lia).
      destruct (kind x) eqn:Hx.
      - intros Hq Hpos.
        destruct (Z.eq_dec q 0) as [-> | Hq0].
        + exists [], x, xs. cbn [obligation_balance].
          rewrite Hx. cbn. by repeat split.
        + assert (0 <= q - 1) by lia.
          cbn [obligation_balance] in Hpos.
          rewrite Hx in Hpos. cbn in Hpos.
          assert (Hstep : - (q - 1) + obligation_balance xs > 0).
          { replace (- (q - 1) + obligation_balance xs)
              with (- q + (1 + obligation_balance xs)) by ring.
            done. }
          destruct (IH (q - 1) ltac:(done) Hstep) as
            (pre & a & post & -> & Ha & Hpre).
          exists (x :: pre), a, post. cbn [obligation_balance].
          rewrite Hx. cbn.
          repeat split; try done.
          change (- q + (1 + obligation_balance pre) = 0).
          replace (- q + (1 + obligation_balance pre))
            with (- (q - 1) + obligation_balance pre) by ring.
          done.
      - intros Hq Hpos.
        cbn [obligation_balance] in Hpos.
        rewrite Hx in Hpos. cbn in Hpos.
        assert (Hq' : 0 <= q + 1) by lia.
        assert (Hpos' : - (q + 1) + obligation_balance xs > 0).
        { replace (- (q + 1) + obligation_balance xs)
            with (- q + (-1 + obligation_balance xs)) by ring.
          done. }
        destruct (IH (q + 1) Hq' Hpos') as
          (pre & a & post & -> & Ha & Hpre).
        exists (x :: pre), a, post. cbn [obligation_balance].
        rewrite Hx. cbn.
        repeat split; try done.
        change (- q + (-1 + obligation_balance pre) = 0).
        replace (- q + (-1 + obligation_balance pre))
          with (- (q + 1) + obligation_balance pre) by ring.
        done.
    Qed.

    (** This grammar is used only as an internal proof bridge to the CAT
        recursion.  The independent public invariant is the counter on a
        linked list, not this derivation. *)
    Inductive obligation_derivation : list A -> Prop :=
    | OD_gp a :
        kind a = KGP ->
        obligation_derivation [a]
    | OD_gp_rscs a b :
        kind a = KGP -> kind b = KRscs ->
        obligation_derivation [a; b]
    | OD_rscs_gp a b :
        kind a = KRscs -> kind b = KGP ->
        obligation_derivation [a; b]
    | OD_gp_inner_rscs a xs b :
        kind a = KGP -> obligation_derivation xs -> kind b = KRscs ->
        obligation_derivation (a :: xs ++ [b])
    | OD_rscs_inner_gp a xs b :
        kind a = KRscs -> obligation_derivation xs -> kind b = KGP ->
        obligation_derivation (a :: xs ++ [b])
    | OD_join xs ys :
        obligation_derivation xs -> obligation_derivation ys ->
        obligation_derivation (xs ++ ys).

    Lemma obligation_derivation_nonempty xs :
      obligation_derivation xs -> xs <> [].
    Proof.
      induction 1; try discriminate.
      intros Happ. apply app_eq_nil in Happ as [Hxs Hys].
      naive_solver.
    Qed.

    Lemma obligation_derivation_sound xs :
      obligation_derivation xs -> 0 <= obligation_balance xs.
    Proof.
      induction 1 as
        [a Ha
        | a b Ha Hb
        | a b Ha Hb
        | a xs b Ha Hxs IH Hb
        | a xs b Ha Hxs IH Hb
        | xs ys Hxs IHxs Hys IHys].
      - change (0 <=
          match kind a with KGP => 1 | KRscs => -1 end).
        by rewrite Ha.
      - change (0 <=
          match kind a with
          | KGP =>
              1 + match kind b with KGP => 1 | KRscs => -1 end
          | KRscs =>
              -1 + match kind b with KGP => 1 | KRscs => -1 end
          end).
        rewrite Ha, Hb. lia.
      - change (0 <=
          match kind a with
          | KGP =>
              1 + match kind b with KGP => 1 | KRscs => -1 end
          | KRscs =>
              -1 + match kind b with KGP => 1 | KRscs => -1 end
          end).
        rewrite Ha, Hb. lia.
      - change (0 <=
          match kind a with
          | KGP => 1 + obligation_balance (xs ++ [b])
          | KRscs => -1 + obligation_balance (xs ++ [b])
          end).
        rewrite Ha, obligation_balance_app.
        change (0 <= 1 + (obligation_balance xs +
          match kind b with KGP => 1 | KRscs => -1 end)).
        rewrite Hb. lia.
      - change (0 <=
          match kind a with
          | KGP => 1 + obligation_balance (xs ++ [b])
          | KRscs => -1 + obligation_balance (xs ++ [b])
          end).
        rewrite Ha, obligation_balance_app.
        change (0 <= -1 + (obligation_balance xs +
          match kind b with KGP => 1 | KRscs => -1 end)).
        rewrite Hb. lia.
      - rewrite obligation_balance_app. lia.
    Qed.

    Lemma obligation_derivation_complete_bounded (n : nat) xs :
      (length xs <= n)%nat ->
      xs <> [] ->
      0 <= obligation_balance xs ->
      obligation_derivation xs.
    Proof.
      induction n as [|n IH] in xs |- *.
      - destruct xs as [|a xs].
        + intros _ Hne. exfalso. by apply Hne.
        + simpl. lia.
      - destruct xs as [|a tail]; first done.
        intros Hlen _ Hbal.
        destruct (kind a) eqn:Ha.
        + destruct tail as [|t tail].
          { apply OD_gp. done. }
          destruct (Z_le_dec 0 (obligation_balance (t :: tail)))
            as [Htail | Htail].
          * eapply OD_join with (xs := [a]) (ys := t :: tail).
            -- by apply OD_gp.
            -- apply IH; last done.
               ++ by apply (proj2
                    (Nat.succ_le_mono (length (t :: tail)) n)).
               ++ discriminate.
          * change (0 <=
              match kind a with
              | KGP => 1 + obligation_balance (t :: tail)
              | KRscs => -1 + obligation_balance (t :: tail)
              end) in Hbal.
            rewrite Ha in Hbal.
            assert (Hminus : obligation_balance (t :: tail) = -1) by lia.
            destruct (cross_down 0 (t :: tail)) as
              (pre & b & post & Hsplit & Hb & Hpre); [lia | lia |].
            assert (Hpost : obligation_balance post = 0).
            { rewrite Hsplit, obligation_balance_app in Hminus.
              change (obligation_balance pre +
                match kind b with
                | KGP => 1 + obligation_balance post
                | KRscs => -1 + obligation_balance post
                end = -1) in Hminus.
              rewrite Hb in Hminus.
              change (obligation_balance pre = 0) in Hpre.
              lia. }
            assert (Htaillen : (length (t :: tail) <= n)%nat).
            { by apply (proj2
                (Nat.succ_le_mono (length (t :: tail)) n)). }
            rewrite Hsplit, length_app in Htaillen. simpl in Htaillen.
            assert (Hprelen : (length pre <= n)%nat) by lia.
            assert (Hpostlen : (length post <= n)%nat) by lia.
            assert (Hblock : obligation_derivation (a :: pre ++ [b])).
            { destruct pre as [|p pre].
              - simpl. by apply OD_gp_rscs.
              - apply OD_gp_inner_rscs; try done.
                apply IH; try done. lia. }
            rewrite Hsplit.
            replace (a :: pre ++ b :: post)
              with ((a :: pre ++ [b]) ++ post).
            2: { rewrite <- app_comm_cons. f_equal.
                 exact (eq_sym (app_assoc pre [b] post)). }
            destruct post as [|p post].
            { by rewrite app_nil_r. }
            apply OD_join; first done.
            apply IH; try done. lia.
        + change (0 <=
            match kind a with
            | KGP => 1 + obligation_balance tail
            | KRscs => -1 + obligation_balance tail
            end) in Hbal.
          rewrite Ha in Hbal.
          assert (Htail : obligation_balance tail > 0) by lia.
          destruct (cross_up 0 tail) as
            (pre & b & post & Hsplit & Hb & Hpre); [lia | done |].
          assert (Hpost : 0 <= obligation_balance post).
          { rewrite Hsplit, obligation_balance_app in Hbal.
            change (0 <= -1 + (obligation_balance pre +
              match kind b with
              | KGP => 1 + obligation_balance post
              | KRscs => -1 + obligation_balance post
              end)) in Hbal.
            rewrite Hb in Hbal.
            change (obligation_balance pre = 0) in Hpre.
            lia. }
          assert (Htaillen : (length tail <= n)%nat).
          { by apply (proj2 (Nat.succ_le_mono (length tail) n)). }
          rewrite Hsplit, length_app in Htaillen. simpl in Htaillen.
          assert (Hprelen : (length pre <= n)%nat) by lia.
          assert (Hpostlen : (length post <= n)%nat) by lia.
          assert (Hblock : obligation_derivation (a :: pre ++ [b])).
          { destruct pre as [|p pre].
            - simpl. by apply OD_rscs_gp.
            - apply OD_rscs_inner_gp; try done.
              apply IH; try done. lia. }
          rewrite Hsplit.
          replace (a :: pre ++ b :: post)
            with ((a :: pre ++ [b]) ++ post).
          2: { rewrite <- app_comm_cons. f_equal.
               exact (eq_sym (app_assoc pre [b] post)). }
          destruct post as [|p post].
          { by rewrite app_nil_r. }
          apply OD_join; first done.
          apply IH; done.
    Qed.

    Theorem obligation_derivation_iff xs :
      obligation_derivation xs <->
      xs <> [] /\ 0 <= obligation_balance xs.
    Proof.
      split.
      - intros H. split.
        + by apply obligation_derivation_nonempty.
        + by apply obligation_derivation_sound.
      - intros [Hne Hbal].
        apply (obligation_derivation_complete_bounded (length xs) xs);
          done.
    Qed.
  End GenericObligations.

  Inductive rcu_atom :=
  | AtomGp (g : event_id)
  | AtomRscs (u l : event_id).

  Definition atom_kind_of (a : rcu_atom) : atom_kind :=
    match a with AtomGp _ => KGP | AtomRscs _ _ => KRscs end.

  Definition atom_start (a : rcu_atom) : event_id :=
    match a with AtomGp g => g | AtomRscs u _ => u end.

  Definition atom_end (a : rcu_atom) : event_id :=
    match a with AtomGp g => g | AtomRscs _ l => l end.

  Definition atom_valid (G : graph) (a : rcu_atom) : Prop :=
    match a with
    | AtomGp g => is_gp G g
    | AtomRscs u l => rcu_rscsi G u l
    end.

  (** A finite, nonempty sequence of valid atoms whose adjacent endpoints are
      connected by [rcu_link]. *)
  Inductive linked_chain (G : graph) : list rcu_atom -> event_id -> event_id -> Prop :=
  | Linked_one a :
      atom_valid G a ->
      linked_chain G [a] (atom_start a) (atom_end a)
  (** [Linked_cons a atoms x y] prepends the atom [a] to the existing tail
      [atoms].  In the premise [linked_chain G atoms x y], [x] is the start
      of that tail (and hence the junction point), while [y] is both the
      tail's end and the resulting chain's end.  The [rcu_link] premise
      connects [atom_end a] to [x], so the resulting chain starts at
      [atom_start a] and ends at [y]. *)
  | Linked_cons a atoms x y :
      atom_valid G a ->
      linked_chain G atoms x y ->
      rcu_link G (atom_end a) x ->
      linked_chain G (a :: atoms) (atom_start a) y.

  Definition chain_balance : list rcu_atom -> Z := obligation_balance atom_kind_of.

  (** The independent chain/obligation semantics.  This definition mentions
      neither [rcu_order] nor an isomorphic recursive derivation. *)
  Definition rcu_chain_order (G : graph) (x y : event_id) : Prop :=
    exists atoms,
      linked_chain G atoms x y /\
      0 <= chain_balance atoms.

  Lemma linked_chain_nonempty G atoms x y :
    linked_chain G atoms x y -> atoms <> [].
  Proof. induction 1; discriminate. Qed.

  Lemma linked_chain_prepend G a atoms x y :
    atom_valid G a ->
    linked_chain G atoms x y ->
    rcu_link G (atom_end a) x ->
    linked_chain G (a :: atoms) (atom_start a) y.
  Proof. intros. by eapply Linked_cons. Qed.

  Lemma linked_chain_append G atoms x y last :
    linked_chain G atoms x y ->
    atom_valid G last ->
    rcu_link G y (atom_start last) ->
    linked_chain G (atoms ++ [last]) x (atom_end last).
  Proof.
    intros Hchain Hvalid Hlink.
    induction Hchain as
      [first Hfirst
      | first rest rx ry Hfirst Hrest IH Hfirstlink].
    - simpl. eapply Linked_cons with (x := atom_start last); try done.
      by apply Linked_one.
    - simpl. eapply Linked_cons; try done.
      by apply IH.
  Qed.

  Lemma linked_chain_join G left right x y z w :
    linked_chain G left x y ->
    linked_chain G right z w ->
    rcu_link G y z ->
    linked_chain G (left ++ right) x w.
  Proof.
    intros Hleft Hright Hlink.
    induction Hleft as
      [first Hfirst
      | first rest rx ry Hfirst Hrest IH Hfirstlink].
    - simpl. eapply Linked_cons with (x := z); done.
    - simpl. eapply Linked_cons with (x := rx); try done.
      by apply IH.
  Qed.

  Lemma linked_chain_one_inv G a x y :
    linked_chain G [a] x y ->
    atom_valid G a /\ x = atom_start a /\ y = atom_end a.
  Proof.
    intros Hchain. inversion Hchain; subst.
    - naive_solver.
    - match goal with H : linked_chain _ [] _ _ |- _ => inversion H end.
  Qed.

  Lemma linked_chain_cons_inv G a rest x y :
    rest <> [] ->
    linked_chain G (a :: rest) x y ->
    atom_valid G a /\ x = atom_start a /\
    exists z, linked_chain G rest z y /\ rcu_link G (atom_end a) z.
  Proof.
    intros Hne Hchain. inversion Hchain; subst.
    - exfalso. by apply Hne.
    - repeat split; try done.
      eexists. split; eassumption.
  Qed.

  Lemma linked_chain_app_inv G left right x y :
    left <> [] ->
    right <> [] ->
    linked_chain G (left ++ right) x y ->
    exists m n,
      linked_chain G left x m /\
      linked_chain G right n y /\
      rcu_link G m n.
  Proof.
    induction left as [|a left IH] in x |- *; first done.
    intros _ Hright Hchain.
    destruct left as [|b left].
    - simpl in Hchain.
      destruct (linked_chain_cons_inv G a right x y Hright Hchain)
        as (Hvalid & -> & n & Hrightchain & Hlink).
      exists (atom_end a), n. repeat split; try done.
      by apply Linked_one.
    - change ((a :: b :: left) ++ right)
        with (a :: ((b :: left) ++ right)) in Hchain.
      assert (Htailne : (b :: left) ++ right <> []) by discriminate.
      destruct (linked_chain_cons_inv G a ((b :: left) ++ right) x y
          Htailne Hchain)
        as (Hvalid & -> & z & Htailchain & Hfirstlink).
      destruct (IH z ltac:(discriminate) Hright Htailchain)
        as (m & n & Hleftchain & Hrightchain & Hboundary).
      exists m, n. repeat split; try done.
      by eapply Linked_cons.
  Qed.

  Lemma linked_chain_snoc_inv G prefix last x y :
    prefix <> [] ->
    linked_chain G (prefix ++ [last]) x y ->
    exists m,
      linked_chain G prefix x m /\
      atom_valid G last /\
      rcu_link G m (atom_start last) /\
      y = atom_end last.
  Proof.
    intros Hprefix Hchain.
    destruct (linked_chain_app_inv G prefix [last] x y
        Hprefix ltac:(discriminate) Hchain)
      as (m & n & Hpre & Hlast & Hlink).
    destruct (linked_chain_one_inv G last n y Hlast)
      as (Hvalid & -> & ->).
    exists m. repeat split; done.
  Qed.

  Lemma rcu_order_chain_sound G x y :
    rcu_order G x y -> rcu_chain_order G x y.
  Proof.
    intros Horder. induction Horder.
    - exists [AtomGp g]. split.
      + by constructor.
      + cbn [chain_balance obligation_balance atom_kind_of]. lia.
    - exists [AtomGp g; AtomRscs u l]. split.
      + eapply Linked_cons with (x := u); try done.
        by apply Linked_one.
      + cbn [chain_balance obligation_balance atom_kind_of]. lia.
    - exists [AtomRscs u l; AtomGp g]. split.
      + eapply Linked_cons with (x := g); try done.
        by apply Linked_one.
      + cbn [chain_balance obligation_balance atom_kind_of]. lia.
    - destruct IHHorder as (atoms & Hchain & Hbal).
      exists ((AtomGp g :: atoms) ++ [AtomRscs u l]). split.
      + eapply linked_chain_append; try done.
        by eapply linked_chain_prepend.
      + unfold chain_balance.
        unfold chain_balance in Hbal.
        rewrite obligation_balance_app.
        change (0 <=
          (1 + obligation_balance atom_kind_of atoms) + -1).
        lia.
    - destruct IHHorder as (atoms & Hchain & Hbal).
      exists ((AtomRscs u l :: atoms) ++ [AtomGp g]). split.
      + eapply linked_chain_append; try done.
        by eapply linked_chain_prepend.
      + unfold chain_balance.
        unfold chain_balance in Hbal.
        rewrite obligation_balance_app.
        change (0 <=
          (-1 + obligation_balance atom_kind_of atoms) + 1).
        lia.
    - destruct IHHorder1 as (left & Hleft & Hbal1).
      destruct IHHorder2 as (right & Hright & Hbal2).
      exists (left ++ right). split.
      + by eapply linked_chain_join.
      + unfold chain_balance in *. rewrite obligation_balance_app. lia.
  Qed.

  Lemma obligation_derivation_linked_order G atoms x y :
    obligation_derivation atom_kind_of atoms ->
    linked_chain G atoms x y ->
    rcu_order G x y.
  Proof.
    intros Hder. induction Hder as
      [a Ha
      | a b Ha Hb
      | a b Ha Hb
      | a inner b Ha Hinner IH Hb
      | a inner b Ha Hinner IH Hb
      | left right Hleft IHleft Hright IHright]
      in x, y |- *; intros Hchain.
    - destruct (linked_chain_one_inv G a x y Hchain)
        as (Hvalid & -> & ->).
      destruct a as [g | u l]; cbn in Ha; try discriminate.
      by apply RO_gp.
    - destruct a as [g | u1 l1]; cbn in Ha; try discriminate.
      destruct b as [g2 | u l]; cbn in Hb; try discriminate.
      destruct (linked_chain_app_inv G [AtomGp g] [AtomRscs u l] x y
          ltac:(discriminate) ltac:(discriminate) Hchain)
        as (m & n & Hfirst & Hsecond & Hlink).
      destruct (linked_chain_one_inv G (AtomGp g) x m Hfirst)
        as (Hgp & -> & ->).
      destruct (linked_chain_one_inv G (AtomRscs u l) n y Hsecond)
        as (Hcs & -> & ->).
      cbn in Hgp, Hcs, Hlink.
      by apply RO_gp_rscs with u.
    - destruct a as [g1 | u l]; cbn in Ha; try discriminate.
      destruct b as [g | u2 l2]; cbn in Hb; try discriminate.
      destruct (linked_chain_app_inv G [AtomRscs u l] [AtomGp g] x y
          ltac:(discriminate) ltac:(discriminate) Hchain)
        as (m & n & Hfirst & Hsecond & Hlink).
      destruct (linked_chain_one_inv G (AtomRscs u l) x m Hfirst)
        as (Hcs & -> & ->).
      destruct (linked_chain_one_inv G (AtomGp g) n y Hsecond)
        as (Hgp & -> & ->).
      cbn in Hgp, Hcs, Hlink.
      by apply RO_rscs_gp with l.
    - destruct a as [g | u1 l1]; cbn in Ha; try discriminate.
      destruct b as [g2 | u l]; cbn in Hb; try discriminate.
      assert (Hinnerne : inner <> []).
      { by apply (obligation_derivation_nonempty atom_kind_of inner Hinner). }
      assert (Hprefixne : AtomGp g :: inner <> []) by discriminate.
      change (linked_chain G ((AtomGp g :: inner) ++ [AtomRscs u l])
          x y) in Hchain.
      destruct (linked_chain_snoc_inv G (AtomGp g :: inner)
          (AtomRscs u l) x y Hprefixne Hchain)
        as (m & Hprefix & Hcs & Hlastlink & ->).
      destruct (linked_chain_cons_inv G (AtomGp g) inner x m
          Hinnerne Hprefix)
        as (Hgp & -> & z & Hinnerchain & Hfirstlink).
      cbn in Hgp, Hcs, Hfirstlink, Hlastlink.
      eapply RO_gp_inner_rscs with (x := z) (y := m) (u := u);
        try done.
      by apply IH.
    - destruct a as [g1 | u l]; cbn in Ha; try discriminate.
      destruct b as [g | u2 l2]; cbn in Hb; try discriminate.
      assert (Hinnerne : inner <> []).
      { by apply (obligation_derivation_nonempty atom_kind_of inner Hinner). }
      assert (Hprefixne : AtomRscs u l :: inner <> []) by discriminate.
      change (linked_chain G ((AtomRscs u l :: inner) ++ [AtomGp g])
          x y) in Hchain.
      destruct (linked_chain_snoc_inv G (AtomRscs u l :: inner)
          (AtomGp g) x y Hprefixne Hchain)
        as (m & Hprefix & Hgp & Hlastlink & ->).
      destruct (linked_chain_cons_inv G (AtomRscs u l) inner x m
          Hinnerne Hprefix)
        as (Hcs & -> & z & Hinnerchain & Hfirstlink).
      cbn in Hgp, Hcs, Hfirstlink, Hlastlink.
      eapply RO_rscs_inner_gp with (l := l) (x := z) (y := m);
        try done.
      by apply IH.
    - assert (Hleftne : left <> []).
      { by apply (obligation_derivation_nonempty atom_kind_of left Hleft). }
      assert (Hrightne : right <> []).
      { by apply (obligation_derivation_nonempty atom_kind_of right Hright). }
      destruct (linked_chain_app_inv G left right x y
          Hleftne Hrightne Hchain)
        as (m & n & Hleftchain & Hrightchain & Hlink).
      eapply RO_join; [by apply IHleft | done | by apply IHright].
  Qed.

  Lemma rcu_chain_order_complete G x y :
    rcu_chain_order G x y -> rcu_order G x y.
  Proof.
    intros (atoms & Hchain & Hbalance).
    apply (obligation_derivation_linked_order G atoms x y); last done.
    apply (proj2 (obligation_derivation_iff atom_kind_of atoms)).
    split; last done.
    by eapply linked_chain_nonempty.
  Qed.

  Lemma rcu_chain_order_join G x y z w :
    rcu_chain_order G x y ->
    rcu_link G y z ->
    rcu_chain_order G z w ->
    rcu_chain_order G x w.
  Proof.
    intros (left & Hleft & Hbal1) Hlink
      (right & Hright & Hbal2).
    exists (left ++ right). split.
    - by eapply linked_chain_join.
    - unfold chain_balance in *. rewrite obligation_balance_app. lia.
  Qed.

  Theorem rcu_order_chain_equiv G x y :
    rcu_order G x y <-> rcu_chain_order G x y.
  Proof.
    split.
    - apply rcu_order_chain_sound.
    - apply rcu_chain_order_complete.
  Qed.

End RcuObligations.
