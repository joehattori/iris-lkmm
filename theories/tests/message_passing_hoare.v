From Stdlib Require Import List Lia.
From iris.proofmode Require Import proofmode.
From iris_lkmm.lang Require Import candidate_renaming.
From iris_lkmm.operational Require Import lkmm_machine.
From iris_lkmm.logic Require Import program_hoare wp_publication.
From iris_lkmm.examples Require Import message_passing_code message_passing_wp.
From iris_lkmm.tests Require Import message_passing_allowed.
Import ListNotations.

(** Whole-test triples for the four message-passing variants.
    Initial memory (data = flag = 0) is part of each Core program. Trailing
    [?] triples give completed execution witnesses for final-register outcomes;
    the release/acquire claim is refuted using the existing Iris adequacy proof. *)
Module MessagePassingHoare.
  Import LkmmProgramHoare LkmmWpPublication MessagePassingCode MessagePassingWp.
  Import LkmmMachine LkmmCandidateRenaming.
  Module Allowed := MessagePassingAllowed.

  Definition registers_are result r0 r1 : Prop :=
    final_register result 1 0 = Some r0 /\ final_register result 1 1 = Some r1.

  (** Receipts connect the actual final registers to the generated reads. *)
  Definition reads_result lm actions final : Prop :=
    exists r0 r1 flag_read data_read,
      registers_are (ProgramResult actions final) r0 r1 /\
      lookup_event final.(lkmm_machine).(machine_core).(core_events) flag_read =
        Some (Allowed.flag_read lm r0) /\
      lookup_event final.(lkmm_machine).(machine_core).(core_events) data_read =
        Some (Allowed.data_read r1).

  (** The exact final registers in the original Iris publication theorem
      imply the register notation used by the litmus specification. *)
  Lemma publication_result actions final :
    mp_result actions final ->
    exists r0 r1, registers_are (ProgramResult actions final) r0 r1 /\
      (r0 = 1%Z -> r1 = 1%Z).
  Proof.
    intros (thread & r0 & r1 & Hthread & Hr0 & Hr1 & Hresult).
    exists r0.(reg_integer), r1.(reg_integer). split; last done.
    by rewrite /registers_are /final_register /= Hthread /= Hr0 Hr1.
  Qed.

  Section proofs.
    Context `{!invGS Σ, !stateG Σ}.

    Lemma reads_closed sm lm :
      ⊢ completed_program_wp (program sm lm) (reads_result lm).
    Proof.
      iIntros (γ) "Hinit".
      iMod (initial_shared with "Hinit") as "#Hshared".
      iModIntro. iIntros (G HG).
      iExists (post sm lm G γ). iSplitL.
      - by iApply message_passing_wps.
      - iIntros (actions final) "_ [Hstate Hposts]".
        iDestruct (big_sepM_lookup _ _ 1 with "Hposts") as "Hconsumer"; first reflexivity.
        iDestruct "Hconsumer" as (v) "[%Hview Hconsumer]".
        iDestruct "Hconsumer" as (r0 r1) "(%Hregisters & Hflag & Hdata)".
        iDestruct "Hflag" as (flag_read flag_source) "[Hflag _]".
        iDestruct "Hdata" as (data_read data_source) "[Hdata _]".
        iDestruct (state_interp_event with "Hstate Hflag") as %Hflag.
        iDestruct (state_interp_event with "Hstate Hdata") as %Hdata.
        iApply fupd_mask_intro_discard; first set_solver. iPureIntro.
        exists r0.(reg_integer), r1.(reg_integer), flag_read, data_read.
        split; last done.
        destruct Hregisters as [Hr0 Hr1].
        pose proof (lookup_lkmm_thread_view_lookup _ _ _ Hview) as Hthread.
        by rewrite /registers_are /final_register /= Hthread /= Hr0 Hr1.
    Qed.

  End proofs.

  Lemma reads_adequate sm lm actions final :
    lkmm_run (program sm lm) (initial_lkmm (program sm lm)) actions final ->
    lkmm_complete final -> lkmm_program_graph_obligations final ->
    reads_result lm actions final.
  Proof.
    apply (wp_adequacy (Σ := mpΣ)). intros Hinv. apply reads_closed.
  Qed.

  (** Completeness preserves event labels. The receipt theorem above makes
      those witnessed read values observable in the final registers. *)
  Lemma bad_outcome_registers sm lm actions final :
    lkmm_run (program sm lm) (initial_lkmm (program sm lm)) actions final ->
    lkmm_complete final -> lkmm_program_graph_obligations final ->
    Allowed.bad_outcome lm (lkmm_candidate final) ->
    registers_are (ProgramResult actions final) 1%Z 0%Z.
  Proof.
    intros Hrun Hcomplete Hobligations (c' & d' & Hc' & Hd').
    destruct (reads_adequate _ _ _ _ Hrun Hcomplete Hobligations)
      as (r0 & r1 & c & d & Hregs & Hc & Hd).
    destruct (lkmm_run_soundness _ _ _ Hrun Hcomplete Hobligations) as [Hgraph _].
    destruct (program_graph_wf _ _ Hgraph) as (Hwf & _).
    destruct (lkmm_complete_generated_matches _ Hcomplete) as [Hevents _].
    rewrite Hevents in Hc, Hd.
    assert (c = c') as -> by (eapply Hwf; [exact Hc | exact Hc']).
    assert (d = d') as -> by (eapply Hwf; [exact Hd | exact Hd']).
    rewrite Hc' in Hc. rewrite Hd' in Hd.
    unfold Allowed.flag_read in Hc. unfold Allowed.data_read in Hd.
    injection Hc as <-. injection Hd as <-. done.
  Qed.

  Lemma mp_weakened_possible sm lm :
    sm = StoreOnce \/ lm = LoadOnce ->
    {{{ True }}} program sm lm
    {{{ result, RET result; registers_are result 1%Z 0%Z }}}?.
  Proof.
    intros Hweak _.
    destruct (Allowed.mp_weakened_allowed sm lm Hweak)
      as (G & Hgraph & (c & d & Hc & Hd) & Hconsistent).
    destruct (lkmm_run_completeness _ _ Hgraph Hconsistent)
      as (actions & final & f & Hrun & Hcomplete & Hobligations & Hrename).
    exists actions, final. split; first done. split; first done. split; first done.
    exists (ProgramResult actions final). split; first done.
    eapply bad_outcome_registers; [exact Hrun | done | done |].
    exists (f c), (f d). split;
      eapply (renaming_lookup _ _ _ (candidate_renaming_events _ _ _ Hrename)); done.
  Qed.

  (** The three weaker variants admit the final-register outcome (1,0). *)
  Theorem mp_once_once_possible :
    {{{ True }}} program StoreOnce LoadOnce
    {{{ result, RET result; registers_are result 1%Z 0%Z }}}?.
  Proof. apply mp_weakened_possible. by left. Qed.

  Theorem mp_release_once_possible :
    {{{ True }}} program StoreRelease LoadOnce
    {{{ result, RET result; registers_are result 1%Z 0%Z }}}?.
  Proof. apply mp_weakened_possible. by right. Qed.

  Theorem mp_once_acquire_possible :
    {{{ True }}} program StoreOnce LoadAcquire
    {{{ result, RET result; registers_are result 1%Z 0%Z }}}?.
  Proof. apply mp_weakened_possible. by left. Qed.

  (** The fixed-RET form names the same concrete trace and final state.
      It cannot silently pick a different result after the witness is chosen. *)
  Example mp_once_once_fixed_witness :
    exists result,
      {{{ True }}} program StoreOnce LoadOnce
      {{{ RET result; registers_are result 1%Z 0%Z }}}?.
  Proof.
    destruct (mp_once_once_possible I) as (actions & final & Hrun & Hcomplete &
      Hobligations & result & <- & Hregisters).
    exists (ProgramResult actions final). intros _.
    exists actions, final. split_and!; done.
  Qed.

  (** Existential postcondition binders use their witnessed return value. *)
  Example mp_once_once_bound_values :
    {{{ True }}} program StoreOnce LoadOnce
    {{{ result r0 r1, RET result;
      registers_are result r0 r1 /\ r0 = 1%Z /\ r1 = 0%Z }}}?.
  Proof.
    intros _.
    destruct (mp_once_once_possible I) as (actions & final & Hrun & Hcomplete &
      Hobligations & result & <- & Hregisters).
    exists actions, final. split; first done. split; first done. split; first done.
    exists (ProgramResult actions final), 1%Z, 0%Z. split_and!; done.
  Qed.

  (** The forbidden outcome follows directly from the existing Iris
      release/acquire adequacy theorem. *)
  Theorem mp_release_acquire_never actions final :
    lkmm_run (program StoreRelease LoadAcquire)
      (initial_lkmm (program StoreRelease LoadAcquire)) actions final ->
    lkmm_complete final -> lkmm_program_graph_obligations final ->
    ~ registers_are (ProgramResult actions final) 1%Z 0%Z.
  Proof.
    intros Hrun Hcomplete Hobligations.
    destruct (publication_result _ _
      (mp_release_acquire_adequate _ _ Hrun Hcomplete Hobligations))
      as (r0 & r1 & Hregisters & Hpublication).
    unfold registers_are in *. naive_solver lia.
  Qed.

  Theorem mp_release_acquire_not_possible :
    ~ ({{{ True }}} program StoreRelease LoadAcquire
       {{{ result, RET result; registers_are result 1%Z 0%Z }}}?).
  Proof.
    intros Hpossible.
    destruct (Hpossible I) as (actions & final & Hrun & Hcomplete & Hobligations &
      result & <- & Hregisters).
    exact (mp_release_acquire_never _ _ Hrun Hcomplete Hobligations Hregisters).
  Qed.
End MessagePassingHoare.
