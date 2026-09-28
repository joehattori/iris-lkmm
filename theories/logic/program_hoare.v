From iris.proofmode Require Import proofmode.
From iris_lkmm.operational Require Import lkmm_machine.
From iris_lkmm.logic Require Export hoare adequacy.
From iris_lkmm.logic Require Import graph_judgment.

(** Whole-program specifications use the same initial resources, candidate
    quantification, agent WPs, and final extraction as completed adequacy. *)
Module LkmmProgramHoare.
  Export LkmmHoare LkmmAdequacy.
  Import LkmmGraphJudgment LkmmMachine.

  Inductive program_context := WholeProgram.

  Record program_result := ProgramResult {
    result_actions : list lkmm_action;
    result_state : lkmm_state
  }.

  Definition final_register (result : program_result) agent reg : option value :=
    thread ← result.(result_state).(lkmm_machine).(machine_core).(core_threads) !! agent;
    val ← thread.(thread_registers) !! reg;
    Some val.(reg_integer).

  (** Existential reachability from the program's fixed initial state.
      Unlike the Iris WP, both assertions here are ordinary propositions.
      A satisfied precondition requires an actual accepted completed run. *)
  Definition program_may (P : core_program) (Pre : Prop) (Post : program_result -> Prop) : Prop :=
    Pre -> exists actions final,
      lkmm_run P (initial_lkmm P) actions final /\
      lkmm_complete final /\ lkmm_program_graph_obligations final /\
      Post (ProgramResult actions final).

  (** Keep [?] after the entire triple: Iris's [? {{{ ... }}}] notation
      before the postcondition instead denotes [MaybeStuck]. *)
  Notation "'{{{' Pre } } } P {{{ x .. y , 'RET' pat ; Post } } } '?'" :=
    (program_may P Pre (fun result =>
      exists x, .. (exists y, result = pat /\ Post) ..))
    (at level 20, x closed binder, y closed binder,
     format "'[hv' {{{  '[' Pre  ']' } } }  '/  ' P  '/' {{{  '[' x  ..  y ,  RET  pat ;  '/' Post  ']' } } } ? ']'")
    : stdpp_scope.
  Notation "'{{{' Pre } } } P {{{ 'RET' pat ; Post } } } '?'" :=
    (program_may P Pre (fun result => result = pat /\ Post))
    (at level 20,
     format "'[hv' {{{  '[' Pre  ']' } } }  '/  ' P  '/' {{{  '[' RET  pat ;  '/' Post  ']' } } } ? ']'")
    : stdpp_scope.

  Section rules.
    Context `{!invGS Σ, !stateG Σ}.

    Global Instance whole_program_wp :
        Wp (iProp Σ) core_program program_result program_context :=
      fun _ E P Φ => program_wp P E (fun actions final => Φ (ProgramResult actions final)).

    (** The callback can own resources. Carry its later through a designated
        active agent, then recover it only after that agent has completed. *)
    Lemma program_wp_wand_later P E agent body Q Ψ :
      P.(program_agents) !! agent = Some body -> body <> SSkip ->
      program_wp P E Q -∗
      ▷ (∀ actions final, Q actions final -∗ Ψ (ProgramResult actions final)) -∗
      WP P @ WholeProgram; E {{ Ψ }}.
    Proof.
      intros Hagent Hbody. iIntros "Hwp HΨ" (γ) "Hinit".
      iMod ("Hwp" with "Hinit") as "Hwp".
      iModIntro. iIntros (G HG).
      iDestruct ("Hwp" $! G with "[]") as (Φ) "[Hwps Hfinish]"; first done.
      set (R := (∀ actions final, Q actions final -∗ Ψ (ProgramResult actions final))%I).
      iExists (fun other v => (Φ other v ∗ if decide (other = agent) then R else True)%I).
      iSplitL "Hwps HΨ".
      - iDestruct (big_sepM_delete _ _ agent with "Hwps") as "[Hagent Hwps]"; first done.
        iApply big_sepM_delete; first done. iSplitL "Hagent HΨ".
        + rewrite decide_True; last done.
          iApply (wp_frame_later with "Hagent HΨ").
          intros [[Hskip _] _]. by apply Hbody.
        + iApply (big_sepM_mono with "Hwps"). iIntros (other code Hlookup) "Hwp".
          apply lookup_delete_Some in Hlookup as [Hne _].
          rewrite decide_False; last congruence.
          iApply (wp_mono with "Hwp"). iIntros (v) "HΦ". by iFrame.
      - iIntros (actions final) "Hpos [Hstate Hposts]".
        iDestruct (big_sepM_delete _ _ agent with "Hposts") as "[Hagent Hposts]"; first done.
        iDestruct "Hagent" as (v) "(Hview & HΦ & HΨ)".
        rewrite decide_True; last done.
        iAssert (final_posts P Φ actions final) with "[Hview HΦ Hposts]" as "Hposts".
        { iApply big_sepM_delete; first done. iSplitL "Hview HΦ".
          - iExists v. iFrame.
          - iApply (big_sepM_mono with "Hposts").
            iIntros (other code Hlookup) "Hpost".
            iDestruct "Hpost" as (v') "[Hview [HΦ _]]". iExists v'. iFrame. }
        iMod ("Hfinish" with "Hpos [$Hstate $Hposts]") as "HQ".
        iModIntro. by iApply ("HΨ" with "HQ").
    Qed.

    Lemma program_wp_spec P agent body Q Ψ :
      P.(program_agents) !! agent = Some body -> body <> SSkip ->
      completed_program_wp P Q -∗
      ▷ (∀ actions final, ⌜Q actions final⌝ -∗ Ψ (ProgramResult actions final)) -∗
      WP P @ WholeProgram; ⊤ {{ Ψ }}.
    Proof. apply program_wp_wand_later. Qed.

    (** Pure outcomes continue to use the existing completed-program adequacy. *)
    Lemma program_wp_pure P Q :
      WP P @ WholeProgram; ⊤ {{ result, ⌜Q result.(result_actions) result.(result_state)⌝ }}
      ⊣⊢ completed_program_wp P Q.
    Proof. done. Qed.
  End rules.
End LkmmProgramHoare.
