From Stdlib Require Import List.
From iris.base_logic.lib Require Import fancy_updates.
From iris.proofmode Require Import proofmode.
From iris_lkmm.operational Require Import lkmm_machine lkmm_coupled.
From iris_lkmm.logic Require Import graph_correspondence state_interp wp.
From iris_lkmm.examples Require Import graph_correspondence_examples.
Import ListNotations.

Module WpBodyExamples.
  Import LkmmMachine LkmmCoupled LkmmGraphCorrespondence LkmmStateInterp LkmmWp.
  Module GP := GraphCorrespondenceExamples.GpState.

  Definition sync_view := ThreadView (initial_thread SSynchronizeRcu) 0 [].

  (** Even an empty captured set changes which half of synchronization runs. *)
  Example begin_distinguishes_local_gp_phases suffix final :
    project_coupled_thread (CoupledExecutionPosition [] GP.before
      (CoupledMachineAction (BeginGp 0) :: suffix) final) 0 =
      Some (CoupledThreadView sync_view None) /\
    project_coupled_thread (CoupledExecutionPosition [CoupledMachineAction (BeginGp 0)]
      GP.waiting suffix final) 0 = Some (CoupledThreadView sync_view (Some [])) /\
    CoupledThreadView sync_view None <> CoupledThreadView sync_view (Some []).
  Proof. split; first reflexivity. split; first reflexivity. discriminate. Qed.

  (** A finished thread still owes its resource postcondition, independently
      of the supplied recursive function. *)
  Example terminal_body_requires_postcondition `{!invGS Σ, !stateG Σ}
      P G γ recurse E agent regs index actions (Φ : coupled_thread_view -> iProp Σ) :
    let v := CoupledThreadView (ThreadView (ThreadState SSkip [] regs) index actions) None in
    wp_body P G γ recurse E agent v Φ ⊣⊢ |={E}=> Φ v.
  Proof. reflexivity. Qed.
End WpBodyExamples.
