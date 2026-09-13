From Stdlib Require Import List.
From iris.base_logic.lib Require Import fancy_updates.
From iris.proofmode Require Import proofmode.
From iris_lkmm.operational Require Import lkmm_machine.
From iris_lkmm.logic Require Import graph_correspondence state_interp.
Import ListNotations.

Module LkmmWp.
  Import LkmmMachine LkmmGraphCorrespondence LkmmStateInterp.

  Section wp.
    Context `{!invGS Σ, !stateG Σ}.

    (** One layer of the per-agent WP, with [P], [G], and [γ] fixed for
        recursive calls. All accepted schedules of this local view are
        quantified over. Builder and other-agent steps are handled by the
        surrounding execution; this body handles the scheduled agent.

        The execution supplies the state interpretation and thread token.
        Reader and pending-GP tokens must come from the proof's resources
        and pass to the continuation when still owned. *)
    Definition wp_body (P : core_program) (G : core_candidate) (γ : state_names)
        (recurse : coPset -d> agent_id -d> coupled_thread_view -d>
          (coupled_thread_view -d> iPropO Σ) -d> iPropO Σ) :
        coPset -d> agent_id -d> coupled_thread_view -d>
          (coupled_thread_view -d> iPropO Σ) -d> iPropO Σ := λ E agent v Φ,
      match v.(coupled_view_core).(view_thread).(thread_statement),
          v.(coupled_view_core).(view_thread).(thread_continuation),
          v.(coupled_view_pending_gp) with
      | SSkip, [], None => |={E}=> Φ v
      | _, _, _ =>
          ∀ prefix s a suffix final,
            let p := CoupledExecutionPosition prefix s (CoupledMachineAction a :: suffix) final in
            ⌜coupled_thread_at P G p agent v /\ executing_agent a = agent⌝ -∗
            state_interp γ s ∗ thread_token γ agent v.(coupled_view_core).(view_thread)
              ={E,∅}=∗
            ∀ next,
              let p' := CoupledExecutionPosition (prefix ++ [CoupledMachineAction a])
                next suffix final in
              ⌜coupled_step P s (CoupledMachineAction a) next /\ coupled_position P G p'⌝ -∗
              |={∅}=> ▷ |={∅,E}=> ∃ v',
                ⌜project_coupled_thread p' agent = Some v'⌝ ∗
                state_interp γ next ∗
                thread_token γ agent v'.(coupled_view_core).(view_thread) ∗
                recurse E agent v' Φ
      end%I.
  End wp.
End LkmmWp.
