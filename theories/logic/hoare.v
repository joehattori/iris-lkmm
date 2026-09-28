From iris.base_logic.lib Require Export fancy_updates.
From iris.proofmode Require Import proofmode.
From iris_lkmm.logic Require Export graph_correspondence state_interp wp wp_parallel.
From iris.bi Require Export weakestpre.

(** Use Iris's WP and Texan-triple notation for the graph-relative WP.
    The context is explicit: all agents in a program proof must share the
    same candidate and ghost names. It is not a stuckness/safety flag. *)
Module LkmmHoare.
  Export LkmmWp LkmmWpParallel LkmmGraphCorrespondence LkmmStateInterp.

  Record wp_context := WpContext {
    wp_program : core_program;
    wp_candidate : core_candidate;
    wp_names : state_names;
    wp_agent : agent_id
  }.

  Section notation.
    Context `{!invGS Σ, !stateG Σ}.

    (** Statement specifications start with empty registers, no continuation,
        event index zero, an empty action history, and no pending GP. *)
    Global Instance stmt_wp : Wp (iProp Σ) stmt lkmm_thread_view wp_context :=
      fun c E body Φ => LkmmWp.wp c.(wp_program) c.(wp_candidate) c.(wp_names)
        E c.(wp_agent) (initial_thread_view body) Φ.

    (** Use a full view when specifying an intermediate execution position;
        registers, dependency origins, continuations, and RCU state are kept. *)
    Global Instance view_wp : Wp (iProp Σ) lkmm_thread_view lkmm_thread_view wp_context :=
      fun c E v Φ => LkmmWp.wp c.(wp_program) c.(wp_candidate) c.(wp_names)
        E c.(wp_agent) v Φ.

    Lemma stmt_wp_unfold c E body Φ :
      WP body @ c; E {{ Φ }} ⊣⊢
      LkmmWp.wp c.(wp_program) c.(wp_candidate) c.(wp_names)
        E c.(wp_agent) (initial_thread_view body) Φ.
    Proof. done. Qed.

    Lemma view_wp_unfold c E (v : lkmm_thread_view) Φ :
      WP v @ c; E {{ Φ }} ⊣⊢
      LkmmWp.wp c.(wp_program) c.(wp_candidate) c.(wp_names)
        E c.(wp_agent) v Φ.
    Proof. done. Qed.
  End notation.
End LkmmHoare.
