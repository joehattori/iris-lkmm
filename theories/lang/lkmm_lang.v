From Stdlib Require Import ZArith.
From iris_lkmm.lkmm Require Import events.

(** Minimal input language for the selected LKMM feasibility gate.

    This syntax is intentionally independent of the operational machines
    that execute it.  It remains smaller than the planned full LKMM-Core
    language. *)
Module LkmmLang.
  Import LkmmEvents.

  Definition agent := agent_id.

  Inductive label :=
  | LRead | LWrite | LRcuLock | LRcuUnlock | LSyncRcu.

  Inductive instruction :=
  | IRead | IWrite | IRcuLock | IRcuUnlock | ISynchronizeRcu.

  Definition program := agent -> list instruction.

  Definition canonical_label (lab : label) : event_label :=
    match lab with
    | LRead => LMemory AccessRead AccessOnce NotRmw 0 0%Z
    | LWrite => LMemory AccessWrite AccessOnce NotRmw 0 0%Z
    | LRcuLock => LBarrier BarrierRcuLock
    | LRcuUnlock => LBarrier BarrierRcuUnlock
    | LSyncRcu => LBarrier BarrierSyncRcu
    end.
End LkmmLang.
