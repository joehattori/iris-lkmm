From Stdlib Require Import ZArith.
From stdpp Require Import gmap.
From iris_lkmm.lang Require Import lkmm_core.

(** Shared Core programs for the four message-passing variants.
    Data is location 0, flag is location 1, and both reads are unconditional. *)
Module MessagePassingCode.
  Export LkmmCore.
  Definition producer sm :=
    SSeq (SStore StoreOnce (EConst 0) (EConst 1))
      (SStore sm (EConst 1) (EConst 1)).
  Definition consumer lm :=
    SSeq (SLoad 0 lm (EConst 1)) (SLoad 1 LoadOnce (EConst 0)).
  Definition program sm lm :=
    CoreProgram {[0 := 0%Z; 1 := 0%Z]} {[0 := producer sm; 1 := consumer lm]}.

End MessagePassingCode.
