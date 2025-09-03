From mathcomp Require Import all_ssreflect ssralg.
From mathcomp.algebra_tactics Require Import ring.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.

Local Open Scope ring_scope.

(* A failure to test the error message *)

Goal forall (R : comRingType) (a : R), a + a = a.
Proof.
move=> R a.
Fail ring. (* prints Not a valid ring equation. *)
ring || idtac. (* elpi-tactic failure can be caught by Ltac. *)
Abort.
