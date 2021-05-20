From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat choice seq.
From mathcomp Require Import fintype finfun bigop order ssralg ssrnum ssrint rat.
From mathcomp Require Import ring.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.

Local Open Scope ring_scope.

(* Examples in the Coq Reference Manual *)

Goal forall (F : fieldType) (x : F), x != 0 -> (1 - 1 / x) * x - x + 1 = 0.
Proof. by move=> F x x_neq0; field; exact/eqP. Qed.

Goal forall (F : fieldType) (x y : F), y != 0 -> y = x -> x / y = 1.
Proof. by move=> F x y y_neq0 eq_yx; field: eq_yx; exact/eqP. Qed.
