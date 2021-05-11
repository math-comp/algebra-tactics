From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat choice seq.
From mathcomp Require Import fintype finfun bigop order ssralg ssrnum ssrint rat.
From mathcomp Require Import ring.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.

Local Open Scope ring_scope.

Goal forall x : rat, x != 0 -> (1 - 1 / x) * x - x + 1 = 0.
Proof.
move=> x x_neq0.
elpi field.
exact/eqP.
Qed.
