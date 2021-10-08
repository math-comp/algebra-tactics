From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat choice seq.
From mathcomp Require Import fintype finfun bigop order ssralg ssrnum ssrint rat.
From mathcomp Require Import ring zify_ring.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.

Local Open Scope ring_scope.

(* Examples from the Coq Reference Manual, but for an instance of MathComp's
   (abstract) field. *)

Goal forall (F : fieldType) (x : F), x != 0 -> (1 - 1 / x) * x - x + 1 = 0.
Proof. by move=> F x x_neq0; field. Qed.

Goal forall (F F' : fieldType) (f : {rmorphism F -> F'}) (x : F),
    f x != 0 -> f ((1 - 1 / x) * x - x + 1) = 0.
Proof. by move=> F F' f x x_neq0; field. Qed.

Goal forall (F : fieldType) (x y : F), y != 0 -> y = x -> x / y = 1.
Proof. by move=> F x y y_neq0; field. Qed.

Goal forall (F : fieldType) (x y : F), y != 0 -> y = 1 -> x = 1 -> x / y = 1.
Proof. by move=> F x y y_neq0; field. Qed.

(* Using the _%:R embedding from nat to F *)

Goal forall (F : fieldType) (n : nat),
    n%:R != 0 :> F -> (2 * n)%:R / n%:R = 2%:R :> F.
Proof. by move=> F n n_neq0; field. Qed.

Goal forall (F : numFieldType) (n : nat),
    n != 1%N -> (2%:R - (2 * n)%:R) / (1 - n%:R) = 2%:R :> F.
Proof. by move=> F n n_neq0; field; lia_ring. Qed.
