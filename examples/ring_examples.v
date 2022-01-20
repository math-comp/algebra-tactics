From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat choice seq.
From mathcomp Require Import fintype finfun bigop order ssralg ssrnum ssrint rat.
From mathcomp Require Import ring.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.

Local Open Scope ring_scope.

Section AbstractCommutativeRing.

Variables (R : comRingType) (a b c : R).

(* Examples from the Coq Reference Manual, but for an instance of MathComp's
   (abstract) commutative ring. *)


(* Using the _%:R embedding from nat to R *)
Goal (a + b + c) ^+ 2 =
     a * a + b ^+ 2 + c * c + 2%:R * a * b + 2%:R * a * c + 2%:R * b * c.
Proof. ring. Qed.

(* Using the _%:~R embedding from int to R : 2 is coerced to (Posz 2) : int *)
Goal (a + b + c) ^+ 2 =
     a * a + b ^+ 2 + c * c + 2%:~R * a * b + 2%:~R * a * c + 2%:~R * b * c.
Proof. ring. Qed.

(* With an identity hypothesis *)
(* Using the _%:R embedding from nat to R *)
Goal 2%:R * a * b = 30%:R -> (a + b) ^+ 2 = a ^+ 2 + b ^+ 2 + 30%:R.
Proof. move=> H; ring: H. Qed.

(* With an identity hypothesis *)
(* Using the _%:~R embedding from int to R *)
Goal 2%:~R * a * b = 30%:~R -> (a + b) ^+ 2 = a ^+ 2 + b ^+ 2 + 30%:~R.
Proof. move=> H; ring: H. Qed.

End AbstractCommutativeRing.

Section AbstractRingMorphism.

Variables (R : ringType) (S : comRingType) (f : {rmorphism R -> S}) (a b : R).

Goal f ((a + b) ^+ 2) = f a ^+ 2 + f b ^+ 2 + 2%:R * f a * f b.
Proof. ring. Qed.

End AbstractRingMorphism.

Section AbstractAdditiveFunction.

Variables (U V : zmodType) (R : comRingType).
Variables (g : {additive U -> V}) (f : {additive V -> R}) (a : U) (b : V).

Goal f (g a + b) ^+ 2 = f (g a) ^+ 2 + f b ^+ 2 + f (g (a *+ 2)) * f b.
Proof. ring. Qed.

End AbstractAdditiveFunction.

Section NumeralExamples.

Variable (R : comRingType).

(* With numeral constants *)
Goal 20%:R * 3%:R = 60%:R :> R.
Proof. ring. Qed.

Goal 20%:~R * 3%:~R = 60%:~R :> R.
Proof. ring. Qed.

Goal 200%:~R * 30%:~R = 6000%:~R :> R.
Proof. ring. Qed.

Goal 2%:~R * 10%:~R ^+ 2 * 3%:~R * 10%:~R ^+ 2 = 6%:~R * 10%:~R ^+ 4:> R.
Proof. ring. Qed.

Goal 200%:R * 30%:R = 6000%:R :> R.
Proof.
Time ring. (* 0.186 secs *)
Qed.

Goal 200%:R * 30%:R = 6000%:R :> int.
Proof.
Time ring. (* 0.343 secs *)
Qed.

Goal 20%:R * 3%:R = 60%:R :> rat.
Proof.
Time ring. (* 0.018 secs *)
Qed.

Goal 200%:R * 30%:R = 6000%:R :> rat.
Proof.
Time ring. (* 0.208 secs *)
Qed.

End NumeralExamples.

Section MoreVariables.

Variables (q w e r t y u i o p a s d f g h j k l : int).

Lemma test_vars : 
  q * w * e * r * t * y * u * i * o * p * a * s * d * f * g * h * j * k * l =
  l * w * e * r * t * y * u * i * o * p * a * s * d * f * g * h * j * k * q.
Proof. Time ring. Qed. (* 0.049 secs *)

End MoreVariables.

(* A failure to test the error message *)

Goal forall (R : comRingType) (a : R), a + a = a.
Proof.
move=> R a.
Fail ring. (* prints Not a valid ring equation. *)
ring || idtac. (* elpi-tactic failure can be caught by Ltac. *)
Abort.
