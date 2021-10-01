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

Variables (R : ringType) (R' : comRingType) (f : {rmorphism R -> R'}) (a b : R).

Goal f ((a + b) ^+ 2) = f a ^+ 2 + f b ^+ 2 + 2%:R * f a * f b.
Proof. ring. Qed.

End AbstractRingMorphism.

Section AbstractAdditiveFunction.

Variables (V' V : zmodType) (R : comRingType).
Variables (g : {additive V' -> V}) (f : {additive V -> R}) (a : V') (b : V).

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

Section BiggerExample.

Variables (x1 x2 x3 y1 y2 y3 : int).

Definition f1 :=
  x1^3*x2 - x1*x2^3 - x1^3*x3 + x2^3*x3 + x1*x3^3 - x2*x3^3 - x2*y1^
  2 + x3*y1^2 + x1*y2^2 - x3*y2^2 - x1*y3^2 + x2*y3^2.

Definition f2 := 2%:R*x1^6%:R*x2^3 -
  6%:R*x1^4%:R*x2^5 + 6%:R*x1^2*x2^7 - 2%:R*x2^9 - 6%:R*x1^6%:R*x2^ 2%:R*x3 +
  6%:R*x1^5*x2^3*x3 + 12%:R*x1^4%:R*x2^4%:R*x3 - 12%:R*x1^3*x2^5*x3 -
  6%:R*x1^2*x2^6%:R*x3 + 6%:R*x1*x2^7%:R*x3 + 6%:R*x1^6%:R*x2*x3^2 -
  18%:R*x1^5*x2^2*x3^2 + 6%:R*x1^4%:R*x2^3*x3^2 + 24%:R*x1^3*x2^4%:R*x3^2 -
  18%:R*x1^2*x2^5*x3^2 - 6%:R*x1*x2^6%:R*x3^2 + 6%:R*x2^7%:R*x3^2 - 2%:R*x1^6%:R*x3^3
  + 18%:R*x1^5*x2*x3^3 - 30%:R*x1^4%:R*x2^2*x3^3 + 2%:R*x1^3*x2^3*x3^3 +
  24%:R*x1^2*x2^4%:R*x3^3 - 12%:R*x1*x2^5*x3^3 - 6%:R*x1^5*x3^4 +
  24%:R*x1^4%:R*x2*x3^4 - 30%:R*x1^3*x2^2*x3^4 + 6%:R*x1^2*x2^3*x3^4 +
  12%:R*x1*x2^4%:R*x3^4 - 6%:R*x2^5*x3^4 - 6%:R*x1^4%:R*x3^5 + 18%:R*x1^3*x2*x3^5 -
  18%:R*x1^2*x2^2*x3^5 + 6%:R*x1*x2^3*x3^5 - 2%:R*x1^3*x3^6 +
  6%:R*x1^2*x2*x3^6 - 6%:R*x1*x2^2*x3^6 + 2%:R*x2^3*x3^6 -
  3%:R*x1^3*x2^3*y1^2 + 3%:R*x1*x2^5*y1^2 + 9%:R*x1^3*x2^2*x3*y1^2 -
  6%:R*x1^2*x2^3*x3*y1^2 - 6%:R*x1*x2^4%:R*x3*y1^2 + 3%:R*x2^5*x3*y1^2 -
  9%:R*x1^3*x2*x3^2*y1^2 + 18%:R*x1^2*x2^2*x3^2*y1^2 -
  3%:R*x1*x2^3*x3^2*y1^2 - 6%:R*x2^4%:R*x3^2*y1^2 + 3%:R*x1^3*x3^3*y1^2 -
  18%:R*x1^2*x2*x3^3*y1^2 + 15%:R*x1*x2^2*x3^3*y1^2 + 6%:R*x1^2*x3^4%:R*y1^2
  - 12%:R*x1*x2*x3^4%:R*y1^2 + 6%:R*x2^2*x3^4%:R*y1^2 + 3%:R*x1*x3^5*y1^2 -
  3%:R*x2*x3^5*y1^2 + x2^3*y1^4 - 3%:R*x2^2*x3*y1^4 + 3%:R*x2*x3^2*y1^4 -
  x3^3*y1^4 + 8%:R*x1^3*x2^3*y1*y2 - 2%:R*x1^2*x2^4%:R*y1*y2 -
  8%:R*x1*x2^5*y1*y2 + 2%:R*x2^6%:R*y1*y2 - 18%:R*x1^3*x2^2*x3*y1*y2 +
  14%:R*x1^2*x2^3*x3*y1*y2 + 8%:R*x1*x2^4%:R*x3*y1*y2 - 4%:R*x2^5*x3*y1*y2 +
  12%:R*x1^3*x2*x3^2*y1*y2 - 30%:R*x1^2*x2^2*x3^2*y1*y2 +
  12%:R*x1*x2^3*x3^2*y1*y2 + 6%:R*x2^4%:R*x3^2*y1*y2 - 2%:R*x1^3*x3^3*y1*y2 +
  26%:R*x1^2*x2*x3^3*y1*y2 - 22%:R*x1*x2^2*x3^3*y1*y2 -
  2%:R*x2^3*x3^3*y1*y2 - 8%:R*x1^2*x3^4%:R*y1*y2 + 16%:R*x1*x2*x3^4%:R*y1*y2 -
  8%:R*x2^2*x3^4%:R*y1*y2 - 6%:R*x1*x3^5*y1*y2 + 6%:R*x2*x3^5*y1*y2 -
  6%:R*x2^3*y1^3*y2 + 12%:R*x2^2*x3*y1^3*y2 - 6%:R*x2*x3^2*y1^3*y2 -
  3%:R*x1^5*x2*y2^2 + 2%:R*x1^4%:R*x2^2*y2^2 + 3%:R*x1^3*x2^3*y2^2 -
  4%:R*x1^2*x2^4%:R*y2^2 + 2%:R*x2^6%:R*y2^2 + 3%:R*x1^5*x3*y2^2 -
  4%:R*x1^4%:R*x2*x3*y2^2 + 4%:R*x1^3*x2^2*x3*y2^2 + x1^2*x2^3*x3*y2^2 -
  4%:R*x1*x2^4%:R*x3*y2^2 + 2%:R*x1^4%:R*x3^2*y2^2 - 5%:R*x1^3*x2*x3^2*y2^2 +
  6%:R*x1^2*x2^2*x3^2*y2^2 + x1*x2^3*x3^2*y2^2 - 4%:R*x2^4%:R*x3^2*y2^2 -
  2%:R*x1^3*x3^3*y2^2 - 5%:R*x1^2*x2*x3^3*y2^2 + 4%:R*x1*x2^2*x3^3*y2^2 +
  3%:R*x2^3*x3^3*y2^2 + 2%:R*x1^2*x3^4%:R*y2^2 - 4%:R*x1*x2*x3^4%:R*y2^2 +
  2%:R*x2^2*x3^4%:R*y2^2 + 3%:R*x1*x3^5*y2^2 - 3%:R*x2*x3^5*y2^2 +
  3%:R*x1^2*x2*y1^2*y2^2 - x1*x2^2*y1^2*y2^2 + 10%:R*x2^3*y1^2*y2^2 -
  3%:R*x1^2*x3*y1^2*y2^2 + 2%:R*x1*x2*x3*y1^2*y2^2 -
  17%:R*x2^2*x3*y1^2*y2^2 - x1*x3^2*y1^2*y2^2 + x2*x3^2*y1^2*y2^2 +
  6%:R*x3^3*y1^2*y2^2 - 2%:R*x1^3*y1*y2^3 - 4%:R*x1^2*x2*y1*y2^3 +
  4%:R*x1*x2^2*y1*y2^3 - 8%:R*x2^3*y1*y2^3 + 4%:R*x1^2*x3*y1*y2^3 +
  8%:R*x2^2*x3*y1*y2^3 + 2%:R*x1*x3^2*y1*y2^3 + 4%:R*x2*x3^2*y1*y2^3 -
  8%:R*x3^3*y1*y2^3 + 2%:R*y1^3*y2^3 + 3%:R*x1^3*y2^4 - 2%:R*x1^2*x2*y2^4 +
  2%:R*x2^3*y2^4 - x1^2*x3*y2^4 - 2%:R*x1*x2*x3*y2^4 - x1*x3^2*y2^4 -
  2%:R*x2*x3^2*y2^4 + 3%:R*x3^3*y2^4 - 6%:R*y1^2*y2^4 + 6%:R*y1*y2^5 - 2%:R*y2^6
  - 6%:R*x1^3*x2^3*y1*y3 + 6%:R*x1^2*x2^4%:R*y1*y3 + 6%:R*x1*x2^5*y1*y3 -
  6%:R*x2^6%:R*y1*y3 + 12%:R*x1^3*x2^2*x3*y1*y3 - 18%:R*x1^2*x2^3*x3*y1*y3 +
  6%:R*x2^5*x3*y1*y3 - 6%:R*x1^3*x2*x3^2*y1*y3 +
  18%:R*x1^2*x2^2*x3^2*y1*y3 - 18%:R*x1*x2^3*x3^2*y1*y3 +
  6%:R*x2^4%:R*x3^2*y1*y3 - 6%:R*x1^2*x2*x3^3*y1*y3 +
  12%:R*x1*x2^2*x3^3*y1*y3 - 6%:R*x2^3*x3^3*y1*y3 + 4%:R*x2^3*y1^3*y3 -
  6%:R*x2^2*x3*y1^3*y3 + 2%:R*x3^3*y1^3*y3 + 6%:R*x1^5*x2*y2*y3 -
  8%:R*x1^4%:R*x2^2*y2*y3 - 2%:R*x1^3*x2^3*y2*y3 + 6%:R*x1^2*x2^4%:R*y2*y3 -
  4%:R*x1*x2^5*y2*y3 + 2%:R*x2^6%:R*y2*y3 - 6%:R*x1^5*x3*y2*y3 +
  16%:R*x1^4%:R*x2*x3*y2*y3 - 22%:R*x1^3*x2^2*x3*y2*y3 +
  12%:R*x1^2*x2^3*x3*y2*y3 + 8%:R*x1*x2^4%:R*x3*y2*y3 - 8%:R*x2^5*x3*y2*y3 -
  8%:R*x1^4%:R*x3^2*y2*y3 + 26%:R*x1^3*x2*x3^2*y2*y3 -
  30%:R*x1^2*x2^2*x3^2*y2*y3 + 14%:R*x1*x2^3*x3^2*y2*y3 -
  2%:R*x2^4%:R*x3^2*y2*y3 - 2%:R*x1^3*x3^3*y2*y3 + 12%:R*x1^2*x2*x3^3*y2*y3 -
  18%:R*x1*x2^2*x3^3*y2*y3 + 8%:R*x2^3*x3^3*y2*y3 -
  6%:R*x1^2*x2*y1^2*y2*y3 + 4%:R*x1*x2^2*y1^2*y2*y3 -
  10%:R*x2^3*y1^2*y2*y3 + 6%:R*x1^2*x3*y1^2*y2*y3 -
  8%:R*x1*x2*x3*y1^2*y2*y3 + 20%:R*x2^2*x3*y1^2*y2*y3 +
  4%:R*x1*x3^2*y1^2*y2*y3 - 4%:R*x2*x3^2*y1^2*y2*y3 - 6%:R*x3^3*y1^2*y2*y3
  + 6%:R*x1^3*y1*y2^2*y3 + 8%:R*x1^2*x2*y1*y2^2*y3 -
  18%:R*x1*x2^2*y1*y2^2*y3 + 16%:R*x2^3*y1*y2^2*y3 -
  8%:R*x1^2*x3*y1*y2^2*y3 + 8%:R*x1*x2*x3*y1*y2^2*y3 -
  18%:R*x2^2*x3*y1*y2^2*y3 - 8%:R*x1*x3^2*y1*y2^2*y3 +
  8%:R*x2*x3^2*y1*y2^2*y3 + 6%:R*x3^3*y1*y2^2*y3 - 6%:R*y1^3*y2^2*y3 -
  8%:R*x1^3*y2^3*y3 + 4%:R*x1^2*x2*y2^3*y3 + 8%:R*x1*x2^2*y2^3*y3 -
  8%:R*x2^3*y2^3*y3 + 2%:R*x1^2*x3*y2^3*y3 + 4%:R*x2^2*x3*y2^3*y3 +
  4%:R*x1*x3^2*y2^3*y3 - 4%:R*x2*x3^2*y2^3*y3 - 2%:R*x3^3*y2^3*y3 +
  18%:R*y1^2*y2^3*y3 - 18%:R*y1*y2^4%:R*y3 + 6%:R*y2^5*y3 - 3%:R*x1^5*x2*y3^2 +
  6%:R*x1^4%:R*x2^2*y3^2 - 6%:R*x1^2*x2^4%:R*y3^2 + 3%:R*x1*x2^5*y3^2 +
  3%:R*x1^5*x3*y3^2 - 12%:R*x1^4%:R*x2*x3*y3^2 + 15%:R*x1^3*x2^2*x3*y3^2 -
  3%:R*x1^2*x2^3*x3*y3^2 - 6%:R*x1*x2^4%:R*x3*y3^2 + 3%:R*x2^5*x3*y3^2 +
  6%:R*x1^4%:R*x3^2*y3^2 - 18%:R*x1^3*x2*x3^2*y3^2 +
  18%:R*x1^2*x2^2*x3^2*y3^2 - 6%:R*x1*x2^3*x3^2*y3^2 + 3%:R*x1^3*x3^3*y3^2
  - 9%:R*x1^2*x2*x3^3*y3^2 + 9%:R*x1*x2^2*x3^3*y3^2 - 3%:R*x2^3*x3^3*y3^2
  + 3%:R*x1^2*x2*y1^2*y3^2 - 3%:R*x1*x2^2*y1^2*y3^2 -
  3%:R*x1^2*x3*y1^2*y3^2 + 6%:R*x1*x2*x3*y1^2*y3^2 -
  3%:R*x2^2*x3*y1^2*y3^2 - 3%:R*x1*x3^2*y1^2*y3^2 + 3%:R*x2*x3^2*y1^2*y3^2
  - 6%:R*x1^3*y1*y2*y3^2 - 4%:R*x1^2*x2*y1*y2*y3^2 +
  20%:R*x1*x2^2*y1*y2*y3^2 - 10%:R*x2^3*y1*y2*y3^2 +
  4%:R*x1^2*x3*y1*y2*y3^2 - 8%:R*x1*x2*x3*y1*y2*y3^2 +
  4%:R*x2^2*x3*y1*y2*y3^2 + 6%:R*x1*x3^2*y1*y2*y3^2 -
  6%:R*x2*x3^2*y1*y2*y3^2 + 6%:R*y1^3*y2*y3^2 + 6%:R*x1^3*y2^2*y3^2 +
  x1^2*x2*y2^2*y3^2 - 17%:R*x1*x2^2*y2^2*y3^2 + 10%:R*x2^3*y2^2*y3^2 -
  x1^2*x3*y2^2*y3^2 + 2%:R*x1*x2*x3*y2^2*y3^2 - x2^2*x3*y2^2*y3^2 -
  3%:R*x1*x3^2*y2^2*y3^2 + 3%:R*x2*x3^2*y2^2*y3^2 - 18%:R*y1^2*y2^2*y3^2 +
  18%:R*y1*y2^3*y3^2 - 6%:R*y2^4%:R*y3^2 + 2%:R*x1^3*y1*y3^3 -
  6%:R*x1*x2^2*y1*y3^3 + 4%:R*x2^3*y1*y3^3 - 2%:R*y1^3*y3^3 -
  6%:R*x1^2*x2*y2*y3^3 + 12%:R*x1*x2^2*y2*y3^3 - 6%:R*x2^3*y2*y3^3 +
  6%:R*y1^2*y2*y3^3 - 6%:R*y1*y2^2*y3^3 + 2%:R*y2^3*y3^3 - x1^3*y3^4 +
  3%:R*x1^2*x2*y3^4 - 3%:R*x1*x2^2*y3^4 + x2^3*y3^4.

Definition f3 := 2%:R*x1^9%:R*x2^4 -
 8%:R*x1^7%:R*x2^6 + 12%:R*x1^5*x2^8 - 8%:R*x1^3*x2^10 + 2%:R*x1*x2^12 -
 8%:R*x1^9%:R*x2^3*x3 + 6%:R*x1^ 8%:R*x2^4%:R*x3 + 24%:R*x1^7%:R*x2^5*x3 -
16%:R*x1^6%:R*x2^6%:R*x3 - 24%:R*x1^5*x2^7%:R*x3 + 12%:R*x1^4%:R*x2^ 8%:R*x3 +
 8%:R*x1^3*x2^9%:R*x3 - 2%:R*x2^12%:R*x3 + 12%:R*x1^9%:R*x2^2*x3^2 -
 24%:R*x1^ 8%:R*x2^3*x3^2 - 12%:R*x1^7%:R*x2^4%:R*x3^2 + 48%:R*x1^6%:R*x2^5*x3^2 -
12%:R*x1^5*x2^6%:R*x3^2 - 24%:R*x1^4%:R*x2^7%:R*x3^2 + 12%:R*x1^3*x2^ 8%:R*x3^2 -
 8%:R*x1^9%:R*x2*x3^3 + 36%:R*x1^ 8%:R*x2^2*x3^3 - 32%:R*x1^7%:R*x2^3*x3^3 -
36%:R*x1^6%:R*x2^4%:R*x3^3 + 48%:R*x1^5*x2^5*x3^3 + 4%:R*x1^4%:R*x2^6%:R*x3^3 -
12%:R*x1^2*x2^ 8%:R*x3^3 - 8%:R*x1*x2^9%:R*x3^3 + 8%:R*x2^10%:R*x3^3 + 2%:R*x1^9%:R*x3^4 -
 24%:R*x1^ 8%:R*x2*x3^4 + 48%:R*x1^7%:R*x2^2*x3^4 - 16%:R*x1^6%:R*x2^3*x3^4 -
18%:R*x1^5*x2^4%:R*x3^4 - 4%:R*x1^3*x2^6%:R*x3^4 + 24%:R*x1^2*x2^7%:R*x3^4 -
12%:R*x1*x2^ 8%:R*x3^4 + 6%:R*x1^ 8%:R*x3^5 - 24%:R*x1^7%:R*x2*x3^5 +
 24%:R*x1^6%:R*x2^2*x3^5 + 18%:R*x1^4%:R*x2^4%:R*x3^5 - 48%:R*x1^3*x2^5*x3^5 +
12%:R*x1^2*x2^6%:R*x3^5 + 24%:R*x1*x2^7%:R*x3^5 - 12%:R*x2^ 8%:R*x3^5 + 4%:R*x1^7%:R*x3^6
- 24%:R*x1^5*x2^2*x3^6 + 16%:R*x1^4%:R*x2^3*x3^6 + 36%:R*x1^3*x2^4%:R*x3^6 -
48%:R*x1^2*x2^5*x3^6 + 16%:R*x1*x2^6%:R*x3^6 - 4%:R*x1^6%:R*x3^7 +
 24%:R*x1^5*x2*x3^7 - 48%:R*x1^4%:R*x2^2*x3^7 + 32%:R*x1^3*x2^3*x3^7 +
12%:R*x1^2*x2^4%:R*x3^7 - 24%:R*x1*x2^5*x3^7 + 8%:R*x2^6%:R*x3^7 - 6%:R*x1^5*x3^8 +
 24%:R*x1^4%:R*x2*x3^8 - 36%:R*x1^3*x2^2*x3^8 + 24%:R*x1^2*x2^3*x3^8 -
6%:R*x1*x2^4%:R*x3^8 - 2%:R*x1^4%:R*x3^9 + 8%:R*x1^3*x2*x3^9 - 12%:R*x1^2*x2^2*x3^9
+ 8%:R*x1*x2^3*x3^9 - 2%:R*x2^4%:R*x3^9 - 5%:R*x1^6%:R*x2^4%:R*y1^2 +
12%:R*x1^4%:R*x2^6%:R*y1^2 - 9%:R*x1^2*x2^ 8%:R*y1^2 + 2%:R*x2^10%:R*y1^2 +
20%:R*x1^6%:R*x2^3*x3*y1^2 - 12%:R*x1^5*x2^4%:R*x3*y1^2 -
36%:R*x1^4%:R*x2^5*x3*y1^2 + 18%:R*x1^3*x2^6%:R*x3*y1^2 +
18%:R*x1^2*x2^7%:R*x3*y1^2 - 6%:R*x1*x2^ 8%:R*x3*y1^2 - 2%:R*x2^9%:R*x3*y1^2 -
30%:R*x1^6%:R*x2^2*x3^2*y1^2 + 48%:R*x1^5*x2^3*x3^2*y1^2 +
18%:R*x1^4%:R*x2^4%:R*x3^2*y1^2 - 54%:R*x1^3*x2^5*x3^2*y1^2 +
9%:R*x1^2*x2^6%:R*x3^2*y1^2 + 12%:R*x1*x2^7%:R*x3^2*y1^2 - 3%:R*x2^ 8%:R*x3^2*y1^2 +
20%:R*x1^6%:R*x2*x3^3*y1^2 - 72%:R*x1^5*x2^2*x3^3*y1^2 +
48%:R*x1^4%:R*x2^3*x3^3*y1^2 + 40%:R*x1^3*x2^4%:R*x3^3*y1^2 -
36%:R*x1^2*x2^5*x3^3*y1^2 - 5%:R*x1^6%:R*x3^4%:R*y1^2 + 48%:R*x1^5*x2*x3^4%:R*y1^2
- 72%:R*x1^4%:R*x2^2*x3^4%:R*y1^2 + 20%:R*x1^3*x2^3*x3^4%:R*y1^2 +
12%:R*x1^2*x2^4%:R*x3^4%:R*y1^2 - 6%:R*x1*x2^5*x3^4%:R*y1^2 + 3%:R*x2^6%:R*x3^4%:R*y1^2 -
12%:R*x1^5*x3^5*y1^2 + 36%:R*x1^4%:R*x2*x3^5*y1^2 - 30%:R*x1^3*x2^2*x3^5*y1^2
+ 6%:R*x1^2*x2^3*x3^5*y1^2 - 6%:R*x1*x2^4%:R*x3^5*y1^2 + 6%:R*x2^5*x3^5*y1^2
- 6%:R*x1^4%:R*x3^6%:R*y1^2 + 2%:R*x1^3*x2*x3^6%:R*y1^2 + 9%:R*x1^2*x2^2*x3^6%:R*y1^2
- 5%:R*x2^4%:R*x3^6%:R*y1^2 + 4%:R*x1^3*x3^7%:R*y1^2 - 12%:R*x1^2*x2*x3^7%:R*y1^2 +
12%:R*x1*x2^2*x3^7%:R*y1^2 - 4%:R*x2^3*x3^7%:R*y1^2 + 3%:R*x1^2*x3^ 8%:R*y1^2 -
6%:R*x1*x2*x3^ 8%:R*y1^2 + 3%:R*x2^2*x3^ 8%:R*y1^2 + 4%:R*x1^3*x2^4%:R*y1^4 -
4%:R*x1*x2^6%:R*y1^4 - 16%:R*x1^3*x2^3*x3*y1^4 + 6%:R*x1^2*x2^4%:R*x3*y1^4 +
12%:R*x1*x2^5*x3*y1^4 - 2%:R*x2^6%:R*x3*y1^4 + 24%:R*x1^3*x2^2*x3^2*y1^4 -
 24%:R*x1^2*x2^3*x3^2*y1^4 - 6%:R*x1*x2^4%:R*x3^2*y1^4 + 6%:R*x2^5*x3^2*y1^4 -
16%:R*x1^3*x2*x3^3*y1^4 + 36%:R*x1^2*x2^2*x3^3*y1^4 -
16%:R*x1*x2^3*x3^3*y1^4 - 4%:R*x2^4%:R*x3^3*y1^4 + 4%:R*x1^3*x3^4%:R*y1^4 -
 24%:R*x1^2*x2*x3^4%:R*y1^4 + 24%:R*x1*x2^2*x3^4%:R*y1^4 - 4%:R*x2^3*x3^4%:R*y1^4 +
6%:R*x1^2*x3^5*y1^4 - 12%:R*x1*x2*x3^5*y1^4 + 6%:R*x2^2*x3^5*y1^4 +
2%:R*x1*x3^6%:R*y1^4 - 2%:R*x2*x3^6%:R*y1^4 - x2^4%:R*y1^6 + 4%:R*x2^3*x3*y1^6 -
6%:R*x2^2*x3^2*y1^6 + 4%:R*x2*x3^3*y1^6 - x3^4%:R*y1^6 + 8%:R*x1^6%:R*x2^4%:R*y1*y2
- 2%:R*x1^5*x2^5*y1*y2 - 16%:R*x1^4%:R*x2^6%:R*y1*y2 + 4%:R*x1^3*x2^7%:R*y1*y2 +
 8%:R*x1^2*x2^ 8%:R*y1*y2 - 2%:R*x1*x2^9%:R*y1*y2 - 26%:R*x1^6%:R*x2^3*x3*y1*y2 +
16%:R*x1^5*x2^4%:R*x3*y1*y2 + 34%:R*x1^4%:R*x2^5*x3*y1*y2 -
12%:R*x1^3*x2^6%:R*x3*y1*y2 - 10%:R*x1^2*x2^7%:R*x3*y1*y2 -
4%:R*x1*x2^ 8%:R*x3*y1*y2 + 2%:R*x2^9%:R*x3*y1*y2 + 30%:R*x1^6%:R*x2^2*x3^2*y1*y2 -
44%:R*x1^5*x2^3*x3^2*y1*y2 - 8%:R*x1^4%:R*x2^4%:R*x3^2*y1*y2 +
22%:R*x1^3*x2^5*x3^2*y1*y2 + 2%:R*x1^2*x2^6%:R*x3^2*y1*y2 +
2%:R*x1*x2^7%:R*x3^2*y1*y2 - 4%:R*x2^ 8%:R*x3^2*y1*y2 - 14%:R*x1^6%:R*x2*x3^3*y1*y2
+ 56%:R*x1^5*x2^2*x3^3*y1*y2 - 24%:R*x1^4%:R*x2^3*x3^3*y1*y2 -
32%:R*x1^3*x2^4%:R*x3^3*y1*y2 - 14%:R*x1^2*x2^5*x3^3*y1*y2 +
 24%:R*x1*x2^6%:R*x3^3*y1*y2 + 4%:R*x2^7%:R*x3^3*y1*y2 + 2%:R*x1^6%:R*x3^4%:R*y1*y2 -
34%:R*x1^5*x2*x3^4%:R*y1*y2 + 20%:R*x1^4%:R*x2^2*x3^4%:R*y1*y2 +
32%:R*x1^3*x2^3*x3^4%:R*y1*y2 + 4%:R*x1^2*x2^4%:R*x3^4%:R*y1*y2 -
26%:R*x1*x2^5*x3^4%:R*y1*y2 + 2%:R*x2^6%:R*x3^4%:R*y1*y2 + 8%:R*x1^5*x3^5*y1*y2 -
10%:R*x1^4%:R*x2*x3^5*y1*y2 - 28%:R*x1^3*x2^2*x3^5*y1*y2 +
40%:R*x1^2*x2^3*x3^5*y1*y2 + 4%:R*x1*x2^4%:R*x3^5*y1*y2 -
14%:R*x2^5*x3^5*y1*y2 + 4%:R*x1^4%:R*x3^6%:R*y1*y2 + 22%:R*x1^3*x2*x3^6%:R*y1*y2 -
48%:R*x1^2*x2^2*x3^6%:R*y1*y2 + 14%:R*x1*x2^3*x3^6%:R*y1*y2 +
 8%:R*x2^4%:R*x3^6%:R*y1*y2 - 8%:R*x1^3*x3^7%:R*y1*y2 + 24%:R*x1^2*x2*x3^7%:R*y1*y2 -
 24%:R*x1*x2^2*x3^7%:R*y1*y2 + 8%:R*x2^3*x3^7%:R*y1*y2 - 6%:R*x1^2*x3^ 8%:R*y1*y2 +
12%:R*x1*x2*x3^ 8%:R*y1*y2 - 6%:R*x2^2*x3^ 8%:R*y1*y2 - 14%:R*x1^3*x2^4%:R*y1^3*y2 +
2%:R*x1^2*x2^5*y1^3*y2 + 14%:R*x1*x2^6%:R*y1^3*y2 - 2%:R*x2^7%:R*y1^3*y2 +
44%:R*x1^3*x2^3*x3*y1^3*y2 - 16%:R*x1^2*x2^4%:R*x3*y1^3*y2 -
28%:R*x1*x2^5*x3*y1^3*y2 - 48%:R*x1^3*x2^2*x3^2*y1^3*y2 +
44%:R*x1^2*x2^3*x3^2*y1^3*y2 + 2%:R*x1*x2^4%:R*x3^2*y1^3*y2 +
2%:R*x2^5*x3^2*y1^3*y2 + 20%:R*x1^3*x2*x3^3*y1^3*y2 -
56%:R*x1^2*x2^2*x3^3*y1^3*y2 + 28%:R*x1*x2^3*x3^3*y1^3*y2 +
 8%:R*x2^4%:R*x3^3*y1^3*y2 - 2%:R*x1^3*x3^4%:R*y1^3*y2 +
34%:R*x1^2*x2*x3^4%:R*y1^3*y2 - 26%:R*x1*x2^2*x3^4%:R*y1^3*y2 -
6%:R*x2^3*x3^4%:R*y1^3*y2 - 8%:R*x1^2*x3^5*y1^3*y2 + 16%:R*x1*x2*x3^5*y1^3*y2
- 8%:R*x2^2*x3^5*y1^3*y2 - 6%:R*x1*x3^6%:R*y1^3*y2 + 6%:R*x2*x3^6%:R*y1^3*y2 +
6%:R*x2^4%:R*y1^5*y2 - 18%:R*x2^3*x3*y1^5*y2 + 18%:R*x2^2*x3^2*y1^5*y2 -
6%:R*x2*x3^3*y1^5*y2 - 3%:R*x1^ 8%:R*x2^2*y2^2 + 4%:R*x1^7%:R*x2^3*y2^2 +
6%:R*x1^6%:R*x2^4%:R*y2^2 - 12%:R*x1^5*x2^5*y2^2 - 3%:R*x1^4%:R*x2^6%:R*y2^2 +
12%:R*x1^3*x2^7%:R*y2^2 - 4%:R*x1*x2^9%:R*y2^2 + 6%:R*x1^ 8%:R*x2*x3*y2^2 -
12%:R*x1^7%:R*x2^2*x3*y2^2 + 2%:R*x1^6%:R*x2^3*x3*y2^2 + 18%:R*x1^5*x2^4%:R*x3*y2^2
- 12%:R*x1^4%:R*x2^5*x3*y2^2 - 6%:R*x1^3*x2^6%:R*x3*y2^2 + 4%:R*x2^9%:R*x3*y2^2 -
3%:R*x1^ 8%:R*x3^2*y2^2 + 12%:R*x1^7%:R*x2*x3^2*y2^2 - 21%:R*x1^6%:R*x2^2*x3^2*y2^2
+ 6%:R*x1^5*x2^3*x3^2*y2^2 + 18%:R*x1^4%:R*x2^4%:R*x3^2*y2^2 -
12%:R*x1^3*x2^5*x3^2*y2^2 - 4%:R*x1^7%:R*x3^3*y2^2 + 12%:R*x1^6%:R*x2*x3^3*y2^2
- 18%:R*x1^5*x2^2*x3^3*y2^2 + 4%:R*x1^4%:R*x2^3*x3^3*y2^2 +
12%:R*x1^2*x2^5*x3^3*y2^2 + 6%:R*x1*x2^6%:R*x3^3*y2^2 - 12%:R*x2^7%:R*x3^3*y2^2
+ x1^6%:R*x3^4%:R*y2^2 + 6%:R*x1^5*x2*x3^4%:R*y2^2 - 4%:R*x1^3*x2^3*x3^4%:R*y2^2 -
18%:R*x1^2*x2^4%:R*x3^4%:R*y2^2 + 12%:R*x1*x2^5*x3^4%:R*y2^2 + 3%:R*x2^6%:R*x3^4%:R*y2^2
- 6%:R*x1^4%:R*x2*x3^5*y2^2 + 18%:R*x1^3*x2^2*x3^5*y2^2 -
6%:R*x1^2*x2^3*x3^5*y2^2 - 18%:R*x1*x2^4%:R*x3^5*y2^2 + 12%:R*x2^5*x3^5*y2^2
- x1^4%:R*x3^6%:R*y2^2 - 12%:R*x1^3*x2*x3^6%:R*y2^2 + 21%:R*x1^2*x2^2*x3^6%:R*y2^2
- 2%:R*x1*x2^3*x3^6%:R*y2^2 - 6%:R*x2^4%:R*x3^6%:R*y2^2 + 4%:R*x1^3*x3^7%:R*y2^2 -
12%:R*x1^2*x2*x3^7%:R*y2^2 + 12%:R*x1*x2^2*x3^7%:R*y2^2 - 4%:R*x2^3*x3^7%:R*y2^2 +
3%:R*x1^2*x3^ 8%:R*y2^2 - 6%:R*x1*x2*x3^ 8%:R*y2^2 + 3%:R*x2^2*x3^ 8%:R*y2^2 +
6%:R*x1^5*x2^2*y1^2*y2^2 - 6%:R*x1^4%:R*x2^3*y1^2*y2^2 +
4%:R*x1^3*x2^4%:R*y1^2*y2^2 + 8%:R*x1^2*x2^5*y1^2*y2^2 -
10%:R*x1*x2^6%:R*y1^2*y2^2 - 2%:R*x2^7%:R*y1^2*y2^2 - 12%:R*x1^5*x2*x3*y1^2*y2^2
+ 18%:R*x1^4%:R*x2^2*x3*y1^2*y2^2 - 28%:R*x1^3*x2^3*x3*y1^2*y2^2 -
10%:R*x1^2*x2^4%:R*x3*y1^2*y2^2 + 20%:R*x1*x2^5*x3*y1^2*y2^2 +
12%:R*x2^6%:R*x3*y1^2*y2^2 + 6%:R*x1^5*x3^2*y1^2*y2^2 -
18%:R*x1^4%:R*x2*x3^2*y1^2*y2^2 + 36%:R*x1^3*x2^2*x3^2*y1^2*y2^2 -
4%:R*x1^2*x2^3*x3^2*y1^2*y2^2 - 4%:R*x1*x2^4%:R*x3^2*y1^2*y2^2 -
16%:R*x2^5*x3^2*y1^2*y2^2 + 6%:R*x1^4%:R*x3^3*y1^2*y2^2 -
4%:R*x1^3*x2*x3^3*y1^2*y2^2 + 4%:R*x1^2*x2^2*x3^3*y1^2*y2^2 +
4%:R*x1*x2^3*x3^3*y1^2*y2^2 - 10%:R*x2^4%:R*x3^3*y1^2*y2^2 -
 8%:R*x1^3*x3^4%:R*y1^2*y2^2 + 4%:R*x1^2*x2*x3^4%:R*y1^2*y2^2 -
20%:R*x1*x2^2*x3^4%:R*y1^2*y2^2 + 24%:R*x2^3*x3^4%:R*y1^2*y2^2 -
2%:R*x1^2*x3^5*y1^2*y2^2 + 4%:R*x1*x2*x3^5*y1^2*y2^2 -
2%:R*x2^2*x3^5*y1^2*y2^2 + 6%:R*x1*x3^6%:R*y1^2*y2^2 - 6%:R*x2*x3^6%:R*y1^2*y2^2
- 3%:R*x1^2*x2^2*y1^4%:R*y2^2 + 2%:R*x1*x2^3*y1^4%:R*y2^2 - 10%:R*x2^4%:R*y1^4%:R*y2^2
+ 6%:R*x1^2*x2*x3*y1^4%:R*y2^2 - 6%:R*x1*x2^2*x3*y1^4%:R*y2^2 +
26%:R*x2^3*x3*y1^4%:R*y2^2 - 3%:R*x1^2*x3^2*y1^4%:R*y2^2 +
6%:R*x1*x2*x3^2*y1^4%:R*y2^2 - 15%:R*x2^2*x3^2*y1^4%:R*y2^2 -
2%:R*x1*x3^3*y1^4%:R*y2^2 - 8%:R*x2*x3^3*y1^4%:R*y2^2 + 7%:R*x3^4%:R*y1^4%:R*y2^2 -
2%:R*x1^6%:R*x2*y1*y2^3 - 4%:R*x1^5*x2^2*y1*y2^3 + 14%:R*x1^4%:R*x2^3*y1*y2^3 -
6%:R*x1^3*x2^4%:R*y1*y2^3 - 12%:R*x1^2*x2^5*y1*y2^3 + 10%:R*x1*x2^6%:R*y1*y2^3 +
2%:R*x1^6%:R*x3*y1*y2^3 + 8%:R*x1^5*x2*x3*y1*y2^3 -
22%:R*x1^4%:R*x2^2*x3*y1*y2^3 + 16%:R*x1^3*x2^3*x3*y1*y2^3 +
6%:R*x1^2*x2^4%:R*x3*y1*y2^3 - 10%:R*x2^6%:R*x3*y1*y2^3 - 4%:R*x1^5*x3^2*y1*y2^3
+ 14%:R*x1^4%:R*x2*x3^2*y1*y2^3 - 16%:R*x1^3*x2^2*x3^2*y1*y2^3 -
6%:R*x1*x2^4%:R*x3^2*y1*y2^3 + 12%:R*x2^5*x3^2*y1*y2^3 -
6%:R*x1^4%:R*x3^3*y1*y2^3 + 16%:R*x1^2*x2^2*x3^3*y1*y2^3 -
16%:R*x1*x2^3*x3^3*y1*y2^3 + 6%:R*x2^4%:R*x3^3*y1*y2^3 +
6%:R*x1^3*x3^4%:R*y1*y2^3 - 14%:R*x1^2*x2*x3^4%:R*y1*y2^3 +
22%:R*x1*x2^2*x3^4%:R*y1*y2^3 - 14%:R*x2^3*x3^4%:R*y1*y2^3 +
4%:R*x1^2*x3^5*y1*y2^3 - 8%:R*x1*x2*x3^5*y1*y2^3 + 4%:R*x2^2*x3^5*y1*y2^3
- 2%:R*x1*x3^6%:R*y1*y2^3 + 2%:R*x2*x3^6%:R*y1*y2^3 + 4%:R*x1^3*x2*y1^3*y2^3 +
4%:R*x1^2*x2^2*y1^3*y2^3 - 12%:R*x1*x2^3*y1^3*y2^3 + 8%:R*x2^4%:R*y1^3*y2^3 -
4%:R*x1^3*x3*y1^3*y2^3 - 8%:R*x1^2*x2*x3*y1^3*y2^3 +
16%:R*x1*x2^2*x3*y1^3*y2^3 - 8%:R*x2^3*x3*y1^3*y2^3 +
4%:R*x1^2*x3^2*y1^3*y2^3 - 8%:R*x1*x2*x3^2*y1^3*y2^3 -
 8%:R*x2^2*x3^2*y1^3*y2^3 + 4%:R*x1*x3^3*y1^3*y2^3 +
16%:R*x2*x3^3*y1^3*y2^3 - 8%:R*x3^4%:R*y1^3*y2^3 - 2%:R*x2*y1^5*y2^3 +
2%:R*x3*y1^5*y2^3 - 6%:R*x1^3*x2*y1^2*y2^4 + x1^2*x2^2*y1^2*y2^4 +
16%:R*x1*x2^3*y1^2*y2^4 - 2%:R*x2^4%:R*y1^2*y2^4 + 6%:R*x1^3*x3*y1^2*y2^4 -
2%:R*x1^2*x2*x3*y1^2*y2^4 - 14%:R*x1*x2^2*x3*y1^2*y2^4 -
14%:R*x2^3*x3*y1^2*y2^4 + x1^2*x3^2*y1^2*y2^4 -
2%:R*x1*x2*x3^2*y1^2*y2^4 + 19%:R*x2^2*x3^2*y1^2*y2^4 -
3%:R*x3^4%:R*y1^2*y2^4 + 6%:R*x2*y1^4%:R*y2^4 - 6%:R*x3*y1^4%:R*y2^4 -
2%:R*x1^4%:R*y1*y2^5 + 2%:R*x1^3*x2*y1*y2^5 + 4%:R*x1^2*x2^2*y1*y2^5 -
14%:R*x1*x2^3*y1*y2^5 + 4%:R*x1^2*x2*x3*y1*y2^5 + 4%:R*x1*x2^2*x3*y1*y2^5
+ 14%:R*x2^3*x3*y1*y2^5 - 2%:R*x1^2*x3^2*y1*y2^5 + 4%:R*x1*x2*x3^2*y1*y2^5
- 8%:R*x2^2*x3^2*y1*y2^5 - 4%:R*x1*x3^3*y1*y2^5 - 10%:R*x2*x3^3*y1*y2^5 +
 8%:R*x3^4%:R*y1*y2^5 + 2%:R*x1*y1^3*y2^5 - 6%:R*x2*y1^3*y2^5 + 4%:R*x3*y1^3*y2^5
+ 3%:R*x1^4%:R*y2^6 - 4%:R*x1^3*x2*y2^6 + 4%:R*x1*x2^3*y2^6 - 2%:R*x1^3*x3*y2^6
- 4%:R*x2^3*x3*y2^6 + 2%:R*x1*x3^3*y2^6 + 4%:R*x2*x3^3*y2^6 - 3%:R*x3^4%:R*y2^6
- 6%:R*x1*y1^2*y2^6 + 2%:R*x2*y1^2*y2^6 + 4%:R*x3*y1^2*y2^6 + 6%:R*x1*y1*y2^7
- 6%:R*x3*y1*y2^7 - 2%:R*x1*y2^8 + 2%:R*x3*y2^8 - 6%:R*x1^6%:R*x2^4%:R*y1*y3 +
6%:R*x1^5*x2^5*y1*y3 + 12%:R*x1^4%:R*x2^6%:R*y1*y3 - 12%:R*x1^3*x2^7%:R*y1*y3 -
6%:R*x1^2*x2^ 8%:R*y1*y3 + 6%:R*x1*x2^9%:R*y1*y3 + 18%:R*x1^6%:R*x2^3*x3*y1*y3 -
 24%:R*x1^5*x2^4%:R*x3*y1*y3 - 18%:R*x1^4%:R*x2^5*x3*y1*y3 +
 24%:R*x1^3*x2^6%:R*x3*y1*y3 + 6%:R*x1^2*x2^7%:R*x3*y1*y3 - 6%:R*x2^9%:R*x3*y1*y3 -
18%:R*x1^6%:R*x2^2*x3^2*y1*y3 + 36%:R*x1^5*x2^3*x3^2*y1*y3 -
12%:R*x1^4%:R*x2^4%:R*x3^2*y1*y3 - 6%:R*x1^3*x2^5*x3^2*y1*y3 -
6%:R*x1*x2^7%:R*x3^2*y1*y3 + 6%:R*x2^ 8%:R*x3^2*y1*y3 + 6%:R*x1^6%:R*x2*x3^3*y1*y3 -
 24%:R*x1^5*x2^2*x3^3*y1*y3 + 24%:R*x1^4%:R*x2^3*x3^3*y1*y3 +
6%:R*x1^2*x2^5*x3^3*y1*y3 - 24%:R*x1*x2^6%:R*x3^3*y1*y3 +
12%:R*x2^7%:R*x3^3*y1*y3 + 6%:R*x1^5*x2*x3^4%:R*y1*y3 -
 24%:R*x1^3*x2^3*x3^4%:R*y1*y3 + 12%:R*x1^2*x2^4%:R*x3^4%:R*y1*y3 +
18%:R*x1*x2^5*x3^4%:R*y1*y3 - 12%:R*x2^6%:R*x3^4%:R*y1*y3 - 6%:R*x1^4%:R*x2*x3^5*y1*y3
+ 24%:R*x1^3*x2^2*x3^5*y1*y3 - 36%:R*x1^2*x2^3*x3^5*y1*y3 +
 24%:R*x1*x2^4%:R*x3^5*y1*y3 - 6%:R*x2^5*x3^5*y1*y3 - 6%:R*x1^3*x2*x3^6%:R*y1*y3
+ 18%:R*x1^2*x2^2*x3^6%:R*y1*y3 - 18%:R*x1*x2^3*x3^6%:R*y1*y3 +
6%:R*x2^4%:R*x3^6%:R*y1*y3 + 10%:R*x1^3*x2^4%:R*y1^3*y3 - 6%:R*x1^2*x2^5*y1^3*y3 -
10%:R*x1*x2^6%:R*y1^3*y3 + 6%:R*x2^7%:R*y1^3*y3 - 28%:R*x1^3*x2^3*x3*y1^3*y3 +
 24%:R*x1^2*x2^4%:R*x3*y1^3*y3 + 12%:R*x1*x2^5*x3*y1^3*y3 -
 8%:R*x2^6%:R*x3*y1^3*y3 + 24%:R*x1^3*x2^2*x3^2*y1^3*y3 -
36%:R*x1^2*x2^3*x3^2*y1^3*y3 + 18%:R*x1*x2^4%:R*x3^2*y1^3*y3 -
6%:R*x2^5*x3^2*y1^3*y3 - 4%:R*x1^3*x2*x3^3*y1^3*y3 +
 24%:R*x1^2*x2^2*x3^3*y1^3*y3 - 28%:R*x1*x2^3*x3^3*y1^3*y3 +
 8%:R*x2^4%:R*x3^3*y1^3*y3 - 2%:R*x1^3*x3^4%:R*y1^3*y3 -
6%:R*x1^2*x2*x3^4%:R*y1^3*y3 + 6%:R*x1*x2^2*x3^4%:R*y1^3*y3 +
2%:R*x2^3*x3^4%:R*y1^3*y3 + 2%:R*x1*x3^6%:R*y1^3*y3 - 2%:R*x2*x3^6%:R*y1^3*y3 -
4%:R*x2^4%:R*y1^5*y3 + 10%:R*x2^3*x3*y1^5*y3 - 6%:R*x2^2*x3^2*y1^5*y3 -
2%:R*x2*x3^3*y1^5*y3 + 2%:R*x3^4%:R*y1^5*y3 + 6%:R*x1^ 8%:R*x2^2*y2*y3 -
 8%:R*x1^7%:R*x2^3*y2*y3 - 8%:R*x1^6%:R*x2^4%:R*y2*y3 + 14%:R*x1^5*x2^5*y2*y3 -
2%:R*x1^4%:R*x2^6%:R*y2*y3 - 4%:R*x1^3*x2^7%:R*y2*y3 + 4%:R*x1^2*x2^ 8%:R*y2*y3 -
2%:R*x1*x2^9%:R*y2*y3 - 12%:R*x1^ 8%:R*x2*x3*y2*y3 + 24%:R*x1^7%:R*x2^2*x3*y2*y3 -
14%:R*x1^6%:R*x2^3*x3*y2*y3 - 4%:R*x1^5*x2^4%:R*x3*y2*y3 +
26%:R*x1^4%:R*x2^5*x3*y2*y3 - 24%:R*x1^3*x2^6%:R*x3*y2*y3 -
2%:R*x1^2*x2^7%:R*x3*y2*y3 + 4%:R*x1*x2^ 8%:R*x3*y2*y3 + 2%:R*x2^9%:R*x3*y2*y3 +
6%:R*x1^ 8%:R*x3^2*y2*y3 - 24%:R*x1^7%:R*x2*x3^2*y2*y3 +
48%:R*x1^6%:R*x2^2*x3^2*y2*y3 - 40%:R*x1^5*x2^3*x3^2*y2*y3 -
4%:R*x1^4%:R*x2^4%:R*x3^2*y2*y3 + 14%:R*x1^3*x2^5*x3^2*y2*y3 -
2%:R*x1^2*x2^6%:R*x3^2*y2*y3 + 10%:R*x1*x2^7%:R*x3^2*y2*y3 -
 8%:R*x2^ 8%:R*x3^2*y2*y3 + 8%:R*x1^7%:R*x3^3*y2*y3 - 22%:R*x1^6%:R*x2*x3^3*y2*y3 +
28%:R*x1^5*x2^2*x3^3*y2*y3 - 32%:R*x1^4%:R*x2^3*x3^3*y2*y3 +
32%:R*x1^3*x2^4%:R*x3^3*y2*y3 - 22%:R*x1^2*x2^5*x3^3*y2*y3 +
12%:R*x1*x2^6%:R*x3^3*y2*y3 - 4%:R*x2^7%:R*x3^3*y2*y3 - 4%:R*x1^6%:R*x3^4%:R*y2*y3 +
10%:R*x1^5*x2*x3^4%:R*y2*y3 - 20%:R*x1^4%:R*x2^2*x3^4%:R*y2*y3 +
 24%:R*x1^3*x2^3*x3^4%:R*y2*y3 + 8%:R*x1^2*x2^4%:R*x3^4%:R*y2*y3 -
34%:R*x1*x2^5*x3^4%:R*y2*y3 + 16%:R*x2^6%:R*x3^4%:R*y2*y3 - 8%:R*x1^5*x3^5*y2*y3 +
34%:R*x1^4%:R*x2*x3^5*y2*y3 - 56%:R*x1^3*x2^2*x3^5*y2*y3 +
44%:R*x1^2*x2^3*x3^5*y2*y3 - 16%:R*x1*x2^4%:R*x3^5*y2*y3 +
2%:R*x2^5*x3^5*y2*y3 - 2%:R*x1^4%:R*x3^6%:R*y2*y3 + 14%:R*x1^3*x2*x3^6%:R*y2*y3 -
30%:R*x1^2*x2^2*x3^6%:R*y2*y3 + 26%:R*x1*x2^3*x3^6%:R*y2*y3 -
 8%:R*x2^4%:R*x3^6%:R*y2*y3 - 12%:R*x1^5*x2^2*y1^2*y2*y3 +
12%:R*x1^4%:R*x2^3*y1^2*y2*y3 - 2%:R*x1^3*x2^4%:R*y1^2*y2*y3 -
10%:R*x1^2*x2^5*y1^2*y2*y3 + 14%:R*x1*x2^6%:R*y1^2*y2*y3 -
2%:R*x2^7%:R*y1^2*y2*y3 + 24%:R*x1^5*x2*x3*y1^2*y2*y3 -
36%:R*x1^4%:R*x2^2*x3*y1^2*y2*y3 + 44%:R*x1^3*x2^3*x3*y1^2*y2*y3 -
4%:R*x1^2*x2^4%:R*x3*y1^2*y2*y3 - 28%:R*x1*x2^5*x3*y1^2*y2*y3 -
12%:R*x1^5*x3^2*y1^2*y2*y3 + 36%:R*x1^4%:R*x2*x3^2*y1^2*y2*y3 -
72%:R*x1^3*x2^2*x3^2*y1^2*y2*y3 + 44%:R*x1^2*x2^3*x3^2*y1^2*y2*y3 -
10%:R*x1*x2^4%:R*x3^2*y1^2*y2*y3 + 14%:R*x2^5*x3^2*y1^2*y2*y3 -
12%:R*x1^4%:R*x3^3*y1^2*y2*y3 + 20%:R*x1^3*x2*x3^3*y1^2*y2*y3 -
32%:R*x1^2*x2^2*x3^3*y1^2*y2*y3 + 28%:R*x1*x2^3*x3^3*y1^2*y2*y3 -
4%:R*x2^4%:R*x3^3*y1^2*y2*y3 + 10%:R*x1^3*x3^4%:R*y1^2*y2*y3 -
2%:R*x1^2*x2*x3^4%:R*y1^2*y2*y3 + 10%:R*x1*x2^2*x3^4%:R*y1^2*y2*y3 -
18%:R*x2^3*x3^4%:R*y1^2*y2*y3 + 4%:R*x1^2*x3^5*y1^2*y2*y3 -
 8%:R*x1*x2*x3^5*y1^2*y2*y3 + 4%:R*x2^2*x3^5*y1^2*y2*y3 -
6%:R*x1*x3^6%:R*y1^2*y2*y3 + 6%:R*x2*x3^6%:R*y1^2*y2*y3 +
6%:R*x1^2*x2^2*y1^4%:R*y2*y3 - 4%:R*x1*x2^3*y1^4%:R*y2*y3 +
10%:R*x2^4%:R*y1^4%:R*y2*y3 - 12%:R*x1^2*x2*x3*y1^4%:R*y2*y3 +
12%:R*x1*x2^2*x3*y1^4%:R*y2*y3 - 30%:R*x2^3*x3*y1^4%:R*y2*y3 +
6%:R*x1^2*x3^2*y1^4%:R*y2*y3 - 12%:R*x1*x2*x3^2*y1^4%:R*y2*y3 +
 24%:R*x2^2*x3^2*y1^4%:R*y2*y3 + 4%:R*x1*x3^3*y1^4%:R*y2*y3 +
2%:R*x2*x3^3*y1^4%:R*y2*y3 - 6%:R*x3^4%:R*y1^4%:R*y2*y3 + 6%:R*x1^6%:R*x2*y1*y2^2*y3 +
 8%:R*x1^5*x2^2*y1*y2^2*y3 - 30%:R*x1^4%:R*x2^3*y1*y2^2*y3 +
14%:R*x1^3*x2^4%:R*y1*y2^2*y3 + 24%:R*x1^2*x2^5*y1*y2^2*y3 -
22%:R*x1*x2^6%:R*y1*y2^2*y3 - 6%:R*x1^6%:R*x3*y1*y2^2*y3 -
16%:R*x1^5*x2*x3*y1*y2^2*y3 + 38%:R*x1^4%:R*x2^2*x3*y1*y2^2*y3 -
32%:R*x1^3*x2^3*x3*y1*y2^2*y3 - 6%:R*x1^2*x2^4%:R*x3*y1*y2^2*y3 +
22%:R*x2^6%:R*x3*y1*y2^2*y3 + 8%:R*x1^5*x3^2*y1*y2^2*y3 -
22%:R*x1^4%:R*x2*x3^2*y1*y2^2*y3 + 32%:R*x1^3*x2^2*x3^2*y1*y2^2*y3 +
6%:R*x1*x2^4%:R*x3^2*y1*y2^2*y3 - 24%:R*x2^5*x3^2*y1*y2^2*y3 +
14%:R*x1^4%:R*x3^3*y1*y2^2*y3 - 32%:R*x1^2*x2^2*x3^3*y1*y2^2*y3 +
32%:R*x1*x2^3*x3^3*y1*y2^2*y3 - 14%:R*x2^4%:R*x3^3*y1*y2^2*y3 -
14%:R*x1^3*x3^4%:R*y1*y2^2*y3 + 22%:R*x1^2*x2*x3^4%:R*y1*y2^2*y3 -
38%:R*x1*x2^2*x3^4%:R*y1*y2^2*y3 + 30%:R*x2^3*x3^4%:R*y1*y2^2*y3 -
 8%:R*x1^2*x3^5*y1*y2^2*y3 + 16%:R*x1*x2*x3^5*y1*y2^2*y3 -
 8%:R*x2^2*x3^5*y1*y2^2*y3 + 6%:R*x1*x3^6%:R*y1*y2^2*y3 -
6%:R*x2*x3^6%:R*y1*y2^2*y3 - 12%:R*x1^3*x2*y1^3*y2^2*y3 -
 8%:R*x1^2*x2^2*y1^3*y2^2*y3 + 28%:R*x1*x2^3*y1^3*y2^2*y3 -
16%:R*x2^4%:R*y1^3*y2^2*y3 + 12%:R*x1^3*x3*y1^3*y2^2*y3 +
16%:R*x1^2*x2*x3*y1^3*y2^2*y3 - 32%:R*x1*x2^2*x3*y1^3*y2^2*y3 +
 24%:R*x2^3*x3*y1^3*y2^2*y3 - 8%:R*x1^2*x3^2*y1^3*y2^2*y3 +
16%:R*x1*x2*x3^2*y1^3*y2^2*y3 - 20%:R*x2^2*x3^2*y1^3*y2^2*y3 -
12%:R*x1*x3^3*y1^3*y2^2*y3 + 8%:R*x2*x3^3*y1^3*y2^2*y3 +
4%:R*x3^4%:R*y1^3*y2^2*y3 + 6%:R*x2*y1^5*y2^2*y3 - 6%:R*x3*y1^5*y2^2*y3 -
2%:R*x1^6%:R*x2*y2^3*y3 - 4%:R*x1^5*x2^2*y2^3*y3 + 14%:R*x1^4%:R*x2^3*y2^3*y3 -
6%:R*x1^3*x2^4%:R*y2^3*y3 - 12%:R*x1^2*x2^5*y2^3*y3 + 10%:R*x1*x2^6%:R*y2^3*y3 +
2%:R*x1^6%:R*x3*y2^3*y3 + 8%:R*x1^5*x2*x3*y2^3*y3 -
22%:R*x1^4%:R*x2^2*x3*y2^3*y3 + 16%:R*x1^3*x2^3*x3*y2^3*y3 +
6%:R*x1^2*x2^4%:R*x3*y2^3*y3 - 10%:R*x2^6%:R*x3*y2^3*y3 - 4%:R*x1^5*x3^2*y2^3*y3
+ 14%:R*x1^4%:R*x2*x3^2*y2^3*y3 - 16%:R*x1^3*x2^2*x3^2*y2^3*y3 -
6%:R*x1*x2^4%:R*x3^2*y2^3*y3 + 12%:R*x2^5*x3^2*y2^3*y3 -
6%:R*x1^4%:R*x3^3*y2^3*y3 + 16%:R*x1^2*x2^2*x3^3*y2^3*y3 -
16%:R*x1*x2^3*x3^3*y2^3*y3 + 6%:R*x2^4%:R*x3^3*y2^3*y3 +
6%:R*x1^3*x3^4%:R*y2^3*y3 - 14%:R*x1^2*x2*x3^4%:R*y2^3*y3 +
22%:R*x1*x2^2*x3^4%:R*y2^3*y3 - 14%:R*x2^3*x3^4%:R*y2^3*y3 +
4%:R*x1^2*x3^5*y2^3*y3 - 8%:R*x1*x2*x3^5*y2^3*y3 + 4%:R*x2^2*x3^5*y2^3*y3
- 2%:R*x1*x3^6%:R*y2^3*y3 + 2%:R*x2*x3^6%:R*y2^3*y3 + 20%:R*x1^3*x2*y1^2*y2^3*y3
- 36%:R*x1*x2^3*y1^2*y2^3*y3 + 8%:R*x2^4%:R*y1^2*y2^3*y3 -
20%:R*x1^3*x3*y1^2*y2^3*y3 + 24%:R*x1*x2^2*x3*y1^2*y2^3*y3 +
16%:R*x2^3*x3*y1^2*y2^3*y3 - 12%:R*x2^2*x3^2*y1^2*y2^3*y3 +
12%:R*x1*x3^3*y1^2*y2^3*y3 - 16%:R*x2*x3^3*y1^2*y2^3*y3 +
4%:R*x3^4%:R*y1^2*y2^3*y3 - 18%:R*x2*y1^4%:R*y2^3*y3 + 18%:R*x3*y1^4%:R*y2^3*y3 +
6%:R*x1^4%:R*y1*y2^4%:R*y3 - 10%:R*x1^3*x2*y1*y2^4%:R*y3 -
18%:R*x1^2*x2^2*y1*y2^4%:R*y3 + 34%:R*x1*x2^3*y1*y2^4%:R*y3 +
4%:R*x1^3*x3*y1*y2^4%:R*y3 - 34%:R*x2^3*x3*y1*y2^4%:R*y3 +
18%:R*x2^2*x3^2*y1*y2^4%:R*y3 - 4%:R*x1*x3^3*y1*y2^4%:R*y3 +
10%:R*x2*x3^3*y1*y2^4%:R*y3 - 6%:R*x3^4%:R*y1*y2^4%:R*y3 - 6%:R*x1*y1^3*y2^4%:R*y3 +
18%:R*x2*y1^3*y2^4%:R*y3 - 12%:R*x3*y1^3*y2^4%:R*y3 - 8%:R*x1^4%:R*y2^5*y3 +
10%:R*x1^3*x2*y2^5*y3 + 8%:R*x1^2*x2^2*y2^5*y3 - 14%:R*x1*x2^3*y2^5*y3 +
4%:R*x1^3*x3*y2^5*y3 - 4%:R*x1^2*x2*x3*y2^5*y3 - 4%:R*x1*x2^2*x3*y2^5*y3 +
14%:R*x2^3*x3*y2^5*y3 + 2%:R*x1^2*x3^2*y2^5*y3 - 4%:R*x1*x2*x3^2*y2^5*y3 -
4%:R*x2^2*x3^2*y2^5*y3 - 2%:R*x2*x3^3*y2^5*y3 + 2%:R*x3^4%:R*y2^5*y3 +
18%:R*x1*y1^2*y2^5*y3 - 6%:R*x2*y1^2*y2^5*y3 - 12%:R*x3*y1^2*y2^5*y3 -
18%:R*x1*y1*y2^6%:R*y3 + 18%:R*x3*y1*y2^6%:R*y3 + 6%:R*x1*y2^7%:R*y3 - 6%:R*x3*y2^7%:R*y3
- 3%:R*x1^ 8%:R*x2^2*y3^2 + 4%:R*x1^7%:R*x2^3*y3^2 + 5%:R*x1^6%:R*x2^4%:R*y3^2 -
6%:R*x1^5*x2^5*y3^2 - 3%:R*x1^4%:R*x2^6%:R*y3^2 + 3%:R*x1^2*x2^ 8%:R*y3^2 +
2%:R*x1*x2^9%:R*y3^2 - 2%:R*x2^10%:R*y3^2 + 6%:R*x1^ 8%:R*x2*x3*y3^2 -
12%:R*x1^7%:R*x2^2*x3*y3^2 + 6%:R*x1^5*x2^4%:R*x3*y3^2 + 6%:R*x1^4%:R*x2^5*x3*y3^2
- 12%:R*x1^2*x2^7%:R*x3*y3^2 + 6%:R*x1*x2^ 8%:R*x3*y3^2 - 3%:R*x1^ 8%:R*x3^2*y3^2 +
12%:R*x1^7%:R*x2*x3^2*y3^2 - 9%:R*x1^6%:R*x2^2*x3^2*y3^2 -
6%:R*x1^5*x2^3*x3^2*y3^2 - 12%:R*x1^4%:R*x2^4%:R*x3^2*y3^2 +
36%:R*x1^3*x2^5*x3^2*y3^2 - 9%:R*x1^2*x2^6%:R*x3^2*y3^2 -
18%:R*x1*x2^7%:R*x3^2*y3^2 + 9%:R*x2^ 8%:R*x3^2*y3^2 - 4%:R*x1^7%:R*x3^3*y3^2 -
2%:R*x1^6%:R*x2*x3^3*y3^2 + 30%:R*x1^5*x2^2*x3^3*y3^2 -
20%:R*x1^4%:R*x2^3*x3^3*y3^2 - 40%:R*x1^3*x2^4%:R*x3^3*y3^2 +
54%:R*x1^2*x2^5*x3^3*y3^2 - 18%:R*x1*x2^6%:R*x3^3*y3^2 + 6%:R*x1^6%:R*x3^4%:R*y3^2
- 36%:R*x1^5*x2*x3^4%:R*y3^2 + 72%:R*x1^4%:R*x2^2*x3^4%:R*y3^2 -
48%:R*x1^3*x2^3*x3^4%:R*y3^2 - 18%:R*x1^2*x2^4%:R*x3^4%:R*y3^2 +
36%:R*x1*x2^5*x3^4%:R*y3^2 - 12%:R*x2^6%:R*x3^4%:R*y3^2 + 12%:R*x1^5*x3^5*y3^2 -
48%:R*x1^4%:R*x2*x3^5*y3^2 + 72%:R*x1^3*x2^2*x3^5*y3^2 -
48%:R*x1^2*x2^3*x3^5*y3^2 + 12%:R*x1*x2^4%:R*x3^5*y3^2 + 5%:R*x1^4%:R*x3^6%:R*y3^2
- 20%:R*x1^3*x2*x3^6%:R*y3^2 + 30%:R*x1^2*x2^2*x3^6%:R*y3^2 -
20%:R*x1*x2^3*x3^6%:R*y3^2 + 5%:R*x2^4%:R*x3^6%:R*y3^2 + 6%:R*x1^5*x2^2*y1^2*y3^2 -
6%:R*x1^4%:R*x2^3*y1^2*y3^2 - 6%:R*x1^3*x2^4%:R*y1^2*y3^2 +
6%:R*x1^2*x2^5*y1^2*y3^2 - 12%:R*x1^5*x2*x3*y1^2*y3^2 +
18%:R*x1^4%:R*x2^2*x3*y1^2*y3^2 - 6%:R*x1^2*x2^4%:R*x3*y1^2*y3^2 +
6%:R*x1^5*x3^2*y1^2*y3^2 - 18%:R*x1^4%:R*x2*x3^2*y1^2*y3^2 +
12%:R*x1^3*x2^2*x3^2*y1^2*y3^2 + 6%:R*x1*x2^4%:R*x3^2*y1^2*y3^2 -
6%:R*x2^5*x3^2*y1^2*y3^2 + 6%:R*x1^4%:R*x3^3*y1^2*y3^2 -
12%:R*x1^2*x2^2*x3^3*y1^2*y3^2 + 6%:R*x2^4%:R*x3^3*y1^2*y3^2 -
6%:R*x1^3*x3^4%:R*y1^2*y3^2 + 18%:R*x1^2*x2*x3^4%:R*y1^2*y3^2 -
18%:R*x1*x2^2*x3^4%:R*y1^2*y3^2 + 6%:R*x2^3*x3^4%:R*y1^2*y3^2 -
6%:R*x1^2*x3^5*y1^2*y3^2 + 12%:R*x1*x2*x3^5*y1^2*y3^2 -
6%:R*x2^2*x3^5*y1^2*y3^2 - 3%:R*x1^2*x2^2*y1^4%:R*y3^2 +
2%:R*x1*x2^3*y1^4%:R*y3^2 + x2^4%:R*y1^4%:R*y3^2 + 6%:R*x1^2*x2*x3*y1^4%:R*y3^2 -
6%:R*x1*x2^2*x3*y1^4%:R*y3^2 - 3%:R*x1^2*x3^2*y1^4%:R*y3^2 +
6%:R*x1*x2*x3^2*y1^4%:R*y3^2 - 3%:R*x2^2*x3^2*y1^4%:R*y3^2 -
2%:R*x1*x3^3*y1^4%:R*y3^2 + 2%:R*x2*x3^3*y1^4%:R*y3^2 - 6%:R*x1^6%:R*x2*y1*y2*y3^2
- 4%:R*x1^5*x2^2*y1*y2*y3^2 + 18%:R*x1^4%:R*x2^3*y1*y2*y3^2 +
4%:R*x1^3*x2^4%:R*y1*y2*y3^2 - 14%:R*x1^2*x2^5*y1*y2*y3^2 +
2%:R*x2^7%:R*y1*y2*y3^2 + 6%:R*x1^6%:R*x3*y1*y2*y3^2 +
 8%:R*x1^5*x2*x3*y1*y2*y3^2 - 10%:R*x1^4%:R*x2^2*x3*y1*y2*y3^2 -
28%:R*x1^3*x2^3*x3*y1*y2*y3^2 + 10%:R*x1^2*x2^4%:R*x3*y1*y2*y3^2 +
28%:R*x1*x2^5*x3*y1*y2*y3^2 - 14%:R*x2^6%:R*x3*y1*y2*y3^2 -
4%:R*x1^5*x3^2*y1*y2*y3^2 + 2%:R*x1^4%:R*x2*x3^2*y1*y2*y3^2 +
32%:R*x1^3*x2^2*x3^2*y1*y2*y3^2 - 44%:R*x1^2*x2^3*x3^2*y1*y2*y3^2 +
4%:R*x1*x2^4%:R*x3^2*y1*y2*y3^2 + 10%:R*x2^5*x3^2*y1*y2*y3^2 -
10%:R*x1^4%:R*x3^3*y1*y2*y3^2 - 20%:R*x1^3*x2*x3^3*y1*y2*y3^2 +
72%:R*x1^2*x2^2*x3^3*y1*y2*y3^2 - 44%:R*x1*x2^3*x3^3*y1*y2*y3^2 +
2%:R*x2^4%:R*x3^3*y1*y2*y3^2 + 12%:R*x1^3*x3^4%:R*y1*y2*y3^2 -
36%:R*x1^2*x2*x3^4%:R*y1*y2*y3^2 + 36%:R*x1*x2^2*x3^4%:R*y1*y2*y3^2 -
12%:R*x2^3*x3^4%:R*y1*y2*y3^2 + 12%:R*x1^2*x3^5*y1*y2*y3^2 -
 24%:R*x1*x2*x3^5*y1*y2*y3^2 + 12%:R*x2^2*x3^5*y1*y2*y3^2 +
12%:R*x1^3*x2*y1^3*y2*y3^2 + 4%:R*x1^2*x2^2*y1^3*y2*y3^2 -
20%:R*x1*x2^3*y1^3*y2*y3^2 + 4%:R*x2^4%:R*y1^3*y2*y3^2 -
12%:R*x1^3*x3*y1^3*y2*y3^2 - 8%:R*x1^2*x2*x3*y1^3*y2*y3^2 +
16%:R*x1*x2^2*x3*y1^3*y2*y3^2 + 4%:R*x2^3*x3*y1^3*y2*y3^2 +
4%:R*x1^2*x3^2*y1^3*y2*y3^2 - 8%:R*x1*x2*x3^2*y1^3*y2*y3^2 +
4%:R*x2^2*x3^2*y1^3*y2*y3^2 + 12%:R*x1*x3^3*y1^3*y2*y3^2 -
12%:R*x2*x3^3*y1^3*y2*y3^2 - 6%:R*x2*y1^5*y2*y3^2 + 6%:R*x3*y1^5*y2*y3^2 +
6%:R*x1^6%:R*x2*y2^2*y3^2 + 2%:R*x1^5*x2^2*y2^2*y3^2 -
 24%:R*x1^4%:R*x2^3*y2^2*y3^2 + 10%:R*x1^3*x2^4%:R*y2^2*y3^2 +
16%:R*x1^2*x2^5*y2^2*y3^2 - 12%:R*x1*x2^6%:R*y2^2*y3^2 + 2%:R*x2^7%:R*y2^2*y3^2
- 6%:R*x1^6%:R*x3*y2^2*y3^2 - 4%:R*x1^5*x2*x3*y2^2*y3^2 +
20%:R*x1^4%:R*x2^2*x3*y2^2*y3^2 - 4%:R*x1^3*x2^3*x3*y2^2*y3^2 +
4%:R*x1^2*x2^4%:R*x3*y2^2*y3^2 - 20%:R*x1*x2^5*x3*y2^2*y3^2 +
10%:R*x2^6%:R*x3*y2^2*y3^2 + 2%:R*x1^5*x3^2*y2^2*y3^2 -
4%:R*x1^4%:R*x2*x3^2*y2^2*y3^2 - 4%:R*x1^3*x2^2*x3^2*y2^2*y3^2 +
4%:R*x1^2*x2^3*x3^2*y2^2*y3^2 + 10%:R*x1*x2^4%:R*x3^2*y2^2*y3^2 -
 8%:R*x2^5*x3^2*y2^2*y3^2 + 8%:R*x1^4%:R*x3^3*y2^2*y3^2 +
4%:R*x1^3*x2*x3^3*y2^2*y3^2 - 36%:R*x1^2*x2^2*x3^3*y2^2*y3^2 +
28%:R*x1*x2^3*x3^3*y2^2*y3^2 - 4%:R*x2^4%:R*x3^3*y2^2*y3^2 -
6%:R*x1^3*x3^4%:R*y2^2*y3^2 + 18%:R*x1^2*x2*x3^4%:R*y2^2*y3^2 -
18%:R*x1*x2^2*x3^4%:R*y2^2*y3^2 + 6%:R*x2^3*x3^4%:R*y2^2*y3^2 -
6%:R*x1^2*x3^5*y2^2*y3^2 + 12%:R*x1*x2*x3^5*y2^2*y3^2 -
6%:R*x2^2*x3^5*y2^2*y3^2 - 24%:R*x1^3*x2*y1^2*y2^2*y3^2 +
 24%:R*x1*x2^3*y1^2*y2^2*y3^2 + 24%:R*x1^3*x3*y1^2*y2^2*y3^2 -
 24%:R*x2^3*x3*y1^2*y2^2*y3^2 - 24%:R*x1*x3^3*y1^2*y2^2*y3^2 +
 24%:R*x2*x3^3*y1^2*y2^2*y3^2 + 18%:R*x2*y1^4%:R*y2^2*y3^2 -
18%:R*x3*y1^4%:R*y2^2*y3^2 - 4%:R*x1^4%:R*y1*y2^3*y3^2 +
16%:R*x1^3*x2*y1*y2^3*y3^2 + 12%:R*x1^2*x2^2*y1*y2^3*y3^2 -
16%:R*x1*x2^3*y1*y2^3*y3^2 - 8%:R*x2^4%:R*y1*y2^3*y3^2 -
12%:R*x1^3*x3*y1*y2^3*y3^2 - 24%:R*x1*x2^2*x3*y1*y2^3*y3^2 +
36%:R*x2^3*x3*y1*y2^3*y3^2 + 20%:R*x1*x3^3*y1*y2^3*y3^2 -
20%:R*x2*x3^3*y1*y2^3*y3^2 + 4%:R*x1*y1^3*y2^3*y3^2 -
16%:R*x2*y1^3*y2^3*y3^2 + 12%:R*x3*y1^3*y2^3*y3^2 + 3%:R*x1^4%:R*y2^4%:R*y3^2 -
19%:R*x1^2*x2^2*y2^4%:R*y3^2 + 14%:R*x1*x2^3*y2^4%:R*y3^2 + 2%:R*x2^4%:R*y2^4%:R*y3^2
+ 2%:R*x1^2*x2*x3*y2^4%:R*y3^2 + 14%:R*x1*x2^2*x3*y2^4%:R*y3^2 -
16%:R*x2^3*x3*y2^4%:R*y3^2 - x1^2*x3^2*y2^4%:R*y3^2 +
2%:R*x1*x2*x3^2*y2^4%:R*y3^2 - x2^2*x3^2*y2^4%:R*y3^2 -
6%:R*x1*x3^3*y2^4%:R*y3^2 + 6%:R*x2*x3^3*y2^4%:R*y3^2 - 12%:R*x1*y1^2*y2^4%:R*y3^2
+ 12%:R*x3*y1^2*y2^4%:R*y3^2 + 12%:R*x1*y1*y2^5*y3^2 + 6%:R*x2*y1*y2^5*y3^2 -
18%:R*x3*y1*y2^5*y3^2 - 4%:R*x1*y2^6%:R*y3^2 - 2%:R*x2*y2^6%:R*y3^2 +
6%:R*x3*y2^6%:R*y3^2 + 2%:R*x1^6%:R*x2*y1*y3^3 - 2%:R*x1^4%:R*x2^3*y1*y3^3 -
 8%:R*x1^3*x2^4%:R*y1*y3^3 + 6%:R*x1^2*x2^5*y1*y3^3 + 8%:R*x1*x2^6%:R*y1*y3^3 -
6%:R*x2^7%:R*y1*y3^3 - 2%:R*x1^6%:R*x3*y1*y3^3 - 6%:R*x1^4%:R*x2^2*x3*y1*y3^3 +
28%:R*x1^3*x2^3*x3*y1*y3^3 - 18%:R*x1^2*x2^4%:R*x3*y1*y3^3 -
12%:R*x1*x2^5*x3*y1*y3^3 + 10%:R*x2^6%:R*x3*y1*y3^3 +
6%:R*x1^4%:R*x2*x3^2*y1*y3^3 - 24%:R*x1^3*x2^2*x3^2*y1*y3^3 +
36%:R*x1^2*x2^3*x3^2*y1*y3^3 - 24%:R*x1*x2^4%:R*x3^2*y1*y3^3 +
6%:R*x2^5*x3^2*y1*y3^3 + 2%:R*x1^4%:R*x3^3*y1*y3^3 +
4%:R*x1^3*x2*x3^3*y1*y3^3 - 24%:R*x1^2*x2^2*x3^3*y1*y3^3 +
28%:R*x1*x2^3*x3^3*y1*y3^3 - 10%:R*x2^4%:R*x3^3*y1*y3^3 -
4%:R*x1^3*x2*y1^3*y3^3 + 4%:R*x1*x2^3*y1^3*y3^3 + 4%:R*x1^3*x3*y1^3*y3^3 -
4%:R*x2^3*x3*y1^3*y3^3 - 4%:R*x1*x3^3*y1^3*y3^3 + 4%:R*x2*x3^3*y1^3*y3^3 +
2%:R*x2*y1^5*y3^3 - 2%:R*x3*y1^5*y3^3 - 6%:R*x1^6%:R*x2*y2*y3^3 +
 8%:R*x1^5*x2^2*y2*y3^3 + 6%:R*x1^4%:R*x2^3*y2*y3^3 - 8%:R*x1^3*x2^4%:R*y2*y3^3 -
2%:R*x1^2*x2^5*y2*y3^3 + 2%:R*x2^7%:R*y2*y3^3 + 6%:R*x1^6%:R*x3*y2*y3^3 -
16%:R*x1^5*x2*x3*y2*y3^3 + 26%:R*x1^4%:R*x2^2*x3*y2*y3^3 -
28%:R*x1^3*x2^3*x3*y2*y3^3 - 2%:R*x1^2*x2^4%:R*x3*y2*y3^3 +
28%:R*x1*x2^5*x3*y2*y3^3 - 14%:R*x2^6%:R*x3*y2*y3^3 + 8%:R*x1^5*x3^2*y2*y3^3
- 34%:R*x1^4%:R*x2*x3^2*y2*y3^3 + 56%:R*x1^3*x2^2*x3^2*y2*y3^3 -
44%:R*x1^2*x2^3*x3^2*y2*y3^3 + 16%:R*x1*x2^4%:R*x3^2*y2*y3^3 -
2%:R*x2^5*x3^2*y2*y3^3 + 2%:R*x1^4%:R*x3^3*y2*y3^3 -
20%:R*x1^3*x2*x3^3*y2*y3^3 + 48%:R*x1^2*x2^2*x3^3*y2*y3^3 -
44%:R*x1*x2^3*x3^3*y2*y3^3 + 14%:R*x2^4%:R*x3^3*y2*y3^3 +
12%:R*x1^3*x2*y1^2*y2*y3^3 - 4%:R*x1^2*x2^2*y1^2*y2*y3^3 -
4%:R*x1*x2^3*y1^2*y2*y3^3 - 4%:R*x2^4%:R*y1^2*y2*y3^3 -
12%:R*x1^3*x3*y1^2*y2*y3^3 + 8%:R*x1^2*x2*x3*y1^2*y2*y3^3 -
16%:R*x1*x2^2*x3*y1^2*y2*y3^3 + 20%:R*x2^3*x3*y1^2*y2*y3^3 -
4%:R*x1^2*x3^2*y1^2*y2*y3^3 + 8%:R*x1*x2*x3^2*y1^2*y2*y3^3 -
4%:R*x2^2*x3^2*y1^2*y2*y3^3 + 12%:R*x1*x3^3*y1^2*y2*y3^3 -
12%:R*x2*x3^3*y1^2*y2*y3^3 - 6%:R*x2*y1^4%:R*y2*y3^3 + 6%:R*x3*y1^4%:R*y2*y3^3 -
4%:R*x1^4%:R*y1*y2^2*y3^3 - 8%:R*x1^3*x2*y1*y2^2*y3^3 +
20%:R*x1^2*x2^2*y1*y2^2*y3^3 - 24%:R*x1*x2^3*y1*y2^2*y3^3 +
16%:R*x2^4%:R*y1*y2^2*y3^3 + 12%:R*x1^3*x3*y1*y2^2*y3^3 -
16%:R*x1^2*x2*x3*y1*y2^2*y3^3 + 32%:R*x1*x2^2*x3*y1*y2^2*y3^3 -
28%:R*x2^3*x3*y1*y2^2*y3^3 + 8%:R*x1^2*x3^2*y1*y2^2*y3^3 -
16%:R*x1*x2*x3^2*y1*y2^2*y3^3 + 8%:R*x2^2*x3^2*y1*y2^2*y3^3 -
12%:R*x1*x3^3*y1*y2^2*y3^3 + 12%:R*x2*x3^3*y1*y2^2*y3^3 +
4%:R*x1*y1^3*y2^2*y3^3 - 4%:R*x3*y1^3*y2^2*y3^3 + 8%:R*x1^4%:R*y2^3*y3^3 -
16%:R*x1^3*x2*y2^3*y3^3 + 8%:R*x1^2*x2^2*y2^3*y3^3 +
 8%:R*x1*x2^3*y2^3*y3^3 - 8%:R*x2^4%:R*y2^3*y3^3 - 4%:R*x1^3*x3*y2^3*y3^3 +
 8%:R*x1^2*x2*x3*y2^3*y3^3 - 16%:R*x1*x2^2*x3*y2^3*y3^3 +
12%:R*x2^3*x3*y2^3*y3^3 - 4%:R*x1^2*x3^2*y2^3*y3^3 +
 8%:R*x1*x2*x3^2*y2^3*y3^3 - 4%:R*x2^2*x3^2*y2^3*y3^3 +
4%:R*x1*x3^3*y2^3*y3^3 - 4%:R*x2*x3^3*y2^3*y3^3 - 12%:R*x1*y1^2*y2^3*y3^3
+ 16%:R*x2*y1^2*y2^3*y3^3 - 4%:R*x3*y1^2*y2^3*y3^3 + 12%:R*x1*y1*y2^4%:R*y3^3
- 18%:R*x2*y1*y2^4%:R*y3^3 + 6%:R*x3*y1*y2^4%:R*y3^3 - 4%:R*x1*y2^5*y3^3 +
6%:R*x2*y2^5*y3^3 - 2%:R*x3*y2^5*y3^3 + 2%:R*x1^6%:R*x2*y3^4 -
6%:R*x1^5*x2^2*y3^4 + 4%:R*x1^4%:R*x2^3*y3^4 + 4%:R*x1^3*x2^4%:R*y3^4 -
6%:R*x1^2*x2^5*y3^4 + 2%:R*x1*x2^6%:R*y3^4 - 2%:R*x1^6%:R*x3*y3^4 +
12%:R*x1^5*x2*x3*y3^4 - 24%:R*x1^4%:R*x2^2*x3*y3^4 + 16%:R*x1^3*x2^3*x3*y3^4
+ 6%:R*x1^2*x2^4%:R*x3*y3^4 - 12%:R*x1*x2^5*x3*y3^4 + 4%:R*x2^6%:R*x3*y3^4 -
6%:R*x1^5*x3^2*y3^4 + 24%:R*x1^4%:R*x2*x3^2*y3^4 - 36%:R*x1^3*x2^2*x3^2*y3^4
+ 24%:R*x1^2*x2^3*x3^2*y3^4 - 6%:R*x1*x2^4%:R*x3^2*y3^4 - 4%:R*x1^4%:R*x3^3*y3^4
+ 16%:R*x1^3*x2*x3^3*y3^4 - 24%:R*x1^2*x2^2*x3^3*y3^4 +
16%:R*x1*x2^3*x3^3*y3^4 - 4%:R*x2^4%:R*x3^3*y3^4 - 2%:R*x1^3*x2*y1^2*y3^4 +
3%:R*x1^2*x2^2*y1^2*y3^4 - x2^4%:R*y1^2*y3^4 + 2%:R*x1^3*x3*y1^2*y3^4 -
6%:R*x1^2*x2*x3*y1^2*y3^4 + 6%:R*x1*x2^2*x3*y1^2*y3^4 -
2%:R*x2^3*x3*y1^2*y3^4 + 3%:R*x1^2*x3^2*y1^2*y3^4 -
6%:R*x1*x2*x3^2*y1^2*y3^4 + 3%:R*x2^2*x3^2*y1^2*y3^4 +
6%:R*x1^4%:R*y1*y2*y3^4 - 2%:R*x1^3*x2*y1*y2*y3^4 -
 24%:R*x1^2*x2^2*y1*y2*y3^4 + 30%:R*x1*x2^3*y1*y2*y3^4 -
10%:R*x2^4%:R*y1*y2*y3^4 - 4%:R*x1^3*x3*y1*y2*y3^4 +
12%:R*x1^2*x2*x3*y1*y2*y3^4 - 12%:R*x1*x2^2*x3*y1*y2*y3^4 +
4%:R*x2^3*x3*y1*y2*y3^4 - 6%:R*x1^2*x3^2*y1*y2*y3^4 +
12%:R*x1*x2*x3^2*y1*y2*y3^4 - 6%:R*x2^2*x3^2*y1*y2*y3^4 -
6%:R*x1*y1^3*y2*y3^4 + 6%:R*x2*y1^3*y2*y3^4 - 7%:R*x1^4%:R*y2^2*y3^4 +
 8%:R*x1^3*x2*y2^2*y3^4 + 15%:R*x1^2*x2^2*y2^2*y3^4 -
26%:R*x1*x2^3*y2^2*y3^4 + 10%:R*x2^4%:R*y2^2*y3^4 + 2%:R*x1^3*x3*y2^2*y3^4 -
6%:R*x1^2*x2*x3*y2^2*y3^4 + 6%:R*x1*x2^2*x3*y2^2*y3^4 -
2%:R*x2^3*x3*y2^2*y3^4 + 3%:R*x1^2*x3^2*y2^2*y3^4 -
6%:R*x1*x2*x3^2*y2^2*y3^4 + 3%:R*x2^2*x3^2*y2^2*y3^4 +
18%:R*x1*y1^2*y2^2*y3^4 - 18%:R*x2*y1^2*y2^2*y3^4 - 18%:R*x1*y1*y2^3*y3^4
+ 18%:R*x2*y1*y2^3*y3^4 + 6%:R*x1*y2^4%:R*y3^4 - 6%:R*x2*y2^4%:R*y3^4 -
2%:R*x1^4%:R*y1*y3^5 + 2%:R*x1^3*x2*y1*y3^5 + 6%:R*x1^2*x2^2*y1*y3^5 -
10%:R*x1*x2^3*y1*y3^5 + 4%:R*x2^4%:R*y1*y3^5 + 2%:R*x1*y1^3*y3^5 -
2%:R*x2*y1^3*y3^5 + 6%:R*x1^3*x2*y2*y3^5 - 18%:R*x1^2*x2^2*y2*y3^5 +
18%:R*x1*x2^3*y2*y3^5 - 6%:R*x2^4%:R*y2*y3^5 - 6%:R*x1*y1^2*y2*y3^5 +
6%:R*x2*y1^2*y2*y3^5 + 6%:R*x1*y1*y2^2*y3^5 - 6%:R*x2*y1*y2^2*y3^5 -
2%:R*x1*y2^3*y3^5 + 2%:R*x2*y2^3*y3^5 + x1^4%:R*y3^6 - 4%:R*x1^3*x2*y3^6 +
6%:R*x1^2*x2^2*y3^6 - 4%:R*x1*x2^3*y3^6 + x2^4%:R*y3^6.

Lemma from_sander : f1 * f2 = f3.
Proof.
rewrite /f1 /f2 /f3.
Time ring. (* 5.394 secs *)
Time Qed. (* 2.121 secs *)

End BiggerExample.
