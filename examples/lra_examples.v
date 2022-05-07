From mathcomp Require Import all_ssreflect ssralg ssrnum rat.
From mathcomp Require Import lra.

Local Open Scope ring_scope.

Lemma test (F : realFieldType) (x y : F) :
  x + 2%:R * y <= 3%:R -> 2%:R * x + y <= 3%:R -> x + y <= 2%:R.
Proof.
lra.
Qed.

(* Print test. *)
(* Print Assumptions test.  (* Closed under the global context *) *)

Lemma test_rat (x y : rat) :
  x + 2%:R * y <= 3%:R -> 2%:R * x + y <= 3%:R -> x + y <= 2%:R.
Proof.
lra.
Qed.

Lemma test_realDomain (F : realDomainType) (x y : F) :
  x + 2%:R * y <= 3%:R -> 2%:R * x + y <= 3%:R -> x + y <= 2%:R.
Proof.
(* lra. *)
Abort.

Section Tests.

Variable F : realFieldType.

Implicit Types x y : F.

Lemma test_lt x y :
  x + 2%:R * y < 3%:R -> 2%:R * x + y <= 3%:R -> x + y < 2%:R.
Proof.
lra.
Qed.

Lemma test_eq x y :
  x + 2%:R * y = 3%:R -> 2%:R * x + y <= 3%:R -> x + y <= 2%:R.
Proof.
lra.
Qed.

Lemma test_eqop x y :
  x + 2%:R * y == 3%:R -> 2%:R * x + y <= 3%:R -> x + y <= 2%:R.
Proof.
lra.
Qed.

Lemma test_prop_in_middle (C : Prop) x :
  x <= 2%:R -> C -> x <= 3%:R.
Proof.
lra.
Qed.

Lemma test_opp x : x <= 2%:R -> -x >= -2%:R.
Proof.
lra.
Qed.

Lemma test_iff x : x <= 2%:R <-> -x >= -2%:R.
Proof.
lra.
Qed.

Lemma test_eq_bool x : x <= 2%:R = (-x >= -2%:R).
Proof.
lra.
Qed.

Lemma test_not x : x <= 2%:R -> ~ (x > 2%:R).
Proof.
lra.
Qed.

Lemma test_negb x : x <= 2%:R -> ~~ (x > 2%:R).
Proof.
lra.
Qed.

Lemma test_and x : x <= 2%:R -> (x <= 3%:R /\ x <= 4%:R).
Proof.
lra.
Qed.

Lemma test_andb x : x <= 2%:R -> (x <= 3%:R) && (x <= 4%:R).
Proof.
lra.
Qed.

Lemma test_or x : x <= 2%:R -> (x <= 3%:R \/ x <= 1%:R).
Proof.
lra.
Qed.

Lemma test_orb x : x <= 2%:R -> (x <= 3%:R) || (x <= 1%:R).
Proof.
lra.
Qed.

Lemma test_exfalso x (xle2 : x <= 2%:R) (xge3 : x >= 3%:R) : bool.
Proof.
lra.
Qed.

Lemma test_rat_constant x : 0 <= x -> 1 / 3 * x <= 2^-1 * x.
Proof.
lra.
Qed.

End Tests.

(* Examples from the test suite of Coq *)
Section TestsCoq.

Variable F : realFieldType.

Implicit Types x y : F.

Lemma plus_minus x y : 0 = x + y -> 0 = x - y -> 0 = x /\ 0 = y.
Proof.
lra.
Qed.

Lemma plus_minus' x y : 0 = x + y -> 0 = x - y -> 0 = x /\ 0 = y.
Proof.
move=> *.
lra.
Qed.

Lemma cst_test : 5%:R^+5 = 5%:R * 5%:R * 5%:R * 5%:R * 5%:R :> F.
Proof.
lra.
Qed.

Goal forall x y, x <> x -> x > y.
Proof.
move=> *.
lra.
Qed.

Lemma binomial x y : (x + y)^+2 = x^+2 + 2%:R * x * y + y^+2.
Proof.
move=> *.
lra.
Qed.

Lemma hol_light19 x y : 2%:R * y + x = (x + y) + y.
Proof.
lra.
Qed.

Lemma vcgen_25 (n m jt j it i : F) :
  1 * it + -(2%:R) * i + -(1%:R) = 0 ->
  1 * jt + -(2%:R) * j + -(1%:R) = 0 ->
  1 * n + -(10%:R) = 0 ->
  0 <= -(4028%:R)  * i + 6222%:R * j + 705%:R * m + -(16674%:R) ->
  0 <= -(418%:R) * i + 651%:R * j + 94 %:R * m + -(1866%:R) ->
  0 <= -(209%:R) * i + 302%:R * j + 47%:R * m + -(839%:R) ->
  0 <= -(1%:R) * i + 1 * j + -(1%:R) ->
  0 <= -(1%:R) * j + 1 * m + 0 ->
  0 <= 1 * j + 5%:R * m + -(27%:R) ->
  0 <= 2%:R * j + -(1%:R) * m + 2%:R ->
  0 <= 7%:R * j + 10%:R * m + -(74%:R) ->
  0 <= 18%:R * j + -(139%:R) * m + 1188%:R ->
  0 <= 1  * i + 0 ->
  0 <= 121%:R  * i + 810%:R  * j + -(7465%:R) * m + 64350%:R ->
  1 = -(2%:R) * i + it.
Proof.
move=> *.
(* lra. *)
Abort.

Lemma l1 x y z : `|x - z| <= `|x - y| + `|y - z|.
Proof.
Fail intros; split_Rabs; lra.  (* TODO should work *)
Abort.

Lemma l2 x y :
  x < `|y| -> y < 1 -> x >= 0 -> - y <= 1 -> `|x| <= 1.
Proof.
Fail intros; split_Rabs; lra.  (* TODO should work *)
Abort.

(*  Bug 5073 *)
Lemma opp_eq_0_iff x : -x = 0 <-> x = 0.
Proof.
lra.
Qed.

(* From L. Théry *)

Goal forall x y, x = 0 -> x * y = 0.
Proof.
move=> *.
(* nra. *)
Abort.

Goal forall x y, 2%:R * x = 0 -> x * y = 0.
Proof.
move=> *.
(* nra. *)
Abort.

Goal forall x y, - x * x >= 0 -> x * y = 0.
Proof.
move=> *.
(* nra. *)
Abort.

Goal forall x, x * x >= 0.
Proof.
move=> *.
(* nra. *)
Abort.

Goal forall x, -x^+2 >= 0 -> x - 1 >= 0 -> False.
Proof.
move=> *.
(* psatz 3. *)
Abort.

Goal forall x, -x^+2 >= 0 -> x - 1 >= 0 -> False.
Proof.
move=> *.
(* nra. *)
Abort.

Lemma motzkin' x y :
  (x^+2 + y^+2 + 1) * (x^+2 * y^+4 + x^+4*y^+2 + 1 - 3%:R * x^+2 * y^+2) >= 0.
Proof.
move=> *.
(* psatz 3. *)
Abort.

Goal forall x, -x^+2 >= 0 -> x - 1 >= 0 -> False.
Proof.
move=> *.
(* nra. *)
Abort.

Goal 1 / (1 - 1) = 0 :> F.
Proof.
Fail lra. (* division by zero *)
Abort.

Goal 0 / (1 - 1) = 0 :> F.
Proof.
lra.  (* 0 * x = 0 *)
Qed.

Goal 10%:R ^+ 2 = 100%:R :> F.
Proof.
(* pow is reified as a constant *)
lra.
Qed.

Goal ratr (1 / 2%:R) = 1 / 2%:R :> F.
Proof.
Fail lra.  (* TODO should work *)
Abort.

Goal 1 ^+ (2 + 2) = 1 :> F.
Proof.
lra.
Qed.

(* Instance Dplus : DeclaredConstant addn := {}. *)  (* TODO should work *)

Goal 1 ^+ (2 + 2) = 1 :> F.
Proof.
lra.
Qed.

End TestsCoq.
