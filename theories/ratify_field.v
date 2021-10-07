From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat choice seq.
From mathcomp Require Import fintype finfun bigop order ssralg ssrnum ssrint.
From mathcomp Require Import rat.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.Theory GRing.Theory.

Local Open Scope ring_scope.

Module Import Internals.

Section NumField.

Variable (F : numFieldType).

Structure ratifyField :=
  RatifyField { fval : F; rval : rat; _ : fval = ratr rval }.

Arguments RatifyField fval rval _ : clear implicits.

Lemma ratifyFieldE e : fval e = ratr (rval e). Proof. by case: e. Qed.

Definition ratify_zero := RatifyField 0 0 (esym (ratr_int F 0)).

Lemma ratify_opp_subproof e : - fval e = ratr (- rval e).
Proof. by rewrite ratifyFieldE raddfN. Qed.

Definition ratify_opp e :=
  RatifyField (- fval e) (- rval e) (ratify_opp_subproof e).

Lemma ratify_add_subproof e1 e2 : fval e1 + fval e2 = ratr (rval e1 + rval e2).
Proof. by rewrite !ratifyFieldE raddfD. Qed.

Definition ratify_add e1 e2 := RatifyField
  (fval e1 + fval e2) (rval e1 + rval e2) (ratify_add_subproof e1 e2).

Lemma ratify_mulrz_subproof e n : fval e *~ n = ratr (rval e *~ n).
Proof. by rewrite ratifyFieldE rmorphMz. Qed.

Definition ratify_mulrn e n :=
  RatifyField (fval e *+ n) (rval e *+ n) (ratify_mulrz_subproof e n).

Definition ratify_mulrz e n :=
  RatifyField (fval e *~ n) (rval e *~ n) (ratify_mulrz_subproof e n).

Definition ratify_one := RatifyField 1 1 (esym (ratr_int F 1)).

Lemma ratify_mul_subproof e1 e2 : fval e1 * fval e2 = ratr (rval e1 * rval e2).
Proof. by rewrite !ratifyFieldE rmorphM. Qed.

Definition ratify_mul e1 e2 := RatifyField
  (fval e1 * fval e2) (rval e1 * rval e2) (ratify_mul_subproof e1 e2).

Lemma ratify_exprn_subproof e n : fval e ^+ n = ratr (rval e ^+ n).
Proof. by rewrite ratifyFieldE rmorphX. Qed.

Definition ratify_exprn e n :=
  RatifyField (fval e ^+ n) (rval e ^+ n) (ratify_exprn_subproof e n).

Lemma ratify_inv_subproof e : (fval e)^-1 = ratr (rval e)^-1.
Proof. by rewrite ratifyFieldE fmorphV. Qed.

Definition ratify_inv e :=
  RatifyField (fval e)^-1 (rval e)^-1 (ratify_inv_subproof e).

Definition ratify_ratr x := RatifyField (ratr x) x erefl.

Lemma ratify_eqb e1 e2 : (fval e1 == fval e2) = (rval e1 == rval e2).
Proof. by rewrite 2!ratifyFieldE eq_le !ler_rat -eq_le. Qed.

Lemma ratify_lef e1 e2 : (fval e1 <= fval e2) = (rval e1 <= rval e2).
Proof. by rewrite 2!ratifyFieldE ler_rat. Qed.

Lemma ratify_ltf e1 e2 : (fval e1 < fval e2) = (rval e1 < rval e2).
Proof. by rewrite 2!ratifyFieldE ltr_rat. Qed.

End NumField.

End Internals.

Canonical ratify_zero.
Canonical ratify_opp.
Canonical ratify_add.
Canonical ratify_mulrn.
Canonical ratify_mulrz.
Canonical ratify_one.
Canonical ratify_mul.
Canonical ratify_exprn.
Canonical ratify_inv.
Canonical ratify_ratr.

Ltac ratify_field :=
  repeat
    match goal with
      | [H : context [eq_op]    |- _] => rewrite ratify_eqb /= in H
      | [H : context [Order.le] |- _] => rewrite ratify_lef /= in H
      | [H : context [Order.lt] |- _] => rewrite ratify_ltf /= in H
    end;
  rewrite ?(ratify_eqb, ratify_lef, ratify_ltf) /=.
