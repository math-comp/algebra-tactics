From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat choice seq.
From mathcomp Require Import fintype finfun bigop order ssralg ssrnum ssrint.
From mathcomp Require Export zify.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.

Local Open Scope ring_scope.

Module Import Internals.

Section Ring.

Variable R : ringType.

Structure zifyRing := ZifyRing { rval : R; zval : int; _ : rval = zval%:~R }.

Arguments ZifyRing rval zval _ : clear implicits.

Lemma zifyRingE (e : zifyRing) : rval e = (zval e)%:~R. Proof. by case: e. Qed.

Definition zify_zero := ZifyRing 0%R 0%R erefl.

Lemma zify_opp_subproof e1 : - rval e1 = (- zval e1)%:~R.
Proof. by rewrite zifyRingE mulrNz. Qed.

Definition zify_opp e1 :=
  ZifyRing (- rval e1) (- zval e1) (zify_opp_subproof e1).

Lemma zify_add_subproof e1 e2 : rval e1 + rval e2 = (zval e1 + zval e2)%:~R.
Proof. by rewrite 2!zifyRingE intrD. Qed.

Definition zify_add e1 e2 :=
  ZifyRing (rval e1 + rval e2) (zval e1 + zval e2) (zify_add_subproof e1 e2).

Lemma zify_mulrz_subproof e1 n : rval e1 *~ n = (zval e1 *~ n)%:~R.
Proof. by rewrite zifyRingE -mulrzA -mulrzz. Qed.

Definition zify_mulrn e1 n :=
  ZifyRing (rval e1 *+ n) (zval e1 *+ n) (zify_mulrz_subproof e1 n).

Definition zify_mulrz e1 n :=
  ZifyRing (rval e1 *~ n) (zval e1 *~ n) (zify_mulrz_subproof e1 n).

Definition zify_one := ZifyRing 1%R 1%R erefl.

Lemma zify_mul_subproof e1 e2 : rval e1 * rval e2 = (zval e1 * zval e2)%:~R.
Proof. by rewrite 2!zifyRingE intrM. Qed.

Definition zify_mul e1 e2 :=
  ZifyRing (rval e1 * rval e2) (zval e1 * zval e2) (zify_mul_subproof e1 e2).

Lemma zify_exprn_subproof e1 n : rval e1 ^+ n = (zval e1 ^+ n)%:~R.
Proof. by rewrite zifyRingE; elim: n => //= n; rewrite !exprS intrM => ->. Qed.

Definition zify_exprn e1 n :=
  ZifyRing (rval e1 ^+ n) (zval e1 ^+ n) (zify_exprn_subproof e1 n).

End Ring.

Lemma zify_eqb (R : numDomainType) (e1 e2 : zifyRing R) :
  (rval e1 == rval e2) = (zval e1 == zval e2).
Proof. by rewrite 2!zifyRingE eqr_int. Qed.

Lemma zify_ler (R : numDomainType) (e1 e2 : zifyRing R) :
  (rval e1 <= rval e2) = (zval e1 <= zval e2).
Proof. by rewrite 2!zifyRingE ler_int. Qed.

Lemma zify_ltr (R : numDomainType) (e1 e2 : zifyRing R) :
  (rval e1 < rval e2) = (zval e1 < zval e2).
Proof. by rewrite 2!zifyRingE ltr_int. Qed.

End Internals.

Canonical zify_zero.
Canonical zify_opp.
Canonical zify_add.
Canonical zify_mulrn.
Canonical zify_mulrz.
Canonical zify_one.
Canonical zify_mul.
Canonical zify_exprn.

Ltac zify_ring :=
  repeat
    match goal with
      | [H : context [eq_op]    |- _] => rewrite zify_eqb /= in H
      | [H : context [Order.le] |- _] => rewrite zify_ler /= in H
      | [H : context [Order.lt] |- _] => rewrite zify_ltr /= in H
    end;
  rewrite ?(zify_eqb, zify_ler, zify_ltr) /=.

Ltac lia_ring := zify_ring; lia.
Ltac nia_ring := zify_ring; nia.
