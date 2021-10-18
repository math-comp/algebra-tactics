From Coq Require Import ZArith ZifyClasses.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat choice seq.
From mathcomp Require Import fintype finfun bigop order ssralg ssrnum ssrint.
From mathcomp Require Import rat.
From mathcomp Require Import ssrZ.
From mathcomp Require Export zify.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.Theory GRing.Theory Num.Theory.

Local Open Scope ring_scope.

Module Import Internals.

Section NumField.

Variable (F : numFieldType).

Structure zifyField := ZifyField {
  fval : F;
  #[canonical=no] nval : int;
  #[canonical=no] dval : int;
  _ : dval != 0;
  _ : fval *~ dval = nval%:~R }.

Arguments ZifyField fval nval dval _ : clear implicits.

Lemma dval_neq0 e : dval e != 0. Proof. by case: e. Qed.

Lemma zifyFieldE e : fval e *~ dval e = (nval e)%:~R. Proof. by case: e. Qed.

Definition zify_zero := ZifyField 0 0 1 erefl erefl.

Lemma zify_opp_subproof e : - fval e *~ dval e = (- nval e)%:~R.
Proof. by rewrite mulNrz mulrNz zifyFieldE. Qed.

Definition zify_opp e :=
  ZifyField (- fval e) (- nval e) (dval e) (dval_neq0 e) (zify_opp_subproof e).

Lemma zify_add_subproof e1 e2 :
  (fval e1 + fval e2) *~ (dval e1 * dval e2) =
  (nval e1 * dval e2 + nval e2 * dval e1)%:~R.
Proof.
by rewrite mulrzDl mulrzDr !mulrzA [fval e2 *~ _ *~ _]mulrzAC !zifyFieldE.
Qed.

Definition zify_add e1 e2 :=
  ZifyField (fval e1 + fval e2) (nval e1 * dval e2 + nval e2 * dval e1)
            (dval e1 * dval e2)
            (mulf_neq0 (dval_neq0 e1) (dval_neq0 e2)) (zify_add_subproof e1 e2).

Lemma zify_mulrz_subproof e n : fval e *~ n *~ dval e = (nval e *~ n)%:~R.
Proof. by rewrite mulrzAC zifyFieldE -mulrzA mulrzz. Qed.

Definition zify_mulrn e n :=
  ZifyField (fval e *+ n) (nval e *+ n) (dval e)
            (dval_neq0 e) (zify_mulrz_subproof e n).

Definition zify_mulrz e n :=
  ZifyField (fval e *~ n) (nval e *~ n) (dval e)
            (dval_neq0 e) (zify_mulrz_subproof e n).

Definition zify_one := ZifyField 1 1 1 erefl erefl.

Lemma zify_mul_subproof e1 e2 :
  (fval e1 * fval e2) *~ (dval e1 * dval e2) = (nval e1 * nval e2)%:~R.
Proof. by rewrite -mulrzr intrM mulrACA !mulrzr !zifyFieldE intrM. Qed.

Definition zify_mul e1 e2 :=
  ZifyField (fval e1 * fval e2) (nval e1 * nval e2) (dval e1 * dval e2)
            (mulf_neq0 (dval_neq0 e1) (dval_neq0 e2)) (zify_mul_subproof e1 e2).

Lemma zify_exprn_subproof e n :
  (fval e ^+ n) *~ (dval e ^+ n) = (nval e ^+ n)%:~R.
Proof. by rewrite -mulrzr !rmorphX /= -exprMn mulrzr zifyFieldE. Qed.

Definition zify_exprn e n :=
  ZifyField (fval e ^+ n) (nval e ^+ n) (dval e ^+ n)
            (expf_neq0 _ (dval_neq0 e)) (zify_exprn_subproof e n).

(* Numerator and denominator of inverse. *)

Definition num_inv (num den : int) : int := if num == 0 then 0 else den.

Definition den_inv (num : int) : int := if num == 0 then 1 else num.

Definition num_invZ (num den : Z) : Z := if Z.eqb num 0 then 0 else den.

Definition den_invZ (num : Z) : Z := if Z.eqb num 0 then 1 else num.

Fact Op_num_inv_subproof n m :
  Z_of_int (num_inv n m) = num_invZ (Z_of_int n) (Z_of_int m).
Proof. rewrite /num_inv /num_invZ; do 2 case: ifP; lia. Qed.

Instance Op_num_inv : BinOp num_inv :=
  { TBOp := num_invZ; TBOpInj := Op_num_inv_subproof }.

Fact Op_den_inv_subproof n : Z_of_int (den_inv n) = den_invZ (Z_of_int n).
Proof. rewrite /den_inv /den_invZ; do 2 case: ifP; lia. Qed.

Instance Op_den_inv : UnOp den_inv :=
  { TUOp := den_invZ; TUOpInj := Op_den_inv_subproof }.

Lemma zify_inv_subproof1 e : den_inv (nval e) != 0.
Proof. by rewrite /den_inv; have [] := eqVneq (nval e). Qed.

Lemma zify_inv_subproof2 e :
  (fval e)^-1 *~ den_inv (nval e) = (num_inv (nval e) (dval e))%:~R.
Proof.
rewrite /num_inv /den_inv -(intr_eq0 F) -zifyFieldE mulrz_eq0 -[_ == _]negbK.
rewrite dval_neq0 /=.
have [->|e_neq0] := eqVneq; first by rewrite invr0.
rewrite -[LHS]mulrzr; apply: (mulfI e_neq0).
by rewrite mulrA divff // mul1r mulrzr zifyFieldE.
Qed.

Definition zify_inv e :=
  ZifyField (fval e)^-1 (num_inv (nval e) (dval e)) (den_inv (nval e))
            (zify_inv_subproof1 e) (zify_inv_subproof2 e).

(* Workaround: let Micromega recognize that [denq] is a positive integer.     *)
(* Ideally, [denq_pos] should be replaced with [denq].                        *)

Definition denq_pos (x : rat) : positive := Pos.of_nat `|denq x|.

Lemma zify_ratr_subproof1 x : Pos.to_nat (denq_pos x) != 0 :> int.
Proof. lia. Qed.

Lemma zify_ratr_subproof2 x :
  ratr x *+ Pos.to_nat (denq_pos x) = (numq x)%:~R :> F.
Proof.
rewrite /denq_pos /absz; case: ratP => n d _; rewrite Nat2Pos.id //.
rewrite rmorphM /= [ratr _^-1]fmorphV /= ?ratr_int.
by rewrite pmulrn -[LHS]mulrzr divfK // intr_eq0.
Qed.

Definition zify_ratr x :=
  ZifyField (ratr x) (numq x) (Pos.to_nat (denq_pos x))
            (zify_ratr_subproof1 x) (zify_ratr_subproof2 x).

Lemma zify_eqb e1 e2 :
  (fval e1 == fval e2) = (nval e1 * dval e2 == nval e2 * dval e1).
Proof.
rewrite -[RHS](eqr_int F) !intrM -!zifyFieldE !mulrzr -!mulrzA.
rewrite [dval e2 * _]mulrC; apply/eqP/eqP => [-> //|].
rewrite -mulrzr -[RHS]mulrzr; apply: mulIf.
by rewrite intr_eq0; apply/mulf_neq0/dval_neq0/dval_neq0.
Qed.

Lemma zify_lef e1 e2 :
  (fval e1 <= fval e2) =
  ((0 < dval e1) && (0 < dval e2) || (dval e1 < 0) && (dval e2 < 0)) &&
  (nval e1 * dval e2 <= nval e2 * dval e1) ||
  ((0 < dval e1) && (dval e2 < 0) || (dval e1 < 0) && (0 < dval e2)) &&
  (nval e2 * dval e1 <= nval e1 * dval e2).
Proof.
rewrite -![_ * _ <= _ * _](ler_int F) !intrM -!zifyFieldE !mulrzr -!mulrzA.
rewrite [dval e2 * _]mulrC -mulrzr -[fval e2 *~ _]mulrzr.
case: ltgtP (dval_neq0 e1) (dval_neq0 e2) => //= [pos_e1|neg_e1] _;
  case: ltgtP => //= [pos_e2|neg_e2] _.
- by rewrite orbF ler_pmul2r // ltr0z pmulr_lgt0.
- by rewrite ler_nmul2r // ltrz0 nmulr_llt0.
- by rewrite orbF ler_pmul2r // ltr0z nmulr_lgt0.
- by rewrite ler_nmul2r // ltrz0 pmulr_llt0.
Qed.

Lemma zify_ltf e1 e2 :
  (fval e1 < fval e2) =
  ((0 < dval e1) && (0 < dval e2) || (dval e1 < 0) && (dval e2 < 0)) &&
  (nval e1 * dval e2 < nval e2 * dval e1) ||
  ((0 < dval e1) && (dval e2 < 0) || (dval e1 < 0) && (0 < dval e2)) &&
  (nval e2 * dval e1 < nval e1 * dval e2).
Proof.
rewrite -![_ * _ < _ * _](ltr_int F) !intrM -!zifyFieldE !mulrzr -!mulrzA.
rewrite [dval e2 * _]mulrC -mulrzr -[fval e2 *~ _]mulrzr.
case: ltgtP (dval_neq0 e1) (dval_neq0 e2) => //= [pos_e1|neg_e1] _;
  case: ltgtP => //= [pos_e2|neg_e2] _.
- by rewrite orbF ltr_pmul2r // ltr0z pmulr_lgt0.
- by rewrite ltr_nmul2r // ltrz0 nmulr_llt0.
- by rewrite orbF ltr_pmul2r // ltr0z nmulr_lgt0.
- by rewrite ltr_nmul2r // ltrz0 pmulr_llt0.
Qed.

End NumField.

End Internals.

Canonical zify_zero.
Canonical zify_opp.
Canonical zify_add.
Canonical zify_mulrn.
Canonical zify_mulrz.
Canonical zify_one.
Canonical zify_mul.
Canonical zify_exprn.
Canonical zify_inv.
Canonical zify_ratr.
Add Zify BinOp Op_num_inv.
Add Zify UnOp Op_den_inv.

Ltac zify_field :=
  repeat
    match goal with
      | [H : context [eq_op]    |- _] => rewrite zify_eqb /= in H
      | [H : context [Order.le] |- _] => rewrite zify_lef /= in H
      | [H : context [Order.lt] |- _] => rewrite zify_ltf /= in H
    end;
  rewrite ?(zify_eqb, zify_lef, zify_ltf) /=.

Ltac field_lia := zify_field; lia.
Ltac field_nia := zify_field; nia.
