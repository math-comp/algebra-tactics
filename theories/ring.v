From Coq Require Import ZArith ZifyClasses Ring Ring_polynom Field_theory.
From elpi Require Export elpi.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat choice seq.
From mathcomp Require Import fintype finfun bigop order ssralg ssrnum ssrint.
From mathcomp Require Import ssrZ zify.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.

Local Open Scope ring_scope.

Module Import Internals.

Implicit Types (V : zmodType) (R : ringType) (F : fieldType).

(* In reified syntax trees, constants must be represented by binary integers  *)
(* `N` and `Z`. For the fine-grained control of conversion, we provide        *)
(* transparent (immediately expanding) versions of `N -> nat` and  `Z -> int` *)
(* conversions.                                                               *)

Definition addn_expand := Eval compute in addn.

Fixpoint nat_of_pos_rec_expand (p : positive) (a : nat) : nat :=
  match p with
  | p0~1 => addn_expand a (nat_of_pos_rec_expand p0 (addn_expand a a))
  | p0~0 => nat_of_pos_rec_expand p0 (addn_expand a a)
  | 1 => a
  end%positive.

Definition nat_of_pos_expand (p : positive) : nat := nat_of_pos_rec_expand p 1.

Definition nat_of_N_expand (n : N) : nat :=
  if n is N.pos p then nat_of_pos_expand p else 0%N.

Definition int_of_Z_expand (n : Z) : int :=
  match n with
    | Z0 => Posz 0
    | Zpos p => Posz (nat_of_pos_expand p)
    | Zneg p => Negz (nat_of_pos_expand p).-1
  end.

Lemma nat_of_N_expandE : nat_of_N_expand = nat_of_N. Proof. by []. Qed.
Lemma int_of_Z_expandE : int_of_Z_expand = int_of_Z. Proof. by []. Qed.

(* Pushing down morphisms in ring and field expressions by reflection         *)

Inductive NExpr : Type :=
  | NC    of N
  | NX    of nat
  | NAdd  of NExpr & NExpr
  | NSucc of NExpr
  | NMul  of NExpr & NExpr
  | NExp  of NExpr & N.

Fixpoint Neval (e : NExpr) : nat :=
  match e with
    | NC n => nat_of_N_expand n
    | NX x => x
    | NAdd e1 e2 => Neval e1 + Neval e2
    | NSucc e => S (Neval e)
    | NMul e1 e2 => Neval e1 * Neval e2
    | NExp e1 n => Neval e1 ^ nat_of_N_expand n
  end.

Inductive RExpr : ringType -> Type :=
  | RX R : R -> RExpr R
  | R0 R : RExpr R
  | ROpp R : RExpr R -> RExpr R
  | RZOpp : RExpr [ringType of Z] -> RExpr [ringType of Z]
  | RAdd R : RExpr R -> RExpr R -> RExpr R
  | RZAdd : RExpr [ringType of Z] -> RExpr [ringType of Z] ->
            RExpr [ringType of Z]
  | RZSub : RExpr [ringType of Z] -> RExpr [ringType of Z] ->
            RExpr [ringType of Z]
  | RMuln R : RExpr R -> NExpr -> RExpr R
  | RMulz R : RExpr R -> RExpr [ringType of int] -> RExpr R
  | R1 R : RExpr R
  | RMul R : RExpr R -> RExpr R -> RExpr R
  | RZMul : RExpr [ringType of Z] -> RExpr [ringType of Z] ->
            RExpr [ringType of Z]
  | RExpn R : RExpr R -> N -> RExpr R
  | RExpPosz (R : unitRingType) : RExpr R -> N -> RExpr R
  | RExpNegz F : RExpr F -> N -> RExpr F
  | RZExp : RExpr [ringType of Z] -> Z -> RExpr [ringType of Z]
  | RInv F : RExpr F -> RExpr F
  | RMorph R' R : {rmorphism R' -> R} -> RExpr R' -> RExpr R
  | RMorph' V R : {additive V -> R} -> ZMExpr V -> RExpr R
  | RPosz : NExpr -> RExpr [ringType of int]
  | RNegz : NExpr -> RExpr [ringType of int]
  | RZC : Z -> RExpr [ringType of Z]
with ZMExpr : zmodType -> Type :=
  | ZMX V : V -> ZMExpr V
  | ZM0 V : ZMExpr V
  | ZMOpp V : ZMExpr V -> ZMExpr V
  | ZMAdd V : ZMExpr V -> ZMExpr V -> ZMExpr V
  | ZMMuln V : ZMExpr V -> NExpr -> ZMExpr V
  | ZMMulz V : ZMExpr V -> RExpr [ringType of int] -> ZMExpr V
  | ZMMorph V' V : {additive V' -> V} -> ZMExpr V' -> ZMExpr V.

Scheme RExpr_ind' := Induction for RExpr Sort Prop
  with ZMExpr_ind' := Induction for ZMExpr Sort Prop.

Fixpoint Reval R (e : RExpr R) : R :=
  match e with
    | RX _ x => x
    | R0 _ => 0%R
    | ROpp _ e1 => - Reval e1
    | RZOpp e1 => Z.opp (Reval e1)
    | RAdd _ e1 e2 => Reval e1 + Reval e2
    | RZAdd e1 e2 => Z.add (Reval e1) (Reval e2)
    | RZSub e1 e2 => Z.sub (Reval e1) (Reval e2)
    | RMuln _ e1 e2 => Reval e1 *+ Neval e2
    | RMulz _ e1 e2 => Reval e1 *~ Reval e2
    | R1 _ => 1%R
    | RMul _ e1 e2 => Reval e1 * Reval e2
    | RZMul e1 e2 => Z.mul (Reval e1) (Reval e2)
    | RExpn _ e1 n => Reval e1 ^+ nat_of_N_expand n
    | RExpPosz _ e1 n => Reval e1 ^ Posz (nat_of_N_expand n)
    | RExpNegz _ e1 n => Reval e1 ^ Negz (nat_of_N_expand n)
    | RZExp e1 n => Z.pow (Reval e1) n
    | RInv _ e1 => (Reval e1)^-1
    | RMorph _ _ f e1 => f (Reval e1)
    | RMorph' _ _ f e1 => f (ZMeval e1)
    | RPosz e1 => Posz (Neval e1)
    | RNegz e2 => Negz (Neval e2)
    | RZC x => x
  end
with ZMeval V (e : ZMExpr V) : V :=
  match e with
    | ZMX _ x => x
    | ZM0 _ => 0%R
    | ZMOpp _ e1 => - ZMeval e1
    | ZMAdd _ e1 e2 => ZMeval e1 + ZMeval e2
    | ZMMuln _ e1 e2 => ZMeval e1 *+ Neval e2
    | ZMMulz _ e1 e2 => ZMeval e1 *~ Reval e2
    | ZMMorph _ _ f e1 => f (ZMeval e1)
  end.

Fixpoint interp_RElist
    R (lpe : list (RExpr R * RExpr R * PExpr Z * PExpr Z)) : Prop :=
  if lpe is (lhs, rhs, _, _) :: lpe then
    Reval lhs = Reval rhs /\ interp_RElist lpe else True.

Section Rnorm.

Variables (R' : ringType).
Variables (R_of_Z : Z -> R') (R_of_ZE : R_of_Z = (fun n => (int_of_Z n)%:~R)).
Variables (zero : R') (zeroE : zero = 0%R) (opp : R' -> R') (oppE : opp = -%R).
Variables (add : R' -> R' -> R') (addE : add = +%R).
Variables (sub : R' -> R' -> R') (subE : sub = (fun x y => x - y)).
Variables (one : R') (oneE : one = 1%R).
Variables (mul : R' -> R' -> R') (mulE : mul = *%R).
Variables (exp : R' -> N -> R') (expE : exp = (fun x n => x ^+ nat_of_N n)).

Fixpoint Nnorm (e : NExpr) : R' :=
  match e with
    | NC N0 => R_of_Z Z0
    | NC (Npos n) => R_of_Z (Zpos n)
    | NX x => x%:~R
    | NAdd e1 e2 => add (Nnorm e1) (Nnorm e2)
    | NSucc e1 => add one (Nnorm e1)
    | NMul e1 e2 => mul (Nnorm e1) (Nnorm e2)
    | NExp e1 n => exp (Nnorm e1) n
  end.

Lemma Nnorm_correct (e : NExpr) : (Neval e)%:R = Nnorm e.
Proof.
elim: e => //=.
- by case; rewrite R_of_ZE.
- by move=> e1 IHe1 e2 IHe2; rewrite addE natrD IHe1 IHe2.
- by move=> e IHe; rewrite addE oneE mulrS IHe.
- by move=> e1 IHe1 e2 IHe2; rewrite mulE natrM IHe1 IHe2.
- by move=> e1 IHe1 e2; rewrite expE natrX IHe1.
Qed.

Fixpoint Rnorm R (f : {rmorphism R -> R'}) (e : RExpr R) : R' :=
  match e in RExpr R return {rmorphism R -> R'} -> R' with
    | RX _ x => fun f => f x
    | R0 _ => fun => zero
    | ROpp _ e1 => fun f => opp (Rnorm f e1)
    | RZOpp e1 => fun f => opp (Rnorm f e1)
    | RAdd _ e1 e2 => fun f => add (Rnorm f e1) (Rnorm f e2)
    | RZAdd e1 e2 => fun f => add (Rnorm f e1) (Rnorm f e2)
    | RZSub e1 e2 => fun f => sub (Rnorm f e1) (Rnorm f e2)
    | RMuln _ e1 e2 => fun f => mul (Rnorm f e1) (Nnorm e2)
    | RMulz _ e1 e2 => fun f =>
        mul (Rnorm f e1) (Rnorm [rmorphism of intmul 1] e2)
    | R1 _ => fun => one
    | RMul _ e1 e2 => fun f => mul (Rnorm f e1) (Rnorm f e2)
    | RZMul e1 e2 => fun f => mul (Rnorm f e1) (Rnorm f e2)
    | RExpn _ e1 n => fun f => exp (Rnorm f e1) n
    | RExpPosz _ e1 n => fun f => exp (Rnorm f e1) n
    | RExpNegz _ _ _ => fun _ => f (Reval e)
    | RZExp e1 (Z.neg _) => fun f => zero
    | RZExp e1 n => fun f => exp (Rnorm f e1) (Z.to_N n)
    | RInv _ _ => fun _ => f (Reval e)
    | RMorph _ _ g e1 => fun f => Rnorm [rmorphism of f \o g] e1
    | RMorph' _ _ g e1 => fun f => RZMnorm [additive of f \o g] e1
    | RPosz e1 => fun => Nnorm e1
    | RNegz e1 => fun => opp (add one (Nnorm e1))
    | RZC x => fun => R_of_Z x
  end f
with RZMnorm V (f : {additive V -> R'}) (e : ZMExpr V) : R' :=
  match e in ZMExpr V return {additive V -> R'} -> R' with
    | ZMX _ x => fun f => f x
    | ZM0 _ => fun => zero
    | ZMOpp _ e1 => fun f => opp (RZMnorm f e1)
    | ZMAdd _ e1 e2 => fun f => add (RZMnorm f e1) (RZMnorm f e2)
    | ZMMuln _ e1 e2 => fun f => mul (RZMnorm f e1) (Nnorm e2)
    | ZMMulz _ e1 e2 => fun f =>
        mul (RZMnorm f e1) (Rnorm [rmorphism of intmul 1] e2)
    | ZMMorph _ _ g e1 => fun f => RZMnorm [additive of f \o g] e1
  end f.

Fixpoint norm_RElist
    (lpe : list (RExpr R' * RExpr R' * PExpr Z * PExpr Z)) : seq R' :=
  if lpe is (lhs, rhs, _, _) :: lpe then
    Rnorm [rmorphism of idfun] lhs ::
    Rnorm [rmorphism of idfun] rhs :: norm_RElist lpe
  else
    [::].

Lemma Rnorm_correct_rec R (f : {rmorphism R -> R'}) (e : RExpr R) :
  f (Reval e) = Rnorm f e.
Proof.
pose P R e := forall (f : {rmorphism R -> R'}), f (Reval e) = Rnorm f e.
pose P0 V e := forall (f : {additive V -> R'}), f (ZMeval e) = RZMnorm f e.
move: f; elim e using (@RExpr_ind' P P0); rewrite {R e}/P {}/P0 //=.
- by move=> R f; rewrite rmorph0 zeroE.
- by move=> R e1 IHe1 f; rewrite rmorphN IHe1 oppE.
- by move=> e1 IHe1 f; rewrite rmorphN IHe1 oppE.
- by move=> R e1 IHe1 e2 IHe2 f; rewrite rmorphD IHe1 IHe2 addE.
- by move=> e1 IHe1 e2 IHe2 f; rewrite rmorphD IHe1 IHe2 addE.
- by move=> e1 IHe1 e2 IHe2 f; rewrite rmorphB IHe1 IHe2 subE.
- by move=> R e1 IHe1 e2 f; rewrite rmorphMn IHe1 -mulr_natr Nnorm_correct mulE.
- by move=> R e1 IHe1 e2 IHe2 f; rewrite rmorphMz IHe1 -mulrzr IHe2 mulE.
- by move=> R f; rewrite rmorph1 oneE.
- by move=> R e1 IHe1 e2 IHe2 f; rewrite rmorphM IHe1 IHe2 mulE.
- by move=> e1 IHe1 e2 IHe2 f; rewrite rmorphM IHe1 IHe2 mulE.
- by move=> R e1 IHe1 e2 f; rewrite rmorphX IHe1 expE.
- by move=> R e1 IHe1 e2 f; rewrite rmorphX IHe1 expE.
- move=> e1 IHe1 [|n|n] f; rewrite !(zeroE, expE, rmorph0, rmorph1) //=.
  rewrite -IHe1 -rmorphX; congr (f _); lia.
- by move=> R S g e1 IHe1 f; rewrite -IHe1.
- by move=> V R g e1 IHe1 f; rewrite -IHe1.
- by move=> e f; rewrite -[Posz _]intz rmorph_int [LHS]Nnorm_correct.
- move=> e f; rewrite -[Negz _]intz rmorph_int /intmul mulrS Nnorm_correct.
  by rewrite oppE addE oneE.
- by move=> x f; rewrite R_of_ZE -(rmorph_int f); congr (f _); lia.
- by move=> V f; rewrite raddf0 zeroE.
- by move=> V e1 IHe1 f; rewrite raddfN IHe1 oppE.
- by move=> V e1 IHe1 e2 IHe2 f; rewrite raddfD IHe1 IHe2 addE.
- move=> V e1 IHe1 e2 f.
  by rewrite raddfMn IHe1 -mulr_natr Nnorm_correct mulE.
- by move=> V e1 IHe1 e2 IHe2 f; rewrite raddfMz IHe1 -mulrzr IHe2 mulE.
- by move=> V V' g e1 IHe1 f; rewrite -IHe1.
Qed.

Lemma Rnorm_correct (e : RExpr R') : Reval e = Rnorm [rmorphism of idfun] e.
Proof. exact: Rnorm_correct_rec [rmorphism of idfun] _. Qed.

End Rnorm.

Section Fnorm.

Variables (F : fieldType).
Variables (F_of_Z : Z -> F) (F_of_ZE : F_of_Z = (fun n => (int_of_Z n)%:~R)).
Variables (zero : F) (zeroE : zero = 0%R) (opp : F -> F) (oppE : opp = -%R).
Variables (add : F -> F -> F) (addE : add = +%R).
Variables (sub : F -> F -> F) (subE : sub = (fun x y => x - y)).
Variables (one : F) (oneE : one = 1%R) (mul : F -> F -> F) (mulE : mul = *%R).
Variables (exp : F -> N -> F) (expE : exp = (fun x n => x ^+ nat_of_N n)).
Variables (inv : F -> F) (invE : inv = GRing.inv).

Notation Nnorm := (Nnorm F_of_Z add one mul exp).
Let Nnorm_correct := (Nnorm_correct F_of_ZE addE oneE mulE expE).

Fixpoint Fnorm R (f : {rmorphism R -> F}) (e : RExpr R) : F :=
  match e in RExpr R return {rmorphism R -> F} -> F with
    | RX _ x => fun f => f x
    | R0 _ => fun => zero
    | ROpp _ e1 => fun f => opp (Fnorm f e1)
    | RZOpp e1 => fun f => opp (Fnorm f e1)
    | RAdd _ e1 e2 => fun f => add (Fnorm f e1) (Fnorm f e2)
    | RZAdd e1 e2 => fun f => add (Fnorm f e1) (Fnorm f e2)
    | RZSub e1 e2 => fun f => sub (Fnorm f e1) (Fnorm f e2)
    | RMuln _ e1 e2 => fun f => mul (Fnorm f e1) (Nnorm e2)
    | RMulz _ e1 e2 => fun f =>
        mul (Fnorm f e1) (Fnorm [rmorphism of intmul 1] e2)
    | R1 _ => fun => one
    | RMul _ e1 e2 => fun f => mul (Fnorm f e1) (Fnorm f e2)
    | RZMul e1 e2 => fun f => mul (Fnorm f e1) (Fnorm f e2)
    | RExpn _ e1 n => fun f => exp (Fnorm f e1) n
    | RExpPosz _ e1 n => fun f => exp (Fnorm f e1) n
    | RExpNegz _ e1 n => fun f => inv (exp (Fnorm f e1) (N.succ n))
    | RZExp e1 (Z.neg _) => fun f => zero
    | RZExp e1 n => fun f => exp (Fnorm f e1) (Z.to_N n)
    | RInv _ e1 => fun f => inv (Fnorm f e1)
    | RMorph _ _ g e1 => fun f => Fnorm [rmorphism of f \o g] e1
    | RMorph' _ _ g e1 => fun f => FZMnorm [additive of f \o g] e1
    | RPosz e1 => fun => Nnorm e1
    | RNegz e1 => fun => opp (add one (Nnorm e1))
    | RZC x => fun => F_of_Z x
  end f
with FZMnorm V (f : {additive V -> F}) (e : ZMExpr V) : F :=
  match e in ZMExpr V return {additive V -> F} -> F with
    | ZMX _ x => fun f => f x
    | ZM0 _ => fun => zero
    | ZMOpp _ e1 => fun f => opp (FZMnorm f e1)
    | ZMAdd _ e1 e2 => fun f => add (FZMnorm f e1) (FZMnorm f e2)
    | ZMMuln _ e1 e2 => fun f => mul (FZMnorm f e1) (Nnorm e2)
    | ZMMulz _ e1 e2 => fun f =>
        mul (FZMnorm f e1) (Fnorm [rmorphism of intmul 1] e2)
    | ZMMorph _ _ g e1 => fun f => FZMnorm [additive of f \o g] e1
  end f.

Lemma Fnorm_correct_rec R (f : {rmorphism R -> F}) (e : RExpr R) :
  f (Reval e) = Fnorm f e.
Proof.
pose P R e := forall (f : {rmorphism R -> F}), f (Reval e) = Fnorm f e.
pose P0 V e := forall (f : {additive V -> F}), f (ZMeval e) = FZMnorm f e.
move: f; elim e using (@RExpr_ind' P P0); rewrite {R e}/P {}/P0 //=.
- by move=> R f; rewrite rmorph0 zeroE.
- by move=> R e1 IHe1 f; rewrite rmorphN IHe1 oppE.
- by move=> e1 IHe1 f; rewrite rmorphN IHe1 oppE.
- by move=> R e1 IHe1 e2 IHe2 f; rewrite rmorphD IHe1 IHe2 addE.
- by move=> e1 IHe1 e2 IHe2 f; rewrite rmorphD IHe1 IHe2 addE.
- by move=> e1 IHe1 e2 IHe2 f; rewrite rmorphB IHe1 IHe2 subE.
- move=> R e1 IHe1 e2 f.
  by rewrite rmorphMn IHe1 -mulr_natr Nnorm_correct mulE.
- by move=> R e1 IHe1 e2 IHe2 f; rewrite rmorphMz IHe1 -mulrzr IHe2 mulE.
- by move=> R f; rewrite rmorph1 oneE.
- by move=> R e1 IHe1 e2 IHe2 f; rewrite rmorphM IHe1 IHe2 mulE.
- by move=> e1 IHe1 e2 IHe2 f; rewrite rmorphM IHe1 IHe2 mulE.
- by move=> R e1 IHe1 e2 f; rewrite rmorphX IHe1 expE.
- by move=> R e1 IHe1 n f; rewrite rmorphX IHe1 expE.
- move=> R e1 IHe1 n f; rewrite fmorphV rmorphX IHe1 invE expE.
  rewrite nat_of_N_expandE; congr (_ ^- _); lia.
- move=> e1 IHe1 [|n|n] f; rewrite ?(zeroE, oneE, expE, rmorph0, rmorph1) //=.
  rewrite -IHe1 -rmorphX; congr (f _); lia.
- by move=> F' e1 IHe1 f; rewrite fmorphV IHe1 invE.
- by move=> R R' g e1 IHe1 f; rewrite -IHe1.
- by move=> V R g e1 IHe1 f; rewrite -IHe1.
- by move=> e f; rewrite -[Posz _]intz rmorph_int [LHS]Nnorm_correct.
- move=> e f; rewrite -[Negz _]intz rmorph_int /intmul mulrS Nnorm_correct.
  by rewrite oppE addE oneE.
- by move=> x f; rewrite F_of_ZE -(rmorph_int f); congr (f _); lia.
- by move=> V f; rewrite raddf0 zeroE.
- by move=> V e1 IHe1 f; rewrite raddfN IHe1 oppE.
- by move=> V e1 IHe1 e2 IHe2 f; rewrite raddfD IHe1 IHe2 addE.
- by move=> V e1 IHe1 e2 f; rewrite raddfMn IHe1 -mulr_natr Nnorm_correct mulE.
- by move=> V e1 IHe1 e2 IHe2 f; rewrite raddfMz IHe1 -mulrzr IHe2 mulE.
- by move=> V V' g e1 IHe1 f; rewrite -IHe1.
Qed.

Lemma Fnorm_correct (e : RExpr F) : Reval e = Fnorm [rmorphism of idfun] e.
Proof. exact: Fnorm_correct_rec [rmorphism of idfun] _. Qed.

End Fnorm.

(* Normalizing ring and field expressions to the Horner form by reflection    *)

Lemma RE R : @ring_eq_ext R +%R *%R -%R eq.
Proof. by split; do! move=> ? _ <-. Qed.

Lemma RZ R : ring_morph 0 1 +%R *%R (fun x y : R => x - y) -%R eq
                        0 1 Z.add Z.mul Z.sub Z.opp Z.eqb
                        (fun n => (int_of_Z n)%:~R).
Proof.
split=> //= [x y | x y | x y | x | x y /Z.eqb_eq -> //].
- by rewrite !rmorphD.
- by rewrite !rmorphB.
- by rewrite !rmorphM.
- by rewrite !rmorphN.
Qed.

Lemma PN R : @power_theory R 1 *%R eq N id (fun x n => x ^+ nat_of_N n).
Proof.
split => r [] //=; elim=> //= p <-.
- by rewrite Pos2Nat.inj_xI ?exprS -exprD addnn -mul2n.
- by rewrite Pos2Nat.inj_xO ?exprS -exprD addnn -mul2n.
Qed.

Lemma RR (R : comRingType) :
  @ring_theory R 0 1 +%R *%R (fun x y => x - y) -%R eq.
Proof.
exact/mk_rt/subrr/(fun _ _ => erefl)/mulrDl/mulrA/mulrC/mul1r/addrA/addrC/add0r.
Qed.

Lemma RF F : @field_theory F 0 1 +%R *%R (fun x y => x - y) -%R
                           (fun x y => x / y) GRing.inv eq.
Proof.
by split=> // [||x /eqP]; [exact: RR | exact/eqP/oner_neq0 | exact: mulVf].
Qed.

Fixpoint interp_PElist
    R R_of_Z zero opp add sub one mul exp
    (l : seq R) (lpe : list (RExpr R * RExpr R * PExpr Z * PExpr Z)) : seq R :=
  if lpe is (_, _, lhs, rhs) :: lpe then
    PEeval zero one add mul sub opp R_of_Z id exp l lhs ::
    PEeval zero one add mul sub opp R_of_Z id exp l rhs ::
    interp_PElist R_of_Z zero opp add sub one mul exp l lpe
  else
    [::].

Definition Rcorrect (R : comRingType) :=
  ring_correct
    (Eqsth R) (RE R) (Rth_ARth (Eqsth R) (RE R) (RR R)) (RZ R) (PN R)
    (triv_div_th (Eqsth R) (RE R) (Rth_ARth (Eqsth R) (RE R) (RR R)) (RZ R)).

Lemma ring_correct (R : comRingType) (n : nat) (l : seq R)
                   (lpe : seq (RExpr R * RExpr R * PExpr Z * PExpr Z))
                   (re1 re2 : RExpr R) (pe1 pe2 : PExpr Z) :
  interp_RElist lpe ->
  (forall R_of_Z zero opp add sub one mul exp,
      Rnorm R_of_Z zero opp add sub one mul exp [rmorphism of idfun] re1 ::
      Rnorm R_of_Z zero opp add sub one mul exp [rmorphism of idfun] re2 ::
      norm_RElist R_of_Z zero opp add sub one mul exp lpe =
      PEeval zero one add mul sub opp R_of_Z id exp l pe1 ::
      PEeval zero one add mul sub opp R_of_Z id exp l pe2 ::
     interp_PElist R_of_Z zero opp add sub one mul exp l lpe) ->
  (let norm_subst' :=
     norm_subst 0 1 Z.add Z.mul Z.sub Z.opp Z.eqb (triv_div 0 1 Z.eqb) n
                (mk_monpol_list
                   0 1 Z.add Z.mul Z.sub Z.opp Z.eqb (triv_div 0 1 Z.eqb)
                   (map (fun '(_, _, lhs, rhs) => (lhs, rhs)) lpe))
   in
   Peq Z.eqb (norm_subst' pe1) (norm_subst' pe2)) ->
  Reval re1 = Reval re2.
Proof.
move=> Hlpe' /(_ (fun n => (int_of_Z n)%:~R) 0%R -%R +%R (fun x y => x - y)).
move=> /(_ 1%R *%R (fun x n => x ^+ nat_of_N n)) /=.
rewrite -!Rnorm_correct // => -[-> -> Hlpe]; apply: Rcorrect.
elim: lpe Hlpe Hlpe' => [|[[[{}re1 {}re2] {}pe1] {}pe2] lpe IHlpe] //=.
rewrite /= -!Rnorm_correct //.
by move=> [-> ->] Hlpe [Hpe /(IHlpe Hlpe)] {IHlpe Hlpe} /=; case: lpe.
Qed.

(* Post-processing non-zero conditions of the field tactic                    *)
Section PCond.

Variables (P : Type) (ptrue : P) (pneg : P -> P) (pand : P -> P -> P).
Variables (R : Type) (rO rI : R) (radd rmul rsub : R -> R -> R) (ropp : R -> R).
Variables (req : R -> R -> P).
Variables (C : Type) (phi : C -> R).
Variables (Cpow : Type) (Cp_phi : N -> Cpow) (rpow : R -> Cpow -> R).

Notation eval := (PEeval rO rI radd rmul rsub ropp phi Cp_phi rpow).

Fixpoint PCond' (l : seq R) (le : seq (PExpr C)) : P :=
  match le with
  | [::] => ptrue
  | [:: e1] => pneg (req (eval l e1) rO)
  | e1 :: l1 => pand (pneg (req (eval l e1) rO)) (PCond' l l1)
  end.

End PCond.

Section PCond_facts.

Lemma PCondE : PCond = PCond' True not and. Proof. by []. Qed.

Variable (F : fieldType).
Let F_of_pos p : F := if p is xH then 1 else (Pos.to_nat p)%:R.
Let F_of_Z n : F :=
  match n with Z0 => 0 | Zpos p => F_of_pos p | Zneg p => - F_of_pos p end.

(* The following two lemmas should be immediate consequences of parametricity *)
Lemma PEvalE l e :
  PEeval 0 1 +%R *%R (fun x y => x - y) -%R F_of_Z N.to_nat (@GRing.exp F) l e =
  PEeval 0 1 +%R *%R (fun x y => x - y) -%R (fun n => (int_of_Z n)%:~R)
         N.to_nat (@GRing.exp F) l e.
Proof.
elim: e => //= [| ? -> ? -> | ? -> ? -> | ? -> ? -> | ? -> | ? ->] //.
by case=> [|[p|p|]|[p|p|]]; rewrite //= nmulrn; congr intmul; lia.
Qed.

Lemma PCondP l le :
  reflect
    (PCond' True not and 0 1 +%R *%R (fun x y : F => x - y) -%R eq
            (fun n0 : Z => (int_of_Z n0)%:~R) N.to_nat (@GRing.exp F) l le)
    (PCond' true negb andb 0 1 +%R *%R (fun x y : F => x - y) -%R eq_op
            F_of_Z N.to_nat (@GRing.exp F) l le).
Proof.
elim: le => [/=|e1 /= [|e2 le] IH].
- exact: ReflectT.
- by rewrite PEvalE; apply: (iffP negP); apply/contra_not => /eqP.
- by rewrite PEvalE; apply: (iffP andP) => -[/eqP ? /IH ?].
Qed.

End PCond_facts.

Definition Fcorrect F :=
  Field_correct
    (Eqsth F) (RE F) (congr1 GRing.inv)
    (F2AF (Eqsth F) (RE F) (RF F)) (RZ F) (PN F)
    (triv_div_th (Eqsth F) (RE F) (Rth_ARth (Eqsth F) (RE F) (RR F)) (RZ F)).

Lemma field_correct (F : fieldType) (n : nat) (l : seq F)
                    (lpe : seq (RExpr F * RExpr F * PExpr Z * PExpr Z))
                    (re1 re2 : RExpr F) (fe1 fe2 : FExpr Z) :
  interp_RElist lpe ->
  (forall R_of_Z zero opp add sub one mul exp div inv,
      Fnorm R_of_Z zero opp add sub one mul exp inv [rmorphism of idfun] re1 ::
      Fnorm R_of_Z zero opp add sub one mul exp inv [rmorphism of idfun] re2 ::
      norm_RElist R_of_Z zero opp add sub one mul exp lpe =
      FEeval zero one add mul sub opp div inv R_of_Z id exp l fe1 ::
      FEeval zero one add mul sub opp div inv R_of_Z id exp l fe2 ::
      interp_PElist R_of_Z zero opp add sub one mul exp l lpe) ->
  (forall is_true_ negb_ andb_ zero one add mul sub opp Feqb F_of_nat exp l',
      is_true_ = is_true -> negb_ = negb -> andb_ = andb ->
      zero = 0 -> one = 1 -> add = +%R -> mul = *%R ->
      sub = (fun x y => x - y) -> opp = -%R -> Feqb = eq_op ->
      F_of_nat = GRing.natmul 1 -> exp = @GRing.exp F -> l' = l ->
      let F_of_pos p := if p is xH then one else F_of_nat (Pos.to_nat p) in
      let F_of_Z n :=
        match n with
          Z0 => zero | Zpos p => F_of_pos p | Zneg p => opp (F_of_pos p)
        end
      in
      let norm_subst' :=
        norm_subst
          0 1 Z.add Z.mul Z.sub Z.opp Z.eqb (triv_div 0 1 Z.eqb) n
          (mk_monpol_list 0 1 Z.add Z.mul Z.sub Z.opp Z.eqb (triv_div 0 1 Z.eqb)
                          (map (fun '(_, _, lhs, rhs) => (lhs, rhs)) lpe))
      in
      let nfe1 := Field_theory.Fnorm 0 1 Z.add Z.mul Z.sub Z.opp Z.eqb fe1 in
      let nfe2 := Field_theory.Fnorm 0 1 Z.add Z.mul Z.sub Z.opp Z.eqb fe2 in
      Peq Z.eqb (norm_subst' (PEmul (num nfe1) (denum nfe2)))
                (norm_subst' (PEmul (num nfe2) (denum nfe1))) /\
      is_true_ (PCond' true negb_ andb_
                       zero one add mul sub opp Feqb F_of_Z N.to_nat exp l'
                       (Fapp (Fcons00 0 1 Z.add Z.mul Z.sub Z.opp Z.eqb
                                      (triv_div 0 1 Z.eqb))
                             (condition nfe1 ++ condition nfe2) [::]))) ->
  Reval re1 = Reval re2.
Proof.
move=> Hlpe' /(_ (fun n => (int_of_Z n)%:~R) 0%R -%R +%R (fun x y => x - y)).
move=> /(_ 1%R *%R (fun x n => x ^+ nat_of_N n) (fun x y => x / y) GRing.inv).
rewrite -!Fnorm_correct // => -[-> -> Hlpe].
move=> /(_ _ _ _ _ _ _ _ _ _ _ _ _ _ erefl erefl erefl erefl erefl erefl erefl).
move=> /(_ _ _ _ _ _ _ erefl erefl erefl erefl erefl erefl) [Heq Hcond].
apply: (Fcorrect _ erefl erefl erefl Heq).
  elim: {Heq Hcond}lpe Hlpe Hlpe' => //.
  move=> [[[{}re1 {}re2] {}pe1] {}pe2] lpe IHlpe; rewrite /= -!Rnorm_correct //.
  by move=> [-> ->] Hlpe [Hpe /(IHlpe Hlpe)] {IHlpe Hlpe} /=; case: lpe.
by apply: Pcond_simpl_gen;
  [ exact: RE | exact/F2AF/RF/RE | exact: RZ | exact: PN |
    exact/triv_div_th/RZ/Rth_ARth/RR/RE/RE/Eqsth | move=> _ ->; exact/PCondP ].
Qed.

Lemma numField_correct (F : numFieldType) (n : nat) (l : seq F)
                       (lpe : seq (RExpr F * RExpr F * PExpr Z * PExpr Z))
                       (re1 re2 : RExpr F) (fe1 fe2 : FExpr Z) :
  interp_RElist lpe ->
  (forall R_of_Z zero opp add sub one mul exp div inv,
      Fnorm R_of_Z zero opp add sub one mul exp inv [rmorphism of idfun] re1 ::
      Fnorm R_of_Z zero opp add sub one mul exp inv [rmorphism of idfun] re2 ::
      norm_RElist R_of_Z zero opp add sub one mul exp lpe =
      FEeval zero one add mul sub opp div inv R_of_Z id exp l fe1 ::
      FEeval zero one add mul sub opp div inv R_of_Z id exp l fe2 ::
      interp_PElist R_of_Z zero opp add sub one mul exp l lpe) ->
  (forall is_true_ negb_ andb_ zero one add mul sub opp Feqb F_of_nat exp l',
      is_true_ = is_true -> negb_ = negb -> andb_ = andb ->
      zero = 0 -> one = 1 -> add = +%R -> mul = *%R ->
      sub = (fun x y => x - y) -> opp = -%R -> Feqb = eq_op ->
      F_of_nat = GRing.natmul 1 -> exp = @GRing.exp F -> l' = l ->
      let F_of_pos p := if p is xH then one else F_of_nat (Pos.to_nat p) in
      let F_of_Z n :=
        match n with
          Z0 => zero | Zpos p => F_of_pos p | Zneg p => opp (F_of_pos p)
        end
      in
      let norm_subst' :=
        norm_subst
          0 1 Z.add Z.mul Z.sub Z.opp Z.eqb (triv_div 0 1 Z.eqb) n
          (mk_monpol_list 0 1 Z.add Z.mul Z.sub Z.opp Z.eqb (triv_div 0 1 Z.eqb)
                          (map (fun '(_, _, lhs, rhs) => (lhs, rhs)) lpe))
      in
      let nfe1 := Field_theory.Fnorm 0 1 Z.add Z.mul Z.sub Z.opp Z.eqb fe1 in
      let nfe2 := Field_theory.Fnorm 0 1 Z.add Z.mul Z.sub Z.opp Z.eqb fe2 in
      Peq Z.eqb (norm_subst' (PEmul (num nfe1) (denum nfe2)))
                (norm_subst' (PEmul (num nfe2) (denum nfe1))) /\
      is_true_ (PCond' true negb_ andb_
                       zero one add mul sub opp Feqb F_of_Z N.to_nat exp l'
                       (Fapp (Fcons2 0 1 Z.add Z.mul Z.sub Z.opp Z.eqb
                                     (triv_div 0 1 Z.eqb))
                             (condition nfe1 ++ condition nfe2) [::]))) ->
  Reval re1 = Reval re2.
Proof.
move=> Hlpe' /(_ (fun n => (int_of_Z n)%:~R) 0%R -%R +%R (fun x y => x - y)).
move=> /(_ 1%R *%R (fun x n => x ^+ nat_of_N n) (fun x y => x / y) GRing.inv).
rewrite -!Fnorm_correct // => -[-> -> Hlpe].
move=> /(_ _ _ _ _ _ _ _ _ _ _ _ _ _ erefl erefl erefl erefl erefl erefl erefl).
move=> /(_ _ _ _ _ _ _ erefl erefl erefl erefl erefl erefl) [Heq Hcond].
apply: (Fcorrect _ erefl erefl erefl Heq).
  elim: {Heq Hcond}lpe Hlpe Hlpe' => //.
  move=> [[[{}re1 {}re2] {}pe1] {}pe2] lpe IHlpe; rewrite /= -!Rnorm_correct //.
  by move=> [-> ->] Hlpe [Hpe /(IHlpe Hlpe)] {IHlpe Hlpe} /=; case: lpe.
apply: Pcond_simpl_complete;
  [ exact: RE | exact/F2AF/RF/RE | exact: RZ | exact: PN |
    exact/triv_div_th/RZ/Rth_ARth/RR/RE/RE/Eqsth | move=> x y /intr_inj; lia |
    move=> _ ->; exact/PCondP ].
Qed.

Ltac reflexivity_no_check :=
  match goal with
    | |- @eq ?T ?LHS ?RHS => exact_no_check (@Logic.eq_refl T LHS)
  end.

Ltac field_normalization :=
  let is_true_ := fresh "is_true_" in
  let negb_ := fresh "negb_" in
  let andb_ := fresh "andb_" in
  let zero := fresh "zero" in
  let one := fresh "one" in
  let add := fresh "add" in
  let mul := fresh "mul" in
  let sub := fresh "sub" in
  let opp := fresh "opp" in
  let Feqb := fresh "Feqb" in
  let F_of_nat := fresh "F_of_nat" in
  let exp := fresh "exp" in
  let l := fresh "l" in
  let is_trueE := fresh "is_trueE" in
  let negbE := fresh "negbE" in
  let andbE := fresh "andbE" in
  let zeroE := fresh "zeroE" in
  let oneE := fresh "oneE" in
  let addE := fresh "addE" in
  let mulE := fresh "mulE" in
  let subE := fresh "subE" in
  let oppE := fresh "oppE" in
  let FeqbE := fresh "FeqbE" in
  let F_of_natE := fresh "F_of_natE" in
  let expE := fresh "expE" in
  let lE := fresh "lE" in
  move=> is_true_ negb_ andb_ zero one add mul sub opp Feqb F_of_nat exp l;
  move=> is_trueE negbE andbE zeroE oneE addE mulE subE oppE FeqbE F_of_natE;
  move=> expE lE;
  vm_compute; refine (conj erefl _);
  rewrite ?{is_true_}is_trueE ?{negb_}negbE ?{andb_}andbE;
  rewrite ?{zero}zeroE ?{one}oneE ?{add}addE ?{mul}mulE ?{sub}subE ?{opp}oppE;
  rewrite ?{Feqb}FeqbE ?{F_of_nat}F_of_natE ?{exp}expE ?{l}lE.

End Internals.

(* Auxiliary Ltac code which will be invoked from Elpi *)

Ltac ring_reflection_check R VarMap Lpe RE1 RE2 PE1 PE2 LpeProofs :=
  refine (@ring_correct R 100%N VarMap Lpe RE1 RE2 PE1 PE2 LpeProofs
                        (fun _ _ _ _ _ _ _ _ => erefl) _);
  [ vm_compute; reflexivity ].

Ltac ring_reflection_no_check R VarMap Lpe RE1 RE2 PE1 PE2 LpeProofs :=
  exact_no_check (@ring_correct
    R 100%N VarMap Lpe RE1 RE2 PE1 PE2 LpeProofs
    (fun _ _ _ _ _ _ _ _ => ltac:(reflexivity_no_check))
    ltac:(vm_compute; reflexivity)).

Ltac ring_reflection := ring_reflection_check.

Ltac field_reflection_check F VarMap Lpe RE1 RE2 PE1 PE2 LpeProofs :=
  let refl_lemma :=
    match type of F with
      numFieldType => constr:(@numField_correct) | _ => constr:(@field_correct)
    end
  in
  refine (refl_lemma F 100%N VarMap Lpe RE1 RE2 PE1 PE2 LpeProofs
                     (fun _ _ _ _ _ _ _ _ _ _ => erefl) _);
  field_normalization.

Ltac field_reflection_no_check F VarMap Lpe RE1 RE2 PE1 PE2 LpeProofs :=
  let refl_lemma :=
    match type of F with
      numFieldType => constr:(@numField_correct) | _ => constr:(@field_correct)
    end
  in
  let obligation := fresh in
  eassert (obligation : _);
  [ | exact_no_check (refl_lemma
        F 100%N VarMap Lpe RE1 RE2 PE1 PE2 LpeProofs
        (fun _ _ _ _ _ _ _ _ _ _ => ltac:(reflexivity_no_check))
        ltac:(field_normalization; exact obligation)) ].

Ltac field_reflection := field_reflection_check.

Strategy expand
         [addn_expand nat_of_pos_rec_expand nat_of_pos_expand nat_of_N_expand
          int_of_Z_expand Neval Reval Nnorm Rnorm Fnorm PEeval FEeval].

Register Coq.Init.Logic.eq       as ring.eq.
Register Coq.Init.Logic.eq_refl  as ring.erefl.
Register Coq.Init.Logic.eq_sym   as ring.esym.
Register Coq.Init.Logic.eq_trans as ring.etrans.

Elpi Tactic ring.
Elpi Accumulate File "theories/common.elpi".
Elpi Accumulate File "theories/ring.elpi".
Elpi Typecheck.

Tactic Notation "ring" := elpi ring.
Tactic Notation "ring" ":" ne_constr_list(L) := elpi ring ltac_term_list:(L).

Elpi Tactic field.
Elpi Accumulate File "theories/common.elpi".
Elpi Accumulate File "theories/field.elpi".
Elpi Typecheck.

Tactic Notation "field" := elpi field.
Tactic Notation "field" ":" ne_constr_list(L) := elpi field ltac_term_list:(L).

Elpi Query lp:{{
  coq.option.add ["Algebra", "Tactics", "Debug"] (coq.option.bool ff) ff
}}.
