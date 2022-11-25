From elpi Require Import elpi.
From Coq Require Import QArith Ring.
From Coq.micromega Require Import RingMicromega QMicromega EnvRing Tauto Lqa.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat choice seq.
From mathcomp Require Import fintype finfun bigop order ssralg ssrnum ssrint.
From mathcomp.zify Require Import ssrZ zify.
From mathcomp.algebra_tactics Require Import common.
From mathcomp.algebra_tactics Extra Dependency "common.elpi" as common.
From mathcomp.algebra_tactics Extra Dependency "lra.elpi" as lra.

Import Order.TTheory GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

Module Import Internals.

Implicit Types (k : kind) (R S : ringType) (F : fieldType).

Inductive RExpr : ringType -> Type :=
  | RX R : R -> RExpr R
  | R0 R : RExpr R
  | ROpp R : RExpr R -> RExpr R
  | RAdd R : RExpr R -> RExpr R -> RExpr R
  (* TODO: support nat expressions: *)
  | RMuln R : RExpr R -> large_nat -> RExpr R
  | RMulz R : RExpr R -> RExpr [ringType of int] -> RExpr R
  | R1 R : RExpr R
  | RMul R : RExpr R -> RExpr R -> RExpr R
  | RExpn R : RExpr R -> large_nat -> RExpr R
  | RInv F : RExpr F -> RExpr F
  | RMorph R R' : {rmorphism R -> R'} -> RExpr R -> RExpr R'
  | RintC : large_int -> RExpr [ringType of int]
  | RZC : Z -> RExpr [ringType of Z].

Fixpoint Reval_expr R (e : RExpr R) : R :=
  match e with
  | RX _ x => x
  | R0 _ => 0%R
  | ROpp _ e => - Reval_expr e
  | RAdd _ e1 e2 => Reval_expr e1 + Reval_expr e2
  | RMuln _ e n => Reval_expr e *+ nat_of_large_nat n
  | RMulz _ e1 e2 => Reval_expr e1 *~ Reval_expr e2
  | R1 _ => 1%R
  | RMul _ e1 e2 => Reval_expr e1 * Reval_expr e2
  | RExpn _ e n => Reval_expr e ^+ nat_of_large_nat n
  | RInv _  e => (Reval_expr e)^-1
  | RMorph _ _ f e => f (Reval_expr e)
  | RintC x => int_of_large_int x
  | RZC x => x
  end.

(* Define [Reval_formula] the semantics of [BFormula (Formula Z) Tauto.isProp]
   as arithmetic expressions on some [realDomainType].
   Then prove [RTautoChecker_sound] stating that [ZTautoChecker f w = true]
   implies that the formula [Reval_formula f] holds. *)
Record RFormula R := { Rlhs : RExpr R;  Rop : Op2;  Rrhs : RExpr R }.

Section Rnorm_expr.

Variables (R' : ringType).
Variables (R_of_Z : Z -> R') (R_of_ZE : R_of_Z = (fun n => (int_of_Z n)%:~R)).
Variables (opp : R' -> R') (oppE : opp = -%R).
Variables (add : R' -> R' -> R') (addE : add = +%R).
Variables (mul : R' -> R' -> R') (mulE : mul = *%R).
Variables (exp : R' -> N -> R') (expE : exp = (fun x n => x ^+ nat_of_N n)).

Fixpoint Rnorm_expr R (f : {rmorphism R -> R'}) (e : RExpr R) : R' :=
  match e in RExpr R return {rmorphism R -> R'} -> R' with
  | RX _ x => fun f => f x
  | R0 _ => fun=> R_of_Z 0
  | ROpp _ e => fun f => opp (Rnorm_expr f e)
  | RAdd _ e1 e2 => fun f => add (Rnorm_expr f e1) (Rnorm_expr f e2)
  | RMuln _ e n => fun f => mul (Rnorm_expr f e) (R_of_Z (Z_of_large_nat n))
  | RMulz _ e1 e2 =>
      fun f => mul (Rnorm_expr f e1) (Rnorm_expr [rmorphism of intmul 1] e2)
  | R1 _ => fun=> R_of_Z 1
  | RMul _ e1 e2 => fun f => mul (Rnorm_expr f e1) (Rnorm_expr f e2)
  | RExpn _ e1 n => fun f => exp (Rnorm_expr f e1) (N_of_large_nat n)
  | RInv _ _ => fun=> f (Reval_expr e)
  | RMorph _ _ g e => fun f => Rnorm_expr [rmorphism of f \o g] e
  | RintC x => fun=> R_of_Z (Z_of_large_int x)
  | RZC x => fun=> R_of_Z x
  end f.

Lemma Rnorm_expr_correct_rec R (f : {rmorphism R -> R'}) (e : RExpr R) :
  f (Reval_expr e) = Rnorm_expr f e.
Proof.
move: f; elim: e => {R} //=.
- by move=> R f; rewrite R_of_ZE rmorph0.
- by move=> R e IHe f; rewrite oppE rmorphN IHe.
- by move=> R e1 IHe1 e2 IHe2 f; rewrite addE rmorphD IHe1 IHe2.
- move=> R e IHe n f.
  by rewrite mulE R_of_ZE rmorphMn -mulr_natr IHe large_nat_Z_int.
- by move=> R e1 IHe1 e2 IHe2 f; rewrite mulE rmorphMz -mulrzr IHe1 IHe2.
- by move=> R f; rewrite R_of_ZE rmorph1.
- by move=> R e1 IHe1 e2 IHe2 f; rewrite mulE rmorphM IHe1 IHe2.
- by move=> R e IHe n f; rewrite expE rmorphX IHe large_nat_N_nat.
- by move=> R S g e IHe f; rewrite -IHe.
- by move=> x f; rewrite R_of_ZE -(rmorph_int f) intz large_int_Z_int.
- by move=> x f; rewrite R_of_ZE -(rmorph_int f); congr (f _); lia.
Qed.

Lemma Rnorm_expr_correct (e : RExpr R') :
  Reval_expr e = Rnorm_expr [rmorphism of idfun] e.
Proof. exact: Rnorm_expr_correct_rec [rmorphism of idfun] _. Qed.

End Rnorm_expr.

Section Rnorm_formula.

Variables (R : numDomainType).
Variables (R_of_Z : Z -> R) (R_of_ZE : R_of_Z = (fun n => (int_of_Z n)%:~R)).
Variables (opp : R -> R) (oppE : opp = -%R).
Variables (add : R -> R -> R) (addE : add = +%R).
Variables (sub : R -> R -> R) (subE : sub = (fun x y => x - y)).
Variables (mul : R -> R -> R) (mulE : mul = *%R).
Variables (exp : R -> N -> R) (expE : exp = (fun x n => x ^+ nat_of_N n)).
Variables (eqProp : R -> R -> Prop) (eqPropE : eqProp = eq).
Variables (eqBool : R -> R -> bool) (eqBoolE : eqBool = eq_op).
Variables (le : R -> R -> bool) (leE : le = <=%O).
Variables (lt : R -> R -> bool) (ltE : lt = <%O).

Notation Rnorm_expr := (Rnorm_expr R_of_Z opp add mul exp).

Definition Reval_pop2 (o : Op2) : R -> R -> Prop :=
  match o with
  | OpEq => eqProp
  | OpNEq => fun x y => ~ eqProp x y
  | OpLe => le
  | OpGe => fun x y => le y x
  | OpLt => lt
  | OpGt => fun x y => lt y x
  end.

Definition Reval_bop2 (o : Op2) : R -> R -> bool :=
  match o with
  | OpEq  => eqBool
  | OpNEq => fun x y => ~~ eqBool x y
  | OpLe  => le
  | OpGe  => fun x y => le y x
  | OpLt  => lt
  | OpGt  => fun x y => lt y x
  end.

Definition Reval_op2 k : Op2 -> R -> R -> rtyp k :=
  match k with isProp => Reval_pop2 | isBool => Reval_bop2 end.

Definition Reval_formula k (ff : RFormula R) : rtyp k :=
  let (lhs,o,rhs) := ff in Reval_op2 k o (Reval_expr lhs) (Reval_expr rhs).

Definition Rnorm_formula k (ff : RFormula R) :=
  let norm := Rnorm_expr [rmorphism of idfun] in
  let (lhs,o,rhs) := ff in Reval_op2 k o (norm lhs) (norm rhs).

Lemma Rnorm_formula_correct k (ff : RFormula R) :
  Reval_formula k ff = Rnorm_formula k ff.
Proof. by case: ff => l o r /=; rewrite -!Rnorm_expr_correct. Qed.

Lemma Rnorm_bf_correct k (ff : BFormula (RFormula R) k) :
  eval_bf Reval_formula ff = eval_bf Rnorm_formula ff.
Proof.
elim: ff => // {k}.
- by move=> k ff ?; exact: Rnorm_formula_correct.
- by move=> k ff1 IH1 ff2 IH2; congr eAND.
- by move=> k ff1 IH1 ff2 IH2; congr eOR.
- by move=> k ff IH; congr eNOT.
- by move=> k ff1 IH1 o ff2 IH2; congr eIMPL.
- by move=> k ff1 IH1 ff2 IH2; congr eIFF.
- by move=> ff1 IH1 ff2 IH2; congr eq.
Qed.

Definition Reval_PFormula (e : PolEnv R) k (ff : Formula Z) : rtyp k :=
  let eval := PEeval add mul sub opp R_of_Z id exp e in
  let (lhs,o,rhs) := ff in Reval_op2 k o (eval lhs) (eval rhs).

Lemma pop2_bop2 (op : Op2) (q1 q2 : R) :
  Reval_bop2 op q1 q2 <-> Reval_pop2 op q1 q2.
Proof. by case: op => //=; rewrite eqPropE eqBoolE; split => /eqP. Qed.

Lemma Reval_formula_compat (env : PolEnv R) k (f : Formula Z) :
  hold k (Reval_PFormula env k f) <->
  eval_formula add mul sub opp eqProp le lt R_of_Z id exp env f.
Proof. by case: f => lhs op rhs; case: k => //=; rewrite pop2_bop2. Qed.

End Rnorm_formula.

Section RealDomain.

Variable R : realDomainType.

Notation Rsor := (Rsor R).
Notation RSORaddon := (RSORaddon R).

Definition ZTautoChecker (f : BFormula (Formula Z) isProp) (w: list (Psatz Z)) :
    bool :=
  @tauto_checker
    (Formula Z) (NFormula Z) unit
    (check_inconsistent 0 Z.eqb Z.leb)
    (nformula_plus_nformula 0 Z.add Z.eqb)
    (@cnf_normalise Z 0 1 Z.add Z.mul Z.sub Z.opp Z.eqb Z.leb unit)
    (@cnf_negate Z 0 1 Z.add Z.mul Z.sub Z.opp Z.eqb Z.leb unit)
    (Psatz Z)
    (fun cl => check_normalised_formulas
                 0 1 Z.add Z.mul Z.eqb Z.leb (List.map fst cl)) f w.

Definition Reval_nformula : PolEnv R -> NFormula Z -> Prop :=
  eval_nformula 0 +%R *%R eq <=%O <%O (fun n => (int_of_Z n)%:~R).

Lemma RTautoChecker_sound
    (ff : BFormula (RFormula R) isProp) (f : BFormula (Formula Z) isProp)
    (w : seq (Psatz Z)) (env : PolEnv R) :
  (forall R_of_Z opp add sub mul exp eqProp eqBool le lt,
      let norm_ff := Rnorm_formula R_of_Z opp add mul exp eqProp eqBool le lt in
      let eval_f :=
        Reval_PFormula R_of_Z opp add sub mul exp eqProp eqBool le lt env in
      eval_bf norm_ff ff = eval_bf eval_f f) ->
  ZTautoChecker f w = true -> eval_bf (Reval_formula eq eq_op <=%O <%O) ff.
Proof.
rewrite (Rnorm_bf_correct erefl erefl erefl erefl erefl).
move=> /(_ _ _ _ (fun x y => x - y)) -> Hchecker.
move: Hchecker env; apply: (tauto_checker_sound _ _ _ _ Reval_nformula).
- exact: (eval_nformula_dec Rsor).
- by move=> [? ?] ? ?; apply: (check_inconsistent_sound Rsor RSORaddon).
- move=> t t' u deducett'u env evalt evalt'.
  exact: (nformula_plus_nformula_correct Rsor RSORaddon env t t').
- move=> env k t tg cnfff; rewrite Reval_formula_compat //.
  exact: (cnf_normalise_correct Rsor RSORaddon env t tg).1.
- move=> env k t tg cnfff; rewrite hold_eNOT Reval_formula_compat //.
  exact: (cnf_negate_correct Rsor RSORaddon env t tg).1.
- move=> t w0 checkw0 env; rewrite (Refl.make_impl_map (Reval_nformula env)) //.
  exact: (checker_nf_sound Rsor RSORaddon) checkw0 env.
Qed.

End RealDomain.

Section Fnorm_expr.

Variables (F : fieldType).
Variables (F_of_Q : Q -> F) (F_of_QE : F_of_Q = R_of_Q).
Variables (opp : F -> F) (oppE : opp = -%R).
Variables (add : F -> F -> F) (addE : add = +%R).
Variables (mul : F -> F -> F) (mulE : mul = *%R).
Variables (exp : F -> N -> F) (expE : exp = (fun x n => x ^+ nat_of_N n)).
Variables (inv : F -> F) (invE : inv = GRing.inv).

Fixpoint Fnorm_expr R (f : {rmorphism R -> F}) (e : RExpr R) (invb : bool) :
    F :=
  match e in RExpr R, invb return {rmorphism R -> F} -> F with
  | RX _ x, false => fun f => f x
  | RX _ x, true => fun f => inv (f x)
  | R0 _, _ => fun=> F_of_Q 0
  | ROpp _ e, _ => fun f => opp (Fnorm_expr f e invb)
  | RAdd _ e1 e2, false =>
      fun f => add (Fnorm_expr f e1 false) (Fnorm_expr f e2 false)
  | RMuln _ e n, _ => fun f =>
      mul (Fnorm_expr f e invb)
        (if invb then
           F_of_Q (Qinv (Z_of_large_nat n # 1))
         else F_of_Q (Z_of_large_nat n # 1))
  | RMulz _ e1 e2, _ => fun f =>
      mul (Fnorm_expr f e1 invb) (Fnorm_expr [rmorphism of intmul 1] e2 invb)
  | R1 _, _ => fun=> F_of_Q 1
  | RMul _ e1 e2, _ =>
      fun f => mul (Fnorm_expr f e1 invb) (Fnorm_expr f e2 invb)
  | RExpn _ e1 n, _ => fun f => exp (Fnorm_expr f e1 invb) (N_of_large_nat n)
  | RInv _ e, _ => fun f => Fnorm_expr f e (negb invb)
  | RMorph _ _ g e, _ => fun f => Fnorm_expr [rmorphism of f \o g] e invb
  | RintC x, false => fun=> F_of_Q (Z_of_large_int x # 1)
  | RintC x, true => fun=> F_of_Q (Qinv (Z_of_large_int x # 1))
  | RZC x, false => fun=> F_of_Q (x # 1)
  | RZC x, true => fun=> F_of_Q (Qinv (x # 1))
  | _, true => fun=> inv (f (Reval_expr e))
  end f.

Lemma Fnorm_expr_correct_rec R (f : {rmorphism R -> F}) (e : RExpr R) :
  (f (Reval_expr e) = Fnorm_expr f e false) /\
    ((f (Reval_expr e))^-1 = Fnorm_expr f e true).
Proof.
move: f; elim: e => {R} //=.
- by move=> R x f; rewrite invE.
- by move=> R f; rewrite F_of_QE rmorph0 invr0 /R_of_Q divr1.
- move=> R e IHe f; case: (IHe f) => {}IHe IHe'.
  by rewrite oppE rmorphN invrN IHe' IHe.
- move=> R e1 IHe1 e2 IHe2 f; move: (IHe1 f) (IHe2 f) => [{}IHe1 _] [{}IHe2 _].
  by rewrite addE invE rmorphD IHe1 IHe2.
- move=> R e IHe n f; move: (IHe f) => [{}IHe IHe'].
  rewrite mulE F_of_QE rmorphMn -mulr_natr invfM IHe' IHe R_of_Q_invZ.
  by rewrite /R_of_Q divr1 large_nat_Z_int.
- move=> R e1 IHe1 e2 IHe2 f.
  move: (IHe1 f) (IHe2 [rmorphism of intr]) => [{}IHe1 IHe1'] [{}IHe2 IHe2'].
  by rewrite mulE rmorphMz -mulrzr invfM IHe1' IHe1 IHe2' IHe2.
- by move=> R f; rewrite F_of_QE rmorph1 invr1 /R_of_Q divr1.
- move=> R e1 IHe1 e2 IHe2 f.
  move: (IHe1 f) (IHe2 f) => [{}IHe1 IHe1'] [{}IHe2 IHe2'].
  by rewrite mulE rmorphM invfM IHe1' IHe1 IHe2' IHe2.
- move=> R e IHe n f; case: (IHe f) => {}IHe IHe'.
  by rewrite expE rmorphX -exprVn IHe' IHe large_nat_N_nat.
- move=> R e IHe f; case: (IHe f) => {}IHe IHe'.
  by rewrite fmorphV invrK IHe' IHe.
- by move=> R S g e IHe f; case: (IHe [rmorphism of f \o g]); split.
- move=> x f; rewrite F_of_QE R_of_Q_invZ /R_of_Q divr1 /= -(rmorph_int f).
  by rewrite intz large_int_Z_int.
- move=> x f; rewrite F_of_QE R_of_Q_invZ /R_of_Q divr1 /= -(rmorph_int f).
  by split; [congr (f _) | congr (f _)^-1]; lia.
Qed.

Lemma Fnorm_expr_correct (e : RExpr F) :
  Reval_expr e = Fnorm_expr [rmorphism of idfun] e false.
Proof. by have [] := Fnorm_expr_correct_rec [rmorphism of idfun] e. Qed.

End Fnorm_expr.

Section Fnorm_formula.

Variables (F : numFieldType).
Variables (F_of_Q : Q -> F) (F_of_QE : F_of_Q = R_of_Q).
Variables (opp : F -> F) (oppE : opp = -%R).
Variables (add : F -> F -> F) (addE : add = +%R).
Variables (sub : F -> F -> F) (subE : sub = (fun x y => x - y)).
Variables (mul : F -> F -> F) (mulE : mul = *%R).
Variables (exp : F -> N -> F) (expE : exp = (fun x n => x ^+ nat_of_N n)).
Variables (eqProp : F -> F -> Prop) (eqPropE : eqProp = eq).
Variables (eqBool : F -> F -> bool) (eqBoolE : eqBool = eq_op).
Variables (le : F -> F -> bool) (leE : le = <=%O).
Variables (lt : F -> F -> bool) (ltE : lt = <%O).

Notation Fnorm_expr := (Fnorm_expr F_of_Q opp add mul exp GRing.inv).
Notation Feval_pop2 := (Reval_pop2 eqProp le lt).
Notation Feval_bop2 := (Reval_bop2 eqBool le lt).
Notation Feval_op2 := (Reval_op2 eqProp eqBool le lt).
Notation Feval_formula := (Reval_formula eqProp eqBool le lt).

Definition Fnorm_formula k (ff : RFormula F) :=
  let norm := Fnorm_expr [rmorphism of idfun] in
  let (lhs,o,rhs) := ff in Feval_op2 k o (norm lhs false) (norm rhs false).

Lemma Fnorm_formula_correct k (ff : RFormula F) :
  Feval_formula k ff = Fnorm_formula k ff.
Proof. by case: ff => l o r /=; rewrite -!Fnorm_expr_correct. Qed.

Lemma Fnorm_bf_correct k (ff : BFormula (RFormula F) k) :
  eval_bf Feval_formula ff = eval_bf Fnorm_formula ff.
Proof.
elim: ff => // {k}.
- by move=> k ff ?; exact: Fnorm_formula_correct.
- by move=> k ff1 IH1 ff2 IH2; congr eAND.
- by move=> k ff1 IH1 ff2 IH2; congr eOR.
- by move=> k ff IH; congr eNOT.
- by move=> k ff1 IH1 o ff2 IH2; congr eIMPL.
- by move=> k ff1 IH1 ff2 IH2; congr eIFF.
- by move=> ff1 IH1 ff2 IH2; congr eq.
Qed.

Definition Feval_PFormula (e : PolEnv F) k (ff : Formula Q) : rtyp k :=
  let eval := eval_pexpr add mul sub opp F_of_Q id exp e in
  let (lhs,o,rhs) := ff in Feval_op2 k o (eval lhs) (eval rhs).

Lemma pop2_bop2' (op : Op2) (q1 q2 : F) :
  Feval_bop2 op q1 q2 <-> Feval_pop2 op q1 q2.
Proof. by case: op => //=; rewrite eqPropE eqBoolE; split => /eqP. Qed.

Lemma Feval_formula_compat env b f :
  hold b (Feval_PFormula env b f) <->
  eval_formula add mul sub opp eqProp le lt F_of_Q id exp env f.
Proof. by case: f => lhs op rhs; case: b => //=; rewrite pop2_bop2'. Qed.

End Fnorm_formula.

(* Define [Feval_formula] the semantics of [BFormula (Formula Q) Tauto.isProp]
   as arithmetic expressions on some [realFieldType].
   Then prove [FTautoChecker_sound] stating that [QTautoChecker f w = true]
   implies that the formula [Feval_formula f] holds. *)
Section RealField.

Variable F : realFieldType.

Notation Rsor := (Rsor F).
Notation FSORaddon := (FSORaddon F).

Definition Feval_nformula : PolEnv F -> NFormula Q -> Prop :=
  eval_nformula 0 +%R *%R eq (fun x y => x <= y) (fun x y => x < y) R_of_Q.

Lemma FTautoChecker_sound
    (ff : BFormula (RFormula F) isProp) (f : BFormula (Formula Q) isProp)
    (w : seq (Psatz Q)) (env : PolEnv F) :
  (forall F_of_Q opp add sub mul exp eqProp eqBool le lt,
      let norm_ff := Fnorm_formula F_of_Q opp add mul exp eqProp eqBool le lt in
      let eval_f :=
        Feval_PFormula F_of_Q opp add sub mul exp eqProp eqBool le lt env in
      eval_bf norm_ff ff = eval_bf eval_f f) ->
  QTautoChecker f w = true -> eval_bf (Reval_formula eq eq_op <=%O <%O) ff.
Proof.
rewrite (Fnorm_bf_correct erefl erefl erefl erefl erefl).
move=> /(_ _ _ _ (fun x y => x - y)) -> Hchecker.
move: Hchecker env; apply: (tauto_checker_sound _ _ _ _ Feval_nformula).
- exact: (eval_nformula_dec Rsor).
- by move=> [? ?] ? ?; apply: (check_inconsistent_sound Rsor FSORaddon).
- move=> t t' u deducett'u env evalt evalt'.
  exact: (nformula_plus_nformula_correct Rsor FSORaddon env t t').
- move=> env k t tg cnfff; rewrite Feval_formula_compat //.
  exact: (cnf_normalise_correct Rsor FSORaddon env t tg).1.
- move=> env k t tg cnfff; rewrite hold_eNOT Feval_formula_compat //.
  exact: (cnf_negate_correct Rsor FSORaddon env t tg).1.
- move=> t w0 checkw0 env; rewrite (Refl.make_impl_map (Feval_nformula env)) //.
  exact: (checker_nf_sound Rsor FSORaddon) checkw0 env.
Qed.

End RealField.

(* Auxiliary function called from lra.elpi *)
Definition vm_of_list T (l : list T) : VarMap.t T :=
  let fix aux acc p l :=
    match l with
    | [::] => acc
    | x :: l => aux (VarMap.vm_add x p x acc) (Pos.succ p) l
    end in
  aux VarMap.Empty 1%positive l.

(* Translating formulas and witnesses from Q to Z for the realDomainType case *)

Definition omap2 {aT1 aT2 rT} (f : aT1 -> aT2 -> rT) o1 o2 :=
  obind (fun a1 => omap (f a1) o2) o1.

Fixpoint PExpr_Q2Z (e : PExpr Q) : option (PExpr Z) := match e with
  | PEc (Qmake z 1) => Some (PEc z) | PEc _ => None
  | PEX n => Some (PEX n)
  | PEadd e1 e2 => omap2 PEadd (PExpr_Q2Z e1) (PExpr_Q2Z e2)
  | PEsub e1 e2 => omap2 PEsub (PExpr_Q2Z e1) (PExpr_Q2Z e2)
  | PEmul e1 e2 => omap2 PEmul (PExpr_Q2Z e1) (PExpr_Q2Z e2)
  | PEopp e1 => omap PEopp (PExpr_Q2Z e1)
  | PEpow e1 n => omap (PEpow ^~ n) (PExpr_Q2Z e1) end.

Definition Formula_Q2Z (ff : Formula Q) : option (Formula Z) :=
  omap2
    (fun l r => Build_Formula l (Fop ff) r)
    (PExpr_Q2Z (Flhs ff)) (PExpr_Q2Z (Frhs ff)).

Fixpoint BFormula_Q2Z [k] (ff : BFormula (Formula Q) k) :
    option (BFormula (Formula Z) k) := match ff with
  | TT k => Some (TT k)
  | FF k => Some (FF k)
  | X k P => Some (X k P)
  | A k a aa => omap (A k ^~ aa) (Formula_Q2Z a)
  | AND _ f1 f2 => omap2 (fun f => AND f) (BFormula_Q2Z f1) (BFormula_Q2Z f2)
  | OR _ f1 f2 => omap2 (fun f => OR f) (BFormula_Q2Z f1) (BFormula_Q2Z f2)
  | NOT _ f1 => omap (fun f => NOT f) (BFormula_Q2Z f1)
  | IMPL _ f1 o f2 =>
      omap2 (fun f => IMPL f o) (BFormula_Q2Z f1) (BFormula_Q2Z f2)
  | IFF _ f1 f2 => omap2 (fun f => IFF f) (BFormula_Q2Z f1) (BFormula_Q2Z f2)
  | EQ f1 f2 => omap2 EQ (BFormula_Q2Z f1) (BFormula_Q2Z f2) end.

Fixpoint Pol_Q2Z (p : Pol Q) : Pol Z * positive := match p with
  | Pc (Qmake n d) => (Pc n, d)
  | Pinj j p => let (p, n) := Pol_Q2Z p in (Pinj j p, n)
  | PX p1 i p2 =>
      let (p1, n1) := Pol_Q2Z p1 in
      let (p2, n2) := Pol_Q2Z p2 in
      let mulc c p := PmulC Z0 (Zpos 1) Z.mul Z.eqb p (Zpos c) in
      (PX (mulc n2 p1) i (mulc n1 p2), Pos.mul n1 n2)
  end.

Fixpoint Psatz_Q2Z (l : seq positive) (p : Psatz Q) : Psatz Z * positive :=
  match p with
  | PsatzC (Qmake n d) => (PsatzC n, d)
  | PsatzLet p1 p2 =>
      let (p1, n1) := Psatz_Q2Z l p1 in
      let (p2, n2) := Psatz_Q2Z (n1 :: l) p2 in
      (PsatzLet p1 p2, n2)
  | PsatzIn n => (PsatzIn _ n, nth 1%positive l n)
  | PsatzSquare p => let (p, n) := Pol_Q2Z p in (PsatzSquare p, Pos.mul n n)
  | PsatzMulC p1 p2 =>
      let (p1, n1) := Pol_Q2Z p1 in
      let (p2, n2) := Psatz_Q2Z l p2 in
      (PsatzMulC p1 p2, Pos.mul n1 n2)
  | PsatzMulE p1 p2 =>
      let (p1, n1) := Psatz_Q2Z l p1 in
      let (p2, n2) := Psatz_Q2Z l p2 in
      (PsatzMulE p1 p2, Pos.mul n1 n2)
  | PsatzAdd p1 p2 =>
      let (p1, n1) := Psatz_Q2Z l p1 in
      let (p2, n2) := Psatz_Q2Z l p2 in
      let mulc c p := PsatzMulE (PsatzC (Zpos c)) p in
      (PsatzAdd (mulc n2 p1) (mulc n1 p2), Pos.mul n1 n2)
  | PsatzZ => (PsatzZ _, 1%positive)
  end.

Definition seq_Psatz_Q2Z : seq (Psatz Q) -> seq (Psatz Z) :=
  map (fun p => fst (Psatz_Q2Z [::] p)).

End Internals.

Strategy expand [addn_expand nat_of_pos_rec_expand nat_of_pos_expand].
Strategy expand [nat_of_N_expand int_of_Z_expand Z_of_N_expand].
Strategy expand [nat_of_large_nat N_of_large_nat Z_of_large_nat].
Strategy expand [int_of_large_int Z_of_large_int].

Strategy expand [Reval_expr Rnorm_expr Fnorm_expr].
Strategy expand [Reval_pop2 Reval_bop2 Reval_op2].
Strategy expand [Reval_formula Rnorm_formula Fnorm_formula].
Strategy expand [Reval_PFormula Feval_PFormula].

(* Main tactics, called from the elpi parser (c.f., lra.elpi) *)

Ltac tacF tac efalso hyps_goal rff ff varmap :=
  match efalso with true => exfalso | _ => idtac end;
  (suff: hyps_goal by exact);
  let irff := fresh "__rff" in
  let iff := fresh "__ff" in
  let ivarmap := fresh "__varmap" in
  let iwit := fresh "__wit" in
  let iprf := fresh "__prf" in
  pose (irff := rff);
  pose (iff := ff);
  pose (ivarmap := varmap);
  tac iwit ff;
  pose (iprf := erefl true <: QTautoChecker iff iwit = true);
  exact: (@FTautoChecker_sound _ irff iff iwit
            (VarMap.find 0 (vm_of_list ivarmap))
            (fun _ _ _ _ _ _ _ _ _ _ => erefl) iprf).
Ltac lraF n := let wlra_Q w f := wlra_Q w f in tacF wlra_Q.
Ltac nraF n := let wnra_Q w f := wnra_Q w f in tacF wnra_Q.
Ltac psatzF n :=
  let sos_or_psatzn w f := wsos_Q w f || wpsatz_Q n w f in
  tacF sos_or_psatzn.

Ltac tacR tac efalso hyps_goal rff ff varmap :=
  match efalso with true => exfalso | _ => idtac end;
  (suff: hyps_goal by exact);
  let irff := fresh "__rff" in
  let iff := fresh "__ff" in
  let ivarmap := fresh "__varmap" in
  let iwit := fresh "__wit" in
  let iprf := fresh "__prf" in
  match eval vm_compute in (BFormula_Q2Z ff) with
  | Some ?f =>
      pose (irff := rff);
      pose (iff := f);
      pose (ivarmap := varmap);
      tac iwit ff;
      let tr := seq_Psatz_Q2Z in
      pose (iprf := erefl true <: ZTautoChecker iff (tr iwit) = true);
      exact: (@RTautoChecker_sound _ irff iff (tr iwit)
                (VarMap.find 0 (vm_of_list ivarmap))
                (fun _ _ _ _ _ _ _ _ _ _ => erefl) iprf)
  | _ => fail  (* should never happen, the parser only parses int constants *)
  end.
Ltac lraR n := let wlra_Q w f := wlra_Q w f in tacR wlra_Q.
Ltac nraR n := let wnra_Q w f := wnra_Q w f in tacR wnra_Q.
Ltac psatzR n :=
  let sos_or_psatzn w f := wsos_Q w f || wpsatz_Q n w f in
  tacF sos_or_psatzn.

Elpi Tactic lra.
Elpi Accumulate File common lra.
Elpi Typecheck.

Tactic Notation "lra" := elpi lra "lraF" "lraR" 0.
Tactic Notation "nra" := elpi lra "nraF" "nraR" 0.
Tactic Notation "psatz" integer(n) := elpi lra "psatzF" "psatzR" ltac_int:(n).
Tactic Notation "psatz" := elpi lra "psatzF" "psatzR" (-1).
