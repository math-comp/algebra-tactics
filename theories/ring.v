From Coq Require Import ZArith ZifyClasses Ring Ring_polynom Field_theory.
From elpi Require Export elpi.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat choice seq.
From mathcomp Require Import fintype finfun bigop order ssralg ssrnum ssrint.
From mathcomp Require Import zify ssrZ.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.

Local Open Scope ring_scope.

Module Import Internals.

Implicit Types (V : zmodType) (R : ringType) (F : fieldType).

Lemma RE R : @ring_eq_ext R +%R *%R -%R eq.
Proof. by split; do! move=> ? _ <-. Qed.

Lemma RZ R : ring_morph 0 1 +%R *%R (fun x y : R => x - y) -%R eq
                        0%Z 1%Z Z.add Z.mul Z.sub Z.opp Z.eqb
                        (fun n => (int_of_Z n)%:~R).
Proof.
split=> //= [x y | x y | x y | x | x y /Z.eqb_eq -> //].
- by rewrite !rmorphD.
- by rewrite !rmorphB.
- by rewrite !rmorphM.
- by rewrite !rmorphN.
Qed.

Lemma PN R : @power_theory R 1 *%R eq nat nat_of_N (@GRing.exp R).
Proof.
by split=> r [] //=; elim=> //= p <-;
  rewrite (Pos2Nat.inj_xI, Pos2Nat.inj_xO) ?exprS -exprD addnn -mul2n.
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

Definition Rcorrect (R : comRingType) :=
  ring_correct
    (Eqsth R) (RE R) (Rth_ARth (Eqsth R) (RE R) (RR R)) (RZ R) (PN R)
    (triv_div_th (Eqsth R) (RE R) (Rth_ARth (Eqsth R) (RE R) (RR R)) (RZ R)).

Definition Fcorrect F :=
  Field_correct
    (Eqsth F) (RE F) (congr1 GRing.inv)
    (F2AF (Eqsth F) (RE F) (RF F)) (RZ F) (PN F)
    (triv_div_th (Eqsth F) (RE F) (Rth_ARth (Eqsth F) (RE F) (RR F)) (RZ F)).

Inductive NatExpr : Type :=
  | NatX : nat -> NatExpr
  | NatAdd : NatExpr -> NatExpr -> NatExpr
  | NatSucc : NatExpr -> NatExpr
  | NatMul : NatExpr -> NatExpr -> NatExpr
  | NatExp : NatExpr -> nat -> NatExpr.

Fixpoint NatEval (ne : NatExpr) : nat :=
  match ne with
    | NatX x => x
    | NatAdd e1 e2 => NatEval e1 + NatEval e2
    | NatSucc e => S (NatEval e)
    | NatMul e1 e2 => NatEval e1 * NatEval e2
    | NatExp e1 n => NatEval e1 ^ n
  end.

Fixpoint NatEval' R (e : NatExpr) : R :=
  match e with
    | NatX x => x%:~R
    | NatAdd e1 e2 => NatEval' R e1 + NatEval' R e2
    | NatSucc e1 => 1 + NatEval' R e1
    | NatMul e1 e2 => NatEval' R e1 * NatEval' R e2
    | NatExp e1 n => NatEval' R e1 ^+ n
  end.

Lemma NatEval_correct R (e : NatExpr) : (NatEval e)%:R = NatEval' R e.
Proof.
elim: e => //=.
- by move=> e1 IHe1 e2 IHe2; rewrite natrD IHe1 IHe2.
- by move=> e IHe; rewrite mulrS IHe.
- by move=> e1 IHe1 e2 IHe2; rewrite natrM IHe1 IHe2.
- by move=> e1 IHe1 e2; rewrite natrX IHe1.
Qed.

Inductive RingExpr : ringType -> Type :=
  | RingX R : R -> RingExpr R
  | Ring0 R : RingExpr R
  | RingOpp R : RingExpr R -> RingExpr R
  | RingAdd R : RingExpr R -> RingExpr R -> RingExpr R
  | RingMuln R : RingExpr R -> NatExpr -> RingExpr R
  | RingMulz R : RingExpr R -> RingExpr [ringType of int] -> RingExpr R
  | Ring1 R : RingExpr R
  | RingMul R : RingExpr R -> RingExpr R -> RingExpr R
  | RingExpn R : RingExpr R -> nat -> RingExpr R
  | RingInv F : RingExpr F -> RingExpr F
  | RingMorph R' R : {rmorphism R' -> R} -> RingExpr R' -> RingExpr R
  | RingMorph' V R : {additive V -> R} -> ZmodExpr V -> RingExpr R
  | RingPosz : NatExpr -> RingExpr [ringType of int]
  | RingNegz : NatExpr -> RingExpr [ringType of int]
with ZmodExpr : zmodType -> Type :=
  | ZmodX V : V -> ZmodExpr V
  | Zmod0 V : ZmodExpr V
  | ZmodOpp V : ZmodExpr V -> ZmodExpr V
  | ZmodAdd V : ZmodExpr V -> ZmodExpr V -> ZmodExpr V
  | ZmodMuln V : ZmodExpr V -> NatExpr -> ZmodExpr V
  | ZmodMulz V : ZmodExpr V -> RingExpr [ringType of int] -> ZmodExpr V
  | ZmodMorph V' V : {additive V' -> V} -> ZmodExpr V' -> ZmodExpr V.

Scheme RingExpr_ind' := Induction for RingExpr Sort Prop
  with ZmodExpr_ind' := Induction for ZmodExpr Sort Prop.

Fixpoint RingEval R (e : RingExpr R) : R :=
  match e with
    | RingX _ x => x
    | Ring0 _ => 0%R
    | RingOpp _ e1 => - RingEval e1
    | RingAdd _ e1 e2 => RingEval e1 + RingEval e2
    | RingMuln _ e1 e2 => RingEval e1 *+ NatEval e2
    | RingMulz _ e1 e2 => RingEval e1 *~ RingEval e2
    | Ring1 _ => 1%R
    | RingMul _ e1 e2 => RingEval e1 * RingEval e2
    | RingExpn _ e1 n => RingEval e1 ^+ n
    | RingInv _ e1 => (RingEval e1) ^-1
    | RingMorph _ _ f e1 => f (RingEval e1)
    | RingMorph' _ _ f e1 => f (ZmodEval e1)
    | RingPosz e1 => Posz (NatEval e1)
    | RingNegz e2 => Negz (NatEval e2)
  end
with ZmodEval V (e : ZmodExpr V) : V :=
  match e with
    | ZmodX _ x => x
    | Zmod0 _ => 0%R
    | ZmodOpp _ e1 => - ZmodEval e1
    | ZmodAdd _ e1 e2 => ZmodEval e1 + ZmodEval e2
    | ZmodMuln _ e1 e2 => ZmodEval e1 *+ NatEval e2
    | ZmodMulz _ e1 e2 => ZmodEval e1 *~ RingEval e2
    | ZmodMorph _ _ f e1 => f (ZmodEval e1)
  end.

Fixpoint RingEval' R R' (f : {rmorphism R -> R'}) (e : RingExpr R) : R' :=
  match e in RingExpr R return {rmorphism R -> R'} -> R' with
    | RingX _ x => fun f => f x
    | Ring0 _ => fun => 0%R
    | RingOpp _ e1 => fun f => - RingEval' f e1
    | RingAdd _ e1 e2 => fun f => RingEval' f e1 + RingEval' f e2
    | RingMuln _ e1 e2 => fun f => RingEval' f e1 * NatEval' R' e2
    | RingMulz _ e1 e2 => fun f =>
      RingEval' f e1 * RingEval' [rmorphism of intmul 1] e2
    | Ring1 _ => fun => 1%R
    | RingMul _ e1 e2 => fun f => RingEval' f e1 * RingEval' f e2
    | RingExpn _ e1 n => fun f => RingEval' f e1 ^+ n
    | RingInv _ e1 => fun f => f (RingEval e1)^-1
    | RingMorph _ _ g e1 => fun f => RingEval' [rmorphism of f \o g] e1
    | RingMorph' _ _ g e1 => fun f => RZmodEval' [additive of f \o g] e1
    | RingPosz e1 => fun => NatEval' _ e1
    | RingNegz e1 => fun => - (1 + NatEval' _ e1)
  end f
with RZmodEval' V R (f : {additive V -> R}) (e : ZmodExpr V) : R :=
  match e in ZmodExpr V return {additive V -> R} -> R with
    | ZmodX _ x => fun f => f x
    | Zmod0 _ => fun => 0%R
    | ZmodOpp _ e1 => fun f => - RZmodEval' f e1
    | ZmodAdd _ e1 e2 => fun f => RZmodEval' f e1 + RZmodEval' f e2
    | ZmodMuln _ e1 e2 => fun f => RZmodEval' f e1 * NatEval' R e2
    | ZmodMulz _ e1 e2 => fun f =>
      RZmodEval' f e1 * RingEval' [rmorphism of intmul 1] e2
    | ZmodMorph _ _ g e1 => fun f => RZmodEval' [additive of f \o g] e1
  end f.

Lemma RingEval_correct R R' (f : {rmorphism R -> R'}) (e : RingExpr R) :
  f (RingEval e) = RingEval' f e.
Proof.
pose P R e :=
  forall R' (f : {rmorphism R -> R'}), f (RingEval e) = RingEval' f e.
pose P0 V e :=
  forall R' (f : {additive V -> R'}), f (ZmodEval e) = RZmodEval' f e.
move: R' f; elim e using (@RingExpr_ind' P P0); rewrite {R e}/P {}/P0 //=.
- by move=> R R' f; rewrite rmorph0.
- by move=> R e1 IHe1 R' f; rewrite rmorphN IHe1.
- by move=> R e1 IHe1 e2 IHe2 R' f; rewrite rmorphD IHe1 IHe2.
- by move=> R e1 IHe1 e2 R' f; rewrite rmorphMn IHe1 -mulr_natr NatEval_correct.
- by move=> R e1 IHe1 e2 IHe2 R' f; rewrite rmorphMz IHe1 -mulrzr IHe2.
- by move=> R R' f; rewrite rmorph1.
- by move=> R e1 IHe1 e2 IHe2 R' f; rewrite rmorphM IHe1 IHe2.
- by move=> R e1 IHe1 e2 R' f; rewrite rmorphX IHe1.
- by move=> R R' g e1 IHe1 R'' f; rewrite -IHe1.
- by move=> V R g e1 IHe1 R' f; rewrite -IHe1.
- by move=> e R' f; rewrite -[Posz _]intz rmorph_int [LHS]NatEval_correct.
- move=> e R' f.
  by rewrite -[Negz _]intz rmorph_int /intmul mulrS NatEval_correct.
- by move=> V R f; rewrite raddf0.
- by move=> V e1 IHe1 R f; rewrite raddfN IHe1.
- by move=> V e1 IHe1 e2 IHe2 R f; rewrite raddfD IHe1 IHe2.
- by move=> V e1 IHe1 e2 R f; rewrite raddfMn IHe1 -mulr_natr NatEval_correct.
- by move=> V e1 IHe1 e2 IHe2 R f; rewrite raddfMz IHe1 -mulrzr IHe2.
- by move=> V V' g e1 IHe1 R f; rewrite -IHe1.
Qed.

Fixpoint FieldEval' R F (f : {rmorphism R -> F}) (e : RingExpr R) : F :=
  match e in RingExpr R return {rmorphism R -> F} -> F with
    | RingX _ x => fun f => f x
    | Ring0 _ => fun => 0%R
    | RingOpp _ e1 => fun f => - FieldEval' f e1
    | RingAdd _ e1 e2 => fun f => FieldEval' f e1 + FieldEval' f e2
    | RingMuln _ e1 e2 => fun f => FieldEval' f e1 * NatEval' F e2
    | RingMulz _ e1 e2 => fun f =>
      FieldEval' f e1 * FieldEval' [rmorphism of intmul 1] e2
    | Ring1 _ => fun => 1%R
    | RingMul _ e1 e2 => fun f => FieldEval' f e1 * FieldEval' f e2
    | RingExpn _ e1 n => fun f => FieldEval' f e1 ^+ n
    | RingInv _ e1 => fun f => (FieldEval' f e1)^-1
    | RingMorph _ _ g e1 => fun f => FieldEval' [rmorphism of f \o g] e1
    | RingMorph' _ _ g e1 => fun f => FZmodEval' [additive of f \o g] e1
    | RingPosz e1 => fun => NatEval' _ e1
    | RingNegz e1 => fun => - (1 + NatEval' _ e1)
  end f
with FZmodEval' V F (f : {additive V -> F}) (e : ZmodExpr V) : F :=
  match e in ZmodExpr V return {additive V -> F} -> F with
    | ZmodX _ x => fun f => f x
    | Zmod0 _ => fun => 0%R
    | ZmodOpp _ e1 => fun f => - FZmodEval' f e1
    | ZmodAdd _ e1 e2 => fun f => FZmodEval' f e1 + FZmodEval' f e2
    | ZmodMuln _ e1 e2 => fun f => FZmodEval' f e1 * NatEval' F e2
    | ZmodMulz _ e1 e2 => fun f =>
      FZmodEval' f e1 * FieldEval' [rmorphism of intmul 1] e2
    | ZmodMorph _ _ g e1 => fun f => FZmodEval' [additive of f \o g] e1
  end f.

Lemma FieldEval_correct R F (f : {rmorphism R -> F}) (e : RingExpr R) :
  f (RingEval e) = FieldEval' f e.
Proof.
pose P R e :=
  forall F (f : {rmorphism R -> F}), f (RingEval e) = FieldEval' f e.
pose P0 V e :=
  forall F (f : {additive V -> F}), f (ZmodEval e) = FZmodEval' f e.
move: F f; elim e using (@RingExpr_ind' P P0); rewrite {R e}/P {}/P0 //=.
- by move=> R F f; rewrite rmorph0.
- by move=> R e1 IHe1 F f; rewrite rmorphN IHe1.
- by move=> R e1 IHe1 e2 IHe2 F f; rewrite rmorphD IHe1 IHe2.
- by move=> R e1 IHe1 e2 F f; rewrite rmorphMn IHe1 -mulr_natr NatEval_correct.
- by move=> R e1 IHe1 e2 IHe2 F f; rewrite rmorphMz IHe1 -mulrzr IHe2.
- by move=> R F f; rewrite rmorph1.
- by move=> R e1 IHe1 e2 IHe2 F f; rewrite rmorphM IHe1 IHe2.
- by move=> R e1 IHe1 e2 F f; rewrite rmorphX IHe1.
- by move=> F' e1 IHe1 F f; rewrite fmorphV IHe1.
- by move=> R R' g e1 IHe1 F f; rewrite -IHe1.
- by move=> V R g e1 IHe1 F f; rewrite -IHe1.
- by move=> e F f; rewrite -[Posz _]intz rmorph_int [LHS]NatEval_correct.
- move=> e F f.
  by rewrite -[Negz _]intz rmorph_int /intmul mulrS NatEval_correct.
- by move=> V F f; rewrite raddf0.
- by move=> V e1 IHe1 F f; rewrite raddfN IHe1.
- by move=> V e1 IHe1 e2 IHe2 F f; rewrite raddfD IHe1 IHe2.
- by move=> V e1 IHe1 e2 F f; rewrite raddfMn IHe1 -mulr_natr NatEval_correct.
- by move=> V e1 IHe1 e2 IHe2 F f; rewrite raddfMz IHe1 -mulrzr IHe2.
- by move=> V V' g e1 IHe1 F f; rewrite -IHe1.
Qed.

Lemma lock_PCond (F : fieldType) (l : seq F) (le : seq (PExpr Z)) :
  (forall zero one add mul sub opp Feq R_of_int exp,
   zero = 0 -> one = 1 -> add = +%R -> mul = *%R -> sub = (fun x y => x - y) ->
   opp = -%R -> Feq = eq -> R_of_int = intmul 1 -> exp = @GRing.exp F ->
   Field_theory.PCond
     zero one add mul sub opp Feq
     (fun n : Z => R_of_int (int_of_Z n)) N.to_nat exp l le) ->
  Field_theory.PCond
    0 1 +%R *%R (fun x y => x - y) -%R eq
    (fun n : Z => (int_of_Z n)%:~R) N.to_nat (@GRing.exp F) l le.
Proof. exact. Qed.

Ltac ring_reflection RMcorrect1 RMcorrect2 Rcorrect :=
  apply: (eq_trans RMcorrect1);
  apply: (eq_trans _ (esym RMcorrect2));
  apply: Rcorrect;
  [vm_compute; reflexivity].

Ltac simpl_PCond :=
  let zero := fresh "zero" in
  let one := fresh "one" in
  let add := fresh "add" in
  let mul := fresh "mul" in
  let sub := fresh "sub" in
  let opp := fresh "opp" in
  let Feq := fresh "Feq" in
  let R_of_int := fresh "R_of_int" in
  let exp := fresh "exp" in
  let zeroE := fresh "zeroE" in
  let oneE := fresh "oneE" in
  let addE := fresh "addE" in
  let mulE := fresh "mulE" in
  let subE := fresh "subE" in
  let oppE := fresh "oppE" in
  let FeqE := fresh "FeqE" in
  let R_of_intE := fresh "R_of_intE" in
  let expE := fresh "expE" in
  apply: Internals.lock_PCond;
  move=> zero one add mul sub opp Feq R_of_int exp;
  move=> zeroE oneE addE mulE subE oppE FeqE R_of_intE expE;
  vm_compute;
  rewrite ?{zero}zeroE ?{one}oneE ?{add}addE ?{mul}mulE ?{sub}subE ?{opp}oppE;
  rewrite ?{Feq}FeqE ?{R_of_int}R_of_intE ?{exp}expE;
  do ?split; apply/eqP.

Ltac field_reflection FMcorrect1 FMcorrect2 Fcorrect :=
  apply: (eq_trans FMcorrect1);
  apply: (eq_trans _ (esym FMcorrect2));
  apply: Fcorrect; [reflexivity | reflexivity | reflexivity |
                    vm_compute; reflexivity | simpl_PCond].

End Internals.

Register Coq.Init.Logic.eq       as ring.eq.
Register Coq.Init.Logic.eq_refl  as ring.erefl.
Register Coq.Init.Logic.eq_sym   as ring.esym.
Register Coq.Init.Logic.eq_trans as ring.etrans.

Elpi Tactic ring.
Elpi Accumulate File "theories/quote.elpi".
Elpi Accumulate File "theories/ring.elpi".
Elpi Typecheck.

Tactic Notation "ring" := elpi ring.
Tactic Notation "ring" ":" ne_constr_list(L) := elpi ring ltac_term_list:(L).

Elpi Tactic field.
Elpi Accumulate File "theories/quote.elpi".
Elpi Accumulate File "theories/field.elpi".
Elpi Typecheck.

Tactic Notation "field" := elpi field.
Tactic Notation "field" ":" ne_constr_list(L) := elpi field ltac_term_list:(L).
