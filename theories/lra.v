Require Import DecimalNat DecimalPos List QArith.
From Coq.micromega Require Import OrderedRing RingMicromega QMicromega EnvRing.
From Coq.micromega Require Import Refl Tauto Lqa.
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint.
From mathcomp.zify Require Import ssrZ.
From mathcomp.algebra_tactics Require ring.

Import Order.TTheory GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

Module Internals.

(* Define [Reval_formula] the semantics of [BFormula (Formula Z) Tauto.isProp]
   as arithmetic expressions on some [realDomainType].
   Then prove [RTautoChecker_sound] stating that [ZTautoChecker f w = true]
   implies that the formula [Reval_formula f] holds. *)
Section RealDomain.

Variable R : realDomainType.

Lemma Rsor :
  @SOR R 0 1 +%R *%R (fun x y => x - y) -%R
       eq (fun x y => x <= y) (fun x y => x < y).
Proof.
apply: mk_SOR_theory.
- exact: RelationClasses.eq_equivalence.
- by move=> x _ <- y _ <-.
- by move=> x _ <- y _ <-.
- by move=> x _ <-.
- by move=> x _ <- y _ <-.
- by move=> x _ <- y _ <-.
- exact: ring.Internals.RR.
- by [].
- by move=> x y xley ylex; apply: le_anti; rewrite xley ylex.
- by move=> x y z; apply: le_trans.
- move=> x y; rewrite lt_neqAle; split.
  + by move=> /andP[/eqP yneqx ->]; split.
  + by move=> [-> /eqP ->].
- move=> x y; case: (ltgtP x y) => [xlty|yltx|<-].
  + by left.
  + by right; right.
  + by right; left.
- by move=> x y z; rewrite ler_add2l.
- exact: mulr_gt0.
- by apply/eqP; rewrite eq_sym oner_neq0.
Qed.

Definition pos_to_nat' p :=
  if (p <=? 5000)%positive then Pos.to_nat p
  else Init.Nat.of_num_uint (Pos.to_num_uint p).

Lemma pos_to_nat_pos_to_nat' p : Pos.to_nat p = pos_to_nat' p.
Proof.
rewrite /pos_to_nat'; case: ifP => //= _.
rewrite -positive_N_nat -DecimalPos.Unsigned.of_to.
rewrite DecimalPos.Unsigned.of_uint_alt DecimalNat.Unsigned.of_uint_alt.
by elim: Decimal.rev => // u IHu;
  rewrite /DecimalPos.Unsigned.of_lu -/(DecimalPos.Unsigned.of_lu u);
  rewrite ?Nnat.N2Nat.inj_add Nnat.N2Nat.inj_mul IHu.
Qed.

Definition int_of_Z' (z : Z) : int :=
  match n with
  | Z0 => 0
  | Z.pos p => pos_to_nat' p
  | Z.neg p => Negz (pos_to_nat' p).-1
  end.

Lemma int_of_Z_int_of_Z' n : int_of_Z n = int_of_Z' n.
Proof. by case: n => //= p; rewrite pos_to_nat_pos_to_nat'. Qed.

Definition Z2R (x : Z) : R := (int_of_Z' x)%:~R.

Lemma Pos_to_nat_gt0 p : 0 < (Pos.to_nat p)%:R :> R.
Proof. rewrite ltr0n; exact/ssrnat.ltP/Pos2Nat.is_pos. Qed.

Lemma Pos_to_nat_neq0 p : (Pos.to_nat p)%:R != 0 :> R.
Proof. by rewrite pnatr_eq0 -lt0n; apply/ssrnat.ltP/Pos2Nat.is_pos. Qed.

Lemma Z2R_add x y : Z2R (x + y) = Z2R x + Z2R y.
Proof. by rewrite /Z2R -!int_of_Z_int_of_Z' !rmorphD/=. Qed.

Lemma Z2R_opp x : Z2R (- x) = - Z2R x.
Proof. by rewrite /Z2R -!int_of_Z_int_of_Z' !rmorphN. Qed.

Lemma Z2R_sub x y : Z2R (x - y) = Z2R x - Z2R y.
Proof. by rewrite Z2R_add Z2R_opp. Qed.

Lemma Z2R_mul x y : Z2R (x * y) = Z2R x * Z2R y.
Proof. by rewrite /Z2R -!int_of_Z_int_of_Z' !rmorphM. Qed.

Lemma Z2R_eq x y : Z.eqb x y = (Z2R x == Z2R y).
Proof.
rewrite /Z2R -!int_of_Z_int_of_Z' eqr_int.
apply/idP/idP; first by move=> /Z.eqb_spec ->.
by move=> /eqP/(f_equal Z_of_int); rewrite !int_of_ZK => ->; apply/Z.eqb_spec.
Qed.

Lemma le_int_of_Z x y : Z.le x y -> int_of_Z x <= int_of_Z y.
Proof.
case: x y => [|x|x] [|y|y] //.
- rewrite /Z.le/= Pos.compare_le_iff => xley.
  by apply/ssrnat.leP; rewrite -Pos2Nat.inj_le.
- rewrite /Z.le/= -Pos.compare_antisym Pos.compare_le_iff => ylex.
  by apply/ssrnat.leP/Peano.le_pred; rewrite -Pos2Nat.inj_le.
Qed.

Lemma Z2R_le x y : Z.leb x y = true -> Z2R x <= Z2R y.
Proof.
rewrite /Z2R -!int_of_Z_int_of_Z' ler_int => /Z.leb_le; exact: le_int_of_Z.
Qed.

Lemma RZ : ring_morph 0 1 +%R  *%R (fun x y : R => x - y) -%R eq
                      Z0 (Zpos 1) Z.add Z.mul Z.sub Z.opp Z.eqb Z2R.
Proof.
apply: mkmorph => //.
- exact: Z2R_add.
- exact: Z2R_sub.
- exact: Z2R_mul.
- exact: Z2R_opp.
- by move=> x y; rewrite Z2R_eq => /eqP.
Qed.

Lemma Rpower : power_theory 1 *%R eq N.to_nat (@GRing.exp R).
Proof.
apply: mkpow_th => x n; case: n => [//|p]; elim: p => [p|p|//] /= IHp.
- by rewrite Pos2Nat.inj_xI exprS multE mulnC exprM expr2 IHp.
- by rewrite Pos2Nat.inj_xO multE mulnC exprM expr2 IHp.
Qed.

Lemma RSORaddon :
  @SORaddon R 0 1 +%R *%R (fun x y => x - y) -%R eq (fun x y => x <= y) (* ring elements *)
  Z Z0 (Zpos 1) Z.add Z.mul Z.sub Z.opp Z.eqb Z.leb (* coefficients *)
  Z2R nat N.to_nat (@GRing.exp R).
Proof.
apply: mk_SOR_addon.
- exact: RZ.
- exact: Rpower.
- by move=> x y; rewrite Z2R_eq => /negbT/eqP.
- exact: Z2R_le.
Qed.

Definition Reval_expr :=
  eval_pexpr +%R *%R (fun x y => x - y) -%R Z2R N.to_nat (@GRing.exp R).

Definition Reval_pop2 (o : Op2) : R -> R -> Prop :=
  match o with
  | OpEq => eq
  | OpNEq => fun x y  => ~ x = y
  | OpLe => fun x y => x <= y
  | OpGe => fun x y => x >= y
  | OpLt => fun x y => x < y
  | OpGt => fun x y => x > y
  end.

Definition Reval_bop2 (o : Op2) : R -> R -> bool :=
  match o with
  | OpEq  => fun x y => x == y
  | OpNEq => fun x y => x != y
  | OpLe  => fun x y => x <= y
  | OpGe  => fun x y => x >= y
  | OpLt  => fun x y => x < y
  | OpGt  => fun x y => x > y
  end.

Definition Reval_op2 (k : Tauto.kind) : Op2 -> R -> R -> Tauto.rtyp k :=
  match k with isProp => Reval_pop2 | isBool => Reval_bop2 end.

Definition Reval_formula (e : PolEnv R) (k : Tauto.kind) (ff : Formula Z) :=
  let (lhs,o,rhs) := ff in Reval_op2 k o (Reval_expr e lhs) (Reval_expr e rhs).

Definition Reval_formula' :=
  eval_formula
    +%R *%R (fun x y => x - y) -%R
    eq (fun x y => x <= y) (fun x y => x < y) Z2R N.to_nat (@GRing.exp R).

Lemma pop2_bop2 (op : Op2) (q1 q2 : R) :
  (Reval_bop2 op q1 q2) <-> Reval_pop2 op q1 q2.
Proof. by case: op => //=; split; move/eqP. Qed.

Lemma Reval_formula_compat env b f :
  Tauto.hold b (Reval_formula env b f) <-> Reval_formula' env f.
Proof. by case: f => lhs op rhs; case: b => //=; rewrite pop2_bop2. Qed.

Definition Reval_nformula :=
  eval_nformula 0 +%R *%R eq (fun x y => x <= y) (fun x y => x < y) Z2R.

Definition ZTautoChecker (f : BFormula (Formula Z) Tauto.isProp)
    (w: list (Psatz Z)) : bool :=
  @tauto_checker
    (Formula Z) (NFormula Z) unit
    (check_inconsistent Z0 Z.eqb Z.leb)
    (nformula_plus_nformula Z0 Z.add Z.eqb)
    (@cnf_normalise Z Z0 (Zpos 1) Z.add Z.mul Z.sub Z.opp Z.eqb Z.leb unit)
    (@cnf_negate Z Z0 (Zpos 1) Z.add Z.mul Z.sub Z.opp Z.eqb Z.leb unit)
    (Psatz Z)
    (fun cl => check_normalised_formulas
                 Z0 (Zpos 1) Z.add Z.mul Z.eqb Z.leb (List.map fst cl)) f w.

Lemma RTautoChecker_sound f w : ZTautoChecker f w = true ->
  forall env, eval_bf (Reval_formula env) f.
Proof.
apply: (tauto_checker_sound _ _ _ _ Reval_nformula).
- exact: (eval_nformula_dec Rsor).
- by move=> [? ?] ? ?; apply: (check_inconsistent_sound Rsor RSORaddon).
- move=> t t' u deducett'u env evalt evalt'.
  exact: (nformula_plus_nformula_correct Rsor RSORaddon env t t').
- move=> env k ff tg cnfff; rewrite Reval_formula_compat.
  exact: (cnf_normalise_correct Rsor RSORaddon env ff tg).1.
- move=> env k ff tg cnfff; rewrite Tauto.hold_eNOT Reval_formula_compat.
  exact: (cnf_negate_correct Rsor RSORaddon env ff tg).1.
- move=> t w0 checkw0 env.
  rewrite (make_impl_map (Reval_nformula env))//.
  exact: (checker_nf_sound Rsor RSORaddon) checkw0 env.
Qed.

End RealDomain.

(* Define [Feval_formula] the semantics of [BFormula (Formula Q) Tauto.isProp]
   as arithmetic expressions on some [realFieldType].
   Then prove [FTautoChecker_sound] stating that [QTautoChecker f w = true]
   implies that the formula [Feval_formula f] holds. *)
Section RealField.

Variable F : realFieldType.

Definition Q2F (x : Q) : F :=
  match x with
  | Qmake n 1 => (int_of_Z' n)%:~R
  | Qmake 1 d => GRing.inv (int_of_Z' (Zpos d))%:~R
  | Qmake n d => (int_of_Z' n)%:~R / (nat_of_pos d)%:R
  end.

Definition Q2F' (x : Q) : F :=
  (int_of_Z (Qnum x))%:~R / (nat_of_pos (Qden x))%:R.

Lemma Q2F_Q2F' x : Q2F x = Q2F' x.
Proof.
rewrite /Q2F/Q2F'.
by case: x => -[|n|n] [p|p|] //; rewrite -int_of_Z_int_of_Z'// ?divr1//;
  case: n; rewrite // -int_of_Z_int_of_Z' mul1r;
  rewrite zify_ssreflect.SsreflectZifyInstances.nat_of_posE.
Qed.

Lemma Q2F0 : Q2F 0 = 0.
Proof. by rewrite Q2F_Q2F' /Q2F'/= mul0r. Qed.

Lemma Q2F1 : Q2F 1 = 1.
Proof. by rewrite Q2F_Q2F' /Q2F'/= Pos2Nat.inj_1 divrr// unitr1. Qed.

Lemma Q2F_add x y : Q2F (x + y) = Q2F x + Q2F y.
Proof.
rewrite !Q2F_Q2F' /Q2F'/= rmorphD/= !rmorphM/= nat_of_mul_pos intrD.
rewrite !intrM natrM mulrDl [(int_of_Z (Qnum y))%:~R * _]mulrC -!mulf_div.
rewrite !zify_ssreflect.SsreflectZifyInstances.nat_of_posE -!pmulrn.
by rewrite !divff ?Pos_to_nat_neq0// mulr1 mul1r.
Qed.

Lemma Q2F_opp x : Q2F (- x) = - Q2F x.
Proof. by rewrite !Q2F_Q2F' /Q2F'/= rmorphN/= mulrNz mulNr. Qed.

Lemma Q2F_sub x y : Q2F (x - y) = Q2F x - Q2F y.
Proof. by rewrite Q2F_add Q2F_opp. Qed.

Lemma Q2F_mul x y : Q2F (x * y) = Q2F x * Q2F y.
Proof.
by rewrite !Q2F_Q2F' /Q2F'/= rmorphM/= nat_of_mul_pos intrM natrM mulf_div.
Qed.

Lemma Q2F_eq x y : Qeq_bool x y = (Q2F x == Q2F y).
Proof.
rewrite !Q2F_Q2F' /Q2F'.
rewrite !zify_ssreflect.SsreflectZifyInstances.nat_of_posE.
rewrite GRing.eqr_div ?Pos_to_nat_neq0// !pmulrn -!intrM eqr_int.
apply/idP/idP.
- by move=> /Qeq_bool_eq/(f_equal int_of_Z); rewrite 2!rmorphM => ->.
- move=> /eqP eq; apply: Qeq_eq_bool.
  by rewrite /Qeq -[LHS]int_of_ZK -[RHS]int_of_ZK rmorphM/= eq !rmorphM.
Qed.

Lemma Q2F_le x y : Qle_bool x y = true -> Q2F x <= Q2F y.
Proof.
rewrite !Q2F_Q2F' /Q2F' Qle_bool_iff => /le_int_of_Z; rewrite !rmorphM/= => le.
rewrite !zify_ssreflect.SsreflectZifyInstances.nat_of_posE.
rewrite ler_pdivr_mulr ?Pos_to_nat_gt0// mulrAC.
by rewrite ler_pdivl_mulr ?Pos_to_nat_gt0// !pmulrn -!intrM ler_int.
Qed.

Lemma FQ : ring_morph 0 1 +%R *%R (fun x y : F => x - y) -%R eq
                      0%Q 1%Q Qplus Qmult Qminus Qopp Qeq_bool Q2F.
Proof.
apply: mkmorph.
- exact: Q2F0.
- exact: Q2F1.
- exact: Q2F_add.
- exact: Q2F_sub.
- exact: Q2F_mul.
- exact: Q2F_opp.
- by move=> x y; rewrite Q2F_eq => /eqP.
Qed.

Lemma FSORaddon :
  @SORaddon F 0 1 +%R *%R (fun x y => x - y) -%R eq (fun x y => x <= y) (* ring elements *)
  Q 0%Q 1%Q Qplus Qmult Qminus Qopp Qeq_bool Qle_bool (* coefficients *)
  Q2F nat N.to_nat (@GRing.exp F).
Proof.
apply: mk_SOR_addon.
- exact: FQ.
- exact: Rpower.
- by move=> x y; rewrite Q2F_eq => /negbT/eqP.
- exact: Q2F_le.
Qed.

Definition Feval_expr :=
  eval_pexpr +%R *%R (fun x y => x - y) -%R Q2F N.to_nat (@GRing.exp F).

Definition Feval_formula (e : PolEnv F) (k : Tauto.kind) (ff : Formula Q) :=
  let (lhs,o,rhs) := ff in Reval_op2 k o (Feval_expr e lhs) (Feval_expr e rhs).

Definition Feval_formula' :=
  eval_formula
    +%R *%R (fun x y => x - y) -%R
    eq (fun x y => x <= y) (fun x y => x < y) Q2F N.to_nat (@GRing.exp F).

Lemma Feval_formula_compat env b f :
  Tauto.hold b (Feval_formula env b f) <-> Feval_formula' env f.
Proof. by case: f => lhs op rhs; case: b => //=; rewrite pop2_bop2. Qed.

Definition Feval_nformula :=
  eval_nformula 0 +%R *%R eq (fun x y => x <= y) (fun x y => x < y) Q2F.

Lemma FTautoChecker_sound f w : QTautoChecker f w = true ->
  forall env, eval_bf (Feval_formula env) f.
Proof.
apply: (tauto_checker_sound _ _ _ _ Feval_nformula).
- exact: (eval_nformula_dec (Rsor F)).
- by move=> [? ?] ? ?; apply: (check_inconsistent_sound (Rsor F) FSORaddon).
- move=> t t' u deducett'u env evalt evalt'.
  exact: (nformula_plus_nformula_correct (Rsor F) FSORaddon env t t').
- move=> env k ff tg cnfff; rewrite Feval_formula_compat.
  exact: (cnf_normalise_correct (Rsor F) FSORaddon env ff tg).1.
- move=> env k ff tg cnfff; rewrite Tauto.hold_eNOT Feval_formula_compat.
  exact: (cnf_negate_correct (Rsor F) FSORaddon env ff tg).1.
- move=> t w0 checkw0 env.
  rewrite (make_impl_map (Feval_nformula env))//.
  exact: (checker_nf_sound (Rsor F) FSORaddon) checkw0 env.
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

(* Main tactics, called from the elpi parser (c.f., lra.elpi) *)

Ltac tacF tac efalso hyps_goal ff varmap :=
  match efalso with true => exfalso | _ => idtac end;
  (suff: hyps_goal by exact);
  let iff := fresh "__ff" in
  let ivarmap := fresh "__varmap" in
  let iwit := fresh "__wit" in
  let iprf := fresh "__prf" in
  pose (iff := ff);
  pose (ivarmap := varmap);
  tac iwit ff;
  pose (iprf := erefl true <: QTautoChecker iff iwit = true);
  change (eval_bf (Internals.Feval_formula (VarMap.find 0 ivarmap)) iff);
  exact (Internals.FTautoChecker_sound iprf (VarMap.find 0 ivarmap)).
Ltac lraF n := let wlra_Q w f := wlra_Q w f in tacF wlra_Q.
Ltac nraF n := let wnra_Q w f := wnra_Q w f in tacF wnra_Q.
Ltac psatzF n :=
  let sos_or_psatzn w f := wsos_Q w f || wpsatz_Q n w f in
  tacF sos_or_psatzn.

Ltac tacR tac efalso hyps_goal ff varmap :=
  match efalso with true => exfalso | _ => idtac end;
  (suff: hyps_goal by exact);
  let iff := fresh "__ff" in
  let ivarmap := fresh "__varmap" in
  let iwit := fresh "__wit" in
  let iprf := fresh "__prf" in
  match eval vm_compute in (Internals.BFormula_Q2Z ff) with
  | Some ?f =>
      pose (iff := f);
      pose (ivarmap := varmap);
      tac iwit ff;
      let tr := Internals.seq_Psatz_Q2Z in
      pose (iprf := erefl true <: Internals.ZTautoChecker iff (tr iwit) = true);
      change (eval_bf (Internals.Reval_formula (VarMap.find 0 ivarmap)) iff);
      exact (Internals.RTautoChecker_sound iprf (VarMap.find 0 ivarmap))
  | _ => fail  (* should never happen, the parser only parses int constants *)
  end.
Ltac lraR n := let wlra_Q w f := wlra_Q w f in tacR wlra_Q.
Ltac nraR n := let wnra_Q w f := wnra_Q w f in tacR wnra_Q.
Ltac psatzR n :=
  let sos_or_psatzn w f := wsos_Q w f || wpsatz_Q n w f in
  tacF sos_or_psatzn.

From elpi Require Import elpi.

Elpi Tactic lra.
Elpi Accumulate File "theories/lra.elpi".
Elpi Typecheck.

Tactic Notation "lra" := elpi lra "lraF" "lraR" 0.
Tactic Notation "nra" := elpi lra "nraF" "nraR" 0.
Tactic Notation "psatz" integer(n) := elpi lra "psatzF" "psatzR" ltac_int:(n).
Tactic Notation "psatz" := elpi lra "psatzF" "psatzR" (-1).

(* Avoid some stack overflows with large constants *)
#[global] Opaque Init.Nat.of_num_uint.
