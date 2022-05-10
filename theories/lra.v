From elpi Require Import elpi.
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

Section MExpr.

Implicit Types (R : ringType) (U : unitRingType) (F : fieldType).

Inductive MExpr : ringType -> Type :=
  | MEX R : R -> MExpr R
  | MEint R : Z -> MExpr R
  | MErat F : Q -> MExpr F
  | MEadd R : MExpr R -> MExpr R -> MExpr R
  | MEmul R : MExpr R -> MExpr R -> MExpr R
  | MEopp R : MExpr R -> MExpr R
  | MEpow R : MExpr R -> N -> MExpr R
  | MEmorph R R' : {rmorphism R -> R'} -> MExpr R -> MExpr R'.

Definition pos_to_nat' p :=
  if (p <=? 5000)%positive then Pos.to_nat p
  else Init.Nat.of_num_uint (Pos.to_num_uint p).

Definition int_of_Z' (z : Z) : int :=
  match z with
  | Z0 => 0
  | Z.pos p => pos_to_nat' p
  | Z.neg p => Negz (pos_to_nat' p).-1
  end.

Definition Z2R {R} (x : Z) : R := (int_of_Z' x)%:~R.

Definition Q2F {U} (x : Q) : U :=
  match x with
  | Qmake n 1 => (int_of_Z' n)%:~R
  | Qmake 1 d => GRing.inv (int_of_Z' (Zpos d))%:~R
  | Qmake n d => (int_of_Z' n)%:~R / (nat_of_pos d)%:R
  end.

Fixpoint Meval_expr R (e : MExpr R) : R :=
  match e with
  | MEX _ x => x
  | MEint _ c => Z2R c
  | MErat _ c => Q2F c
  | MEadd _ e1 e2 => Meval_expr e1 + Meval_expr e2
  | MEmul _ e1 e2 => Meval_expr e1 * Meval_expr e2
  | MEopp _ e => - Meval_expr e
  | MEpow _ e n => (Meval_expr e) ^+ (N.to_nat n)
  | MEmorph _ _ f e => f (Meval_expr e)
  end.

Fixpoint Mnorm_expr R U (f : {rmorphism R -> U}) (e : MExpr R) : U :=
  match e in MExpr R return {rmorphism R -> U} -> U with
  | MEX _ x => fun f => f x
  | MEint _ c => fun=> Z2R c
  | MErat _ c => fun=> Q2F c
  | MEadd _ e1 e2 => fun f => Mnorm_expr f e1 + Mnorm_expr f e2
  | MEmul _ e1 e2 => fun f => Mnorm_expr f e1 * Mnorm_expr f e2
  | MEopp _ e => fun f => - Mnorm_expr f e
  | MEpow _ e n => fun f => (Mnorm_expr f e) ^+ (N.to_nat n)
  | MEmorph _ _ g e => fun f => Mnorm_expr [rmorphism of f \o g] e
  end f.

Definition Q2F' {U} (x : Q) : U :=
  (int_of_Z (Qnum x))%:~R / (nat_of_pos (Qden x))%:R.

Lemma pos_to_nat_pos_to_nat' p : Pos.to_nat p = pos_to_nat' p.
Proof.
rewrite /pos_to_nat'; case: ifP => //= _.
rewrite -positive_N_nat -DecimalPos.Unsigned.of_to.
rewrite DecimalPos.Unsigned.of_uint_alt DecimalNat.Unsigned.of_uint_alt.
by elim: Decimal.rev => // u IHu;
  rewrite /DecimalPos.Unsigned.of_lu -/(DecimalPos.Unsigned.of_lu u);
  rewrite ?Nnat.N2Nat.inj_add Nnat.N2Nat.inj_mul IHu.
Qed.

Lemma int_of_Z_int_of_Z' n : int_of_Z n = int_of_Z' n.
Proof. by case: n => //= p; rewrite pos_to_nat_pos_to_nat'. Qed.

Lemma Q2F_Q2F' {U} x : Q2F x = Q2F' x :> U.
Proof.
rewrite /Q2F/Q2F'.
by case: x => -[|n|n] [p|p|] //; rewrite -int_of_Z_int_of_Z'// ?divr1//;
  case: n; rewrite // -int_of_Z_int_of_Z' mul1r;
  rewrite zify_ssreflect.SsreflectZifyInstances.nat_of_posE.
Qed.

Lemma Mnorm_expr_correct U (e : MExpr U) :
  Meval_expr e = Mnorm_expr [rmorphism of idfun] e.
Proof.
suff: forall R (e : MExpr R) (f : {rmorphism R -> U}),
    f (Meval_expr e) = Mnorm_expr f e.
  by move=> /(_ _ e [rmorphism of idfun]).
move=> R {}e.
elim: e => {}R.
- by [].
- by move=> c f; rewrite rmorph_int.
- by move=> c f; rewrite /= !Q2F_Q2F' rmorphM rmorph_int fmorphV rmorph_nat.
- by move=> e1 IH1 e2 IH2 f; rewrite rmorphD IH1 IH2.
- by move=> e1 IH1 e2 IH2 f; rewrite rmorphM IH1 IH2.
- by move=> e IH f; rewrite /= rmorphN IH.
- by move=> e IH n f; rewrite /= rmorphX IH.
- by move=> R' g e IH f; apply: (IH [rmorphism of f \o g]).
Qed.

End MExpr.

Section MFormula.

Context {R : numDomainType}.

Record MFormula := { Mlhs : MExpr R;  Mop : Op2;  Mrhs : MExpr R }.

Definition Reval_pop2 (o : Op2) : R -> R -> Prop :=
  match o with
  | OpEq => eq
  | OpNEq => fun x y => ~ x = y
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

Definition Meval_formula (k : Tauto.kind) (ff : MFormula) :=
  let (lhs,o,rhs) := ff in Reval_op2 k o (Meval_expr lhs) (Meval_expr rhs).

Definition Mnorm_formula (k : Tauto.kind) (ff : MFormula) :=
  let norm := Mnorm_expr [rmorphism of idfun] in
  let (lhs,o,rhs) := ff in Reval_op2 k o (norm lhs) (norm rhs).

Lemma Mnorm_formula_correct k (ff : MFormula) :
  Meval_formula k ff = Mnorm_formula k ff.
Proof. by case: ff => l o r /=; rewrite !Mnorm_expr_correct. Qed.

Lemma Mnorm_bf_correct k (ff : BFormula MFormula k) :
  eval_bf Meval_formula ff = eval_bf Mnorm_formula ff.
Proof.
elim: ff => // {k}.
- by move=> k ff ?; exact: Mnorm_formula_correct.
- by move=> k ff1 IH1 ff2 IH2; congr eAND.
- by move=> k ff1 IH1 ff2 IH2; congr eOR.
- by move=> k ff IH; congr eNOT.
- by move=> k ff1 IH1 o ff2 IH2; congr eIMPL.
- by move=> k ff1 IH1 ff2 IH2; congr eIFF.
- by move=> ff1 IH1 ff2 IH2; congr eq.
Qed.

End MFormula.

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

Lemma Pos_to_nat_gt0 p : 0 < (Pos.to_nat p)%:R :> R.
Proof. rewrite ltr0n; exact/ssrnat.ltP/Pos2Nat.is_pos. Qed.

Lemma Pos_to_nat_neq0 p : (Pos.to_nat p)%:R != 0 :> R.
Proof. by rewrite pnatr_eq0 -lt0n; apply/ssrnat.ltP/Pos2Nat.is_pos. Qed.

Lemma Z2R_add x y : Z2R (x + y) = Z2R x + Z2R y :> R.
Proof. by rewrite /Z2R -!int_of_Z_int_of_Z' !rmorphD/=. Qed.

Lemma Z2R_opp x : Z2R (- x) = - Z2R x :> R.
Proof. by rewrite /Z2R -!int_of_Z_int_of_Z' !rmorphN. Qed.

Lemma Z2R_sub x y : Z2R (x - y) = Z2R x - Z2R y :> R.
Proof. by rewrite Z2R_add Z2R_opp. Qed.

Lemma Z2R_mul x y : Z2R (x * y) = Z2R x * Z2R y :> R.
Proof. by rewrite /Z2R -!int_of_Z_int_of_Z' !rmorphM. Qed.

Lemma Z2R_eq x y : Z.eqb x y = (Z2R x == Z2R y :> R).
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

Lemma Z2R_le x y : Z.leb x y = true -> Z2R x <= Z2R y :> R.
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
  eval_nformula 0 +%R *%R eq (fun x y => x <= y) (fun x y => x < y) (@Z2R R).

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

Lemma Q2F0 : Q2F 0 = 0 :> F.
Proof. by rewrite Q2F_Q2F' /Q2F'/= mul0r. Qed.

Lemma Q2F1 : Q2F 1 = 1 :> F.
Proof. by rewrite Q2F_Q2F' /Q2F'/= Pos2Nat.inj_1 divrr// unitr1. Qed.

Lemma Q2F_add x y : Q2F (x + y) = Q2F x + Q2F y :> F.
Proof.
rewrite !Q2F_Q2F' /Q2F'/= rmorphD/= !rmorphM/= nat_of_mul_pos intrD.
rewrite !intrM natrM mulrDl [(int_of_Z (Qnum y))%:~R * _]mulrC -!mulf_div.
rewrite !zify_ssreflect.SsreflectZifyInstances.nat_of_posE -!pmulrn.
by rewrite !divff ?Pos_to_nat_neq0// mulr1 mul1r.
Qed.

Lemma Q2F_opp x : Q2F (- x) = - Q2F x :> F.
Proof. by rewrite !Q2F_Q2F' /Q2F'/= rmorphN/= mulrNz mulNr. Qed.

Lemma Q2F_sub x y : Q2F (x - y) = Q2F x - Q2F y :> F.
Proof. by rewrite Q2F_add Q2F_opp. Qed.

Lemma Q2F_mul x y : Q2F (x * y) = Q2F x * Q2F y :> F.
Proof.
by rewrite !Q2F_Q2F' /Q2F'/= rmorphM/= nat_of_mul_pos intrM natrM mulf_div.
Qed.

Lemma Q2F_eq x y : Qeq_bool x y = (Q2F x == Q2F y :> F).
Proof.
rewrite !Q2F_Q2F' /Q2F'.
rewrite !zify_ssreflect.SsreflectZifyInstances.nat_of_posE.
rewrite GRing.eqr_div ?Pos_to_nat_neq0// !pmulrn -!intrM eqr_int.
apply/idP/idP.
- by move=> /Qeq_bool_eq/(f_equal int_of_Z); rewrite 2!rmorphM => ->.
- move=> /eqP eq; apply: Qeq_eq_bool.
  by rewrite /Qeq -[LHS]int_of_ZK -[RHS]int_of_ZK rmorphM/= eq !rmorphM.
Qed.

Lemma Q2F_le x y : Qle_bool x y = true -> Q2F x <= Q2F y :> F.
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
  eval_nformula 0 +%R *%R eq (fun x y => x <= y) (fun x y => x < y) (@Q2F F).

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
  (* Add support for PsatzLet once 8.16 becomes the minimum Coq version *)
  (* | PsatzLet p1 p2 => *)
  (*     let (p1, n1) := Psatz_Q2Z l p1 in *)
  (*     let (p2, n2) := Psatz_Q2Z (n1 :: l) p2 in *)
  (*     (PsatzLet p1 p2, n2) *)
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
  | _ => (PsatzZ _, 1%positive)
  (* replace previous line by the following once 8.16 becomes the minimum Coq *)
  (* | PsatzZ => (PsatzZ _, 1%positive) *)
  end.

Definition seq_Psatz_Q2Z : seq (Psatz Q) -> seq (Psatz Z) :=
  map (fun p => fst (Psatz_Q2Z [::] p)).

(* BEGIN compat Coq <= 8.15 *)
(* This should be removed when algebra-tactics requires Coq >= 8.16
   (also remove all the translation to Q in lra.elpi) *)

(* Dummy function to feed micromega with formulas whose variables are in Q *)
Definition R2Q {R : ringType} (_ : R) : Q := 0%Q.

(* As a small optimization, micromega postprocesses formulas
   to abstract parts that are not used in the proof.
   In practice, algebraic parts of the formulas [A] are replaced
   by propositions [X], see vcgen_25 in ../examples/lra_examples.v
   for an example (most of the hypotheses are unused there).
   We thus need to postprocess our own reified formulas to avoid
   the witness produced by micromega to become out of sync. *)
Let BF C k := BFormula (Formula C) k.
Fixpoint abstract {C} (eval : forall k, BF C k -> rtyp k) {k} (aff : BF Q k) :
    BF C k -> BF C k :=
  match aff in GFormula k1 return BF C k1 -> BF C k1 with
  | IMPL _ aff1 _ aff2
  | AND _ aff1 aff2
  | OR _ aff1 aff2
  | IFF _ aff1 aff2 =>
      fun ff =>
        match
          ff in GFormula k2
          return (BF C k2 -> BF C k2) -> (BF C k2 -> BF C k2) -> BF C k2
        with
        | IMPL _ ff1 _ ff2 => fun a1 a2 => IMPL (a1 ff1) None (a2 ff2)
        | AND _ ff1 ff2 => fun a1 a2 => AND (a1 ff1) (a2 ff2)
        | OR _ ff1 ff2 => fun a1 a2 => OR (a1 ff1) (a2 ff2)
        | IFF _ ff1 ff2 => fun a1 a2 => IFF (a1 ff1) (a2 ff2)
        | TT _ => fun _ _ => TT _
        | FF _ => fun _ _=> FF _
        | X _ t => fun _ _ => X _ t
        | A _ t a => fun _ _ => A _ t a
        | NOT _ g2 => fun _ _ => NOT g2
        | EQ g2 g3 => fun _ _ => EQ g2 g3
        end (abstract eval aff1) (abstract eval aff2)
  | X _ _ => fun ff => X _ (eval _ ff)
  | TT _ | FF _ | A _ _ _ | NOT _ _ | EQ _ _ => id
  end.

(* Coq < 8.16 *)
Ltac tac_compat tac fQ eval f :=
  match eval hnf in (ltac:(tac) : fQ) with
  | QTautoChecker_sound ?aff ?wit _ _ =>
      let iaff := fresh "__aff" in
      let iff := fresh "__ff" in
      let iwit := fresh "__wit" in
      pose (iaff := aff);
      pose (iff := abstract eval iaff f);
      pose (iwit := wit)
  end.

(* Coq >= 8.16 *)
Ltac tac_ltac1 tac ff f :=
  let iff := fresh "__ff" in
  let iwit := fresh "__wit" in
  pose (iff := f);
  tac iwit ff.

Ltac wlra_Q_compat _ := tac_compat lra.

(* The tactic notation wlra_Q doesn't exist in Coq < 8.16, we thus declare
   a tactic with the same name to avoid compilation errors
   (this doesn't mask the tactic notation when it exists). *)
Set Warnings "-unusable-identifier".
Ltac wlra_Q w f := idtac.
Set Warnings "unusable-identifier".
Ltac wlra_Q_ltac1 _ := let wlra_Q w f := wlra_Q w f in tac_ltac1 wlra_Q.

Ltac wnra_Q_compat _ := tac_compat nra.

Set Warnings "-unusable-identifier".
Ltac wnra_Q w f := idtac.
Set Warnings "unusable-identifier".
Ltac wnra_Q_ltac1 _ := let wnra_Q w f := wnra_Q w f in tac_ltac1 wnra_Q.

Ltac wpsatz_Q_compat n := let psatz := psatz Q n in tac_compat psatz.

Set Warnings "-unusable-identifier".
Ltac wsos_Q w f := idtac.
Ltac wpsatz_Q n w f := idtac.
Set Warnings "unusable-identifier".
Ltac wpsatz_Q_ltac1 n :=
  let psatz w f := wsos_Q w f || wpsatz_Q n w f in tac_ltac1 psatz.

End Internals.

Elpi Tactic compat815.
Elpi Accumulate File "theories/compat815.elpi".
Elpi Typecheck.

(* Elpi will call the first or second tactic depending on Coq version *)
Tactic Notation "wlra_Q" ident(w) constr(ff) constr(fQ) constr(env) constr(f) :=
  elpi compat815 "Internals.wlra_Q_compat" "Internals.wlra_Q_ltac1"
       0 ltac_term:(ff) ltac_term:(fQ) ltac_term:(env) ltac_term:(f).
Tactic Notation "wnra_Q" ident(w) constr(ff) constr(fQ) constr(env) constr(f) :=
  elpi compat815 "Internals.wnra_Q_compat" "Internals.wnra_Q_ltac1"
       0 ltac_term:(ff) ltac_term:(fQ) ltac_term:(env) ltac_term:(f).
Tactic Notation "wpsatz_Q" int_or_var(n)
       ident(w) constr(ff) constr(fQ) constr(env) constr(f) :=
  elpi compat815 "Internals.wpsatz_Q_compat" "Internals.wpsatz_Q_ltac1"
       ltac_int:(n) ltac_term:(ff) ltac_term:(fQ) ltac_term:(env) ltac_term:(f).

(* END compat Coq <= 8.15 *)

(* Main tactics, called from the elpi parser (c.f., lra.elpi) *)

Ltac tacF tac efalso hyps_goal rff ff ffQ varmap :=
  match efalso with true => exfalso | _ => idtac end;
  (suff: hyps_goal by exact);
  let irff := fresh "__rff" in
  let iff := fresh "__ff" in
  let ivarmap := fresh "__varmap" in
  let iwit := fresh "__wit" in
  let iprf := fresh "__prf" in
  pose (irff := rff);
  pose (ivarmap := varmap);
  tac iwit ff ffQ
      (eval_bf (Internals.Feval_formula (VarMap.find 0 ivarmap))) ff;
  pose (iprf := erefl true <: QTautoChecker iff iwit = true);
  change (eval_bf Internals.Meval_formula irff);
  rewrite Internals.Mnorm_bf_correct;
  change (eval_bf (Internals.Feval_formula (VarMap.find 0 ivarmap)) iff);
  exact (Internals.FTautoChecker_sound iprf (VarMap.find 0 ivarmap)).
Ltac lraF n := let wlra_Q w ff fQ e f := wlra_Q w ff fQ e f in tacF wlra_Q.
Ltac nraF n := let wnra_Q w ff fQ e f := wnra_Q w ff fQ e f in tacF wnra_Q.
Ltac psatzF n :=
  let wpsatz_Q w ff fQ e f := wpsatz_Q n w ff fQ e f in tacF wpsatz_Q.

Ltac tacR tac efalso hyps_goal rff ff ffQ varmap :=
  match efalso with true => exfalso | _ => idtac end;
  (suff: hyps_goal by exact);
  let irff := fresh "__rff" in
  let iff := fresh "__ff" in
  let ivarmap := fresh "__varmap" in
  let iwit := fresh "__wit" in
  let iprf := fresh "__prf" in
  match eval vm_compute in (Internals.BFormula_Q2Z ff) with
  | Some ?f =>
      pose (irff := rff);
      pose (ivarmap := varmap);
      tac iwit ff ffQ
          (eval_bf (Internals.Reval_formula (VarMap.find 0 ivarmap))) f;
      let tr := Internals.seq_Psatz_Q2Z in
      pose (iprf := erefl true <: Internals.ZTautoChecker iff (tr iwit) = true);
      change (eval_bf Internals.Meval_formula irff);
      rewrite Internals.Mnorm_bf_correct;
      change (eval_bf (Internals.Reval_formula (VarMap.find 0 ivarmap)) iff);
      exact (Internals.RTautoChecker_sound iprf (VarMap.find 0 ivarmap))
  | _ => fail  (* should never happen, the parser only parses int constants *)
  end.
Ltac lraR n := let wlra_Q w ff fQ e f := wlra_Q w ff fQ e f in tacR wlra_Q.
Ltac nraR n := let wnra_Q w ff fQ e f := wnra_Q w ff fQ e f in tacR wnra_Q.
Ltac psatzR n :=
  let wpsatz_Q w ff fQ e f := wpsatz_Q n w ff fQ e f in tacR wpsatz_Q.

Elpi Tactic lra.
Elpi Accumulate File "theories/lra.elpi".
Elpi Typecheck.

Tactic Notation "lra" := elpi lra "lraF" "lraR" 0.
Tactic Notation "nra" := elpi lra "nraF" "nraR" 0.
Tactic Notation "psatz" integer(n) := elpi lra "psatzF" "psatzR" ltac_int:(n).
Tactic Notation "psatz" := elpi lra "psatzF" "psatzR" (-1).

(* Avoid some stack overflows with large constants *)
#[global] Opaque Init.Nat.of_num_uint.
