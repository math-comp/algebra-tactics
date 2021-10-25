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
(* `N` and `Z`. For the fine-grained control of conversion, we provide opaque *)
(* and transparent (immediately expanding) versions of `N -> nat` and         *)
(* `Z -> int` conversions.                                                    *)

Module Type NatOfNSig.
Parameter nat_of_N_opaque : N -> nat.
Axiom nat_of_N_opaqueE : nat_of_N_opaque = nat_of_N.
End NatOfNSig.

Module Import NatOfN : NatOfNSig.
Definition nat_of_N_opaque := nat_of_N.
Definition nat_of_N_opaqueE := erefl nat_of_N.
End NatOfN.

Module Type IntOfZSig.
Parameter int_of_Z_opaque : Z -> int.
Axiom int_of_Z_opaqueE : int_of_Z_opaque = int_of_Z.
End IntOfZSig.

Module Import IntOfZ : IntOfZSig.
Definition int_of_Z_opaque := int_of_Z.
Definition int_of_Z_opaqueE := erefl int_of_Z.
End IntOfZ.

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

(* Normalizing ring and field expressions to the Horner form by reflection    *)

Definition R_of_Z (R : ringType) (n : Z) : R := (int_of_Z_opaque n)%:~R.

Lemma RE R : @ring_eq_ext R +%R *%R -%R eq.
Proof. by split; do! move=> ? _ <-. Qed.

Lemma RZ R : ring_morph 0 1 +%R *%R (fun x y : R => x - y) -%R eq
                        0%Z 1%Z Z.add Z.mul Z.sub Z.opp Z.eqb (R_of_Z R).
Proof.
rewrite /R_of_Z int_of_Z_opaqueE.
split=> //= [x y | x y | x y | x | x y /Z.eqb_eq -> //].
- by rewrite !rmorphD.
- by rewrite !rmorphB.
- by rewrite !rmorphM.
- by rewrite !rmorphN.
Qed.

Lemma PN R : @power_theory R 1 *%R eq nat nat_of_N_opaque (@GRing.exp R).
Proof.
rewrite nat_of_N_opaqueE; split => r [] //=; elim=> //= p <-.
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

Definition Rcorrect (R : comRingType) :=
  ring_correct
    (Eqsth R) (RE R) (Rth_ARth (Eqsth R) (RE R) (RR R)) (RZ R) (PN R)
    (triv_div_th (Eqsth R) (RE R) (Rth_ARth (Eqsth R) (RE R) (RR R)) (RZ R)).

Definition Fcorrect F :=
  Field_correct
    (Eqsth F) (RE F) (congr1 GRing.inv)
    (F2AF (Eqsth F) (RE F) (RF F)) (RZ F) (PN F)
    (triv_div_th (Eqsth F) (RE F) (Rth_ARth (Eqsth F) (RE F) (RR F)) (RZ F)).

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

Lemma field_correct (F : fieldType) (n : nat) (l : seq F)
                    (lpe : seq (PExpr Z * PExpr Z)) (fe1 fe2 : FExpr Z) :
  interp_PElist 0 1 +%R *%R (fun x y => x - y) -%R eq
                (R_of_Z F) nat_of_N_opaque (@GRing.exp F) l lpe ->
  let lmp :=
    mk_monpol_list 0 1 Z.add Z.mul Z.sub Z.opp Z.eqb (triv_div 0 1 Z.eqb) lpe
  in
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
      let nfe1 := Fnorm 0 1 Z.add Z.mul Z.sub Z.opp Z.eqb fe1 in
      let nfe2 := Fnorm 0 1 Z.add Z.mul Z.sub Z.opp Z.eqb fe2 in
      let norm_subst' :=
        norm_subst 0 1 Z.add Z.mul Z.sub Z.opp Z.eqb (triv_div 0 1 Z.eqb) n lmp
      in
      Peq Z.eqb (norm_subst' (PEmul (num nfe1) (denum nfe2)))
                (norm_subst' (PEmul (num nfe2) (denum nfe1))) /\
      is_true_ (PCond' true negb_ andb_
                       zero one add mul sub opp Feqb F_of_Z N.to_nat exp l'
                       (Fapp (Fcons00 0 1 Z.add Z.mul Z.sub Z.opp Z.eqb
                                      (triv_div 0 1 Z.eqb))
                             (condition nfe1 ++ condition nfe2) [::]))) ->
  let FEeval' :=
    FEeval 0 1 +%R *%R (fun x y => x - y) -%R (fun x y => x / y) GRing.inv
           (R_of_Z F) nat_of_N_opaque (@GRing.exp F) l
  in
  FEeval' fe1 = FEeval' fe2.
Proof.
move=> Hlpe lmp /=.
move=> /(_ _ _ _ _ _ _ _ _ _ _ _ _ _ erefl erefl erefl erefl erefl erefl erefl).
move=> /(_ _ _ _ _ _ _ erefl erefl erefl erefl erefl erefl) [] Heq Hcond.
apply: (Fcorrect Hlpe erefl erefl erefl Heq).
apply: Pcond_simpl_gen;
  [ exact: RE | exact/F2AF/RF/RE | exact: RZ | exact: PN |
    exact/triv_div_th/RZ/Rth_ARth/RR/RE/RE/Eqsth | move=> _ -> ].
by rewrite /R_of_Z int_of_Z_opaqueE nat_of_N_opaqueE; exact/PCondP.
Qed.

Lemma numField_correct (F : numFieldType) (n : nat) (l : seq F)
                    (lpe : seq (PExpr Z * PExpr Z)) (fe1 fe2 : FExpr Z) :
  interp_PElist 0 1 +%R *%R (fun x y => x - y) -%R eq
                (R_of_Z F) nat_of_N_opaque (@GRing.exp F) l lpe ->
  let lmp :=
    mk_monpol_list 0 1 Z.add Z.mul Z.sub Z.opp Z.eqb (triv_div 0 1 Z.eqb) lpe
  in
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
      let nfe1 := Fnorm 0 1 Z.add Z.mul Z.sub Z.opp Z.eqb fe1 in
      let nfe2 := Fnorm 0 1 Z.add Z.mul Z.sub Z.opp Z.eqb fe2 in
      let norm_subst' :=
        norm_subst 0 1 Z.add Z.mul Z.sub Z.opp Z.eqb (triv_div 0 1 Z.eqb) n lmp
      in
      Peq Z.eqb (norm_subst' (PEmul (num nfe1) (denum nfe2)))
                (norm_subst' (PEmul (num nfe2) (denum nfe1))) /\
      is_true_ (PCond' true negb_ andb_
                       zero one add mul sub opp Feqb F_of_Z N.to_nat exp l'
                       (Fapp (Fcons2 0 1 Z.add Z.mul Z.sub Z.opp Z.eqb
                                     (triv_div 0 1 Z.eqb))
                             (condition nfe1 ++ condition nfe2) [::]))) ->
  let FEeval' :=
    FEeval 0 1 +%R *%R (fun x y => x - y) -%R (fun x y => x / y) GRing.inv
           (R_of_Z F) nat_of_N_opaque (@GRing.exp F) l
  in
  FEeval' fe1 = FEeval' fe2.
Proof.
move=> Hlpe lmp /=.
move=> /(_ _ _ _ _ _ _ _ _ _ _ _ _ _ erefl erefl erefl erefl erefl erefl erefl).
move=> /(_ _ _ _ _ _ _ erefl erefl erefl erefl erefl erefl) [] Heq Hcond.
apply: (Fcorrect Hlpe erefl erefl erefl Heq).
apply: Pcond_simpl_complete;
  [ exact: RE | exact/F2AF/RF/RE | exact: RZ | exact: PN |
    exact/triv_div_th/RZ/Rth_ARth/RR/RE/RE/Eqsth | | move=> _ -> ].
- by rewrite /R_of_Z int_of_Z_opaqueE => x y /intr_inj; lia.
- by rewrite /R_of_Z int_of_Z_opaqueE nat_of_N_opaqueE; exact/PCondP.
Qed.

(* Pushing down morphisms in ring and field expressions by reflection         *)

Inductive NatExpr : Type :=
  | NatC    of N
  | NatX    of nat
  | NatAdd  of NatExpr & NatExpr
  | NatSucc of NatExpr
  | NatMul  of NatExpr & NatExpr
  | NatExp  of NatExpr & N.

Fixpoint NatEval (ne : NatExpr) : nat :=
  match ne with
    | NatC n => nat_of_N_expand n
    | NatX x => x
    | NatAdd e1 e2 => NatEval e1 + NatEval e2
    | NatSucc e => S (NatEval e)
    | NatMul e1 e2 => NatEval e1 * NatEval e2
    | NatExp e1 n => NatEval e1 ^ nat_of_N_expand n
  end.

Fixpoint NatEval' R (e : NatExpr) : R :=
  match e with
    | NatC N0 => R_of_Z R Z0
    | NatC (Npos n) => R_of_Z R (Zpos n)
    | NatX x => x%:~R
    | NatAdd e1 e2 => NatEval' R e1 + NatEval' R e2
    | NatSucc e1 => 1 + NatEval' R e1
    | NatMul e1 e2 => NatEval' R e1 * NatEval' R e2
    | NatExp e1 n => NatEval' R e1 ^+ nat_of_N_opaque n
  end.

Lemma NatEval_correct R (e : NatExpr) : (NatEval e)%:R = NatEval' R e.
Proof.
elim: e => //=.
- by rewrite /R_of_Z int_of_Z_opaqueE; case.
- by move=> e1 IHe1 e2 IHe2; rewrite natrD IHe1 IHe2.
- by move=> e IHe; rewrite mulrS IHe.
- by move=> e1 IHe1 e2 IHe2; rewrite natrM IHe1 IHe2.
- by move=> e1 IHe1 e2; rewrite natrX IHe1 nat_of_N_opaqueE.
Qed.

Inductive RingExpr : ringType -> Type :=
  | RingX R : R -> RingExpr R
  | Ring0 R : RingExpr R
  | RingOpp R : RingExpr R -> RingExpr R
  | RingZOpp : RingExpr [ringType of Z] -> RingExpr [ringType of Z]
  | RingAdd R : RingExpr R -> RingExpr R -> RingExpr R
  | RingZAdd : RingExpr [ringType of Z] -> RingExpr [ringType of Z] ->
               RingExpr [ringType of Z]
  | RingZSub : RingExpr [ringType of Z] -> RingExpr [ringType of Z] ->
               RingExpr [ringType of Z]
  | RingMuln R : RingExpr R -> NatExpr -> RingExpr R
  | RingMulz R : RingExpr R -> RingExpr [ringType of int] -> RingExpr R
  | Ring1 R : RingExpr R
  | RingMul R : RingExpr R -> RingExpr R -> RingExpr R
  | RingZMul : RingExpr [ringType of Z] -> RingExpr [ringType of Z] ->
               RingExpr [ringType of Z]
  | RingExpn R : RingExpr R -> N -> RingExpr R
  | RingExpPosz (R : unitRingType) : RingExpr R -> N -> RingExpr R
  | RingExpNegz F : RingExpr F -> N -> RingExpr F
  | RingZExp : RingExpr [ringType of Z] -> Z -> RingExpr [ringType of Z]
  | RingInv F : RingExpr F -> RingExpr F
  | RingMorph R' R : {rmorphism R' -> R} -> RingExpr R' -> RingExpr R
  | RingMorph' V R : {additive V -> R} -> ZmodExpr V -> RingExpr R
  | RingPosz : NatExpr -> RingExpr [ringType of int]
  | RingNegz : NatExpr -> RingExpr [ringType of int]
  | RingZC : Z -> RingExpr [ringType of Z]
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
    | RingZOpp e1 => Z.opp (RingEval e1)
    | RingAdd _ e1 e2 => RingEval e1 + RingEval e2
    | RingZAdd e1 e2 => Z.add (RingEval e1) (RingEval e2)
    | RingZSub e1 e2 => Z.sub (RingEval e1) (RingEval e2)
    | RingMuln _ e1 e2 => RingEval e1 *+ NatEval e2
    | RingMulz _ e1 e2 => RingEval e1 *~ RingEval e2
    | Ring1 _ => 1%R
    | RingMul _ e1 e2 => RingEval e1 * RingEval e2
    | RingZMul e1 e2 => Z.mul (RingEval e1) (RingEval e2)
    | RingExpn _ e1 n => RingEval e1 ^+ nat_of_N_expand n
    | RingExpPosz _ e1 n => RingEval e1 ^ Posz (nat_of_N_expand n)
    | RingExpNegz _ e1 n => RingEval e1 ^ Negz (nat_of_N_expand n)
    | RingZExp e1 n => Z.pow (RingEval e1) n
    | RingInv _ e1 => (RingEval e1) ^-1
    | RingMorph _ _ f e1 => f (RingEval e1)
    | RingMorph' _ _ f e1 => f (ZmodEval e1)
    | RingPosz e1 => Posz (NatEval e1)
    | RingNegz e2 => Negz (NatEval e2)
    | RingZC x => x
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
    | RingZOpp e1 => fun f => - RingEval' f e1
    | RingAdd _ e1 e2 => fun f => RingEval' f e1 + RingEval' f e2
    | RingZAdd e1 e2 => fun f => RingEval' f e1 + RingEval' f e2
    | RingZSub e1 e2 => fun f => RingEval' f e1 - RingEval' f e2
    | RingMuln _ e1 e2 => fun f => RingEval' f e1 * NatEval' R' e2
    | RingMulz _ e1 e2 => fun f =>
      RingEval' f e1 * RingEval' [rmorphism of intmul 1] e2
    | Ring1 _ => fun => 1%R
    | RingMul _ e1 e2 => fun f => RingEval' f e1 * RingEval' f e2
    | RingZMul e1 e2 => fun f => RingEval' f e1 * RingEval' f e2
    | RingExpn _ e1 n => fun f => RingEval' f e1 ^+ nat_of_N_opaque n
    | RingExpPosz _ e1 n => fun f => RingEval' f e1 ^+ nat_of_N_opaque n
    | RingExpNegz _ e1 n => fun f => f (RingEval e1 ^- (nat_of_N_opaque n).+1)
    | RingZExp e1 (Z.neg _) => fun f => 0%Z
    | RingZExp e1 n => fun f => RingEval' f e1 ^+ nat_of_N_opaque (Z.to_N n)
    | RingInv _ e1 => fun f => f (RingEval e1)^-1
    | RingMorph _ _ g e1 => fun f => RingEval' [rmorphism of f \o g] e1
    | RingMorph' _ _ g e1 => fun f => RZmodEval' [additive of f \o g] e1
    | RingPosz e1 => fun => NatEval' _ e1
    | RingNegz e1 => fun => - (1 + NatEval' _ e1)
    | RingZC x => fun => R_of_Z R' x
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

Lemma RingEval_correct_rec R R' (f : {rmorphism R -> R'}) (e : RingExpr R) :
  f (RingEval e) = RingEval' f e.
Proof.
pose P R e :=
  forall R' (f : {rmorphism R -> R'}), f (RingEval e) = RingEval' f e.
pose P0 V e :=
  forall R' (f : {additive V -> R'}), f (ZmodEval e) = RZmodEval' f e.
move: R' f; elim e using (@RingExpr_ind' P P0); rewrite {R e}/P {}/P0 //=.
- by move=> R R' f; rewrite rmorph0.
- by move=> R e1 IHe1 R' f; rewrite rmorphN IHe1.
- by move=> e1 IHe1 R' f; rewrite rmorphN IHe1.
- by move=> R e1 IHe1 e2 IHe2 R' f; rewrite rmorphD IHe1 IHe2.
- by move=> e1 IHe1 e2 IHe2 R' f; rewrite rmorphD IHe1 IHe2.
- by move=> e1 IHe1 e2 IHe2 R' f; rewrite rmorphB IHe1 IHe2.
- by move=> R e1 IHe1 e2 R' f; rewrite rmorphMn IHe1 -mulr_natr NatEval_correct.
- by move=> R e1 IHe1 e2 IHe2 R' f; rewrite rmorphMz IHe1 -mulrzr IHe2.
- by move=> R R' f; rewrite rmorph1.
- by move=> R e1 IHe1 e2 IHe2 R' f; rewrite rmorphM IHe1 IHe2.
- by move=> e1 IHe1 e2 IHe2 R' f; rewrite rmorphM IHe1 IHe2.
- by move=> R e1 IHe1 e2 R' f; rewrite rmorphX IHe1 nat_of_N_opaqueE.
- by move=> R e1 IHe1 e2 R' f; rewrite rmorphX IHe1 nat_of_N_opaqueE.
- by rewrite nat_of_N_opaqueE.
- move=> e1 IHe1 [|n|n] R' f; rewrite ?rmorph0 ?rmorph1 ?nat_of_N_opaqueE //=.
  by rewrite -IHe1 -rmorphX; congr (f _); lia.
- by move=> R R' g e1 IHe1 R'' f; rewrite -IHe1.
- by move=> V R g e1 IHe1 R' f; rewrite -IHe1.
- by move=> e R' f; rewrite -[Posz _]intz rmorph_int [LHS]NatEval_correct.
- move=> e R' f.
  by rewrite -[Negz _]intz rmorph_int /intmul mulrS NatEval_correct.
- move=> x R' f; rewrite /R_of_Z int_of_Z_opaqueE -(rmorph_int f); congr (f _).
  lia.
- by move=> V R f; rewrite raddf0.
- by move=> V e1 IHe1 R f; rewrite raddfN IHe1.
- by move=> V e1 IHe1 e2 IHe2 R f; rewrite raddfD IHe1 IHe2.
- by move=> V e1 IHe1 e2 R f; rewrite raddfMn IHe1 -mulr_natr NatEval_correct.
- by move=> V e1 IHe1 e2 IHe2 R f; rewrite raddfMz IHe1 -mulrzr IHe2.
- by move=> V V' g e1 IHe1 R f; rewrite -IHe1.
Qed.

Lemma RingEval_correct R (e : RingExpr R) :
  RingEval e = RingEval' [rmorphism of idfun] e.
Proof. exact: RingEval_correct_rec [rmorphism of idfun] _. Qed.

Fixpoint FieldEval' R F (f : {rmorphism R -> F}) (e : RingExpr R) : F :=
  match e in RingExpr R return {rmorphism R -> F} -> F with
    | RingX _ x => fun f => f x
    | Ring0 _ => fun => 0%R
    | RingOpp _ e1 => fun f => - FieldEval' f e1
    | RingZOpp e1 => fun f => - FieldEval' f e1
    | RingAdd _ e1 e2 => fun f => FieldEval' f e1 + FieldEval' f e2
    | RingZAdd e1 e2 => fun f => FieldEval' f e1 + FieldEval' f e2
    | RingZSub e1 e2 => fun f => FieldEval' f e1 - FieldEval' f e2
    | RingMuln _ e1 e2 => fun f => FieldEval' f e1 * NatEval' F e2
    | RingMulz _ e1 e2 => fun f =>
      FieldEval' f e1 * FieldEval' [rmorphism of intmul 1] e2
    | Ring1 _ => fun => 1%R
    | RingMul _ e1 e2 => fun f => FieldEval' f e1 * FieldEval' f e2
    | RingZMul e1 e2 => fun f => FieldEval' f e1 * FieldEval' f e2
    | RingExpn _ e1 n => fun f => FieldEval' f e1 ^+ nat_of_N_opaque n
    | RingExpPosz _ e1 n => fun f => FieldEval' f e1 ^+ nat_of_N_opaque n
    | RingExpNegz _ e1 n => fun f => (FieldEval' f e1 ^- (nat_of_N_opaque n).+1)
    | RingZExp e1 (Z.neg _) => fun f => 0%Z
    | RingZExp e1 n => fun f => FieldEval' f e1 ^+ nat_of_N_opaque (Z.to_N n)
    | RingInv _ e1 => fun f => (FieldEval' f e1)^-1
    | RingMorph _ _ g e1 => fun f => FieldEval' [rmorphism of f \o g] e1
    | RingMorph' _ _ g e1 => fun f => FZmodEval' [additive of f \o g] e1
    | RingPosz e1 => fun => NatEval' _ e1
    | RingNegz e1 => fun => - (1 + NatEval' _ e1)
    | RingZC x => fun => R_of_Z F x
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

Lemma FieldEval_correct_rec R F (f : {rmorphism R -> F}) (e : RingExpr R) :
  f (RingEval e) = FieldEval' f e.
Proof.
pose P R e :=
  forall F (f : {rmorphism R -> F}), f (RingEval e) = FieldEval' f e.
pose P0 V e :=
  forall F (f : {additive V -> F}), f (ZmodEval e) = FZmodEval' f e.
move: F f; elim e using (@RingExpr_ind' P P0); rewrite {R e}/P {}/P0 //=.
- by move=> R F f; rewrite rmorph0.
- by move=> R e1 IHe1 F f; rewrite rmorphN IHe1.
- by move=> e1 IHe1 F f; rewrite rmorphN IHe1.
- by move=> R e1 IHe1 e2 IHe2 F f; rewrite rmorphD IHe1 IHe2.
- by move=> e1 IHe1 e2 IHe2 F f; rewrite rmorphD IHe1 IHe2.
- by move=> e1 IHe1 e2 IHe2 F f; rewrite rmorphB IHe1 IHe2.
- by move=> R e1 IHe1 e2 F f; rewrite rmorphMn IHe1 -mulr_natr NatEval_correct.
- by move=> R e1 IHe1 e2 IHe2 F f; rewrite rmorphMz IHe1 -mulrzr IHe2.
- by move=> R F f; rewrite rmorph1.
- by move=> R e1 IHe1 e2 IHe2 F f; rewrite rmorphM IHe1 IHe2.
- by move=> e1 IHe1 e2 IHe2 F f; rewrite rmorphM IHe1 IHe2.
- by move=> R e1 IHe1 e2 F f; rewrite rmorphX IHe1 nat_of_N_opaqueE.
- by move=> R e1 IHe1 n R' f; rewrite rmorphX IHe1 nat_of_N_opaqueE.
- by move=> R e1 IHe1 n R' f; rewrite fmorphV rmorphX IHe1 nat_of_N_opaqueE.
- move=> e1 IHe1 [|n|n] F f; rewrite ?rmorph0 ?rmorph1 ?nat_of_N_opaqueE //=.
  rewrite -IHe1 -rmorphX; congr (f _); lia.
- by move=> F' e1 IHe1 F f; rewrite fmorphV IHe1.
- by move=> R R' g e1 IHe1 F f; rewrite -IHe1.
- by move=> V R g e1 IHe1 F f; rewrite -IHe1.
- by move=> e F f; rewrite -[Posz _]intz rmorph_int [LHS]NatEval_correct.
- move=> e F f.
  by rewrite -[Negz _]intz rmorph_int /intmul mulrS NatEval_correct.
- move=> x F f; rewrite /R_of_Z int_of_Z_opaqueE -(rmorph_int f); congr (f _).
  lia.
- by move=> V F f; rewrite raddf0.
- by move=> V e1 IHe1 F f; rewrite raddfN IHe1.
- by move=> V e1 IHe1 e2 IHe2 F f; rewrite raddfD IHe1 IHe2.
- by move=> V e1 IHe1 e2 F f; rewrite raddfMn IHe1 -mulr_natr NatEval_correct.
- by move=> V e1 IHe1 e2 IHe2 F f; rewrite raddfMz IHe1 -mulrzr IHe2.
- by move=> V V' g e1 IHe1 F f; rewrite -IHe1.
Qed.

Lemma FieldEval_correct F (e : RingExpr F) :
  RingEval e = FieldEval' [rmorphism of idfun] e.
Proof. exact: FieldEval_correct_rec [rmorphism of idfun] _. Qed.

(* Auxiliary Ltac code which will be invoked from Elpi *)

Ltac ring_reflection R VarMap Lpe RE1 RE2 PE1 PE2 LpeProofs :=
  let R' := constr:(GRing.ComRing.ringType R) in
  rewrite [LHS](@RingEval_correct R' RE1) [RHS](@RingEval_correct R' RE2);
  apply: (@Rcorrect R 100 VarMap Lpe PE1 PE2 LpeProofs);
  [vm_compute; reflexivity].

Ltac field_reflection F VarMap Lpe RE1 RE2 PE1 PE2 LpeProofs :=
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
  rewrite [LHS](@FieldEval_correct F RE1) [RHS](@FieldEval_correct F RE2);
  (apply: (@numField_correct _ 100 VarMap Lpe PE1 PE2 LpeProofs) ||
   apply: (@field_correct _ 100 VarMap Lpe PE1 PE2 LpeProofs));
  move=> is_true_ negb_ andb_ zero one add mul sub opp Feqb F_of_nat exp l;
  move=> is_trueE negbE andbE zeroE oneE addE mulE subE oppE FeqbE F_of_natE;
  move=> expE lE;
  vm_compute; split; first reflexivity;
  rewrite ?{is_true_}is_trueE ?{negb_}negbE ?{andb_}andbE;
  rewrite ?{zero}zeroE ?{one}oneE ?{add}addE ?{mul}mulE ?{sub}subE ?{opp}oppE;
  rewrite ?{Feqb}FeqbE ?{F_of_nat}F_of_natE ?{exp}expE ?{l}lE.

End Internals.

Strategy expand
         [addn_expand nat_of_pos_rec_expand nat_of_pos_expand nat_of_N_expand
          int_of_Z_expand RingEval RingEval' FieldEval' PEeval FEeval].

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
