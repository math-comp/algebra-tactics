From Coq Require Import ZArith ZifyClasses Ring Ring_polynom Field_theory.
From elpi Require Export elpi.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat choice seq.
From mathcomp Require Import fintype finfun bigop order ssralg ssrnum ssrint rat.
From mathcomp Require Import zify.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.

Local Open Scope ring_scope.

Definition int_of_Z (n : Z) : int :=
  match n with
  | Z0 => Posz 0
  | Zpos p => Posz (Pos.to_nat p)
  | Zneg p => Negz (Pos.to_nat p).-1
  end.

Definition Z_of_int (n : int) : Z :=
  match n with
  | Posz n => Z.of_nat n
  | Negz n' => Z.opp (Z.of_nat (n' + 1))
  end.

Lemma int_of_ZK : cancel int_of_Z Z_of_int.
Proof. by case=> //= p; lia. Qed.

Instance Op_int_of_Z : UnOp int_of_Z := { TUOp := id; TUOpInj := int_of_ZK }.
Add Zify UnOp Op_int_of_Z.

Instance Op_Z_of_int : UnOp Z_of_int := { TUOp := id; TUOpInj := fun => erefl }.
Add Zify UnOp Op_Z_of_int.

Lemma Z_of_intK : cancel Z_of_int int_of_Z.
Proof. by move=> ?; lia. Qed.

(* The following proofs are based on ones in elliptic-curves-ssr:             *)
(* https://github.com/strub/elliptic-curves-ssr/blob/631af893e591466207929714c45b5f7476d579d0/common/ssrring.v *)

Lemma Z_eqP : Equality.axiom Z.eqb.
Proof. by move=> x y; apply: (iffP idP); lia. Qed.

Canonical Z_eqType := EqType Z (EqMixin Z_eqP).
Canonical Z_choiceType := ChoiceType Z (CanChoiceMixin int_of_ZK).
Canonical Z_countType := CountType Z (CanCountMixin int_of_ZK).

Definition Z_zmodMixin :=
  ZmodMixin Zplus_assoc Zplus_comm Zplus_0_l Zplus_opp_l.
Canonical Z_zmodType := ZmodType Z Z_zmodMixin.

Definition Z_ringMixin :=
  RingMixin
    Zmult_assoc Zmult_1_l Zmult_1_r Zmult_plus_distr_l Zmult_plus_distr_r isT.
Canonical Z_ringType := RingType Z Z_ringMixin.

Module Import AuxLemmas.

Implicit Types (R : ringType) (F : fieldType).

Section Ring.

Variable (R : ringType).

Let R_of_Z (n : Z) : R := (int_of_Z n)%:~R.

Lemma R_of_Z_is_additive : additive R_of_Z.
Proof. by move=> x y; rewrite -mulrzBr /+%R /-%R /=; congr intmul; lia. Qed.

Local Canonical R_of_Z_additive := Additive R_of_Z_is_additive.

Lemma R_of_Z_is_multiplicative : multiplicative R_of_Z.
Proof. by split=> //= x y; rewrite -intrM /*%R /=; congr intmul; lia. Qed.

Local Canonical R_of_Z_rmorphism := AddRMorphism R_of_Z_is_multiplicative.

Lemma RE : @ring_eq_ext R +%R *%R -%R eq.
Proof. by split; do! move=> ? _ <-. Qed.

Lemma RZ : ring_morph 0 1 +%R *%R (fun x y => x - y) -%R eq
                      0%Z 1%Z Zplus Zmult Zminus Z.opp Zeq_bool R_of_Z.
Proof.
by split=> //=;
  [ exact: rmorphD | exact: rmorphB | exact: rmorphM | exact: raddfN
  | by move=> x y /Zeq_bool_eq -> ].
Qed.

Lemma PN : @power_theory R 1 *%R eq nat nat_of_N (@GRing.exp R).
Proof.
by split=> r [] //=; elim=> //= p <-;
  rewrite (Pos2Nat.inj_xI, Pos2Nat.inj_xO) ?exprS -exprD addnn -mul2n.
Qed.

End Ring.

Lemma RR (R : comRingType) :
  @ring_theory R 0 1 +%R *%R (fun x y => x - y) -%R eq.
Proof.
exact/mk_rt/subrr/(fun _ _ => erefl)/mulrDl/mulrA/mulrC/mul1r/addrA/addrC/add0r.
Qed.

Lemma RF (F : fieldType) :
  @field_theory
    F 0 1 +%R *%R (fun x y => x - y) -%R (fun x y => x / y) GRing.inv eq.
Proof.
by split => //= [||x /eqP];
  [exact: RR | apply/eqP; rewrite oner_eq0 | exact: mulVf].
Qed.

Definition Rcorrect (R : comRingType) :=
  ring_correct
    (Eqsth R) (RE R) (Rth_ARth (Eqsth R) (RE R) (RR R)) (RZ R) (PN R)
    (triv_div_th (Eqsth R) (RE R) (Rth_ARth (Eqsth R) (RE R) (RR R)) (RZ R)).

Definition Fcorrect (F : fieldType) :=
  Field_correct
    (Eqsth F) (RE F) (congr1 GRing.inv)
    (F2AF (Eqsth F) (RE F) (RF F)) (RZ F) (PN F)
    (triv_div_th (Eqsth F) (RE F) (Rth_ARth (Eqsth F) (RE F) (RR F)) (RZ F)).

Inductive NExpr : Type :=
  | NEX : nat -> NExpr
  | NEadd : NExpr -> NExpr -> NExpr
  | NEsucc : NExpr -> NExpr
  | NEmul : NExpr -> NExpr -> NExpr
  | NEexp : NExpr -> nat -> NExpr.

Fixpoint NEeval (ne : NExpr) : nat :=
  match ne with
    | NEX x => x
    | NEadd e1 e2 => NEeval e1 + NEeval e2
    | NEsucc e => S (NEeval e)
    | NEmul e1 e2 => NEeval e1 * NEeval e2
    | NEexp e1 n => NEeval e1 ^ n
  end.

Fixpoint NEeval' R (e : NExpr) : R :=
  match e with
    | NEX x => x%:~R
    | NEadd e1 e2 => NEeval' R e1 + NEeval' R e2
    | NEsucc e1 => 1 + NEeval' R e1
    | NEmul e1 e2 => NEeval' R e1 * NEeval' R e2
    | NEexp e1 n => NEeval' R e1 ^+ n
  end.

Lemma NEeval_correct R (e : NExpr) : (NEeval e)%:R = NEeval' R e.
Proof.
elim: e => //=.
- by move=> e1 IHe1 e2 IHe2; rewrite natrD IHe1 IHe2.
- by move=> e IHe; rewrite mulrS IHe.
- by move=> e1 IHe1 e2 IHe2; rewrite natrM IHe1 IHe2.
- by move=> e1 IHe1 e2; rewrite natrX IHe1.
Qed.

Inductive RExpr : ringType -> Type :=
  | REX (R : ringType) : R -> RExpr R
  | RE0 (R : ringType) : RExpr R
  | REopp (R : ringType) : RExpr R -> RExpr R
  | REadd (R : ringType) : RExpr R -> RExpr R -> RExpr R
  | REmuln (R : ringType) : RExpr R -> NExpr -> RExpr R
  | REmulz (R : ringType) : RExpr R -> RExpr [ringType of int] -> RExpr R
  | RE1 (R : ringType) : RExpr R
  | REmul (R : ringType) : RExpr R -> RExpr R -> RExpr R
  | REexpn (R : ringType) : RExpr R -> nat -> RExpr R
  | REinv (F : fieldType) : RExpr F -> RExpr F
  | REmorph (R' R : ringType) : {rmorphism R' -> R} -> RExpr R' -> RExpr R
  | REposz : NExpr -> RExpr [ringType of int]
  | REnegz : NExpr -> RExpr [ringType of int].

Fixpoint REeval R (e : RExpr R) : R :=
  match e with
    | REX _ x => x
    | RE0 _ => 0%R
    | REopp _ e1 => - REeval e1
    | REadd _ e1 e2 => REeval e1 + REeval e2
    | REmuln _ e1 e2 => REeval e1 *+ NEeval e2
    | REmulz _ e1 e2 => REeval e1 *~ REeval e2
    | RE1 _ => 1%R
    | REmul _ e1 e2 => REeval e1 * REeval e2
    | REexpn _ e1 n => REeval e1 ^+ n
    | REinv _ e1 => (REeval e1) ^-1
    | REmorph _ _ f e1 => f (REeval e1)
    | REposz e1 => Posz (NEeval e1)
    | REnegz e2 => Negz (NEeval e2)
  end.

Fixpoint RMEeval R R' (f : {rmorphism R -> R'}) (e : RExpr R) : R' :=
  match e in RExpr R return {rmorphism R -> R'} -> R' with
    | REX _ x => fun f => f x
    | RE0 _ => fun => 0%R
    | REopp _ e1 => fun f => - RMEeval f e1
    | REadd _ e1 e2 => fun f => RMEeval f e1 + RMEeval f e2
    | REmuln _ e1 e2 => fun f => RMEeval f e1 * NEeval' R' e2
    | REmulz _ e1 e2 => fun f =>
      RMEeval f e1 * RMEeval [rmorphism of intmul _] e2
    | RE1 _ => fun => 1%R
    | REmul _ e1 e2 => fun f => RMEeval f e1 * RMEeval f e2
    | REexpn _ e1 n => fun f => RMEeval f e1 ^+ n
    | REinv _ e1 => fun f => f (REeval e1)^-1
    | REmorph _ _ g e1 => fun f => RMEeval [rmorphism of f \o g] e1
    | REposz e1 => fun => NEeval' _ e1
    | REnegz e1 => fun => - (1 + NEeval' _ e1)
  end f.

Lemma RMEeval_correct R R' (f : {rmorphism R -> R'}) (e : RExpr R) :
  f (REeval e) = RMEeval f e.
Proof.
elim: {R} e R' f => //=.
- by move=> R R' f; rewrite rmorph0.
- by move=> R e1 IHe1 R' f; rewrite rmorphN IHe1.
- by move=> R e1 IHe1 e2 IHe2 R' f; rewrite rmorphD IHe1 IHe2.
- by move=> R e1 IHe1 e2 R' f; rewrite rmorphMn IHe1 -mulr_natr NEeval_correct.
- by move=> R e1 IHe1 e2 IHe2 R' f; rewrite rmorphMz IHe1 -mulrzr IHe2.
- by move=> R R' f; rewrite rmorph1.
- by move=> R e1 IHe1 e2 IHe2 R' f; rewrite rmorphM IHe1 IHe2.
- by move=> R e1 IHe1 e2 R' f; rewrite rmorphX IHe1.
- by move=> R R' g e1 IHe1 R'' f; rewrite -IHe1.
- by move=> e R' f; rewrite -[Posz _]intz rmorph_int [LHS]NEeval_correct.
- move=> e R' f.
  by rewrite -[Negz _]intz rmorph_int /intmul mulrS NEeval_correct.
Qed.

Fixpoint FMEeval R F (f : {rmorphism R -> F}) (e : RExpr R) : F :=
  match e in RExpr R return {rmorphism R -> F} -> F with
    | REX _ x => fun f => f x
    | RE0 _ => fun => 0%R
    | REopp _ e1 => fun f => - FMEeval f e1
    | REadd _ e1 e2 => fun f => FMEeval f e1 + FMEeval f e2
    | REmuln _ e1 e2 => fun f => FMEeval f e1 * NEeval' F e2
    | REmulz _ e1 e2 => fun f =>
      FMEeval f e1 * FMEeval [rmorphism of intmul _] e2
    | RE1 _ => fun => 1%R
    | REmul _ e1 e2 => fun f => FMEeval f e1 * FMEeval f e2
    | REexpn _ e1 n => fun f => FMEeval f e1 ^+ n
    | REinv _ e1 => fun f => (FMEeval f e1)^-1
    | REmorph _ _ g e1 => fun f => FMEeval [rmorphism of f \o g] e1
    | REposz e1 => fun => NEeval' _ e1
    | REnegz e1 => fun => - (1 + NEeval' _ e1)
  end f.

Lemma FMEeval_correct R F (f : {rmorphism R -> F}) (e : RExpr R) :
  f (REeval e) = FMEeval f e.
Proof.
elim: {R} e F f => //=.
- by move=> R F f; rewrite rmorph0.
- by move=> R e1 IHe1 F f; rewrite rmorphN IHe1.
- by move=> R e1 IHe1 e2 IHe2 F f; rewrite rmorphD IHe1 IHe2.
- by move=> R e1 IHe1 e2 F f; rewrite rmorphMn IHe1 -mulr_natr NEeval_correct.
- by move=> R e1 IHe1 e2 IHe2 F f; rewrite rmorphMz IHe1 -mulrzr IHe2.
- by move=> R F f; rewrite rmorph1.
- by move=> R e1 IHe1 e2 IHe2 F f; rewrite rmorphM IHe1 IHe2.
- by move=> R e1 IHe1 e2 F f; rewrite rmorphX IHe1.
- by move=> F' e1 IHe1 F f; rewrite fmorphV IHe1.
- by move=> R R' g e1 IHe1 F f; rewrite -IHe1.
- by move=> e F f; rewrite -[Posz _]intz rmorph_int [LHS]NEeval_correct.
- move=> e F f.
  by rewrite -[Negz _]intz rmorph_int /intmul mulrS NEeval_correct.
Qed.

End AuxLemmas.

Register Coq.Init.Logic.eq       as ring.eq.
Register Coq.Init.Logic.eq_refl  as ring.erefl.
Register Coq.Init.Logic.eq_sym   as ring.esym.
Register Coq.Init.Logic.eq_trans as ring.etrans.

Elpi Tactic ring.
Elpi Accumulate File "theories/quote.elpi".
Elpi Accumulate File "theories/ring.elpi".
Elpi Typecheck.

Ltac ring_reflection RMcorrect1 RMcorrect2 Rcorrect :=
  apply: (eq_trans RMcorrect1);
  apply: (eq_trans _ (esym RMcorrect2));
  apply: Rcorrect;
  [vm_compute; reflexivity].

Tactic Notation "ring" := elpi ring.
Tactic Notation "ring" ":" ne_constr_list(L) := elpi ring ltac_term_list:(L).

Elpi Tactic field.
Elpi Accumulate File "theories/quote.elpi".
Elpi Accumulate File "theories/field.elpi".
Elpi Typecheck.

Ltac field_reflection FMcorrect1 FMcorrect2 Fcorrect :=
  apply: (eq_trans FMcorrect1);
  apply: (eq_trans _ (esym FMcorrect2));
  apply: Fcorrect; [reflexivity | reflexivity | reflexivity |
                    vm_compute; reflexivity | simpl].

Tactic Notation "field" := elpi field.
Tactic Notation "field" ":" ne_constr_list(L) := elpi field ltac_term_list:(L).
