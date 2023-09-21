From elpi Require Import elpi.
From Coq Require Import QArith.
From Coq.micromega Require Import OrderedRing RingMicromega.
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint.
From mathcomp.zify Require Import ssrZ zify.

Import Order.TTheory GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

Implicit Types (V : nmodType) (R : semiRingType) (F : fieldType).

(* Some basic facts about `Decimal.uint` and `Hexadecimal.uint`               *)

Fixpoint N_of_uint_acc (d : Decimal.uint) (acc : N) : N :=
  match d with
  | Decimal.Nil => acc
  | Decimal.D0 d => N_of_uint_acc d (acc * 10)
  | Decimal.D1 d => N_of_uint_acc d (acc * 10 + 1)
  | Decimal.D2 d => N_of_uint_acc d (acc * 10 + 2)
  | Decimal.D3 d => N_of_uint_acc d (acc * 10 + 3)
  | Decimal.D4 d => N_of_uint_acc d (acc * 10 + 4)
  | Decimal.D5 d => N_of_uint_acc d (acc * 10 + 5)
  | Decimal.D6 d => N_of_uint_acc d (acc * 10 + 6)
  | Decimal.D7 d => N_of_uint_acc d (acc * 10 + 7)
  | Decimal.D8 d => N_of_uint_acc d (acc * 10 + 8)
  | Decimal.D9 d => N_of_uint_acc d (acc * 10 + 9)
  end.

Lemma N_of_uint_accE (d : Decimal.uint) (acc : positive) :
  N.pos (Pos.of_uint_acc d acc) = N_of_uint_acc d (N.pos acc).
Proof.
by elim: d acc => // d IHd acc; rewrite IHd 1?Pos.add_comm Pos.mul_comm.
Qed.

Definition N_of_uint : Decimal.uint -> N := N_of_uint_acc ^~ 0%num.

Lemma N_of_uintE : N.of_uint =1 N_of_uint.
Proof.
rewrite /N.of_uint /Pos.of_uint /N_of_uint /=.
by elim => //= d _; rewrite N_of_uint_accE.
Qed.

Lemma uint_N_nat (d : Decimal.uint) : nat_of_N (N.of_uint d) = Nat.of_uint d.
Proof.
rewrite N_of_uintE /N_of_uint /Nat.of_uint.
have ->: 0%N = nat_of_N 0%num by [].
by elim: d 0%num => //= d IHd acc; rewrite IHd Nat.tail_mul_spec;
  congr Nat.of_uint_acc; lia.
Qed.

Fixpoint N_of_hex_uint_acc (d : Hexadecimal.uint) (acc : N) : N :=
  match d with
  | Hexadecimal.Nil => acc
  | Hexadecimal.D0 d => N_of_hex_uint_acc d (acc * 16)
  | Hexadecimal.D1 d => N_of_hex_uint_acc d (acc * 16 + 1)
  | Hexadecimal.D2 d => N_of_hex_uint_acc d (acc * 16 + 2)
  | Hexadecimal.D3 d => N_of_hex_uint_acc d (acc * 16 + 3)
  | Hexadecimal.D4 d => N_of_hex_uint_acc d (acc * 16 + 4)
  | Hexadecimal.D5 d => N_of_hex_uint_acc d (acc * 16 + 5)
  | Hexadecimal.D6 d => N_of_hex_uint_acc d (acc * 16 + 6)
  | Hexadecimal.D7 d => N_of_hex_uint_acc d (acc * 16 + 7)
  | Hexadecimal.D8 d => N_of_hex_uint_acc d (acc * 16 + 8)
  | Hexadecimal.D9 d => N_of_hex_uint_acc d (acc * 16 + 9)
  | Hexadecimal.Da d => N_of_hex_uint_acc d (acc * 16 + 10)
  | Hexadecimal.Db d => N_of_hex_uint_acc d (acc * 16 + 11)
  | Hexadecimal.Dc d => N_of_hex_uint_acc d (acc * 16 + 12)
  | Hexadecimal.Dd d => N_of_hex_uint_acc d (acc * 16 + 13)
  | Hexadecimal.De d => N_of_hex_uint_acc d (acc * 16 + 14)
  | Hexadecimal.Df d => N_of_hex_uint_acc d (acc * 16 + 15)
  end.

Lemma N_of_hex_uint_accE (d : Hexadecimal.uint) (acc : positive) :
  N.pos (Pos.of_hex_uint_acc d acc) = N_of_hex_uint_acc d (N.pos acc).
Proof.
by elim: d acc => // d IHd acc; rewrite IHd 1?Pos.add_comm Pos.mul_comm.
Qed.

Definition N_of_hex_uint : Hexadecimal.uint -> N := N_of_hex_uint_acc ^~ 0%num.

Lemma N_of_hex_uintE : N.of_hex_uint =1 N_of_hex_uint.
Proof.
rewrite /N.of_hex_uint /Pos.of_hex_uint /N_of_hex_uint /=.
by elim => //= d _; rewrite N_of_hex_uint_accE.
Qed.

Lemma hex_uint_N_nat (d : Hexadecimal.uint) :
  nat_of_N (N.of_hex_uint d) = Nat.of_hex_uint d.
Proof.
rewrite N_of_hex_uintE /N_of_hex_uint /Nat.of_hex_uint.
have ->: 0%N = nat_of_N 0%num by [].
by elim: d 0%num => //= d IHd acc; rewrite IHd Nat.tail_mul_spec;
  congr Nat.of_hex_uint_acc; lia.
Qed.

(* In reified syntax trees, constants must be represented by binary integers  *)
(* `N` and `Z`. For the fine-grained control of conversion, we provide        *)
(* immediately expanding versions of `N -> nat`, `Z -> int`, and `N -> Z`     *)
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

Lemma nat_of_N_expandE : nat_of_N_expand = nat_of_N. Proof. by []. Qed.

(* For representing input terms of the form `S (... (S n) ...)`               *)

Fixpoint add_pos_nat (p : positive) (n : nat) : nat :=
  match p with
  | p0~1 => S (add_pos_nat p0 (add_pos_nat p0 n))
  | p0~0 => add_pos_nat p0 (add_pos_nat p0 n)
  | 1 => S n
  end%positive.

Lemma add_pos_natE p n : add_pos_nat p n = Pos.to_nat p + n.
Proof. elim: p n => //= p IHp n; rewrite !IHp; lia. Qed.

(* Data types for reifying `nat` and `int` constants, including large ones    *)
(* that uses `Number.uint`                                                    *)

Variant large_nat := large_nat_N of N | large_nat_uint of Number.uint.

Definition nat_of_large_nat (n : large_nat) : nat :=
  match n with
  | large_nat_N n => nat_of_N_expand n
  | large_nat_uint n => Nat.of_num_uint n
  end.

Definition N_of_large_nat (n : large_nat) : N :=
  match n with
  | large_nat_N n => n
  | large_nat_uint n => N.of_num_uint n
  end.

Lemma large_nat_N_nat (n : large_nat) :
  nat_of_N (N_of_large_nat n) = nat_of_large_nat n.
Proof.
case: n => [n|[d|d]] /=; first by rewrite nat_of_N_expandE; lia.
  by rewrite uint_N_nat.
by rewrite hex_uint_N_nat.
Qed.

Definition Z_of_large_nat (n : large_nat) : Z :=
  match n with
  | large_nat_N n => Z.of_N n
  | large_nat_uint n => Z.of_num_uint n
  end.

Lemma large_nat_Z_int (n : large_nat) :
  int_of_Z (Z_of_large_nat n) = nat_of_large_nat n.
Proof.
rewrite -large_nat_N_nat; case: n => [n|[d|d]] //=; first lia.
  by rewrite /Z.of_uint /N.of_uint; lia.
by rewrite /Z.of_hex_uint /N.of_hex_uint; lia.
Qed.

Definition quote_icstr_helper (n : int) : bool * N :=
  match n with
  | Posz n => (true, N.of_nat n)
  | Negz n => (false, N.of_nat n)
  end.

(* TODO: remove natn below when we drop support for MathComp 2.0 *)
Lemma natn n : n%:R%R = n :> nat.
Proof. by elim: n => // n; rewrite mulrS => ->. Qed.

(* Type for reified expressions                                               *)

Inductive RExpr : semiRingType -> Type :=
  (* 0 *)
  | R0 R : RExpr R
  (* addition *)
  | RAdd R : RExpr R -> RExpr R -> RExpr R
  | RnatAdd : RExpr nat -> RExpr nat -> RExpr nat
  | RNAdd : RExpr N -> RExpr N -> RExpr N
  | RZAdd : RExpr Z -> RExpr Z -> RExpr Z
  (* natmul *)
  | RMuln R : RExpr R -> RExpr nat -> RExpr R
  (* opposite and subtraction *)
  | ROpp (R : ringType) : RExpr R -> RExpr R
  | RZOpp : RExpr Z -> RExpr Z
  | RZSub : RExpr Z -> RExpr Z -> RExpr Z
  (* intmul *)
  | RMulz (R : ringType) : RExpr R -> RExpr int -> RExpr R
  (* 1 *)
  | R1 R : RExpr R
  (* multiplication *)
  | RMul R : RExpr R -> RExpr R -> RExpr R
  | RnatMul : RExpr nat -> RExpr nat -> RExpr nat
  | RNMul : RExpr N -> RExpr N -> RExpr N
  | RZMul : RExpr Z -> RExpr Z -> RExpr Z
  (* exponentiation *)
  | RExpn R : RExpr R -> large_nat -> RExpr R
  | RExpPosz (R : unitRingType) : RExpr R -> large_nat -> RExpr R
  | RExpNegz F : RExpr F -> large_nat -> RExpr F
  | RnatExpn : RExpr nat -> large_nat -> RExpr nat
  | RNExp : RExpr N -> N -> RExpr N
  | RZExp : RExpr Z -> Z -> RExpr Z
  (* multiplicative inverse *)
  | RInv F : RExpr F -> RExpr F
  (* constants *)
  | RnatS : positive -> RExpr nat -> RExpr nat
  | RnatC : large_nat -> RExpr nat
  | RPosz : RExpr nat -> RExpr int
  | RNegz : RExpr nat -> RExpr int
  | RNC : N -> RExpr N
  | RZC : Z -> RExpr Z
  (* homomorphism applications *)
  | RMorph R' R : {rmorphism R' -> R} -> RExpr R' -> RExpr R
  | RnatMorph R : {rmorphism nat -> R} -> RExpr nat -> RExpr R
  | RNMorph R : {rmorphism N -> R} -> RExpr N -> RExpr R
  | RintMorph R : {rmorphism int -> R} -> RExpr int -> RExpr R
  | RZMorph R : {rmorphism Z -> R} -> RExpr Z -> RExpr R
  | RAdditive V R : {additive V -> R} -> MExpr V -> RExpr R
  | RnatAdditive R : {additive nat -> R} -> RExpr nat -> RExpr R
  | RNAdditive R : {additive N -> R} -> RExpr N -> RExpr R
  | RintAdditive R : {additive int -> R} -> RExpr int -> RExpr R
  | RZAdditive R : {additive Z -> R} -> RExpr Z -> RExpr R
  (* variables *)
  | RX R : R -> RExpr R
with MExpr : nmodType -> Type :=
  | M0 V : MExpr V
  | MAdd V : MExpr V -> MExpr V -> MExpr V
  | MMuln V : MExpr V -> RExpr nat -> MExpr V
  | MOpp (V : zmodType) : MExpr V -> MExpr V
  | MMulz (V : zmodType) : MExpr V -> RExpr int -> MExpr V
  | MAdditive V' V : {additive V' -> V} -> MExpr V' -> MExpr V
  | MnatAdditive V : {additive nat -> V} -> RExpr nat -> MExpr V
  | MNAdditive V : {additive N -> V} -> RExpr N -> MExpr V
  | MintAdditive V : {additive int -> V} -> RExpr int -> MExpr V
  | MZAdditive V : {additive Z -> V} -> RExpr Z -> MExpr V
  | MX V : V -> MExpr V.

Scheme RExpr_ind' := Induction for RExpr Sort Prop
  with MExpr_ind' := Induction for MExpr Sort Prop.

(* Evaluation function for above type                                         *)
(* Evaluating result of reification should be convertible to input expr.      *)

Fixpoint Reval R (e : RExpr R) : R :=
  match e with
  | R0 _ => 0%R
  | RAdd _ e1 e2 => Reval e1 + Reval e2
  | RnatAdd e1 e2 => addn (Reval e1) (Reval e2)
  | RNAdd e1 e2 => N.add (Reval e1) (Reval e2)
  | RZAdd e1 e2 => Z.add (Reval e1) (Reval e2)
  | RMuln _ e1 e2 => Reval e1 *+ Reval e2
  | ROpp _ e1 => - Reval e1
  | RZOpp e1 => Z.opp (Reval e1)
  | RZSub e1 e2 => Z.sub (Reval e1) (Reval e2)
  | RMulz _ e1 e2 => Reval e1 *~ Reval e2
  | R1 _ => 1%R
  | RMul _ e1 e2 => Reval e1 * Reval e2
  | RnatMul e1 e2 => muln (Reval e1) (Reval e2)
  | RNMul e1 e2 => N.mul (Reval e1) (Reval e2)
  | RZMul e1 e2 => Z.mul (Reval e1) (Reval e2)
  | RExpn _ e1 n => Reval e1 ^+ nat_of_large_nat n
  | RExpPosz _ e1 n => Reval e1 ^ Posz (nat_of_large_nat n)
  | RExpNegz _ e1 n => Reval e1 ^ Negz (nat_of_large_nat n)
  | RnatExpn e1 n => expn (Reval e1) (nat_of_large_nat n)
  | RNExp e1 n => N.pow (Reval e1) n
  | RZExp e1 n => Z.pow (Reval e1) n
  | RInv _ e1 => (Reval e1)^-1
  | RnatS p e => add_pos_nat p (Reval e)
  | RnatC n => nat_of_large_nat n
  | RPosz e1 => Posz (Reval e1)
  | RNegz e2 => Negz (Reval e2)
  | RMorph _ _ f e1
  | RnatMorph _ f e1 | RNMorph _ f e1
  | RintMorph _ f e1 | RZMorph _ f e1
  | RnatAdditive _ f e1 | RNAdditive _ f e1
  | RintAdditive _ f e1 | RZAdditive _ f e1 => f (Reval e1)
  | RAdditive _ _ f e1 => f (Meval e1)
  | RNC n | RZC n => n
  | RX _ x => x
  end
with Meval V (e : MExpr V) : V :=
  match e with
  | M0 _ => 0%R
  | MAdd _ e1 e2 => Meval e1 + Meval e2
  | MMuln _ e1 e2 => Meval e1 *+ Reval e2
  | MOpp _ e1 => - Meval e1
  | MMulz _ e1 e2 => Meval e1 *~ Reval e2
  | MAdditive _ _ f e1 => f (Meval e1)
  | MnatAdditive _ f e1 | MNAdditive _ f e1
  | MintAdditive _ f e1 | MZAdditive _ f e1 => f (Reval e1)
  | MX _ x => x
  end.

(* Pushing down morphisms in ring and field expressions by reflection         *)
(* First for semirings, then for rings and finally for fields                 *)

Module SemiRing.

Section norm.

Variables (R' : semiRingType) (R_of_N : N -> R').
Variables (zero : R') (add : R' -> R' -> R').
Variables (one : R') (mul : R' -> R' -> R') (exp : R' -> N -> R').

Fixpoint Rnorm R (f : R -> R') (e : RExpr R) : R' :=
  match e in RExpr R return (R -> R') -> R' with
  | R0 _ => fun => zero
  | RAdd _ e1 e2 | RnatAdd e1 e2 | RNAdd e1 e2 =>
      fun f => add (Rnorm f e1) (Rnorm f e2)
  | RMuln _ e1 e2 => fun f => mul (Rnorm f e1) (Rnorm (GRing.natmul 1) e2)
  | R1 _ => fun => one
  | RMul _ e1 e2 | RnatMul e1 e2 | RNMul e1 e2 =>
      fun f => mul (Rnorm f e1) (Rnorm f e2)
  | RExpn _ e1 n | RnatExpn e1 n =>
      fun f => exp (Rnorm f e1) (N_of_large_nat n)
  | RExpPosz _ e1 n => fun f => exp (Rnorm f e1) (N_of_large_nat n)
  | RNExp e1 n => fun f => exp (Rnorm f e1) n
  | RnatS p e => fun f => add (R_of_N (Npos p)) (Rnorm f e)
  | RnatC n => fun => R_of_N (N_of_large_nat n)
  | RNC n => fun => R_of_N n
  | RMorph _ _ g e1 => fun f => Rnorm (fun x => f (g x)) e1
  | RnatMorph _ _ e1 => fun => Rnorm (GRing.natmul 1) e1
  | RNMorph _ _ e1 => fun => Rnorm (fun n => (N.to_nat n)%:R) e1
  | RAdditive _ _ g e1 => fun f => Mnorm (fun x => f (g x)) e1
  | RnatAdditive _ g e1 => fun f => mul (f (g 1%N)) (Rnorm (GRing.natmul 1) e1)
  | RNAdditive _ g e1 => fun f =>
      mul (f (g 1%num)) (Rnorm (fun n => (N.to_nat n)%:R) e1)
  | RX _ x => fun f => f x
  | _ => fun => f (Reval e)
  end f
with Mnorm V (f : V -> R') (e : MExpr V) : R' :=
  match e in MExpr V return (V -> R') -> R' with
  | M0 _ => fun => zero
  | MAdd _ e1 e2 => fun f => add (Mnorm f e1) (Mnorm f e2)
  | MMuln _ e1 e2 => fun f => mul (Mnorm f e1) (Rnorm (GRing.natmul 1) e2)
  | MAdditive _ _ g e1 => fun f => Mnorm (fun x => f (g x)) e1
  | MnatAdditive _ g e1 => fun f => mul (f (g 1%N)) (Rnorm (GRing.natmul 1) e1)
  | MNAdditive _ g e1 => fun f =>
      mul (f (g 1%num)) (Rnorm (fun n => (N.to_nat n)%:R) e1)
  | MX _ x => fun f => f x
  | _ => fun => f (Meval e)
  end f.

Lemma eq_Rnorm R (f f' : R -> R') (e : RExpr R) :
  f =1 f' -> Rnorm f e = Rnorm f' e.
Proof.
pose P R e := forall (f f' : R -> R'), f =1 f' -> Rnorm f e = Rnorm f' e.
pose P0 V e := forall (f f' : V -> R'), f =1 f' -> Mnorm f e = Mnorm f' e.
move: f f'; elim e using (@RExpr_ind' P P0); rewrite {R e}/P {}/P0 //=.
- by move=> R e1 IHe1 e2 IHe2 f f' feq; rewrite (IHe1 _ _ feq) (IHe2 _ _ feq).
- by move=> e1 IHe1 e2 IHe2 f f' feq; rewrite (IHe1 _ _ feq) (IHe2 _ _ feq).
- by move=> e1 IHe1 e2 IHe2 f f' feq; rewrite (IHe1 _ _ feq) (IHe2 _ _ feq).
- by move=> R e1 IHe1 e2 _ f f' feq; rewrite (IHe1 _ _ feq).
- by move=> R e1 IHe1 e2 IHe2 f f' feq; rewrite (IHe1 _ _ feq) (IHe2 _ _ feq).
- by move=> e1 IHe1 e2 IHe2 f f' feq; rewrite (IHe1 _ _ feq) (IHe2 _ _ feq).
- by move=> e1 IHe1 e2 IHe2 f f' feq; rewrite (IHe1 _ _ feq) (IHe2 _ _ feq).
- by move=> R e1 IHe1 n f f' feq; rewrite (IHe1 _ _ feq).
- by move=> R e1 IHe1 n f f' feq; rewrite (IHe1 _ _ feq).
- by move=> e1 IHe1 n f f' feq; rewrite (IHe1 _ _ feq).
- by move=> e1 IHe1 n f f' feq; rewrite (IHe1 _ _ feq).
- by move=> p e1 IHe1 f f' feq; rewrite (IHe1 _ _ feq).
- by move=> S R g e1 IHe1 f f' feq; apply: IHe1 => x; apply: feq.
- by move=> V R g e1 IHe1 f f' feq; apply: IHe1 => x; apply: feq.
- by move=> R g e1 _ f f' ->.
- by move=> R g e1 _ f f' ->.
- by move=> V e1 IHe1 e2 IHe2 f f' feq; rewrite (IHe1 _ _ feq) (IHe2 _ _ feq).
- by move=> V e1 IHe1 e2 _ f f' feq; rewrite (IHe1 _ _ feq).
- by move=> U V g e1 IHe1 f f' feq; apply: IHe1 => x; apply: feq.
- by move=> V g e1 _ f f' ->.
- by move=> V g e1 _ f f' ->.
Qed.

End norm.

Section correct.

Variables (R' : semiRingType).

Notation Rnorm :=
  (Rnorm (fun n => (nat_of_N n)%:R) 0 +%R 1 *%R (fun x n => x ^+ N.to_nat n)).
Notation Mnorm :=
  (Mnorm (fun n => (nat_of_N n)%:R) 0 +%R 1 *%R (fun x n => x ^+ N.to_nat n)).

Lemma Rnorm_correct_rec R (f : {rmorphism R -> R'}) (e : RExpr R) :
  f (Reval e) = Rnorm f e.
Proof.
pose P R e := forall (f : {rmorphism R -> R'}), f (Reval e) = Rnorm f e.
pose P0 V e := forall (f : {additive V -> R'}), f (Meval e) = Mnorm f e.
move: f; elim e using (@RExpr_ind' P P0); rewrite {R e}/P {}/P0 //=.
- by move=> R f; rewrite rmorph0.
- by move=> R e1 IHe1 e2 IHe2 f; rewrite rmorphD IHe1 IHe2.
- by move=> e1 IHe1 e2 IHe2 f; rewrite rmorphD IHe1 IHe2.
- by move=> e1 IHe1 e2 IHe2 f; rewrite rmorphD IHe1 IHe2.
- by move=> R e1 IHe1 e2 IHe2 f; rewrite rmorphMn -mulr_natr IHe1 IHe2.
- by move=> R f; rewrite rmorph1.
- by move=> R e1 IHe1 e2 IHe2 f; rewrite rmorphM IHe1 IHe2.
- by move=> e1 IHe1 e2 IHe2 f; rewrite rmorphM IHe1 IHe2.
- by move=> e1 IHe1 e2 IHe2 f; rewrite rmorphM IHe1 IHe2.
- by move=> R e1 IHe1 n f; rewrite rmorphXn IHe1 -large_nat_N_nat.
- by move=> R e1 IHe1 n f; rewrite rmorphXn IHe1 -large_nat_N_nat.
- by move=> e1 IHe1 n f; rewrite rmorphXn IHe1 -large_nat_N_nat.
- move=> e1 IHe1 n f.
  have ->: (Reval e1 ^ n)%num = Reval e1 ^+ N.to_nat n by lia.
  by rewrite rmorphXn IHe1.
- move=> p e1 IHe1 f.
  by rewrite add_pos_natE rmorphD IHe1 -[Pos.to_nat p]natn rmorph_nat.
- by move=> n f; rewrite -[nat_of_large_nat _]natn rmorph_nat -large_nat_N_nat.
- by move=> n f; rewrite -[RHS](rmorph_nat f); congr (f _); lia.
- by move=> R S g e1 IHe1 f; rewrite -/(comp f g _) IHe1.
- move=> R g e1 IHe1 f; rewrite -/(comp f g _) IHe1; apply: eq_Rnorm => /= n.
  by rewrite -[RHS](rmorph_nat (f \o g)) natn.
- move=> R g e1 IHe1 f; rewrite -/(comp f g _) IHe1; apply: eq_Rnorm => /= n.
  by rewrite -[RHS](rmorph_nat (f \o g)); congr (f (g _)); lia.
- by move=> V R g e1 IHe1 f; rewrite -/(comp f g _) IHe1.
- by move=> R g e1 IHe1 f; rewrite -[Reval e1]natn !raddfMn -mulr_natr IHe1.
- move=> R g e1 IHe1 f.
  have ->: Reval e1 = (N.to_nat (Reval e1))%:R by lia.
  by rewrite !raddfMn -mulr_natr -/(comp _ N.to_nat _) IHe1.
- by move=> V f; rewrite raddf0.
- by move=> V e1 IHe1 e2 IHe2 f; rewrite raddfD IHe1 IHe2.
- by move=> V e1 IHe1 e2 IHe2 f; rewrite raddfMn -mulr_natr IHe1 IHe2.
- by move=> V V' g e1 IHe1 f; rewrite -/(comp f g _) IHe1.
- by move=> V g e1 IHe1 f; rewrite -[Reval e1]natn !raddfMn -mulr_natr IHe1.
- move=> v g e1 IHe1 f.
  have ->: Reval e1 = (N.to_nat (Reval e1))%:R by lia.
  by rewrite !raddfMn -mulr_natr -/(comp _ N.to_nat _) IHe1.
Qed.

Lemma Rnorm_correct (e : RExpr R') : Reval e = Rnorm id e.
Proof. exact: Rnorm_correct_rec idfun _. Qed.

End correct.

End SemiRing.

Module Ring.

Section norm.

Variables (R' : ringType) (R_of_Z : Z -> R').
Variables (zero : R') (add : R' -> R' -> R').
Variables (opp : R' -> R') (sub : R' -> R' -> R').
Variables (one : R') (mul : R' -> R' -> R') (exp : R' -> N -> R').

Fixpoint Rnorm R (f : R -> R') (e : RExpr R) : R' :=
  match e in RExpr R return (R -> R') -> R' with
  | R0 _ => fun => zero
  | RAdd _ e1 e2 | RnatAdd e1 e2 | RNAdd e1 e2 | RZAdd e1 e2 =>
      fun f => add (Rnorm f e1) (Rnorm f e2)
  | RMuln _ e1 e2 => fun f => mul (Rnorm f e1) (Rnorm (GRing.natmul 1) e2)
  | ROpp _ e1 | RZOpp e1 => fun f => opp (Rnorm f e1)
  | RZSub e1 e2 => fun f => sub (Rnorm f e1) (Rnorm f e2)
  | RMulz _ e1 e2 => fun f => mul (Rnorm f e1) (Rnorm intr e2)
  | R1 _ => fun => one
  | RMul _ e1 e2 | RnatMul e1 e2 | RNMul e1 e2 | RZMul e1 e2 =>
      fun f => mul (Rnorm f e1) (Rnorm f e2)
  | RExpn _ e1 n | RnatExpn e1 n =>
      fun f => exp (Rnorm f e1) (N_of_large_nat n)
  | RExpPosz _ e1 n => fun f => exp (Rnorm f e1) (N_of_large_nat n)
  | RNExp e1 n => fun f => exp (Rnorm f e1) n
  | RZExp e1 (Z.neg _) => fun f => zero
  | RZExp e1 n => fun f => exp (Rnorm f e1) (Z.to_N n)
  | RnatS p e => fun f => add (R_of_Z (Zpos p)) (Rnorm f e)
  | RnatC n => fun => R_of_Z (Z_of_large_nat n)
  | RPosz e1 => fun => Rnorm (GRing.natmul 1) e1
  | RNegz e1 => fun => opp (add one (Rnorm (GRing.natmul 1) e1))
  | RNC n => fun => R_of_Z (Z_of_N n)
  | RZC n => fun => R_of_Z n
  | RMorph _ _ g e1 => fun f => Rnorm (fun x => f (g x)) e1
  | RnatMorph _ _ e1 => fun => Rnorm (GRing.natmul 1) e1
  | RNMorph _ _ e1 => fun => Rnorm (fun n => (N.to_nat n)%:R) e1
  | RintMorph _ _ e1 => fun => Rnorm intr e1
  | RZMorph _ _ e1 => fun => Rnorm (fun n => (int_of_Z n)%:~R) e1
  | RAdditive _ _ g e1 => fun f => Mnorm (fun x => f (g x)) e1
  | RnatAdditive _ g e1 => fun f => mul (f (g 1%N)) (Rnorm (GRing.natmul 1) e1)
  | RNAdditive _ g e1 => fun f =>
      mul (f (g 1%num)) (Rnorm (fun n => (N.to_nat n)%:R) e1)
  | RintAdditive _ g e1 => fun f => mul (f (g 1%Z)) (Rnorm intr e1)
  | RZAdditive _ g e1 => fun f =>
      mul (f (g (Zpos 1))) (Rnorm (fun n => (int_of_Z n)%:~R) e1)
  | RX _ x => fun f => f x
  | _ => fun => f (Reval e)
  end f
with Mnorm V (f : V -> R') (e : MExpr V) : R' :=
  match e in MExpr V return (V -> R') -> R' with
  | M0 _ => fun => zero
  | MAdd _ e1 e2 => fun f => add (Mnorm f e1) (Mnorm f e2)
  | MMuln _ e1 e2 => fun f => mul (Mnorm f e1) (Rnorm (GRing.natmul 1) e2)
  | MOpp _ e1 => fun f => opp (Mnorm f e1)
  | MMulz _ e1 e2 => fun f => mul (Mnorm f e1) (Rnorm intr e2)
  | MAdditive _ _ g e1 => fun f => Mnorm (fun x => f (g x)) e1
  | MnatAdditive _ g e1 => fun f => mul (f (g 1%N)) (Rnorm (GRing.natmul 1) e1)
  | MNAdditive _ g e1 => fun f =>
      mul (f (g 1%num)) (Rnorm (fun n => (N.to_nat n)%:R) e1)
  | MintAdditive _ g e1 => fun f => mul (f (g 1%Z)) (Rnorm intr e1)
  | MZAdditive _ g e1 => fun f =>
      mul (f (g (Zpos 1))) (Rnorm (fun n => (int_of_Z n)%:~R) e1)
  | MX _ x => fun f => f x
  end f.

Lemma eq_Rnorm R (f f' : R -> R') (e : RExpr R) :
  f =1 f' -> Rnorm f e = Rnorm f' e.
Proof.
pose P R e := forall (f f' : R -> R'), f =1 f' -> Rnorm f e = Rnorm f' e.
pose P0 V e := forall (f f' : V -> R'), f =1 f' -> Mnorm f e = Mnorm f' e.
move: f f'; elim e using (@RExpr_ind' P P0); rewrite {R e}/P {}/P0 //=.
- by move=> R e1 IHe1 e2 IHe2 f f' feq; rewrite (IHe1 _ _ feq) (IHe2 _ _ feq).
- by move=> e1 IHe1 e2 IHe2 f f' feq; rewrite (IHe1 _ _ feq) (IHe2 _ _ feq).
- by move=> e1 IHe1 e2 IHe2 f f' feq; rewrite (IHe1 _ _ feq) (IHe2 _ _ feq).
- by move=> e1 IHe1 e2 IHe2 f f' feq; rewrite (IHe1 _ _ feq) (IHe2 _ _ feq).
- by move=> R e1 IHe1 e2 _ f f' feq; rewrite (IHe1 _ _ feq).
- by move=> R e1 IHe1 f f' feq; rewrite (IHe1 _ _ feq).
- by move=> e1 IHe1 f f' feq; rewrite (IHe1 _ _ feq).
- by move=> e1 IHe1 e2 IHe2 f f' feq; rewrite (IHe1 _ _ feq) (IHe2 _ _ feq).
- by move=> R e1 IHe1 e2 _ f f' feq; rewrite (IHe1 _ _ feq).
- by move=> R e1 IHe1 e2 IHe2 f f' feq; rewrite (IHe1 _ _ feq) (IHe2 _ _ feq).
- by move=> e1 IHe1 e2 IHe2 f f' feq; rewrite (IHe1 _ _ feq) (IHe2 _ _ feq).
- by move=> e1 IHe1 e2 IHe2 f f' feq; rewrite (IHe1 _ _ feq) (IHe2 _ _ feq).
- by move=> e1 IHe1 e2 IHe2 f f' feq; rewrite (IHe1 _ _ feq) (IHe2 _ _ feq).
- by move=> R e1 IHe1 n f f' feq; rewrite (IHe1 _ _ feq).
- by move=> R e1 IHe1 n f f' feq; rewrite (IHe1 _ _ feq).
- by move=> e1 IHe1 n f f' feq; rewrite (IHe1 _ _ feq).
- by move=> e1 IHe1 n f f' feq; rewrite (IHe1 _ _ feq).
- by move=> e1 IHe1 [|p|p] f f' feq //; rewrite (IHe1 _ _ feq).
- by move=> p e1 IHe1 f f' feq; rewrite (IHe1 _ _ feq).
- by move=> S R g e1 IHe1 f f' feq; apply: IHe1 => x; apply: feq.
- by move=> V R g e1 IHe1 f f' feq; apply: IHe1 => x; apply: feq.
- by move=> R g e1 _ f f' ->.
- by move=> R g e1 _ f f' ->.
- by move=> R g e1 _ f f' ->.
- by move=> R g e1 _ f f' ->.
- by move=> V e1 IHe1 e2 IHe2 f f' feq; rewrite (IHe1 _ _ feq) (IHe2 _ _ feq).
- by move=> V e1 IHe1 e2 _ f f' feq; rewrite (IHe1 _ _ feq).
- by move=> V e1 IHe1 f f' feq; rewrite (IHe1 _ _ feq).
- by move=> V e1 IHe1 e2 _ f f' feq; rewrite (IHe1 _ _ feq).
- by move=> U V g e1 IHe1 f f' feq; apply: IHe1 => x; apply: feq.
- by move=> V g e1 _ f f' ->.
- by move=> V g e1 _ f f' ->.
- by move=> V g e1 _ f f' ->.
- by move=> V g e1 _ f f' ->.
Qed.

End norm.

Section correct.

Variables (R' : ringType).

Notation Rnorm :=
  (Rnorm (fun n : Z => (int_of_Z n)%:~R) 0 +%R -%R (fun x y => x - y)
     1 *%R (fun x n => x ^+ N.to_nat n)).
Notation Mnorm :=
  (Mnorm (fun n : Z => (int_of_Z n)%:~R) 0 +%R -%R (fun x y => x - y)
     1 *%R (fun x n => x ^+ N.to_nat n)).

Lemma Rnorm_correct_rec R (f : {rmorphism R -> R'}) (e : RExpr R) :
  f (Reval e) = Rnorm f e.
Proof.
pose P R e := forall (f : {rmorphism R -> R'}), f (Reval e) = Rnorm f e.
pose P0 V e := forall (f : {additive V -> R'}), f (Meval e) = Mnorm f e.
move: f; elim e using (@RExpr_ind' P P0); rewrite {R e}/P {}/P0 //=.
- by move=> R f; rewrite rmorph0.
- by move=> R e1 IHe1 e2 IHe2 f; rewrite rmorphD IHe1 IHe2.
- by move=> e1 IHe1 e2 IHe2 f; rewrite rmorphD IHe1 IHe2.
- by move=> e1 IHe1 e2 IHe2 f; rewrite rmorphD IHe1 IHe2.
- by move=> e1 IHe1 e2 IHe2 f; rewrite rmorphD IHe1 IHe2.
- by move=> R e1 IHe1 e2 IHe2 f; rewrite rmorphMn -mulr_natr IHe1 IHe2.
- by move=> R e1 IHe1 f; rewrite rmorphN IHe1.
- by move=> e1 IHe1 f; rewrite rmorphN IHe1.
- by move=> e1 IHe1 e2 IHe2 f; rewrite rmorphB IHe1 IHe2.
- by move=> R e1 IHe1 e2 IHe2 f; rewrite rmorphMz -mulrzr IHe1 IHe2.
- by move=> R f; rewrite rmorph1.
- by move=> R e1 IHe1 e2 IHe2 f; rewrite rmorphM IHe1 IHe2.
- by move=> e1 IHe1 e2 IHe2 f; rewrite rmorphM IHe1 IHe2.
- by move=> e1 IHe1 e2 IHe2 f; rewrite rmorphM IHe1 IHe2.
- by move=> e1 IHe1 e2 IHe2 f; rewrite rmorphM IHe1 IHe2.
- by move=> R e1 IHe1 n f; rewrite rmorphXn IHe1 -large_nat_N_nat.
- by move=> R e1 IHe1 n f; rewrite rmorphXn IHe1 -large_nat_N_nat.
- by move=> e1 IHe1 n f; rewrite rmorphXn IHe1 -large_nat_N_nat.
- move=> e1 IHe1 n f.
  have ->: (Reval e1 ^ n)%num = Reval e1 ^+ N.to_nat n by lia.
  by rewrite rmorphXn IHe1.
- move=> e1 IHe1 [|p|p] f; rewrite ?(rmorph0, rmorph1) //=.
  by rewrite /Rnorm -/Rnorm -IHe1 -rmorphXn /=; congr (f _); lia.
- move=> p e1 IHe1 f.
  by rewrite add_pos_natE rmorphD IHe1 -[Pos.to_nat p]natn rmorph_nat.
- move=> n f.
  by rewrite -[nat_of_large_nat _]natn rmorph_nat pmulrn -large_nat_Z_int.
- by move=> e1 IHe1 f; rewrite -[Posz _]intz rmorph_int /intmul IHe1.
- by move=> e1 IHe1 f; rewrite -[Negz _]intz rmorph_int /intmul mulrS IHe1.
- move=> n f; rewrite /Rnorm.
  have ->: int_of_Z (Z_of_N n) = nat_of_N n by lia.
  by rewrite -[RHS](rmorph_nat f); congr (f _); lia.
- by move=> n f; rewrite -[RHS](rmorph_int f); congr (f _); lia.
- by move=> R S g e1 IHe1 f; rewrite -/(comp f g _) IHe1.
- move=> R g e1 IHe1 f; rewrite -/(comp f g _) IHe1; apply: eq_Rnorm => /= n.
  by rewrite -[RHS](rmorph_nat (f \o g)) natn.
- move=> R g e1 IHe1 f; rewrite -/(comp f g _) IHe1; apply: eq_Rnorm => /= n.
  by rewrite -[RHS](rmorph_nat (f \o g)); congr (f (g _)); lia.
- move=> R g e1 IHe1 f; rewrite -/(comp f g _) IHe1; apply: eq_Rnorm => /= n.
  by rewrite -[RHS](rmorph_int (f \o g)); congr (f (g _)); lia.
- move=> R g e1 IHe1 f; rewrite -/(comp f g _) IHe1; apply: eq_Rnorm => /= n.
  by rewrite -[RHS](rmorph_int (f \o g)); congr (f (g _)); lia.
- by move=> V R g e1 IHe1 f; rewrite -/(comp f g _) IHe1.
- by move=> R g e1 IHe1 f; rewrite -[Reval e1]natn !raddfMn -mulr_natr IHe1.
- move=> R g e1 IHe1 f.
  have ->: Reval e1 = (N.to_nat (Reval e1))%:R by lia.
  by rewrite !raddfMn -mulr_natr -/(comp _ N.to_nat _) IHe1.
- move=> R g e1 IHe1 f.
  by rewrite -[Reval e1]intz [LHS](raddfMz (f \o g)) -mulrzr IHe1.
- move=> R g e1 IHe1 f.
  have ->: Reval e1 = (int_of_Z (Reval e1))%:~R by lia.
  by rewrite [LHS](raddfMz (f \o g)) -mulrzr -/(comp _ int_of_Z _) IHe1.
- by move=> V f; rewrite raddf0.
- by move=> V e1 IHe1 e2 IHe2 f; rewrite raddfD IHe1 IHe2.
- by move=> V e1 IHe1 e2 IHe2 f; rewrite raddfMn -mulr_natr IHe1 IHe2.
- by move=> V e1 IHe1 f; rewrite raddfN IHe1.
- by move=> V e1 IHe1 e2 IHe2 f; rewrite raddfMz -mulrzr IHe1 IHe2.
- by move=> V V' g e1 IHe1 f; rewrite -/(comp f g _) IHe1.
- by move=> V g e1 IHe1 f; rewrite -[Reval e1]natn !raddfMn -mulr_natr IHe1.
- move=> v g e1 IHe1 f.
  have ->: Reval e1 = (N.to_nat (Reval e1))%:R by lia.
  by rewrite !raddfMn -mulr_natr -/(comp _ N.to_nat _) IHe1.
- move=> V g e1 IHe1 f.
  by rewrite -[Reval e1]intz [LHS](raddfMz (f \o g)) -mulrzr IHe1.
- move=> V g e1 IHe1 f.
  have ->: Reval e1 = (int_of_Z (Reval e1))%:~R by lia.
  by rewrite [LHS](raddfMz (f \o g)) -mulrzr -/(comp _ int_of_Z _) IHe1.
Qed.

Lemma Rnorm_correct (e : RExpr R') : Reval e = Rnorm id e.
Proof. exact: Rnorm_correct_rec idfun _. Qed.

End correct.

End Ring.

Module Field.

Section norm.

Variables (F : ringType) (F_of_Z : Z -> F).
Variables (zero : F) (add : F -> F -> F) (opp : F -> F) (sub : F -> F -> F).
Variables (one : F) (mul : F -> F -> F) (exp : F -> N -> F) (inv : F -> F).

Fixpoint Rnorm R (f : R -> F) (e : RExpr R) : F :=
  match e in RExpr R return (R -> F) -> F with
  | R0 _ => fun => zero
  | RAdd _ e1 e2 | RnatAdd e1 e2 | RNAdd e1 e2 | RZAdd e1 e2 =>
      fun f => add (Rnorm f e1) (Rnorm f e2)
  | RMuln _ e1 e2 => fun f => mul (Rnorm f e1) (Rnorm (GRing.natmul 1) e2)
  | ROpp _ e1 | RZOpp e1 => fun f => opp (Rnorm f e1)
  | RZSub e1 e2 => fun f => sub (Rnorm f e1) (Rnorm f e2)
  | RMulz _ e1 e2 => fun f => mul (Rnorm f e1) (Rnorm intr e2)
  | R1 _ => fun => one
  | RMul _ e1 e2 | RnatMul e1 e2 | RNMul e1 e2 | RZMul e1 e2  =>
      fun f => mul (Rnorm f e1) (Rnorm f e2)
  | RExpn _ e1 n | RnatExpn e1 n => fun f => exp (Rnorm f e1) (N_of_large_nat n)
  | RExpPosz _ e1 n => fun f => exp (Rnorm f e1) (N_of_large_nat n)
  | RExpNegz _ e1 n =>
      fun f => inv (exp (Rnorm f e1) (N.succ (N_of_large_nat n)))
  | RNExp e1 n => fun f => exp (Rnorm f e1) n
  | RZExp e1 (Z.neg _) => fun f => zero
  | RZExp e1 n => fun f => exp (Rnorm f e1) (Z.to_N n)
  | RInv _ e1 => fun f => inv (Rnorm f e1)
  | RnatS p e => fun f => add (F_of_Z (Zpos p)) (Rnorm f e)
  | RnatC n => fun => F_of_Z (Z_of_large_nat n)
  | RPosz e1 => fun => Rnorm (GRing.natmul 1) e1
  | RNegz e1 => fun => opp (add one (Rnorm (GRing.natmul 1) e1))
  | RNC n => fun => F_of_Z (Z_of_N n)
  | RZC n => fun => F_of_Z n
  | RMorph _ _ g e1 => fun f => Rnorm (fun x => f (g x)) e1
  | RnatMorph _ _ e1 => fun => Rnorm (GRing.natmul 1) e1
  | RNMorph _ _ e1 => fun => Rnorm (fun n => (N.to_nat n)%:R) e1
  | RintMorph _ _ e1 => fun => Rnorm intr e1
  | RZMorph _ _ e1 => fun => Rnorm (fun n => (int_of_Z n)%:~R) e1
  | RAdditive _ _ g e1 => fun f => Mnorm (fun x => f (g x)) e1
  | RnatAdditive _ g e1 => fun f => mul (f (g 1%N)) (Rnorm (GRing.natmul 1) e1)
  | RNAdditive _ g e1 => fun f =>
      mul (f (g 1%num)) (Rnorm (fun n => (N.to_nat n)%:R) e1)
  | RintAdditive _ g e1 => fun f => mul (f (g 1%Z)) (Rnorm intr e1)
  | RZAdditive _ g e1 => fun f =>
      mul (f (g (Zpos 1))) (Rnorm (fun n => (int_of_Z n)%:~R) e1)
  | RX _ x => fun f => f x
  end f
with Mnorm V (f : V -> F) (e : MExpr V) : F :=
  match e in MExpr V return (V -> F) -> F with
  | M0 _ => fun => zero
  | MAdd _ e1 e2 => fun f => add (Mnorm f e1) (Mnorm f e2)
  | MMuln _ e1 e2 => fun f => mul (Mnorm f e1) (Rnorm (GRing.natmul 1) e2)
  | MOpp _ e1 => fun f => opp (Mnorm f e1)
  | MMulz _ e1 e2 => fun f => mul (Mnorm f e1) (Rnorm intr e2)
  | MAdditive _ _ g e1 => fun f => Mnorm (fun x => f (g x)) e1
  | MnatAdditive _ g e1 => fun f => mul (f (g 1%N)) (Rnorm (GRing.natmul 1) e1)
  | MNAdditive _ g e1 => fun f =>
      mul (f (g 1%num)) (Rnorm (fun n => (N.to_nat n)%:R) e1)
  | MintAdditive _ g e1 => fun f => mul (f (g 1%Z)) (Rnorm intr e1)
  | MZAdditive _ g e1 => fun f =>
      mul (f (g (Zpos 1))) (Rnorm (fun n => (int_of_Z n)%:~R) e1)
  | MX _ x => fun f => f x
  end f.

Lemma eq_Rnorm R (f f' : R -> F) (e : RExpr R) :
  f =1 f' -> Rnorm f e = Rnorm f' e.
Proof.
pose P R e := forall (f f' : R -> F), f =1 f' -> Rnorm f e = Rnorm f' e.
pose P0 V e := forall (f f' : V -> F), f =1 f' -> Mnorm f e = Mnorm f' e.
move: f f'; elim e using (@RExpr_ind' P P0); rewrite {R e}/P {}/P0 //=.
- by move=> R e1 IHe1 e2 IHe2 f f' feq; rewrite (IHe1 _ _ feq) (IHe2 _ _ feq).
- by move=> e1 IHe1 e2 IHe2 f f' feq; rewrite (IHe1 _ _ feq) (IHe2 _ _ feq).
- by move=> e1 IHe1 e2 IHe2 f f' feq; rewrite (IHe1 _ _ feq) (IHe2 _ _ feq).
- by move=> e1 IHe1 e2 IHe2 f f' feq; rewrite (IHe1 _ _ feq) (IHe2 _ _ feq).
- by move=> R e1 IHe1 e2 _ f f' feq; rewrite (IHe1 _ _ feq).
- by move=> R e1 IHe1 f f' feq; rewrite (IHe1 _ _ feq).
- by move=> e1 IHe1 f f' feq; rewrite (IHe1 _ _ feq).
- by move=> e1 IHe1 e2 IHe2 f f' feq; rewrite (IHe1 _ _ feq) (IHe2 _ _ feq).
- by move=> R e1 IHe1 e2 _ f f' feq; rewrite (IHe1 _ _ feq).
- by move=> R e1 IHe1 e2 IHe2 f f' feq; rewrite (IHe1 _ _ feq) (IHe2 _ _ feq).
- by move=> e1 IHe1 e2 IHe2 f f' feq; rewrite (IHe1 _ _ feq) (IHe2 _ _ feq).
- by move=> e1 IHe1 e2 IHe2 f f' feq; rewrite (IHe1 _ _ feq) (IHe2 _ _ feq).
- by move=> e1 IHe1 e2 IHe2 f f' feq; rewrite (IHe1 _ _ feq) (IHe2 _ _ feq).
- by move=> R e1 IHe1 n f f' feq; rewrite (IHe1 _ _ feq).
- by move=> R e1 IHe1 n f f' feq; rewrite (IHe1 _ _ feq).
- by move=> R e1 IHe1 n f f' feq; rewrite (IHe1 _ _ feq).
- by move=> e1 IHe1 n f f' feq; rewrite (IHe1 _ _ feq).
- by move=> e1 IHe1 n f f' feq; rewrite (IHe1 _ _ feq).
- by move=> e1 IHe1 [|p|p] f f' feq //; rewrite (IHe1 _ _ feq).
- by move=> R e1 IHe1 f f' feq; rewrite !(IHe1 _ _ feq).
- by move=> P e1 IHe1 f f' feq; rewrite (IHe1 _ _ feq).
- by move=> S R g e1 IHe1 f f' feq; apply: IHe1 => x; apply: feq.
- by move=> V R g e1 IHe1 f f' feq; apply: IHe1 => x; apply: feq.
- by move=> R g e1 _ f f' ->.
- by move=> R g e1 _ f f' ->.
- by move=> R g e1 _ f f' ->.
- by move=> R g e1 _ f f' ->.
- by move=> V e1 IHe1 e2 IHe2 f f' feq; rewrite (IHe1 _ _ feq) (IHe2 _ _ feq).
- by move=> V e1 IHe1 e2 _ f f' feq; rewrite (IHe1 _ _ feq).
- by move=> V e1 IHe1 f f' feq; rewrite (IHe1 _ _ feq).
- by move=> V e1 IHe1 e2 _ f f' feq; rewrite (IHe1 _ _ feq).
- by move=> U V g e1 IHe1 f f' feq; apply: IHe1 => x; apply: feq.
- by move=> V g e1 _ f f' ->.
- by move=> V g e1 _ f f' ->.
- by move=> V g e1 _ f f' ->.
- by move=> V g e1 _ f f' ->.
Qed.

End norm.

Section correct.

Variables (F : fieldType).

Notation Rnorm :=
  (Rnorm (fun (n : Z) => (int_of_Z n)%:~R) 0 +%R -%R (fun x y => x - y)
     1 *%R (fun x n => x ^+ N.to_nat n) GRing.inv).
Notation Mnorm :=
  (Mnorm (fun (n : Z) => (int_of_Z n)%:~R) 0 +%R -%R (fun x y => x - y)
     1 *%R (fun x n => x ^+ N.to_nat n) GRing.inv).

Lemma Rnorm_correct_rec R (f : {rmorphism R -> F}) (e : RExpr R) :
  f (Reval e) = Rnorm f e.
Proof.
pose P R e := forall (f : {rmorphism R -> F}), f (Reval e) = Rnorm f e.
pose P0 V e := forall (f : {additive V -> F}), f (Meval e) = Mnorm f e.
move: f; elim e using (@RExpr_ind' P P0); rewrite {R e}/P {}/P0 //=.
- by move=> R f; rewrite rmorph0.
- by move=> R e1 IHe1 e2 IHe2 f; rewrite rmorphD IHe1 IHe2.
- by move=> e1 IHe1 e2 IHe2 f; rewrite rmorphD IHe1 IHe2.
- by move=> e1 IHe1 e2 IHe2 f; rewrite rmorphD IHe1 IHe2.
- by move=> e1 IHe1 e2 IHe2 f; rewrite rmorphD IHe1 IHe2.
- by move=> R e1 IHe1 e2 IHe2 f; rewrite rmorphMn -mulr_natr IHe1 IHe2.
- by move=> R e1 IHe1 f; rewrite rmorphN IHe1.
- by move=> e1 IHe1 f; rewrite rmorphN IHe1.
- by move=> e1 IHe1 e2 IHe2 f; rewrite rmorphB IHe1 IHe2.
- by move=> R e1 IHe1 e2 IHe2 f; rewrite rmorphMz -mulrzr IHe1 IHe2.
- by move=> R f; rewrite rmorph1.
- by move=> R e1 IHe1 e2 IHe2 f; rewrite rmorphM IHe1 IHe2.
- by move=> e1 IHe1 e2 IHe2 f; rewrite rmorphM IHe1 IHe2.
- by move=> e1 IHe1 e2 IHe2 f; rewrite rmorphM IHe1 IHe2.
- by move=> e1 IHe1 e2 IHe2 f; rewrite rmorphM IHe1 IHe2.
- by move=> R e1 IHe1 n f; rewrite rmorphXn IHe1 -large_nat_N_nat.
- by move=> R e1 IHe1 n f; rewrite rmorphXn IHe1 -large_nat_N_nat.
- move=> R e1 IHe1 n f; rewrite fmorphV rmorphXn IHe1 -large_nat_N_nat.
  by congr (_ ^- _); lia.
- by move=> e1 IHe1 n f; rewrite rmorphXn IHe1 -large_nat_N_nat.
- move=> e1 IHe1 n f.
  have ->: (Reval e1 ^ n)%num = Reval e1 ^+ N.to_nat n by lia.
  by rewrite rmorphXn IHe1.
- move=> e1 IHe1 [|p|p] f; rewrite ?(rmorph0, rmorph1) //=.
  by rewrite /Rnorm -/Rnorm -IHe1 -rmorphXn /=; congr (f _); lia.
- by move=> R e1 IHe1 f; rewrite fmorphV IHe1.
- move=> p e1 IHe1 f.
  by rewrite add_pos_natE rmorphD IHe1 -[Pos.to_nat p]natn rmorph_nat.
- move=> n f.
  by rewrite -[nat_of_large_nat _]natn rmorph_nat pmulrn -large_nat_Z_int.
- by move=> e1 IHe1 f; rewrite -[Posz _]intz rmorph_int /intmul IHe1.
- by move=> e1 IHe1 f; rewrite -[Negz _]intz rmorph_int /intmul mulrS IHe1.
- move=> n f; rewrite /Rnorm.
  have ->: int_of_Z (Z_of_N n) = nat_of_N n by lia.
  by rewrite -[RHS](rmorph_nat f); congr (f _); lia.
- by move=> n f; rewrite -[RHS](rmorph_int f); congr (f _); lia.
- by move=> R S g e1 IHe1 f; rewrite -/(comp f g _) IHe1.
- move=> R g e1 IHe1 f; rewrite -/(comp f g _) IHe1; apply: eq_Rnorm => /= n.
  by rewrite -[RHS](rmorph_nat (f \o g)) natn.
- move=> R g e1 IHe1 f; rewrite -/(comp f g _) IHe1; apply: eq_Rnorm => /= n.
  by rewrite -[RHS](rmorph_nat (f \o g)); congr (f (g _)); lia.
- move=> R g e1 IHe1 f; rewrite -/(comp f g _) IHe1; apply: eq_Rnorm => /= n.
  by rewrite -[RHS](rmorph_int (f \o g)); congr (f (g _)); lia.
- move=> R g e1 IHe1 f; rewrite -/(comp f g _) IHe1; apply: eq_Rnorm => /= n.
  by rewrite -[RHS](rmorph_int (f \o g)); congr (f (g _)); lia.
- by move=> V R g e1 IHe1 f; rewrite -/(comp f g _) IHe1.
- by move=> R g e1 IHe1 f; rewrite -[Reval e1]natn !raddfMn -mulr_natr IHe1.
- move=> R g e1 IHe1 f.
  have ->: Reval e1 = (N.to_nat (Reval e1))%:R by lia.
  by rewrite !raddfMn -mulr_natr -/(comp _ N.to_nat _) IHe1.
- move=> R g e1 IHe1 f.
  by rewrite -[Reval e1]intz [LHS](raddfMz (f \o g)) -mulrzr IHe1.
- move=> R g e1 IHe1 f.
  have ->: Reval e1 = (int_of_Z (Reval e1))%:~R by lia.
  by rewrite [LHS](raddfMz (f \o g)) -mulrzr -/(comp _ int_of_Z _) IHe1.
- by move=> V f; rewrite raddf0.
- by move=> V e1 IHe1 e2 IHe2 f; rewrite raddfD IHe1 IHe2.
- by move=> V e1 IHe1 e2 IHe2 f; rewrite raddfMn -mulr_natr IHe1 IHe2.
- by move=> V e1 IHe1 f; rewrite raddfN IHe1.
- by move=> V e1 IHe1 e2 IHe2 f; rewrite raddfMz -mulrzr IHe1 IHe2.
- by move=> V V' g e1 IHe1 f; rewrite -/(comp f g _) IHe1.
- by move=> V g e1 IHe1 f; rewrite -[Reval e1]natn !raddfMn -mulr_natr IHe1.
- move=> v g e1 IHe1 f.
  have ->: Reval e1 = (N.to_nat (Reval e1))%:R by lia.
  by rewrite !raddfMn -mulr_natr -/(comp _ N.to_nat _) IHe1.
- move=> V g e1 IHe1 f.
  by rewrite -[Reval e1]intz [LHS](raddfMz (f \o g)) -mulrzr IHe1.
- move=> V g e1 IHe1 f.
  have ->: Reval e1 = (int_of_Z (Reval e1))%:~R by lia.
  by rewrite [LHS](raddfMz (f \o g)) -mulrzr -/(comp _ int_of_Z _) IHe1.
Qed.

Lemma Rnorm_correct (e : RExpr F) : Reval e = Rnorm id e.
Proof. exact: Rnorm_correct_rec idfun _. Qed.

End correct.

End Field.

Module Lra.

Section norm.

Variables (F : ringType) (F_of_Z : bool -> Z -> F).
Variables (zero : F) (add : F -> F -> F) (opp : F -> F) (sub : F -> F -> F).
Variables (one : F) (mul : F -> F -> F) (exp : F -> N -> F) (inv : F -> F).

Fixpoint Rnorm invb R (f : R -> F) (e : RExpr R) : F :=
  let invr r := if invb then inv r else r in
  match e in RExpr R return (R -> F) -> F with
  | R0 _ => fun => zero
  | RAdd _ e1 e2 | RnatAdd e1 e2 | RNAdd e1 e2 | RZAdd e1 e2 => fun f =>
      invr (add (Rnorm false f e1) (Rnorm false f e2))
  | RMuln _ e1 e2 => fun f =>
      mul (Rnorm invb f e1) (Rnorm invb (GRing.natmul 1) e2)
  | ROpp _ e1 | RZOpp e1 => fun f => opp (Rnorm invb f e1)
  | RZSub e1 e2 => fun f => invr (sub (Rnorm false f e1) (Rnorm false f e2))
  | RMulz _ e1 e2 => fun f => mul (Rnorm invb f e1) (Rnorm invb intr e2)
  | R1 _ => fun => one
  | RMul _ e1 e2 | RnatMul e1 e2 | RNMul e1 e2 | RZMul e1 e2  => fun f =>
      mul (Rnorm invb f e1) (Rnorm invb f e2)
  | RExpn _ e1 n | RnatExpn e1 n => fun f =>
      exp (Rnorm invb f e1) (N_of_large_nat n)
  | RExpPosz _ e1 n => fun f => exp (Rnorm invb f e1) (N_of_large_nat n)
  | RExpNegz _ e1 n => fun f =>
      exp (Rnorm (~~ invb) f e1) (N.succ (N_of_large_nat n))
  | RNExp e1 n => fun f => exp (Rnorm invb f e1) n
  | RZExp e1 (Z.neg _) => fun f => zero
  | RZExp e1 n => fun f => exp (Rnorm invb f e1) (Z.to_N n)
  | RInv _ e1 => fun f => Rnorm (~~ invb) f e1
  | RnatS p e => fun f => invr (add (F_of_Z false (Zpos p)) (Rnorm false f e))
  | RnatC n => fun => F_of_Z invb (Z_of_large_nat n)
  | RPosz e1 => fun => Rnorm invb (GRing.natmul 1) e1
  | RNegz e1 => fun => invr (opp (add one (Rnorm false (GRing.natmul 1) e1)))
  | RNC n => fun => F_of_Z invb (Z_of_N n)
  | RZC n => fun => F_of_Z invb n
  | RMorph _ _ g e1 => fun f => Rnorm invb (fun x => f (g x)) e1
  | RnatMorph _ _ e1 => fun => Rnorm invb (GRing.natmul 1) e1
  | RNMorph _ _ e1 => fun => Rnorm invb (fun n => (N.to_nat n)%:R) e1
  | RintMorph _ _ e1 => fun => Rnorm invb intr e1
  | RZMorph _ _ e1 => fun => Rnorm invb (fun n => (int_of_Z n)%:~R) e1
  | RAdditive _ _ g e1 => fun f => Mnorm invb (fun x => f (g x)) e1
  | RnatAdditive _ g e1 => fun f =>
      mul (invr (f (g 1%N))) (Rnorm invb (GRing.natmul 1) e1)
  | RNAdditive _ g e1 => fun f =>
      mul (invr (f (g 1%num))) (Rnorm invb (fun n => (N.to_nat n)%:R) e1)
  | RintAdditive _ g e1 => fun f =>
      mul (invr (f (g 1%Z))) (Rnorm invb intr e1)
  | RZAdditive _ g e1 => fun f =>
      mul (invr (f (g (Zpos 1)))) (Rnorm invb (fun n => (int_of_Z n)%:~R) e1)
  | RX _ x => fun f => invr (f x)
  end f
with Mnorm invb V (f : V -> F) (e : MExpr V) : F :=
  let invr r := if invb then inv r else r in
  match e in MExpr V return (V -> F) -> F with
  | M0 _ => fun => zero
  | MAdd _ e1 e2 => fun f => invr (add (Mnorm false f e1) (Mnorm false f e2))
  | MMuln _ e1 e2 => fun f =>
      mul (Mnorm invb f e1) (Rnorm invb (GRing.natmul 1) e2)
  | MOpp _ e1 => fun f => opp (Mnorm invb f e1)
  | MMulz _ e1 e2 => fun f => mul (Mnorm invb f e1) (Rnorm invb intr e2)
  | MAdditive _ _ g e1 => fun f => Mnorm invb (fun x => f (g x)) e1
  | MnatAdditive _ g e1 => fun f =>
      mul (invr (f (g 1%N))) (Rnorm invb (GRing.natmul 1) e1)
  | MNAdditive _ g e1 => fun f =>
      mul (invr (f (g 1%num))) (Rnorm invb (fun n => (N.to_nat n)%:R) e1)
  | MintAdditive _ g e1 => fun f => mul (invr (f (g 1%Z))) (Rnorm invb intr e1)
  | MZAdditive _ g e1 => fun f =>
      mul (invr (f (g (Zpos 1)))) (Rnorm invb (fun n => (int_of_Z n)%:~R) e1)
  | MX _ x => fun f => invr (f x)
  end f.

Lemma eq_Rnorm invb R (f f' : R -> F) (e : RExpr R) :
  f =1 f' -> Rnorm invb f e = Rnorm invb f' e.
Proof.
pose P R e :=
  forall invb (f f' : R -> F), f =1 f' -> Rnorm invb f e = Rnorm invb f' e.
pose P0 V e :=
  forall invb (f f' : V -> F), f =1 f' -> Mnorm invb f e = Mnorm invb f' e.
move: invb f f'; elim e using (@RExpr_ind' P P0); rewrite {R e}/P {}/P0 //=.
- move=> R e1 IHe1 e2 IHe2 invb f f' feq.
  by rewrite (IHe1 _ _ _ feq) (IHe2 _ _ _ feq).
- move=> e1 IHe1 e2 IHe2 invb f f' feq.
  by rewrite (IHe1 _ _ _ feq) (IHe2 _ _ _ feq).
- move=> e1 IHe1 e2 IHe2 invb f f' feq.
  by rewrite (IHe1 _ _ _ feq) (IHe2 _ _ _ feq).
- move=> e1 IHe1 e2 IHe2 invb f f' feq.
  by rewrite (IHe1 _ _ _ feq) (IHe2 _ _ _ feq).
- by move=> R e1 IHe1 e2 _ invb f f' feq; rewrite (IHe1 _ _ _ feq).
- by move=> R e1 IHe1 invb f f' feq; rewrite (IHe1 _ _ _ feq).
- by move=> e1 IHe1 invb f f' feq; rewrite (IHe1 _ _ _ feq).
- move=> e1 IHe1 e2 IHe2 invb f f' feq.
  by rewrite (IHe1 _ _ _ feq) (IHe2 _ _ _ feq).
- by move=> R e1 IHe1 e2 _ invb f f' feq; rewrite (IHe1 _ _ _ feq).
- move=> R e1 IHe1 e2 IHe2 invb f f' feq.
  by rewrite (IHe1 _ _ _ feq) (IHe2 _ _ _ feq).
- move=> e1 IHe1 e2 IHe2 invb f f' feq.
  by rewrite (IHe1 _ _ _ feq) (IHe2 _ _ _ feq).
- move=> e1 IHe1 e2 IHe2 invb f f' feq.
  by rewrite (IHe1 _ _ _ feq) (IHe2 _ _ _ feq).
- move=> e1 IHe1 e2 IHe2 invb f f' feq.
  by rewrite (IHe1 _ _ _ feq) (IHe2 _ _ _ feq).
- by move=> R e1 IHe1 n invb f f' feq; rewrite (IHe1 _ _ _ feq).
- by move=> R e1 IHe1 n invb f f' feq; rewrite (IHe1 _ _ _ feq).
- by move=> R e1 IHe1 n invb f f' feq; rewrite (IHe1 _ _ _ feq).
- by move=> e1 IHe1 n invb f f' feq; rewrite (IHe1 _ _ _ feq).
- by move=> e1 IHe1 n invb f f' feq; rewrite (IHe1 _ _ _ feq).
- by move=> e1 IHe1 [|p|p] invb f f' feq //; rewrite (IHe1 _ _ _ feq).
- by move=> R e1 IHe1 invb f f' feq; rewrite !(IHe1 _ _ _ feq).
- by move=> P e1 IHe1 invb f f' feq; rewrite (IHe1 _ _ _ feq).
- by move=> S R g e1 IHe1 invb f f' feq; apply: IHe1 => x; apply: feq.
- by move=> V R g e1 IHe1 invb f f' feq; apply: IHe1 => x; apply: feq.
- by move=> R g e1 _ invb f f' ->.
- by move=> R g e1 _ invb f f' ->.
- by move=> R g e1 _ invb f f' ->.
- by move=> R g e1 _ invb f f' ->.
- by move=> R x invb f f' ->.
- move=> V e1 IHe1 e2 IHe2 invb f f' feq.
  by rewrite (IHe1 _ _ _ feq) (IHe2 _ _ _ feq).
- by move=> V e1 IHe1 e2 _ invb f f' feq; rewrite (IHe1 _ _ _ feq).
- by move=> V e1 IHe1 invb f f' feq; rewrite (IHe1 _ _ _ feq).
- by move=> V e1 IHe1 e2 _ invb f f' feq; rewrite (IHe1 _ _ _ feq).
- by move=> U V g e1 IHe1 invb f f' feq; apply: IHe1 => x; apply: feq.
- by move=> V g e1 _ invb f f' ->.
- by move=> V g e1 _ invb f f' ->.
- by move=> V g e1 _ invb f f' ->.
- by move=> V g e1 _ invb f f' ->.
- by move=> V x invb f f' ->.
Qed.

End norm.

Lemma Rnorm_eq invb (F : ringType) (f f' : bool -> Z -> F)
  zero add opp sub one mul exp inv : f =2 f' ->
  forall (R : semiRingType) (env : R -> F) e,
    Rnorm f zero add opp sub one mul exp inv invb env e =
    Rnorm f' zero add opp sub one mul exp inv invb env e.
Proof.
move=> ff' R m e.
pose P R e := forall f f' invb (m : R -> F), f =2 f' ->
  Rnorm f zero add opp sub one mul exp inv invb m e =
  Rnorm f' zero add opp sub one mul exp inv invb m e.
pose P0 V e := forall f f' invb (m : V -> F), f =2 f' ->
  Mnorm f zero add opp sub one mul exp inv invb m e =
  Mnorm f' zero add opp sub one mul exp inv invb m e.
move: f f' invb m ff'.
elim e using (@RExpr_ind' P P0); rewrite {R e}/P {}/P0 //=.
- move=> R e1 IHe1 e2 IHe2 f f'.
  by case=> m ff'; [congr inv|]; (congr add; [exact: IHe1|exact: IHe2]).
- move=> e1 IHe1 e2 IHe2 f f'.
  by case=> m ff'; [congr inv|]; (congr add; [exact: IHe1|exact: IHe2]).
- move=> e1 IHe1 e2 IHe2 f f'.
  by case=> m ff'; [congr inv|]; (congr add; [exact: IHe1|exact: IHe2]).
- move=> e1 IHe1 e2 IHe2 f f'.
  by case=> m ff'; [congr inv|]; (congr add; [exact: IHe1|exact: IHe2]).
- move=> R e1 IHe1 e2 IHe2 f f' invb m ff'.
  by congr mul; [exact: IHe1|exact: IHe2].
- by move=> R e1 IHe1 f f' invb m ff'; congr opp; exact: IHe1.
- by move=> e1 IHe1 f f' invb m ff'; congr opp; exact: IHe1.
- move=> e1 IHe1 e2 IHe2 f f'.
  by case=> m ff'; [congr inv|]; (congr sub; [exact: IHe1|exact: IHe2]).
- move=> R e1 IHe1 e2 IHe2 f f' invb m ff'.
  by congr mul; [exact: IHe1|exact: IHe2].
- move=> R e1 IHe1 e2 IHe2 f f' invb m ff'.
  by congr mul; [exact: IHe1|exact: IHe2].
- move=> e1 IHe1 e2 IHe2 f f' invb m ff'.
  by congr mul; [exact: IHe1|exact: IHe2].
- move=> e1 IHe1 e2 IHe2 f f' invb m ff'.
  by congr mul; [exact: IHe1|exact: IHe2].
- move=> e1 IHe1 e2 IHe2 f f' invb m ff'.
  by congr mul; [exact: IHe1|exact: IHe2].
- by move=> R e1 IHe1 n f f' invb m ff'; congr exp; exact: IHe1.
- by move=> R e1 IHe1 n f f' invb m ff'; congr exp; exact: IHe1.
- by move=> R e1 IHe1 n f f' invb m ff'; congr exp; exact: IHe1.
- by move=> e1 IHe1 n f f' invb m ff'; congr exp; exact: IHe1.
- by move=> e1 IHe1 n f f' invb m ff'; congr exp; exact: IHe1.
- by move=> e1 IHe1 [|p|//] f f' invb m ff'; congr exp; exact: IHe1.
- by move=> R e1 IHe1 f f' invb m ff'; apply: IHe1.
- move=> p e IHe f f'.
  by case=> m ff'; [congr inv|]; congr add; rewrite ?ff'//; exact: IHe.
- by move=> n f f' invb m ff'; rewrite /Rnorm ff'.
- by move=> e IHe f f' invb m ff'; exact: IHe.
- by move=> e IHe f f' [] m ff'; [congr inv|]; congr opp; congr add; exact: IHe.
- by move=> n f f' invb m ff'; rewrite /Rnorm ff'.
- by move=> n f f' invb m ff'; rewrite /Rnorm ff'.
- by move=> R' R g e IHe f f' invb m ff'; exact: IHe.
- by move=> R g e IHe f f' invb m ff'; exact: IHe.
- by move=> R g e IHe f f' invb m ff'; exact: IHe.
- by move=> R g e IHe f f' invb m ff'; exact: IHe.
- by move=> R g e IHe f f' invb m ff'; exact: IHe.
- by move=> V R g e IHe f f' invb m ff'; exact: IHe.
- by move=> R g e IHe f f' invb m ff'; congr mul; exact: IHe.
- by move=> R g e IHe f f' invb m ff'; congr mul; exact: IHe.
- by move=> R g e IHe f f' invb m ff'; congr mul; exact: IHe.
- by move=> R g e IHe f f' invb m ff'; congr mul; exact: IHe.
- move=> V e1 IHe1 e2 IHe2 f f'.
  by case=> m ff'; [congr inv|]; (congr add; [exact: IHe1|exact: IHe2]).
- move=> V e1 IHe1 e2 IHe2 f f' invb m ff'.
  by congr mul; [exact: IHe1|exact: IHe2].
- by move=> V e IHe f f' invb m ff'; congr opp; exact: IHe.
- move=> V e1 IHe1 e2 IHe2 f f' invb m ff'.
  by congr mul; [exact: IHe1|exact: IHe2].
- by move=> V V' g e IHe f f' invb m ff'; exact: IHe.
- by move=> V g e IHe f f' invb m ff'; congr mul; exact: IHe.
- by move=> V g e IHe f f' invb m ff'; congr mul; exact: IHe.
- by move=> V g e IHe f f' invb m ff'; congr mul; exact: IHe.
- by move=> V g e IHe f f' invb m ff'; congr mul; exact: IHe.
Qed.

Section correct.

Variables (F : fieldType).

Notation F_of_Z :=
  (fun b (n : Z) => if b then (int_of_Z n)%:~R^-1 else (int_of_Z n)%:~R).
Notation Rnorm :=
  (Rnorm F_of_Z 0 +%R -%R (fun x y => x - y)
     1 *%R (fun x n => x ^+ N.to_nat n) GRing.inv).
Notation Mnorm :=
  (Mnorm F_of_Z 0 +%R -%R (fun x y => x - y)
     1 *%R (fun x n => x ^+ N.to_nat n) GRing.inv).

Lemma Rnorm_correct_rec (invb : bool) R (f : {rmorphism R -> F}) (e : RExpr R) :
  (if invb then (f (Reval e))^-1 else f (Reval e)) = Rnorm invb f e.
Proof.
pose P R e := forall invb (f : {rmorphism R -> F}),
  (if invb then (f (Reval e))^-1 else f (Reval e)) = Rnorm invb f e.
pose P0 V e := forall invb (f : {additive V -> F}),
  (if invb then (f (Meval e))^-1 else f (Meval e)) = Mnorm invb f e.
move: invb f; elim e using (@RExpr_ind' P P0); rewrite {R e}/P {}/P0 //=.
- by move=> R invb f; rewrite rmorph0 invr0 if_same.
- by move=> R e1 IHe1 e2 IHe2 invb f; rewrite rmorphD (IHe1 false) (IHe2 false).
- by move=> e1 IHe1 e2 IHe2 invb f; rewrite rmorphD (IHe1 false) (IHe2 false).
- by move=> e1 IHe1 e2 IHe2 invb f; rewrite rmorphD (IHe1 false) (IHe2 false).
- by move=> e1 IHe1 e2 IHe2 invb f; rewrite rmorphD (IHe1 false) (IHe2 false).
- move=> R e1 IHe1 e2 IHe2 invb f; rewrite rmorphMn -mulr_natr invfM.
  by rewrite (IHe1 true) (IHe2 true) (IHe1 false) (IHe2 false); case: invb.
- move=> R e1 IHe1 invb f.
  by rewrite rmorphN invrN (IHe1 true) (IHe1 false); case: invb.
- move=> e1 IHe1 invb f.
  by rewrite rmorphN invrN (IHe1 true) (IHe1 false); case: invb.
- by move=> e1 IHe1 e2 IHe2 invb f; rewrite rmorphB (IHe1 false) (IHe2 false).
- move=> R e1 IHe1 e2 IHe2 invb f; rewrite rmorphMz -mulrzr invfM.
  by rewrite (IHe1 true) (IHe2 true) (IHe1 false) (IHe2 false); case: invb.
- by move=> R invb f; rewrite rmorph1 invr1 if_same.
- move=> R e1 IHe1 e2 IHe2 invb f; rewrite rmorphM invfM.
  by rewrite (IHe1 true) (IHe2 true) (IHe1 false) (IHe2 false); case: invb.
- move=> e1 IHe1 e2 IHe2 invb f; rewrite rmorphM invfM.
  by rewrite (IHe1 true) (IHe2 true) (IHe1 false) (IHe2 false); case: invb.
- move=> e1 IHe1 e2 IHe2 invb f; rewrite rmorphM invfM.
  by rewrite (IHe1 true) (IHe2 true) (IHe1 false) (IHe2 false); case: invb.
- move=> e1 IHe1 e2 IHe2 invb f; rewrite rmorphM invfM.
  by rewrite (IHe1 true) (IHe2 true) (IHe1 false) (IHe2 false); case: invb.
- move=> R e1 IHe1 n invb f; rewrite rmorphXn -exprVn (IHe1 true) (IHe1 false).
  by rewrite -large_nat_N_nat; case: invb.
- move=> R e1 IHe1 n invb f; rewrite rmorphXn -exprVn (IHe1 true) (IHe1 false).
  by rewrite -large_nat_N_nat; case: invb.
- move=> R e1 IHe1 n invb f; rewrite fmorphV rmorphXn invrK -exprVn.
  rewrite (IHe1 true) (IHe1 false) -large_nat_N_nat.
  by case: invb; congr (_ ^+ _); lia.
- move=> e1 IHe1 n invb f; rewrite rmorphXn -exprVn (IHe1 true) (IHe1 false).
  by rewrite -large_nat_N_nat; case: invb.
- move=> e1 IHe1 n invb f.
  have ->: (Reval e1 ^ n)%num = Reval e1 ^+ N.to_nat n by lia.
  by rewrite rmorphXn -exprVn (IHe1 true) (IHe1 false); case: invb.
- move=> e1 IHe1 [|p|p] invb f;
    rewrite ?(rmorph0, rmorph1, invr0, invr1, if_same) //=.
  rewrite /Rnorm /= -/(Rnorm _) -IHe1 (fun_if (fun x => GRing.exp x _)).
  by rewrite exprVn -rmorphXn; congr (if _ then (f _)^-1 else f _); lia.
- by move=> R e1 IHe1 invb f; rewrite fmorphV invrK -if_neg IHe1.
- move=> p e1 IHe1 invb f.
  by rewrite add_pos_natE rmorphD (IHe1 false) -[Pos.to_nat p]natn rmorph_nat.
- move=> n invb f.
  by rewrite -[nat_of_large_nat _]natn rmorph_nat pmulrn -large_nat_Z_int.
- move=> e1 IHe1 invb f; rewrite -[Posz _]intz rmorph_int -pmulrn.
  by rewrite (IHe1 true) (IHe1 false); case: invb.
- move=> e1 IHe1 invb f.
  by rewrite -[Negz _]intz rmorph_int /intmul mulrS (IHe1 false).
- move=> n invb f; rewrite /Rnorm.
  have ->: int_of_Z (Z_of_N n) = nat_of_N n by lia.
  rewrite -[_%:~R](rmorph_nat f).
  by case: invb; [congr (_ ^-1)|]; congr (f _); lia.
- move=> n invb f; rewrite /Rnorm -(rmorph_int f).
  by case: invb; [congr (_ ^-1)|]; congr (f _); lia.
- by move=> R S g e1 IHe1 invb f; rewrite -/(comp f g _) IHe1.
- move=> R g e1 IHe1 invb f; rewrite -/(comp f g _) IHe1.
  by apply: eq_Rnorm => /= n; rewrite -[RHS](rmorph_nat (f \o g)) natn.
- move=> R g e1 IHe1 invb f; rewrite -/(comp f g _) IHe1.
  apply: eq_Rnorm => /= n; rewrite -[RHS](rmorph_nat (f \o g)).
  by congr (f (g _)); lia.
- move=> R g e1 IHe1 invb f; rewrite -/(comp f g _) IHe1.
  apply: eq_Rnorm => /= n; rewrite -[RHS](rmorph_int (f \o g)).
  by congr (f (g _)); lia.
- move=> R g e1 IHe1 invb f; rewrite -/(comp f g _) IHe1.
  apply: eq_Rnorm => /= n; rewrite -[RHS](rmorph_int (f \o g)).
  by congr (f (g _)); lia.
- by move=> V R g e1 IHe1 invb f; rewrite -/(comp f g _) IHe1.
- move=> R g e1 IHe1 invb f.
  rewrite -[Reval e1]natn !raddfMn -mulr_natr ?invfM.
  by rewrite (IHe1 true) (IHe1 false); case: invb.
- move=> R g e1 IHe1 invb f.
  have ->: Reval e1 = (N.to_nat (Reval e1))%:R by lia.
  rewrite !raddfMn -mulr_natr -/(comp _ N.to_nat _) ?invfM.
  by rewrite (IHe1 true) (IHe1 false); case: invb.
- move=> R g e1 IHe1 invb f.
  rewrite -[Reval e1]intz ![f _](raddfMz (f \o g)) -mulrzr ?invfM.
  by rewrite (IHe1 true) (IHe1 false); case:invb.
- move=> R g e1 IHe1 invb f.
  have ->: Reval e1 = (int_of_Z (Reval e1))%:~R by lia.
  rewrite [f _](raddfMz (f \o g)) -mulrzr -/(comp _ int_of_Z _) ?invfM.
  by rewrite (IHe1 true) (IHe1 false); case:invb.
- by move=> V invb f; rewrite raddf0 invr0 if_same.
- by move=> V e1 IHe1 e2 IHe2 invb f; rewrite raddfD (IHe1 false) (IHe2 false).
- move=> V e1 IHe1 e2 IHe2 invb f; rewrite raddfMn -mulr_natr invfM.
  by rewrite (IHe1 true) (IHe2 true) (IHe1 false) (IHe2 false); case: invb.
- move=> V e1 IHe1 invb f.
  by rewrite raddfN invrN (IHe1 true) (IHe1 false); case: invb.
- move=> V e1 IHe1 e2 IHe2 invb f; rewrite raddfMz -mulrzr invfM.
  by rewrite (IHe1 true) (IHe2 true) (IHe1 false) (IHe2 false); case: invb.
- by move=> V V' g e1 IHe1 invb f; rewrite -/(comp f g _) IHe1.
- move=> V g e1 IHe1 invb f; rewrite -[Reval e1]natn !raddfMn -mulr_natr invfM.
  by rewrite (IHe1 true) (IHe1 false); case: invb.
- move=> V g e1 IHe1 invb f.
  have ->: Reval e1 = (N.to_nat (Reval e1))%:R by lia.
  rewrite !raddfMn -mulr_natr invfM -/(comp _ N.to_nat _).
  by rewrite (IHe1 true) (IHe1 false); case: invb.
- move=> V g e1 IHe1 invb f.
  rewrite -[Reval e1]intz ![f _](raddfMz (f \o g)) -mulrzr invfM.
  by rewrite (IHe1 true) (IHe1 false); case: invb.
- move=> V g e1 IHe1 invb f.
  have ->: Reval e1 = (int_of_Z (Reval e1))%:~R by lia.
  rewrite [f _](raddfMz (f \o g)) -mulrzr -/(comp _ int_of_Z _) invfM.
  by rewrite (IHe1 true) (IHe1 false); case: invb.
Qed.

Lemma Rnorm_correct (e : RExpr F) : Reval e = Rnorm false id e.
Proof. by rewrite -(Rnorm_correct_rec _ idfun). Qed.

End correct.

End Lra.

(* Embedding of rational numbers `Q` in a generic `unitRingType`              *)

Definition R_of_Q {R : unitRingType} (x : Q) : R :=
  (int_of_Z (Qnum x))%:~R / (Pos.to_nat (Qden x))%:R.

Lemma R_of_Q0 (R : unitRingType) : R_of_Q 0 = 0 :> R.
Proof. by rewrite /R_of_Q mul0r. Qed.

Lemma R_of_Q1 (R : unitRingType) : R_of_Q 1 = 1 :> R.
Proof. by rewrite /R_of_Q divr1. Qed.

Lemma R_of_Q_add (F : numFieldType) x y :
  R_of_Q (x + y) = R_of_Q x + R_of_Q y :> F.
Proof.
rewrite /R_of_Q /= addf_div ?pnatr_eq0; try lia.
by rewrite !pmulrn -!intrM -!intrD; congr (_%:~R / _%:~R); lia.
Qed.

Lemma R_of_Q_opp (R : unitRingType) x : R_of_Q (- x) = - R_of_Q x :> R.
Proof. by rewrite /R_of_Q !rmorphN mulNr. Qed.

Lemma R_of_Q_sub (F : numFieldType) x y :
  R_of_Q (x - y) = R_of_Q x - R_of_Q y :> F.
Proof. by rewrite R_of_Q_add R_of_Q_opp. Qed.

Lemma R_of_Q_mul (F : fieldType) x y :
  R_of_Q (x * y) = R_of_Q x * R_of_Q y :> F.
Proof.
by rewrite /R_of_Q /= mulrACA -invfM -intrM -natrM; congr (_%:~R / _%:R); lia.
Qed.

(* Some instances required to adapt `ring`, `field`, and `lra` tactics to     *)
(* MathComp                                                                   *)

Lemma RN (SR : semiRingType) : semi_morph (0 : SR) 1 +%R *%R eq
                N.zero N.one N.add N.mul N.eqb (fun n => (nat_of_N n)%:R).
Proof.
split=> //= [x y | x y | x y].
- by rewrite -natrD; congr _%:R; lia.
- by rewrite -natrM; congr _%:R; lia.
- by move=> ?; congr _%:R; lia.
Qed.

Lemma RZ (R : ringType) : ring_morph 0 1 +%R *%R (fun x y : R => x - y) -%R eq
               0 1 Z.add Z.mul Z.sub Z.opp Z.eqb (fun n => (int_of_Z n)%:~R).
Proof.
split=> //= [x y | x y | x y | x | x y /Z.eqb_eq -> //].
- by rewrite !rmorphD.
- by rewrite !rmorphB.
- by rewrite !rmorphM.
- by rewrite !rmorphN.
Qed.

Lemma PN (SR : semiRingType) : @power_theory SR 1 *%R eq
                                 N id (fun x n => x ^+ nat_of_N n).
Proof.
split => r [] //=; elim=> //= p <-.
- by rewrite Pos2Nat.inj_xI ?exprS -exprD addnn -mul2n.
- by rewrite Pos2Nat.inj_xO ?exprS -exprD addnn -mul2n.
Qed.

Lemma RS (SR : comSemiRingType) : @semi_ring_theory SR 0 1 +%R *%R eq.
Proof. exact/mk_srt/mulrDl/mulrA/mulrC/mul0r/mul1r/addrA/addrC/add0r. Qed.

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

Section RealDomain.

Variable R : realDomainType.

Lemma Rsor : @SOR R 0 1 +%R *%R (fun x y => x - y) -%R eq Order.le Order.lt.
Proof.
apply: mk_SOR_theory.
- exact: RelationClasses.eq_equivalence.
- by move=> x _ <- y _ <-.
- by move=> x _ <- y _ <-.
- by move=> x _ <-.
- by move=> x _ <- y _ <-.
- by move=> x _ <- y _ <-.
- exact: RR.
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
- by move=> x y z; rewrite lerD2l.
- exact: mulr_gt0.
- by apply/eqP; rewrite eq_sym oner_neq0.
Qed.

Lemma Rpower : power_theory 1 *%R eq nat_of_N (@GRing.exp R).
Proof.
apply: mkpow_th => x n; case: n => [//|p]; elim: p => [p|p|//] /= IHp.
- by rewrite Pos2Nat.inj_xI exprS multE mulnC exprM expr2 IHp.
- by rewrite Pos2Nat.inj_xO multE mulnC exprM expr2 IHp.
Qed.

Lemma RSORaddon :
  @SORaddon R 0 1 +%R *%R (fun x y => x - y) -%R eq (fun x y => x <= y) (* ring elements *)
  Z Z0 (Zpos 1) Z.add Z.mul Z.sub Z.opp Z.eqb Z.leb (* coefficients *)
  (fun n => (int_of_Z n)%:~R) nat nat_of_N (@GRing.exp R).
Proof.
apply: mk_SOR_addon.
- exact: RZ.
- exact: Rpower.
- by move=> x y ? /intr_inj; lia.
- by move=> x y; rewrite ler_int; lia.
Qed.

End RealDomain.

Section RealField.

Variable F : realFieldType.

Lemma R_of_Q_eq x y : Qeq_bool x y = (R_of_Q x == R_of_Q y :> F).
Proof.
rewrite /Qeq_bool /R_of_Q /= eqr_div ?pnatr_eq0; try lia.
rewrite !pmulrn -!intrM eqr_int -!/(int_of_Z (Z.pos _)) -!rmorphM /=.
by rewrite (can_eq int_of_ZK); apply/idP/eqP => /Zeq_is_eq_bool.
Qed.

Lemma R_of_Q_le x y : Qle_bool x y = (R_of_Q x <= R_of_Q y :> F).
Proof.
rewrite /Qle_bool /R_of_Q /=.
rewrite ler_pdivrMr ?ltr0n; last lia.
rewrite mulrAC ler_pdivlMr ?ltr0n; last lia.
rewrite !pmulrn -!intrM ler_int; lia.
Qed.

Lemma FQ : ring_morph 0 1 +%R *%R (fun x y : F => x - y) -%R eq
                      0%Q 1%Q Qplus Qmult Qminus Qopp Qeq_bool R_of_Q.
Proof.
apply: mkmorph.
- exact: R_of_Q0.
- exact: R_of_Q1.
- exact: R_of_Q_add.
- exact: R_of_Q_sub.
- exact: R_of_Q_mul.
- exact: R_of_Q_opp.
- by move=> x y; rewrite R_of_Q_eq => /eqP.
Qed.

Lemma FSORaddon :
  @SORaddon F 0 1 +%R *%R (fun x y => x - y) -%R eq (fun x y => x <= y) (* ring elements *)
  Q 0%Q 1%Q Qplus Qmult Qminus Qopp Qeq_bool Qle_bool (* coefficients *)
  R_of_Q nat nat_of_N (@GRing.exp F).
Proof.
apply: mk_SOR_addon.
- exact: FQ.
- exact: Rpower.
- by move=> x y; rewrite R_of_Q_eq => /eqP.
- by move=> x y; rewrite R_of_Q_le.
Qed.

End RealField.

Elpi Db canonicals.db lp:{{

pred canonical-nat-nmodule o:constant.
pred canonical-nat-semiring o:constant.
pred canonical-nat-comsemiring o:constant.
pred canonical-N-nmodule o:constant.
pred canonical-N-semiring o:constant.
pred canonical-N-comsemiring o:constant.
pred canonical-int-nmodule o:constant.
pred canonical-int-zmodule o:constant.
pred canonical-int-semiring o:constant.
pred canonical-int-ring o:constant.
pred canonical-int-comring o:constant.
pred canonical-int-unitring o:constant.
pred canonical-Z-nmodule o:constant.
pred canonical-Z-zmodule o:constant.
pred canonical-Z-semiring o:constant.
pred canonical-Z-ring o:constant.
pred canonical-Z-comring o:constant.
pred canonical-Z-unitring o:constant.

}}.
