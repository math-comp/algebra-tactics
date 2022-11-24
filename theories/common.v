From Coq Require Import QArith.
From Coq.micromega Require Import OrderedRing RingMicromega.
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint.
From mathcomp.zify Require Import ssrZ zify.

Import Order.TTheory GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

Implicit Types (R : ringType) (F : fieldType).

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

Definition int_of_Z_expand (n : Z) : int :=
  match n with
  | Z0 => Posz 0
  | Zpos p => Posz (nat_of_pos_expand p)
  | Zneg p => Negz (nat_of_pos_expand p).-1
  end.

Definition Z_of_N_expand (n : N) : Z :=
  match n with
  | N0 => Z0
  | N.pos p => Z.pos p
  end.

Lemma nat_of_N_expandE : nat_of_N_expand = nat_of_N. Proof. by []. Qed.
Lemma int_of_Z_expandE : int_of_Z_expand = int_of_Z. Proof. by []. Qed.
Lemma Z_of_N_expandE : Z_of_N_expand = Z.of_N. Proof. by []. Qed.

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

Variant large_int :=
  | large_int_Z of Z
  | large_int_Pos of Number.uint
  | large_int_Neg of Number.uint.

Definition int_of_large_int (n : large_int) : int :=
  match n with
  | large_int_Z n => int_of_Z_expand n
  | large_int_Pos n => Posz (Nat.of_num_uint n)
  | large_int_Neg n => Negz (Nat.of_num_uint n)
  end.

Definition Z_of_large_int (n : large_int) : Z :=
  match n with
  | large_int_Z n => n
  | large_int_Pos n => Z.of_num_uint n
  | large_int_Neg n => - (Z.succ (Z.of_num_uint n))
  end.

Lemma large_int_Z_int (n : large_int) :
  int_of_Z (Z_of_large_int n) = int_of_large_int n.
Proof.
by case: n => [n|[d|d]|[d|d]] //=; rewrite -(uint_N_nat, hex_uint_N_nat);
  rewrite /Z.of_uint /N.of_uint /Z.of_hex_uint /N.of_hex_uint; lia.
Qed.

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

Lemma R_of_Q_inv (F : numFieldType) x : R_of_Q (/ x) = (R_of_Q x)^-1 :> F.
Proof.
case: x => [[|n|n] d]; rewrite /R_of_Q ?mul0r ?invr0 //= invf_div //=.
apply/eqP; rewrite eqr_div ?pnatr_eq0 ?intr_eq0; try lia.
rewrite -intrM -natrM pmulrn; apply/eqP; congr _%:~R.
by rewrite !NegzE mulrNN !prednK; lia. (* FIXME *)
Qed.

Lemma R_of_Q_invZ (R : unitRingType) x :
  R_of_Q (/ (x # 1)) = (int_of_Z x)%:~R^-1 :> R.
Proof.
case: x => [|n|n]; rewrite /R_of_Q ?mul0r ?invr0 ?mul1r ?mulN1r ?invrN //=.
by congr (- _%:R^-1); lia.
Qed.

(* Some instances required to adapt `ring`, `field`, and `lra` tactics to     *)
(* MathComp                                                                   *)

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
- by move=> x y z; rewrite ler_add2l.
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
rewrite ler_pdivr_mulr ?ltr0n; last lia.
rewrite mulrAC ler_pdivl_mulr ?ltr0n; last lia.
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
