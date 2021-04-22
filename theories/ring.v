From Coq Require Import ZArith ZifyClasses Ring Ring_polynom Field_theory.
From elpi Require Import elpi.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat choice seq.
From mathcomp Require Import fintype finfun bigop order ssralg ssrnum ssrint.
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

Section Ring.

Variable (R : ringType).

Definition R_of_Z (n : Z) : R := (int_of_Z n)%:~R.

Lemma R_of_Z_is_additive : additive R_of_Z.
Proof. by move=> x y; rewrite -mulrzBr /+%R /-%R /=; congr intmul; lia. Qed.

Canonical R_of_Z_additive := Additive R_of_Z_is_additive.

Lemma R_of_Z_is_multiplicative : multiplicative R_of_Z.
Proof. by split=> //= x y; rewrite -intrM /*%R /=; congr intmul; lia. Qed.

Canonical R_of_Z_rmorphism := AddRMorphism R_of_Z_is_multiplicative.

Lemma RE : @ring_eq_ext R +%R *%R -%R eq.
Proof. by split; do! move=> ? _ <-. Qed.

Lemma RZ : ring_morph (R := R) 0 1 +%R *%R (fun x y => x - y) -%R eq
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
    F 0 1 +%R *%R (fun x y => x - y) -%R (fun x y => x / y) (@GRing.inv F) eq.
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

Elpi Command ring.
Elpi Accumulate lp:{{

% [eucldiv N D M R] N = D * M + R
pred eucldiv o:int, i:int, o:int, i:int.
eucldiv N D M R :- var N, var M, !, declare_constraint (eucldiv N D M R) [N, M].
eucldiv N D M R :- var N, N is D * M + R.
eucldiv N D M R :- var M, M is N div D, R is N mod D.

pred positive-constant o:int, o:term.
positive-constant 1 {{ lib:num.pos.xH }}.
positive-constant N {{ lib:num.pos.xO lp:T }} :-
  eucldiv N 2 M 0, positive-constant M T.
positive-constant N {{ lib:num.pos.xI lp:T }} :-
  eucldiv N 2 M 1, positive-constant M T.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

pred mem o:term, o:term, o:int.
mem {{ lp:X :: _     }} X 0 :- !.
mem {{ _    :: lp:XS }} X M :- !, mem XS X N, M is N + 1.

pred close o:term.
close {{ nil }} :- !.
close {{ _ :: lp:XS }} :- close XS.

pred quote i:term, i:term, o:term, o:term.
quote ComRing T {{ @PEO Z }} _ :-
  T = {{ @GRing.zero _ }},
  coq.unify-eq T {{ @GRing.zero (GRing.ComRing.zmodType lp:ComRing) }} ok,
  !.
quote ComRing T {{ @PEadd Z lp:R1 lp:R2 }} L :-
  T = {{ @GRing.add lp:Zmodule lp:T1 lp:T2 }},
  coq.unify-eq {{ @GRing.add lp:Zmodule }}
               {{ @GRing.add (GRing.ComRing.zmodType lp:ComRing) }} ok, !,
  quote ComRing T1 R1 L,
  quote ComRing T2 R2 L.
quote ComRing T {{ @PEopp Z lp:R1 }} L :-
  T = {{ @GRing.opp lp:Zmodule lp:T1 }},
  coq.unify-eq {{ @GRing.opp lp:Zmodule }}
               {{ @GRing.opp (GRing.ComRing.zmodType lp:ComRing) }} ok, !,
  quote ComRing T1 R1 L.
% FIXME: [PEeval] is parameterized by a ring morphism [phi : Z -> R] rather than
%        a constant multiplication [GRing.natmul]. So, this does not work.
%
% quote ComRing T {{ @PEmul Z lp:R1 (@PEc Z (Z.of_nat lp:N)) }} :-
%   T = {{ @GRing.natmul lp:Zmodule lp:T1 lp:N }},
%   coq.unify-eq Zmodule {{ GRing.ComRing.zmodType lp:ComRing }} ok, !,
%   quote ComRing T1 R1 L.
quote ComRing T {{ @PEc Z (Z.of_nat lp:N) }} _ :-
  T = {{ @GRing.natmul lp:Zmodule (@GRing.one lp:Ring) lp:N }},
  coq.unify-eq Zmodule {{ @GRing.ComRing.zmodType lp:ComRing }} ok,
  coq.unify-eq {{ @GRing.one lp:Ring }}
               {{ @GRing.one (GRing.ComRing.ringType lp:ComRing) }} ok,
  !.
quote ComRing T {{ @PEI Z }} _ :-
  T = {{ @GRing.one _ }},
  coq.unify-eq T {{ @GRing.one (GRing.ComRing.ringType lp:ComRing) }} ok,
  !.
quote ComRing T {{ @PEmul Z lp:R1 lp:R2 }} L :-
  T = {{ @GRing.mul lp:Ring lp:T1 lp:T2 }},
  coq.unify-eq {{ @GRing.mul lp:Ring }}
               {{ @GRing.mul (GRing.ComRing.ringType lp:ComRing) }} ok, !,
  quote ComRing T1 R1 L,
  quote ComRing T2 R2 L.
% TODO: converse ring
quote ComRing T {{ @PEpow Z lp:R1 (N.of_nat lp:N) }} L :-
  T = {{ @GRing.exp lp:Ring lp:T1 lp:N }},
  coq.unify-eq {{ @GRing.exp lp:Ring }}
               {{ @GRing.exp (GRing.ComRing.ringType lp:ComRing) }} ok, !,
  quote ComRing T1 R1 L.
quote _ T {{ @PEX Z lp:Pos }} L :- !,
  mem L T N, positive-constant {calc (N + 1)} Pos.

}}.
Elpi Typecheck.

Check int_comRing.

Section S.
Variable (x y z : int).

Elpi Query lp:{{

  quote {{ int_comRing }} {{ (10%:R + x + y)%R }} R L. 

}}.
