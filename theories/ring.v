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
Variable (x y z x1 x2 x3 x4 x5: int).

Elpi Query lp:{{

  quote {{ int_comRing }} {{ (10%:R + x + y)%R }} R L. 

}}.

Elpi Query lp:{{

  quote {{ int_comRing }} {{ (10%:R + x1 + x2 + x3 + x4 + x5)%R }} _ _. 

}}.


End S.


Section BiggerExample.

Variables (x1 x2 x3 y1 y2 y3 : int).

Definition f1 (x1 x2 x3 y1 y2 y3 : int) :=
  x1^3*x2 - x1*x2^3 - x1^3*x3 + x2^3*x3 + x1*x3^3 - x2*x3^3 - x2*y1^
  2 + x3*y1^2 + x1*y2^2 - x3*y2^2 - x1*y3^2 + x2*y3^2.

  (* This one is instantaneous, almost *)
  Elpi Query lp:{{

  quote {{ int_comRing }} {{ (x1^3*x2 - x1*x2^3 - x1^3*x3 + x2^3*x3 + x1*x3^3 - x2*x3^3 - x2*y1^
  2 + x3*y1^2 + x1*y2^2 - x3*y2^2 - x1*y3^2 + x2*y3^2)%R }} _ _. 

}}.



Definition f2 (x1 x2 x3 y1 y2 y3 : int) := 2%:R*x1^6%:R*x2^3 -
  6%:R*x1^4%:R*x2^5 + 6%:R*x1^2*x2^7 - 2%:R*x2^9 - 6%:R*x1^6%:R*x2^ 2%:R*x3 +
  6%:R*x1^5*x2^3*x3 + 12%:R*x1^4%:R*x2^4%:R*x3 - 12%:R*x1^3*x2^5*x3 -
  6%:R*x1^2*x2^6%:R*x3 + 6%:R*x1*x2^7%:R*x3 + 6%:R*x1^6%:R*x2*x3^2 -
  18%:R*x1^5*x2^2*x3^2 + 6%:R*x1^4%:R*x2^3*x3^2 + 24%:R*x1^3*x2^4%:R*x3^2 -
  18%:R*x1^2*x2^5*x3^2 - 6%:R*x1*x2^6%:R*x3^2 + 6%:R*x2^7%:R*x3^2 - 2%:R*x1^6%:R*x3^3
  + 18%:R*x1^5*x2*x3^3 - 30%:R*x1^4%:R*x2^2*x3^3 + 2%:R*x1^3*x2^3*x3^3 +
  24%:R*x1^2*x2^4%:R*x3^3 - 12%:R*x1*x2^5*x3^3 - 6%:R*x1^5*x3^4 +
  24%:R*x1^4%:R*x2*x3^4 - 30%:R*x1^3*x2^2*x3^4 + 6%:R*x1^2*x2^3*x3^4 +
  12%:R*x1*x2^4%:R*x3^4 - 6%:R*x2^5*x3^4 - 6%:R*x1^4%:R*x3^5 + 18%:R*x1^3*x2*x3^5 -
  18%:R*x1^2*x2^2*x3^5 + 6%:R*x1*x2^3*x3^5 - 2%:R*x1^3*x3^6 +
  6%:R*x1^2*x2*x3^6 - 6%:R*x1*x2^2*x3^6 + 2%:R*x2^3*x3^6 -
  3%:R*x1^3*x2^3*y1^2 + 3%:R*x1*x2^5*y1^2 + 9%:R*x1^3*x2^2*x3*y1^2 -
  6%:R*x1^2*x2^3*x3*y1^2 - 6%:R*x1*x2^4%:R*x3*y1^2 + 3%:R*x2^5*x3*y1^2 -
  9%:R*x1^3*x2*x3^2*y1^2 + 18%:R*x1^2*x2^2*x3^2*y1^2 -
  3%:R*x1*x2^3*x3^2*y1^2 - 6%:R*x2^4%:R*x3^2*y1^2 + 3%:R*x1^3*x3^3*y1^2 -
  18%:R*x1^2*x2*x3^3*y1^2 + 15%:R*x1*x2^2*x3^3*y1^2 + 6%:R*x1^2*x3^4%:R*y1^2
  - 12%:R*x1*x2*x3^4%:R*y1^2 + 6%:R*x2^2*x3^4%:R*y1^2 + 3%:R*x1*x3^5*y1^2 -
  3%:R*x2*x3^5*y1^2 + x2^3*y1^4 - 3%:R*x2^2*x3*y1^4 + 3%:R*x2*x3^2*y1^4 -
  x3^3*y1^4 + 8%:R*x1^3*x2^3*y1*y2 - 2%:R*x1^2*x2^4%:R*y1*y2 -
  8%:R*x1*x2^5*y1*y2 + 2%:R*x2^6%:R*y1*y2 - 18%:R*x1^3*x2^2*x3*y1*y2 +
  14%:R*x1^2*x2^3*x3*y1*y2 + 8%:R*x1*x2^4%:R*x3*y1*y2 - 4%:R*x2^5*x3*y1*y2 +
  12%:R*x1^3*x2*x3^2*y1*y2 - 30%:R*x1^2*x2^2*x3^2*y1*y2 +
  12%:R*x1*x2^3*x3^2*y1*y2 + 6%:R*x2^4%:R*x3^2*y1*y2 - 2%:R*x1^3*x3^3*y1*y2 +
  26%:R*x1^2*x2*x3^3*y1*y2 - 22%:R*x1*x2^2*x3^3*y1*y2 -
  2%:R*x2^3*x3^3*y1*y2 - 8%:R*x1^2*x3^4%:R*y1*y2 + 16%:R*x1*x2*x3^4%:R*y1*y2 -
  8%:R*x2^2*x3^4%:R*y1*y2 - 6%:R*x1*x3^5*y1*y2 + 6%:R*x2*x3^5*y1*y2 -
  6%:R*x2^3*y1^3*y2 + 12%:R*x2^2*x3*y1^3*y2 - 6%:R*x2*x3^2*y1^3*y2 -
  3%:R*x1^5*x2*y2^2 + 2%:R*x1^4%:R*x2^2*y2^2 + 3%:R*x1^3*x2^3*y2^2 -
  4%:R*x1^2*x2^4%:R*y2^2 + 2%:R*x2^6%:R*y2^2 + 3%:R*x1^5*x3*y2^2 -
  4%:R*x1^4%:R*x2*x3*y2^2 + 4%:R*x1^3*x2^2*x3*y2^2 + x1^2*x2^3*x3*y2^2 -
  4%:R*x1*x2^4%:R*x3*y2^2 + 2%:R*x1^4%:R*x3^2*y2^2 - 5%:R*x1^3*x2*x3^2*y2^2 +
  6%:R*x1^2*x2^2*x3^2*y2^2 + x1*x2^3*x3^2*y2^2 - 4%:R*x2^4%:R*x3^2*y2^2 -
  2%:R*x1^3*x3^3*y2^2 - 5%:R*x1^2*x2*x3^3*y2^2 + 4%:R*x1*x2^2*x3^3*y2^2 +
  3%:R*x2^3*x3^3*y2^2 + 2%:R*x1^2*x3^4%:R*y2^2 - 4%:R*x1*x2*x3^4%:R*y2^2 +
  2%:R*x2^2*x3^4%:R*y2^2 + 3%:R*x1*x3^5*y2^2 - 3%:R*x2*x3^5*y2^2 +
  3%:R*x1^2*x2*y1^2*y2^2 - x1*x2^2*y1^2*y2^2 + 10%:R*x2^3*y1^2*y2^2 -
  3%:R*x1^2*x3*y1^2*y2^2 + 2%:R*x1*x2*x3*y1^2*y2^2 -
  17%:R*x2^2*x3*y1^2*y2^2 - x1*x3^2*y1^2*y2^2 + x2*x3^2*y1^2*y2^2 +
  6%:R*x3^3*y1^2*y2^2 - 2%:R*x1^3*y1*y2^3 - 4%:R*x1^2*x2*y1*y2^3 +
  4%:R*x1*x2^2*y1*y2^3 - 8%:R*x2^3*y1*y2^3 + 4%:R*x1^2*x3*y1*y2^3 +
  8%:R*x2^2*x3*y1*y2^3 + 2%:R*x1*x3^2*y1*y2^3 + 4%:R*x2*x3^2*y1*y2^3 -
  8%:R*x3^3*y1*y2^3 + 2%:R*y1^3*y2^3 + 3%:R*x1^3*y2^4 - 2%:R*x1^2*x2*y2^4 +
  2%:R*x2^3*y2^4 - x1^2*x3*y2^4 - 2%:R*x1*x2*x3*y2^4 - x1*x3^2*y2^4 -
  2%:R*x2*x3^2*y2^4 + 3%:R*x3^3*y2^4 - 6%:R*y1^2*y2^4 + 6%:R*y1*y2^5 - 2%:R*y2^6
  - 6%:R*x1^3*x2^3*y1*y3 + 6%:R*x1^2*x2^4%:R*y1*y3 + 6%:R*x1*x2^5*y1*y3 -
  6%:R*x2^6%:R*y1*y3 + 12%:R*x1^3*x2^2*x3*y1*y3 - 18%:R*x1^2*x2^3*x3*y1*y3 +
  6%:R*x2^5*x3*y1*y3 - 6%:R*x1^3*x2*x3^2*y1*y3 +
  18%:R*x1^2*x2^2*x3^2*y1*y3 - 18%:R*x1*x2^3*x3^2*y1*y3 +
  6%:R*x2^4%:R*x3^2*y1*y3 - 6%:R*x1^2*x2*x3^3*y1*y3 +
  12%:R*x1*x2^2*x3^3*y1*y3 - 6%:R*x2^3*x3^3*y1*y3 + 4%:R*x2^3*y1^3*y3 -
  6%:R*x2^2*x3*y1^3*y3 + 2%:R*x3^3*y1^3*y3 + 6%:R*x1^5*x2*y2*y3 -
  8%:R*x1^4%:R*x2^2*y2*y3 - 2%:R*x1^3*x2^3*y2*y3 + 6%:R*x1^2*x2^4%:R*y2*y3 -
  4%:R*x1*x2^5*y2*y3 + 2%:R*x2^6%:R*y2*y3 - 6%:R*x1^5*x3*y2*y3 +
  16%:R*x1^4%:R*x2*x3*y2*y3 - 22%:R*x1^3*x2^2*x3*y2*y3 +
  12%:R*x1^2*x2^3*x3*y2*y3 + 8%:R*x1*x2^4%:R*x3*y2*y3 - 8%:R*x2^5*x3*y2*y3 -
  8%:R*x1^4%:R*x3^2*y2*y3 + 26%:R*x1^3*x2*x3^2*y2*y3 -
  30%:R*x1^2*x2^2*x3^2*y2*y3 + 14%:R*x1*x2^3*x3^2*y2*y3 -
  2%:R*x2^4%:R*x3^2*y2*y3 - 2%:R*x1^3*x3^3*y2*y3 + 12%:R*x1^2*x2*x3^3*y2*y3 -
  18%:R*x1*x2^2*x3^3*y2*y3 + 8%:R*x2^3*x3^3*y2*y3 -
  6%:R*x1^2*x2*y1^2*y2*y3 + 4%:R*x1*x2^2*y1^2*y2*y3 -
  10%:R*x2^3*y1^2*y2*y3 + 6%:R*x1^2*x3*y1^2*y2*y3 -
  8%:R*x1*x2*x3*y1^2*y2*y3 + 20%:R*x2^2*x3*y1^2*y2*y3 +
  4%:R*x1*x3^2*y1^2*y2*y3 - 4%:R*x2*x3^2*y1^2*y2*y3 - 6%:R*x3^3*y1^2*y2*y3
  + 6%:R*x1^3*y1*y2^2*y3 + 8%:R*x1^2*x2*y1*y2^2*y3 -
  18%:R*x1*x2^2*y1*y2^2*y3 + 16%:R*x2^3*y1*y2^2*y3 -
  8%:R*x1^2*x3*y1*y2^2*y3 + 8%:R*x1*x2*x3*y1*y2^2*y3 -
  18%:R*x2^2*x3*y1*y2^2*y3 - 8%:R*x1*x3^2*y1*y2^2*y3 +
  8%:R*x2*x3^2*y1*y2^2*y3 + 6%:R*x3^3*y1*y2^2*y3 - 6%:R*y1^3*y2^2*y3 -
  8%:R*x1^3*y2^3*y3 + 4%:R*x1^2*x2*y2^3*y3 + 8%:R*x1*x2^2*y2^3*y3 -
  8%:R*x2^3*y2^3*y3 + 2%:R*x1^2*x3*y2^3*y3 + 4%:R*x2^2*x3*y2^3*y3 +
  4%:R*x1*x3^2*y2^3*y3 - 4%:R*x2*x3^2*y2^3*y3 - 2%:R*x3^3*y2^3*y3 +
  18%:R*y1^2*y2^3*y3 - 18%:R*y1*y2^4%:R*y3 + 6%:R*y2^5*y3 - 3%:R*x1^5*x2*y3^2 +
  6%:R*x1^4%:R*x2^2*y3^2 - 6%:R*x1^2*x2^4%:R*y3^2 + 3%:R*x1*x2^5*y3^2 +
  3%:R*x1^5*x3*y3^2 - 12%:R*x1^4%:R*x2*x3*y3^2 + 15%:R*x1^3*x2^2*x3*y3^2 -
  3%:R*x1^2*x2^3*x3*y3^2 - 6%:R*x1*x2^4%:R*x3*y3^2 + 3%:R*x2^5*x3*y3^2 +
  6%:R*x1^4%:R*x3^2*y3^2 - 18%:R*x1^3*x2*x3^2*y3^2 +
  18%:R*x1^2*x2^2*x3^2*y3^2 - 6%:R*x1*x2^3*x3^2*y3^2 + 3%:R*x1^3*x3^3*y3^2
  - 9%:R*x1^2*x2*x3^3*y3^2 + 9%:R*x1*x2^2*x3^3*y3^2 - 3%:R*x2^3*x3^3*y3^2
  + 3%:R*x1^2*x2*y1^2*y3^2 - 3%:R*x1*x2^2*y1^2*y3^2 -
  3%:R*x1^2*x3*y1^2*y3^2 + 6%:R*x1*x2*x3*y1^2*y3^2 -
  3%:R*x2^2*x3*y1^2*y3^2 - 3%:R*x1*x3^2*y1^2*y3^2 + 3%:R*x2*x3^2*y1^2*y3^2
  - 6%:R*x1^3*y1*y2*y3^2 - 4%:R*x1^2*x2*y1*y2*y3^2 +
  20%:R*x1*x2^2*y1*y2*y3^2 - 10%:R*x2^3*y1*y2*y3^2 +
  4%:R*x1^2*x3*y1*y2*y3^2 - 8%:R*x1*x2*x3*y1*y2*y3^2 +
  4%:R*x2^2*x3*y1*y2*y3^2 + 6%:R*x1*x3^2*y1*y2*y3^2 -
  6%:R*x2*x3^2*y1*y2*y3^2 + 6%:R*y1^3*y2*y3^2 + 6%:R*x1^3*y2^2*y3^2 +
  x1^2*x2*y2^2*y3^2 - 17%:R*x1*x2^2*y2^2*y3^2 + 10%:R*x2^3*y2^2*y3^2 -
  x1^2*x3*y2^2*y3^2 + 2%:R*x1*x2*x3*y2^2*y3^2 - x2^2*x3*y2^2*y3^2 -
  3%:R*x1*x3^2*y2^2*y3^2 + 3%:R*x2*x3^2*y2^2*y3^2 - 18%:R*y1^2*y2^2*y3^2 +
  18%:R*y1*y2^3*y3^2 - 6%:R*y2^4%:R*y3^2 + 2%:R*x1^3*y1*y3^3 -
  6%:R*x1*x2^2*y1*y3^3 + 4%:R*x2^3*y1*y3^3 - 2%:R*y1^3*y3^3 -
  6%:R*x1^2*x2*y2*y3^3 + 12%:R*x1*x2^2*y2*y3^3 - 6%:R*x2^3*y2*y3^3 +
  6%:R*y1^2*y2*y3^3 - 6%:R*y1*y2^2*y3^3 + 2%:R*y2^3*y3^3 - x1^3*y3^4 +
  3%:R*x1^2*x2*y3^4 - 3%:R*x1*x2^2*y3^4 + x2^3*y3^4.


  (* This one takes about 12s on my machine*)
  Elpi Query lp:{{

  quote {{ int_comRing }} {{ ( 2%:R*x1^6%:R*x2^3 -
  6%:R*x1^4%:R*x2^5 + 6%:R*x1^2*x2^7 - 2%:R*x2^9 - 6%:R*x1^6%:R*x2^ 2%:R*x3 +
  6%:R*x1^5*x2^3*x3 + 12%:R*x1^4%:R*x2^4%:R*x3 - 12%:R*x1^3*x2^5*x3 -
  6%:R*x1^2*x2^6%:R*x3 + 6%:R*x1*x2^7%:R*x3 + 6%:R*x1^6%:R*x2*x3^2 -
  18%:R*x1^5*x2^2*x3^2 + 6%:R*x1^4%:R*x2^3*x3^2 + 24%:R*x1^3*x2^4%:R*x3^2 -
  18%:R*x1^2*x2^5*x3^2 - 6%:R*x1*x2^6%:R*x3^2 + 6%:R*x2^7%:R*x3^2 - 2%:R*x1^6%:R*x3^3
  + 18%:R*x1^5*x2*x3^3 - 30%:R*x1^4%:R*x2^2*x3^3 + 2%:R*x1^3*x2^3*x3^3 +
  24%:R*x1^2*x2^4%:R*x3^3 - 12%:R*x1*x2^5*x3^3 - 6%:R*x1^5*x3^4 +
  24%:R*x1^4%:R*x2*x3^4 - 30%:R*x1^3*x2^2*x3^4 + 6%:R*x1^2*x2^3*x3^4 +
  12%:R*x1*x2^4%:R*x3^4 - 6%:R*x2^5*x3^4 - 6%:R*x1^4%:R*x3^5 + 18%:R*x1^3*x2*x3^5 -
  18%:R*x1^2*x2^2*x3^5 + 6%:R*x1*x2^3*x3^5 - 2%:R*x1^3*x3^6 +
  6%:R*x1^2*x2*x3^6 - 6%:R*x1*x2^2*x3^6 + 2%:R*x2^3*x3^6 -
  3%:R*x1^3*x2^3*y1^2 + 3%:R*x1*x2^5*y1^2 + 9%:R*x1^3*x2^2*x3*y1^2 -
  6%:R*x1^2*x2^3*x3*y1^2 - 6%:R*x1*x2^4%:R*x3*y1^2 + 3%:R*x2^5*x3*y1^2 -
  9%:R*x1^3*x2*x3^2*y1^2 + 18%:R*x1^2*x2^2*x3^2*y1^2 -
  3%:R*x1*x2^3*x3^2*y1^2 - 6%:R*x2^4%:R*x3^2*y1^2 + 3%:R*x1^3*x3^3*y1^2 -
  18%:R*x1^2*x2*x3^3*y1^2 + 15%:R*x1*x2^2*x3^3*y1^2 + 6%:R*x1^2*x3^4%:R*y1^2
  - 12%:R*x1*x2*x3^4%:R*y1^2 + 6%:R*x2^2*x3^4%:R*y1^2 + 3%:R*x1*x3^5*y1^2 -
  3%:R*x2*x3^5*y1^2 + x2^3*y1^4 - 3%:R*x2^2*x3*y1^4 + 3%:R*x2*x3^2*y1^4 -
  x3^3*y1^4 + 8%:R*x1^3*x2^3*y1*y2 - 2%:R*x1^2*x2^4%:R*y1*y2 -
  8%:R*x1*x2^5*y1*y2 + 2%:R*x2^6%:R*y1*y2 - 18%:R*x1^3*x2^2*x3*y1*y2 +
  14%:R*x1^2*x2^3*x3*y1*y2 + 8%:R*x1*x2^4%:R*x3*y1*y2 - 4%:R*x2^5*x3*y1*y2 +
  12%:R*x1^3*x2*x3^2*y1*y2 - 30%:R*x1^2*x2^2*x3^2*y1*y2 +
  12%:R*x1*x2^3*x3^2*y1*y2 + 6%:R*x2^4%:R*x3^2*y1*y2 - 2%:R*x1^3*x3^3*y1*y2 +
  26%:R*x1^2*x2*x3^3*y1*y2 - 22%:R*x1*x2^2*x3^3*y1*y2 -
  2%:R*x2^3*x3^3*y1*y2 - 8%:R*x1^2*x3^4%:R*y1*y2 + 16%:R*x1*x2*x3^4%:R*y1*y2 -
  8%:R*x2^2*x3^4%:R*y1*y2 - 6%:R*x1*x3^5*y1*y2 + 6%:R*x2*x3^5*y1*y2 -
  6%:R*x2^3*y1^3*y2 + 12%:R*x2^2*x3*y1^3*y2 - 6%:R*x2*x3^2*y1^3*y2 -
  3%:R*x1^5*x2*y2^2 + 2%:R*x1^4%:R*x2^2*y2^2 + 3%:R*x1^3*x2^3*y2^2 -
  4%:R*x1^2*x2^4%:R*y2^2 + 2%:R*x2^6%:R*y2^2 + 3%:R*x1^5*x3*y2^2 -
  4%:R*x1^4%:R*x2*x3*y2^2 + 4%:R*x1^3*x2^2*x3*y2^2 + x1^2*x2^3*x3*y2^2 -
  4%:R*x1*x2^4%:R*x3*y2^2 + 2%:R*x1^4%:R*x3^2*y2^2 - 5%:R*x1^3*x2*x3^2*y2^2 +
  6%:R*x1^2*x2^2*x3^2*y2^2 + x1*x2^3*x3^2*y2^2 - 4%:R*x2^4%:R*x3^2*y2^2 -
  2%:R*x1^3*x3^3*y2^2 - 5%:R*x1^2*x2*x3^3*y2^2 + 4%:R*x1*x2^2*x3^3*y2^2 +
  3%:R*x2^3*x3^3*y2^2 + 2%:R*x1^2*x3^4%:R*y2^2 - 4%:R*x1*x2*x3^4%:R*y2^2 +
  2%:R*x2^2*x3^4%:R*y2^2 + 3%:R*x1*x3^5*y2^2 - 3%:R*x2*x3^5*y2^2 +
  3%:R*x1^2*x2*y1^2*y2^2 - x1*x2^2*y1^2*y2^2 + 10%:R*x2^3*y1^2*y2^2 -
  3%:R*x1^2*x3*y1^2*y2^2 + 2%:R*x1*x2*x3*y1^2*y2^2 -
  17%:R*x2^2*x3*y1^2*y2^2 - x1*x3^2*y1^2*y2^2 + x2*x3^2*y1^2*y2^2 +
  6%:R*x3^3*y1^2*y2^2 - 2%:R*x1^3*y1*y2^3 - 4%:R*x1^2*x2*y1*y2^3 +
  4%:R*x1*x2^2*y1*y2^3 - 8%:R*x2^3*y1*y2^3 + 4%:R*x1^2*x3*y1*y2^3 +
  8%:R*x2^2*x3*y1*y2^3 + 2%:R*x1*x3^2*y1*y2^3 + 4%:R*x2*x3^2*y1*y2^3 -
  8%:R*x3^3*y1*y2^3 + 2%:R*y1^3*y2^3 + 3%:R*x1^3*y2^4 - 2%:R*x1^2*x2*y2^4 +
  2%:R*x2^3*y2^4 - x1^2*x3*y2^4 - 2%:R*x1*x2*x3*y2^4 - x1*x3^2*y2^4 -
  2%:R*x2*x3^2*y2^4 + 3%:R*x3^3*y2^4 - 6%:R*y1^2*y2^4 + 6%:R*y1*y2^5 - 2%:R*y2^6
  - 6%:R*x1^3*x2^3*y1*y3 + 6%:R*x1^2*x2^4%:R*y1*y3 + 6%:R*x1*x2^5*y1*y3 -
  6%:R*x2^6%:R*y1*y3 + 12%:R*x1^3*x2^2*x3*y1*y3 - 18%:R*x1^2*x2^3*x3*y1*y3 +
  6%:R*x2^5*x3*y1*y3 - 6%:R*x1^3*x2*x3^2*y1*y3 +
  18%:R*x1^2*x2^2*x3^2*y1*y3 - 18%:R*x1*x2^3*x3^2*y1*y3 +
  6%:R*x2^4%:R*x3^2*y1*y3 - 6%:R*x1^2*x2*x3^3*y1*y3 +
  12%:R*x1*x2^2*x3^3*y1*y3 - 6%:R*x2^3*x3^3*y1*y3 + 4%:R*x2^3*y1^3*y3 -
  6%:R*x2^2*x3*y1^3*y3 + 2%:R*x3^3*y1^3*y3 + 6%:R*x1^5*x2*y2*y3 -
  8%:R*x1^4%:R*x2^2*y2*y3 - 2%:R*x1^3*x2^3*y2*y3 + 6%:R*x1^2*x2^4%:R*y2*y3 -
  4%:R*x1*x2^5*y2*y3 + 2%:R*x2^6%:R*y2*y3 - 6%:R*x1^5*x3*y2*y3 +
  16%:R*x1^4%:R*x2*x3*y2*y3 - 22%:R*x1^3*x2^2*x3*y2*y3 +
  12%:R*x1^2*x2^3*x3*y2*y3 + 8%:R*x1*x2^4%:R*x3*y2*y3 - 8%:R*x2^5*x3*y2*y3 -
  8%:R*x1^4%:R*x3^2*y2*y3 + 26%:R*x1^3*x2*x3^2*y2*y3 -
  30%:R*x1^2*x2^2*x3^2*y2*y3 + 14%:R*x1*x2^3*x3^2*y2*y3 -
  2%:R*x2^4%:R*x3^2*y2*y3 - 2%:R*x1^3*x3^3*y2*y3 + 12%:R*x1^2*x2*x3^3*y2*y3 -
  18%:R*x1*x2^2*x3^3*y2*y3 + 8%:R*x2^3*x3^3*y2*y3 -
  6%:R*x1^2*x2*y1^2*y2*y3 + 4%:R*x1*x2^2*y1^2*y2*y3 -
  10%:R*x2^3*y1^2*y2*y3 + 6%:R*x1^2*x3*y1^2*y2*y3 -
  8%:R*x1*x2*x3*y1^2*y2*y3 + 20%:R*x2^2*x3*y1^2*y2*y3 +
  4%:R*x1*x3^2*y1^2*y2*y3 - 4%:R*x2*x3^2*y1^2*y2*y3 - 6%:R*x3^3*y1^2*y2*y3
  + 6%:R*x1^3*y1*y2^2*y3 + 8%:R*x1^2*x2*y1*y2^2*y3 -
  18%:R*x1*x2^2*y1*y2^2*y3 + 16%:R*x2^3*y1*y2^2*y3 -
  8%:R*x1^2*x3*y1*y2^2*y3 + 8%:R*x1*x2*x3*y1*y2^2*y3 -
  18%:R*x2^2*x3*y1*y2^2*y3 - 8%:R*x1*x3^2*y1*y2^2*y3 +
  8%:R*x2*x3^2*y1*y2^2*y3 + 6%:R*x3^3*y1*y2^2*y3 - 6%:R*y1^3*y2^2*y3 -
  8%:R*x1^3*y2^3*y3 + 4%:R*x1^2*x2*y2^3*y3 + 8%:R*x1*x2^2*y2^3*y3 -
  8%:R*x2^3*y2^3*y3 + 2%:R*x1^2*x3*y2^3*y3 + 4%:R*x2^2*x3*y2^3*y3 +
  4%:R*x1*x3^2*y2^3*y3 - 4%:R*x2*x3^2*y2^3*y3 - 2%:R*x3^3*y2^3*y3 +
  18%:R*y1^2*y2^3*y3 - 18%:R*y1*y2^4%:R*y3 + 6%:R*y2^5*y3 - 3%:R*x1^5*x2*y3^2 +
  6%:R*x1^4%:R*x2^2*y3^2 - 6%:R*x1^2*x2^4%:R*y3^2 + 3%:R*x1*x2^5*y3^2 +
  3%:R*x1^5*x3*y3^2 - 12%:R*x1^4%:R*x2*x3*y3^2 + 15%:R*x1^3*x2^2*x3*y3^2 -
  3%:R*x1^2*x2^3*x3*y3^2 - 6%:R*x1*x2^4%:R*x3*y3^2 + 3%:R*x2^5*x3*y3^2 +
  6%:R*x1^4%:R*x3^2*y3^2 - 18%:R*x1^3*x2*x3^2*y3^2 +
  18%:R*x1^2*x2^2*x3^2*y3^2 - 6%:R*x1*x2^3*x3^2*y3^2 + 3%:R*x1^3*x3^3*y3^2
  - 9%:R*x1^2*x2*x3^3*y3^2 + 9%:R*x1*x2^2*x3^3*y3^2 - 3%:R*x2^3*x3^3*y3^2
  + 3%:R*x1^2*x2*y1^2*y3^2 - 3%:R*x1*x2^2*y1^2*y3^2 -
  3%:R*x1^2*x3*y1^2*y3^2 + 6%:R*x1*x2*x3*y1^2*y3^2 -
  3%:R*x2^2*x3*y1^2*y3^2 - 3%:R*x1*x3^2*y1^2*y3^2 + 3%:R*x2*x3^2*y1^2*y3^2
  - 6%:R*x1^3*y1*y2*y3^2 - 4%:R*x1^2*x2*y1*y2*y3^2 +
  20%:R*x1*x2^2*y1*y2*y3^2 - 10%:R*x2^3*y1*y2*y3^2 +
  4%:R*x1^2*x3*y1*y2*y3^2 - 8%:R*x1*x2*x3*y1*y2*y3^2 +
  4%:R*x2^2*x3*y1*y2*y3^2 + 6%:R*x1*x3^2*y1*y2*y3^2 -
  6%:R*x2*x3^2*y1*y2*y3^2 + 6%:R*y1^3*y2*y3^2 + 6%:R*x1^3*y2^2*y3^2 +
  x1^2*x2*y2^2*y3^2 - 17%:R*x1*x2^2*y2^2*y3^2 + 10%:R*x2^3*y2^2*y3^2 -
  x1^2*x3*y2^2*y3^2 + 2%:R*x1*x2*x3*y2^2*y3^2 - x2^2*x3*y2^2*y3^2 -
  3%:R*x1*x3^2*y2^2*y3^2 + 3%:R*x2*x3^2*y2^2*y3^2 - 18%:R*y1^2*y2^2*y3^2 +
  18%:R*y1*y2^3*y3^2 - 6%:R*y2^4%:R*y3^2 + 2%:R*x1^3*y1*y3^3 -
  6%:R*x1*x2^2*y1*y3^3 + 4%:R*x2^3*y1*y3^3 - 2%:R*y1^3*y3^3 -
  6%:R*x1^2*x2*y2*y3^3 + 12%:R*x1*x2^2*y2*y3^3 - 6%:R*x2^3*y2*y3^3 +
  6%:R*y1^2*y2*y3^3 - 6%:R*y1*y2^2*y3^3 + 2%:R*y2^3*y3^3 - x1^3*y3^4 +
  3%:R*x1^2*x2*y3^4 - 3%:R*x1*x2^2*y3^4 + x2^3*y3^4 )%R }} _ _. 

}}.


Definition f3 (x1 x2 x3 y1 y2 y3 : int) := 2%:R*x1^9%:R*x2^4 -
 8%:R*x1^7%:R*x2^6 + 12%:R*x1^5*x2^8 - 8%:R*x1^3*x2^10 + 2%:R*x1*x2^12 -
 8%:R*x1^9%:R*x2^3*x3 + 6%:R*x1^ 8%:R*x2^4%:R*x3 + 24%:R*x1^7%:R*x2^5*x3 -
16%:R*x1^6%:R*x2^6%:R*x3 - 24%:R*x1^5*x2^7%:R*x3 + 12%:R*x1^4%:R*x2^ 8%:R*x3 +
 8%:R*x1^3*x2^9%:R*x3 - 2%:R*x2^12%:R*x3 + 12%:R*x1^9%:R*x2^2*x3^2 -
 24%:R*x1^ 8%:R*x2^3*x3^2 - 12%:R*x1^7%:R*x2^4%:R*x3^2 + 48%:R*x1^6%:R*x2^5*x3^2 -
12%:R*x1^5*x2^6%:R*x3^2 - 24%:R*x1^4%:R*x2^7%:R*x3^2 + 12%:R*x1^3*x2^ 8%:R*x3^2 -
 8%:R*x1^9%:R*x2*x3^3 + 36%:R*x1^ 8%:R*x2^2*x3^3 - 32%:R*x1^7%:R*x2^3*x3^3 -
36%:R*x1^6%:R*x2^4%:R*x3^3 + 48%:R*x1^5*x2^5*x3^3 + 4%:R*x1^4%:R*x2^6%:R*x3^3 -
12%:R*x1^2*x2^ 8%:R*x3^3 - 8%:R*x1*x2^9%:R*x3^3 + 8%:R*x2^10%:R*x3^3 + 2%:R*x1^9%:R*x3^4 -
 24%:R*x1^ 8%:R*x2*x3^4 + 48%:R*x1^7%:R*x2^2*x3^4 - 16%:R*x1^6%:R*x2^3*x3^4 -
18%:R*x1^5*x2^4%:R*x3^4 - 4%:R*x1^3*x2^6%:R*x3^4 + 24%:R*x1^2*x2^7%:R*x3^4 -
12%:R*x1*x2^ 8%:R*x3^4 + 6%:R*x1^ 8%:R*x3^5 - 24%:R*x1^7%:R*x2*x3^5 +
 24%:R*x1^6%:R*x2^2*x3^5 + 18%:R*x1^4%:R*x2^4%:R*x3^5 - 48%:R*x1^3*x2^5*x3^5 +
12%:R*x1^2*x2^6%:R*x3^5 + 24%:R*x1*x2^7%:R*x3^5 - 12%:R*x2^ 8%:R*x3^5 + 4%:R*x1^7%:R*x3^6
- 24%:R*x1^5*x2^2*x3^6 + 16%:R*x1^4%:R*x2^3*x3^6 + 36%:R*x1^3*x2^4%:R*x3^6 -
48%:R*x1^2*x2^5*x3^6 + 16%:R*x1*x2^6%:R*x3^6 - 4%:R*x1^6%:R*x3^7 +
 24%:R*x1^5*x2*x3^7 - 48%:R*x1^4%:R*x2^2*x3^7 + 32%:R*x1^3*x2^3*x3^7 +
12%:R*x1^2*x2^4%:R*x3^7 - 24%:R*x1*x2^5*x3^7 + 8%:R*x2^6%:R*x3^7 - 6%:R*x1^5*x3^8 +
 24%:R*x1^4%:R*x2*x3^8 - 36%:R*x1^3*x2^2*x3^8 + 24%:R*x1^2*x2^3*x3^8 -
6%:R*x1*x2^4%:R*x3^8 - 2%:R*x1^4%:R*x3^9 + 8%:R*x1^3*x2*x3^9 - 12%:R*x1^2*x2^2*x3^9
+ 8%:R*x1*x2^3*x3^9 - 2%:R*x2^4%:R*x3^9 - 5%:R*x1^6%:R*x2^4%:R*y1^2 +
12%:R*x1^4%:R*x2^6%:R*y1^2 - 9%:R*x1^2*x2^ 8%:R*y1^2 + 2%:R*x2^10%:R*y1^2 +
20%:R*x1^6%:R*x2^3*x3*y1^2 - 12%:R*x1^5*x2^4%:R*x3*y1^2 -
36%:R*x1^4%:R*x2^5*x3*y1^2 + 18%:R*x1^3*x2^6%:R*x3*y1^2 +
18%:R*x1^2*x2^7%:R*x3*y1^2 - 6%:R*x1*x2^ 8%:R*x3*y1^2 - 2%:R*x2^9%:R*x3*y1^2 -
30%:R*x1^6%:R*x2^2*x3^2*y1^2 + 48%:R*x1^5*x2^3*x3^2*y1^2 +
18%:R*x1^4%:R*x2^4%:R*x3^2*y1^2 - 54%:R*x1^3*x2^5*x3^2*y1^2 +
9%:R*x1^2*x2^6%:R*x3^2*y1^2 + 12%:R*x1*x2^7%:R*x3^2*y1^2 - 3%:R*x2^ 8%:R*x3^2*y1^2 +
20%:R*x1^6%:R*x2*x3^3*y1^2 - 72%:R*x1^5*x2^2*x3^3*y1^2 +
48%:R*x1^4%:R*x2^3*x3^3*y1^2 + 40%:R*x1^3*x2^4%:R*x3^3*y1^2 -
36%:R*x1^2*x2^5*x3^3*y1^2 - 5%:R*x1^6%:R*x3^4%:R*y1^2 + 48%:R*x1^5*x2*x3^4%:R*y1^2
- 72%:R*x1^4%:R*x2^2*x3^4%:R*y1^2 + 20%:R*x1^3*x2^3*x3^4%:R*y1^2 +
12%:R*x1^2*x2^4%:R*x3^4%:R*y1^2 - 6%:R*x1*x2^5*x3^4%:R*y1^2 + 3%:R*x2^6%:R*x3^4%:R*y1^2 -
12%:R*x1^5*x3^5*y1^2 + 36%:R*x1^4%:R*x2*x3^5*y1^2 - 30%:R*x1^3*x2^2*x3^5*y1^2
+ 6%:R*x1^2*x2^3*x3^5*y1^2 - 6%:R*x1*x2^4%:R*x3^5*y1^2 + 6%:R*x2^5*x3^5*y1^2
- 6%:R*x1^4%:R*x3^6%:R*y1^2 + 2%:R*x1^3*x2*x3^6%:R*y1^2 + 9%:R*x1^2*x2^2*x3^6%:R*y1^2
- 5%:R*x2^4%:R*x3^6%:R*y1^2 + 4%:R*x1^3*x3^7%:R*y1^2 - 12%:R*x1^2*x2*x3^7%:R*y1^2 +
12%:R*x1*x2^2*x3^7%:R*y1^2 - 4%:R*x2^3*x3^7%:R*y1^2 + 3%:R*x1^2*x3^ 8%:R*y1^2 -
6%:R*x1*x2*x3^ 8%:R*y1^2 + 3%:R*x2^2*x3^ 8%:R*y1^2 + 4%:R*x1^3*x2^4%:R*y1^4 -
4%:R*x1*x2^6%:R*y1^4 - 16%:R*x1^3*x2^3*x3*y1^4 + 6%:R*x1^2*x2^4%:R*x3*y1^4 +
12%:R*x1*x2^5*x3*y1^4 - 2%:R*x2^6%:R*x3*y1^4 + 24%:R*x1^3*x2^2*x3^2*y1^4 -
 24%:R*x1^2*x2^3*x3^2*y1^4 - 6%:R*x1*x2^4%:R*x3^2*y1^4 + 6%:R*x2^5*x3^2*y1^4 -
16%:R*x1^3*x2*x3^3*y1^4 + 36%:R*x1^2*x2^2*x3^3*y1^4 -
16%:R*x1*x2^3*x3^3*y1^4 - 4%:R*x2^4%:R*x3^3*y1^4 + 4%:R*x1^3*x3^4%:R*y1^4 -
 24%:R*x1^2*x2*x3^4%:R*y1^4 + 24%:R*x1*x2^2*x3^4%:R*y1^4 - 4%:R*x2^3*x3^4%:R*y1^4 +
6%:R*x1^2*x3^5*y1^4 - 12%:R*x1*x2*x3^5*y1^4 + 6%:R*x2^2*x3^5*y1^4 +
2%:R*x1*x3^6%:R*y1^4 - 2%:R*x2*x3^6%:R*y1^4 - x2^4%:R*y1^6 + 4%:R*x2^3*x3*y1^6 -
6%:R*x2^2*x3^2*y1^6 + 4%:R*x2*x3^3*y1^6 - x3^4%:R*y1^6 + 8%:R*x1^6%:R*x2^4%:R*y1*y2
- 2%:R*x1^5*x2^5*y1*y2 - 16%:R*x1^4%:R*x2^6%:R*y1*y2 + 4%:R*x1^3*x2^7%:R*y1*y2 +
 8%:R*x1^2*x2^ 8%:R*y1*y2 - 2%:R*x1*x2^9%:R*y1*y2 - 26%:R*x1^6%:R*x2^3*x3*y1*y2 +
16%:R*x1^5*x2^4%:R*x3*y1*y2 + 34%:R*x1^4%:R*x2^5*x3*y1*y2 -
12%:R*x1^3*x2^6%:R*x3*y1*y2 - 10%:R*x1^2*x2^7%:R*x3*y1*y2 -
4%:R*x1*x2^ 8%:R*x3*y1*y2 + 2%:R*x2^9%:R*x3*y1*y2 + 30%:R*x1^6%:R*x2^2*x3^2*y1*y2 -
44%:R*x1^5*x2^3*x3^2*y1*y2 - 8%:R*x1^4%:R*x2^4%:R*x3^2*y1*y2 +
22%:R*x1^3*x2^5*x3^2*y1*y2 + 2%:R*x1^2*x2^6%:R*x3^2*y1*y2 +
2%:R*x1*x2^7%:R*x3^2*y1*y2 - 4%:R*x2^ 8%:R*x3^2*y1*y2 - 14%:R*x1^6%:R*x2*x3^3*y1*y2
+ 56%:R*x1^5*x2^2*x3^3*y1*y2 - 24%:R*x1^4%:R*x2^3*x3^3*y1*y2 -
32%:R*x1^3*x2^4%:R*x3^3*y1*y2 - 14%:R*x1^2*x2^5*x3^3*y1*y2 +
 24%:R*x1*x2^6%:R*x3^3*y1*y2 + 4%:R*x2^7%:R*x3^3*y1*y2 + 2%:R*x1^6%:R*x3^4%:R*y1*y2 -
34%:R*x1^5*x2*x3^4%:R*y1*y2 + 20%:R*x1^4%:R*x2^2*x3^4%:R*y1*y2 +
32%:R*x1^3*x2^3*x3^4%:R*y1*y2 + 4%:R*x1^2*x2^4%:R*x3^4%:R*y1*y2 -
26%:R*x1*x2^5*x3^4%:R*y1*y2 + 2%:R*x2^6%:R*x3^4%:R*y1*y2 + 8%:R*x1^5*x3^5*y1*y2 -
10%:R*x1^4%:R*x2*x3^5*y1*y2 - 28%:R*x1^3*x2^2*x3^5*y1*y2 +
40%:R*x1^2*x2^3*x3^5*y1*y2 + 4%:R*x1*x2^4%:R*x3^5*y1*y2 -
14%:R*x2^5*x3^5*y1*y2 + 4%:R*x1^4%:R*x3^6%:R*y1*y2 + 22%:R*x1^3*x2*x3^6%:R*y1*y2 -
48%:R*x1^2*x2^2*x3^6%:R*y1*y2 + 14%:R*x1*x2^3*x3^6%:R*y1*y2 +
 8%:R*x2^4%:R*x3^6%:R*y1*y2 - 8%:R*x1^3*x3^7%:R*y1*y2 + 24%:R*x1^2*x2*x3^7%:R*y1*y2 -
 24%:R*x1*x2^2*x3^7%:R*y1*y2 + 8%:R*x2^3*x3^7%:R*y1*y2 - 6%:R*x1^2*x3^ 8%:R*y1*y2 +
12%:R*x1*x2*x3^ 8%:R*y1*y2 - 6%:R*x2^2*x3^ 8%:R*y1*y2 - 14%:R*x1^3*x2^4%:R*y1^3*y2 +
2%:R*x1^2*x2^5*y1^3*y2 + 14%:R*x1*x2^6%:R*y1^3*y2 - 2%:R*x2^7%:R*y1^3*y2 +
44%:R*x1^3*x2^3*x3*y1^3*y2 - 16%:R*x1^2*x2^4%:R*x3*y1^3*y2 -
28%:R*x1*x2^5*x3*y1^3*y2 - 48%:R*x1^3*x2^2*x3^2*y1^3*y2 +
44%:R*x1^2*x2^3*x3^2*y1^3*y2 + 2%:R*x1*x2^4%:R*x3^2*y1^3*y2 +
2%:R*x2^5*x3^2*y1^3*y2 + 20%:R*x1^3*x2*x3^3*y1^3*y2 -
56%:R*x1^2*x2^2*x3^3*y1^3*y2 + 28%:R*x1*x2^3*x3^3*y1^3*y2 +
 8%:R*x2^4%:R*x3^3*y1^3*y2 - 2%:R*x1^3*x3^4%:R*y1^3*y2 +
34%:R*x1^2*x2*x3^4%:R*y1^3*y2 - 26%:R*x1*x2^2*x3^4%:R*y1^3*y2 -
6%:R*x2^3*x3^4%:R*y1^3*y2 - 8%:R*x1^2*x3^5*y1^3*y2 + 16%:R*x1*x2*x3^5*y1^3*y2
- 8%:R*x2^2*x3^5*y1^3*y2 - 6%:R*x1*x3^6%:R*y1^3*y2 + 6%:R*x2*x3^6%:R*y1^3*y2 +
6%:R*x2^4%:R*y1^5*y2 - 18%:R*x2^3*x3*y1^5*y2 + 18%:R*x2^2*x3^2*y1^5*y2 -
6%:R*x2*x3^3*y1^5*y2 - 3%:R*x1^ 8%:R*x2^2*y2^2 + 4%:R*x1^7%:R*x2^3*y2^2 +
6%:R*x1^6%:R*x2^4%:R*y2^2 - 12%:R*x1^5*x2^5*y2^2 - 3%:R*x1^4%:R*x2^6%:R*y2^2 +
12%:R*x1^3*x2^7%:R*y2^2 - 4%:R*x1*x2^9%:R*y2^2 + 6%:R*x1^ 8%:R*x2*x3*y2^2 -
12%:R*x1^7%:R*x2^2*x3*y2^2 + 2%:R*x1^6%:R*x2^3*x3*y2^2 + 18%:R*x1^5*x2^4%:R*x3*y2^2
- 12%:R*x1^4%:R*x2^5*x3*y2^2 - 6%:R*x1^3*x2^6%:R*x3*y2^2 + 4%:R*x2^9%:R*x3*y2^2 -
3%:R*x1^ 8%:R*x3^2*y2^2 + 12%:R*x1^7%:R*x2*x3^2*y2^2 - 21%:R*x1^6%:R*x2^2*x3^2*y2^2
+ 6%:R*x1^5*x2^3*x3^2*y2^2 + 18%:R*x1^4%:R*x2^4%:R*x3^2*y2^2 -
12%:R*x1^3*x2^5*x3^2*y2^2 - 4%:R*x1^7%:R*x3^3*y2^2 + 12%:R*x1^6%:R*x2*x3^3*y2^2
- 18%:R*x1^5*x2^2*x3^3*y2^2 + 4%:R*x1^4%:R*x2^3*x3^3*y2^2 +
12%:R*x1^2*x2^5*x3^3*y2^2 + 6%:R*x1*x2^6%:R*x3^3*y2^2 - 12%:R*x2^7%:R*x3^3*y2^2
+ x1^6%:R*x3^4%:R*y2^2 + 6%:R*x1^5*x2*x3^4%:R*y2^2 - 4%:R*x1^3*x2^3*x3^4%:R*y2^2 -
18%:R*x1^2*x2^4%:R*x3^4%:R*y2^2 + 12%:R*x1*x2^5*x3^4%:R*y2^2 + 3%:R*x2^6%:R*x3^4%:R*y2^2
- 6%:R*x1^4%:R*x2*x3^5*y2^2 + 18%:R*x1^3*x2^2*x3^5*y2^2 -
6%:R*x1^2*x2^3*x3^5*y2^2 - 18%:R*x1*x2^4%:R*x3^5*y2^2 + 12%:R*x2^5*x3^5*y2^2
- x1^4%:R*x3^6%:R*y2^2 - 12%:R*x1^3*x2*x3^6%:R*y2^2 + 21%:R*x1^2*x2^2*x3^6%:R*y2^2
- 2%:R*x1*x2^3*x3^6%:R*y2^2 - 6%:R*x2^4%:R*x3^6%:R*y2^2 + 4%:R*x1^3*x3^7%:R*y2^2 -
12%:R*x1^2*x2*x3^7%:R*y2^2 + 12%:R*x1*x2^2*x3^7%:R*y2^2 - 4%:R*x2^3*x3^7%:R*y2^2 +
3%:R*x1^2*x3^ 8%:R*y2^2 - 6%:R*x1*x2*x3^ 8%:R*y2^2 + 3%:R*x2^2*x3^ 8%:R*y2^2 +
6%:R*x1^5*x2^2*y1^2*y2^2 - 6%:R*x1^4%:R*x2^3*y1^2*y2^2 +
4%:R*x1^3*x2^4%:R*y1^2*y2^2 + 8%:R*x1^2*x2^5*y1^2*y2^2 -
10%:R*x1*x2^6%:R*y1^2*y2^2 - 2%:R*x2^7%:R*y1^2*y2^2 - 12%:R*x1^5*x2*x3*y1^2*y2^2
+ 18%:R*x1^4%:R*x2^2*x3*y1^2*y2^2 - 28%:R*x1^3*x2^3*x3*y1^2*y2^2 -
10%:R*x1^2*x2^4%:R*x3*y1^2*y2^2 + 20%:R*x1*x2^5*x3*y1^2*y2^2 +
12%:R*x2^6%:R*x3*y1^2*y2^2 + 6%:R*x1^5*x3^2*y1^2*y2^2 -
18%:R*x1^4%:R*x2*x3^2*y1^2*y2^2 + 36%:R*x1^3*x2^2*x3^2*y1^2*y2^2 -
4%:R*x1^2*x2^3*x3^2*y1^2*y2^2 - 4%:R*x1*x2^4%:R*x3^2*y1^2*y2^2 -
16%:R*x2^5*x3^2*y1^2*y2^2 + 6%:R*x1^4%:R*x3^3*y1^2*y2^2 -
4%:R*x1^3*x2*x3^3*y1^2*y2^2 + 4%:R*x1^2*x2^2*x3^3*y1^2*y2^2 +
4%:R*x1*x2^3*x3^3*y1^2*y2^2 - 10%:R*x2^4%:R*x3^3*y1^2*y2^2 -
 8%:R*x1^3*x3^4%:R*y1^2*y2^2 + 4%:R*x1^2*x2*x3^4%:R*y1^2*y2^2 -
20%:R*x1*x2^2*x3^4%:R*y1^2*y2^2 + 24%:R*x2^3*x3^4%:R*y1^2*y2^2 -
2%:R*x1^2*x3^5*y1^2*y2^2 + 4%:R*x1*x2*x3^5*y1^2*y2^2 -
2%:R*x2^2*x3^5*y1^2*y2^2 + 6%:R*x1*x3^6%:R*y1^2*y2^2 - 6%:R*x2*x3^6%:R*y1^2*y2^2
- 3%:R*x1^2*x2^2*y1^4%:R*y2^2 + 2%:R*x1*x2^3*y1^4%:R*y2^2 - 10%:R*x2^4%:R*y1^4%:R*y2^2
+ 6%:R*x1^2*x2*x3*y1^4%:R*y2^2 - 6%:R*x1*x2^2*x3*y1^4%:R*y2^2 +
26%:R*x2^3*x3*y1^4%:R*y2^2 - 3%:R*x1^2*x3^2*y1^4%:R*y2^2 +
6%:R*x1*x2*x3^2*y1^4%:R*y2^2 - 15%:R*x2^2*x3^2*y1^4%:R*y2^2 -
2%:R*x1*x3^3*y1^4%:R*y2^2 - 8%:R*x2*x3^3*y1^4%:R*y2^2 + 7%:R*x3^4%:R*y1^4%:R*y2^2 -
2%:R*x1^6%:R*x2*y1*y2^3 - 4%:R*x1^5*x2^2*y1*y2^3 + 14%:R*x1^4%:R*x2^3*y1*y2^3 -
6%:R*x1^3*x2^4%:R*y1*y2^3 - 12%:R*x1^2*x2^5*y1*y2^3 + 10%:R*x1*x2^6%:R*y1*y2^3 +
2%:R*x1^6%:R*x3*y1*y2^3 + 8%:R*x1^5*x2*x3*y1*y2^3 -
22%:R*x1^4%:R*x2^2*x3*y1*y2^3 + 16%:R*x1^3*x2^3*x3*y1*y2^3 +
6%:R*x1^2*x2^4%:R*x3*y1*y2^3 - 10%:R*x2^6%:R*x3*y1*y2^3 - 4%:R*x1^5*x3^2*y1*y2^3
+ 14%:R*x1^4%:R*x2*x3^2*y1*y2^3 - 16%:R*x1^3*x2^2*x3^2*y1*y2^3 -
6%:R*x1*x2^4%:R*x3^2*y1*y2^3 + 12%:R*x2^5*x3^2*y1*y2^3 -
6%:R*x1^4%:R*x3^3*y1*y2^3 + 16%:R*x1^2*x2^2*x3^3*y1*y2^3 -
16%:R*x1*x2^3*x3^3*y1*y2^3 + 6%:R*x2^4%:R*x3^3*y1*y2^3 +
6%:R*x1^3*x3^4%:R*y1*y2^3 - 14%:R*x1^2*x2*x3^4%:R*y1*y2^3 +
22%:R*x1*x2^2*x3^4%:R*y1*y2^3 - 14%:R*x2^3*x3^4%:R*y1*y2^3 +
4%:R*x1^2*x3^5*y1*y2^3 - 8%:R*x1*x2*x3^5*y1*y2^3 + 4%:R*x2^2*x3^5*y1*y2^3
- 2%:R*x1*x3^6%:R*y1*y2^3 + 2%:R*x2*x3^6%:R*y1*y2^3 + 4%:R*x1^3*x2*y1^3*y2^3 +
4%:R*x1^2*x2^2*y1^3*y2^3 - 12%:R*x1*x2^3*y1^3*y2^3 + 8%:R*x2^4%:R*y1^3*y2^3 -
4%:R*x1^3*x3*y1^3*y2^3 - 8%:R*x1^2*x2*x3*y1^3*y2^3 +
16%:R*x1*x2^2*x3*y1^3*y2^3 - 8%:R*x2^3*x3*y1^3*y2^3 +
4%:R*x1^2*x3^2*y1^3*y2^3 - 8%:R*x1*x2*x3^2*y1^3*y2^3 -
 8%:R*x2^2*x3^2*y1^3*y2^3 + 4%:R*x1*x3^3*y1^3*y2^3 +
16%:R*x2*x3^3*y1^3*y2^3 - 8%:R*x3^4%:R*y1^3*y2^3 - 2%:R*x2*y1^5*y2^3 +
2%:R*x3*y1^5*y2^3 - 6%:R*x1^3*x2*y1^2*y2^4 + x1^2*x2^2*y1^2*y2^4 +
16%:R*x1*x2^3*y1^2*y2^4 - 2%:R*x2^4%:R*y1^2*y2^4 + 6%:R*x1^3*x3*y1^2*y2^4 -
2%:R*x1^2*x2*x3*y1^2*y2^4 - 14%:R*x1*x2^2*x3*y1^2*y2^4 -
14%:R*x2^3*x3*y1^2*y2^4 + x1^2*x3^2*y1^2*y2^4 -
2%:R*x1*x2*x3^2*y1^2*y2^4 + 19%:R*x2^2*x3^2*y1^2*y2^4 -
3%:R*x3^4%:R*y1^2*y2^4 + 6%:R*x2*y1^4%:R*y2^4 - 6%:R*x3*y1^4%:R*y2^4 -
2%:R*x1^4%:R*y1*y2^5 + 2%:R*x1^3*x2*y1*y2^5 + 4%:R*x1^2*x2^2*y1*y2^5 -
14%:R*x1*x2^3*y1*y2^5 + 4%:R*x1^2*x2*x3*y1*y2^5 + 4%:R*x1*x2^2*x3*y1*y2^5
+ 14%:R*x2^3*x3*y1*y2^5 - 2%:R*x1^2*x3^2*y1*y2^5 + 4%:R*x1*x2*x3^2*y1*y2^5
- 8%:R*x2^2*x3^2*y1*y2^5 - 4%:R*x1*x3^3*y1*y2^5 - 10%:R*x2*x3^3*y1*y2^5 +
 8%:R*x3^4%:R*y1*y2^5 + 2%:R*x1*y1^3*y2^5 - 6%:R*x2*y1^3*y2^5 + 4%:R*x3*y1^3*y2^5
+ 3%:R*x1^4%:R*y2^6 - 4%:R*x1^3*x2*y2^6 + 4%:R*x1*x2^3*y2^6 - 2%:R*x1^3*x3*y2^6
- 4%:R*x2^3*x3*y2^6 + 2%:R*x1*x3^3*y2^6 + 4%:R*x2*x3^3*y2^6 - 3%:R*x3^4%:R*y2^6
- 6%:R*x1*y1^2*y2^6 + 2%:R*x2*y1^2*y2^6 + 4%:R*x3*y1^2*y2^6 + 6%:R*x1*y1*y2^7
- 6%:R*x3*y1*y2^7 - 2%:R*x1*y2^8 + 2%:R*x3*y2^8 - 6%:R*x1^6%:R*x2^4%:R*y1*y3 +
6%:R*x1^5*x2^5*y1*y3 + 12%:R*x1^4%:R*x2^6%:R*y1*y3 - 12%:R*x1^3*x2^7%:R*y1*y3 -
6%:R*x1^2*x2^ 8%:R*y1*y3 + 6%:R*x1*x2^9%:R*y1*y3 + 18%:R*x1^6%:R*x2^3*x3*y1*y3 -
 24%:R*x1^5*x2^4%:R*x3*y1*y3 - 18%:R*x1^4%:R*x2^5*x3*y1*y3 +
 24%:R*x1^3*x2^6%:R*x3*y1*y3 + 6%:R*x1^2*x2^7%:R*x3*y1*y3 - 6%:R*x2^9%:R*x3*y1*y3 -
18%:R*x1^6%:R*x2^2*x3^2*y1*y3 + 36%:R*x1^5*x2^3*x3^2*y1*y3 -
12%:R*x1^4%:R*x2^4%:R*x3^2*y1*y3 - 6%:R*x1^3*x2^5*x3^2*y1*y3 -
6%:R*x1*x2^7%:R*x3^2*y1*y3 + 6%:R*x2^ 8%:R*x3^2*y1*y3 + 6%:R*x1^6%:R*x2*x3^3*y1*y3 -
 24%:R*x1^5*x2^2*x3^3*y1*y3 + 24%:R*x1^4%:R*x2^3*x3^3*y1*y3 +
6%:R*x1^2*x2^5*x3^3*y1*y3 - 24%:R*x1*x2^6%:R*x3^3*y1*y3 +
12%:R*x2^7%:R*x3^3*y1*y3 + 6%:R*x1^5*x2*x3^4%:R*y1*y3 -
 24%:R*x1^3*x2^3*x3^4%:R*y1*y3 + 12%:R*x1^2*x2^4%:R*x3^4%:R*y1*y3 +
18%:R*x1*x2^5*x3^4%:R*y1*y3 - 12%:R*x2^6%:R*x3^4%:R*y1*y3 - 6%:R*x1^4%:R*x2*x3^5*y1*y3
+ 24%:R*x1^3*x2^2*x3^5*y1*y3 - 36%:R*x1^2*x2^3*x3^5*y1*y3 +
 24%:R*x1*x2^4%:R*x3^5*y1*y3 - 6%:R*x2^5*x3^5*y1*y3 - 6%:R*x1^3*x2*x3^6%:R*y1*y3
+ 18%:R*x1^2*x2^2*x3^6%:R*y1*y3 - 18%:R*x1*x2^3*x3^6%:R*y1*y3 +
6%:R*x2^4%:R*x3^6%:R*y1*y3 + 10%:R*x1^3*x2^4%:R*y1^3*y3 - 6%:R*x1^2*x2^5*y1^3*y3 -
10%:R*x1*x2^6%:R*y1^3*y3 + 6%:R*x2^7%:R*y1^3*y3 - 28%:R*x1^3*x2^3*x3*y1^3*y3 +
 24%:R*x1^2*x2^4%:R*x3*y1^3*y3 + 12%:R*x1*x2^5*x3*y1^3*y3 -
 8%:R*x2^6%:R*x3*y1^3*y3 + 24%:R*x1^3*x2^2*x3^2*y1^3*y3 -
36%:R*x1^2*x2^3*x3^2*y1^3*y3 + 18%:R*x1*x2^4%:R*x3^2*y1^3*y3 -
6%:R*x2^5*x3^2*y1^3*y3 - 4%:R*x1^3*x2*x3^3*y1^3*y3 +
 24%:R*x1^2*x2^2*x3^3*y1^3*y3 - 28%:R*x1*x2^3*x3^3*y1^3*y3 +
 8%:R*x2^4%:R*x3^3*y1^3*y3 - 2%:R*x1^3*x3^4%:R*y1^3*y3 -
6%:R*x1^2*x2*x3^4%:R*y1^3*y3 + 6%:R*x1*x2^2*x3^4%:R*y1^3*y3 +
2%:R*x2^3*x3^4%:R*y1^3*y3 + 2%:R*x1*x3^6%:R*y1^3*y3 - 2%:R*x2*x3^6%:R*y1^3*y3 -
4%:R*x2^4%:R*y1^5*y3 + 10%:R*x2^3*x3*y1^5*y3 - 6%:R*x2^2*x3^2*y1^5*y3 -
2%:R*x2*x3^3*y1^5*y3 + 2%:R*x3^4%:R*y1^5*y3 + 6%:R*x1^ 8%:R*x2^2*y2*y3 -
 8%:R*x1^7%:R*x2^3*y2*y3 - 8%:R*x1^6%:R*x2^4%:R*y2*y3 + 14%:R*x1^5*x2^5*y2*y3 -
2%:R*x1^4%:R*x2^6%:R*y2*y3 - 4%:R*x1^3*x2^7%:R*y2*y3 + 4%:R*x1^2*x2^ 8%:R*y2*y3 -
2%:R*x1*x2^9%:R*y2*y3 - 12%:R*x1^ 8%:R*x2*x3*y2*y3 + 24%:R*x1^7%:R*x2^2*x3*y2*y3 -
14%:R*x1^6%:R*x2^3*x3*y2*y3 - 4%:R*x1^5*x2^4%:R*x3*y2*y3 +
26%:R*x1^4%:R*x2^5*x3*y2*y3 - 24%:R*x1^3*x2^6%:R*x3*y2*y3 -
2%:R*x1^2*x2^7%:R*x3*y2*y3 + 4%:R*x1*x2^ 8%:R*x3*y2*y3 + 2%:R*x2^9%:R*x3*y2*y3 +
6%:R*x1^ 8%:R*x3^2*y2*y3 - 24%:R*x1^7%:R*x2*x3^2*y2*y3 +
48%:R*x1^6%:R*x2^2*x3^2*y2*y3 - 40%:R*x1^5*x2^3*x3^2*y2*y3 -
4%:R*x1^4%:R*x2^4%:R*x3^2*y2*y3 + 14%:R*x1^3*x2^5*x3^2*y2*y3 -
2%:R*x1^2*x2^6%:R*x3^2*y2*y3 + 10%:R*x1*x2^7%:R*x3^2*y2*y3 -
 8%:R*x2^ 8%:R*x3^2*y2*y3 + 8%:R*x1^7%:R*x3^3*y2*y3 - 22%:R*x1^6%:R*x2*x3^3*y2*y3 +
28%:R*x1^5*x2^2*x3^3*y2*y3 - 32%:R*x1^4%:R*x2^3*x3^3*y2*y3 +
32%:R*x1^3*x2^4%:R*x3^3*y2*y3 - 22%:R*x1^2*x2^5*x3^3*y2*y3 +
12%:R*x1*x2^6%:R*x3^3*y2*y3 - 4%:R*x2^7%:R*x3^3*y2*y3 - 4%:R*x1^6%:R*x3^4%:R*y2*y3 +
10%:R*x1^5*x2*x3^4%:R*y2*y3 - 20%:R*x1^4%:R*x2^2*x3^4%:R*y2*y3 +
 24%:R*x1^3*x2^3*x3^4%:R*y2*y3 + 8%:R*x1^2*x2^4%:R*x3^4%:R*y2*y3 -
34%:R*x1*x2^5*x3^4%:R*y2*y3 + 16%:R*x2^6%:R*x3^4%:R*y2*y3 - 8%:R*x1^5*x3^5*y2*y3 +
34%:R*x1^4%:R*x2*x3^5*y2*y3 - 56%:R*x1^3*x2^2*x3^5*y2*y3 +
44%:R*x1^2*x2^3*x3^5*y2*y3 - 16%:R*x1*x2^4%:R*x3^5*y2*y3 +
2%:R*x2^5*x3^5*y2*y3 - 2%:R*x1^4%:R*x3^6%:R*y2*y3 + 14%:R*x1^3*x2*x3^6%:R*y2*y3 -
30%:R*x1^2*x2^2*x3^6%:R*y2*y3 + 26%:R*x1*x2^3*x3^6%:R*y2*y3 -
 8%:R*x2^4%:R*x3^6%:R*y2*y3 - 12%:R*x1^5*x2^2*y1^2*y2*y3 +
12%:R*x1^4%:R*x2^3*y1^2*y2*y3 - 2%:R*x1^3*x2^4%:R*y1^2*y2*y3 -
10%:R*x1^2*x2^5*y1^2*y2*y3 + 14%:R*x1*x2^6%:R*y1^2*y2*y3 -
2%:R*x2^7%:R*y1^2*y2*y3 + 24%:R*x1^5*x2*x3*y1^2*y2*y3 -
36%:R*x1^4%:R*x2^2*x3*y1^2*y2*y3 + 44%:R*x1^3*x2^3*x3*y1^2*y2*y3 -
4%:R*x1^2*x2^4%:R*x3*y1^2*y2*y3 - 28%:R*x1*x2^5*x3*y1^2*y2*y3 -
12%:R*x1^5*x3^2*y1^2*y2*y3 + 36%:R*x1^4%:R*x2*x3^2*y1^2*y2*y3 -
72%:R*x1^3*x2^2*x3^2*y1^2*y2*y3 + 44%:R*x1^2*x2^3*x3^2*y1^2*y2*y3 -
10%:R*x1*x2^4%:R*x3^2*y1^2*y2*y3 + 14%:R*x2^5*x3^2*y1^2*y2*y3 -
12%:R*x1^4%:R*x3^3*y1^2*y2*y3 + 20%:R*x1^3*x2*x3^3*y1^2*y2*y3 -
32%:R*x1^2*x2^2*x3^3*y1^2*y2*y3 + 28%:R*x1*x2^3*x3^3*y1^2*y2*y3 -
4%:R*x2^4%:R*x3^3*y1^2*y2*y3 + 10%:R*x1^3*x3^4%:R*y1^2*y2*y3 -
2%:R*x1^2*x2*x3^4%:R*y1^2*y2*y3 + 10%:R*x1*x2^2*x3^4%:R*y1^2*y2*y3 -
18%:R*x2^3*x3^4%:R*y1^2*y2*y3 + 4%:R*x1^2*x3^5*y1^2*y2*y3 -
 8%:R*x1*x2*x3^5*y1^2*y2*y3 + 4%:R*x2^2*x3^5*y1^2*y2*y3 -
6%:R*x1*x3^6%:R*y1^2*y2*y3 + 6%:R*x2*x3^6%:R*y1^2*y2*y3 +
6%:R*x1^2*x2^2*y1^4%:R*y2*y3 - 4%:R*x1*x2^3*y1^4%:R*y2*y3 +
10%:R*x2^4%:R*y1^4%:R*y2*y3 - 12%:R*x1^2*x2*x3*y1^4%:R*y2*y3 +
12%:R*x1*x2^2*x3*y1^4%:R*y2*y3 - 30%:R*x2^3*x3*y1^4%:R*y2*y3 +
6%:R*x1^2*x3^2*y1^4%:R*y2*y3 - 12%:R*x1*x2*x3^2*y1^4%:R*y2*y3 +
 24%:R*x2^2*x3^2*y1^4%:R*y2*y3 + 4%:R*x1*x3^3*y1^4%:R*y2*y3 +
2%:R*x2*x3^3*y1^4%:R*y2*y3 - 6%:R*x3^4%:R*y1^4%:R*y2*y3 + 6%:R*x1^6%:R*x2*y1*y2^2*y3 +
 8%:R*x1^5*x2^2*y1*y2^2*y3 - 30%:R*x1^4%:R*x2^3*y1*y2^2*y3 +
14%:R*x1^3*x2^4%:R*y1*y2^2*y3 + 24%:R*x1^2*x2^5*y1*y2^2*y3 -
22%:R*x1*x2^6%:R*y1*y2^2*y3 - 6%:R*x1^6%:R*x3*y1*y2^2*y3 -
16%:R*x1^5*x2*x3*y1*y2^2*y3 + 38%:R*x1^4%:R*x2^2*x3*y1*y2^2*y3 -
32%:R*x1^3*x2^3*x3*y1*y2^2*y3 - 6%:R*x1^2*x2^4%:R*x3*y1*y2^2*y3 +
22%:R*x2^6%:R*x3*y1*y2^2*y3 + 8%:R*x1^5*x3^2*y1*y2^2*y3 -
22%:R*x1^4%:R*x2*x3^2*y1*y2^2*y3 + 32%:R*x1^3*x2^2*x3^2*y1*y2^2*y3 +
6%:R*x1*x2^4%:R*x3^2*y1*y2^2*y3 - 24%:R*x2^5*x3^2*y1*y2^2*y3 +
14%:R*x1^4%:R*x3^3*y1*y2^2*y3 - 32%:R*x1^2*x2^2*x3^3*y1*y2^2*y3 +
32%:R*x1*x2^3*x3^3*y1*y2^2*y3 - 14%:R*x2^4%:R*x3^3*y1*y2^2*y3 -
14%:R*x1^3*x3^4%:R*y1*y2^2*y3 + 22%:R*x1^2*x2*x3^4%:R*y1*y2^2*y3 -
38%:R*x1*x2^2*x3^4%:R*y1*y2^2*y3 + 30%:R*x2^3*x3^4%:R*y1*y2^2*y3 -
 8%:R*x1^2*x3^5*y1*y2^2*y3 + 16%:R*x1*x2*x3^5*y1*y2^2*y3 -
 8%:R*x2^2*x3^5*y1*y2^2*y3 + 6%:R*x1*x3^6%:R*y1*y2^2*y3 -
6%:R*x2*x3^6%:R*y1*y2^2*y3 - 12%:R*x1^3*x2*y1^3*y2^2*y3 -
 8%:R*x1^2*x2^2*y1^3*y2^2*y3 + 28%:R*x1*x2^3*y1^3*y2^2*y3 -
16%:R*x2^4%:R*y1^3*y2^2*y3 + 12%:R*x1^3*x3*y1^3*y2^2*y3 +
16%:R*x1^2*x2*x3*y1^3*y2^2*y3 - 32%:R*x1*x2^2*x3*y1^3*y2^2*y3 +
 24%:R*x2^3*x3*y1^3*y2^2*y3 - 8%:R*x1^2*x3^2*y1^3*y2^2*y3 +
16%:R*x1*x2*x3^2*y1^3*y2^2*y3 - 20%:R*x2^2*x3^2*y1^3*y2^2*y3 -
12%:R*x1*x3^3*y1^3*y2^2*y3 + 8%:R*x2*x3^3*y1^3*y2^2*y3 +
4%:R*x3^4%:R*y1^3*y2^2*y3 + 6%:R*x2*y1^5*y2^2*y3 - 6%:R*x3*y1^5*y2^2*y3 -
2%:R*x1^6%:R*x2*y2^3*y3 - 4%:R*x1^5*x2^2*y2^3*y3 + 14%:R*x1^4%:R*x2^3*y2^3*y3 -
6%:R*x1^3*x2^4%:R*y2^3*y3 - 12%:R*x1^2*x2^5*y2^3*y3 + 10%:R*x1*x2^6%:R*y2^3*y3 +
2%:R*x1^6%:R*x3*y2^3*y3 + 8%:R*x1^5*x2*x3*y2^3*y3 -
22%:R*x1^4%:R*x2^2*x3*y2^3*y3 + 16%:R*x1^3*x2^3*x3*y2^3*y3 +
6%:R*x1^2*x2^4%:R*x3*y2^3*y3 - 10%:R*x2^6%:R*x3*y2^3*y3 - 4%:R*x1^5*x3^2*y2^3*y3
+ 14%:R*x1^4%:R*x2*x3^2*y2^3*y3 - 16%:R*x1^3*x2^2*x3^2*y2^3*y3 -
6%:R*x1*x2^4%:R*x3^2*y2^3*y3 + 12%:R*x2^5*x3^2*y2^3*y3 -
6%:R*x1^4%:R*x3^3*y2^3*y3 + 16%:R*x1^2*x2^2*x3^3*y2^3*y3 -
16%:R*x1*x2^3*x3^3*y2^3*y3 + 6%:R*x2^4%:R*x3^3*y2^3*y3 +
6%:R*x1^3*x3^4%:R*y2^3*y3 - 14%:R*x1^2*x2*x3^4%:R*y2^3*y3 +
22%:R*x1*x2^2*x3^4%:R*y2^3*y3 - 14%:R*x2^3*x3^4%:R*y2^3*y3 +
4%:R*x1^2*x3^5*y2^3*y3 - 8%:R*x1*x2*x3^5*y2^3*y3 + 4%:R*x2^2*x3^5*y2^3*y3
- 2%:R*x1*x3^6%:R*y2^3*y3 + 2%:R*x2*x3^6%:R*y2^3*y3 + 20%:R*x1^3*x2*y1^2*y2^3*y3
- 36%:R*x1*x2^3*y1^2*y2^3*y3 + 8%:R*x2^4%:R*y1^2*y2^3*y3 -
20%:R*x1^3*x3*y1^2*y2^3*y3 + 24%:R*x1*x2^2*x3*y1^2*y2^3*y3 +
16%:R*x2^3*x3*y1^2*y2^3*y3 - 12%:R*x2^2*x3^2*y1^2*y2^3*y3 +
12%:R*x1*x3^3*y1^2*y2^3*y3 - 16%:R*x2*x3^3*y1^2*y2^3*y3 +
4%:R*x3^4%:R*y1^2*y2^3*y3 - 18%:R*x2*y1^4%:R*y2^3*y3 + 18%:R*x3*y1^4%:R*y2^3*y3 +
6%:R*x1^4%:R*y1*y2^4%:R*y3 - 10%:R*x1^3*x2*y1*y2^4%:R*y3 -
18%:R*x1^2*x2^2*y1*y2^4%:R*y3 + 34%:R*x1*x2^3*y1*y2^4%:R*y3 +
4%:R*x1^3*x3*y1*y2^4%:R*y3 - 34%:R*x2^3*x3*y1*y2^4%:R*y3 +
18%:R*x2^2*x3^2*y1*y2^4%:R*y3 - 4%:R*x1*x3^3*y1*y2^4%:R*y3 +
10%:R*x2*x3^3*y1*y2^4%:R*y3 - 6%:R*x3^4%:R*y1*y2^4%:R*y3 - 6%:R*x1*y1^3*y2^4%:R*y3 +
18%:R*x2*y1^3*y2^4%:R*y3 - 12%:R*x3*y1^3*y2^4%:R*y3 - 8%:R*x1^4%:R*y2^5*y3 +
10%:R*x1^3*x2*y2^5*y3 + 8%:R*x1^2*x2^2*y2^5*y3 - 14%:R*x1*x2^3*y2^5*y3 +
4%:R*x1^3*x3*y2^5*y3 - 4%:R*x1^2*x2*x3*y2^5*y3 - 4%:R*x1*x2^2*x3*y2^5*y3 +
14%:R*x2^3*x3*y2^5*y3 + 2%:R*x1^2*x3^2*y2^5*y3 - 4%:R*x1*x2*x3^2*y2^5*y3 -
4%:R*x2^2*x3^2*y2^5*y3 - 2%:R*x2*x3^3*y2^5*y3 + 2%:R*x3^4%:R*y2^5*y3 +
18%:R*x1*y1^2*y2^5*y3 - 6%:R*x2*y1^2*y2^5*y3 - 12%:R*x3*y1^2*y2^5*y3 -
18%:R*x1*y1*y2^6%:R*y3 + 18%:R*x3*y1*y2^6%:R*y3 + 6%:R*x1*y2^7%:R*y3 - 6%:R*x3*y2^7%:R*y3
- 3%:R*x1^ 8%:R*x2^2*y3^2 + 4%:R*x1^7%:R*x2^3*y3^2 + 5%:R*x1^6%:R*x2^4%:R*y3^2 -
6%:R*x1^5*x2^5*y3^2 - 3%:R*x1^4%:R*x2^6%:R*y3^2 + 3%:R*x1^2*x2^ 8%:R*y3^2 +
2%:R*x1*x2^9%:R*y3^2 - 2%:R*x2^10%:R*y3^2 + 6%:R*x1^ 8%:R*x2*x3*y3^2 -
12%:R*x1^7%:R*x2^2*x3*y3^2 + 6%:R*x1^5*x2^4%:R*x3*y3^2 + 6%:R*x1^4%:R*x2^5*x3*y3^2
- 12%:R*x1^2*x2^7%:R*x3*y3^2 + 6%:R*x1*x2^ 8%:R*x3*y3^2 - 3%:R*x1^ 8%:R*x3^2*y3^2 +
12%:R*x1^7%:R*x2*x3^2*y3^2 - 9%:R*x1^6%:R*x2^2*x3^2*y3^2 -
6%:R*x1^5*x2^3*x3^2*y3^2 - 12%:R*x1^4%:R*x2^4%:R*x3^2*y3^2 +
36%:R*x1^3*x2^5*x3^2*y3^2 - 9%:R*x1^2*x2^6%:R*x3^2*y3^2 -
18%:R*x1*x2^7%:R*x3^2*y3^2 + 9%:R*x2^ 8%:R*x3^2*y3^2 - 4%:R*x1^7%:R*x3^3*y3^2 -
2%:R*x1^6%:R*x2*x3^3*y3^2 + 30%:R*x1^5*x2^2*x3^3*y3^2 -
20%:R*x1^4%:R*x2^3*x3^3*y3^2 - 40%:R*x1^3*x2^4%:R*x3^3*y3^2 +
54%:R*x1^2*x2^5*x3^3*y3^2 - 18%:R*x1*x2^6%:R*x3^3*y3^2 + 6%:R*x1^6%:R*x3^4%:R*y3^2
- 36%:R*x1^5*x2*x3^4%:R*y3^2 + 72%:R*x1^4%:R*x2^2*x3^4%:R*y3^2 -
48%:R*x1^3*x2^3*x3^4%:R*y3^2 - 18%:R*x1^2*x2^4%:R*x3^4%:R*y3^2 +
36%:R*x1*x2^5*x3^4%:R*y3^2 - 12%:R*x2^6%:R*x3^4%:R*y3^2 + 12%:R*x1^5*x3^5*y3^2 -
48%:R*x1^4%:R*x2*x3^5*y3^2 + 72%:R*x1^3*x2^2*x3^5*y3^2 -
48%:R*x1^2*x2^3*x3^5*y3^2 + 12%:R*x1*x2^4%:R*x3^5*y3^2 + 5%:R*x1^4%:R*x3^6%:R*y3^2
- 20%:R*x1^3*x2*x3^6%:R*y3^2 + 30%:R*x1^2*x2^2*x3^6%:R*y3^2 -
20%:R*x1*x2^3*x3^6%:R*y3^2 + 5%:R*x2^4%:R*x3^6%:R*y3^2 + 6%:R*x1^5*x2^2*y1^2*y3^2 -
6%:R*x1^4%:R*x2^3*y1^2*y3^2 - 6%:R*x1^3*x2^4%:R*y1^2*y3^2 +
6%:R*x1^2*x2^5*y1^2*y3^2 - 12%:R*x1^5*x2*x3*y1^2*y3^2 +
18%:R*x1^4%:R*x2^2*x3*y1^2*y3^2 - 6%:R*x1^2*x2^4%:R*x3*y1^2*y3^2 +
6%:R*x1^5*x3^2*y1^2*y3^2 - 18%:R*x1^4%:R*x2*x3^2*y1^2*y3^2 +
12%:R*x1^3*x2^2*x3^2*y1^2*y3^2 + 6%:R*x1*x2^4%:R*x3^2*y1^2*y3^2 -
6%:R*x2^5*x3^2*y1^2*y3^2 + 6%:R*x1^4%:R*x3^3*y1^2*y3^2 -
12%:R*x1^2*x2^2*x3^3*y1^2*y3^2 + 6%:R*x2^4%:R*x3^3*y1^2*y3^2 -
6%:R*x1^3*x3^4%:R*y1^2*y3^2 + 18%:R*x1^2*x2*x3^4%:R*y1^2*y3^2 -
18%:R*x1*x2^2*x3^4%:R*y1^2*y3^2 + 6%:R*x2^3*x3^4%:R*y1^2*y3^2 -
6%:R*x1^2*x3^5*y1^2*y3^2 + 12%:R*x1*x2*x3^5*y1^2*y3^2 -
6%:R*x2^2*x3^5*y1^2*y3^2 - 3%:R*x1^2*x2^2*y1^4%:R*y3^2 +
2%:R*x1*x2^3*y1^4%:R*y3^2 + x2^4%:R*y1^4%:R*y3^2 + 6%:R*x1^2*x2*x3*y1^4%:R*y3^2 -
6%:R*x1*x2^2*x3*y1^4%:R*y3^2 - 3%:R*x1^2*x3^2*y1^4%:R*y3^2 +
6%:R*x1*x2*x3^2*y1^4%:R*y3^2 - 3%:R*x2^2*x3^2*y1^4%:R*y3^2 -
2%:R*x1*x3^3*y1^4%:R*y3^2 + 2%:R*x2*x3^3*y1^4%:R*y3^2 - 6%:R*x1^6%:R*x2*y1*y2*y3^2
- 4%:R*x1^5*x2^2*y1*y2*y3^2 + 18%:R*x1^4%:R*x2^3*y1*y2*y3^2 +
4%:R*x1^3*x2^4%:R*y1*y2*y3^2 - 14%:R*x1^2*x2^5*y1*y2*y3^2 +
2%:R*x2^7%:R*y1*y2*y3^2 + 6%:R*x1^6%:R*x3*y1*y2*y3^2 +
 8%:R*x1^5*x2*x3*y1*y2*y3^2 - 10%:R*x1^4%:R*x2^2*x3*y1*y2*y3^2 -
28%:R*x1^3*x2^3*x3*y1*y2*y3^2 + 10%:R*x1^2*x2^4%:R*x3*y1*y2*y3^2 +
28%:R*x1*x2^5*x3*y1*y2*y3^2 - 14%:R*x2^6%:R*x3*y1*y2*y3^2 -
4%:R*x1^5*x3^2*y1*y2*y3^2 + 2%:R*x1^4%:R*x2*x3^2*y1*y2*y3^2 +
32%:R*x1^3*x2^2*x3^2*y1*y2*y3^2 - 44%:R*x1^2*x2^3*x3^2*y1*y2*y3^2 +
4%:R*x1*x2^4%:R*x3^2*y1*y2*y3^2 + 10%:R*x2^5*x3^2*y1*y2*y3^2 -
10%:R*x1^4%:R*x3^3*y1*y2*y3^2 - 20%:R*x1^3*x2*x3^3*y1*y2*y3^2 +
72%:R*x1^2*x2^2*x3^3*y1*y2*y3^2 - 44%:R*x1*x2^3*x3^3*y1*y2*y3^2 +
2%:R*x2^4%:R*x3^3*y1*y2*y3^2 + 12%:R*x1^3*x3^4%:R*y1*y2*y3^2 -
36%:R*x1^2*x2*x3^4%:R*y1*y2*y3^2 + 36%:R*x1*x2^2*x3^4%:R*y1*y2*y3^2 -
12%:R*x2^3*x3^4%:R*y1*y2*y3^2 + 12%:R*x1^2*x3^5*y1*y2*y3^2 -
 24%:R*x1*x2*x3^5*y1*y2*y3^2 + 12%:R*x2^2*x3^5*y1*y2*y3^2 +
12%:R*x1^3*x2*y1^3*y2*y3^2 + 4%:R*x1^2*x2^2*y1^3*y2*y3^2 -
20%:R*x1*x2^3*y1^3*y2*y3^2 + 4%:R*x2^4%:R*y1^3*y2*y3^2 -
12%:R*x1^3*x3*y1^3*y2*y3^2 - 8%:R*x1^2*x2*x3*y1^3*y2*y3^2 +
16%:R*x1*x2^2*x3*y1^3*y2*y3^2 + 4%:R*x2^3*x3*y1^3*y2*y3^2 +
4%:R*x1^2*x3^2*y1^3*y2*y3^2 - 8%:R*x1*x2*x3^2*y1^3*y2*y3^2 +
4%:R*x2^2*x3^2*y1^3*y2*y3^2 + 12%:R*x1*x3^3*y1^3*y2*y3^2 -
12%:R*x2*x3^3*y1^3*y2*y3^2 - 6%:R*x2*y1^5*y2*y3^2 + 6%:R*x3*y1^5*y2*y3^2 +
6%:R*x1^6%:R*x2*y2^2*y3^2 + 2%:R*x1^5*x2^2*y2^2*y3^2 -
 24%:R*x1^4%:R*x2^3*y2^2*y3^2 + 10%:R*x1^3*x2^4%:R*y2^2*y3^2 +
16%:R*x1^2*x2^5*y2^2*y3^2 - 12%:R*x1*x2^6%:R*y2^2*y3^2 + 2%:R*x2^7%:R*y2^2*y3^2
- 6%:R*x1^6%:R*x3*y2^2*y3^2 - 4%:R*x1^5*x2*x3*y2^2*y3^2 +
20%:R*x1^4%:R*x2^2*x3*y2^2*y3^2 - 4%:R*x1^3*x2^3*x3*y2^2*y3^2 +
4%:R*x1^2*x2^4%:R*x3*y2^2*y3^2 - 20%:R*x1*x2^5*x3*y2^2*y3^2 +
10%:R*x2^6%:R*x3*y2^2*y3^2 + 2%:R*x1^5*x3^2*y2^2*y3^2 -
4%:R*x1^4%:R*x2*x3^2*y2^2*y3^2 - 4%:R*x1^3*x2^2*x3^2*y2^2*y3^2 +
4%:R*x1^2*x2^3*x3^2*y2^2*y3^2 + 10%:R*x1*x2^4%:R*x3^2*y2^2*y3^2 -
 8%:R*x2^5*x3^2*y2^2*y3^2 + 8%:R*x1^4%:R*x3^3*y2^2*y3^2 +
4%:R*x1^3*x2*x3^3*y2^2*y3^2 - 36%:R*x1^2*x2^2*x3^3*y2^2*y3^2 +
28%:R*x1*x2^3*x3^3*y2^2*y3^2 - 4%:R*x2^4%:R*x3^3*y2^2*y3^2 -
6%:R*x1^3*x3^4%:R*y2^2*y3^2 + 18%:R*x1^2*x2*x3^4%:R*y2^2*y3^2 -
18%:R*x1*x2^2*x3^4%:R*y2^2*y3^2 + 6%:R*x2^3*x3^4%:R*y2^2*y3^2 -
6%:R*x1^2*x3^5*y2^2*y3^2 + 12%:R*x1*x2*x3^5*y2^2*y3^2 -
6%:R*x2^2*x3^5*y2^2*y3^2 - 24%:R*x1^3*x2*y1^2*y2^2*y3^2 +
 24%:R*x1*x2^3*y1^2*y2^2*y3^2 + 24%:R*x1^3*x3*y1^2*y2^2*y3^2 -
 24%:R*x2^3*x3*y1^2*y2^2*y3^2 - 24%:R*x1*x3^3*y1^2*y2^2*y3^2 +
 24%:R*x2*x3^3*y1^2*y2^2*y3^2 + 18%:R*x2*y1^4%:R*y2^2*y3^2 -
18%:R*x3*y1^4%:R*y2^2*y3^2 - 4%:R*x1^4%:R*y1*y2^3*y3^2 +
16%:R*x1^3*x2*y1*y2^3*y3^2 + 12%:R*x1^2*x2^2*y1*y2^3*y3^2 -
16%:R*x1*x2^3*y1*y2^3*y3^2 - 8%:R*x2^4%:R*y1*y2^3*y3^2 -
12%:R*x1^3*x3*y1*y2^3*y3^2 - 24%:R*x1*x2^2*x3*y1*y2^3*y3^2 +
36%:R*x2^3*x3*y1*y2^3*y3^2 + 20%:R*x1*x3^3*y1*y2^3*y3^2 -
20%:R*x2*x3^3*y1*y2^3*y3^2 + 4%:R*x1*y1^3*y2^3*y3^2 -
16%:R*x2*y1^3*y2^3*y3^2 + 12%:R*x3*y1^3*y2^3*y3^2 + 3%:R*x1^4%:R*y2^4%:R*y3^2 -
19%:R*x1^2*x2^2*y2^4%:R*y3^2 + 14%:R*x1*x2^3*y2^4%:R*y3^2 + 2%:R*x2^4%:R*y2^4%:R*y3^2
+ 2%:R*x1^2*x2*x3*y2^4%:R*y3^2 + 14%:R*x1*x2^2*x3*y2^4%:R*y3^2 -
16%:R*x2^3*x3*y2^4%:R*y3^2 - x1^2*x3^2*y2^4%:R*y3^2 +
2%:R*x1*x2*x3^2*y2^4%:R*y3^2 - x2^2*x3^2*y2^4%:R*y3^2 -
6%:R*x1*x3^3*y2^4%:R*y3^2 + 6%:R*x2*x3^3*y2^4%:R*y3^2 - 12%:R*x1*y1^2*y2^4%:R*y3^2
+ 12%:R*x3*y1^2*y2^4%:R*y3^2 + 12%:R*x1*y1*y2^5*y3^2 + 6%:R*x2*y1*y2^5*y3^2 -
18%:R*x3*y1*y2^5*y3^2 - 4%:R*x1*y2^6%:R*y3^2 - 2%:R*x2*y2^6%:R*y3^2 +
6%:R*x3*y2^6%:R*y3^2 + 2%:R*x1^6%:R*x2*y1*y3^3 - 2%:R*x1^4%:R*x2^3*y1*y3^3 -
 8%:R*x1^3*x2^4%:R*y1*y3^3 + 6%:R*x1^2*x2^5*y1*y3^3 + 8%:R*x1*x2^6%:R*y1*y3^3 -
6%:R*x2^7%:R*y1*y3^3 - 2%:R*x1^6%:R*x3*y1*y3^3 - 6%:R*x1^4%:R*x2^2*x3*y1*y3^3 +
28%:R*x1^3*x2^3*x3*y1*y3^3 - 18%:R*x1^2*x2^4%:R*x3*y1*y3^3 -
12%:R*x1*x2^5*x3*y1*y3^3 + 10%:R*x2^6%:R*x3*y1*y3^3 +
6%:R*x1^4%:R*x2*x3^2*y1*y3^3 - 24%:R*x1^3*x2^2*x3^2*y1*y3^3 +
36%:R*x1^2*x2^3*x3^2*y1*y3^3 - 24%:R*x1*x2^4%:R*x3^2*y1*y3^3 +
6%:R*x2^5*x3^2*y1*y3^3 + 2%:R*x1^4%:R*x3^3*y1*y3^3 +
4%:R*x1^3*x2*x3^3*y1*y3^3 - 24%:R*x1^2*x2^2*x3^3*y1*y3^3 +
28%:R*x1*x2^3*x3^3*y1*y3^3 - 10%:R*x2^4%:R*x3^3*y1*y3^3 -
4%:R*x1^3*x2*y1^3*y3^3 + 4%:R*x1*x2^3*y1^3*y3^3 + 4%:R*x1^3*x3*y1^3*y3^3 -
4%:R*x2^3*x3*y1^3*y3^3 - 4%:R*x1*x3^3*y1^3*y3^3 + 4%:R*x2*x3^3*y1^3*y3^3 +
2%:R*x2*y1^5*y3^3 - 2%:R*x3*y1^5*y3^3 - 6%:R*x1^6%:R*x2*y2*y3^3 +
 8%:R*x1^5*x2^2*y2*y3^3 + 6%:R*x1^4%:R*x2^3*y2*y3^3 - 8%:R*x1^3*x2^4%:R*y2*y3^3 -
2%:R*x1^2*x2^5*y2*y3^3 + 2%:R*x2^7%:R*y2*y3^3 + 6%:R*x1^6%:R*x3*y2*y3^3 -
16%:R*x1^5*x2*x3*y2*y3^3 + 26%:R*x1^4%:R*x2^2*x3*y2*y3^3 -
28%:R*x1^3*x2^3*x3*y2*y3^3 - 2%:R*x1^2*x2^4%:R*x3*y2*y3^3 +
28%:R*x1*x2^5*x3*y2*y3^3 - 14%:R*x2^6%:R*x3*y2*y3^3 + 8%:R*x1^5*x3^2*y2*y3^3
- 34%:R*x1^4%:R*x2*x3^2*y2*y3^3 + 56%:R*x1^3*x2^2*x3^2*y2*y3^3 -
44%:R*x1^2*x2^3*x3^2*y2*y3^3 + 16%:R*x1*x2^4%:R*x3^2*y2*y3^3 -
2%:R*x2^5*x3^2*y2*y3^3 + 2%:R*x1^4%:R*x3^3*y2*y3^3 -
20%:R*x1^3*x2*x3^3*y2*y3^3 + 48%:R*x1^2*x2^2*x3^3*y2*y3^3 -
44%:R*x1*x2^3*x3^3*y2*y3^3 + 14%:R*x2^4%:R*x3^3*y2*y3^3 +
12%:R*x1^3*x2*y1^2*y2*y3^3 - 4%:R*x1^2*x2^2*y1^2*y2*y3^3 -
4%:R*x1*x2^3*y1^2*y2*y3^3 - 4%:R*x2^4%:R*y1^2*y2*y3^3 -
12%:R*x1^3*x3*y1^2*y2*y3^3 + 8%:R*x1^2*x2*x3*y1^2*y2*y3^3 -
16%:R*x1*x2^2*x3*y1^2*y2*y3^3 + 20%:R*x2^3*x3*y1^2*y2*y3^3 -
4%:R*x1^2*x3^2*y1^2*y2*y3^3 + 8%:R*x1*x2*x3^2*y1^2*y2*y3^3 -
4%:R*x2^2*x3^2*y1^2*y2*y3^3 + 12%:R*x1*x3^3*y1^2*y2*y3^3 -
12%:R*x2*x3^3*y1^2*y2*y3^3 - 6%:R*x2*y1^4%:R*y2*y3^3 + 6%:R*x3*y1^4%:R*y2*y3^3 -
4%:R*x1^4%:R*y1*y2^2*y3^3 - 8%:R*x1^3*x2*y1*y2^2*y3^3 +
20%:R*x1^2*x2^2*y1*y2^2*y3^3 - 24%:R*x1*x2^3*y1*y2^2*y3^3 +
16%:R*x2^4%:R*y1*y2^2*y3^3 + 12%:R*x1^3*x3*y1*y2^2*y3^3 -
16%:R*x1^2*x2*x3*y1*y2^2*y3^3 + 32%:R*x1*x2^2*x3*y1*y2^2*y3^3 -
28%:R*x2^3*x3*y1*y2^2*y3^3 + 8%:R*x1^2*x3^2*y1*y2^2*y3^3 -
16%:R*x1*x2*x3^2*y1*y2^2*y3^3 + 8%:R*x2^2*x3^2*y1*y2^2*y3^3 -
12%:R*x1*x3^3*y1*y2^2*y3^3 + 12%:R*x2*x3^3*y1*y2^2*y3^3 +
4%:R*x1*y1^3*y2^2*y3^3 - 4%:R*x3*y1^3*y2^2*y3^3 + 8%:R*x1^4%:R*y2^3*y3^3 -
16%:R*x1^3*x2*y2^3*y3^3 + 8%:R*x1^2*x2^2*y2^3*y3^3 +
 8%:R*x1*x2^3*y2^3*y3^3 - 8%:R*x2^4%:R*y2^3*y3^3 - 4%:R*x1^3*x3*y2^3*y3^3 +
 8%:R*x1^2*x2*x3*y2^3*y3^3 - 16%:R*x1*x2^2*x3*y2^3*y3^3 +
12%:R*x2^3*x3*y2^3*y3^3 - 4%:R*x1^2*x3^2*y2^3*y3^3 +
 8%:R*x1*x2*x3^2*y2^3*y3^3 - 4%:R*x2^2*x3^2*y2^3*y3^3 +
4%:R*x1*x3^3*y2^3*y3^3 - 4%:R*x2*x3^3*y2^3*y3^3 - 12%:R*x1*y1^2*y2^3*y3^3
+ 16%:R*x2*y1^2*y2^3*y3^3 - 4%:R*x3*y1^2*y2^3*y3^3 + 12%:R*x1*y1*y2^4%:R*y3^3
- 18%:R*x2*y1*y2^4%:R*y3^3 + 6%:R*x3*y1*y2^4%:R*y3^3 - 4%:R*x1*y2^5*y3^3 +
6%:R*x2*y2^5*y3^3 - 2%:R*x3*y2^5*y3^3 + 2%:R*x1^6%:R*x2*y3^4 -
6%:R*x1^5*x2^2*y3^4 + 4%:R*x1^4%:R*x2^3*y3^4 + 4%:R*x1^3*x2^4%:R*y3^4 -
6%:R*x1^2*x2^5*y3^4 + 2%:R*x1*x2^6%:R*y3^4 - 2%:R*x1^6%:R*x3*y3^4 +
12%:R*x1^5*x2*x3*y3^4 - 24%:R*x1^4%:R*x2^2*x3*y3^4 + 16%:R*x1^3*x2^3*x3*y3^4
+ 6%:R*x1^2*x2^4%:R*x3*y3^4 - 12%:R*x1*x2^5*x3*y3^4 + 4%:R*x2^6%:R*x3*y3^4 -
6%:R*x1^5*x3^2*y3^4 + 24%:R*x1^4%:R*x2*x3^2*y3^4 - 36%:R*x1^3*x2^2*x3^2*y3^4
+ 24%:R*x1^2*x2^3*x3^2*y3^4 - 6%:R*x1*x2^4%:R*x3^2*y3^4 - 4%:R*x1^4%:R*x3^3*y3^4
+ 16%:R*x1^3*x2*x3^3*y3^4 - 24%:R*x1^2*x2^2*x3^3*y3^4 +
16%:R*x1*x2^3*x3^3*y3^4 - 4%:R*x2^4%:R*x3^3*y3^4 - 2%:R*x1^3*x2*y1^2*y3^4 +
3%:R*x1^2*x2^2*y1^2*y3^4 - x2^4%:R*y1^2*y3^4 + 2%:R*x1^3*x3*y1^2*y3^4 -
6%:R*x1^2*x2*x3*y1^2*y3^4 + 6%:R*x1*x2^2*x3*y1^2*y3^4 -
2%:R*x2^3*x3*y1^2*y3^4 + 3%:R*x1^2*x3^2*y1^2*y3^4 -
6%:R*x1*x2*x3^2*y1^2*y3^4 + 3%:R*x2^2*x3^2*y1^2*y3^4 +
6%:R*x1^4%:R*y1*y2*y3^4 - 2%:R*x1^3*x2*y1*y2*y3^4 -
 24%:R*x1^2*x2^2*y1*y2*y3^4 + 30%:R*x1*x2^3*y1*y2*y3^4 -
10%:R*x2^4%:R*y1*y2*y3^4 - 4%:R*x1^3*x3*y1*y2*y3^4 +
12%:R*x1^2*x2*x3*y1*y2*y3^4 - 12%:R*x1*x2^2*x3*y1*y2*y3^4 +
4%:R*x2^3*x3*y1*y2*y3^4 - 6%:R*x1^2*x3^2*y1*y2*y3^4 +
12%:R*x1*x2*x3^2*y1*y2*y3^4 - 6%:R*x2^2*x3^2*y1*y2*y3^4 -
6%:R*x1*y1^3*y2*y3^4 + 6%:R*x2*y1^3*y2*y3^4 - 7%:R*x1^4%:R*y2^2*y3^4 +
 8%:R*x1^3*x2*y2^2*y3^4 + 15%:R*x1^2*x2^2*y2^2*y3^4 -
26%:R*x1*x2^3*y2^2*y3^4 + 10%:R*x2^4%:R*y2^2*y3^4 + 2%:R*x1^3*x3*y2^2*y3^4 -
6%:R*x1^2*x2*x3*y2^2*y3^4 + 6%:R*x1*x2^2*x3*y2^2*y3^4 -
2%:R*x2^3*x3*y2^2*y3^4 + 3%:R*x1^2*x3^2*y2^2*y3^4 -
6%:R*x1*x2*x3^2*y2^2*y3^4 + 3%:R*x2^2*x3^2*y2^2*y3^4 +
18%:R*x1*y1^2*y2^2*y3^4 - 18%:R*x2*y1^2*y2^2*y3^4 - 18%:R*x1*y1*y2^3*y3^4
+ 18%:R*x2*y1*y2^3*y3^4 + 6%:R*x1*y2^4%:R*y3^4 - 6%:R*x2*y2^4%:R*y3^4 -
2%:R*x1^4%:R*y1*y3^5 + 2%:R*x1^3*x2*y1*y3^5 + 6%:R*x1^2*x2^2*y1*y3^5 -
10%:R*x1*x2^3*y1*y3^5 + 4%:R*x2^4%:R*y1*y3^5 + 2%:R*x1*y1^3*y3^5 -
2%:R*x2*y1^3*y3^5 + 6%:R*x1^3*x2*y2*y3^5 - 18%:R*x1^2*x2^2*y2*y3^5 +
18%:R*x1*x2^3*y2*y3^5 - 6%:R*x2^4%:R*y2*y3^5 - 6%:R*x1*y1^2*y2*y3^5 +
6%:R*x2*y1^2*y2*y3^5 + 6%:R*x1*y1*y2^2*y3^5 - 6%:R*x2*y1*y2^2*y3^5 -
2%:R*x1*y2^3*y3^5 + 2%:R*x2*y2^3*y3^5 + x1^4%:R*y3^6 - 4%:R*x1^3*x2*y3^6 +
6%:R*x1^2*x2^2*y3^6 - 4%:R*x1*x2^3*y3^6 + x2^4%:R*y3^6.

(* This one takes much longer (I unterrupted the procedure after 15 minutes of computation 
   on my machine)*)
Elpi Query lp:{{

  quote {{ int_comRing }} {{ ( 2%:R*x1^9%:R*x2^4 -
  8%:R*x1^7%:R*x2^6 + 12%:R*x1^5*x2^8 - 8%:R*x1^3*x2^10 + 2%:R*x1*x2^12 -
  8%:R*x1^9%:R*x2^3*x3 + 6%:R*x1^ 8%:R*x2^4%:R*x3 + 24%:R*x1^7%:R*x2^5*x3 -
 16%:R*x1^6%:R*x2^6%:R*x3 - 24%:R*x1^5*x2^7%:R*x3 + 12%:R*x1^4%:R*x2^ 8%:R*x3 +
  8%:R*x1^3*x2^9%:R*x3 - 2%:R*x2^12%:R*x3 + 12%:R*x1^9%:R*x2^2*x3^2 -
  24%:R*x1^ 8%:R*x2^3*x3^2 - 12%:R*x1^7%:R*x2^4%:R*x3^2 + 48%:R*x1^6%:R*x2^5*x3^2 -
 12%:R*x1^5*x2^6%:R*x3^2 - 24%:R*x1^4%:R*x2^7%:R*x3^2 + 12%:R*x1^3*x2^ 8%:R*x3^2 -
  8%:R*x1^9%:R*x2*x3^3 + 36%:R*x1^ 8%:R*x2^2*x3^3 - 32%:R*x1^7%:R*x2^3*x3^3 -
 36%:R*x1^6%:R*x2^4%:R*x3^3 + 48%:R*x1^5*x2^5*x3^3 + 4%:R*x1^4%:R*x2^6%:R*x3^3 -
 12%:R*x1^2*x2^ 8%:R*x3^3 - 8%:R*x1*x2^9%:R*x3^3 + 8%:R*x2^10%:R*x3^3 + 2%:R*x1^9%:R*x3^4 -
  24%:R*x1^ 8%:R*x2*x3^4 + 48%:R*x1^7%:R*x2^2*x3^4 - 16%:R*x1^6%:R*x2^3*x3^4 -
 18%:R*x1^5*x2^4%:R*x3^4 - 4%:R*x1^3*x2^6%:R*x3^4 + 24%:R*x1^2*x2^7%:R*x3^4 -
 12%:R*x1*x2^ 8%:R*x3^4 + 6%:R*x1^ 8%:R*x3^5 - 24%:R*x1^7%:R*x2*x3^5 +
  24%:R*x1^6%:R*x2^2*x3^5 + 18%:R*x1^4%:R*x2^4%:R*x3^5 - 48%:R*x1^3*x2^5*x3^5 +
 12%:R*x1^2*x2^6%:R*x3^5 + 24%:R*x1*x2^7%:R*x3^5 - 12%:R*x2^ 8%:R*x3^5 + 4%:R*x1^7%:R*x3^6
 - 24%:R*x1^5*x2^2*x3^6 + 16%:R*x1^4%:R*x2^3*x3^6 + 36%:R*x1^3*x2^4%:R*x3^6 -
 48%:R*x1^2*x2^5*x3^6 + 16%:R*x1*x2^6%:R*x3^6 - 4%:R*x1^6%:R*x3^7 +
  24%:R*x1^5*x2*x3^7 - 48%:R*x1^4%:R*x2^2*x3^7 + 32%:R*x1^3*x2^3*x3^7 +
 12%:R*x1^2*x2^4%:R*x3^7 - 24%:R*x1*x2^5*x3^7 + 8%:R*x2^6%:R*x3^7 - 6%:R*x1^5*x3^8 +
  24%:R*x1^4%:R*x2*x3^8 - 36%:R*x1^3*x2^2*x3^8 + 24%:R*x1^2*x2^3*x3^8 -
 6%:R*x1*x2^4%:R*x3^8 - 2%:R*x1^4%:R*x3^9 + 8%:R*x1^3*x2*x3^9 - 12%:R*x1^2*x2^2*x3^9
 + 8%:R*x1*x2^3*x3^9 - 2%:R*x2^4%:R*x3^9 - 5%:R*x1^6%:R*x2^4%:R*y1^2 +
 12%:R*x1^4%:R*x2^6%:R*y1^2 - 9%:R*x1^2*x2^ 8%:R*y1^2 + 2%:R*x2^10%:R*y1^2 +
 20%:R*x1^6%:R*x2^3*x3*y1^2 - 12%:R*x1^5*x2^4%:R*x3*y1^2 -
 36%:R*x1^4%:R*x2^5*x3*y1^2 + 18%:R*x1^3*x2^6%:R*x3*y1^2 +
 18%:R*x1^2*x2^7%:R*x3*y1^2 - 6%:R*x1*x2^ 8%:R*x3*y1^2 - 2%:R*x2^9%:R*x3*y1^2 -
 30%:R*x1^6%:R*x2^2*x3^2*y1^2 + 48%:R*x1^5*x2^3*x3^2*y1^2 +
 18%:R*x1^4%:R*x2^4%:R*x3^2*y1^2 - 54%:R*x1^3*x2^5*x3^2*y1^2 +
 9%:R*x1^2*x2^6%:R*x3^2*y1^2 + 12%:R*x1*x2^7%:R*x3^2*y1^2 - 3%:R*x2^ 8%:R*x3^2*y1^2 +
 20%:R*x1^6%:R*x2*x3^3*y1^2 - 72%:R*x1^5*x2^2*x3^3*y1^2 +
 48%:R*x1^4%:R*x2^3*x3^3*y1^2 + 40%:R*x1^3*x2^4%:R*x3^3*y1^2 -
 36%:R*x1^2*x2^5*x3^3*y1^2 - 5%:R*x1^6%:R*x3^4%:R*y1^2 + 48%:R*x1^5*x2*x3^4%:R*y1^2
 - 72%:R*x1^4%:R*x2^2*x3^4%:R*y1^2 + 20%:R*x1^3*x2^3*x3^4%:R*y1^2 +
 12%:R*x1^2*x2^4%:R*x3^4%:R*y1^2 - 6%:R*x1*x2^5*x3^4%:R*y1^2 + 3%:R*x2^6%:R*x3^4%:R*y1^2 -
 12%:R*x1^5*x3^5*y1^2 + 36%:R*x1^4%:R*x2*x3^5*y1^2 - 30%:R*x1^3*x2^2*x3^5*y1^2
 + 6%:R*x1^2*x2^3*x3^5*y1^2 - 6%:R*x1*x2^4%:R*x3^5*y1^2 + 6%:R*x2^5*x3^5*y1^2
 - 6%:R*x1^4%:R*x3^6%:R*y1^2 + 2%:R*x1^3*x2*x3^6%:R*y1^2 + 9%:R*x1^2*x2^2*x3^6%:R*y1^2
 - 5%:R*x2^4%:R*x3^6%:R*y1^2 + 4%:R*x1^3*x3^7%:R*y1^2 - 12%:R*x1^2*x2*x3^7%:R*y1^2 +
 12%:R*x1*x2^2*x3^7%:R*y1^2 - 4%:R*x2^3*x3^7%:R*y1^2 + 3%:R*x1^2*x3^ 8%:R*y1^2 -
 6%:R*x1*x2*x3^ 8%:R*y1^2 + 3%:R*x2^2*x3^ 8%:R*y1^2 + 4%:R*x1^3*x2^4%:R*y1^4 -
 4%:R*x1*x2^6%:R*y1^4 - 16%:R*x1^3*x2^3*x3*y1^4 + 6%:R*x1^2*x2^4%:R*x3*y1^4 +
 12%:R*x1*x2^5*x3*y1^4 - 2%:R*x2^6%:R*x3*y1^4 + 24%:R*x1^3*x2^2*x3^2*y1^4 -
  24%:R*x1^2*x2^3*x3^2*y1^4 - 6%:R*x1*x2^4%:R*x3^2*y1^4 + 6%:R*x2^5*x3^2*y1^4 -
 16%:R*x1^3*x2*x3^3*y1^4 + 36%:R*x1^2*x2^2*x3^3*y1^4 -
 16%:R*x1*x2^3*x3^3*y1^4 - 4%:R*x2^4%:R*x3^3*y1^4 + 4%:R*x1^3*x3^4%:R*y1^4 -
  24%:R*x1^2*x2*x3^4%:R*y1^4 + 24%:R*x1*x2^2*x3^4%:R*y1^4 - 4%:R*x2^3*x3^4%:R*y1^4 +
 6%:R*x1^2*x3^5*y1^4 - 12%:R*x1*x2*x3^5*y1^4 + 6%:R*x2^2*x3^5*y1^4 +
 2%:R*x1*x3^6%:R*y1^4 - 2%:R*x2*x3^6%:R*y1^4 - x2^4%:R*y1^6 + 4%:R*x2^3*x3*y1^6 -
 6%:R*x2^2*x3^2*y1^6 + 4%:R*x2*x3^3*y1^6 - x3^4%:R*y1^6 + 8%:R*x1^6%:R*x2^4%:R*y1*y2
 - 2%:R*x1^5*x2^5*y1*y2 - 16%:R*x1^4%:R*x2^6%:R*y1*y2 + 4%:R*x1^3*x2^7%:R*y1*y2 +
  8%:R*x1^2*x2^ 8%:R*y1*y2 - 2%:R*x1*x2^9%:R*y1*y2 - 26%:R*x1^6%:R*x2^3*x3*y1*y2 +
 16%:R*x1^5*x2^4%:R*x3*y1*y2 + 34%:R*x1^4%:R*x2^5*x3*y1*y2 -
 12%:R*x1^3*x2^6%:R*x3*y1*y2 - 10%:R*x1^2*x2^7%:R*x3*y1*y2 -
 4%:R*x1*x2^ 8%:R*x3*y1*y2 + 2%:R*x2^9%:R*x3*y1*y2 + 30%:R*x1^6%:R*x2^2*x3^2*y1*y2 -
 44%:R*x1^5*x2^3*x3^2*y1*y2 - 8%:R*x1^4%:R*x2^4%:R*x3^2*y1*y2 +
 22%:R*x1^3*x2^5*x3^2*y1*y2 + 2%:R*x1^2*x2^6%:R*x3^2*y1*y2 +
 2%:R*x1*x2^7%:R*x3^2*y1*y2 - 4%:R*x2^ 8%:R*x3^2*y1*y2 - 14%:R*x1^6%:R*x2*x3^3*y1*y2
 + 56%:R*x1^5*x2^2*x3^3*y1*y2 - 24%:R*x1^4%:R*x2^3*x3^3*y1*y2 -
 32%:R*x1^3*x2^4%:R*x3^3*y1*y2 - 14%:R*x1^2*x2^5*x3^3*y1*y2 +
  24%:R*x1*x2^6%:R*x3^3*y1*y2 + 4%:R*x2^7%:R*x3^3*y1*y2 + 2%:R*x1^6%:R*x3^4%:R*y1*y2 -
 34%:R*x1^5*x2*x3^4%:R*y1*y2 + 20%:R*x1^4%:R*x2^2*x3^4%:R*y1*y2 +
 32%:R*x1^3*x2^3*x3^4%:R*y1*y2 + 4%:R*x1^2*x2^4%:R*x3^4%:R*y1*y2 -
 26%:R*x1*x2^5*x3^4%:R*y1*y2 + 2%:R*x2^6%:R*x3^4%:R*y1*y2 + 8%:R*x1^5*x3^5*y1*y2 -
 10%:R*x1^4%:R*x2*x3^5*y1*y2 - 28%:R*x1^3*x2^2*x3^5*y1*y2 +
 40%:R*x1^2*x2^3*x3^5*y1*y2 + 4%:R*x1*x2^4%:R*x3^5*y1*y2 -
 14%:R*x2^5*x3^5*y1*y2 + 4%:R*x1^4%:R*x3^6%:R*y1*y2 + 22%:R*x1^3*x2*x3^6%:R*y1*y2 -
 48%:R*x1^2*x2^2*x3^6%:R*y1*y2 + 14%:R*x1*x2^3*x3^6%:R*y1*y2 +
  8%:R*x2^4%:R*x3^6%:R*y1*y2 - 8%:R*x1^3*x3^7%:R*y1*y2 + 24%:R*x1^2*x2*x3^7%:R*y1*y2 -
  24%:R*x1*x2^2*x3^7%:R*y1*y2 + 8%:R*x2^3*x3^7%:R*y1*y2 - 6%:R*x1^2*x3^ 8%:R*y1*y2 +
 12%:R*x1*x2*x3^ 8%:R*y1*y2 - 6%:R*x2^2*x3^ 8%:R*y1*y2 - 14%:R*x1^3*x2^4%:R*y1^3*y2 +
 2%:R*x1^2*x2^5*y1^3*y2 + 14%:R*x1*x2^6%:R*y1^3*y2 - 2%:R*x2^7%:R*y1^3*y2 +
 44%:R*x1^3*x2^3*x3*y1^3*y2 - 16%:R*x1^2*x2^4%:R*x3*y1^3*y2 -
 28%:R*x1*x2^5*x3*y1^3*y2 - 48%:R*x1^3*x2^2*x3^2*y1^3*y2 +
 44%:R*x1^2*x2^3*x3^2*y1^3*y2 + 2%:R*x1*x2^4%:R*x3^2*y1^3*y2 +
 2%:R*x2^5*x3^2*y1^3*y2 + 20%:R*x1^3*x2*x3^3*y1^3*y2 -
 56%:R*x1^2*x2^2*x3^3*y1^3*y2 + 28%:R*x1*x2^3*x3^3*y1^3*y2 +
  8%:R*x2^4%:R*x3^3*y1^3*y2 - 2%:R*x1^3*x3^4%:R*y1^3*y2 +
 34%:R*x1^2*x2*x3^4%:R*y1^3*y2 - 26%:R*x1*x2^2*x3^4%:R*y1^3*y2 -
 6%:R*x2^3*x3^4%:R*y1^3*y2 - 8%:R*x1^2*x3^5*y1^3*y2 + 16%:R*x1*x2*x3^5*y1^3*y2
 - 8%:R*x2^2*x3^5*y1^3*y2 - 6%:R*x1*x3^6%:R*y1^3*y2 + 6%:R*x2*x3^6%:R*y1^3*y2 +
 6%:R*x2^4%:R*y1^5*y2 - 18%:R*x2^3*x3*y1^5*y2 + 18%:R*x2^2*x3^2*y1^5*y2 -
 6%:R*x2*x3^3*y1^5*y2 - 3%:R*x1^ 8%:R*x2^2*y2^2 + 4%:R*x1^7%:R*x2^3*y2^2 +
 6%:R*x1^6%:R*x2^4%:R*y2^2 - 12%:R*x1^5*x2^5*y2^2 - 3%:R*x1^4%:R*x2^6%:R*y2^2 +
 12%:R*x1^3*x2^7%:R*y2^2 - 4%:R*x1*x2^9%:R*y2^2 + 6%:R*x1^ 8%:R*x2*x3*y2^2 -
 12%:R*x1^7%:R*x2^2*x3*y2^2 + 2%:R*x1^6%:R*x2^3*x3*y2^2 + 18%:R*x1^5*x2^4%:R*x3*y2^2
 - 12%:R*x1^4%:R*x2^5*x3*y2^2 - 6%:R*x1^3*x2^6%:R*x3*y2^2 + 4%:R*x2^9%:R*x3*y2^2 -
 3%:R*x1^ 8%:R*x3^2*y2^2 + 12%:R*x1^7%:R*x2*x3^2*y2^2 - 21%:R*x1^6%:R*x2^2*x3^2*y2^2
 + 6%:R*x1^5*x2^3*x3^2*y2^2 + 18%:R*x1^4%:R*x2^4%:R*x3^2*y2^2 -
 12%:R*x1^3*x2^5*x3^2*y2^2 - 4%:R*x1^7%:R*x3^3*y2^2 + 12%:R*x1^6%:R*x2*x3^3*y2^2
 - 18%:R*x1^5*x2^2*x3^3*y2^2 + 4%:R*x1^4%:R*x2^3*x3^3*y2^2 +
 12%:R*x1^2*x2^5*x3^3*y2^2 + 6%:R*x1*x2^6%:R*x3^3*y2^2 - 12%:R*x2^7%:R*x3^3*y2^2
 + x1^6%:R*x3^4%:R*y2^2 + 6%:R*x1^5*x2*x3^4%:R*y2^2 - 4%:R*x1^3*x2^3*x3^4%:R*y2^2 -
 18%:R*x1^2*x2^4%:R*x3^4%:R*y2^2 + 12%:R*x1*x2^5*x3^4%:R*y2^2 + 3%:R*x2^6%:R*x3^4%:R*y2^2
 - 6%:R*x1^4%:R*x2*x3^5*y2^2 + 18%:R*x1^3*x2^2*x3^5*y2^2 -
 6%:R*x1^2*x2^3*x3^5*y2^2 - 18%:R*x1*x2^4%:R*x3^5*y2^2 + 12%:R*x2^5*x3^5*y2^2
 - x1^4%:R*x3^6%:R*y2^2 - 12%:R*x1^3*x2*x3^6%:R*y2^2 + 21%:R*x1^2*x2^2*x3^6%:R*y2^2
 - 2%:R*x1*x2^3*x3^6%:R*y2^2 - 6%:R*x2^4%:R*x3^6%:R*y2^2 + 4%:R*x1^3*x3^7%:R*y2^2 -
 12%:R*x1^2*x2*x3^7%:R*y2^2 + 12%:R*x1*x2^2*x3^7%:R*y2^2 - 4%:R*x2^3*x3^7%:R*y2^2 +
 3%:R*x1^2*x3^ 8%:R*y2^2 - 6%:R*x1*x2*x3^ 8%:R*y2^2 + 3%:R*x2^2*x3^ 8%:R*y2^2 +
 6%:R*x1^5*x2^2*y1^2*y2^2 - 6%:R*x1^4%:R*x2^3*y1^2*y2^2 +
 4%:R*x1^3*x2^4%:R*y1^2*y2^2 + 8%:R*x1^2*x2^5*y1^2*y2^2 -
 10%:R*x1*x2^6%:R*y1^2*y2^2 - 2%:R*x2^7%:R*y1^2*y2^2 - 12%:R*x1^5*x2*x3*y1^2*y2^2
 + 18%:R*x1^4%:R*x2^2*x3*y1^2*y2^2 - 28%:R*x1^3*x2^3*x3*y1^2*y2^2 -
 10%:R*x1^2*x2^4%:R*x3*y1^2*y2^2 + 20%:R*x1*x2^5*x3*y1^2*y2^2 +
 12%:R*x2^6%:R*x3*y1^2*y2^2 + 6%:R*x1^5*x3^2*y1^2*y2^2 -
 18%:R*x1^4%:R*x2*x3^2*y1^2*y2^2 + 36%:R*x1^3*x2^2*x3^2*y1^2*y2^2 -
 4%:R*x1^2*x2^3*x3^2*y1^2*y2^2 - 4%:R*x1*x2^4%:R*x3^2*y1^2*y2^2 -
 16%:R*x2^5*x3^2*y1^2*y2^2 + 6%:R*x1^4%:R*x3^3*y1^2*y2^2 -
 4%:R*x1^3*x2*x3^3*y1^2*y2^2 + 4%:R*x1^2*x2^2*x3^3*y1^2*y2^2 +
 4%:R*x1*x2^3*x3^3*y1^2*y2^2 - 10%:R*x2^4%:R*x3^3*y1^2*y2^2 -
  8%:R*x1^3*x3^4%:R*y1^2*y2^2 + 4%:R*x1^2*x2*x3^4%:R*y1^2*y2^2 -
 20%:R*x1*x2^2*x3^4%:R*y1^2*y2^2 + 24%:R*x2^3*x3^4%:R*y1^2*y2^2 -
 2%:R*x1^2*x3^5*y1^2*y2^2 + 4%:R*x1*x2*x3^5*y1^2*y2^2 -
 2%:R*x2^2*x3^5*y1^2*y2^2 + 6%:R*x1*x3^6%:R*y1^2*y2^2 - 6%:R*x2*x3^6%:R*y1^2*y2^2
 - 3%:R*x1^2*x2^2*y1^4%:R*y2^2 + 2%:R*x1*x2^3*y1^4%:R*y2^2 - 10%:R*x2^4%:R*y1^4%:R*y2^2
 + 6%:R*x1^2*x2*x3*y1^4%:R*y2^2 - 6%:R*x1*x2^2*x3*y1^4%:R*y2^2 +
 26%:R*x2^3*x3*y1^4%:R*y2^2 - 3%:R*x1^2*x3^2*y1^4%:R*y2^2 +
 6%:R*x1*x2*x3^2*y1^4%:R*y2^2 - 15%:R*x2^2*x3^2*y1^4%:R*y2^2 -
 2%:R*x1*x3^3*y1^4%:R*y2^2 - 8%:R*x2*x3^3*y1^4%:R*y2^2 + 7%:R*x3^4%:R*y1^4%:R*y2^2 -
 2%:R*x1^6%:R*x2*y1*y2^3 - 4%:R*x1^5*x2^2*y1*y2^3 + 14%:R*x1^4%:R*x2^3*y1*y2^3 -
 6%:R*x1^3*x2^4%:R*y1*y2^3 - 12%:R*x1^2*x2^5*y1*y2^3 + 10%:R*x1*x2^6%:R*y1*y2^3 +
 2%:R*x1^6%:R*x3*y1*y2^3 + 8%:R*x1^5*x2*x3*y1*y2^3 -
 22%:R*x1^4%:R*x2^2*x3*y1*y2^3 + 16%:R*x1^3*x2^3*x3*y1*y2^3 +
 6%:R*x1^2*x2^4%:R*x3*y1*y2^3 - 10%:R*x2^6%:R*x3*y1*y2^3 - 4%:R*x1^5*x3^2*y1*y2^3
 + 14%:R*x1^4%:R*x2*x3^2*y1*y2^3 - 16%:R*x1^3*x2^2*x3^2*y1*y2^3 -
 6%:R*x1*x2^4%:R*x3^2*y1*y2^3 + 12%:R*x2^5*x3^2*y1*y2^3 -
 6%:R*x1^4%:R*x3^3*y1*y2^3 + 16%:R*x1^2*x2^2*x3^3*y1*y2^3 -
 16%:R*x1*x2^3*x3^3*y1*y2^3 + 6%:R*x2^4%:R*x3^3*y1*y2^3 +
 6%:R*x1^3*x3^4%:R*y1*y2^3 - 14%:R*x1^2*x2*x3^4%:R*y1*y2^3 +
 22%:R*x1*x2^2*x3^4%:R*y1*y2^3 - 14%:R*x2^3*x3^4%:R*y1*y2^3 +
 4%:R*x1^2*x3^5*y1*y2^3 - 8%:R*x1*x2*x3^5*y1*y2^3 + 4%:R*x2^2*x3^5*y1*y2^3
 - 2%:R*x1*x3^6%:R*y1*y2^3 + 2%:R*x2*x3^6%:R*y1*y2^3 + 4%:R*x1^3*x2*y1^3*y2^3 +
 4%:R*x1^2*x2^2*y1^3*y2^3 - 12%:R*x1*x2^3*y1^3*y2^3 + 8%:R*x2^4%:R*y1^3*y2^3 -
 4%:R*x1^3*x3*y1^3*y2^3 - 8%:R*x1^2*x2*x3*y1^3*y2^3 +
 16%:R*x1*x2^2*x3*y1^3*y2^3 - 8%:R*x2^3*x3*y1^3*y2^3 +
 4%:R*x1^2*x3^2*y1^3*y2^3 - 8%:R*x1*x2*x3^2*y1^3*y2^3 -
  8%:R*x2^2*x3^2*y1^3*y2^3 + 4%:R*x1*x3^3*y1^3*y2^3 +
 16%:R*x2*x3^3*y1^3*y2^3 - 8%:R*x3^4%:R*y1^3*y2^3 - 2%:R*x2*y1^5*y2^3 +
 2%:R*x3*y1^5*y2^3 - 6%:R*x1^3*x2*y1^2*y2^4 + x1^2*x2^2*y1^2*y2^4 +
 16%:R*x1*x2^3*y1^2*y2^4 - 2%:R*x2^4%:R*y1^2*y2^4 + 6%:R*x1^3*x3*y1^2*y2^4 -
 2%:R*x1^2*x2*x3*y1^2*y2^4 - 14%:R*x1*x2^2*x3*y1^2*y2^4 -
 14%:R*x2^3*x3*y1^2*y2^4 + x1^2*x3^2*y1^2*y2^4 -
 2%:R*x1*x2*x3^2*y1^2*y2^4 + 19%:R*x2^2*x3^2*y1^2*y2^4 -
 3%:R*x3^4%:R*y1^2*y2^4 + 6%:R*x2*y1^4%:R*y2^4 - 6%:R*x3*y1^4%:R*y2^4 -
 2%:R*x1^4%:R*y1*y2^5 + 2%:R*x1^3*x2*y1*y2^5 + 4%:R*x1^2*x2^2*y1*y2^5 -
 14%:R*x1*x2^3*y1*y2^5 + 4%:R*x1^2*x2*x3*y1*y2^5 + 4%:R*x1*x2^2*x3*y1*y2^5
 + 14%:R*x2^3*x3*y1*y2^5 - 2%:R*x1^2*x3^2*y1*y2^5 + 4%:R*x1*x2*x3^2*y1*y2^5
 - 8%:R*x2^2*x3^2*y1*y2^5 - 4%:R*x1*x3^3*y1*y2^5 - 10%:R*x2*x3^3*y1*y2^5 +
  8%:R*x3^4%:R*y1*y2^5 + 2%:R*x1*y1^3*y2^5 - 6%:R*x2*y1^3*y2^5 + 4%:R*x3*y1^3*y2^5
 + 3%:R*x1^4%:R*y2^6 - 4%:R*x1^3*x2*y2^6 + 4%:R*x1*x2^3*y2^6 - 2%:R*x1^3*x3*y2^6
 - 4%:R*x2^3*x3*y2^6 + 2%:R*x1*x3^3*y2^6 + 4%:R*x2*x3^3*y2^6 - 3%:R*x3^4%:R*y2^6
 - 6%:R*x1*y1^2*y2^6 + 2%:R*x2*y1^2*y2^6 + 4%:R*x3*y1^2*y2^6 + 6%:R*x1*y1*y2^7
 - 6%:R*x3*y1*y2^7 - 2%:R*x1*y2^8 + 2%:R*x3*y2^8 - 6%:R*x1^6%:R*x2^4%:R*y1*y3 +
 6%:R*x1^5*x2^5*y1*y3 + 12%:R*x1^4%:R*x2^6%:R*y1*y3 - 12%:R*x1^3*x2^7%:R*y1*y3 -
 6%:R*x1^2*x2^ 8%:R*y1*y3 + 6%:R*x1*x2^9%:R*y1*y3 + 18%:R*x1^6%:R*x2^3*x3*y1*y3 -
  24%:R*x1^5*x2^4%:R*x3*y1*y3 - 18%:R*x1^4%:R*x2^5*x3*y1*y3 +
  24%:R*x1^3*x2^6%:R*x3*y1*y3 + 6%:R*x1^2*x2^7%:R*x3*y1*y3 - 6%:R*x2^9%:R*x3*y1*y3 -
 18%:R*x1^6%:R*x2^2*x3^2*y1*y3 + 36%:R*x1^5*x2^3*x3^2*y1*y3 -
 12%:R*x1^4%:R*x2^4%:R*x3^2*y1*y3 - 6%:R*x1^3*x2^5*x3^2*y1*y3 -
 6%:R*x1*x2^7%:R*x3^2*y1*y3 + 6%:R*x2^ 8%:R*x3^2*y1*y3 + 6%:R*x1^6%:R*x2*x3^3*y1*y3 -
  24%:R*x1^5*x2^2*x3^3*y1*y3 + 24%:R*x1^4%:R*x2^3*x3^3*y1*y3 +
 6%:R*x1^2*x2^5*x3^3*y1*y3 - 24%:R*x1*x2^6%:R*x3^3*y1*y3 +
 12%:R*x2^7%:R*x3^3*y1*y3 + 6%:R*x1^5*x2*x3^4%:R*y1*y3 -
  24%:R*x1^3*x2^3*x3^4%:R*y1*y3 + 12%:R*x1^2*x2^4%:R*x3^4%:R*y1*y3 +
 18%:R*x1*x2^5*x3^4%:R*y1*y3 - 12%:R*x2^6%:R*x3^4%:R*y1*y3 - 6%:R*x1^4%:R*x2*x3^5*y1*y3
 + 24%:R*x1^3*x2^2*x3^5*y1*y3 - 36%:R*x1^2*x2^3*x3^5*y1*y3 +
  24%:R*x1*x2^4%:R*x3^5*y1*y3 - 6%:R*x2^5*x3^5*y1*y3 - 6%:R*x1^3*x2*x3^6%:R*y1*y3
 + 18%:R*x1^2*x2^2*x3^6%:R*y1*y3 - 18%:R*x1*x2^3*x3^6%:R*y1*y3 +
 6%:R*x2^4%:R*x3^6%:R*y1*y3 + 10%:R*x1^3*x2^4%:R*y1^3*y3 - 6%:R*x1^2*x2^5*y1^3*y3 -
 10%:R*x1*x2^6%:R*y1^3*y3 + 6%:R*x2^7%:R*y1^3*y3 - 28%:R*x1^3*x2^3*x3*y1^3*y3 +
  24%:R*x1^2*x2^4%:R*x3*y1^3*y3 + 12%:R*x1*x2^5*x3*y1^3*y3 -
  8%:R*x2^6%:R*x3*y1^3*y3 + 24%:R*x1^3*x2^2*x3^2*y1^3*y3 -
 36%:R*x1^2*x2^3*x3^2*y1^3*y3 + 18%:R*x1*x2^4%:R*x3^2*y1^3*y3 -
 6%:R*x2^5*x3^2*y1^3*y3 - 4%:R*x1^3*x2*x3^3*y1^3*y3 +
  24%:R*x1^2*x2^2*x3^3*y1^3*y3 - 28%:R*x1*x2^3*x3^3*y1^3*y3 +
  8%:R*x2^4%:R*x3^3*y1^3*y3 - 2%:R*x1^3*x3^4%:R*y1^3*y3 -
 6%:R*x1^2*x2*x3^4%:R*y1^3*y3 + 6%:R*x1*x2^2*x3^4%:R*y1^3*y3 +
 2%:R*x2^3*x3^4%:R*y1^3*y3 + 2%:R*x1*x3^6%:R*y1^3*y3 - 2%:R*x2*x3^6%:R*y1^3*y3 -
 4%:R*x2^4%:R*y1^5*y3 + 10%:R*x2^3*x3*y1^5*y3 - 6%:R*x2^2*x3^2*y1^5*y3 -
 2%:R*x2*x3^3*y1^5*y3 + 2%:R*x3^4%:R*y1^5*y3 + 6%:R*x1^ 8%:R*x2^2*y2*y3 -
  8%:R*x1^7%:R*x2^3*y2*y3 - 8%:R*x1^6%:R*x2^4%:R*y2*y3 + 14%:R*x1^5*x2^5*y2*y3 -
 2%:R*x1^4%:R*x2^6%:R*y2*y3 - 4%:R*x1^3*x2^7%:R*y2*y3 + 4%:R*x1^2*x2^ 8%:R*y2*y3 -
 2%:R*x1*x2^9%:R*y2*y3 - 12%:R*x1^ 8%:R*x2*x3*y2*y3 + 24%:R*x1^7%:R*x2^2*x3*y2*y3 -
 14%:R*x1^6%:R*x2^3*x3*y2*y3 - 4%:R*x1^5*x2^4%:R*x3*y2*y3 +
 26%:R*x1^4%:R*x2^5*x3*y2*y3 - 24%:R*x1^3*x2^6%:R*x3*y2*y3 -
 2%:R*x1^2*x2^7%:R*x3*y2*y3 + 4%:R*x1*x2^ 8%:R*x3*y2*y3 + 2%:R*x2^9%:R*x3*y2*y3 +
 6%:R*x1^ 8%:R*x3^2*y2*y3 - 24%:R*x1^7%:R*x2*x3^2*y2*y3 +
 48%:R*x1^6%:R*x2^2*x3^2*y2*y3 - 40%:R*x1^5*x2^3*x3^2*y2*y3 -
 4%:R*x1^4%:R*x2^4%:R*x3^2*y2*y3 + 14%:R*x1^3*x2^5*x3^2*y2*y3 -
 2%:R*x1^2*x2^6%:R*x3^2*y2*y3 + 10%:R*x1*x2^7%:R*x3^2*y2*y3 -
  8%:R*x2^ 8%:R*x3^2*y2*y3 + 8%:R*x1^7%:R*x3^3*y2*y3 - 22%:R*x1^6%:R*x2*x3^3*y2*y3 +
 28%:R*x1^5*x2^2*x3^3*y2*y3 - 32%:R*x1^4%:R*x2^3*x3^3*y2*y3 +
 32%:R*x1^3*x2^4%:R*x3^3*y2*y3 - 22%:R*x1^2*x2^5*x3^3*y2*y3 +
 12%:R*x1*x2^6%:R*x3^3*y2*y3 - 4%:R*x2^7%:R*x3^3*y2*y3 - 4%:R*x1^6%:R*x3^4%:R*y2*y3 +
 10%:R*x1^5*x2*x3^4%:R*y2*y3 - 20%:R*x1^4%:R*x2^2*x3^4%:R*y2*y3 +
  24%:R*x1^3*x2^3*x3^4%:R*y2*y3 + 8%:R*x1^2*x2^4%:R*x3^4%:R*y2*y3 -
 34%:R*x1*x2^5*x3^4%:R*y2*y3 + 16%:R*x2^6%:R*x3^4%:R*y2*y3 - 8%:R*x1^5*x3^5*y2*y3 +
 34%:R*x1^4%:R*x2*x3^5*y2*y3 - 56%:R*x1^3*x2^2*x3^5*y2*y3 +
 44%:R*x1^2*x2^3*x3^5*y2*y3 - 16%:R*x1*x2^4%:R*x3^5*y2*y3 +
 2%:R*x2^5*x3^5*y2*y3 - 2%:R*x1^4%:R*x3^6%:R*y2*y3 + 14%:R*x1^3*x2*x3^6%:R*y2*y3 -
 30%:R*x1^2*x2^2*x3^6%:R*y2*y3 + 26%:R*x1*x2^3*x3^6%:R*y2*y3 -
  8%:R*x2^4%:R*x3^6%:R*y2*y3 - 12%:R*x1^5*x2^2*y1^2*y2*y3 +
 12%:R*x1^4%:R*x2^3*y1^2*y2*y3 - 2%:R*x1^3*x2^4%:R*y1^2*y2*y3 -
 10%:R*x1^2*x2^5*y1^2*y2*y3 + 14%:R*x1*x2^6%:R*y1^2*y2*y3 -
 2%:R*x2^7%:R*y1^2*y2*y3 + 24%:R*x1^5*x2*x3*y1^2*y2*y3 -
 36%:R*x1^4%:R*x2^2*x3*y1^2*y2*y3 + 44%:R*x1^3*x2^3*x3*y1^2*y2*y3 -
 4%:R*x1^2*x2^4%:R*x3*y1^2*y2*y3 - 28%:R*x1*x2^5*x3*y1^2*y2*y3 -
 12%:R*x1^5*x3^2*y1^2*y2*y3 + 36%:R*x1^4%:R*x2*x3^2*y1^2*y2*y3 -
 72%:R*x1^3*x2^2*x3^2*y1^2*y2*y3 + 44%:R*x1^2*x2^3*x3^2*y1^2*y2*y3 -
 10%:R*x1*x2^4%:R*x3^2*y1^2*y2*y3 + 14%:R*x2^5*x3^2*y1^2*y2*y3 -
 12%:R*x1^4%:R*x3^3*y1^2*y2*y3 + 20%:R*x1^3*x2*x3^3*y1^2*y2*y3 -
 32%:R*x1^2*x2^2*x3^3*y1^2*y2*y3 + 28%:R*x1*x2^3*x3^3*y1^2*y2*y3 -
 4%:R*x2^4%:R*x3^3*y1^2*y2*y3 + 10%:R*x1^3*x3^4%:R*y1^2*y2*y3 -
 2%:R*x1^2*x2*x3^4%:R*y1^2*y2*y3 + 10%:R*x1*x2^2*x3^4%:R*y1^2*y2*y3 -
 18%:R*x2^3*x3^4%:R*y1^2*y2*y3 + 4%:R*x1^2*x3^5*y1^2*y2*y3 -
  8%:R*x1*x2*x3^5*y1^2*y2*y3 + 4%:R*x2^2*x3^5*y1^2*y2*y3 -
 6%:R*x1*x3^6%:R*y1^2*y2*y3 + 6%:R*x2*x3^6%:R*y1^2*y2*y3 +
 6%:R*x1^2*x2^2*y1^4%:R*y2*y3 - 4%:R*x1*x2^3*y1^4%:R*y2*y3 +
 10%:R*x2^4%:R*y1^4%:R*y2*y3 - 12%:R*x1^2*x2*x3*y1^4%:R*y2*y3 +
 12%:R*x1*x2^2*x3*y1^4%:R*y2*y3 - 30%:R*x2^3*x3*y1^4%:R*y2*y3 +
 6%:R*x1^2*x3^2*y1^4%:R*y2*y3 - 12%:R*x1*x2*x3^2*y1^4%:R*y2*y3 +
  24%:R*x2^2*x3^2*y1^4%:R*y2*y3 + 4%:R*x1*x3^3*y1^4%:R*y2*y3 +
 2%:R*x2*x3^3*y1^4%:R*y2*y3 - 6%:R*x3^4%:R*y1^4%:R*y2*y3 + 6%:R*x1^6%:R*x2*y1*y2^2*y3 +
  8%:R*x1^5*x2^2*y1*y2^2*y3 - 30%:R*x1^4%:R*x2^3*y1*y2^2*y3 +
 14%:R*x1^3*x2^4%:R*y1*y2^2*y3 + 24%:R*x1^2*x2^5*y1*y2^2*y3 -
 22%:R*x1*x2^6%:R*y1*y2^2*y3 - 6%:R*x1^6%:R*x3*y1*y2^2*y3 -
 16%:R*x1^5*x2*x3*y1*y2^2*y3 + 38%:R*x1^4%:R*x2^2*x3*y1*y2^2*y3 -
 32%:R*x1^3*x2^3*x3*y1*y2^2*y3 - 6%:R*x1^2*x2^4%:R*x3*y1*y2^2*y3 +
 22%:R*x2^6%:R*x3*y1*y2^2*y3 + 8%:R*x1^5*x3^2*y1*y2^2*y3 -
 22%:R*x1^4%:R*x2*x3^2*y1*y2^2*y3 + 32%:R*x1^3*x2^2*x3^2*y1*y2^2*y3 +
 6%:R*x1*x2^4%:R*x3^2*y1*y2^2*y3 - 24%:R*x2^5*x3^2*y1*y2^2*y3 +
 14%:R*x1^4%:R*x3^3*y1*y2^2*y3 - 32%:R*x1^2*x2^2*x3^3*y1*y2^2*y3 +
 32%:R*x1*x2^3*x3^3*y1*y2^2*y3 - 14%:R*x2^4%:R*x3^3*y1*y2^2*y3 -
 14%:R*x1^3*x3^4%:R*y1*y2^2*y3 + 22%:R*x1^2*x2*x3^4%:R*y1*y2^2*y3 -
 38%:R*x1*x2^2*x3^4%:R*y1*y2^2*y3 + 30%:R*x2^3*x3^4%:R*y1*y2^2*y3 -
  8%:R*x1^2*x3^5*y1*y2^2*y3 + 16%:R*x1*x2*x3^5*y1*y2^2*y3 -
  8%:R*x2^2*x3^5*y1*y2^2*y3 + 6%:R*x1*x3^6%:R*y1*y2^2*y3 -
 6%:R*x2*x3^6%:R*y1*y2^2*y3 - 12%:R*x1^3*x2*y1^3*y2^2*y3 -
  8%:R*x1^2*x2^2*y1^3*y2^2*y3 + 28%:R*x1*x2^3*y1^3*y2^2*y3 -
 16%:R*x2^4%:R*y1^3*y2^2*y3 + 12%:R*x1^3*x3*y1^3*y2^2*y3 +
 16%:R*x1^2*x2*x3*y1^3*y2^2*y3 - 32%:R*x1*x2^2*x3*y1^3*y2^2*y3 +
  24%:R*x2^3*x3*y1^3*y2^2*y3 - 8%:R*x1^2*x3^2*y1^3*y2^2*y3 +
 16%:R*x1*x2*x3^2*y1^3*y2^2*y3 - 20%:R*x2^2*x3^2*y1^3*y2^2*y3 -
 12%:R*x1*x3^3*y1^3*y2^2*y3 + 8%:R*x2*x3^3*y1^3*y2^2*y3 +
 4%:R*x3^4%:R*y1^3*y2^2*y3 + 6%:R*x2*y1^5*y2^2*y3 - 6%:R*x3*y1^5*y2^2*y3 -
 2%:R*x1^6%:R*x2*y2^3*y3 - 4%:R*x1^5*x2^2*y2^3*y3 + 14%:R*x1^4%:R*x2^3*y2^3*y3 -
 6%:R*x1^3*x2^4%:R*y2^3*y3 - 12%:R*x1^2*x2^5*y2^3*y3 + 10%:R*x1*x2^6%:R*y2^3*y3 +
 2%:R*x1^6%:R*x3*y2^3*y3 + 8%:R*x1^5*x2*x3*y2^3*y3 -
 22%:R*x1^4%:R*x2^2*x3*y2^3*y3 + 16%:R*x1^3*x2^3*x3*y2^3*y3 +
 6%:R*x1^2*x2^4%:R*x3*y2^3*y3 - 10%:R*x2^6%:R*x3*y2^3*y3 - 4%:R*x1^5*x3^2*y2^3*y3
 + 14%:R*x1^4%:R*x2*x3^2*y2^3*y3 - 16%:R*x1^3*x2^2*x3^2*y2^3*y3 -
 6%:R*x1*x2^4%:R*x3^2*y2^3*y3 + 12%:R*x2^5*x3^2*y2^3*y3 -
 6%:R*x1^4%:R*x3^3*y2^3*y3 + 16%:R*x1^2*x2^2*x3^3*y2^3*y3 -
 16%:R*x1*x2^3*x3^3*y2^3*y3 + 6%:R*x2^4%:R*x3^3*y2^3*y3 +
 6%:R*x1^3*x3^4%:R*y2^3*y3 - 14%:R*x1^2*x2*x3^4%:R*y2^3*y3 +
 22%:R*x1*x2^2*x3^4%:R*y2^3*y3 - 14%:R*x2^3*x3^4%:R*y2^3*y3 +
 4%:R*x1^2*x3^5*y2^3*y3 - 8%:R*x1*x2*x3^5*y2^3*y3 + 4%:R*x2^2*x3^5*y2^3*y3
 - 2%:R*x1*x3^6%:R*y2^3*y3 + 2%:R*x2*x3^6%:R*y2^3*y3 + 20%:R*x1^3*x2*y1^2*y2^3*y3
 - 36%:R*x1*x2^3*y1^2*y2^3*y3 + 8%:R*x2^4%:R*y1^2*y2^3*y3 -
 20%:R*x1^3*x3*y1^2*y2^3*y3 + 24%:R*x1*x2^2*x3*y1^2*y2^3*y3 +
 16%:R*x2^3*x3*y1^2*y2^3*y3 - 12%:R*x2^2*x3^2*y1^2*y2^3*y3 +
 12%:R*x1*x3^3*y1^2*y2^3*y3 - 16%:R*x2*x3^3*y1^2*y2^3*y3 +
 4%:R*x3^4%:R*y1^2*y2^3*y3 - 18%:R*x2*y1^4%:R*y2^3*y3 + 18%:R*x3*y1^4%:R*y2^3*y3 +
 6%:R*x1^4%:R*y1*y2^4%:R*y3 - 10%:R*x1^3*x2*y1*y2^4%:R*y3 -
 18%:R*x1^2*x2^2*y1*y2^4%:R*y3 + 34%:R*x1*x2^3*y1*y2^4%:R*y3 +
 4%:R*x1^3*x3*y1*y2^4%:R*y3 - 34%:R*x2^3*x3*y1*y2^4%:R*y3 +
 18%:R*x2^2*x3^2*y1*y2^4%:R*y3 - 4%:R*x1*x3^3*y1*y2^4%:R*y3 +
 10%:R*x2*x3^3*y1*y2^4%:R*y3 - 6%:R*x3^4%:R*y1*y2^4%:R*y3 - 6%:R*x1*y1^3*y2^4%:R*y3 +
 18%:R*x2*y1^3*y2^4%:R*y3 - 12%:R*x3*y1^3*y2^4%:R*y3 - 8%:R*x1^4%:R*y2^5*y3 +
 10%:R*x1^3*x2*y2^5*y3 + 8%:R*x1^2*x2^2*y2^5*y3 - 14%:R*x1*x2^3*y2^5*y3 +
 4%:R*x1^3*x3*y2^5*y3 - 4%:R*x1^2*x2*x3*y2^5*y3 - 4%:R*x1*x2^2*x3*y2^5*y3 +
 14%:R*x2^3*x3*y2^5*y3 + 2%:R*x1^2*x3^2*y2^5*y3 - 4%:R*x1*x2*x3^2*y2^5*y3 -
 4%:R*x2^2*x3^2*y2^5*y3 - 2%:R*x2*x3^3*y2^5*y3 + 2%:R*x3^4%:R*y2^5*y3 +
 18%:R*x1*y1^2*y2^5*y3 - 6%:R*x2*y1^2*y2^5*y3 - 12%:R*x3*y1^2*y2^5*y3 -
 18%:R*x1*y1*y2^6%:R*y3 + 18%:R*x3*y1*y2^6%:R*y3 + 6%:R*x1*y2^7%:R*y3 - 6%:R*x3*y2^7%:R*y3
 - 3%:R*x1^ 8%:R*x2^2*y3^2 + 4%:R*x1^7%:R*x2^3*y3^2 + 5%:R*x1^6%:R*x2^4%:R*y3^2 -
 6%:R*x1^5*x2^5*y3^2 - 3%:R*x1^4%:R*x2^6%:R*y3^2 + 3%:R*x1^2*x2^ 8%:R*y3^2 +
 2%:R*x1*x2^9%:R*y3^2 - 2%:R*x2^10%:R*y3^2 + 6%:R*x1^ 8%:R*x2*x3*y3^2 -
 12%:R*x1^7%:R*x2^2*x3*y3^2 + 6%:R*x1^5*x2^4%:R*x3*y3^2 + 6%:R*x1^4%:R*x2^5*x3*y3^2
 - 12%:R*x1^2*x2^7%:R*x3*y3^2 + 6%:R*x1*x2^ 8%:R*x3*y3^2 - 3%:R*x1^ 8%:R*x3^2*y3^2 +
 12%:R*x1^7%:R*x2*x3^2*y3^2 - 9%:R*x1^6%:R*x2^2*x3^2*y3^2 -
 6%:R*x1^5*x2^3*x3^2*y3^2 - 12%:R*x1^4%:R*x2^4%:R*x3^2*y3^2 +
 36%:R*x1^3*x2^5*x3^2*y3^2 - 9%:R*x1^2*x2^6%:R*x3^2*y3^2 -
 18%:R*x1*x2^7%:R*x3^2*y3^2 + 9%:R*x2^ 8%:R*x3^2*y3^2 - 4%:R*x1^7%:R*x3^3*y3^2 -
 2%:R*x1^6%:R*x2*x3^3*y3^2 + 30%:R*x1^5*x2^2*x3^3*y3^2 -
 20%:R*x1^4%:R*x2^3*x3^3*y3^2 - 40%:R*x1^3*x2^4%:R*x3^3*y3^2 +
 54%:R*x1^2*x2^5*x3^3*y3^2 - 18%:R*x1*x2^6%:R*x3^3*y3^2 + 6%:R*x1^6%:R*x3^4%:R*y3^2
 - 36%:R*x1^5*x2*x3^4%:R*y3^2 + 72%:R*x1^4%:R*x2^2*x3^4%:R*y3^2 -
 48%:R*x1^3*x2^3*x3^4%:R*y3^2 - 18%:R*x1^2*x2^4%:R*x3^4%:R*y3^2 +
 36%:R*x1*x2^5*x3^4%:R*y3^2 - 12%:R*x2^6%:R*x3^4%:R*y3^2 + 12%:R*x1^5*x3^5*y3^2 -
 48%:R*x1^4%:R*x2*x3^5*y3^2 + 72%:R*x1^3*x2^2*x3^5*y3^2 -
 48%:R*x1^2*x2^3*x3^5*y3^2 + 12%:R*x1*x2^4%:R*x3^5*y3^2 + 5%:R*x1^4%:R*x3^6%:R*y3^2
 - 20%:R*x1^3*x2*x3^6%:R*y3^2 + 30%:R*x1^2*x2^2*x3^6%:R*y3^2 -
 20%:R*x1*x2^3*x3^6%:R*y3^2 + 5%:R*x2^4%:R*x3^6%:R*y3^2 + 6%:R*x1^5*x2^2*y1^2*y3^2 -
 6%:R*x1^4%:R*x2^3*y1^2*y3^2 - 6%:R*x1^3*x2^4%:R*y1^2*y3^2 +
 6%:R*x1^2*x2^5*y1^2*y3^2 - 12%:R*x1^5*x2*x3*y1^2*y3^2 +
 18%:R*x1^4%:R*x2^2*x3*y1^2*y3^2 - 6%:R*x1^2*x2^4%:R*x3*y1^2*y3^2 +
 6%:R*x1^5*x3^2*y1^2*y3^2 - 18%:R*x1^4%:R*x2*x3^2*y1^2*y3^2 +
 12%:R*x1^3*x2^2*x3^2*y1^2*y3^2 + 6%:R*x1*x2^4%:R*x3^2*y1^2*y3^2 -
 6%:R*x2^5*x3^2*y1^2*y3^2 + 6%:R*x1^4%:R*x3^3*y1^2*y3^2 -
 12%:R*x1^2*x2^2*x3^3*y1^2*y3^2 + 6%:R*x2^4%:R*x3^3*y1^2*y3^2 -
 6%:R*x1^3*x3^4%:R*y1^2*y3^2 + 18%:R*x1^2*x2*x3^4%:R*y1^2*y3^2 -
 18%:R*x1*x2^2*x3^4%:R*y1^2*y3^2 + 6%:R*x2^3*x3^4%:R*y1^2*y3^2 -
 6%:R*x1^2*x3^5*y1^2*y3^2 + 12%:R*x1*x2*x3^5*y1^2*y3^2 -
 6%:R*x2^2*x3^5*y1^2*y3^2 - 3%:R*x1^2*x2^2*y1^4%:R*y3^2 +
 2%:R*x1*x2^3*y1^4%:R*y3^2 + x2^4%:R*y1^4%:R*y3^2 + 6%:R*x1^2*x2*x3*y1^4%:R*y3^2 -
 6%:R*x1*x2^2*x3*y1^4%:R*y3^2 - 3%:R*x1^2*x3^2*y1^4%:R*y3^2 +
 6%:R*x1*x2*x3^2*y1^4%:R*y3^2 - 3%:R*x2^2*x3^2*y1^4%:R*y3^2 -
 2%:R*x1*x3^3*y1^4%:R*y3^2 + 2%:R*x2*x3^3*y1^4%:R*y3^2 - 6%:R*x1^6%:R*x2*y1*y2*y3^2
 - 4%:R*x1^5*x2^2*y1*y2*y3^2 + 18%:R*x1^4%:R*x2^3*y1*y2*y3^2 +
 4%:R*x1^3*x2^4%:R*y1*y2*y3^2 - 14%:R*x1^2*x2^5*y1*y2*y3^2 +
 2%:R*x2^7%:R*y1*y2*y3^2 + 6%:R*x1^6%:R*x3*y1*y2*y3^2 +
  8%:R*x1^5*x2*x3*y1*y2*y3^2 - 10%:R*x1^4%:R*x2^2*x3*y1*y2*y3^2 -
 28%:R*x1^3*x2^3*x3*y1*y2*y3^2 + 10%:R*x1^2*x2^4%:R*x3*y1*y2*y3^2 +
 28%:R*x1*x2^5*x3*y1*y2*y3^2 - 14%:R*x2^6%:R*x3*y1*y2*y3^2 -
 4%:R*x1^5*x3^2*y1*y2*y3^2 + 2%:R*x1^4%:R*x2*x3^2*y1*y2*y3^2 +
 32%:R*x1^3*x2^2*x3^2*y1*y2*y3^2 - 44%:R*x1^2*x2^3*x3^2*y1*y2*y3^2 +
 4%:R*x1*x2^4%:R*x3^2*y1*y2*y3^2 + 10%:R*x2^5*x3^2*y1*y2*y3^2 -
 10%:R*x1^4%:R*x3^3*y1*y2*y3^2 - 20%:R*x1^3*x2*x3^3*y1*y2*y3^2 +
 72%:R*x1^2*x2^2*x3^3*y1*y2*y3^2 - 44%:R*x1*x2^3*x3^3*y1*y2*y3^2 +
 2%:R*x2^4%:R*x3^3*y1*y2*y3^2 + 12%:R*x1^3*x3^4%:R*y1*y2*y3^2 -
 36%:R*x1^2*x2*x3^4%:R*y1*y2*y3^2 + 36%:R*x1*x2^2*x3^4%:R*y1*y2*y3^2 -
 12%:R*x2^3*x3^4%:R*y1*y2*y3^2 + 12%:R*x1^2*x3^5*y1*y2*y3^2 -
  24%:R*x1*x2*x3^5*y1*y2*y3^2 + 12%:R*x2^2*x3^5*y1*y2*y3^2 +
 12%:R*x1^3*x2*y1^3*y2*y3^2 + 4%:R*x1^2*x2^2*y1^3*y2*y3^2 -
 20%:R*x1*x2^3*y1^3*y2*y3^2 + 4%:R*x2^4%:R*y1^3*y2*y3^2 -
 12%:R*x1^3*x3*y1^3*y2*y3^2 - 8%:R*x1^2*x2*x3*y1^3*y2*y3^2 +
 16%:R*x1*x2^2*x3*y1^3*y2*y3^2 + 4%:R*x2^3*x3*y1^3*y2*y3^2 +
 4%:R*x1^2*x3^2*y1^3*y2*y3^2 - 8%:R*x1*x2*x3^2*y1^3*y2*y3^2 +
 4%:R*x2^2*x3^2*y1^3*y2*y3^2 + 12%:R*x1*x3^3*y1^3*y2*y3^2 -
 12%:R*x2*x3^3*y1^3*y2*y3^2 - 6%:R*x2*y1^5*y2*y3^2 + 6%:R*x3*y1^5*y2*y3^2 +
 6%:R*x1^6%:R*x2*y2^2*y3^2 + 2%:R*x1^5*x2^2*y2^2*y3^2 -
  24%:R*x1^4%:R*x2^3*y2^2*y3^2 + 10%:R*x1^3*x2^4%:R*y2^2*y3^2 +
 16%:R*x1^2*x2^5*y2^2*y3^2 - 12%:R*x1*x2^6%:R*y2^2*y3^2 + 2%:R*x2^7%:R*y2^2*y3^2
 - 6%:R*x1^6%:R*x3*y2^2*y3^2 - 4%:R*x1^5*x2*x3*y2^2*y3^2 +
 20%:R*x1^4%:R*x2^2*x3*y2^2*y3^2 - 4%:R*x1^3*x2^3*x3*y2^2*y3^2 +
 4%:R*x1^2*x2^4%:R*x3*y2^2*y3^2 - 20%:R*x1*x2^5*x3*y2^2*y3^2 +
 10%:R*x2^6%:R*x3*y2^2*y3^2 + 2%:R*x1^5*x3^2*y2^2*y3^2 -
 4%:R*x1^4%:R*x2*x3^2*y2^2*y3^2 - 4%:R*x1^3*x2^2*x3^2*y2^2*y3^2 +
 4%:R*x1^2*x2^3*x3^2*y2^2*y3^2 + 10%:R*x1*x2^4%:R*x3^2*y2^2*y3^2 -
  8%:R*x2^5*x3^2*y2^2*y3^2 + 8%:R*x1^4%:R*x3^3*y2^2*y3^2 +
 4%:R*x1^3*x2*x3^3*y2^2*y3^2 - 36%:R*x1^2*x2^2*x3^3*y2^2*y3^2 +
 28%:R*x1*x2^3*x3^3*y2^2*y3^2 - 4%:R*x2^4%:R*x3^3*y2^2*y3^2 -
 6%:R*x1^3*x3^4%:R*y2^2*y3^2 + 18%:R*x1^2*x2*x3^4%:R*y2^2*y3^2 -
 18%:R*x1*x2^2*x3^4%:R*y2^2*y3^2 + 6%:R*x2^3*x3^4%:R*y2^2*y3^2 -
 6%:R*x1^2*x3^5*y2^2*y3^2 + 12%:R*x1*x2*x3^5*y2^2*y3^2 -
 6%:R*x2^2*x3^5*y2^2*y3^2 - 24%:R*x1^3*x2*y1^2*y2^2*y3^2 +
  24%:R*x1*x2^3*y1^2*y2^2*y3^2 + 24%:R*x1^3*x3*y1^2*y2^2*y3^2 -
  24%:R*x2^3*x3*y1^2*y2^2*y3^2 - 24%:R*x1*x3^3*y1^2*y2^2*y3^2 +
  24%:R*x2*x3^3*y1^2*y2^2*y3^2 + 18%:R*x2*y1^4%:R*y2^2*y3^2 -
 18%:R*x3*y1^4%:R*y2^2*y3^2 - 4%:R*x1^4%:R*y1*y2^3*y3^2 +
 16%:R*x1^3*x2*y1*y2^3*y3^2 + 12%:R*x1^2*x2^2*y1*y2^3*y3^2 -
 16%:R*x1*x2^3*y1*y2^3*y3^2 - 8%:R*x2^4%:R*y1*y2^3*y3^2 -
 12%:R*x1^3*x3*y1*y2^3*y3^2 - 24%:R*x1*x2^2*x3*y1*y2^3*y3^2 +
 36%:R*x2^3*x3*y1*y2^3*y3^2 + 20%:R*x1*x3^3*y1*y2^3*y3^2 -
 20%:R*x2*x3^3*y1*y2^3*y3^2 + 4%:R*x1*y1^3*y2^3*y3^2 -
 16%:R*x2*y1^3*y2^3*y3^2 + 12%:R*x3*y1^3*y2^3*y3^2 + 3%:R*x1^4%:R*y2^4%:R*y3^2 -
 19%:R*x1^2*x2^2*y2^4%:R*y3^2 + 14%:R*x1*x2^3*y2^4%:R*y3^2 + 2%:R*x2^4%:R*y2^4%:R*y3^2
 + 2%:R*x1^2*x2*x3*y2^4%:R*y3^2 + 14%:R*x1*x2^2*x3*y2^4%:R*y3^2 -
 16%:R*x2^3*x3*y2^4%:R*y3^2 - x1^2*x3^2*y2^4%:R*y3^2 +
 2%:R*x1*x2*x3^2*y2^4%:R*y3^2 - x2^2*x3^2*y2^4%:R*y3^2 -
 6%:R*x1*x3^3*y2^4%:R*y3^2 + 6%:R*x2*x3^3*y2^4%:R*y3^2 - 12%:R*x1*y1^2*y2^4%:R*y3^2
 + 12%:R*x3*y1^2*y2^4%:R*y3^2 + 12%:R*x1*y1*y2^5*y3^2 + 6%:R*x2*y1*y2^5*y3^2 -
 18%:R*x3*y1*y2^5*y3^2 - 4%:R*x1*y2^6%:R*y3^2 - 2%:R*x2*y2^6%:R*y3^2 +
 6%:R*x3*y2^6%:R*y3^2 + 2%:R*x1^6%:R*x2*y1*y3^3 - 2%:R*x1^4%:R*x2^3*y1*y3^3 -
  8%:R*x1^3*x2^4%:R*y1*y3^3 + 6%:R*x1^2*x2^5*y1*y3^3 + 8%:R*x1*x2^6%:R*y1*y3^3 -
 6%:R*x2^7%:R*y1*y3^3 - 2%:R*x1^6%:R*x3*y1*y3^3 - 6%:R*x1^4%:R*x2^2*x3*y1*y3^3 +
 28%:R*x1^3*x2^3*x3*y1*y3^3 - 18%:R*x1^2*x2^4%:R*x3*y1*y3^3 -
 12%:R*x1*x2^5*x3*y1*y3^3 + 10%:R*x2^6%:R*x3*y1*y3^3 +
 6%:R*x1^4%:R*x2*x3^2*y1*y3^3 - 24%:R*x1^3*x2^2*x3^2*y1*y3^3 +
 36%:R*x1^2*x2^3*x3^2*y1*y3^3 - 24%:R*x1*x2^4%:R*x3^2*y1*y3^3 +
 6%:R*x2^5*x3^2*y1*y3^3 + 2%:R*x1^4%:R*x3^3*y1*y3^3 +
 4%:R*x1^3*x2*x3^3*y1*y3^3 - 24%:R*x1^2*x2^2*x3^3*y1*y3^3 +
 28%:R*x1*x2^3*x3^3*y1*y3^3 - 10%:R*x2^4%:R*x3^3*y1*y3^3 -
 4%:R*x1^3*x2*y1^3*y3^3 + 4%:R*x1*x2^3*y1^3*y3^3 + 4%:R*x1^3*x3*y1^3*y3^3 -
 4%:R*x2^3*x3*y1^3*y3^3 - 4%:R*x1*x3^3*y1^3*y3^3 + 4%:R*x2*x3^3*y1^3*y3^3 +
 2%:R*x2*y1^5*y3^3 - 2%:R*x3*y1^5*y3^3 - 6%:R*x1^6%:R*x2*y2*y3^3 +
  8%:R*x1^5*x2^2*y2*y3^3 + 6%:R*x1^4%:R*x2^3*y2*y3^3 - 8%:R*x1^3*x2^4%:R*y2*y3^3 -
 2%:R*x1^2*x2^5*y2*y3^3 + 2%:R*x2^7%:R*y2*y3^3 + 6%:R*x1^6%:R*x3*y2*y3^3 -
 16%:R*x1^5*x2*x3*y2*y3^3 + 26%:R*x1^4%:R*x2^2*x3*y2*y3^3 -
 28%:R*x1^3*x2^3*x3*y2*y3^3 - 2%:R*x1^2*x2^4%:R*x3*y2*y3^3 +
 28%:R*x1*x2^5*x3*y2*y3^3 - 14%:R*x2^6%:R*x3*y2*y3^3 + 8%:R*x1^5*x3^2*y2*y3^3
 - 34%:R*x1^4%:R*x2*x3^2*y2*y3^3 + 56%:R*x1^3*x2^2*x3^2*y2*y3^3 -
 44%:R*x1^2*x2^3*x3^2*y2*y3^3 + 16%:R*x1*x2^4%:R*x3^2*y2*y3^3 -
 2%:R*x2^5*x3^2*y2*y3^3 + 2%:R*x1^4%:R*x3^3*y2*y3^3 -
 20%:R*x1^3*x2*x3^3*y2*y3^3 + 48%:R*x1^2*x2^2*x3^3*y2*y3^3 -
 44%:R*x1*x2^3*x3^3*y2*y3^3 + 14%:R*x2^4%:R*x3^3*y2*y3^3 +
 12%:R*x1^3*x2*y1^2*y2*y3^3 - 4%:R*x1^2*x2^2*y1^2*y2*y3^3 -
 4%:R*x1*x2^3*y1^2*y2*y3^3 - 4%:R*x2^4%:R*y1^2*y2*y3^3 -
 12%:R*x1^3*x3*y1^2*y2*y3^3 + 8%:R*x1^2*x2*x3*y1^2*y2*y3^3 -
 16%:R*x1*x2^2*x3*y1^2*y2*y3^3 + 20%:R*x2^3*x3*y1^2*y2*y3^3 -
 4%:R*x1^2*x3^2*y1^2*y2*y3^3 + 8%:R*x1*x2*x3^2*y1^2*y2*y3^3 -
 4%:R*x2^2*x3^2*y1^2*y2*y3^3 + 12%:R*x1*x3^3*y1^2*y2*y3^3 -
 12%:R*x2*x3^3*y1^2*y2*y3^3 - 6%:R*x2*y1^4%:R*y2*y3^3 + 6%:R*x3*y1^4%:R*y2*y3^3 -
 4%:R*x1^4%:R*y1*y2^2*y3^3 - 8%:R*x1^3*x2*y1*y2^2*y3^3 +
 20%:R*x1^2*x2^2*y1*y2^2*y3^3 - 24%:R*x1*x2^3*y1*y2^2*y3^3 +
 16%:R*x2^4%:R*y1*y2^2*y3^3 + 12%:R*x1^3*x3*y1*y2^2*y3^3 -
 16%:R*x1^2*x2*x3*y1*y2^2*y3^3 + 32%:R*x1*x2^2*x3*y1*y2^2*y3^3 -
 28%:R*x2^3*x3*y1*y2^2*y3^3 + 8%:R*x1^2*x3^2*y1*y2^2*y3^3 -
 16%:R*x1*x2*x3^2*y1*y2^2*y3^3 + 8%:R*x2^2*x3^2*y1*y2^2*y3^3 -
 12%:R*x1*x3^3*y1*y2^2*y3^3 + 12%:R*x2*x3^3*y1*y2^2*y3^3 +
 4%:R*x1*y1^3*y2^2*y3^3 - 4%:R*x3*y1^3*y2^2*y3^3 + 8%:R*x1^4%:R*y2^3*y3^3 -
 16%:R*x1^3*x2*y2^3*y3^3 + 8%:R*x1^2*x2^2*y2^3*y3^3 +
  8%:R*x1*x2^3*y2^3*y3^3 - 8%:R*x2^4%:R*y2^3*y3^3 - 4%:R*x1^3*x3*y2^3*y3^3 +
  8%:R*x1^2*x2*x3*y2^3*y3^3 - 16%:R*x1*x2^2*x3*y2^3*y3^3 +
 12%:R*x2^3*x3*y2^3*y3^3 - 4%:R*x1^2*x3^2*y2^3*y3^3 +
  8%:R*x1*x2*x3^2*y2^3*y3^3 - 4%:R*x2^2*x3^2*y2^3*y3^3 +
 4%:R*x1*x3^3*y2^3*y3^3 - 4%:R*x2*x3^3*y2^3*y3^3 - 12%:R*x1*y1^2*y2^3*y3^3
 + 16%:R*x2*y1^2*y2^3*y3^3 - 4%:R*x3*y1^2*y2^3*y3^3 + 12%:R*x1*y1*y2^4%:R*y3^3
 - 18%:R*x2*y1*y2^4%:R*y3^3 + 6%:R*x3*y1*y2^4%:R*y3^3 - 4%:R*x1*y2^5*y3^3 +
 6%:R*x2*y2^5*y3^3 - 2%:R*x3*y2^5*y3^3 + 2%:R*x1^6%:R*x2*y3^4 -
 6%:R*x1^5*x2^2*y3^4 + 4%:R*x1^4%:R*x2^3*y3^4 + 4%:R*x1^3*x2^4%:R*y3^4 -
 6%:R*x1^2*x2^5*y3^4 + 2%:R*x1*x2^6%:R*y3^4 - 2%:R*x1^6%:R*x3*y3^4 +
 12%:R*x1^5*x2*x3*y3^4 - 24%:R*x1^4%:R*x2^2*x3*y3^4 + 16%:R*x1^3*x2^3*x3*y3^4
 + 6%:R*x1^2*x2^4%:R*x3*y3^4 - 12%:R*x1*x2^5*x3*y3^4 + 4%:R*x2^6%:R*x3*y3^4 -
 6%:R*x1^5*x3^2*y3^4 + 24%:R*x1^4%:R*x2*x3^2*y3^4 - 36%:R*x1^3*x2^2*x3^2*y3^4
 + 24%:R*x1^2*x2^3*x3^2*y3^4 - 6%:R*x1*x2^4%:R*x3^2*y3^4 - 4%:R*x1^4%:R*x3^3*y3^4
 + 16%:R*x1^3*x2*x3^3*y3^4 - 24%:R*x1^2*x2^2*x3^3*y3^4 +
 16%:R*x1*x2^3*x3^3*y3^4 - 4%:R*x2^4%:R*x3^3*y3^4 - 2%:R*x1^3*x2*y1^2*y3^4 +
 3%:R*x1^2*x2^2*y1^2*y3^4 - x2^4%:R*y1^2*y3^4 + 2%:R*x1^3*x3*y1^2*y3^4 -
 6%:R*x1^2*x2*x3*y1^2*y3^4 + 6%:R*x1*x2^2*x3*y1^2*y3^4 -
 2%:R*x2^3*x3*y1^2*y3^4 + 3%:R*x1^2*x3^2*y1^2*y3^4 -
 6%:R*x1*x2*x3^2*y1^2*y3^4 + 3%:R*x2^2*x3^2*y1^2*y3^4 +
 6%:R*x1^4%:R*y1*y2*y3^4 - 2%:R*x1^3*x2*y1*y2*y3^4 -
  24%:R*x1^2*x2^2*y1*y2*y3^4 + 30%:R*x1*x2^3*y1*y2*y3^4 -
 10%:R*x2^4%:R*y1*y2*y3^4 - 4%:R*x1^3*x3*y1*y2*y3^4 +
 12%:R*x1^2*x2*x3*y1*y2*y3^4 - 12%:R*x1*x2^2*x3*y1*y2*y3^4 +
 4%:R*x2^3*x3*y1*y2*y3^4 - 6%:R*x1^2*x3^2*y1*y2*y3^4 +
 12%:R*x1*x2*x3^2*y1*y2*y3^4 - 6%:R*x2^2*x3^2*y1*y2*y3^4 -
 6%:R*x1*y1^3*y2*y3^4 + 6%:R*x2*y1^3*y2*y3^4 - 7%:R*x1^4%:R*y2^2*y3^4 +
  8%:R*x1^3*x2*y2^2*y3^4 + 15%:R*x1^2*x2^2*y2^2*y3^4 -
 26%:R*x1*x2^3*y2^2*y3^4 + 10%:R*x2^4%:R*y2^2*y3^4 + 2%:R*x1^3*x3*y2^2*y3^4 -
 6%:R*x1^2*x2*x3*y2^2*y3^4 + 6%:R*x1*x2^2*x3*y2^2*y3^4 -
 2%:R*x2^3*x3*y2^2*y3^4 + 3%:R*x1^2*x3^2*y2^2*y3^4 -
 6%:R*x1*x2*x3^2*y2^2*y3^4 + 3%:R*x2^2*x3^2*y2^2*y3^4 +
 18%:R*x1*y1^2*y2^2*y3^4 - 18%:R*x2*y1^2*y2^2*y3^4 - 18%:R*x1*y1*y2^3*y3^4
 + 18%:R*x2*y1*y2^3*y3^4 + 6%:R*x1*y2^4%:R*y3^4 - 6%:R*x2*y2^4%:R*y3^4 -
 2%:R*x1^4%:R*y1*y3^5 + 2%:R*x1^3*x2*y1*y3^5 + 6%:R*x1^2*x2^2*y1*y3^5 -
 10%:R*x1*x2^3*y1*y3^5 + 4%:R*x2^4%:R*y1*y3^5 + 2%:R*x1*y1^3*y3^5 -
 2%:R*x2*y1^3*y3^5 + 6%:R*x1^3*x2*y2*y3^5 - 18%:R*x1^2*x2^2*y2*y3^5 +
 18%:R*x1*x2^3*y2*y3^5 - 6%:R*x2^4%:R*y2*y3^5 - 6%:R*x1*y1^2*y2*y3^5 +
 6%:R*x2*y1^2*y2*y3^5 + 6%:R*x1*y1*y2^2*y3^5 - 6%:R*x2*y1*y2^2*y3^5 -
 2%:R*x1*y2^3*y3^5 + 2%:R*x2*y2^3*y3^5 + x1^4%:R*y3^6 - 4%:R*x1^3*x2*y3^6 +
 6%:R*x1^2*x2^2*y3^6 - 4%:R*x1*x2^3*y3^6 + x2^4%:R*y3^6 )%R }} _ _. 

}}.


Lemma sander (x1 x2 x3 y1 y2 y3 : int) :
  (f1 x1 x2 x3 y1 y2 y3) * (f2 x1 x2 x3 y1 y2 y3) = f3 x1 x2 x3 y1 y2 y3.
Proof.
  unfold f1, f2, f3.
  (* objective : have ring solve this goal.*)
  (* On the analogue problem stated in Z, ring succeeds in less than 5s on 
     the same machine as the one used for the previous tests. *)
Admitted.

  End BiggerExample.
