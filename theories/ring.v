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

Elpi Db ring.db lp:{{

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

pred n-constant o:int, o:term.
n-constant N _ :- not (var N), N < 0, !, fail.
n-constant 0 {{ lib:num.N.N0 }} :- !.
n-constant N {{ lib:num.N.Npos lp:T }} :- !, positive-constant N T.

pred nat-constant o:int, o:term.
nat-constant N _ :- not (var N), N < 0, !, fail.
nat-constant 0  {{ lib:num.nat.O }} :- !.
nat-constant SN {{ lib:num.nat.S lp:M }} :-
  0 < SN, N is SN - 1, nat-constant N M.

pred list-constant o:term, o:list term, o:term.
list-constant T [] {{ @nil lp:T }} :- !.
list-constant T [X|XS] {{ @cons lp:T lp:X lp:XS' }} :- list-constant T XS XS'.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

pred mem o:list term, o:term, o:int.
mem [X|_] X 0 :- !.
mem [_|XS] X M :- !, mem XS X N, M is N + 1.

pred close o:list term.
close [] :- !.
close [_|XS] :- close XS.

% [ring.quote Ring Input Output Varmap]
pred ring.quote i:term, i:term, o:term, o:list term.
ring.quote Ring {{ @GRing.zero lp:Zmodule }} {{ @PEO Z }} _ :-
  coq.unify-eq {{ @GRing.zero lp:Zmodule }}
               {{ @GRing.zero (GRing.Ring.zmodType lp:Ring) }} ok,
  !.
ring.quote Ring {{ @GRing.add lp:Zmodule lp:T1 lp:T2 }} {{ @PEadd Z lp:R1 lp:R2 }} L :-
  coq.unify-eq {{ @GRing.add lp:Zmodule }}
               {{ @GRing.add (GRing.Ring.zmodType lp:Ring) }} ok,
  !,
  ring.quote Ring T1 R1 L,
  ring.quote Ring T2 R2 L.
ring.quote Ring {{ @GRing.opp lp:Zmodule lp:T1 }} {{ @PEopp Z lp:R1 }} L :-
  coq.unify-eq {{ @GRing.opp lp:Zmodule }}
               {{ @GRing.opp (GRing.Ring.zmodType lp:Ring) }} ok,
  !,
  ring.quote Ring T1 R1 L.
% FIXME: [PEeval] is parameterized by a ring morphism [phi : Z -> R] rather than
%        a constant multiplication [GRing.natmul]. So, this does not work.
% ring.quote Ring {{ @GRing.natmul lp:Zmodule lp:T1 lp:N }} {{ @PEmul Z lp:R1 (@PEc Z (Z.of_nat lp:N)) }} L :-
%   coq.unify-eq Zmodule {{ GRing.Ring.zmodType lp:Ring }} ok,
%   !,
%   ring.quote Ring T1 R1 L.
ring.quote Ring {{ @GRing.natmul lp:Zmodule (@GRing.one lp:Ring') lp:N }} {{ @PEc Z (Z.of_nat lp:N) }} _ :-
  coq.unify-eq Zmodule {{ @GRing.Ring.zmodType lp:Ring }} ok,
  coq.unify-eq {{ @GRing.one lp:Ring' }} {{ @GRing.one lp:Ring }} ok,
  !.
ring.quote Ring {{ @intmul lp:Zmodule (@GRing.one lp:Ring') lp:Z }} {{ @PEc Z (Z_of_int lp:Z) }} _ :-
  coq.unify-eq Zmodule {{ @GRing.Ring.zmodType lp:Ring }} ok,
  coq.unify-eq {{ @GRing.one lp:Ring' }} {{ @GRing.one lp:Ring }} ok,
  !.
ring.quote Ring {{ @GRing.one lp:Ring' }} {{ @PEI Z }} _ :-
  coq.unify-eq {{ @GRing.one lp:Ring' }} {{ @GRing.one lp:Ring }} ok,
  !.
ring.quote Ring {{ @GRing.mul lp:Ring' lp:T1 lp:T2 }} {{ @PEmul Z lp:R1 lp:R2 }} L :-
  coq.unify-eq {{ @GRing.mul lp:Ring' }} {{ @GRing.mul lp:Ring }} ok,
  !,
  ring.quote Ring T1 R1 L,
  ring.quote Ring T2 R2 L.
% NB: There are several ways to express exponentiation: [x ^+ n], [x ^ Posz n],
% and [x ^ n%:R]. The last one is inconvertible with others if [n] is not a
% constant.
ring.quote Ring {{ @GRing.exp lp:Ring' lp:T1 lp:N }} {{ @PEpow Z lp:R1 (N.of_nat lp:N) }} L :-
  coq.unify-eq Ring' Ring ok,
  !,
  ring.quote Ring T1 R1 L.
ring.quote Ring {{ @exprz lp:UnitRing lp:T1 lp:Z }} {{ @PEpow Z lp:R1 (N.of_nat lp:N) }} L :-
  coq.unify-eq {{ GRing.UnitRing.ringType lp:UnitRing }} Ring ok,
  coq.unify-eq Z {{ Posz lp:N }} ok,
  !,
  ring.quote Ring T1 R1 L.
ring.quote _ T {{ @PEX Z lp:Pos }} L :-
  mem L T N, positive-constant {calc (N + 1)} Pos, !.
ring.quote _ T _ _ :- coq.error "Unknown" {coq.term->string T}.
% TODO: converse ring

% [field.quote Field Input Output Varmap]
pred field.quote i:term, i:term, o:term, o:list term.
field.quote Field {{ @GRing.zero lp:Zmodule }} {{ @FEO Z }} _ :-
  coq.unify-eq {{ @GRing.zero lp:Zmodule }}
               {{ @GRing.zero (GRing.Field.zmodType lp:Field) }} ok,
  !.
field.quote Field {{ @GRing.add lp:Zmodule lp:T1 lp:T2 }} {{ @FEadd Z lp:R1 lp:R2 }} L :-
  coq.unify-eq {{ @GRing.add lp:Zmodule }}
               {{ @GRing.add (GRing.Field.zmodType lp:Field) }} ok,
  !,
  field.quote Field T1 R1 L,
  field.quote Field T2 R2 L.
field.quote Field {{ @GRing.opp lp:Zmodule lp:T1 }} {{ @FEopp Z lp:R1 }} L :-
  coq.unify-eq {{ @GRing.opp lp:Zmodule }}
               {{ @GRing.opp (GRing.Field.zmodType lp:Field) }} ok,
  !,
  field.quote Field T1 R1 L.
field.quote Field {{ @GRing.natmul lp:Zmodule (@GRing.one lp:Ring) lp:N }} {{ @FEc Z (Z.of_nat lp:N) }} _ :-
  coq.unify-eq Zmodule {{ @GRing.Field.zmodType lp:Field }} ok,
  coq.unify-eq {{ @GRing.one lp:Ring }}
               {{ @GRing.one (GRing.Field.ringType lp:Field) }} ok,
  !.
field.quote Field {{ @intmul lp:Zmodule (@GRing.one lp:Ring) lp:Z }} {{ @FEc Z (Z_of_int lp:Z) }} _ :-
  coq.unify-eq Zmodule {{ @GRing.Field.zmodType lp:Field }} ok,
  coq.unify-eq {{ @GRing.one lp:Ring }}
               {{ @GRing.one (GRing.Field.ringType lp:Field) }} ok,
  !.
field.quote Field {{ @GRing.one lp:Ring }} {{ @FEI Z }} _ :-
  coq.unify-eq {{ @GRing.one lp:Ring }}
               {{ @GRing.one (GRing.Field.ringType lp:Field) }} ok,
  !.
field.quote Field {{ @GRing.mul lp:Ring lp:T1 lp:T2 }} {{ @FEmul Z lp:R1 lp:R2 }} L :-
  coq.unify-eq {{ @GRing.mul lp:Ring }}
               {{ @GRing.mul (GRing.Field.ringType lp:Field) }} ok,
  !,
  field.quote Field T1 R1 L,
  field.quote Field T2 R2 L.
field.quote Field {{ @GRing.exp lp:Ring lp:T1 lp:N }} {{ @FEpow Z lp:R1 (N.of_nat lp:N) }} L :-
  coq.unify-eq Ring {{ GRing.Field.ringType lp:Field }} ok,
  !,
  field.quote Field T1 R1 L.
field.quote Field {{ @exprz lp:UnitRing lp:T1 lp:Z }} {{ @FEpow Z lp:R1 (N.of_nat lp:N) }} L :-
  coq.unify-eq UnitRing {{ GRing.Field.unitRingType lp:Field }} ok,
  coq.unify-eq Z {{ Posz lp:N }} ok,
  !,
  field.quote Field T1 R1 L.
field.quote Field {{ @GRing.inv lp:UnitRing lp:T1 }} {{ @FEinv Z lp:R1 }} L :-
  coq.unify-eq {{ @GRing.inv lp:UnitRing }}
               {{ @GRing.inv (GRing.Field.unitRingType lp:Field) }} ok,
  !,
  field.quote Field T1 R1 L.
field.quote _ T {{ @FEX Z lp:Pos }} L :-
  mem L T N, positive-constant {calc (N + 1)} Pos, !.

field.quote _ T _ _ :- coq.error "Unknown" {coq.term->string T}.

}}.

Elpi Command ring_reify.
Elpi Accumulate Db ring.db.
Elpi Accumulate lp:{{

main [trm Ring, trm Input] :- std.do! [
  InputTy = {{ GRing.Ring.sort lp:Ring }},
  std.assert-ok! (coq.elaborate-skeleton Input InputTy Input') "bad input term",
  std.time (ring.quote Ring Input' Output VarMap) Time,
  list-constant InputTy VarMap VarMapTerm,
  std.assert-ok! (coq.typecheck Output _) "bad output term",
  std.assert-ok! (coq.typecheck VarMapTerm _) "bad varmap",
  @ppwidth! 300 => coq.say { coq.term->string Output },
  @ppwidth! 300 => coq.say { coq.term->string VarMapTerm },
  coq.say "Reification:" Time "sec."
].

}}.
Elpi Typecheck.

Elpi Tactic ring.
Elpi Accumulate Db ring.db.
Elpi Accumulate lp:{{

pred quote-arg i:term, o:list term, i:argument, o:pair term term.
quote-arg Ring VarMap (trm Proof)
          (pr {{ @pair (PExpr Z) (PExpr Z) lp:PE1 lp:PE2 }} Proof) :-
  std.do! [
    @ltacfail! 0 => std.assert-ok!
      (coq.typecheck Proof {{ @eq (GRing.Ring.sort lp:Ring) lp:T1 lp:T2 }})
      "An argument is not a proof of equation of the expected type",
    ring.quote Ring T1 PE1 VarMap,
    ring.quote Ring T2 PE2 VarMap
  ].

pred interp-proofs i:list term, o:term.
interp-proofs [] {{ I }} :- !.
interp-proofs [P] P :- !.
interp-proofs [P|PS] {{ conj lp:P lp:IS }} :- !, interp-proofs PS IS.

pred ring_reflection i:term, i:term, i:term, i:term, i:term, i:term, i:goal, o:list sealed-goal.
ring_reflection ComRing VarMap' Lpe' PE1 PE2 LpeProofs' G GS :-
  coq.ltac.call "ring_reflection"
    [ trm {{ @Rcorrect lp:ComRing 100 lp:VarMap' lp:Lpe' lp:PE1 lp:PE2 lp:LpeProofs' }} ]
    G GS.
ring_reflection _ _ _ _ _ _ _ _ :-
  coq.ltac.fail 0 "Not a valid ring equation".

solve (goal _ _ P _ Args as G) GS :- std.do! [
    @ltacfail! 0 => std.assert-ok!
      (coq.unify-eq P {{ @eq lp:Ty lp:T1 lp:T2 }})
      "The goal is not an equation",
    @ltacfail! 0 => std.assert-ok!
      (coq.unify-eq Ty {{ GRing.Ring.sort lp:Ring }})
      "Cannot find a declared ringType",
    @ltacfail! 0 => std.assert-ok!
      (coq.unify-eq Ty {{ GRing.ComRing.sort lp:ComRing }})
      "Cannot find a declared comRingType",
    std.time (std.unzip { std.map Args (quote-arg Ring VarMap) } Lpe LpeProofs,
              ring.quote Ring T1 PE1 VarMap,
              ring.quote Ring T2 PE2 VarMap) ReifTime,
    coq.say "Reification:" ReifTime "sec.",
    list-constant Ty VarMap VarMap',
    list-constant {{ (PExpr Z * PExpr Z)%type }} Lpe Lpe',
    interp-proofs LpeProofs LpeProofs',
    std.time (ring_reflection ComRing VarMap' Lpe' PE1 PE2 LpeProofs' G GS) ReflTime,
    coq.say "Reflection:" ReflTime "sec.",
  ].

}}.
Elpi Typecheck.

Ltac ring_reflection T := apply T; [vm_compute; reflexivity].

Tactic Notation "ring" constr_list(L) := elpi ring ltac_term_list:(L).

Elpi Tactic field.
Elpi Accumulate Db ring.db.
Elpi Accumulate lp:{{

pred quote-arg i:term, o:list term, i:argument, o:pair term term.
quote-arg Ring VarMap (trm Proof)
          (pr {{ @pair (PExpr Z) (PExpr Z) lp:PE1 lp:PE2 }} Proof) :-
  std.do! [
    @ltacfail! 0 => std.assert-ok!
      (coq.typecheck Proof {{ @eq (GRing.Ring.sort lp:Ring) lp:T1 lp:T2 }})
      "An argument is not a proof of equation of the expected type",
    ring.quote Ring T1 PE1 VarMap,
    ring.quote Ring T2 PE2 VarMap
  ].

pred interp-proofs i:list term, o:term.
interp-proofs [] {{ I }} :- !.
interp-proofs [P] P :- !.
interp-proofs [P|PS] {{ conj lp:P lp:IS }} :- !, interp-proofs PS IS.

pred field_reflection i:term, i:term, i:term, i:term, i:term, i:term, i:goal, o:list sealed-goal.
field_reflection Field VarMap' Lpe' PE1 PE2 LpeProofs' G GS :-
  coq.ltac.call "field_reflection"
    [ trm {{ @Fcorrect lp:Field 100 lp:VarMap' lp:Lpe' lp:PE1 lp:PE2 lp:LpeProofs' }} ]
    G GS.
field_reflection _ _ _ _ _ _ _ _ :-
  coq.ltac.fail 0 "Not a valid field equation".

solve (goal _ _ P _ Args as G) GS :- std.do! [
    @ltacfail! 0 => std.assert-ok!
      (coq.unify-eq P {{ @eq lp:Ty lp:T1 lp:T2 }})
      "The goal is not an equation",
    @ltacfail! 0 => std.assert-ok!
      (coq.unify-eq Ty {{ GRing.Ring.sort lp:Ring }})
      "Cannot find a declared ringType",
    @ltacfail! 0 => std.assert-ok!
      (coq.unify-eq Ty {{ GRing.Field.sort lp:Field }})
      "Cannot find a declared fieldType",
    std.time (std.unzip { std.map Args (quote-arg Ring VarMap) } Lpe LpeProofs,
              field.quote Field T1 PE1 VarMap,
              field.quote Field T2 PE2 VarMap) ReifTime,
    coq.say "Reification:" ReifTime "sec.",
    list-constant Ty VarMap VarMap',
    list-constant {{ (PExpr Z * PExpr Z)%type }} Lpe Lpe',
    interp-proofs LpeProofs LpeProofs',
    std.time (field_reflection Field VarMap' Lpe' PE1 PE2 LpeProofs' G GS) ReflTime,
    coq.say "Reflection:" ReflTime "sec."
  ].

}}.
Elpi Typecheck.

Ltac field_reflection T :=
  apply: T; [reflexivity | reflexivity | reflexivity |
             vm_compute; reflexivity | simpl].

Tactic Notation "field" constr_list(L) := elpi field ltac_term_list:(L).
