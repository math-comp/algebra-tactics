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

pred z-constant o:int, o:term.
z-constant N {{ lib:num.Z.Zneg lp:T }} :-
  N < 0, !, positive-constant {calc (~ N)} T.
z-constant 0 {{ lib:num.Z.Z0 }} :- !.
z-constant N {{ lib:num.Z.Zpos lp:T }} :- 0 < N, !, positive-constant N T.

pred nat-constant o:int, o:term.
nat-constant N _ :- not (var N), N < 0, !, fail.
nat-constant 0 {{ lib:num.nat.O }} :- !.
nat-constant SN SM :-
  var SM, 0 < SN, !,
  nat-constant {calc (SN - 1)} M,
  SM = {{ lib:num.nat.S lp:M }}.
nat-constant SN {{ lib:num.nat.S lp:M }} :-
  var SN, !, nat-constant N M, SN is N + 1.

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

pred field-mode.

% [ring-to-field Ring Field]
% [Field] is optionally a [fieldType] instance of [Ring : ringType].
pred ring-to-field i:term, o:option term.
ring-to-field Ring (some Field) :-
  field-mode,
  coq.unify-eq {{ GRing.Ring.sort lp:Ring }} {{ GRing.Field.sort lp:Field }} ok,
  !.
ring-to-field _ none.

% [ring.quote.nat(1|2) Ring Input OutM Out VarMap]
% - [Ring] is a [ringType] instance,
% - [Input] is a term of type [nat],
% - [OutM] and [Out] are reified terms of [Input], and
% - [VarMap] is a variable map.
% [Input] of [ring.quote.nat1] is possibly a constant that reduces to
% [S (..(S O)..)], but of [ring.quote.nat2] is not.
pred ring.quote.nat1 i:term, i:term, o:term, o:term, o:list term.
ring.quote.nat1 _ In {{ @NEX lp:In }} Out _ :-
  % TODO: more efficient constant detection
  if field-mode (Out = {{ @FEc Z lp:Out' }}) (Out = {{ @PEc Z lp:Out' }}),
  nat-constant N { coq.reduction.vm.norm In {{ nat }} }, !,
  z-constant N Out'.
ring.quote.nat1 Ring In OutM Out VarMap :- !,
  ring.quote.nat2 Ring In OutM Out VarMap.

pred ring.quote.nat2 i:term, i:term, o:term, o:term, o:list term.
ring.quote.nat2 Ring {{ addn lp:In1 lp:In2 }}
                {{ @NEadd lp:OutM1 lp:OutM2 }} Out VarMap :- !,
  if field-mode (Out = {{ @FEadd Z lp:Out1 lp:Out2 }})
                (Out = {{ @PEadd Z lp:Out1 lp:Out2 }}), !,
  ring.quote.nat1 Ring In1 OutM1 Out1 VarMap, !,
  ring.quote.nat1 Ring In2 OutM2 Out2 VarMap.
ring.quote.nat2 Ring {{ S lp:In1 }} {{ NEsucc lp:OutM1 }} Out VarMap :- !,
  if field-mode (Out = {{ @FEadd Z (@FEI Z) lp:Out1 }})
                (Out = {{ @PEadd Z (@PEI Z) lp:Out1 }}), !,
  ring.quote.nat2 Ring In1 OutM1 Out1 VarMap.
ring.quote.nat2 Ring {{ muln lp:In1 lp:In2 }}
                {{ NEmul lp:OutM1 lp:OutM2 }} Out VarMap :- !,
  if field-mode (Out = {{ @FEmul Z lp:Out1 lp:Out2 }})
                (Out = {{ @PEmul Z lp:Out1 lp:Out2 }}), !,
  ring.quote.nat1 Ring In1 OutM1 Out1 VarMap, !,
  ring.quote.nat1 Ring In2 OutM2 Out2 VarMap.
ring.quote.nat2 Ring {{ expn lp:In1 lp:In2 }}
                {{ NEexp lp:OutM1 lp:In2 }} Out VarMap :-
  if field-mode (Out = {{ @FEpow Z lp:Out1 lp:Out2 }})
                (Out = {{ @PEpow Z lp:Out1 lp:Out2 }}),
  nat-constant Exp { coq.reduction.vm.norm In2 {{ nat }} },
  !,
  ring.quote.nat2 Ring In1 OutM1 Out1 VarMap, !,
  n-constant Exp Out2.
ring.quote.nat2 Ring In {{ NEX lp:In }} Out VarMap :-
  if field-mode (Out = {{ @FEX Z lp:Out' }}) (Out = {{ @PEX Z lp:Out' }}),
  mem VarMap {{ @GRing.natmul (GRing.Ring.zmodType lp:Ring) (@GRing.one lp:Ring) lp:In }} N,
  positive-constant {calc (N + 1)} Out',
  !.

% [ring.quote SrcRing SrcField TgtRing MorphFun Morph Input OutM Out VarMap]
% - [SrcRing] and [TgtRing] are [ringType] instances,
% - [SrcField] is optionally a [fieldType] instance such that
%   [GRing.Field.ringType SrcField = SrcRing],
% - [Morph] is a ring morphism from [SrcRing] to [TgtRing] whose underlying
%   function is [MorphFun],
% - [Input] is a term of type [SrcRing],
% - [OutM] and [Out] are reified terms of [Input], and
% - [VarMap] is a variable map.
pred ring.quote i:term, i:option term, i:term, i:(term -> term), i:term,
                i:term, o:term, o:term, o:list term.
% 0%R
ring.quote SrcRing _ _ _ _ {{ @GRing.zero lp:SrcZmodule }}
           {{ @RE0 lp:SrcRing }} Out _ :-
  if field-mode (Out = {{ @FEO Z }}) (Out = {{ @PEO Z }}),
  coq.unify-eq {{ @GRing.zero lp:SrcZmodule }}
               {{ @GRing.zero (GRing.Ring.zmodType lp:SrcRing) }} ok,
  !.
% -%R
ring.quote SrcRing SrcField TgtRing MorphFun Morph
           {{ @GRing.opp lp:SrcZmodule lp:In1 }}
           {{ @REopp lp:SrcRing lp:OutM1 }} Out VarMap :-
  if field-mode (Out = {{ @FEopp Z lp:Out1 }}) (Out = {{ @PEopp Z lp:Out1 }}),
  coq.unify-eq {{ @GRing.opp lp:SrcZmodule }}
               {{ @GRing.opp (GRing.Ring.zmodType lp:SrcRing) }} ok,
  !,
  ring.quote SrcRing SrcField TgtRing MorphFun Morph In1 OutM1 Out1 VarMap.
% +%R
ring.quote SrcRing SrcField TgtRing MorphFun Morph
           {{ @GRing.add lp:SrcZmodule lp:In1 lp:In2 }}
           {{ @REadd lp:SrcRing lp:OutM1 lp:OutM2 }} Out VarMap :-
  if field-mode (Out = {{ @FEadd Z lp:Out1 lp:Out2 }})
                (Out = {{ @PEadd Z lp:Out1 lp:Out2 }}),
  coq.unify-eq {{ @GRing.add lp:SrcZmodule }}
               {{ @GRing.add (GRing.Ring.zmodType lp:SrcRing) }} ok,
  !,
  ring.quote SrcRing SrcField TgtRing MorphFun Morph In1 OutM1 Out1 VarMap, !,
  ring.quote SrcRing SrcField TgtRing MorphFun Morph In2 OutM2 Out2 VarMap.
% (_ *+ _)%R
ring.quote SrcRing SrcField TgtRing MorphFun Morph
           {{ @GRing.natmul lp:SrcZmodule lp:In1 lp:In2 }}
           {{ @REmuln lp:SrcRing lp:OutM1 lp:OutM2 }} Out VarMap :-
  if field-mode (Out = {{ @FEmul Z lp:Out1 lp:Out2 }})
                (Out = {{ @PEmul Z lp:Out1 lp:Out2 }}),
  coq.unify-eq SrcZmodule {{ @GRing.Ring.zmodType lp:SrcRing }} ok,
  !,
  ring.quote SrcRing SrcField TgtRing MorphFun Morph In1 OutM1 Out1 VarMap, !,
  ring.quote.nat1 TgtRing In2 OutM2 Out2 VarMap.
% (_ *~ _)%R
ring.quote SrcRing SrcField TgtRing MorphFun Morph
           {{ @intmul lp:SrcZmodule lp:In1 lp:In2 }}
           {{ @REmulz lp:SrcRing lp:OutM1 lp:OutM2 }} Out VarMap :-
  if field-mode (Out = {{ @FEmul Z lp:Out1 lp:Out2 }})
                (Out = {{ @PEmul Z lp:Out1 lp:Out2 }}),
  coq.unify-eq SrcZmodule {{ @GRing.Ring.zmodType lp:SrcRing }} ok,
  !,
  ring.quote SrcRing SrcField TgtRing MorphFun Morph In1 OutM1 Out1 VarMap, !,
  ring.quote
    {{ int_Ring }} none TgtRing
    (n\ {{ @intmul (GRing.Ring.zmodType lp:TgtRing) (@GRing.one lp:TgtRing) lp:n }})
    {{ @intmul1_rmorphism lp:TgtRing }} In2 OutM2 Out2 VarMap.
% 1%R
ring.quote SrcRing _ _ _ _ {{ @GRing.one lp:SrcRing' }}
           {{ @RE1 lp:SrcRing }} Out _ :-
  if field-mode (Out = {{ @FEI Z }}) (Out = {{ @PEI Z }}),
  coq.unify-eq {{ @GRing.one lp:SrcRing' }} {{ @GRing.one lp:SrcRing }} ok,
  !.
% *%R
ring.quote SrcRing SrcField TgtRing MorphFun Morph
           {{ @GRing.mul lp:SrcRing' lp:In1 lp:In2 }}
           {{ @REmul lp:SrcRing lp:OutM1 lp:OutM2 }} Out VarMap :-
  if field-mode (Out = {{ @FEmul Z lp:Out1 lp:Out2 }})
                (Out = {{ @PEmul Z lp:Out1 lp:Out2 }}),
  coq.unify-eq {{ @GRing.mul lp:SrcRing' }} {{ @GRing.mul lp:SrcRing }} ok,
  !,
  ring.quote SrcRing SrcField TgtRing MorphFun Morph In1 OutM1 Out1 VarMap, !,
  ring.quote SrcRing SrcField TgtRing MorphFun Morph In2 OutM2 Out2 VarMap.
% (_ ^+ _)%R
% TODO: Treat [GRing.exp] as morphisms
ring.quote SrcRing SrcField TgtRing MorphFun Morph
           {{ @GRing.exp lp:SrcRing' lp:In1 lp:In2 }}
           {{ @REexpn lp:SrcRing lp:OutM1 lp:In2 }} Out VarMap :-
  if field-mode (Out = {{ @FEpow Z lp:Out1 lp:Out2 }})
                (Out = {{ @PEpow Z lp:Out1 lp:Out2 }}),
  coq.unify-eq SrcRing' SrcRing ok,
  nat-constant Exp { coq.reduction.vm.norm In2 {{ nat }} },
  !,
  ring.quote SrcRing SrcField TgtRing MorphFun Morph In1 OutM1 Out1 VarMap, !,
  n-constant Exp Out2.
% (_ ^ _)%R
ring.quote SrcRing SrcField TgtRing MorphFun Morph
           {{ @exprz lp:SrcUnitRing lp:In1 lp:In2 }}
           {{ @REexpn lp:SrcRing lp:OutM1 lp:In2' }} Out VarMap :-
  if field-mode (Out = {{ @FEpow Z lp:Out1 lp:Out2 }})
                (Out = {{ @PEpow Z lp:Out1 lp:Out2 }}),
  coq.unify-eq {{ GRing.UnitRing.ringType lp:SrcUnitRing }} SrcRing ok,
  coq.unify-eq In2 {{ Posz lp:In2' }} ok,
  nat-constant Exp { coq.reduction.vm.norm In2' {{ nat }} },
  !,
  ring.quote SrcRing SrcField TgtRing MorphFun Morph In1 OutM1 Out1 VarMap, !,
  n-constant Exp Out2.
% _^-1
ring.quote SrcRing (some SrcField) TgtRing MorphFun Morph
           {{ @GRing.inv lp:SrcUnitRing' lp:In1 }}
           {{ @REinv lp:SrcField lp:OutM1 }} {{ @FEinv Z lp:Out1 }} VarMap :-
  field-mode,
  coq.unify-eq {{ @GRing.inv lp:SrcUnitRing' }}
               {{ @GRing.inv (GRing.Field.unitRingType lp:SrcField) }} ok,
  !,
  ring.quote SrcRing (some SrcField) TgtRing MorphFun Morph
             In1 OutM1 Out1 VarMap.
% Posz
ring.quote SrcRing _ TgtRing _ _
           {{ Posz lp:In }} {{ @REposz lp:OutM }} Out VarMap :-
  coq.unify-eq {{ int_Ring }} SrcRing ok,
  !,
  ring.quote.nat1 TgtRing In OutM Out VarMap.
% Negz
ring.quote SrcRing _ TgtRing _ _ {{ Negz lp:In }}
           {{ @REnegz lp:OutM' }} Out VarMap :-
  if field-mode (Out = {{ @FEopp Z (@FEadd Z (@FEI Z) lp:Out') }})
                (Out = {{ @PEopp Z (@PEadd Z (@PEI Z) lp:Out') }}),
  coq.unify-eq {{ int_Ring }} SrcRing ok,
  !,
  ring.quote.nat1 TgtRing In OutM' Out' VarMap.
% morphisms
ring.quote SrcRing _ TgtRing MorphFun Morph In
           {{ @REmorph lp:NewSrcRing lp:SrcRing lp:NewMorph lp:OutM }}
           Out VarMap :-
  NewMorphFun = (x\ {{ @GRing.RMorphism.apply
                      lp:NewSrcRing lp:SrcRing _ lp:NewMorph lp:x }}),
  coq.unify-eq In (NewMorphFun In1) ok,
  !,
  % TODO: for concrete morphisms, should we unpack [NewMorph]?
  CompMorph = {{ @GRing.comp_rmorphism lp:NewSrcRing lp:SrcRing lp:TgtRing
                                       lp:Morph lp:NewMorph }},
  ring.quote NewSrcRing { ring-to-field NewSrcRing } TgtRing
             (x\ MorphFun (NewMorphFun x)) CompMorph In1 OutM Out VarMap.
% variables
ring.quote SrcRing _ _ MorphFun _ In {{ @REX lp:SrcRing lp:In }} Out VarMap :-
  if field-mode (Out = {{ @FEX Z lp:Pos }}) (Out = {{ @PEX Z lp:Pos }}),
  mem VarMap (MorphFun In) N,
  positive-constant {calc (N + 1)} Pos,
  !.
ring.quote _ _ _ _ _ In _ _ _ :- coq.error "Unknown" {coq.term->string In}.
% TODO: converse ring

}}.

Elpi Command ring_reify.
Elpi Accumulate Db ring.db.
Elpi Accumulate lp:{{

main [trm Ring, trm Input] :- std.do! [
  InputTy = {{ GRing.Ring.sort lp:Ring }},
  std.assert-ok! (coq.elaborate-skeleton Input InputTy Input') "bad input term",
  std.time (
    ring.quote Ring none Ring (x\ x) {{ @GRing.idfun_rmorphism lp:Ring }}
               Input' OutM Out VarMap
  ) Time,
  list-constant InputTy VarMap VarMapTerm,
  std.assert-ok! (coq.typecheck OutM _) "bad output term",
  std.assert-ok! (coq.typecheck Out _)  "bad output term",
  std.assert-ok! (coq.typecheck VarMapTerm _) "bad varmap",
  @ppwidth! 300 => coq.say { coq.term->string OutM },
  @ppwidth! 300 => coq.say { coq.term->string Out },
  @ppwidth! 300 => coq.say { coq.term->string VarMapTerm },
  coq.say "Reification:" Time "sec."
].

}}.
Elpi Typecheck.

Elpi Tactic ring.
Elpi Accumulate Db ring.db.
Elpi Accumulate lp:{{

pred append-last-hyp-to-args i:sealed-goal, o:sealed-goal.
append-last-hyp-to-args (nabla G) (nabla G1) :-
  pi x\ append-last-hyp-to-args (G x) (G1 x).
append-last-hyp-to-args (seal (goal Ctx RE Ty E Args))
                        (seal (goal Ctx RE Ty E Args1)) :-
  Ctx = [decl X _ _|_],
  std.append Args [trm X] Args1.

pred with-top-hyp i:goal, o:list sealed-goal.
with-top-hyp (goal _ _ (prod N Src _) _ A as G) [G3] :- !,
  refine (fun N Src _) G [G1],
  coq.ltac.set-goal-arguments A G G1 G2,
  append-last-hyp-to-args G2 G3.

pred quote-arg i:term, o:list term, i:argument, o:pair term term.
quote-arg Ring VarMap (trm Proof)
          (pr {{ @pair (PExpr Z) (PExpr Z) lp:PE1 lp:PE2 }} Proof') :-
  std.do! [
    @ltacfail! 0 => std.assert-ok!
      (coq.typecheck Proof {{ @eq (GRing.Ring.sort lp:Ring) lp:T1 lp:T2 }})
      "An argument is not a proof of equation of the expected type",
    IdRingMorph = {{ @GRing.idfun_rmorphism lp:Ring }},
    ring.quote Ring none Ring (x\ x) IdRingMorph T1 RE1 PE1 VarMap,
    ring.quote Ring none Ring (x\ x) IdRingMorph T2 RE2 PE2 VarMap,
    RMcorrect1 = {{ @RMEeval_correct lp:Ring lp:Ring lp:IdRingMorph lp:RE1 }},
    RMcorrect2 = {{ @RMEeval_correct lp:Ring lp:Ring lp:IdRingMorph lp:RE2 }},
    Proof' = {{ lib:ring.etrans (lib:ring.esym lp:RMcorrect1)
                                (lib:ring.etrans lp:Proof lp:RMcorrect2) }}
  ].

pred interp-proofs i:list term, o:term.
interp-proofs [] {{ I }} :- !.
interp-proofs [P] P :- !.
interp-proofs [P|PS] {{ conj lp:P lp:IS }} :- !, interp-proofs PS IS.

pred ring-reflection i:term, i:term, i:term, i:term, i:term, i:term, i:term,
                     i:term, i:term, i:goal, o:list sealed-goal.
ring-reflection
    Ring ComRing VarMap' Lpe' RE1 RE2 PE1 PE2 LpeProofs' G GS :-
  IdRingMorph = {{ @GRing.idfun_rmorphism lp:Ring }},
  RMcorrect1 = {{ @RMEeval_correct lp:Ring lp:Ring lp:IdRingMorph lp:RE1 }},
  RMcorrect2 = {{ @RMEeval_correct lp:Ring lp:Ring lp:IdRingMorph lp:RE2 }},
  Rcorrect = {{ @Rcorrect lp:ComRing 100 lp:VarMap' lp:Lpe' lp:PE1 lp:PE2 lp:LpeProofs' }},
  coq.ltac.call "ring_reflection"
    [ trm RMcorrect1, trm RMcorrect2, trm Rcorrect ] G GS.
ring-reflection _ _ _ _ _ _ _ _ _ _ _ :-
  coq.ltac.fail 0 "Not a valid ring equation".

pred ring i:goal, o:list sealed-goal.
ring (goal _ _ P _ Args as G) GS :- std.do! [
    @ltacfail! 0 => std.assert-ok!
      (coq.unify-eq P {{ @eq lp:Ty lp:T1 lp:T2 }})
      "The goal is not an equation",
    @ltacfail! 0 => std.assert-ok!
      (coq.unify-eq Ty {{ GRing.Ring.sort lp:Ring }})
      "Cannot find a declared ringType",
    @ltacfail! 0 => std.assert-ok!
      (coq.unify-eq Ty {{ GRing.ComRing.sort lp:ComRing }})
      "Cannot find a declared comRingType",
    std.time (
      std.unzip { std.map Args (quote-arg Ring VarMap) } Lpe LpeProofs,
      IdRingMorph = {{ @GRing.idfun_rmorphism lp:Ring }},
      ring.quote Ring none Ring (x\ x) IdRingMorph T1 RE1 PE1 VarMap,
      ring.quote Ring none Ring (x\ x) IdRingMorph T2 RE2 PE2 VarMap
    ) ReifTime,
    coq.say "Reification:" ReifTime "sec.",
    list-constant Ty VarMap VarMap',
    list-constant {{ (PExpr Z * PExpr Z)%type }} Lpe Lpe',
    interp-proofs LpeProofs LpeProofs',
    std.assert-ok! (coq.typecheck LpeProofs' _) "Ill-typed equations",
    std.time (
      ring-reflection Ring ComRing VarMap' Lpe' RE1 RE2 PE1 PE2 LpeProofs' G GS
    ) ReflTime,
    coq.say "Reflection:" ReflTime "sec.",
  ].

shorten coq.ltac.{ open, repeat, all,  thenl }.

msolve GL SubGL :- all (thenl [repeat (open with-top-hyp), open ring]) GL SubGL.

}}.
Elpi Typecheck.

Ltac ring_reflection RMcorrect1 RMcorrect2 Rcorrect :=
  apply: (eq_trans RMcorrect1);
  apply: (eq_trans _ (esym RMcorrect2));
  apply: Rcorrect;
  [vm_compute; reflexivity].

Tactic Notation "ring" := elpi ring.
Tactic Notation "ring" ":" ne_constr_list(L) := elpi ring ltac_term_list:(L).

Elpi Tactic field.
Elpi Accumulate Db ring.db.
Elpi Accumulate lp:{{

pred append-last-hyp-to-args i:sealed-goal, o:sealed-goal.
append-last-hyp-to-args (nabla G) (nabla G1) :-
  pi x\ append-last-hyp-to-args (G x) (G1 x).
append-last-hyp-to-args (seal (goal Ctx RE Ty E Args))
                        (seal (goal Ctx RE Ty E Args1)) :-
  Ctx = [decl X _ _|_],
  std.append Args [trm X] Args1.

pred with-top-hyp i:goal, o:list sealed-goal.
with-top-hyp (goal _ _ (prod N Src _) _ A as G) [G3] :- !,
  refine (fun N Src _) G [G1],
  coq.ltac.set-goal-arguments A G G1 G2,
  append-last-hyp-to-args G2 G3.

pred quote-arg i:term, o:list term, i:argument, o:pair term term.
quote-arg Ring VarMap (trm Proof)
          (pr {{ @pair (PExpr Z) (PExpr Z) lp:PE1 lp:PE2 }} Proof') :-
  std.do! [
    @ltacfail! 0 => std.assert-ok!
      (coq.typecheck Proof {{ @eq (GRing.Ring.sort lp:Ring) lp:T1 lp:T2 }})
      "An argument is not a proof of equation of the expected type",
    IdRingMorph = {{ @GRing.idfun_rmorphism lp:Ring }},
    ring.quote Ring none Ring (x\ x) IdRingMorph T1 RE1 PE1 VarMap,
    ring.quote Ring none Ring (x\ x) IdRingMorph T2 RE2 PE2 VarMap,
    RMcorrect1 = {{ @RMEeval_correct lp:Ring lp:Ring lp:IdRingMorph lp:RE1 }},
    RMcorrect2 = {{ @RMEeval_correct lp:Ring lp:Ring lp:IdRingMorph lp:RE2 }},
    Proof' = {{ lib:ring.etrans (lib:ring.esym lp:RMcorrect1)
                                (lib:ring.etrans lp:Proof lp:RMcorrect2) }}
  ].

pred interp-proofs i:list term, o:term.
interp-proofs [] {{ I }} :- !.
interp-proofs [P] P :- !.
interp-proofs [P|PS] {{ conj lp:P lp:IS }} :- !, interp-proofs PS IS.

pred field-reflection i:term, i:term, i:term, i:term, i:term, i:term, i:term,
                      i:term, i:term, i:goal, o:list sealed-goal.
field-reflection Ring Field VarMap' Lpe' RE1 RE2 PE1 PE2 LpeProofs' G GS :-
  IdRingMorph = {{ @GRing.idfun_rmorphism lp:Ring }},
  FMcorrect1 = {{ @FMEeval_correct lp:Ring lp:Field lp:IdRingMorph lp:RE1 }},
  FMcorrect2 = {{ @FMEeval_correct lp:Ring lp:Field lp:IdRingMorph lp:RE2 }},
  Fcorrect = {{ @Fcorrect lp:Field 100 lp:VarMap' lp:Lpe' lp:PE1 lp:PE2 lp:LpeProofs' }},
  coq.ltac.call "field_reflection"
    [ trm FMcorrect1, trm FMcorrect2, trm Fcorrect ] G GS.
field-reflection _ _ _ _ _ _ _ _ _ _ _ :-
  coq.ltac.fail 0 "Not a valid ring equation".

pred field i:goal, o:list sealed-goal.
field (goal _ _ P _ Args as G) GS :- std.do! [
    @ltacfail! 0 => std.assert-ok!
      (coq.unify-eq P {{ @eq lp:Ty lp:T1 lp:T2 }})
      "The goal is not an equation",
    @ltacfail! 0 => std.assert-ok!
      (coq.unify-eq Ty {{ GRing.Ring.sort lp:Ring }})
      "Cannot find a declared ringType",
    @ltacfail! 0 => std.assert-ok!
      (coq.unify-eq Ty {{ GRing.Field.sort lp:Field }})
      "Cannot find a declared fieldType",
    std.time (
      std.unzip { std.map Args (quote-arg Ring VarMap) } Lpe LpeProofs,
      IdRingMorph = {{ @GRing.idfun_rmorphism lp:Ring }},
      field-mode =>
        ring.quote Ring (some Field) Ring (x\ x) IdRingMorph T1 RE1 PE1 VarMap,
      field-mode =>
        ring.quote Ring (some Field) Ring (x\ x) IdRingMorph T2 RE2 PE2 VarMap
    ) ReifTime,
    coq.say "Reification:" ReifTime "sec.",
    list-constant Ty VarMap VarMap',
    list-constant {{ (PExpr Z * PExpr Z)%type }} Lpe Lpe',
    interp-proofs LpeProofs LpeProofs',
    std.assert-ok! (coq.typecheck LpeProofs' _) "Ill-typed equations",
    std.time (
      field-reflection Ring Field VarMap' Lpe' RE1 RE2 PE1 PE2 LpeProofs' G GS
    ) ReflTime,
    coq.say "Reflection:" ReflTime "sec.",
  ].

shorten coq.ltac.{ open, repeat, all,  thenl }.

msolve GL SubGL :- all (thenl [repeat (open with-top-hyp), open field]) GL SubGL.

}}.
Elpi Typecheck.

Ltac field_reflection RMcorrect1 RMcorrect2 Rcorrect :=
  apply: (eq_trans RMcorrect1);
  apply: (eq_trans _ (esym RMcorrect2));
  apply: Rcorrect; [reflexivity | reflexivity | reflexivity |
                    vm_compute; reflexivity | simpl].

Tactic Notation "field" := elpi field.
Tactic Notation "field" ":" ne_constr_list(L) := elpi field ltac_term_list:(L).
