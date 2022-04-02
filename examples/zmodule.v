(* This file demonstrates the implementation techniques behind Algebra        *)
(* Tactics by applying them to `zmodType`s (additive Abelian groups).         *)
(* This example is also described in the following paper:                     *)
(* Kazuhiko Sakaguchi. Reflexive tactics for algebra, revisited.              *)

From elpi Require Export elpi.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat choice seq.
From mathcomp Require Import fintype finfun bigop order ssralg ssrnum ssrint.
From mathcomp Require Import rat zify.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.

Local Open Scope ring_scope.

Notation zeroz := (Posz 0).
Notation addz := intZmod.addz.
Notation oppz := intZmod.oppz.

(******************************************************************************)
(* Section 2.1                                                                *)
(******************************************************************************)

Module Section_2_1.

Structure eqType := { eq_sort : Type; eq_op : eq_sort -> eq_sort -> bool }.

Definition nat_eqType : eqType := {| eq_sort := nat; eq_op := eqn |}.

Fail Check eq_op 0%N 1%N.

Canonical nat_eqType.

Check eq_op 0%N 1%N.

Definition prod_eqType (T1 T2 : eqType) :=
  {| eq_sort := eq_sort T1 * eq_sort T2;
     eq_op := fun x y => eq_op x.1 y.1 && eq_op x.2 y.2 |}.

Fail Check eq_op (0, 0)%N (0, 1)%N.

Canonical prod_eqType.

Check eq_op (0, 0)%N (0, 1)%N.

Coercion eq_sort : eqType >-> Sortclass.

End Section_2_1.

(******************************************************************************)
(* Normalizing Z-module expressions to formal sums by reflection              *)
(******************************************************************************)

Inductive AGExpr : Type :=
  | AGX : nat -> AGExpr
  | AGO : AGExpr
  | AGOpp : AGExpr -> AGExpr
  | AGAdd : AGExpr -> AGExpr -> AGExpr.

Section AGeval.

Variables (V : Type) (zero : V) (opp : V -> V) (add : V -> V -> V).

Definition mulz (x : V) (n : int) :=
  match n with
    | Posz n => iterop n add x zero
    | Negz n => opp (iterop n.+1 add x zero)
  end.

Fixpoint AGeval (varmap : seq V) (e : AGExpr) : V :=
  match e with
    | AGX j => nth zero varmap j
    | AGO => zero
    | AGOpp e1 => opp (AGeval varmap e1)
    | AGAdd e1 e2 => add (AGeval varmap e1) (AGeval varmap e2)
  end.

Fixpoint AGnorm (e : AGExpr) : seq int :=
  match e with
    | AGX j => ncons j 0 [:: 1]
    | AGO => [::]
    | AGOpp e1 => map -%R (AGnorm e1)
    | AGAdd e1 e2 =>
      (fix add_rec (xs ys : seq int) : seq int :=
         match xs, ys with
           | [::], s | s, [::] => s
           | x :: xs, y :: ys => (x + y) :: add_rec xs ys
         end) (AGnorm e1) (AGnorm e2)
  end.

Definition AGsubst (varmap : seq V) (e : seq int) : V :=
  foldr (fun p n => add (mulz p.1 p.2) n) zero (zip varmap e).

End AGeval.

Lemma AG_norm_subst (V : zmodType) (varmap : seq V) (e : AGExpr) :
  AGsubst 0 -%R +%R varmap (AGnorm e) = AGeval 0 -%R +%R varmap e.
Proof.
rewrite /AGsubst -[mulz _ _ _]/*~%R.
elim: e => /= [j||e1 <-|e1 <- e2 <-].
- elim: j varmap => [|j IHj] [|x varmap] //=.
    by case: varmap => [|? ?]; rewrite /AGsubst /= mulr1z addr0.
  by rewrite /AGsubst /= mulr0z add0r; exact: IHj.
- by case: varmap.
- by elim: (AGnorm e1) varmap => [|x xs IHxs] [|v varmap];
  rewrite /AGsubst /= ?oppr0 // opprD -IHxs raddfN.
- move: (AGnorm e1) (AGnorm e2) varmap.
  elim=> [|x xs IHxs] [|y ys] [|v varmap];
    rewrite /AGsubst /= ?(add0r, addr0) //.
  by rewrite addrACA -IHxs raddfD.
Qed.

Lemma AG_correct (V : zmodType) (varmap : seq V) (e1 e2 : AGExpr) :
  all (fun i => i == 0) (AGnorm (AGAdd e1 (AGOpp e2))) = true ->
  AGeval 0 -%R +%R varmap e1 = AGeval 0 -%R +%R varmap e2.
Proof.
rewrite -!AG_norm_subst /AGsubst -[mulz _ _ _]/*~%R /=.
move: (AGnorm e1) (AGnorm e2) varmap.
elim=> [|x xs IH] [|y ys] [|v varmap] //=.
- rewrite oppr_eq0 => /andP[/eqP ->] /=; rewrite mulr0z add0r.
  elim: ys varmap => [|{}y ys IH] [|{}v varmap] //=.
  by rewrite oppr_eq0 => /andP[/eqP -> /IH <-]; rewrite mulr0z add0r.
- move=> /andP[/eqP ->] /=; rewrite mulr0z add0r.
  elim: xs varmap {IH} => [|{}x xs IH] [|{}v varmap] //=.
  by move=> /andP[/eqP -> /IH ->]; rewrite mulr0z add0r.
- by rewrite subr_eq0 => /andP[/eqP -> /IH] ->.
Qed.

Lemma int_norm_subst (varmap : seq int) (e : AGExpr) :
  AGsubst zeroz oppz addz varmap (AGnorm e) =
  AGeval zeroz oppz addz varmap e.
Proof. exact: AG_norm_subst. Qed.

Lemma int_correct (varmap : seq int) (e1 e2 : AGExpr) :
  all (fun i => i == zeroz) (AGnorm (AGAdd e1 (AGOpp e2))) = true ->
  AGeval zeroz oppz addz varmap e1 = AGeval zeroz oppz addz varmap e2.
Proof. exact: AG_correct. Qed.

(******************************************************************************)
(* Section 2.3 and 2.4                                                        *)
(******************************************************************************)

Ltac int_zmodule_reflection VarMap ZE1 ZE2 :=
  apply: (@int_correct VarMap ZE1 ZE2); [vm_compute; reflexivity].

Elpi Tactic int_zmodule.
Elpi Accumulate lp:{{

pred list-constant o:term, o:list term, o:term.
list-constant T [] {{ @nil lp:T }} :- !.
list-constant T [X|XS] {{ @cons lp:T lp:X lp:XS' }} :- list-constant T XS XS'.

% [quote In Out VarMap]
pred quote i:term, o:term, o:list term.
quote {{ zeroz }} {{ AGO }} _ :- !.
quote {{ oppz lp:In1 }} {{ AGOpp lp:Out1 }} VarMap :- !,
  quote In1 Out1 VarMap.
quote {{ addz lp:In1 lp:In2 }} {{ AGAdd lp:Out1 lp:Out2 }} VarMap :- !,
  quote In1 Out1 VarMap, quote In2 Out2 VarMap.
quote In {{ AGX lp:N }} VarMap :- !, mem VarMap In N.

pred mem o:list term, o:term, o:term.
mem [X|_] X {{ O }} :- !.
mem [_|XS] X {{ S lp:N }} :- !, mem XS X N.

pred close o:list term.
close [] :- !.
close [_|XS] :- close XS.

pred zmod-reflection i:term, i:term, i:term, i:goal, o:list sealed-goal.
zmod-reflection VarMap ZE1 ZE2 G GS :-
  coq.ltac.call "int_zmodule_reflection" [trm VarMap, trm ZE1, trm ZE2] G GS.
zmod-reflection VarMap ZE1 ZE2 _ _ :-
  coq.ltac.fail 0 "Not a valid Z-module equation" VarMap ZE1 ZE2.

pred solve i:goal, o:list sealed-goal.
solve (goal _ _ {{ @eq int lp:T1 lp:T2 }} _ _ as G) GS :-
  quote T1 ZE1 VarMap, !,
  quote T2 ZE2 VarMap, !,
  close VarMap, !,
  list-constant {{ int }} VarMap VarMap', !,
  zmod-reflection VarMap' ZE1 ZE2 G GS.
solve G _ :- coq.ltac.fail 0 "The goal is not an integer equation" G.

}}.
Elpi Typecheck.

Section Examples.

Local Open Scope int_scope.

Local Notation "0" := (Posz O) : int_scope.
Local Notation "- x" := (oppz x%Z) : int_scope.
Local Notation "x + y" := (addz x%Z y%Z) : int_scope.

Goal forall (x y : int), (x + (- y)) + x = (- y) + (x + x).
Proof.
move=> x y.
exact:
(let e1 := AGAdd (AGAdd (AGX 0) (AGOpp (AGX 1))) (AGX 0) in
 let e2 := AGAdd (AGOpp (AGX 1)) (AGAdd (AGX 0) (AGX 0)) in
 @int_correct [:: x; y] e1 e2 erefl).
Restart.
move=> x y.
elpi int_zmodule.
Qed.

End Examples.

(******************************************************************************)
(* Section 3.1                                                                *)
(******************************************************************************)

Ltac poly_zmodule_reflection V VarMap ZE1 ZE2 :=
  apply: (@AG_correct V VarMap ZE1 ZE2); [vm_compute; reflexivity].

Elpi Tactic fail_zmodule.
Elpi Accumulate lp:{{

pred list-constant o:term, o:list term, o:term.
list-constant T [] {{ @nil lp:T }} :- !.
list-constant T [X|XS] {{ @cons lp:T lp:X lp:XS' }} :- list-constant T XS XS'.

% [quote V In Out VarMap]
pred quote i:term, i:term, o:term, o:list term.
quote V {{ @GRing.zero lp:V }} {{ AGO }} _ :- !.
quote V {{ @GRing.opp lp:V lp:In1 }} {{ AGOpp lp:Out1 }} VarMap :- !,
  quote V In1 Out1 VarMap.
quote V {{ @GRing.add lp:V lp:In1 lp:In2 }} {{ AGAdd lp:Out1 lp:Out2 }} VarMap :- !,
  quote V In1 Out1 VarMap, quote V In2 Out2 VarMap.
quote _ In {{ AGX lp:N }} VarMap :- !, mem VarMap In N.

pred mem o:list term, o:term, o:term.
mem [X|_] X {{ O }} :- !.
mem [_|XS] X {{ S lp:N }} :- !, mem XS X N.

pred close o:list term.
close [] :- !.
close [_|XS] :- close XS.

pred zmod-reflection i:term, i:term, i:term, i:term, i:goal, o:list sealed-goal.
zmod-reflection V VarMap ZE1 ZE2 G GS :-
  coq.ltac.call "poly_zmodule_reflection"
    [trm V, trm VarMap, trm ZE1, trm ZE2] G GS.
zmod-reflection _ _ _ _ _ _ :-
  coq.ltac.fail 0 "Not a valid Z-module equation".

pred solve i:goal, o:list sealed-goal.
solve (goal _ _ {{ @eq lp:Ty lp:T1 lp:T2 }} _ [trm V] as G) GS :-
  @ltacfail! 0 => std.assert-ok!
    (coq.unify-eq {{ GRing.Zmodule.sort lp:V }} Ty)
    "The goal is not an equation of the given Z-module", !,
  quote V T1 ZE1 VarMap, !,
  quote V T2 ZE2 VarMap, !,
  close VarMap, !,
  list-constant Ty VarMap VarMap', !,
  zmod-reflection V VarMap' ZE1 ZE2 G GS.
solve G _ :- coq.ltac.fail 0 "The goal is not an equation" G.

}}.
Elpi Typecheck.

Goal forall x y : [zmodType of int * int], x + y + x = y + x + x.
Proof.
move=> x y.
elpi fail_zmodule ([zmodType of int * int]).
Qed.

Goal forall x : int, x + 1 = 1 + x.
Proof.
Fail elpi fail_zmodule (int_ZmodType).
Abort.

(******************************************************************************)
(* Section 3.2                                                                *)
(******************************************************************************)

Elpi Tactic poly_zmodule.
Elpi Accumulate lp:{{

pred list-constant o:term, o:list term, o:term.
list-constant T [] {{ @nil lp:T }} :- !.
list-constant T [X|XS] {{ @cons lp:T lp:X lp:XS' }} :- list-constant T XS XS'.

% [quote V In Out VarMap]
pred quote i:term, i:term, o:term, o:list term.
quote V {{ @GRing.zero lp:V' }} {{ AGO }} _ :- coq.unify-eq V V' ok, !.
quote V {{ @GRing.opp lp:V' lp:In1 }} {{ AGOpp lp:Out1 }} VarMap :-
  coq.unify-eq V V' ok, !, quote V In1 Out1 VarMap.
quote V {{ @GRing.add lp:V' lp:In1 lp:In2 }} {{ AGAdd lp:Out1 lp:Out2 }} VarMap :-
  coq.unify-eq V V' ok, !, quote V In1 Out1 VarMap, quote V In2 Out2 VarMap.
quote _ In {{ AGX lp:N }} VarMap :- !, mem VarMap In N.

pred mem o:list term, o:term, o:term.
mem [X|_] X {{ O }} :- !.
mem [_|XS] X {{ S lp:N }} :- !, mem XS X N.

pred close o:list term.
close [] :- !.
close [_|XS] :- close XS.

pred zmod-reflection i:term, i:term, i:term, i:term, i:goal, o:list sealed-goal.
zmod-reflection V VarMap ZE1 ZE2 G GS :-
  coq.ltac.call "poly_zmodule_reflection"
    [trm V, trm VarMap, trm ZE1, trm ZE2] G GS.
zmod-reflection _ _ _ _ _ _ :-
  coq.ltac.fail 0 "Not a valid Z-module equation".

pred solve i:goal, o:list sealed-goal.
solve (goal _ _ {{ @eq lp:Ty lp:T1 lp:T2 }} _ _ as G) GS :-
  @ltacfail! 0 => std.assert-ok!
    (coq.unify-eq {{ GRing.Zmodule.sort lp:V }} Ty)
    "Cannot find a declared Z-module", !,
  quote V T1 ZE1 VarMap, !,
  quote V T2 ZE2 VarMap, !,
  close VarMap, !,
  list-constant Ty VarMap VarMap', !,
  zmod-reflection V VarMap' ZE1 ZE2 G GS.
solve G _ :- coq.ltac.fail 0 "The goal is not a Z-module equation" G.

}}.
Elpi Typecheck.

Goal forall (x y : int * int), x + y + x = y + x + x.
Proof.
move=> x y.
elpi poly_zmodule.
Qed.

Goal forall x : int, x + 1 = 1 + x.
Proof.
move=> x.
elpi poly_zmodule.
Qed.

(******************************************************************************)
(* Section 4                                                                  *)
(******************************************************************************)

Module Type ZmodSubSig.
Parameter subr : forall U : zmodType, U -> U -> U.
Axiom subrE : subr = (fun _ x y => x + - y).
End ZmodSubSig.

Module Import ZmodSub : ZmodSubSig.
Definition subr (U : zmodType) (x y : U) := x - y.
Definition subrE := erefl subr.
End ZmodSub.

Implicit Types (U V : zmodType).

Inductive MExpr : zmodType -> Type :=
  | MX V : V -> MExpr V
  | MO V : MExpr V
  | MOpp V : MExpr V -> MExpr V
  | MAdd V : MExpr V -> MExpr V -> MExpr V
  | MSub V : MExpr V -> MExpr V -> MExpr V
  | MMorph U V : {additive U -> V} -> MExpr U -> MExpr V.

Fixpoint Meval V (e : MExpr V) : V :=
  match e with
    | MX _ x => x
    | MO _ => 0
    | MOpp _ e1 => - Meval e1
    | MAdd _ e1 e2 => Meval e1 + Meval e2
    | MSub _ e1 e2 => subr (Meval e1) (Meval e2)
    | MMorph _ _ f e1 => f (Meval e1)
  end.

Fixpoint Mnorm U V (f : {additive U -> V}) (e : MExpr U) : V :=
  match e in MExpr U return {additive U -> V} -> V with
    | MX _ x => fun f => f x
    | MO _ => fun _ => 0
    | MOpp _ e1 => fun f => - Mnorm f e1
    | MAdd _ e1 e2 => fun f => Mnorm f e1 + Mnorm f e2
    | MSub _ e1 e2 => fun f => Mnorm f e1 + (- Mnorm f e2)
    | MMorph _ _ g e1 => fun f => Mnorm [additive of f \o g] e1
  end f.

Lemma M_correct_rec U V (f : {additive U -> V}) (e : MExpr U) :
  f (Meval e) = Mnorm f e.
Proof.
elim: e V f => //= {U}.
- by move=> U V f; rewrite raddf0.
- by move=> U e1 IHe1 V f; rewrite raddfN IHe1.
- by move=> U e1 IHe1 e2 IHe2 V f; rewrite raddfD IHe1 IHe2.
- by move=> U e1 IHe1 e2 IHe2 V f; rewrite subrE raddfB IHe1 IHe2.
- by move=> U U' g e1 IHe1 V f; rewrite -IHe1.
Qed.

Lemma M_correct V (e : MExpr V) : Meval e = Mnorm [additive of idfun] e.
Proof. exact: M_correct_rec [additive of idfun] _. Qed.

Ltac morph_zmodule_reflection V VarMap ME1 ME2 ZE1 ZE2 :=
  rewrite [LHS](@M_correct V ME1) [RHS](@M_correct V ME2);
  apply: (@AG_correct V VarMap ZE1 ZE2);
  [vm_compute; reflexivity].

Elpi Tactic morph_zmodule.
Elpi Accumulate lp:{{

pred list-constant o:term, o:list term, o:term.
list-constant T [] {{ @nil lp:T }} :- !.
list-constant T [X|XS] {{ @cons lp:T lp:X lp:XS' }} :- list-constant T XS XS'.

% [quote V F In OutM Out VarMap]
pred quote i:term, i:(term -> term), i:term, o:term, o:term, o:list term.
quote V _ {{ @GRing.zero lp:V' }} {{ MO lp:V }} {{ AGO }} _ :-
  coq.unify-eq V V' ok, !.
quote V F {{ @GRing.opp lp:V' lp:In1 }}
      {{ @MOpp lp:V lp:OutM1 }} {{ AGOpp lp:Out1 }} VarMap :-
  coq.unify-eq V V' ok, !, quote V F In1 OutM1 Out1 VarMap.
quote V F {{ @GRing.add lp:V' lp:In1 lp:In2 }}
      {{ @MAdd lp:V lp:OutM1 lp:OutM2 }} {{ AGAdd lp:Out1 lp:Out2 }} VarMap :-
  coq.unify-eq V V' ok, !,
  quote V F In1 OutM1 Out1 VarMap, quote V F In2 OutM2 Out2 VarMap.
quote V F {{ @subr lp:V' lp:In1 lp:In2 }}
      {{ @MSub lp:V lp:OutM1 lp:OutM2 }} {{ AGAdd lp:Out1 (AGOpp lp:Out2) }}
      VarMap :-
  coq.unify-eq V V' ok, !,
  quote V F In1 OutM1 Out1 VarMap, quote V F In2 OutM2 Out2 VarMap.
quote V F In {{ @MMorph lp:U lp:V lp:G lp:OutM }} Out VarMap :-
  coq.unify-eq {{ @GRing.Additive.apply lp:U lp:V lp:Ph lp:G lp:In1 }} In ok, !,
  quote U (x\ F {{ @GRing.Additive.apply lp:U lp:V lp:Ph lp:G lp:x }})
        In1 OutM Out VarMap.
quote V F In {{ @MX lp:V lp:In }} {{ AGX lp:N }} VarMap :- !,
  mem VarMap (F In) N.

pred mem o:list term, o:term, o:term.
mem [X|_] X {{ O }} :- !.
mem [_|XS] X {{ S lp:N }} :- !, mem XS X N.

pred close o:list term.
close [] :- !.
close [_|XS] :- close XS.

pred zmod-reflection i:term, i:term, i:term, i:term, i:term, i:term,
                     i:goal, o:list sealed-goal.
zmod-reflection V VarMap ZM1 ZM2 ZE1 ZE2 G GS :-
  coq.ltac.call "morph_zmodule_reflection"
    [trm V, trm VarMap, trm ZM1, trm ZM2, trm ZE1, trm ZE2] G GS.
zmod-reflection _ _ _ _ _ _ _ _ :-
  coq.ltac.fail 0 "Not a valid Z-module equation".

pred solve i:goal, o:list sealed-goal.
solve (goal _ _ {{ @eq lp:Ty lp:T1 lp:T2 }} _ _ as G) GS :-
  @ltacfail! 0 => std.assert-ok!
    (coq.unify-eq {{ GRing.Zmodule.sort lp:V }} Ty)
    "Cannot find a declared zmodType", !,
  quote V (x\ x) T1 ZM1 ZE1 VarMap, !,
  quote V (x\ x) T2 ZM2 ZE2 VarMap, !,
  close VarMap, !,
  list-constant Ty VarMap VarMap', !,
  zmod-reflection V VarMap' ZM1 ZM2 ZE1 ZE2 G GS.
solve G _ :- coq.ltac.fail 0 "The goal is not a Z-module equation" G.

}}.
Elpi Typecheck.

Goal forall (x y : int), (x + y)%:~R + x%:~R = (y + x + x)%:~R :> rat.
Proof.
move=> x y.
elpi morph_zmodule.
Qed.

Goal forall (x y : int), (- subr x y)%:~R = y%:~R - x%:~R :> rat.
Proof.
move=> x y.
elpi morph_zmodule.
Qed.

(******************************************************************************)
(* Section 5.2                                                                *)
(******************************************************************************)

Section ZifyRing.

Variable R : ringType.

Structure zifyRing :=
  ZifyRing { rval : R; zval : int; zifyRingE : rval = zval%:~R }.

Canonical zify_zero := @ZifyRing 0 0 (erefl : 0 = 0%:~R).
Canonical zify_one  := @ZifyRing 1 1 (erefl : 1 = 1%:~R).

Lemma zify_opp_subproof e1 : - rval e1 = (- zval e1)%:~R.
Proof. by rewrite zifyRingE mulrNz. Qed.

Canonical zify_opp e1 :=
  @ZifyRing (- rval e1) (- zval e1) (zify_opp_subproof e1).

Lemma zify_add_subproof e1 e2 : rval e1 + rval e2 = (zval e1 + zval e2)%:~R.
Proof. by rewrite 2!zifyRingE intrD. Qed.

Canonical zify_add e1 e2 :=
  @ZifyRing (rval e1 + rval e2) (zval e1 + zval e2) (zify_add_subproof e1 e2).

Lemma zify_mulrz_subproof e1 n : rval e1 *~ n = (zval e1 *~ n)%:~R.
Proof. by rewrite zifyRingE -mulrzA -mulrzz. Qed.

Canonical zify_mulrn e1 n :=
  @ZifyRing (rval e1 *+ n) (zval e1 *+ n) (zify_mulrz_subproof e1 n).

Canonical zify_mulrz e1 n :=
  @ZifyRing (rval e1 *~ n) (zval e1 *~ n) (zify_mulrz_subproof e1 n).

Lemma zify_mul_subproof e1 e2 : rval e1 * rval e2 = (zval e1 * zval e2)%:~R.
Proof. by rewrite 2!zifyRingE intrM. Qed.

Canonical zify_mul e1 e2 :=
  @ZifyRing (rval e1 * rval e2) (zval e1 * zval e2) (zify_mul_subproof e1 e2).

Goal False.
Proof.
move: (0%N) => n.
evar (e : zifyRing).
unify (rval ?e) (1 + n%:~R *+ 2 : R).
Abort.

End ZifyRing.

Lemma zify_eqb (R : numDomainType) (e1 e2 : zifyRing R) :
  (rval e1 == rval e2) = (zval e1 == zval e2).
Proof. by rewrite 2!zifyRingE eqr_int. Qed.

Goal forall n : int, n%:~R *+ 2 + 1 != 0 :> rat.
Proof. move=> n; rewrite zify_eqb /=; lia. Qed.
