From elpi Require Import elpi.

(******************************************************************************)
(* Automatic generation of reification procedure implemented as a translation *)
(* from the interpretation function, i.e., the [quote] tactic reimplemented   *)
(* as a translation                                                           *)
(*                                                                            *)
(* As of now, the translation has the following limitations:                  *)
(* - Given that the interpretation function [eval] takes [n] arguments, the   *)
(*   reification procedure [quote] must take [n + 1] arguments: the term to   *)
(*   be reified, followed by the arguments of [eval].                         *)
(* - The user must specify:                                                   *)
(*   1) which argument of [eval] is the reified syntax tree, by the (0-based) *)
(*      index [NIn], and                                                      *)
(*   2) the input/output modes of the arguments of [quote], except for the    *)
(*      first argument that must be input.                                    *)
(*   The [NIn + 1]-th argument of [quote], i.e., the syntax tree, must be     *)
(*   output.                                                                  *)
(* - The case analysis is done by destructing [NIn]-th argument of [eval],    *)
(*   not by inspecting the body of [eval]. Therefore, nested match is not     *)
(*   supported.                                                               *)
(* - The inductive datatype for reified syntax trees must be uniform.         *)
(* - Variable maps are not supported yet.                                     *)
(******************************************************************************)

Elpi Db genquote lp:{{

% Mapping from interpretation functions to reification procedures:
func interp->quote term -> (term -> prop).

func interp->quote.gen string, term, term, list term -> prop, prop.
interp->quote.gen PredName T (prod N Ty TyF) Args
    (pi x\ P x) (@pi-decl N Ty x\ Pwhd x) :- !,
  @pi-decl N Ty x\ interp->quote.gen PredName T (TyF x) [x|Args] (P x) (Pwhd x).
interp->quote.gen PredName T Ty Args P Pwhd :- !,
  coq.reduction.lazy.whd Ty Ty',
  if (Ty == Ty')
     (std.rev Args Args',
      coq.mk-app T Args' T',
      coq.reduction.lazy.whd T' T'whd,
      (pi x\ coq.elpi.predicate PredName [x|Args'] (PF x)),
      P = interp->quote T' PF,
      Pwhd = interp->quote T'whd PF)
     (interp->quote.gen PredName T Ty' Args P Pwhd).

func distr-pi (any -> list prop) -> list prop.
distr-pi (_\ []) [] :- !.
distr-pi (x\ H x :: T x) ((pi x\ H x) :: T') :- !, distr-pi T T'.

% [indt-decomp T GR Args] decompose an inductive datatype [T] to its type
% constructor [GR] and arguments [Args]
func indt-decomp term -> inductive, list term.
indt-decomp (global (indt GR)) GR [] :- !.
indt-decomp (app [global (indt GR)|Args]) GR Args :- !.

% NB: written in CPS style since it needs to introduce binders at top while
% traversing the term.
func genquote.fold.app
  list term -> ((list term -> (list prop -> list prop) -> prop) -> prop).
genquote.fold.app [] (pf\ pf [] (l\ l)).
genquote.fold.app [T|Ts] PF :- !,
  genquote.fold T P1, genquote.fold.app Ts P2,
  PF = pf\ P1 (t\ ps1\ P2 (ts\ ps2\ pf [t|ts] (b\ ps1 (ps2 b)))).

func genquote.fold term -> ((term -> (list prop -> list prop) -> prop) -> prop).
genquote.fold T (pf\ pi x\ pf x (l\ [QF x | l])) :- interp->quote T QF, !.
genquote.fold (app L) (pf\ P (ts\ pf (app ts))) :- !, genquote.fold.app L P.
genquote.fold T (pf\ pf T (l\ l)) :- !.

func genquote.unfold.ind (term -> prop), term, term -> list prop.
genquote.unfold.ind PFQ T (prod N Ty TyF) Cls' :- !,
  (@pi-decl N Ty x\
    genquote.unfold.ind PFQ { coq.mk-app T [x] } (TyF x) (Cls x)),
  distr-pi Cls Cls'.
genquote.unfold.ind PFQ T _ Cls :- !, genquote.unfold (PFQ T) (-1) Cls.

func genquote.unfold prop, int -> list prop.
genquote.unfold (@pi-decl _ Ty x\ PFQ x) 0 Cls :- !,
  std.assert! (indt-decomp Ty GR TArgs)
    "genquote.unfold: not an inductive type",
  coq.env.indt GR tt NParams NParams' _ Ks Tys,
  std.assert! (NParams = NParams')
    "genquote.unfold: Non-uniform inductive types are not supported",
  std.assert! (NParams = { std.length TArgs }) "genquote.unfold",
  std.map2 Ks Tys
    (k\ ty\ cls\ sigma k' ty'\
       coq.mk-app (global (indc k)) TArgs k',
       coq.subst-prod TArgs ty ty',
       genquote.unfold.ind PFQ k' ty' cls) Clss,
  std.flatten Clss Cls.
genquote.unfold (@pi-decl N Ty x\ PFQ x) NIn Cls' :- !,
  (@pi-decl N Ty x\ genquote.unfold (PFQ x) { calc (NIn - 1) } (Cls x)),
  distr-pi Cls Cls'.
genquote.unfold (interp->quote T PF) _ [PF' (x\ ps\ PF x :- ps [])] :- !,
  (@redflags! coq.redflags.betaiotazeta => coq.reduction.lazy.whd T T'),
  genquote.fold T' PF'.

% [genquote DbName PredName T NIn Modes] takes the interpretation function
% [T], and generates and accumulates the clauses (of [interp-quote] and
% [PredName]) that implements the reification procedure
func genquote string, string, term, int, list argument_mode.
genquote DbName PredName T NIn Modes :-
  std.assert-ok! (coq.typecheck T Ty) "genquote: The given term is ill-typed.",
  std.length Modes NArgs,
  std.assert! ({ coq.count-prods Ty } = NArgs)
    "genquote: The number of the given modes does not match with the type.",
  std.assert! (NIn < NArgs) "genquote: index out of bounds",
  % It looks like [coq.elpi.add-predicate] below does not immediately take
  % effect. For the moment, we write the signature by hand.
  % coq.elpi.add-predicate DbName _ PredName
  %   [pr in "term" | { std.map Modes (mode\ o\ o = pr mode "term") } ],
  interp->quote.gen PredName T Ty [] PFQ PFQwhd,
  (PFQwhd => genquote.unfold PFQwhd NIn Cls),
  coq.say "[DEBUG] genquote accumulates the following clauses:\n",
  std.forall [PFQ|Cls] (cls\
    coq.say cls "\n",
    coq.elpi.accumulate execution-site DbName (clause _ _ cls)).

}}.

(* Example *)

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat.

Inductive Nexpr :=
  | zeroNE
  | succNE of Nexpr
  | addNE of Nexpr & Nexpr
  | subNE of Nexpr & Nexpr
  | mulNE of Nexpr & Nexpr
  | varNE of nat.

Fixpoint evalNE e :=
  match e with
  | zeroNE => O
  | succNE e => S (evalNE e)
  | addNE e1 e2 => evalNE e1 + evalNE e2
  | subNE e1 e2 => evalNE e1 - evalNE e2
  | mulNE e1 e2 => evalNE e1 * evalNE e2
  | varNE n => n
  end.

Elpi Tactic quote.nat.

Elpi Accumulate Db genquote.

Elpi Db quote.nat.db lp:{{

% What I want to automatically obtain:

func interp->quote term -> (term -> prop).
% interp->quote {{ evalNE lp:Out }} (in\ quote.nat in Out) :- !.

pred quote.nat i:term, o:term.
% quote.nat {{ O }} {{ zeroNE }}.
% quote.nat {{ S lp:In }} {{ succNE lp:Out }} :- quote.nat In Out.
% quote.nat {{ lp:In1 + lp:In2 }} {{ addNE lp:Out1 lp:Out2 }} :-
%   quote.nat In1 Out1, quote.nat In2 Out2.
% quote.nat {{ lp:In1 - lp:In2 }} {{ subNE lp:Out1 lp:Out2 }} :-
%   quote.nat In1 Out1, quote.nat In2 Out2.
% quote.nat {{ lp:In1 * lp:In2 }} {{ mulNE lp:Out1 lp:Out2 }} :-
%   quote.nat In1 Out1, quote.nat In2 Out2.
% quote.nat In {{ varNE lp:In }}.

}}.

Elpi Accumulate Db quote.nat.db.

Elpi Query lp:{{
genquote "quote.nat.db" "quote.nat" {{ evalNE }} 0 [out].
}}.

(* Another way to dump the clauses accumulated by [genquote]: *)
(* Elpi Print quote.nat.db "algebra_tactics/quote.nat.db". *)

Section S.
Context (n m : nat).
Elpi Query lp:{{ quote.nat {{ (3 + n) * m }} Out. }}.
End S.
