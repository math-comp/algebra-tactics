From mathcomp Require all_algebra. (* Remove this line when requiring Rocq > 9.1 *)
From elpi Require Import elpi.
From Coq Require Import ZArith Ring Ring_polynom Field_theory.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat choice seq.
From mathcomp Require Import fintype finfun bigop order ssralg ssrnum ssrint.
From mathcomp.zify Require Import ssrZ zify.
From mathcomp.algebra_tactics Require Import common.
From mathcomp.algebra_tactics Extra Dependency "common.elpi" as common.
From mathcomp.algebra_tactics Extra Dependency "ring.elpi" as ring.
From mathcomp.algebra_tactics Extra Dependency "ring_tac.elpi" as ring_tac.
From mathcomp.algebra_tactics Extra Dependency "field_tac.elpi" as field_tac.

Import GRing.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

Module Import Internals.

Implicit Types (V : nmodType) (R : pzSemiRingType) (F : fieldType).

(* Pushing down morphisms in ring and field expressions by reflection         *)

Fixpoint Reval_eqs C R (lpe : list (RExpr R * RExpr R * PExpr C * PExpr C)) :
  Prop :=
  if lpe is (lhs, rhs, _, _) :: lpe then
    Reval lhs = Reval rhs /\ Reval_eqs lpe else True.

Variant target_comSemiRing :=
  | target_nat
  | target_N
  | target_other_comSemiRing of comPzSemiRingType.

Local Coercion target_comSemiRingType (R : target_comSemiRing) :
  comPzSemiRingType :=
  match R with
  | target_nat => nat
  | target_N => N
  | target_other_comSemiRing R => R
  end.

Definition target_comSemiRingMorph (R : target_comSemiRing) : R -> R :=
  match R with
  | target_nat => GRing.natmul 1
  | target_N => fun n => (N.to_nat n)%:R
  | target_other_comSemiRing _ => id
  end.

Variant target_comRing :=
  | target_int
  | target_Z
  | target_other_comRing of comPzRingType.

Local Coercion target_comRingType (R : target_comRing) : comPzRingType :=
  match R with
  | target_int => int
  | target_Z => Z
  | target_other_comRing R => R
  end.

Definition target_comRingMorph (R : target_comRing) : R -> R :=
  match R with
  | target_int => intr
  | target_Z => fun n => (int_of_Z n)%:~R
  | target_other_comRing _ => id
  end.

Section Snorm.

Variables (R' : pzSemiRingType) (R_of_N : N -> R').
Variables (zero : R') (add : R' -> R' -> R').
Variables (one : R') (mul : R' -> R' -> R') (exp : R' -> N -> R').

Local Notation Snorm := (SemiRing.Rnorm R_of_N zero add one mul exp).

Fixpoint Snorm_list
    (lpe : list (RExpr R' * RExpr R' * PExpr N * PExpr N)) : seq R' :=
  if lpe is (lhs, rhs, _, _) :: lpe then
    Snorm id lhs :: Snorm id rhs :: Snorm_list lpe
  else
    [::].

End Snorm.

Section Rnorm.

Variables (R' : pzRingType) (R_of_Z : Z -> R').
Variables (zero : R') (add : R' -> R' -> R').
Variables (opp : R' -> R') (sub : R' -> R' -> R').
Variables (one : R') (mul : R' -> R' -> R') (exp : R' -> N -> R').

Local Notation Rnorm := (Ring.Rnorm R_of_Z zero add opp sub one mul exp).

Fixpoint Rnorm_list
    (lpe : list (RExpr R' * RExpr R' * PExpr Z * PExpr Z)) : seq R' :=
  if lpe is (lhs, rhs, _, _) :: lpe then
    Rnorm id lhs :: Rnorm id rhs :: Rnorm_list lpe
  else
    [::].

End Rnorm.

(* Normalizing ring and field expressions to the Horner form by reflection    *)

Fixpoint PEeval_list
    C R (R_of_C : C -> R) zero opp add sub one mul exp
    (l : seq R) (lpe : list (RExpr R * RExpr R * PExpr C * PExpr C)) : seq R :=
  if lpe is (_, _, lhs, rhs) :: lpe then
    PEeval zero one add mul sub opp R_of_C id exp l lhs ::
    PEeval zero one add mul sub opp R_of_C id exp l rhs ::
    PEeval_list R_of_C zero opp add sub one mul exp l lpe
  else
    [::].

Definition Scorrect (R : comPzSemiRingType) :=
  let RE := Eq_ext +%R *%R id in
  let RN := SRmorph_Rmorph (Eqsth R) (RN R) in
  ring_correct (Eqsth R) RE (SRth_ARth (Eqsth R) (RS R)) RN (PN R)
    (triv_div_th (Eqsth R) RE (SRth_ARth (Eqsth R) (RS R)) RN).

Lemma semiring_correct
  (R : target_comSemiRing) (n : nat) (l : seq R)
  (lpe : seq (RExpr R * RExpr R * PExpr N * PExpr N))
  (re1 re2 : RExpr R) (pe1 pe2 : PExpr N) :
  Reval_eqs lpe ->
  (forall R_of_N zero add one mul exp,
      SemiRing.Rnorm R_of_N zero add one mul exp
        (@target_comSemiRingMorph R) re1 ::
      SemiRing.Rnorm R_of_N zero add one mul exp
        (@target_comSemiRingMorph R) re2 ::
      Snorm_list R_of_N zero add one mul exp lpe =
      PEeval zero one add mul add id R_of_N id exp l pe1 ::
      PEeval zero one add mul add id R_of_N id exp l pe2 ::
      PEeval_list R_of_N zero id add add one mul exp l lpe) ->
  (let norm_subst' :=
     norm_subst 0 1 N.add N.mul N.add id N.eqb (triv_div 0 1 N.eqb) n
                (mk_monpol_list
                   0 1 N.add N.mul N.add id N.eqb (triv_div 0 1 N.eqb)
                   (map (fun '(_, _, lhs, rhs) => (lhs, rhs)) lpe))
   in
   Peq N.eqb (norm_subst' pe1) (norm_subst' pe2)) ->
  Reval re1 = Reval re2.
Proof.
move=> Hlpe' /(_ (fun n => (nat_of_N n)%:R) 0%R +%R).
move=> /(_ 1%R *%R (fun x n => x ^+ nat_of_N n)) /=.
have /SemiRing.eq_Rnorm Hnorm: @target_comSemiRingMorph R =1 id.
  by case R => //= ?; lia.
rewrite !{}Hnorm -!SemiRing.Rnorm_correct => -[-> -> Hlpe]; apply: Scorrect.
elim: lpe Hlpe Hlpe' => [|[[[{}re1 {}re2] {}pe1] {}pe2] lpe IHlpe] //=.
rewrite /= -!SemiRing.Rnorm_correct //.
by move=> [-> ->] Hlpe [Hpe /(IHlpe Hlpe)] {IHlpe Hlpe} /=; case: lpe.
Qed.

Definition Rcorrect (R : comPzRingType) :=
  let RE := Eq_ext +%R *%R -%R in
  ring_correct
    (Eqsth R) RE (Rth_ARth (Eqsth R) RE (RR R)) (RZ R) (PN R)
    (triv_div_th (Eqsth R) RE (Rth_ARth (Eqsth R) RE (RR R)) (RZ R)).

Lemma ring_correct (R : target_comRing) (n : nat) (l : seq R)
                   (lpe : seq (RExpr R * RExpr R * PExpr Z * PExpr Z))
                   (re1 re2 : RExpr R) (pe1 pe2 : PExpr Z) :
  Reval_eqs lpe ->
  (forall R_of_Z zero opp add sub one mul exp,
      Ring.Rnorm R_of_Z zero add opp sub one mul exp
        (@target_comRingMorph R) re1 ::
      Ring.Rnorm R_of_Z zero add opp sub one mul exp
        (@target_comRingMorph R) re2 ::
      Rnorm_list R_of_Z zero add opp sub one mul exp lpe =
      PEeval zero one add mul sub opp R_of_Z id exp l pe1 ::
      PEeval zero one add mul sub opp R_of_Z id exp l pe2 ::
      PEeval_list R_of_Z zero opp add sub one mul exp l lpe) ->
  (let norm_subst' :=
     norm_subst 0 1 Z.add Z.mul Z.sub Z.opp Z.eqb (triv_div 0 1 Z.eqb) n
                (mk_monpol_list
                   0 1 Z.add Z.mul Z.sub Z.opp Z.eqb (triv_div 0 1 Z.eqb)
                   (map (fun '(_, _, lhs, rhs) => (lhs, rhs)) lpe))
   in
   Peq Z.eqb (norm_subst' pe1) (norm_subst' pe2)) ->
  Reval re1 = Reval re2.
Proof.
move=> Hlpe' /(_ (fun n => (int_of_Z n)%:~R) 0%R -%R +%R (fun x y => x - y)).
move=> /(_ 1%R *%R (fun x n => x ^+ nat_of_N n)) /=.
have /Ring.eq_Rnorm Hnorm: @target_comRingMorph R =1 id by case R => //= ?; lia.
rewrite !Hnorm -!Ring.Rnorm_correct => -[-> -> Hlpe]; apply: Rcorrect.
elim: lpe Hlpe Hlpe' => [|[[[{}re1 {}re2] {}pe1] {}pe2] lpe IHlpe] //=.
rewrite /= -!Ring.Rnorm_correct //.
by move=> [-> ->] Hlpe [Hpe /(IHlpe Hlpe)] {IHlpe Hlpe} /=; case: lpe.
Qed.

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
  PEeval 0 1 +%R *%R (fun x y => x - y) -%R F_of_Z nat_of_N (@GRing.exp F) l e =
  PEeval 0 1 +%R *%R (fun x y => x - y) -%R (fun n => (int_of_Z n)%:~R)
         nat_of_N (@GRing.exp F) l e.
Proof.
elim: e => //= [| ? -> ? -> | ? -> ? -> | ? -> ? -> | ? -> | ? ->] //.
by case=> [|[p|p|]|[p|p|]]; rewrite //= nmulrn; congr intmul; lia.
Qed.

Lemma PCondP l le :
  reflect
    (PCond' True not and 0 1 +%R *%R (fun x y : F => x - y) -%R eq
            (fun n0 : Z => (int_of_Z n0)%:~R) nat_of_N (@GRing.exp F) l le)
    (PCond' true negb andb 0 1 +%R *%R (fun x y : F => x - y) -%R eq_op
            F_of_Z nat_of_N (@GRing.exp F) l le).
Proof.
elim: le => [/=|e1 /= [|e2 le] IH].
- exact: ReflectT.
- by rewrite PEvalE; apply: (iffP negP); apply/contra_not => /eqP.
- by rewrite PEvalE; apply: (iffP andP) => -[/eqP ? /IH ?].
Qed.

End PCond_facts.

Definition Fcorrect F :=
  let RE := Eq_ext +%R *%R -%R in
  Field_correct
    (Eqsth F) RE (congr1 GRing.inv) (F2AF (Eqsth F) RE (RF F)) (RZ F) (PN F)
    (triv_div_th (Eqsth F) RE (Rth_ARth (Eqsth F) RE (RR F)) (RZ F)).

#[local] Notation nFcons00 :=
  ltac:(exact (Fcons00 0 1 Z.add Z.mul Z.sub Z.opp Z.eqb)
        || exact (Fcons00 0 1 Z.add Z.mul Z.sub Z.opp Z.eqb
                    (triv_div 0 1 Z.eqb))) (only parsing).
  (* Replace by LHS when requiring Rocq >= 9.2 *)

Lemma field_correct (F : fieldType) (n : nat) (l : seq F)
                    (lpe : seq (RExpr F * RExpr F * PExpr Z * PExpr Z))
                    (re1 re2 : RExpr F) (fe1 fe2 : FExpr Z) :
  Reval_eqs lpe ->
  (forall R_of_Z zero opp add sub one mul exp div inv,
      Field.Rnorm R_of_Z zero add opp sub one mul exp inv id re1 ::
      Field.Rnorm R_of_Z zero add opp sub one mul exp inv id re2 ::
      Rnorm_list R_of_Z zero add opp sub one mul exp lpe =
      FEeval zero one add mul sub opp div inv R_of_Z id exp l fe1 ::
      FEeval zero one add mul sub opp div inv R_of_Z id exp l fe2 ::
      PEeval_list R_of_Z zero opp add sub one mul exp l lpe) ->
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
      let norm_subst' :=
        norm_subst
          0 1 Z.add Z.mul Z.sub Z.opp Z.eqb (triv_div 0 1 Z.eqb) n
          (mk_monpol_list 0 1 Z.add Z.mul Z.sub Z.opp Z.eqb (triv_div 0 1 Z.eqb)
                          (map (fun '(_, _, lhs, rhs) => (lhs, rhs)) lpe))
      in
      let nfe1 := Field_theory.Fnorm 0 1 Z.add Z.mul Z.sub Z.opp Z.eqb fe1 in
      let nfe2 := Field_theory.Fnorm 0 1 Z.add Z.mul Z.sub Z.opp Z.eqb fe2 in
      Peq Z.eqb (norm_subst' (PEmul (num nfe1) (denum nfe2)))
                (norm_subst' (PEmul (num nfe2) (denum nfe1))) /\
      is_true_ (PCond' true negb_ andb_
                       zero one add mul sub opp Feqb F_of_Z nat_of_N exp l'
                       (Fapp nFcons00
                          (condition nfe1 ++ condition nfe2) [::]))) ->
  Reval re1 = Reval re2.
Proof.
move=> Hlpe' /(_ (fun n => (int_of_Z n)%:~R) 0%R -%R +%R (fun x y => x - y)).
move=> /(_ 1%R *%R (fun x n => x ^+ nat_of_N n) (fun x y => x / y) GRing.inv).
rewrite -!Field.Rnorm_correct => -[-> -> Hlpe].
move=> /(_ _ _ _ _ _ _ _ _ _ _ _ _ _ erefl erefl erefl erefl erefl erefl erefl).
move=> /(_ _ _ _ _ _ _ erefl erefl erefl erefl erefl erefl) [Heq Hcond].
apply: (Fcorrect _ erefl erefl erefl Heq).
  elim: {Heq Hcond}lpe Hlpe Hlpe' => // -[[[{}re1 {}re2] {}pe1] {}pe2].
  move=> lpe IHlpe /=; rewrite -!Ring.Rnorm_correct.
  by move=> [-> ->] Hlpe [Hpe /(IHlpe Hlpe)] {IHlpe Hlpe} /=; case: lpe.
by apply: Pcond_simpl_gen;
  [ exact: Eq_ext | exact/F2AF/RF/Eq_ext | exact: RZ | exact: PN |
    exact/triv_div_th/RZ/Rth_ARth/RR/Eq_ext/Eq_ext/Eqsth |
    move=> _ ->; exact/PCondP ].
Qed.

#[local] Notation nFcons2 :=
  ltac:(exact (Fcons2 0 1 Z.add Z.mul Z.sub Z.opp (pow_pos Z.mul) Z.eqb)
        || exact (Fcons2 0 1 Z.add Z.mul Z.sub Z.opp Z.eqb
                    (triv_div 0 1 Z.eqb))) (only parsing).
  (* Replace by LHS when requiring Rocq >= 9.2 *)

Lemma numField_correct (F : numFieldType) (n : nat) (l : seq F)
                       (lpe : seq (RExpr F * RExpr F * PExpr Z * PExpr Z))
                       (re1 re2 : RExpr F) (fe1 fe2 : FExpr Z) :
  Reval_eqs lpe ->
  (forall R_of_Z zero opp add sub one mul exp div inv,
      Field.Rnorm R_of_Z zero add opp sub one mul exp inv id re1 ::
      Field.Rnorm R_of_Z zero add opp sub one mul exp inv id re2 ::
      Rnorm_list R_of_Z zero add opp sub one mul exp lpe =
      FEeval zero one add mul sub opp div inv R_of_Z id exp l fe1 ::
      FEeval zero one add mul sub opp div inv R_of_Z id exp l fe2 ::
      PEeval_list R_of_Z zero opp add sub one mul exp l lpe) ->
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
      let norm_subst' :=
        norm_subst
          0 1 Z.add Z.mul Z.sub Z.opp Z.eqb (triv_div 0 1 Z.eqb) n
          (mk_monpol_list 0 1 Z.add Z.mul Z.sub Z.opp Z.eqb (triv_div 0 1 Z.eqb)
                          (map (fun '(_, _, lhs, rhs) => (lhs, rhs)) lpe))
      in
      let nfe1 := Field_theory.Fnorm 0 1 Z.add Z.mul Z.sub Z.opp Z.eqb fe1 in
      let nfe2 := Field_theory.Fnorm 0 1 Z.add Z.mul Z.sub Z.opp Z.eqb fe2 in
      Peq Z.eqb (norm_subst' (PEmul (num nfe1) (denum nfe2)))
                (norm_subst' (PEmul (num nfe2) (denum nfe1))) /\
      is_true_ (PCond' true negb_ andb_
                       zero one add mul sub opp Feqb F_of_Z nat_of_N exp l'
                       (Fapp nFcons2
                          (condition nfe1 ++ condition nfe2) [::]))) ->
  Reval re1 = Reval re2.
Proof.
move=> Hlpe' /(_ (fun n => (int_of_Z n)%:~R) 0%R -%R +%R (fun x y => x - y)).
move=> /(_ 1%R *%R (fun x n => x ^+ nat_of_N n) (fun x y => x / y) GRing.inv).
rewrite -!Field.Rnorm_correct => -[-> -> Hlpe].
move=> /(_ _ _ _ _ _ _ _ _ _ _ _ _ _ erefl erefl erefl erefl erefl erefl erefl).
move=> /(_ _ _ _ _ _ _ erefl erefl erefl erefl erefl erefl) [Heq Hcond].
apply: (Fcorrect _ erefl erefl erefl Heq).
  elim: {Heq Hcond}lpe Hlpe Hlpe' => // -[[[{}re1 {}re2] {}pe1] {}pe2].
  move=> lpe IHlpe /=; rewrite -!Ring.Rnorm_correct.
  by move=> [-> ->] Hlpe [Hpe /(IHlpe Hlpe)] {IHlpe Hlpe} /=; case: lpe.
apply: Pcond_simpl_complete;
  [ exact: Eq_ext | exact/F2AF/RF/Eq_ext | exact: RZ | exact: PN |
    exact/triv_div_th/RZ/Rth_ARth/RR/Eq_ext/Eq_ext/Eqsth |
    move=> x y /intr_inj; lia | move=> _ ->; exact/PCondP ].
Qed.

Ltac reflexivity_no_check :=
  move=> *;
  match goal with
    | |- @eq ?T ?LHS ?RHS => exact_no_check (@Logic.eq_refl T LHS)
  end.

Ltac field_normalization :=
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
  move=> is_true_ negb_ andb_ zero one add mul sub opp Feqb F_of_nat exp l;
  move=> is_trueE negbE andbE zeroE oneE addE mulE subE oppE FeqbE F_of_natE;
  move=> expE lE;
  vm_compute; refine (conj erefl _);
  rewrite ?{is_true_}is_trueE ?{negb_}negbE ?{andb_}andbE;
  rewrite ?{zero}zeroE ?{one}oneE ?{add}addE ?{mul}mulE ?{sub}subE ?{opp}oppE;
  rewrite ?{Feqb}FeqbE ?{F_of_nat}F_of_natE ?{exp}expE ?{l}lE.

Ltac field_postprocessing :=
  do ?[apply/andP; split].

End Internals.

(* Auxiliary Ltac code which will be invoked from Elpi *)

Ltac ring_reflection_check Lem R VarMap Lpe RE1 RE2 PE1 PE2 LpeProofs :=
  exact (Lem R 100%N VarMap Lpe RE1 RE2 PE1 PE2 LpeProofs
             ltac:(reflexivity) ltac:(vm_compute; reflexivity)).

Ltac ring_reflection_no_check Lem R VarMap Lpe RE1 RE2 PE1 PE2 LpeProofs :=
  exact_no_check (Lem
    R 100%N VarMap Lpe RE1 RE2 PE1 PE2 LpeProofs
    ltac:(reflexivity_no_check) ltac:(vm_compute; reflexivity)).

Ltac ring_reflection := ring_reflection_check.

Ltac field_reflection_check Lem F VarMap Lpe RE1 RE2 PE1 PE2 LpeProofs :=
  refine (Lem F 100%N VarMap Lpe RE1 RE2 PE1 PE2 LpeProofs
          ltac:(reflexivity) ltac:(field_normalization; field_postprocessing)).

Ltac field_reflection_no_check Lem F VarMap Lpe RE1 RE2 PE1 PE2 LpeProofs :=
  let obligation := fresh in
  eassert (obligation : _);
  [ | exact_no_check (Lem
        F 100%N VarMap Lpe RE1 RE2 PE1 PE2 LpeProofs
        ltac:(reflexivity_no_check)
        ltac:(field_normalization; exact obligation)) ];
  field_postprocessing.

Ltac field_reflection := field_reflection_check.

Strategy expand [addn_expand nat_of_pos_rec_expand nat_of_pos_expand].
Strategy expand [nat_of_N_expand].
Strategy expand [nat_of_large_nat N_of_large_nat Z_of_large_nat].

Strategy expand [Reval Meval SemiRing.Rnorm SemiRing.Mnorm].
Strategy expand [Ring.Rnorm Ring.Mnorm Field.Rnorm Field.Mnorm PEeval FEeval].

Elpi Tactic ring.
Elpi Accumulate Db canonicals.db.
Elpi Accumulate File common ring ring_tac.

Tactic Notation "ring" := elpi ring.
Tactic Notation "ring" ":" ne_constr_list(L) := elpi ring ltac_term_list:(L).
Tactic Notation "#[" attributes(A) "]" "ring" := ltac_attributes:(A) elpi ring.
Tactic Notation "#[" attributes(A) "]" "ring" ":" ne_constr_list(L) :=
  ltac_attributes:(A) elpi ring ltac_term_list:(L).

Elpi Tactic field.
Elpi Accumulate Db canonicals.db.
Elpi Accumulate File common ring field_tac.

Tactic Notation "field" := elpi field.
Tactic Notation "field" ":" ne_constr_list(L) := elpi field ltac_term_list:(L).
Tactic Notation "#[" attributes(A) "]" "field" :=
  ltac_attributes:(A) elpi field.
Tactic Notation "#[" attributes(A) "]" "field" ":" ne_constr_list(L) :=
  ltac_attributes:(A) elpi field ltac_term_list:(L).

Elpi Query lp:{{ canonical-init library "canonicals.db" }}.
Elpi Query lp:{{ coercion-init library "canonicals.db" }}.
