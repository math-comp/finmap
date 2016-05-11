(*************************************************************************)
(* Copyright (C) 2012 - 2016 (Draft)                                     *)
(* C. Cohen                                                              *)
(* Based on prior works by                                               *)
(* D. Dreyer, G. Gonthier, A. Nanevski, P-Y Strub, B. Ziliani            *)
(*                                                                       *)
(* This program is free software: you can redistribute it and/or modify  *)
(* it under the terms of the GNU General Public License as published by  *)
(* the Free Software Foundation, either version 3 of the License, or     *)
(* (at your option) any later version.                                   *)
(*                                                                       *)
(* This program is distributed in the hope that it will be useful,       *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the         *)
(* GNU General Public License for more details.                          *)
(*                                                                       *)
(* You should have received a copy of the GNU General Public License     *)
(* along with this program.  If not, see <http://www.gnu.org/licenses/>. *)
(*************************************************************************)

From mathcomp
Require Import ssreflect ssrbool eqtype ssrfun ssrnat choice seq.
From mathcomp
Require Import fintype tuple bigop path finset.


(*****************************************************************************)
(* This files definies a ordered and decidable relations on a                *)
(* type as canonical structure.  One need to import Order.Theory to get      *)
(* the theory of such relations. The scope order_scope (%ord) contains       *)
(* fancier notation for this kind of ordeeing.                               *)
(*                                                                           *)
(*           posetType == the type of partially ordered types                *)
(*           orderType == the type of totally ordered types                  *)
(*                                                                           *)
(* POsetType ord_mixin == builds an ordtype from a mixing containing         *)
(*                        proofs of reflexivity, antisymmetry & transitivity *)
(*                                                                           *)
(* We provide a canonical structure of orderType for natural numbers (nat)   *)
(* for finType and for pairs of ordType by lexicographic orderering.         *)
(*                                                                           *)
(* leP ltP ltgtP are the three main lemmas for case analysis, note that      *)
(* they are doing a bit more than the one for natural numbers.               *)
(*                                                                           *)
(* We also provide specialized version of some theorems from path.v.         *)
(*                                                                           *)
(* There are three distinct uses of the symbols <, <=, > and >=:             *)
(*    0-ary, unary (prefix) and binary (infix).                              *)
(* 0. <%O, <=%O, >%O, >=%O stand respectively for lt, le, gt and ge.         *)
(* 1. (< x),  (<= x), (> x),  (>= x) stand respectively for                  *)
(*    (gt x), (ge x), (lt x), (le x).                                        *)
(*    So (< x) is a predicate characterizing elements smaller than x.        *)
(* 2. (x < y), (x <= y), ... mean what they are expected to.                 *)
(*  These convention are compatible with haskell's,                          *)
(*   where ((< y) x) = (x < y) = ((<) x y),                                  *)
(*   except that we write <%R instead of (<).                                *)
(*****************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Delimit Scope order_scope with O.
Local Open Scope order_scope.

Reserved Notation "<= y" (at level 35).
Reserved Notation ">= y" (at level 35).
Reserved Notation "< y" (at level 35).
Reserved Notation "> y" (at level 35).
Reserved Notation "<= y :> T" (at level 35, y at next level).
Reserved Notation ">= y :> T" (at level 35, y at next level).
Reserved Notation "< y :> T" (at level 35, y at next level).
Reserved Notation "> y :> T" (at level 35, y at next level).
Reserved Notation "x >=< y" (at level 70, no associativity).
Reserved Notation ">=< x" (at level 35).
Reserved Notation ">=< y :> T" (at level 35, y at next level).
Reserved Notation "x >< y" (at level 70, no associativity).
Reserved Notation ">< x" (at level 35).
Reserved Notation ">< y :> T" (at level 35, y at next level).

(* Reserved notation for set-theretic operations. *)
Reserved Notation "A `&` B"  (at level 48, left associativity).
Reserved Notation "A `|` B" (at level 52, left associativity).
Reserved Notation "A `\` B" (at level 50, left associativity).
Reserved Notation "~` A" (at level 35, right associativity).

Reserved Notation "\meet_ i F"
  (at level 41, F at level 41, i at level 0,
           format "'[' \meet_ i '/  '  F ']'").
Reserved Notation "\meet_ ( i <- r | P ) F"
  (at level 41, F at level 41, i, r at level 50,
           format "'[' \meet_ ( i  <-  r  |  P ) '/  '  F ']'").
Reserved Notation "\meet_ ( i <- r ) F"
  (at level 41, F at level 41, i, r at level 50,
           format "'[' \meet_ ( i  <-  r ) '/  '  F ']'").
Reserved Notation "\meet_ ( m <= i < n | P ) F"
  (at level 41, F at level 41, i, m, n at level 50,
           format "'[' \meet_ ( m  <=  i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\meet_ ( m <= i < n ) F"
  (at level 41, F at level 41, i, m, n at level 50,
           format "'[' \meet_ ( m  <=  i  <  n ) '/  '  F ']'").
Reserved Notation "\meet_ ( i | P ) F"
  (at level 41, F at level 41, i at level 50,
           format "'[' \meet_ ( i  |  P ) '/  '  F ']'").
Reserved Notation "\meet_ ( i : t | P ) F"
  (at level 41, F at level 41, i at level 50,
           only parsing).
Reserved Notation "\meet_ ( i : t ) F"
  (at level 41, F at level 41, i at level 50,
           only parsing).
Reserved Notation "\meet_ ( i < n | P ) F"
  (at level 41, F at level 41, i, n at level 50,
           format "'[' \meet_ ( i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\meet_ ( i < n ) F"
  (at level 41, F at level 41, i, n at level 50,
           format "'[' \meet_ ( i  <  n )  F ']'").
Reserved Notation "\meet_ ( i 'in' A | P ) F"
  (at level 41, F at level 41, i, A at level 50,
           format "'[' \meet_ ( i  'in'  A  |  P ) '/  '  F ']'").
Reserved Notation "\meet_ ( i 'in' A ) F"
  (at level 41, F at level 41, i, A at level 50,
           format "'[' \meet_ ( i  'in'  A ) '/  '  F ']'").

Reserved Notation "\join_ i F"
  (at level 41, F at level 41, i at level 0,
           format "'[' \join_ i '/  '  F ']'").
Reserved Notation "\join_ ( i <- r | P ) F"
  (at level 41, F at level 41, i, r at level 50,
           format "'[' \join_ ( i  <-  r  |  P ) '/  '  F ']'").
Reserved Notation "\join_ ( i <- r ) F"
  (at level 41, F at level 41, i, r at level 50,
           format "'[' \join_ ( i  <-  r ) '/  '  F ']'").
Reserved Notation "\join_ ( m <= i < n | P ) F"
  (at level 41, F at level 41, i, m, n at level 50,
           format "'[' \join_ ( m  <=  i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\join_ ( m <= i < n ) F"
  (at level 41, F at level 41, i, m, n at level 50,
           format "'[' \join_ ( m  <=  i  <  n ) '/  '  F ']'").
Reserved Notation "\join_ ( i | P ) F"
  (at level 41, F at level 41, i at level 50,
           format "'[' \join_ ( i  |  P ) '/  '  F ']'").
Reserved Notation "\join_ ( i : t | P ) F"
  (at level 41, F at level 41, i at level 50,
           only parsing).
Reserved Notation "\join_ ( i : t ) F"
  (at level 41, F at level 41, i at level 50,
           only parsing).
Reserved Notation "\join_ ( i < n | P ) F"
  (at level 41, F at level 41, i, n at level 50,
           format "'[' \join_ ( i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\join_ ( i < n ) F"
  (at level 41, F at level 41, i, n at level 50,
           format "'[' \join_ ( i  <  n )  F ']'").
Reserved Notation "\join_ ( i 'in' A | P ) F"
  (at level 41, F at level 41, i, A at level 50,
           format "'[' \join_ ( i  'in'  A  |  P ) '/  '  F ']'").
Reserved Notation "\join_ ( i 'in' A ) F"
  (at level 41, F at level 41, i, A at level 50,
           format "'[' \join_ ( i  'in'  A ) '/  '  F ']'").

Module Order.
Module POrder.
Section ClassDef.
Structure mixin_of (T : eqType) := Mixin {
  le : rel T;
  lt : rel T;
  _  : forall x y, lt x y = (x != y) && (le x y);
  _  : reflexive     le;
  _  : antisymmetric le;
  _  : transitive    le
}.

Record class_of T := Class {
  base  : Equality.class_of T;
  mixin : mixin_of (EqType T base)
}.

Local Coercion base : class_of >-> Equality.class_of.

Structure type := Pack { sort; _ : class_of sort; _ : Type }.

Local Coercion sort : type >-> Sortclass.

Variables (T : Type) (cT : type).

Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack T c T.
Let xT := let: Pack T _ _ := cT in T.
Notation xclass := (class : class_of xT).

Definition pack :=
  fun b bT & phant_id (Equality.class bT) b =>
  fun m => Pack (@Class T b m) T.

Definition eqType := @Equality.Pack cT xclass xT.
End ClassDef.

Module Import Exports.
Coercion base   : class_of >-> Equality.class_of.
Coercion mixin  : class_of >-> mixin_of.
Coercion sort   : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.

Canonical eqType.

Notation porderType := type.
Notation porderMixin := mixin_of.
Notation POrderMixin := Mixin.
Notation POrderType T m := (@pack T _ _ id m).

Notation "[ 'porderType' 'of' T 'for' cT ]" := (@clone T cT _ id)
  (at level 0, format "[ 'porderType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'porderType' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'porderType'  'of'  T ]") : form_scope.
End Exports.
End POrder.

Import POrder.Exports.
Bind Scope cpo_sort with POrder.sort.

Module Import POrderDef.
Section Def.
Variable (T : porderType).

Definition le (R : porderType) : rel R := POrder.le (POrder.class R).
Local Notation "x <= y" := (le x y) : order_scope.

Definition lt (R : porderType) : rel R := POrder.lt (POrder.class R).
Local Notation "x < y" := (lt x y) : order_scope.

Definition comparable (R : porderType) : rel R :=
  fun (x y : R) => (x <= y) || (y <= x).
Local Notation "x >=< y" := (comparable x y) : order_scope.
Local Notation "x >< y" := (~~ (x >=< y)) : order_scope.

Definition ge : simpl_rel T := [rel x y | y <= x].
Definition gt : simpl_rel T := [rel x y | y < x].
Definition leif (x y : T) C : Prop := ((x <= y) * ((x == y) = C))%type.

Definition le_of_leif x y C (le_xy : @leif x y C) := le_xy.1 : le x y.

CoInductive le_xor_gt (x y : T) : bool -> bool -> Set :=
  | LerNotGt of x <= y : le_xor_gt x y true false
  | GtrNotLe of y < x  : le_xor_gt x y false true.

CoInductive lt_xor_ge (x y : T) : bool -> bool -> Set :=
  | LtrNotGe of x < y  : lt_xor_ge x y false true
  | GerNotLt of y <= x : lt_xor_ge x y true false.

CoInductive comparer (x y : T) :
  bool -> bool -> bool -> bool -> bool -> bool -> Set :=
  | ComparerEq of x = y : comparer x y
    true true true true false false
  | ComparerLt of x < y : comparer x y
    false false true false true false
  | ComparerGt of y < x : comparer x y
    false false false true false true.

CoInductive incomparer (x y : T) :
  bool -> bool -> bool -> bool -> bool -> bool -> bool -> bool -> Set :=
  | InComparerEq of x = y : incomparer x y
    true true true true false false true true
  | InComparerLt of x < y : incomparer x y
    false false true false true false true true
  | InComparerGt of y < x : incomparer x y
    false false false true false true true true
  | InComparer of x >< y : incomparer x y
    false false false false false false false false.

End Def.
End POrderDef.

Prenex Implicits lt le leif.

Module Import POSyntax.

Notation "<=%O" := le : order_scope.
Notation ">=%O" := ge : order_scope.
Notation "<%O" := lt : order_scope.
Notation ">%O" := gt : order_scope.
Notation "<?=%O" := leif : order_scope.
Notation ">=<%O" := comparable : order_scope.
Notation "><%O" := (fun x y => ~~ (comparable x y)) : order_scope.

Notation "<= y" := (ge y) : order_scope.
Notation "<= y :> T" := (<= (y : T)) : order_scope.
Notation ">= y"  := (le y) : order_scope.
Notation ">= y :> T" := (>= (y : T)) : order_scope.

Notation "< y" := (gt y) : order_scope.
Notation "< y :> T" := (< (y : T)) : order_scope.
Notation "> y" := (lt y) : order_scope.
Notation "> y :> T" := (> (y : T)) : order_scope.

Notation ">=< y" := (comparable y) : order_scope.
Notation ">=< y :> T" := (>=< (y : T)) : order_scope.

Notation "x <= y" := (le x y) : order_scope.
Notation "x <= y :> T" := ((x : T) <= (y : T)) : order_scope.
Notation "x >= y" := (y <= x) (only parsing) : order_scope.
Notation "x >= y :> T" := ((x : T) >= (y : T)) (only parsing) : order_scope.

Notation "x < y"  := (lt x y) : order_scope.
Notation "x < y :> T" := ((x : T) < (y : T)) : order_scope.
Notation "x > y"  := (y < x) (only parsing) : order_scope.
Notation "x > y :> T" := ((x : T) > (y : T)) (only parsing) : order_scope.

Notation "x <= y <= z" := ((x <= y) && (y <= z)) : order_scope.
Notation "x < y <= z" := ((x < y) && (y <= z)) : order_scope.
Notation "x <= y < z" := ((x <= y) && (y < z)) : order_scope.
Notation "x < y < z" := ((x < y) && (y < z)) : order_scope.

Notation "x <= y ?= 'iff' C" := (leif x y C) : order_scope.
Notation "x <= y ?= 'iff' C :> R" := ((x : R) <= (y : R) ?= iff C)
  (only parsing) : order_scope.

Notation ">=< x" := (comparable x) : order_scope.
Notation ">=< x :> T" := (>=< (x : T)) (only parsing) : order_scope.
Notation "x >=< y" := (comparable x y) : order_scope.

Notation ">< x" := (fun y => ~~ (comparable x y)) : order_scope.
Notation ">< x :> T" := (>< (x : T)) (only parsing) : order_scope.
Notation "x >< y" := (~~ (comparable x y)) : order_scope.

Coercion le_of_leif : leif >-> is_true.

End POSyntax.

Module Import POrderTheory.
Section POrderTheory.
Context {T : porderType}.

Implicit Types x y : T.

Lemma lexx (x : T) : x <= x.
Proof. by case: T x => ? [? []]. Qed.
Hint Resolve lexx.

Definition le_refl : reflexive le := lexx.
Hint Resolve le_refl.

Lemma le_anti: antisymmetric (<=%O : rel T).
Proof. by case: T => ? [? []]. Qed.

Lemma le_trans: transitive (<=%O : rel T).
Proof. by case: T => ? [? []]. Qed.

Lemma lt_neqAle x y: (x < y) = (x != y) && (x <= y).
Proof. by case: T x y => ? [? []]. Qed.

Lemma ltxx x: x < x = false.
Proof. by rewrite lt_neqAle eqxx. Qed.

Definition lt_irreflexive : irreflexive lt := ltxx.
Hint Resolve lt_irreflexive.

Lemma le_eqVlt x y: (x <= y) = (x == y) || (x < y).
Proof. by rewrite lt_neqAle; case: eqP => //= ->; rewrite lexx. Qed.

Lemma lt_eqF x y: x < y -> x == y = false.
Proof. by rewrite lt_neqAle => /andP [/negbTE->]. Qed.

Lemma gt_eqF x y : y < x -> x == y = false.
Proof. by apply: contraTF => /eqP ->; rewrite ltxx. Qed.

Lemma eq_le x y: (x == y) = (x <= y <= x).
Proof. by apply/eqP/idP => [->|/le_anti]; rewrite ?lexx. Qed.

Lemma ltW x y: x < y -> x <= y.
Proof. by rewrite le_eqVlt orbC => ->. Qed.

Lemma lt_le_trans y x z: x < y -> y <= z -> x < z.
Proof.
rewrite !lt_neqAle => /andP [nexy lexy leyz]; rewrite (le_trans lexy) // andbT.
by apply: contraNneq nexy => eqxz; rewrite eqxz eq_le leyz andbT in lexy *.
Qed.

Lemma lt_trans: transitive (<%O : rel T).
Proof. by move=> y x z le1 /ltW le2; apply/(@lt_le_trans y). Qed.

Lemma le_lt_trans y x z: x <= y -> y < z -> x < z.
Proof. by rewrite le_eqVlt => /orP [/eqP ->|/lt_trans t /t]. Qed.

Lemma lt_nsym x y : x < y -> y < x -> False.
Proof. by move=> xy /(lt_trans xy); rewrite ltxx. Qed.

Lemma le_gtF x y: x <= y -> y < x = false.
Proof.
by move=> le_xy; apply/negP => /lt_le_trans /(_ le_xy); rewrite ltxx.
Qed.

Lemma lt_geF x y : (x < y) -> y <= x = false.
Proof.
by move=> le_xy; apply/negP => /le_lt_trans /(_ le_xy); rewrite ltxx.
Qed.

Definition lt_gtF x y hxy := le_gtF (@ltW x y hxy).

Lemma lt_leAnge x y : (x < y) = (x <= y) && ~~ (y <= x).
Proof.
apply/idP/idP => [ltxy|/andP[lexy Nleyx]]; first by rewrite ltW // lt_geF.
by rewrite lt_neqAle lexy andbT; apply: contraNneq Nleyx => ->.
Qed.

Lemma lt_le_asym x y : x < y <= x = false.
Proof. by rewrite lt_neqAle -andbA -eq_le eq_sym; case: (_ == _). Qed.

Lemma le_lt_asym x y : x <= y < x = false.
Proof. by rewrite andbC lt_le_asym. Qed.

Lemma lt_sorted_uniq_le (s : seq T) :
   sorted lt s = uniq s && sorted le s.
Proof.
case: s => //= n s; elim: s n => //= m s IHs n.
rewrite inE lt_neqAle negb_or IHs -!andbA.
case sn: (n \in s); last do !bool_congr.
rewrite andbF; apply/and5P=> [[ne_nm lenm _ _ le_ms]]; case/negP: ne_nm.
by rewrite eq_le lenm /=; apply: (allP (order_path_min le_trans le_ms)).
Qed.

Lemma eq_sorted_lt (s1 s2 : seq T) :
  sorted lt s1 -> sorted lt s2 -> s1 =i s2 -> s1 = s2.
Proof. by apply: eq_sorted_irr => //; apply: lt_trans. Qed.

Lemma eq_sorted_le (s1 s2 : seq T) :
   sorted le s1 -> sorted le s2 -> perm_eq s1 s2 -> s1 = s2.
Proof. by apply: eq_sorted; [apply: le_trans|apply: le_anti]. Qed.

Lemma comparable_leNgt x y : x >=< y -> (x <= y) = ~~ (y < x).
Proof.
move=> c_xy; apply/idP/idP => [/le_gtF/negP/negP//|]; rewrite lt_neqAle.
by move: c_xy => /orP [] -> //; rewrite andbT negbK => /eqP ->.
Qed.

Lemma comparable_ltNge x y : x >=< y -> (x < y) = ~~ (y <= x).
Proof.
move=> c_xy; apply/idP/idP => [/lt_geF/negP/negP//|].
by rewrite lt_neqAle eq_le; move: c_xy => /orP [] -> //; rewrite andbT.
Qed.

Lemma comparable_ltgtP x y : x >=< y ->
  comparer x y (y == x) (x == y) (x <= y) (y <= x) (x < y) (x > y).
Proof.
rewrite />=<%O !le_eqVlt [y == x]eq_sym.
have := (altP (x =P y), (boolP (x < y), boolP (y < x))).
move=> [[->//|neq_xy /=] [[] xy [] //=]] ; do ?by rewrite ?ltxx; constructor.
  by rewrite ltxx in xy.
by rewrite le_gtF // ltW.
Qed.

Lemma comparable_leP x y : x >=< y -> le_xor_gt x y (x <= y) (y < x).
Proof.
by move=> /comparable_ltgtP [->|xy|xy]; constructor => //; rewrite ltW.
Qed.

Lemma comparable_ltP x y : x >=< y -> lt_xor_ge x y (y <= x) (x < y).
Proof.
by move=> /comparable_ltgtP [->|xy|xy]; constructor => //; rewrite ltW.
Qed.

Lemma comparable_sym x y : (y >=< x) = (x >=< y).
Proof. by rewrite /comparable orbC. Qed.

Lemma comparablexx x : x >=< x.
Proof. by rewrite /comparable lexx. Qed.

Lemma incomparable_eqF x y : (x >< y) -> (x == y) = false.
Proof. by apply: contraNF => /eqP ->; rewrite comparablexx. Qed.

Lemma incomparable_leF x y : (x >< y) -> (x <= y) = false.
Proof. by apply: contraNF; rewrite /comparable => ->. Qed.

Lemma incomparable_ltF x y : (x >< y) -> (x < y) = false.
Proof. by rewrite lt_neqAle => /incomparable_leF ->; rewrite andbF. Qed.

Lemma comparableP x y : incomparer x y
  (y == x) (x == y) (x <= y) (y <= x) (x < y) (x > y)
  (y >=< x) (x >=< y).
Proof.
rewrite ![y >=< _]comparable_sym; have [c_xy|i_xy] := boolP (x >=< y).
  by case: (comparable_ltgtP c_xy) => ?; constructor.
by rewrite ?incomparable_eqF ?incomparable_leF ?incomparable_ltF //
           1?comparable_sym //; constructor.
Qed.

Lemma le_comparable (x y : T) : x <= y -> x >=< y.
Proof. by case: comparableP. Qed.

Lemma lt_comparable (x y : T) : x < y -> x >=< y.
Proof. by case: comparableP. Qed.

Lemma ge_comparable (x y : T) : y <= x -> x >=< y.
Proof. by case: comparableP. Qed.

Lemma gt_comparable (x y : T) : y < x -> x >=< y.
Proof. by case: comparableP. Qed.

Lemma leifP x y C : reflect (x <= y ?= iff C) (if C then x == y else x < y).
Proof.
rewrite /leif le_eqVlt; apply: (iffP idP)=> [|[]].
  by case: C => [/eqP->|lxy]; rewrite ?eqxx // lxy lt_eqF.
by move=> /orP[/eqP->|lxy] <-; rewrite ?eqxx // lt_eqF.
Qed.

End POrderTheory.
End POrderTheory.

Hint Resolve lexx le_refl lt_irreflexive.

Definition reverse T : Type := T.
Local Notation "T ^r" := (reverse T) (at level 2, format "T ^r") : type_scope.

Module Import ReversePOrder.
Section ReversePOrder.
Canonical reverse_eqType (T : eqType) := EqType T [eqMixin of T^r].
Canonical reverse_choiceType (T : choiceType) := [choiceType of T^r].

Variable T : porderType.

Definition reverse_le (x y : T) := (y <= x).
Definition reverse_lt (x y : T) := (y < x).

Lemma reverse_lt_neqAle (x y : T) : reverse_lt x y = (x != y) && (reverse_le x y).
Proof. by rewrite eq_sym; apply: lt_neqAle. Qed.

Fact reverse_le_anti : antisymmetric reverse_le.
Proof. by move=> x y /andP [xy yx]; apply/le_anti/andP; split. Qed.

Definition reverse_porderMixin :=
  POrderMixin reverse_lt_neqAle (lexx : reflexive reverse_le) reverse_le_anti
             (fun y z x zy yx => @le_trans _ y x z yx zy).
Canonical reverse_porderType := POrderType (T^r) reverse_porderMixin.

End ReversePOrder.
End ReversePOrder.

Definition LePOrderMixin T le rle ale tle :=
   @POrderMixin T le _ (fun _ _ => erefl) rle ale tle.

Program Definition natPOrderMixin := @POrderMixin _ leq ltn _ leqnn anti_leq leq_trans.
Next Obligation. by rewrite ltn_neqAle. Qed.
Canonical  natPOrderType  := POrderType nat natPOrderMixin.

Lemma leEnat (n m : nat): (n <= m) = (n <= m)%N.
Proof. by []. Qed.

Lemma ltEnat (n m : nat): (n < m) = (n < m)%N.
Proof. by []. Qed.

Module SeqLexPOrder.
Section SeqLexPOrder.
Variable T : porderType.

Implicit Types s : seq T.

Fixpoint lexi s1 s2 :=
  if s1 is x1 :: s1' then
    if s2 is x2 :: s2' then
      (x1 < x2) || ((x1 == x2) && lexi s1' s2')
    else
      false
  else
    true.

Fact lexi_le_head x sx y sy:
  lexi (x :: sx) (y :: sy) -> x <= y.
Proof. by case/orP => [/ltW|/andP [/eqP-> _]]. Qed.

Fact lexi_refl: reflexive lexi.
Proof. by elim => [|x s ih] //=; rewrite eqxx ih orbT. Qed.

Fact lexi_anti: antisymmetric lexi.
Proof.
move=> x y /andP []; elim: x y => [|x sx ih] [|y sy] //=.
by case: comparableP => //= -> lesxsy /(ih _ lesxsy) ->.
Qed.

Fact lexi_trans: transitive lexi.
Proof.
elim=> [|y sy ih] [|x sx] [|z sz] //=.
case: (comparableP x y) => //=; case: (comparableP y z) => //=.
- by move=> -> -> lesxsy /(ih _ _ lesxsy) ->; rewrite eqxx orbT.
- by move=> ltyz ->; rewrite ltyz.
- by move=> -> ->.
- by move=> ltyz /lt_trans - /(_ _ ltyz) ->.
Qed.

Definition lexi_porderMixin := LePOrderMixin lexi_refl lexi_anti lexi_trans.
Canonical lexi_porderType := POrderType (seq T) lexi_porderMixin.

End SeqLexPOrder.
End SeqLexPOrder.

Canonical SeqLexPOrder.lexi_porderType.

Module Lattice.
  Section ClassDef.
    Structure mixin_of (T : porderType) := Mixin {
      meet : T -> T -> T;
      join : T -> T -> T;
      _ : commutative meet;
      _ : commutative join;
      _ : associative meet;
      _ : associative join;
      _ : forall y x, meet x (join x y) = x;
      _ : forall y x, join x (meet x y) = x;
      _ : forall x y, (x <= y) = (meet x y == x);
      _ : left_distributive meet join;
    }.

    Record class_of (T : Type) := Class {
      base  : POrder.class_of T;
      mixin : mixin_of (POrder.Pack base T)
    }.

    Local Coercion base : class_of >-> POrder.class_of.

    Structure type := Pack { sort; _ : class_of sort; _ : Type }.

    Local Coercion sort : type >-> Sortclass.

    Variables (T : Type) (cT : type).

    Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.
    Definition clone c of phant_id class c := @Pack T c T.
    Let xT := let: Pack T _ _ := cT in T.
    Notation xclass := (class : class_of xT).

    Definition pack b0 (m0 : mixin_of (@POrder.Pack T b0 T)) :=
      fun bT b & phant_id (POrder.class bT) b =>
        fun    m & phant_id m0 m => Pack (@Class T b m) T.

    Definition eqType := @Equality.Pack cT xclass xT.
    Definition porderType := @POrder.Pack cT xclass xT.
  End ClassDef.

  Module Import Exports.
    Coercion base      : class_of >-> POrder.class_of.
    Coercion mixin     : class_of >-> mixin_of.
    Coercion sort      : type >-> Sortclass.
    Coercion eqType    : type >-> Equality.type.
    Coercion porderType : type >-> POrder.type.

    Canonical eqType.
    Canonical porderType.

    Notation latticeType  := type.
    Notation latticeMixin := mixin_of.
    Notation LatticeMixin := Mixin.
    Notation LatticeType T m := (@pack T _ m _ _ id _ id).

    Notation "[ 'latticeType' 'of' T 'for' cT ]" := (@clone T cT _ id)
      (at level 0, format "[ 'latticeType'  'of'  T  'for'  cT ]") : form_scope.
    Notation "[ 'latticeType' 'of' T ]" := (@clone T _ _ id)
      (at level 0, format "[ 'latticeType'  'of'  T ]") : form_scope.
  End Exports.
End Lattice.

Export Lattice.Exports.

Module Import LatticeDef.
Definition meet {T : latticeType} : T -> T -> T := Lattice.meet (Lattice.class T).
Definition join {T : latticeType} : T -> T -> T := Lattice.join (Lattice.class T).
End LatticeDef.

Module Import LatticeSyntax.

Notation "x `&` y" :=  (meet x y).
Notation "x `|` y" := (join x y).

End LatticeSyntax.

Module Import ReverseLattice.
Section ReverseLattice.
Variable L : latticeType.
Implicit Types (x y : L).

Lemma meetC : commutative (@meet L). Proof. by case: L => [?[?[]]]. Qed.
Lemma joinC : commutative (@join L). Proof. by case: L => [?[?[]]]. Qed.

Lemma meetA : associative (@meet L). Proof. by case: L => [?[?[]]]. Qed.
Lemma joinA : associative (@join L). Proof. by case: L => [?[?[]]]. Qed.

Lemma joinKI y x : x `&` (x `|` y) = x. Proof. by case: L x y => [?[?[]]]. Qed.
Lemma meetKU y x : x `|` (x `&` y) = x. Proof. by case: L x y => [?[?[]]]. Qed.

Lemma joinKIC y x : x `&` (y `|` x) = x. Proof. by rewrite joinC joinKI. Qed.
Lemma meetKUC y x : x `|` (y `&` x) = x. Proof. by rewrite meetC meetKU. Qed.

Lemma meetUK x y : (x `&` y) `|` y = y.
Proof. by rewrite joinC meetC meetKU. Qed.
Lemma joinIK x y : (x `|` y) `&` y = y.
Proof. by rewrite joinC meetC joinKI. Qed.

Lemma meetUKC x y : (y `&` x) `|` y = y. Proof. by rewrite meetC meetUK. Qed.
Lemma joinIKC x y : (y `|` x) `&` y = y. Proof. by rewrite joinC joinIK. Qed.

Lemma leEmeet x y : (x <= y) = (x `&` y == x).
Proof. by case: L x y => [?[?[]]]. Qed.

Lemma leEjoin x y : (x <= y) = (x `|` y == y).
Proof. by rewrite leEmeet; apply/eqP/eqP => <-; rewrite (joinKI, meetUK). Qed.

Lemma meetUl : left_distributive (@meet L) (@join L).
Proof. by case: L => [?[?[]]]. Qed.

Lemma meetUr : right_distributive (@meet L) (@join L).
Proof. by move=> x y z; rewrite meetC meetUl ![_ `&` x]meetC. Qed.

Lemma joinIl : left_distributive (@join L) (@meet L).
Proof. by move=> x y z; rewrite meetUr joinIK meetUl -joinA meetUKC. Qed.

Fact reverse_leEmeet (x y : L^r) : (x <= y) = (x `|` y == x).
Proof. by rewrite [LHS]leEjoin joinC. Qed.

Definition reverse_latticeMixin :=
   @LatticeMixin [porderType of L^r] _ _ joinC meetC
  joinA meetA meetKU joinKI reverse_leEmeet joinIl.
Canonical reverse_latticeType := LatticeType L^r reverse_latticeMixin.
End ReverseLattice.
End ReverseLattice.

Module Import LatticeTheoryMeet.
Section LatticeTheoryMeet.
Context {L : latticeType}.
Implicit Types (x y : L).

(* lattice theory *)
Lemma meetAC : right_commutative (@meet L).
Proof. by move=> x y z; rewrite -!meetA [X in _ `&` X]meetC. Qed.
Lemma meetCA : left_commutative (@meet L).
Proof. by move=> x y z; rewrite !meetA [X in X `&` _]meetC. Qed.
Lemma meetACA : interchange (@meet L) (@meet L).
Proof. by move=> x y z t; rewrite !meetA [X in X `&` _]meetAC. Qed.

Lemma meetxx x : x `&` x = x.
Proof. by rewrite -[X in _ `&` X](meetKU x) joinKI. Qed.

Lemma meetKI y x : x `&` (x `&` y) = x `&` y.
Proof. by rewrite meetA meetxx. Qed.
Lemma meetIK y x : (x `&` y) `&` y = x `&` y.
Proof. by rewrite -meetA meetxx. Qed.
Lemma meetKIC y x : x `&` (y `&` x) = x `&` y.
Proof. by rewrite meetC meetIK meetC. Qed.
Lemma meetIKC y x : y `&` x `&` y = x `&` y.
Proof. by rewrite meetAC meetC meetxx. Qed.

(* interaction with order *)

Lemma meet_idPl {x y} : reflect (x `&` y = x) (x <= y).
Proof. by rewrite leEmeet; apply/eqP. Qed.
Lemma meet_idPr {x y} : reflect (y `&` x = x) (x <= y).
Proof. by rewrite meetC; apply/meet_idPl. Qed.

Lemma leIidl x y : (x <= x `&` y) = (x <= y).
Proof. by rewrite !leEmeet meetKI. Qed.
Lemma leIidr x y : (x <= y `&` x) = (x <= y).
Proof. by rewrite !leEmeet meetKIC. Qed.

Lemma lexI x y z : (x <= y `&` z) = (x <= y) && (x <= z).
Proof.
rewrite !leEmeet; apply/idP/idP => [/eqP<-|/andP[/eqP<- /eqP<-]].
  by rewrite meetA meetIK eqxx -meetA meetACA meetxx meetAC eqxx.
by rewrite -[X in X `&` _]meetA meetIK meetA.
Qed.

Lemma leIx x y z : (y <= x) || (z <= x) -> y `&` z <= x.
Proof.
rewrite !leEmeet => /orP [/eqP <-|/eqP <-].
  by rewrite -meetA meetACA meetxx meetAC.
by rewrite -meetA meetIK.
Qed.

Lemma leIr x y : y `&` x <= x.
Proof. by rewrite leIx ?lexx ?orbT. Qed.

Lemma leIl x y : x `&` y <= x.
Proof. by rewrite leIx ?lexx ?orbT. Qed.

Lemma leI2 x y z t : x <= z -> y <= t -> x `&` y <= z `&` t.
Proof. by move=> xz yt; rewrite lexI !leIx ?xz ?yt ?orbT //. Qed.

End LatticeTheoryMeet.
End LatticeTheoryMeet.

Module Import LatticeTheoryJoin.
Section LatticeTheoryJoin.
Variable (L : latticeType).
Implicit Types (x y z : L).

(* lattice theory *)
Lemma joinAC : right_commutative (@join L).
Proof. exact: (@meetAC [latticeType of L^r]). Qed.
Lemma joinCA : left_commutative (@join L).
Proof. exact: (@meetCA [latticeType of L^r]). Qed.
Lemma joinACA : interchange (@join L) (@join L).
Proof. exact: (@meetACA [latticeType of L^r]). Qed.

Lemma joinxx x : x `|` x = x.
Proof. exact: (@meetxx [latticeType of L^r]). Qed.

Lemma joinKU y x : x `|` (x `|` y) = x `|` y.
Proof. exact: (@meetKI [latticeType of L^r]). Qed.
Lemma joinUK y x : (x `|` y) `|` y = x `|` y.
Proof. exact: (@meetIK [latticeType of L^r]). Qed.
Lemma joinKUC y x : x `|` (y `|` x) = x `|` y.
Proof. exact: (@meetKIC [latticeType of L^r]). Qed.
Lemma joinUKC y x : y `|` x `|` y = x `|` y.
Proof. exact: (@meetIKC [latticeType of L^r]). Qed.

(* interaction with order *)
Lemma join_idPl {x y} : reflect (x `|` y = y) (x <= y).
Proof. exact: (@meet_idPr [latticeType of L^r]). Qed.
Lemma join_idPr {x y} : reflect (y `|` x = y) (x <= y).
Proof. exact: (@meet_idPl [latticeType of L^r]). Qed.

Lemma leUidl x y : (x `|` y <= y) = (x <= y).
Proof. exact: (@leIidr [latticeType of L^r]). Qed.
Lemma leUidr x y : (y `|` x <= y) = (x <= y).
Proof. exact: (@leIidl [latticeType of L^r]). Qed.

Lemma leUx x y z : (x `|` y <= z) = (x <= z) && (y <= z).
Proof. exact: (@lexI [latticeType of L^r]). Qed.

Lemma lexU x y z : (x <= y) || (x <= z) -> x <= y `|` z.
Proof. exact: (@leIx [latticeType of L^r]). Qed.

Lemma leUr x y : x <= y `|` x.
Proof. exact: (@leIr [latticeType of L^r]). Qed.

Lemma leUl x y : x <= x `|` y.
Proof. exact: (@leIl [latticeType of L^r]). Qed.

Lemma leU2 x y z t : x <= z -> y <= t -> x `|` y <= z `|` t.
Proof. exact: (@leI2 [latticeType of L^r]). Qed.

(* Distributive lattice theory *)
Lemma joinIr : right_distributive (@join L) (@meet L).
Proof. exact: (@meetUr [latticeType of L^r]). Qed.

End LatticeTheoryJoin.
End LatticeTheoryJoin.

Module Total.
  Section ClassDef.
    Structure mixin_of (T : porderType) := Mixin {
      _ : total (<=%O : rel T)
    }.

    Record class_of (T : Type) := Class {
      base  : Lattice.class_of T;
      mixin : mixin_of (POrder.Pack base T)
    }.

    Local Coercion base : class_of >-> Lattice.class_of.

    Structure type := Pack { sort; _ : class_of sort; _ : Type }.

    Local Coercion sort : type >-> Sortclass.

    Variables (T : Type) (cT : type).

    Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.
    Definition clone c of phant_id class c := @Pack T c T.
    Let xT := let: Pack T _ _ := cT in T.
    Notation xclass := (class : class_of xT).

    Definition pack b0 (m0 : mixin_of (@Lattice.Pack T b0 T)) :=
      fun bT b & phant_id (Lattice.class bT) b =>
        fun    m & phant_id m0 m => Pack (@Class T b m) T.

    Definition eqType := @Equality.Pack cT xclass xT.
    Definition porderType := @POrder.Pack cT xclass xT.
    Definition latticeType := @Lattice.Pack cT xclass xT.
  End ClassDef.

  Module Import Exports.
    Coercion base      : class_of >-> Lattice.class_of.
    Coercion mixin     : class_of >-> mixin_of.
    Coercion sort      : type >-> Sortclass.
    Coercion eqType    : type >-> Equality.type.
    Coercion porderType : type >-> POrder.type.
    Coercion latticeType : type >-> Lattice.type.

    Canonical eqType.
    Canonical porderType.
    Canonical latticeType.

    Notation orderType  := type.
    Notation orderMixin := mixin_of.
    Notation OrderMixin := Mixin.
    Notation OrderType T m := (@pack T _ m _ _ id _ id).
  End Exports.
End Total.

Import Total.Exports.

Module TotalLattice.
Section TotalLattice.
Variable (T : porderType).
Implicit Types (x y z : T).
Hypothesis le_total : total (<=%O : rel T).

Fact comparableT x y : x >=< y. Proof. exact: le_total. Qed.
Hint Resolve comparableT.

Fact ltgtP x y :
  comparer x y (y == x) (x == y) (x <= y) (y <= x) (x < y) (x > y).
Proof. exact: comparable_ltgtP. Qed.

Fact leP x y : le_xor_gt x y (x <= y) (y < x).
Proof. exact: comparable_leP. Qed.

Fact ltP x y : lt_xor_ge x y (y <= x) (x < y).
Proof. exact: comparable_ltP. Qed.

Definition meet x y := if x <= y then x else y.
Definition join x y := if y <= x then x else y.

Fact meetC : commutative meet.
Proof. by move=> x y; rewrite /meet; have [] := ltgtP. Qed.

Fact joinC : commutative join.
Proof. by move=> x y; rewrite /join; have [] := ltgtP. Qed.

Fact meetA : associative meet.
Proof.
move=> x y z; rewrite /meet; case: (leP y z) => yz; case: (leP x y) => xy //=.
- by rewrite (le_trans xy).
- by rewrite yz.
by rewrite !lt_geF // (lt_trans yz).
Qed.

Fact joinA : associative join.
Proof.
move=> x y z; rewrite /join; case: (leP z y) => yz; case: (leP y x) => xy //=.
- by rewrite (le_trans yz).
- by rewrite yz.
by rewrite !lt_geF // (lt_trans xy).
Qed.

Fact joinKI y x : meet x (join x y) = x.
Proof. by rewrite /meet /join; case: (leP y x) => yx; rewrite ?lexx ?ltW. Qed.

Fact meetKU y x : join x (meet x y) = x.
Proof. by rewrite /meet /join; case: (leP x y) => yx; rewrite ?lexx ?ltW. Qed.

Fact leEmeet x y : (x <= y) = (meet x y == x).
Proof. by rewrite /meet; case: leP => ?; rewrite ?eqxx ?lt_eqF. Qed.

Fact meetUl : left_distributive meet join.
Proof.
move=> x y z; rewrite /meet /join.
case: (leP y z) => yz; case: (leP y x) => xy //=; first 1 last.
- by rewrite yz [x <= z](le_trans _ yz) ?[x <= y]ltW // lt_geF.
- by rewrite lt_geF ?lexx // (lt_le_trans yz).
- by rewrite lt_geF //; have [->|/lt_geF->|] := (ltgtP x z); rewrite ?lexx.
- by have [] := (leP x z); rewrite ?xy ?yz.
Qed.

Definition Mixin := LatticeMixin meetC joinC meetA joinA joinKI meetKU leEmeet meetUl.

End TotalLattice.
End TotalLattice.

Module TotalTheory.
Section TotalTheory.
Variable (T : orderType).

Implicit Types (x y : T).

Lemma le_total : total (<=%O : rel T). Proof. by case: T => [? [? []]]. Qed.
Hint Resolve le_total.

Lemma comparableT x y : x >=< y. Proof. exact: le_total. Qed.
Hint Resolve comparableT.

Lemma sort_le_sorted (s : seq T) : sorted <=%O (sort <=%O s).
Proof. exact: sort_sorted. Qed.

Lemma sort_lt_sorted (s : seq T) : sorted lt (sort le s) = uniq s.
Proof. by rewrite lt_sorted_uniq_le sort_uniq sort_le_sorted andbT. Qed.

Lemma sort_le_id (s : seq T) : sorted le s -> sort le s = s.
Proof.
by move=> ss; apply: eq_sorted_le; rewrite ?sort_le_sorted // perm_sort.
Qed.

Lemma leNgt x y : (x <= y) = ~~ (y < x).
Proof. by rewrite comparable_leNgt. Qed.

Lemma ltNge x y : (x < y) = ~~ (y <= x).
Proof. by rewrite comparable_ltNge. Qed.

Definition ltgtP := TotalLattice.ltgtP le_total.
Definition leP := TotalLattice.leP le_total.
Definition ltP := TotalLattice.ltP le_total.

End TotalTheory.
End TotalTheory.

Module BLattice.
  Section ClassDef.
    Structure mixin_of (T : porderType) := Mixin {
      bottom : T;
      _ : forall x, bottom <= x;
    }.

    Record class_of (T : Type) := Class {
      base  : Lattice.class_of T;
      mixin : mixin_of (POrder.Pack base T)
    }.

    Local Coercion base : class_of >-> Lattice.class_of.

    Structure type := Pack { sort; _ : class_of sort; _ : Type }.

    Local Coercion sort : type >-> Sortclass.

    Variables (T : Type) (cT : type).

    Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.
    Definition clone c of phant_id class c := @Pack T c T.
    Let xT := let: Pack T _ _ := cT in T.
    Notation xclass := (class : class_of xT).

    Definition pack b0 (m0 : mixin_of (@Lattice.Pack T b0 T)) :=
      fun bT b & phant_id (Lattice.class bT) b =>
        fun    m & phant_id m0 m => Pack (@Class T b m) T.

    Definition eqType := @Equality.Pack cT xclass xT.
    Definition porderType := @POrder.Pack cT xclass xT.
    Definition latticeType := @Lattice.Pack cT xclass xT.
  End ClassDef.

  Module Import Exports.
    Coercion base      : class_of >-> Lattice.class_of.
    Coercion mixin     : class_of >-> mixin_of.
    Coercion sort      : type >-> Sortclass.
    Coercion eqType    : type >-> Equality.type.
    Coercion porderType : type >-> POrder.type.
    Coercion latticeType : type >-> Lattice.type.

    Canonical eqType.
    Canonical porderType.
    Canonical latticeType.

    Notation blatticeType  := type.
    Notation blatticeMixin := mixin_of.
    Notation BLatticeMixin := Mixin.
    Notation BLatticeType T m := (@pack T _ m _ _ id _ id).

    Notation "[ 'blatticeType' 'of' T 'for' cT ]" := (@clone T cT _ id)
      (at level 0, format "[ 'blatticeType'  'of'  T  'for'  cT ]") : form_scope.
    Notation "[ 'blatticeType' 'of' T ]" := (@clone T _ _ id)
      (at level 0, format "[ 'blatticeType'  'of'  T ]") : form_scope.
  End Exports.
End BLattice.

Export BLattice.Exports.

Module Import BLatticeDef.
Definition bottom (T : blatticeType) : T := BLattice.bottom (BLattice.class T).
End BLatticeDef.

Module Import BLatticeSyntax.

Notation "0" := (@bottom _) : order_scope.

Notation "\join_ ( i <- r | P ) F" :=
  (\big[@join _/0%O]_(i <- r | P%B) F%N) : order_scope.
Notation "\join_ ( i <- r ) F" :=
  (\big[@join _/0%O]_(i <- r) F%N) : order_scope.
Notation "\join_ ( i | P ) F" :=
  (\big[@join _/0%O]_(i | P%B) F%N) : order_scope.
Notation "\join_ i F" :=
  (\big[@join _/0%O]_i F%N) : order_scope.
Notation "\join_ ( i : I | P ) F" :=
  (\big[@join _/0%O]_(i : I | P%B) F%N) (only parsing) : order_scope.
Notation "\join_ ( i : I ) F" :=
  (\big[@join _/0%O]_(i : I) F%N) (only parsing) : order_scope.
Notation "\join_ ( m <= i < n | P ) F" :=
 (\big[@join _/0%O]_(m <= i < n | P%B) F%N) : order_scope.
Notation "\join_ ( m <= i < n ) F" :=
 (\big[@join _/0%O]_(m <= i < n) F%N) : order_scope.
Notation "\join_ ( i < n | P ) F" :=
 (\big[@join _/0%O]_(i < n | P%B) F%N) : order_scope.
Notation "\join_ ( i < n ) F" :=
 (\big[@join _/0%O]_(i < n) F%N) : order_scope.
Notation "\join_ ( i 'in' A | P ) F" :=
 (\big[@join _/0%O]_(i in A | P%B) F%N) : order_scope.
Notation "\join_ ( i 'in' A ) F" :=
 (\big[@join _/0%O]_(i in A) F%N) : order_scope.

End BLatticeSyntax.

Module Import BLatticeTheory.
Section BLatticeTheory.
Variable (L : blatticeType).
Implicit Types (x y z : L).

(* Distributive lattice theory with 0 & 1*)
Lemma le0x x : 0 <= x. Proof. by case: L x => [?[?[]]]. Qed.
Hint Resolve le0x.

Lemma lex0 x : (x <= 0) = (x == 0).
Proof. by rewrite le_eqVlt (le_gtF (le0x _)) orbF. Qed.

Lemma ltx0 x : (x < 0) = false.
Proof. by rewrite lt_neqAle lex0 andNb. Qed.

Lemma lt0x x : (0 < x) = (x != 0).
Proof. by rewrite lt_neqAle le0x andbT eq_sym. Qed.

Lemma meet0x : left_zero 0 (@meet L).
Proof. by move=> x; apply/eqP; rewrite -leEmeet. Qed.

Lemma meetx0 : right_zero 0 (@meet L).
Proof. by move=> x; rewrite meetC meet0x. Qed.

Lemma join0x : left_id 0 (@join L).
Proof. by move=> x; apply/eqP; rewrite -leEjoin. Qed.

Lemma joinx0 : right_id 0 (@join L).
Proof. by move=> x; rewrite joinC join0x. Qed.

Lemma leU2l_le y t x z : x `&` t = 0 -> x `|` y <= z `|` t -> x <= z.
Proof.
by move=> xIt0 /(leI2 (lexx x)); rewrite joinKI meetUr xIt0 joinx0 leIidl.
Qed.

Lemma leU2r_le y t x z : x `&` t = 0 -> y `|` x <= t `|` z -> x <= z.
Proof. by rewrite joinC [_ `|` z]joinC => /leU2l_le H /H. Qed.

Lemma lexUl z x y : x `&` z = 0 -> (x <= y `|` z) = (x <= y).
Proof.
move=> xz0; apply/idP/idP=> xy; last by rewrite lexU ?xy.
by apply: (@leU2l_le x z); rewrite ?joinxx.
Qed.

Lemma lexUr z x y : x `&` z = 0 -> (x <= z `|` y) = (x <= y).
Proof. by move=> xz0; rewrite joinC; rewrite lexUl. Qed.

Lemma leU2E x y z t : x `&` t = 0 -> y `&` z = 0 ->
  (x `|` y <= z `|` t) = (x <= z) && (y <= t).
Proof.
move=> dxt dyz; apply/idP/andP; last by case=> ??; exact: leU2.
by move=> lexyzt; rewrite (leU2l_le _ lexyzt) // (leU2r_le _ lexyzt).
Qed.

Lemma join_eq0 x y : (x `|` y == 0) = (x == 0) && (y == 0).
Proof.
apply/idP/idP; last by move=> /andP [/eqP-> /eqP->]; rewrite joinx0.
by move=> /eqP xUy0; rewrite -!lex0 -!xUy0 ?leUl ?leUr.
Qed.

CoInductive eq0_xor_gt0 x : bool -> bool -> Set :=
    Eq0NotPOs : x = 0 -> eq0_xor_gt0 x true false
  | POsNotEq0 : 0 < x -> eq0_xor_gt0 x false true.

Lemma posxP x : eq0_xor_gt0 x (x == 0) (0 < x).
Proof. by rewrite lt0x; have [] := altP eqP; constructor; rewrite ?lt0x. Qed.

Canonical join_monoid := Monoid.Law (@joinA _) join0x joinx0.
Canonical join_comoid := Monoid.ComLaw (@joinC _).

Lemma join_sup (I : finType) (j : I) (P : pred I) (F : I -> L) :
   P j -> F j <= \join_(i | P i) F i.
Proof. by move=> Pj; rewrite (bigD1 j) //= lexU ?lexx. Qed.

Lemma join_min (I : finType) (j : I) (l : L) (P : pred I) (F : I -> L) :
   P j -> l <= F j -> l <= \join_(i | P i) F i.
Proof. by move=> Pj /le_trans -> //; rewrite join_sup. Qed.

Lemma joinsP (I : finType) (u : L) (P : pred I) (F : I -> L) :
   reflect (forall i : I, P i -> F i <= u) (\join_(i | P i) F i <= u).
Proof.
have -> : \join_(i | P i) F i <= u = (\big[andb/true]_(i | P i) (F i <= u)).
  by elim/big_rec2: _ => [|i y b Pi <-]; rewrite ?le0x ?leUx.
rewrite big_all_cond; apply: (iffP allP) => /= H i;
have := H i _; rewrite mem_index_enum; last by move/implyP->.
by move=> /(_ isT) /implyP.
Qed.

Lemma le_joins (I : finType) (A B : {set I}) (F : I -> L) :
   A \subset B -> \join_(i in A) F i <= \join_(i in B) F i.
Proof.
move=> AsubB; rewrite -(setID B A).
rewrite [X in _ <= X](eq_bigl [predU B :&: A & B :\: A]); last first.
  by move=> i; rewrite !inE.
rewrite bigU //=; last by rewrite -setI_eq0 setDE setIACA setICr setI0.
by rewrite lexU // (setIidPr _) // lexx.
Qed.

Lemma joins_setU (I : finType) (A B : {set I}) (F : I -> L) :
   \join_(i in (A :|: B)) F i = \join_(i in A) F i `|` \join_(i in B) F i.
Proof.
apply/eqP; rewrite eq_le leUx !le_joins ?subsetUl ?subsetUr ?andbT //.
apply/joinsP => i; rewrite inE; move=> /orP.
by case=> ?; rewrite lexU //; [rewrite join_sup|rewrite orbC join_sup].
Qed.

Lemma join_seq (I : finType) (r : seq I) (F : I -> L) :
   \join_(i <- r) F i = \join_(i in r) F i.
Proof.
rewrite [RHS](eq_bigl (mem [set i | i \in r])); last by move=> i; rewrite !inE.
elim: r => [|i r ihr]; first by rewrite big_nil big1 // => i; rewrite ?inE.
rewrite big_cons {}ihr; apply/eqP; rewrite eq_le set_cons.
rewrite leUx join_sup ?inE ?eqxx // le_joins //= ?subsetUr //.
apply/joinsP => j; rewrite !inE => /predU1P [->|jr]; rewrite ?lexU ?lexx //.
by rewrite join_sup ?orbT ?inE.
Qed.

Lemma joins_disjoint (I : finType) (d : L) (P : pred I) (F : I -> L) :
   (forall i : I, P i -> d `&` F i = 0) -> d `&` \join_(i | P i) F i = 0.
Proof.
move=> d_Fi_disj; have : \big[andb/true]_(i | P i) (d `&` F i == 0).
  rewrite big_all_cond; apply/allP => i _ /=.
  by apply/implyP => /d_Fi_disj ->.
elim/big_rec2: _ => [|i y]; first by rewrite meetx0.
case; rewrite (andbF, andbT) // => Pi /(_ isT) dy /eqP dFi.
by rewrite meetUr dy dFi joinxx.
Qed.

End BLatticeTheory.
End BLatticeTheory.

Module TBLattice.
  Section ClassDef.
    Structure mixin_of (T : porderType) := Mixin {
      top : T;
      _ : forall x, x <= top;
    }.

    Record class_of (T : Type) := Class {
      base  : BLattice.class_of T;
      mixin : mixin_of (POrder.Pack base T)
    }.

    Local Coercion base : class_of >-> BLattice.class_of.

    Structure type := Pack { sort; _ : class_of sort; _ : Type }.

    Local Coercion sort : type >-> Sortclass.

    Variables (T : Type) (cT : type).

    Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.
    Definition clone c of phant_id class c := @Pack T c T.
    Let xT := let: Pack T _ _ := cT in T.
    Notation xclass := (class : class_of xT).

    Definition pack b0 (m0 : mixin_of (@BLattice.Pack T b0 T)) :=
      fun bT b & phant_id (BLattice.class bT) b =>
        fun    m & phant_id m0 m => Pack (@Class T b m) T.

    Definition eqType := @Equality.Pack cT xclass xT.
    Definition porderType := @POrder.Pack cT xclass xT.
    Definition latticeType := @Lattice.Pack cT xclass xT.
    Definition blatticeType := @BLattice.Pack cT xclass xT.
  End ClassDef.

  Module Import Exports.
    Coercion base      : class_of >-> BLattice.class_of.
    Coercion mixin     : class_of >-> mixin_of.
    Coercion sort      : type >-> Sortclass.
    Coercion eqType    : type >-> Equality.type.
    Coercion porderType : type >-> POrder.type.
    Coercion latticeType : type >-> Lattice.type.
    Coercion blatticeType : type >-> BLattice.type.

    Canonical eqType.
    Canonical porderType.
    Canonical latticeType.
    Canonical blatticeType.

    Notation tblatticeType  := type.
    Notation tblatticeMixin := mixin_of.
    Notation TBLatticeMixin := Mixin.
    Notation TBLatticeType T m := (@pack T _ m _ _ id _ id).

    Notation "[ 'tblatticeType' 'of' T 'for' cT ]" := (@clone T cT _ id)
      (at level 0, format "[ 'tblatticeType'  'of'  T  'for'  cT ]") : form_scope.
    Notation "[ 'tblatticeType' 'of' T ]" := (@clone T _ _ id)
      (at level 0, format "[ 'tblatticeType'  'of'  T ]") : form_scope.

  End Exports.
End TBLattice.

Export TBLattice.Exports.

Module Import TBLatticeDef.
Definition top (T : tblatticeType) : T := TBLattice.top (TBLattice.class T).
End TBLatticeDef.

Module Import TBLatticeSyntax.

Notation "1" := (@top _) : order_scope.

Notation "\meet_ ( i <- r | P ) F" :=
  (\big[@meet _/1%O]_(i <- r | P%B) F%N) : order_scope.
Notation "\meet_ ( i <- r ) F" :=
  (\big[@meet _/1%O]_(i <- r) F%N) : order_scope.
Notation "\meet_ ( i | P ) F" :=
  (\big[@meet _/1%O]_(i | P%B) F%N) : order_scope.
Notation "\meet_ i F" :=
  (\big[@meet _/1%O]_i F%N) : order_scope.
Notation "\meet_ ( i : I | P ) F" :=
  (\big[@meet _/1%O]_(i : I | P%B) F%N) (only parsing) : order_scope.
Notation "\meet_ ( i : I ) F" :=
  (\big[@meet _/1%O]_(i : I) F%N) (only parsing) : order_scope.
Notation "\meet_ ( m <= i < n | P ) F" :=
 (\big[@meet _/1%O]_(m <= i < n | P%B) F%N) : order_scope.
Notation "\meet_ ( m <= i < n ) F" :=
 (\big[@meet _/1%O]_(m <= i < n) F%N) : order_scope.
Notation "\meet_ ( i < n | P ) F" :=
 (\big[@meet _/1%O]_(i < n | P%B) F%N) : order_scope.
Notation "\meet_ ( i < n ) F" :=
 (\big[@meet _/1%O]_(i < n) F%N) : order_scope.
Notation "\meet_ ( i 'in' A | P ) F" :=
 (\big[@meet _/1%O]_(i in A | P%B) F%N) : order_scope.
Notation "\meet_ ( i 'in' A ) F" :=
 (\big[@meet _/1%O]_(i in A) F%N) : order_scope.

End TBLatticeSyntax.

Module Import ReverseTBLattice.
Section ReverseTBLattice.
Variable L : tblatticeType.

Lemma lex1 (x : L) : x <= 1. Proof. by case: L x => [?[?[]]]. Qed.

Definition reverse_blatticeMixin :=
  @BLatticeMixin [latticeType of L^r] 1 lex1.
Canonical reverse_blatticeType := BLatticeType L^r reverse_blatticeMixin.

Definition reverse_tblatticeMixin :=
   @TBLatticeMixin [latticeType of L^r] (0 : L) (@le0x L).
Canonical reverse_tblatticeType := TBLatticeType L^r reverse_tblatticeMixin.

End ReverseTBLattice.
End ReverseTBLattice.

Module Import TBLatticeTheory.
Section TBLatticeTheory.
Variable (L : tblatticeType).
Implicit Types (x y : L).

Hint Resolve le0x lex1.

Lemma meetx1 : right_id 1 (@meet L).
Proof. exact: (@joinx0 [tblatticeType of L^r]). Qed.

Lemma meet1x : left_id 1 (@meet L).
Proof. exact: (@join0x [tblatticeType of L^r]). Qed.

Lemma joinx1 : right_zero 1 (@join L).
Proof. exact: (@meetx0 [tblatticeType of L^r]). Qed.

Lemma join1x : left_zero 1 (@join L).
Proof. exact: (@meet0x [tblatticeType of L^r]). Qed.

Lemma le1x x : (1 <= x) = (x == 1).
Proof. exact: (@lex0 [tblatticeType of L^r]). Qed.

Lemma leI2l_le y t x z : y `|` z = 1 -> x `&` y <= z `&` t -> x <= z.
Proof. rewrite joinC; exact: (@leU2l_le [tblatticeType of L^r]). Qed.

Lemma leI2r_le y t x z : y `|` z = 1 -> y `&` x <= t `&` z -> x <= z.
Proof. rewrite joinC; exact: (@leU2r_le [tblatticeType of L^r]). Qed.

Lemma lexIl z x y : z `|` y = 1 -> (x `&` z <= y) = (x <= y).
Proof. rewrite joinC; exact: (@lexUl [tblatticeType of L^r]). Qed.

Lemma lexIr z x y : z `|` y = 1 -> (z `&` x <= y) = (x <= y).
Proof. rewrite joinC; exact: (@lexUr [tblatticeType of L^r]). Qed.

Lemma leI2E x y z t : x `|` t = 1 -> y `|` z = 1 ->
  (x `&` y <= z `&` t) = (x <= z) && (y <= t).
Proof.
by move=> ? ?; apply: (@leU2E [tblatticeType of L^r]); rewrite meetC.
Qed.

Lemma meet_eq1 x y : (x `&` y == 1) = (x == 1) && (y == 1).
Proof. exact: (@join_eq0 [tblatticeType of L^r]). Qed.

Canonical meet_monoid := Monoid.Law (@meetA _) meet1x meetx1.
Canonical meet_comoid := Monoid.ComLaw (@meetC _).

Canonical meet_muloid := Monoid.MulLaw (@meet0x L) (@meetx0 _).
Canonical join_muloid := Monoid.MulLaw join1x joinx1.
Canonical join_addoid := Monoid.AddLaw (@meetUl L) (@meetUr _).
Canonical meet_addoid := Monoid.AddLaw (@joinIl L) (@joinIr _).

Lemma meets_inf (I : finType) (j : I) (P : pred I) (F : I -> L) :
   P j -> \meet_(i | P i) F i <= F j.
Proof. exact: (@join_sup [tblatticeType of L^r]). Qed.

Lemma meets_max (I : finType) (j : I) (u : L) (P : pred I) (F : I -> L) :
   P j -> F j <= u -> \meet_(i | P i) F i <= u.
Proof. exact: (@join_min [tblatticeType of L^r]). Qed.

Lemma meetsP (I : finType) (l : L) (P : pred I) (F : I -> L) :
   reflect (forall i : I, P i -> l <= F i) (l <= \meet_(i | P i) F i).
Proof. exact: (@joinsP [tblatticeType of L^r]). Qed.

Lemma le_meets (I : finType) (A B : {set I}) (F : I -> L) :
   A \subset B -> \meet_(i in B) F i <= \meet_(i in A) F i.
Proof. exact: (@le_joins [tblatticeType of L^r]). Qed.

Lemma meets_setU (I : finType) (A B : {set I}) (F : I -> L) :
   \meet_(i in (A :|: B)) F i = \meet_(i in A) F i `&` \meet_(i in B) F i.
Proof. exact: (@joins_setU [tblatticeType of L^r]). Qed.

Lemma meet_seq (I : finType) (r : seq I) (F : I -> L) :
   \meet_(i <- r) F i = \meet_(i in r) F i.
Proof. exact: (@join_seq [tblatticeType of L^r]). Qed.

Lemma meets_total (I : finType) (d : L) (P : pred I) (F : I -> L) :
   (forall i : I, P i -> d `|` F i = 1) -> d `|` \meet_(i | P i) F i = 1.
Proof. exact: (@joins_disjoint [tblatticeType of L^r]). Qed.

End TBLatticeTheory.
End TBLatticeTheory.

Module CBLattice.
  Section ClassDef.
    Structure mixin_of (T : blatticeType) := Mixin {
      sub : T -> T -> T;
      _ : forall x y, y `&` sub x y = 0;
      _ : forall x y, (x `&` y) `|` sub x y = x
    }.

    Record class_of (T : Type) := Class {
      base  : BLattice.class_of T;
      mixin : mixin_of (BLattice.Pack base T)
    }.

    Local Coercion base : class_of >-> BLattice.class_of.

    Structure type := Pack { sort; _ : class_of sort; _ : Type }.

    Local Coercion sort : type >-> Sortclass.

    Variables (T : Type) (cT : type).

    Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.
    Definition clone c of phant_id class c := @Pack T c T.
    Let xT := let: Pack T _ _ := cT in T.
    Notation xclass := (class : class_of xT).

    Definition pack b0 (m0 : mixin_of (@BLattice.Pack T b0 T)) :=
      fun bT b & phant_id (BLattice.class bT) b =>
        fun    m & phant_id m0 m => Pack (@Class T b m) T.

    Definition eqType := @Equality.Pack cT xclass xT.
    Definition porderType := @POrder.Pack cT xclass xT.
    Definition latticeType := @Lattice.Pack cT xclass xT.
    Definition blatticeType := @BLattice.Pack cT xclass xT.
  End ClassDef.

  Module Import Exports.
    Coercion base      : class_of >-> BLattice.class_of.
    Coercion mixin     : class_of >-> mixin_of.
    Coercion sort      : type >-> Sortclass.
    Coercion eqType    : type >-> Equality.type.
    Coercion porderType : type >-> POrder.type.
    Coercion latticeType : type >-> Lattice.type.
    Coercion blatticeType : type >-> BLattice.type.

    Canonical eqType.
    Canonical porderType.
    Canonical latticeType.
    Canonical blatticeType.

    Notation cblatticeType  := type.
    Notation cblatticeMixin := mixin_of.
    Notation CBLatticeMixin := Mixin.
    Notation CBLatticeType T m := (@pack T _ m _ _ id _ id).

    Notation "[ 'cblatticeType' 'of' T 'for' cT ]" := (@clone T cT _ id)
      (at level 0, format "[ 'cblatticeType'  'of'  T  'for'  cT ]") : form_scope.
    Notation "[ 'cblatticeType' 'of' T ]" := (@clone T _ _ id)
      (at level 0, format "[ 'cblatticeType'  'of'  T ]") : form_scope.

  End Exports.
End CBLattice.

Export CBLattice.Exports.

Module Import CBLatticeDef.
Definition sub {T : cblatticeType} : T -> T -> T := CBLattice.sub (CBLattice.class T).
End CBLatticeDef.

Module Import CBLatticeSyntax.
Notation "x `\` y" := (sub x y).
End CBLatticeSyntax.

Module Import CBLatticeTheory.
Section CBLatticeTheory.
Variable (L : cblatticeType).
Implicit Types (x y z : L).

Lemma subKI x y : y `&` (x `\` y) = 0.
Proof. by case: L x y => ? [? []]. Qed.

Lemma subIK x y : (x `\` y) `&` y = 0.
Proof. by rewrite meetC subKI. Qed.

Lemma meetIB z x y : (z `&` y) `&` (x `\` y) = 0.
Proof. by rewrite -meetA subKI meetx0. Qed.

Lemma meetBI z x y : (x `\` y) `&` (z `&` y) = 0.
Proof. by rewrite meetC meetIB. Qed.

Lemma joinIB y x : (x `&` y) `|` (x `\` y) = x.
Proof. by case: L x y => ? [? []]. Qed.

Lemma joinBI y x : (x `\` y) `|` (x `&` y) = x.
Proof. by rewrite joinC joinIB. Qed.

Lemma joinIBC y x : (y `&` x) `|` (x `\` y) = x.
Proof. by rewrite meetC joinIB. Qed.

Lemma joinBIC y x : (x `\` y) `|` (y `&` x) = x.
Proof. by rewrite meetC joinBI. Qed.

Lemma leBx x y : x `\` y <= x.
Proof. by rewrite -{2}[x](joinIB y) lexU // lexx orbT. Qed.
Hint Resolve leBx.

Lemma subxx x : x `\` x = 0.
Proof. by have := subKI x x; rewrite (meet_idPr _). Qed.

Lemma leBl z x y : x <= y -> x `\` z <= y `\` z.
Proof.
rewrite -{1}[x](joinIB z) -{1}[y](joinIB z).
by rewrite leU2E ?meetIB ?meetBI // => /andP [].
Qed.

Lemma subKU y x : y `|` (x `\` y) = y `|` x.
Proof.
apply/eqP; rewrite eq_le leU2 //= leUx leUl.
by apply/meet_idPl; have := joinIB y x; rewrite joinIl (join_idPr _).
Qed.

Lemma subUK y x : (x `\` y) `|` y = x `|` y.
Proof. by rewrite joinC subKU joinC. Qed.

Lemma leBKU y x : y <= x -> y `|` (x `\` y) = x.
Proof. by move=> /join_idPl {2}<-; rewrite subKU. Qed.

Lemma leBUK y x : y <= x -> (x `\` y) `|` y = x.
Proof. by move=> leyx; rewrite joinC leBKU. Qed.

Lemma leBLR x y z : (x `\` y <= z) = (x <= y `|` z).
Proof.
apply/idP/idP; first by move=> /join_idPl <-; rewrite joinA subKU joinAC leUr.
by rewrite -{1}[x](joinIB y) => /(leU2r_le (subIK _ _)).
Qed.

Lemma subUx x y z : (x `|` y) `\` z = (x `\` z) `|` (y `\` z).
Proof.
apply/eqP; rewrite eq_le leUx !leBl ?leUr ?leUl ?andbT //.
by rewrite leBLR joinA subKU joinAC subKU joinAC -joinA leUr.
Qed.

Lemma sub_eq0 x y : (x `\` y == 0) = (x <= y).
Proof. by rewrite -lex0 leBLR joinx0. Qed.

Lemma joinxB x y z : x `|` (y `\` z) = ((x `|` y) `\` z) `|` (x `&` z).
Proof. by rewrite subUx joinAC joinBI. Qed.

Lemma joinBx x y z : (y `\` z) `|` x = ((y `|` x) `\` z) `|` (z `&` x).
Proof. by rewrite ![_ `|` x]joinC ![_ `&` x]meetC joinxB. Qed.

Lemma leBr z x y : x <= y -> z `\` y <= z `\` x.
Proof.
by move=> lexy; rewrite leBLR joinxB (meet_idPr _) ?leBUK ?leUr ?lexU ?lexy.
Qed.

Lemma leB2 x y z t : x <= z -> t <= y -> x `\` y <= z `\` t.
Proof. by move=> /(@leBl t) ? /(@leBr x) /le_trans ->. Qed.

Lemma meet_eq0E_sub z x y : x <= z -> (x `&` y == 0) = (x <= z `\` y).
Proof.
move=> xz; apply/idP/idP; last by move=> /meet_idPr <-; rewrite -meetA meetBI.
by move=> /eqP xIy_eq0; rewrite -[x](joinIB y) xIy_eq0 join0x leBl.
Qed.

Lemma leBRL x y z : (x <= z `\` y) = (x <= z) && (x `&` y == 0).
Proof.
apply/idP/idP => [xyz|]; first by rewrite (@meet_eq0E_sub z) // (le_trans xyz).
by move=> /andP [?]; rewrite -meet_eq0E_sub.
Qed.

Lemma eq_sub x y z : (x `\` y == z) = (z <= x <= y `|` z) && (z `&` y == 0).
Proof. by rewrite eq_le leBLR leBRL andbCA andbA. Qed.

Lemma subxU x y z : z `\` (x `|` y) = (z `\` x) `&` (z `\` y).
Proof.
apply/eqP; rewrite eq_le lexI !leBr ?leUl ?leUr //=.
rewrite leBRL leIx ?leBx //= meetUr meetAC subIK -meetA subIK.
by rewrite meet0x meetx0 joinx0.
Qed.

Lemma subx0 x : x `\` 0 = x.
Proof. by apply/eqP; rewrite eq_sub join0x meetx0 lexx eqxx. Qed.

Lemma sub0x x : 0 `\` x = 0.
Proof. by apply/eqP; rewrite eq_sub joinx0 meet0x lexx eqxx le0x. Qed.

Lemma subIx x y z : (x `&` y) `\` z = (x `\` z) `&` (y `\` z).
Proof.
apply/eqP; rewrite eq_sub joinIr ?leI2 ?subKU ?leUr ?leBx //=.
by rewrite -meetA subIK meetx0.
Qed.

Lemma meetxB x y z : x `&` (y `\` z) = (x `&` y) `\` z.
Proof. by rewrite subIx -{1}[x](joinBI z) meetUl meetIB joinx0. Qed.

Lemma meetBx x y z : (x `\` y) `&` z = (x `&` z) `\` y.
Proof. by rewrite ![_ `&` z]meetC meetxB. Qed.

Lemma subxI x y z : x `\` (y `&` z) = (x `\` y) `|` (x `\` z).
Proof.
apply/eqP; rewrite eq_sub leUx !leBx //= joinIl joinA joinCA !subKU.
rewrite joinCA -joinA [_ `|` x]joinC ![x `|` _](join_idPr _) //.
by rewrite -joinIl leUr /= meetUl {1}[_ `&` z]meetC ?meetBI joinx0.
Qed.

Lemma subBx x y z : (x `\` y) `\` z = x `\` (y `|` z).
Proof.
apply/eqP; rewrite eq_sub leBr ?leUl //=.
rewrite subxU joinIr subKU -joinIr (meet_idPl _) ?leUr //=.
by rewrite -meetA subIK meetx0.
Qed.

Lemma subxB x y z : x `\` (y `\` z) = (x `\` y) `|` (x `&` z).
Proof.
rewrite -[y in RHS](joinIB z) subxU joinIl subxI -joinA.
rewrite joinBI (join_idPl _) // joinBx [x `|` _](join_idPr _) ?leIl //.
by rewrite meetA meetAC subIK meet0x joinx0 (meet_idPr _).
Qed.

Lemma joinBK x y : (y `|` x) `\` x = (y `\` x).
Proof. by rewrite subUx subxx joinx0. Qed.

Lemma joinBKC x y : (x `|` y) `\` x = (y `\` x).
Proof. by rewrite subUx subxx join0x. Qed.

Lemma disj_le x y : x `&` y == 0 -> x <= y = (x == 0).
Proof.
have [->|x_neq0] := altP (x =P 0); first by rewrite le0x.
by apply: contraTF => lexy; rewrite (meet_idPl _).
Qed.

Lemma disj_leC x y : y `&` x == 0 -> x <= y = (x == 0).
Proof. by rewrite meetC => /disj_le. Qed.

Lemma disj_subl x y : x `&` y == 0 -> x `\` y = x.
Proof. by move=> dxy; apply/eqP; rewrite eq_sub dxy lexx leUr. Qed.

Lemma disj_subr x y : x `&` y == 0 -> y `\` x = y.
Proof. by rewrite meetC => /disj_subl. Qed.

Lemma lt0B x y : x < y -> 0 < y `\` x.
Proof.
by move=> ?; rewrite lt_leAnge leBRL leBLR le0x meet0x eqxx joinx0 /= lt_geF.
Qed.

End CBLatticeTheory.
End CBLatticeTheory.

Module CTBLattice.
  Section ClassDef.
    Record mixin_of (T : tblatticeType) (sub : T -> T -> T) := Mixin {
       compl : T -> T;
       _ : forall x, compl x = sub 1 x
    }.

    Record class_of (T : Type) := Class {
      base  : TBLattice.class_of T;
      mixin1 : CBLattice.mixin_of (BLattice.Pack base T);
      mixin2 : @mixin_of (TBLattice.Pack base T) (CBLattice.sub mixin1)
    }.

    Local Coercion base : class_of >-> TBLattice.class_of.
    Local Coercion base2 T (c : class_of T) :=
      CBLattice.Class (mixin1 c).

    Structure type := Pack { sort; _ : class_of sort; _ : Type }.

    Local Coercion sort : type >-> Sortclass.

    Variables (T : Type) (cT : type).

    Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.
    Definition clone c of phant_id class c := @Pack T c T.
    Let xT := let: Pack T _ _ := cT in T.
    Notation xclass := (class : class_of xT).

    Definition pack :=
      fun bT b & phant_id (TBLattice.class bT) (b : TBLattice.class_of T) =>
      fun m1T m1 &  phant_id (CBLattice.class m1T) (@CBLattice.Class T b m1) =>
      fun (m2 : @mixin_of (@TBLattice.Pack T b T) (CBLattice.sub m1)) =>
      Pack (@Class T b m1 m2) T.

    Definition eqType := @Equality.Pack cT xclass xT.
    Definition porderType := @POrder.Pack cT xclass xT.
    Definition latticeType := @Lattice.Pack cT xclass xT.
    Definition blatticeType := @BLattice.Pack cT xclass xT.
    Definition tblatticeType := @TBLattice.Pack cT xclass xT.
    Definition cblatticeType := @CBLattice.Pack cT xclass xT.
    Definition tbd_cblatticeType :=
      @CBLattice.Pack tblatticeType xclass xT.
  End ClassDef.

  Module Import Exports.
    Coercion base      : class_of >-> TBLattice.class_of.
    Coercion base2     : class_of >-> CBLattice.class_of.
    Coercion mixin1     : class_of >-> CBLattice.mixin_of.
    Coercion mixin2     : class_of >-> mixin_of.
    Coercion sort      : type >-> Sortclass.
    Coercion eqType    : type >-> Equality.type.
    Coercion porderType : type >-> POrder.type.
    Coercion latticeType : type >-> Lattice.type.
    Coercion blatticeType : type >-> BLattice.type.
    Coercion tblatticeType : type >-> TBLattice.type.
    Coercion cblatticeType : type >-> CBLattice.type.

    Canonical eqType.
    Canonical porderType.
    Canonical latticeType.
    Canonical blatticeType.
    Canonical tblatticeType.
    Canonical cblatticeType.
    Canonical tbd_cblatticeType.

    Notation ctblatticeType  := type.
    Notation ctblatticeMixin := mixin_of.
    Notation CTBLatticeMixin := Mixin.
    Notation CTBLatticeType T m := (@pack T _ _ id _ _ id m).

    Notation "[ 'ctblatticeType' 'of' T 'for' cT ]" := (@clone T cT _ id)
      (at level 0, format "[ 'ctblatticeType'  'of'  T  'for'  cT ]") : form_scope.
    Notation "[ 'ctblatticeType' 'of' T ]" := (@clone T _ _ id)
      (at level 0, format "[ 'ctblatticeType'  'of'  T ]") : form_scope.

    Notation "[ 'default_ctblatticeType' 'of' T ]" :=
      (@pack T _ _ id _ _ id (fun=> erefl))
      (at level 0, format "[ 'default_ctblatticeType'  'of'  T ]") : form_scope.

  End Exports.
End CTBLattice.

Export CTBLattice.Exports.

Module Import CTBLatticeDef.
Definition compl {T : ctblatticeType} : T -> T :=
  CTBLattice.compl (CTBLattice.class T).
End CTBLatticeDef.

Module Import CTBLatticeSyntax.
Notation "~` A" := (compl A).
End CTBLatticeSyntax.

Module Import CTBLatticeTheory.
Section CTBLatticeTheory.
Variable (L : ctblatticeType).
Implicit Types (x y z : L).

Lemma complE x : ~` x = 1 `\` x.
Proof. by case: L x => [? [? ? []]]. Qed.

Lemma sub1x x : 1 `\` x = ~` x.
Proof. by rewrite complE. Qed.

Lemma subE x y : x `\` y = x `&` ~` y.
Proof. by rewrite complE meetxB meetx1. Qed.

Lemma complK : involutive (@compl L).
Proof. by move=> x; rewrite !complE subxB subxx meet1x join0x. Qed.

Lemma compl_inj : injective (@compl L).
Proof. exact/inv_inj/complK. Qed.

Lemma disj_leC x y : (x `&` y == 0) = (x <= ~` y).
Proof. by rewrite -sub_eq0 subE complK. Qed.

Lemma leC x y : (~` x <= ~` y) = (y <= x).
Proof.
gen have leC : x y / y <= x -> ~` x <= ~` y; last first.
  by apply/idP/idP=> /leC; rewrite ?complK.
by move=> leyx; rewrite !complE leBr.
Qed.

Lemma complU x y : ~` (x `|` y) = ~` x `&` ~` y.
Proof. by rewrite !complE subxU. Qed.

Lemma complI  x y : ~` (x `&` y) = ~` x `|` ~` y.
Proof. by rewrite !complE subxI. Qed.

Lemma joinxC  x :  x `|` ~` x = 1.
Proof. by rewrite complE subKU joinx1. Qed.

Lemma joinCx  x : ~` x `|` x = 1.
Proof. by rewrite joinC joinxC. Qed.

Lemma meetxC  x :  x `&` ~` x = 0.
Proof. by rewrite complE subKI. Qed.

Lemma meetCx  x : ~` x `&` x = 0.
Proof. by rewrite meetC meetxC. Qed.

Lemma compl1 : ~` 1 = 0 :> L.
Proof. by rewrite complE subxx. Qed.

Lemma compl0 : ~` 0 = 1 :> L.
Proof. by rewrite complE subx0. Qed.

Lemma complB x y : ~` (x `\` y) = ~` x `|` y.
Proof. by rewrite !complE subxB meet1x. Qed.

Lemma leBC x y : x `\` y <= ~` y.
Proof. by rewrite leBLR joinxC lex1. Qed.

Lemma leCx x y : (~` x <= y) = (~` y <= x).
Proof. by rewrite !complE !leBLR joinC. Qed.

Lemma lexC x y : (x <= ~` y) = (y <= ~` x).
Proof. by rewrite !complE !leBRL !lex1 meetC. Qed.

Lemma compl_joins (J : Type) (r : seq J) (P : pred J) (F : J -> L) :
   ~` (\join_(j <- r | P j) F j) = \meet_(j <- r | P j) ~` F j.
Proof. by elim/big_rec2: _=> [|i x y ? <-]; rewrite ?compl0 ?complU. Qed.

Lemma compl_meets (J : Type) (r : seq J) (P : pred J) (F : J -> L) :
   ~` (\meet_(j <- r | P j) F j) = \join_(j <- r | P j) ~` F j.
Proof. by elim/big_rec2: _=> [|i x y ? <-]; rewrite ?compl1 ?complI. Qed.

End CTBLatticeTheory.
End CTBLatticeTheory.

Module Def.
Export POrderDef.
Export LatticeDef.
Export BLatticeDef.
Export TBLatticeDef.
Export CBLatticeDef.
Export CTBLatticeDef.
End Def.

Module Syntax.
Export POSyntax.
Export LatticeSyntax.
Export BLatticeSyntax.
Export TBLatticeSyntax.
Export CBLatticeSyntax.
Export CTBLatticeSyntax.
End Syntax.

Module Theory.
Export ReversePOrder.
Export POrderTheory.
Export TotalTheory.
Export ReverseLattice.
Export LatticeTheoryMeet.
Export LatticeTheoryJoin.
Export BLatticeTheory.
Export CBLatticeTheory.
Export ReverseTBLattice.
Export TBLatticeTheory.
Export CTBLatticeTheory.

Export POrder.Exports.
Export Total.Exports.
Export Lattice.Exports.
Export BLattice.Exports.
Export CBLattice.Exports.
Export TBLattice.Exports.
Export CTBLattice.Exports.

End Theory.

End Order.

Module SET.
Import Order.Theory Order.Syntax.
Open Scope order_scope.

Module Semiset.
Section ClassDef.
Variable elementType : Type.
Variable eqType_of_elementType : elementType -> eqType.
Coercion eqType_of_elementType : elementType >-> eqType.
Implicit Types (X Y : elementType).

Structure mixin_of (set : elementType -> cblatticeType) := Mixin {
  memset : forall X, set X -> X -> bool;
  set1 : forall X, X -> set X;
  _ : forall X (x : X), set1 x != 0;
  _ : forall X (x y : X), memset (set1 y) x = (x == y);
  _ : forall X (x : X) A, (set1 x <= A) = (memset A x);
  _ : forall X (A : set X), (A > 0) -> {x | memset A x} ;
  _ : forall X (A B : set X), (forall x, memset A x -> memset B x) -> A <= B;
  _ : forall X (x : X) A B, (memset (A `|` B) x) =
                    (memset A x) || (memset B x);

  funsort : elementType -> elementType -> Type;
  fun_of_funsort : forall X Y, funsort X Y -> X -> Y;
  imset : forall X Y, funsort X Y -> set X -> set Y;
  _ : forall X Y (f : funsort X Y) (A : set X) (y : Y),
    reflect (exists2 x : X, memset A x & y = fun_of_funsort f x)
            (memset (imset f A) y)
}.

Record class_of (set : elementType -> Type) := Class {
  base  : forall X, Order.CBLattice.class_of (set X);
  mixin : mixin_of (fun X => Order.CBLattice.Pack (base X) (set X))
}.

Local Coercion base : class_of >-> Funclass.

Structure type := Pack { sort ; _ : class_of sort;
                         _ : elementType -> Type }.

Local Coercion sort : type >-> Funclass.

Variables (set : elementType -> Type) (cT : type).

Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack set c set.
Let xset := let: Pack set _ _ := cT in set.
Notation xclass := (class : class_of xset).

Definition pack b0
  (m0 : mixin_of (fun X=> @Order.CBLattice.Pack (set X) (b0 X) (set X))) :=
  fun bT b & (forall X, phant_id (Order.CBLattice.class (bT X)) (b X)) =>
  fun    m & phant_id m0 m => Pack (@Class set b m) set.
End ClassDef.

Section CanonicalDef.
Variable elementType : Type.
Variable eqType_of_elementType : elementType -> eqType.
Coercion eqType_of_elementType : elementType >-> eqType.
Notation type := (type eqType_of_elementType).
Local Coercion base : class_of >-> Funclass.
Local Coercion sort : type >-> Funclass.
Variables (set : elementType -> Type) (X : elementType) (cT : type).

Let xset := let: Pack set _ _ := cT in set.
Notation xclass := (@class _ eqType_of_elementType cT : class_of eqType_of_elementType xset).

Definition eqType := @Equality.Pack (cT X) (xclass X) (xset X).
Definition porderType := @Order.POrder.Pack (cT X) (xclass X) (xset X).
Definition latticeType :=
  @Order.Lattice.Pack (cT X) (xclass X) (xset X).
Definition blatticeType :=
  @Order.BLattice.Pack (cT X) (xclass X) (xset X).
Definition cblatticeType :=
  @Order.CBLattice.Pack (cT X) (xclass X) (xset X).
End CanonicalDef.

Module Import Exports.
Coercion mixin     : class_of >-> mixin_of.
Coercion base      : class_of >-> Funclass.
Coercion sort      : type >-> Funclass.
Coercion eqType    : type >-> Equality.type.
Coercion porderType : type >-> Order.POrder.type.
Coercion latticeType : type >-> Order.Lattice.type.
Coercion blatticeType : type >-> Order.BLattice.type.
Coercion cblatticeType : type >-> Order.CBLattice.type.

Canonical eqType.
Canonical porderType.
Canonical latticeType.
Canonical blatticeType.
Canonical cblatticeType.

Notation semisetType  := type.
Notation semisetMixin := mixin_of.
Notation SemisetMixin := Mixin.
Notation SemisetType set m := (@pack _ _ set _ m _ _ (fun=> id) _ id).

Notation "[ 'semisetType' 'of' set 'for' cset ]" := (@clone _ _ set cset _ id)
  (at level 0, format "[ 'semisetType'  'of'  set  'for'  cset ]") :
                                                         form_scope.
Notation "[ 'semisetType' 'of' set ]" := (@clone _ _ set _ _ id)
  (at level 0, format "[ 'semisetType'  'of'  set ]") : form_scope.

End Exports.
End Semiset.

Import Semiset.Exports.

Section SemisetOperations.
Variable elementType : Type.
Variable eqType_of_elementType : elementType -> eqType.
Coercion eqType_of_elementType : elementType >-> eqType.
Variable set : semisetType eqType_of_elementType.

Definition setfun := Semiset.funsort (Semiset.class set).
Definition fun_of_setfun X Y (f : setfun X Y) : X -> Y :=
  @Semiset.fun_of_funsort _ _ _ (Semiset.class set) _ _ f.
Coercion fun_of_setfun : setfun >-> Funclass.

Variable X Y : elementType.

Definition memset : set X -> X -> bool :=
  @Semiset.memset _ _ _ (Semiset.class set) _.
Definition set1 : X -> set X :=
  @Semiset.set1 _ _ _ (Semiset.class set) _.
Definition imset : setfun X Y -> set X -> set Y:=
  @Semiset.imset _ _ _ (Semiset.class set) _ _.

Canonical set_predType := Eval hnf in mkPredType memset.

Structure setpredType := SetPredType {
  setpred_sort :> Type;
  tosetpred : setpred_sort -> pred X;
  _ : {mem : setpred_sort -> mem_pred X | isMem tosetpred mem};
  _ : {pred_fset : setpred_sort -> set X |
       forall p x, x \in pred_fset p = tosetpred p x}
}.

Canonical setpredType_predType (fpX : setpredType) :=
  @PredType X (setpred_sort fpX) (@tosetpred fpX)
  (let: SetPredType _ _ mem _ := fpX in mem).

Definition predset (fpX : setpredType) : fpX -> set X :=
  let: SetPredType _ _ _ (exist pred_fset _) := fpX in pred_fset.

End SemisetOperations.

Module Import SemisetSyntax.

Notation "[ 'set' x : T | P ]" := (predset (fun x : T => P%B))
  (at level 0, x at level 99, only parsing) : set_scope.
Notation "[ 'set' x | P ]" := [set x : _ | P]
  (at level 0, x, P at level 99, format "[ 'set'  x  |  P ]") : set_scope.
Notation "[ 'set' x 'in' A ]" := [set x | x \in A]
  (at level 0, x at level 99, format "[ 'set'  x  'in'  A ]") : set_scope.
Notation "[ 'set' x : T 'in' A ]" := [set x : T | x \in A]
  (at level 0, x at level 99, only parsing) : set_scope.
Notation "[ 'set' x : T | P & Q ]" := [set x : T | P && Q]
  (at level 0, x at level 99, only parsing) : set_scope.
Notation "[ 'set' x | P & Q ]" := [set x | P && Q ]
  (at level 0, x, P at level 99, format "[ 'set'  x  |  P  &  Q ]") : set_scope.
Notation "[ 'set' x : T 'in' A | P ]" := [set x : T | x \in A & P]
  (at level 0, x at level 99, only parsing) : set_scope.
Notation "[ 'set' x 'in' A | P ]" := [set x | x \in A & P]
  (at level 0, x at level 99, format "[ 'set'  x  'in'  A  |  P ]") : set_scope.
Notation "[ 'set' x 'in' A | P & Q ]" := [set x in A | P && Q]
  (at level 0, x at level 99,
   format "[ 'set'  x  'in'  A  |  P  &  Q ]") : set_scope.
Notation "[ 'set' x : T 'in' A | P & Q ]" := [set x : T in A | P && Q]
  (at level 0, x at level 99, only parsing) : set_scope.

Notation "[ 'set' a ]" := (set1 _ a)
  (at level 0, a at level 99, format "[ 'set'  a ]") : set_scope.
Notation "[ 'set' a : T ]" := [set (a : T)]
  (at level 0, a at level 99, format "[ 'set'  a   :  T ]") : set_scope.

End SemisetSyntax.

Module Import SemisetTheory.
Section SemisetTheory.

Variable elementType : Type.
Variable eqType_of_elementType : elementType -> eqType.
Coercion eqType_of_elementType : elementType >-> eqType.
Variable set : semisetType eqType_of_elementType.

Section setX.

Variables X : elementType.
Implicit Types (x y : X) (A B : set X).

Lemma set1_neq0 (x : X) : [set x] != 0 :> set X.
Proof.
rewrite /set1 /in_mem /= /memset.
case: set => [S [base [memset set1 /= H ? ? ? ? ? ? ? ? ?]] ?] /=.
exact: H.
Qed.

Lemma in_set1 x y : x \in ([set y] : set X) = (x == y).
Proof.
rewrite /set1 /in_mem /= /memset.
case: set => [S [base [memset set1 /= ? H ? ? ? ? ? ? ? ?]] ?] /=.
exact: H.
Qed.

Lemma sub1set x A : ([set x] <= A) = (x \in A).
Proof.
rewrite /set1 /in_mem /= /memset.
case: set A => [S [base [memset set1 /= ? ? H ? ? ? ? ? ? ?]] ?] A /=.
exact: H.
Qed.

Lemma set_gt0_ex A : A > 0 -> {x | x \in A}.
Proof.
rewrite /set1 /in_mem /= /memset.
case: set A => [S [base [memset set1 /= ? ? ? H ? ? ? ? ? ?]] ?] A /=.
exact: H.
Qed.

Lemma subsetP_subproof A B : {subset A <= B} -> A <= B.
Proof.
rewrite /set1 /in_mem /= /memset.
case: set A B => [S [base [memset set1 /= ? ? ? ? H ? ? ? ? ?]] ?] /=.
exact: H.
Qed.

Lemma in_setU (x : X) A B : (x \in A `|` B) = (x \in A) || (x \in B).
Proof.
rewrite /set1 /in_mem /= /memset.
case: set A B => [S [base [memset set1 /= ? ? ? ? ? H ? ? ? ?]] ?] /=.
exact: H.
Qed.

Lemma set1_eq0 x : ([set x] == 0 :> set X) = false.
Proof. by rewrite (negPf (set1_neq0 _)). Qed.

Lemma in_set0 x : x \in (0 : set X) = false.
Proof. by rewrite -sub1set lex0 set1_eq0. Qed.

Lemma set11 x : x \in ([set x] : set X).
Proof. by rewrite -sub1set. Qed.
Hint Resolve set11.

Lemma set1_inj : injective (@set1 _ _ set X).
Proof.
move=> x y /eqP; rewrite eq_le sub1set => /andP [].
by rewrite in_set1 => /eqP.
Qed.

Lemma set_0Vmem A : (A = 0) + {x : X | x \in A}.
Proof.
have [|AN0] := eqVneq A 0; [left|right] => //.
by move: AN0; rewrite -lt0x => /set_gt0_ex.
Qed.

Lemma set0Pn A : reflect (exists x, x \in A) (A != 0).
Proof.
have [->|[x xA]] := set_0Vmem A; rewrite ?eqxx -?lt0x.
  by constructor=> [[x]]; rewrite in_set0.
suff -> : 0 < A by constructor; exists x.
by move: xA; rewrite -sub1set => /(lt_le_trans _)->; rewrite ?lt0x ?set1_eq0.
Qed.

Lemma subsetP {A B} : reflect {subset A <= B} (A <= B).
Proof.
apply: (iffP idP) => [sAB x xA|/subsetP_subproof//].
by rewrite -sub1set (le_trans _ sAB) // sub1set.
Qed.

Lemma setP A B : A =i B <-> A = B.
Proof.
split; last by move->.
move=> eqAB; apply/eqP; rewrite eq_le.
gen have leAB : A B eqAB / A <= B; last by rewrite !leAB.
by apply/subsetP => x; rewrite eqAB.
Qed.

Lemma subset1 A x : (A <= [set x]) = (A == [set x]) || (A == 0).
Proof.
symmetry; rewrite eq_le; have [] /= := boolP (A <= [set x]); last first.
  by apply: contraNF => /eqP ->; rewrite ?le0x.
have [/eqP->|[y yA]] := set_0Vmem A; rewrite ?orbT // ?sub1set.
by move=> /subsetP /(_ _ yA); rewrite in_set1 => /eqP<-; rewrite yA.
Qed.

Lemma eq_set1 (x : X) A : (A == [set x]) = (0 < A <= [set x]).
Proof.
by rewrite subset1; have [->|?] := posxP A; rewrite 1?eq_sym ?set1_eq0 ?orbF.
Qed.

Lemma in_setI A B (x : X) : (x \in A `&` B) = (x \in A) && (x \in B).
Proof.
apply/idP/idP => [xAB|?]; last by rewrite -sub1set lexI !sub1set.
by rewrite (subsetP (leIr _ _) _ xAB) (subsetP (leIl _ _) _ xAB).
Qed.

Lemma set1U A x : [set x] `&` A = if x \in A then [set x] else 0.
Proof.
apply/setP => y; rewrite (fun_if (fun E => y \in E)) in_setI in_set1 in_set0.
by have [->|] := altP (y =P x); rewrite ?if_same //; case: (_ \in A).
Qed.

Lemma set1U_eq0 A x : ([set x] `&` A == 0) = (x \notin A).
Proof. by rewrite set1U; case: (x \in A); rewrite ?set1_eq0 ?eqxx. Qed.

Lemma in_setD A B x : (x \in A `\` B) = (x \notin B) && (x \in A).
Proof.
apply/idP/idP => [|/andP[xNB xA]]; last first.
  by rewrite -sub1set leBRL sub1set xA set1U_eq0.
rewrite -sub1set leBRL sub1set => /andP [-> dxB].
by rewrite -sub1set disj_le ?set1_eq0.
Qed.

Lemma properP A B : reflect (A <= B /\ (exists2 x, x \in B & x \notin A))
                            (A < B).
Proof.
apply: (iffP idP)=> [ltAB|[leAB [x xB xNA]]].
  rewrite ltW //; split => //; have := lt0B ltAB; rewrite lt0x.
  by move => /set0Pn [x]; rewrite in_setD => /andP [xNA xB]; exists x.
rewrite lt_neqAle leAB andbT; apply: contraTneq xNA.
by move=> /setP /(_ x) ->; rewrite xB.
Qed.

Lemma set1P x y : reflect (x = y) (x \in ([set y] : set X)).
Proof. by rewrite in_set1; apply/eqP. Qed.

End setX.

Section setXY.

Variables X Y : elementType.
Implicit Types (x : X) (y : Y) (A : set X) (B : set Y) (f : setfun set X Y).

Lemma imsetP (f : setfun set X Y) A y :
    reflect (exists2 x : X, x \in A & y = f x) (y \in imset f A).
Proof.
move: A f; rewrite /set1 /in_mem /= /memset /imset /setfun.
case: set => [S [base [memset set1 /= ? ? ? ? ? ? ? ? ? H]]] ? /= A f.
exact: H.
Qed.

Lemma mem_imset f A x : x \in A -> f x \in imset f A.
Proof. by move=> Dx; apply/imsetP; exists x. Qed.

Lemma imset0 f : imset f 0 = 0.
Proof.
apply/setP => y; rewrite in_set0.
by apply/imsetP => [[x]]; rewrite in_set0.
Qed.

Lemma imset_eq0 f A : (imset f A == 0) = (A == 0).
Proof.
have [->|/set_gt0_ex [x xA]] := posxP A; first by rewrite imset0 eqxx.
by apply/set0Pn; exists (f x); rewrite mem_imset.
Qed.

Lemma imset_set1 f x : imset f [set x] = [set f x].
Proof.
apply/setP => y.
by apply/imsetP/set1P=> [[x' /set1P-> //]| ->]; exists x; rewrite ?set11.
Qed.

Lemma imsetS f A A' : A <= A' -> imset f A <= imset f A'.
Proof.
move=> leAB; apply/subsetP => y /imsetP [x xA ->].
by rewrite mem_imset // (subsetP leAB).
Qed.

Lemma imset_proper f A A' :
   {in A' &, injective f} -> A < A' -> imset f A < imset f A'.
Proof.
move=> injf /properP[sAB [x Bx nAx]]; rewrite lt_leAnge imsetS //=.
apply: contra nAx => sfBA.
have: f x \in imset f A by rewrite (subsetP sfBA) ?mem_imset.
by case/imsetP=> y Ay /injf-> //; apply: subsetP sAB y Ay.
Qed.

End setXY.

End SemisetTheory.
End SemisetTheory.

(* Module Import FinsetSemiset. *)
(* Section FinsetSemiset. *)
(* Variable *)

(* End FinsetSemiset. *)
(* End FinsetSemiset. *)

Module set.
Section ClassDef.
Variable elementType : Type.
Variable eqType_of_elementType : elementType -> eqType.
Coercion eqType_of_elementType : elementType >-> eqType.
Implicit Types (X Y : elementType).

Record class_of (set : elementType -> Type) := Class {
  base  : forall X, Order.CTBLattice.class_of (set X);
  mixin : Semiset.mixin_of eqType_of_elementType
                           (fun X => Order.CBLattice.Pack (base X) (set X))
}.

Local Coercion base : class_of >-> Funclass.
Definition base2 (set : elementType -> Type)
         (c : class_of set) := Semiset.Class (@mixin set c).
Local Coercion base2 : class_of >-> Semiset.class_of.

(* Local Coercion base : class_of >-> Order.CBLattice.class_of. *)

Structure type := Pack { sort ; _ : class_of sort;
                         _ : elementType -> Type }.

Local Coercion sort : type >-> Funclass.

Variables (set : elementType -> Type) (cT : type).

Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.
(* Definition clone c of phant_id class c := @Pack set c set. *)
Let xset := let: Pack set _ _ := cT in set.
Notation xclass := (class : class_of xset).

Definition pack :=
  fun bT (b : forall X, Order.CTBLattice.class_of _)
      & (forall X, phant_id (Order.CTBLattice.class (bT X)) (b X)) =>
  fun mT m & phant_id (@Semiset.class _ eqType_of_elementType mT)
                      (@Semiset.Class _ _ set b m) =>
  Pack (@Class set (fun x => b x) m) set.

End ClassDef.

Section CanonicalDef.
Variable elementType : Type.
Variable eqType_of_elementType : elementType -> eqType.
Coercion eqType_of_elementType : elementType >-> eqType.
Notation type := (type eqType_of_elementType).
Local Coercion sort : type >-> Funclass.
Local Coercion base : class_of >-> Funclass.
Local Coercion base2 : class_of >-> Semiset.class_of.
Variables (set : elementType -> Type) (X : elementType) (cT : type).

Let xset := let: Pack set _ _ := cT in set.
Notation xclass := (@class _ eqType_of_elementType cT : class_of eqType_of_elementType xset).

Definition eqType := @Equality.Pack (cT X) (xclass X) (xset X).
Definition porderType := @Order.POrder.Pack (cT X) (xclass X) (xset X).
Definition latticeType :=
  @Order.Lattice.Pack (cT X) (xclass X) (xset X).
Definition blatticeType :=
  @Order.BLattice.Pack (cT X) (xclass X) (xset X).
Definition cblatticeType :=
  @Order.CBLattice.Pack (cT X) (xclass X) (xset X).
Definition ctblatticeType :=
  @Order.CTBLattice.Pack (cT X) (xclass X) (xset X).
Definition semisetType := @Semiset.Pack _ _ cT xclass xset.
Definition semiset_ctblatticeType :=
  @Order.CTBLattice.Pack (semisetType X) (xclass X) (xset X).
End CanonicalDef.

Module Import Exports.
Coercion base      : class_of >-> Funclass.
Coercion base2     : class_of >-> Semiset.class_of.
Coercion sort      : type >-> Funclass.
Coercion eqType    : type >-> Equality.type.
Coercion porderType : type >-> Order.POrder.type.
Coercion latticeType : type >-> Order.Lattice.type.
Coercion blatticeType : type >-> Order.BLattice.type.
Coercion cblatticeType : type >-> Order.CBLattice.type.
Coercion ctblatticeType : type >-> Order.CTBLattice.type.
Coercion semisetType : type >-> Semiset.type.

Canonical eqType.
Canonical porderType.
Canonical latticeType.
Canonical blatticeType.
Canonical cblatticeType.
Canonical ctblatticeType.
Canonical semisetType.

Notation setType  := type.

Notation "[ 'setType' 'of' set ]" :=
  (@pack _ _ set _ _ (fun=> id) _ _ id)
  (at level 0, format "[ 'setType'  'of'  set ]") : form_scope.

End Exports.
End set.

Import set.Exports.

Module Import setTheory.
Section setTheory.

Variable elementType : Type.
Variable eqType_of_elementType : elementType -> eqType.
Coercion eqType_of_elementType : elementType >-> eqType.
Variable set : setType eqType_of_elementType.

Section setX.

Variables X : elementType.
Implicit Types (x y : X) (A B : set X).

End setX.

End setTheory.
End setTheory.

End SET.
