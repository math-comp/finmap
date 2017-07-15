(*************************************************************************)
(* Copyright (C) 2013 - 2015                                             *)
(* Author C. Cohen                                                       *)
(* DRAFT - PLEASE USE WITH CAUTION                                       *)
(* License CeCILL-B                                                      *)
(*************************************************************************)

From mathcomp
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq.
From mathcomp
Require Import choice path finset finfun fintype bigop.

(*****************************************************************************)
(* This file provides a representation of finitely supported maps where      *)
(* the keys K lie in a choiceType and the values V in an arbitrary type.     *)
(*                                                                           *)
(*         {fset K} == finite sets of elements of K                          *)
(*    {fmap K -> V} == finitely supported maps from K to V.                  *)
(*                                                                           *)
(* In the remainder, A and B are of type {fset K}.                           *)
(* - {fset K} is provided with a canonical structure of predType, in order   *)
(*   to enable the notation "a \in A"                                        *)
(* - There is a coercion from {fset K} to Type in order to interpret any     *)
(*   finset A as the subType of elements a : K such that a \in A             *)
(*   because of this coercion, writing a : A makes sense                     *)
(*                                                                           *)
(* The following notations are in the %fset scope                            *)
(*            fset0 == the empty finite set                                  *)
(*         [fset k] == the singleton finite set {k}                          *)
(*          A `&` B == the intersection of A and B                           *)
(*          A `|` B == the union of A and B                                  *)
(*           a |` B == the union of singleton a and B                        *)
(*          A `\` B == the complement of B in A                              *)
(*           A `\ b == A without b                                           *)
(*          A `*` B == the cartesian product of A and B                      *)
(* [disjoint A & B] := A `&` B == 0                                          *)
(*     A `<=` B == A is a subset of B                                        *)
(*     A `<` B == A is a proper subset of B                                  *)
(*            #|`A| == cardinal of A                                         *)
(*    fincl AsubB a == turns a : A  into an element of B                     *)
(*                     using a proof AsubB of A \fsubset B                   *)
(*         fsub B A == turns A : {fset K} into a {set B}                     *)
(*           f @` A == the image set of the collective predicate A by f.     *)
(*      f @2`(A, B) == the image set of A x B by the binary function f.      *)
(*                                                                           *)
(* In order to support the following notations, we introduce three canonical *)
(* structure that reflect the finiteness of a predicate, in the following    *)
(* notations, p (resp q) are such finite predicates, which are ultimately    *)
(* represented by elements A (resp B) from {fset K}.                         *)
(*                                                                           *)
(*    [fset x in p | P] == the set of all x of type K, such that             *)
(*                         x \in p and P x where P is a predicate on K       *)
(*  [fset x in p | P & Q] := [set x in p | P && Q].                          *)
(*                                                                           *)
(* [fset E | x in p] == the set of all the values of the expression E, for x *)
(*                     drawn from the collective finite predicate p.         *)
(* [fset E | x in p & P] == the set of values of E for x drawn from p, such  *)
(*                     that P is true.                                       *)
(* [fset E | x in p, y in q] == the set of values of E for x drawn from p and*)
(*                     and y drawn from q; q may depend on x.                *)
(* [fset E | x in p, y in q & P] == the set of values of E for x drawn from  *)
(*                    p and y drawn from q; such that P is true.             *)
(* [fsetval x in p] == the set of (val x) for x in the finite predicate p    *)
(* [fsetval x in p | P ] == the set of (val x) for x in p, such that P       *)
(* [fsetval x in p | P & Q] := [fsetval x in p | P && Q]                     *)
(*                                                                           *)
(* For each notation above, there is an additional one with ':' instead of   *)
(* 'in' which is used to range over the finite type A instead of the finite  *)
(* set A, and the optional predicate is over A instead of K                  *)
(* For example:                                                              *)
(*    [fset x : A | P] := [fset x in {: A} | P]                              *)
(*                     == the set of all x of type A, such that P x          *)
(* [fset E | x : A] == the set of all the values of the expression E, for x  *)
(*                     drawn from the finite type A                          *)
(*                                                                           *)
(* Operations on finmap:                                                     *)
(* The following notations are in the %fmap scope                            *)
(*                                                                           *)
(*           f.[? k] == returns Some v if k maps to v, otherwise None        *)
(*             f.[p] == returns v if p has type k \in f, and k maps to v     *)
(*        f.[k <- v] == f extended with the mapping k -> v                   *)
(*            domf f == finite set (of type {fset K}) of keys of f           *)
(*          codomf f == finite set (of type {fset V}) of values of f         *)
(*           k \in f == k is a key of f                                      *)
(*                   := k \in domf f                                         *)
(*            [fmap] == the empty finite map                                 *)
(* [fmap x : S => E] == the finmap defined by E on the support S             *)
(*           f.[& A] == f restricted to A (intersected with domf f)          *)
(*           f.[\ A] := f.[& domf `\` A]                                     *)
(*                   == f where all the keys in A have been removed          *)
(*           f.[~ k] := f.[\ [fset k]]                                       *)
(*             f + g == concatenation of f and g,                            *)
(*                      the keys of g override the keys of f                 *)
(*                                                                           *)
(* Operation on function with finite support, i.e. finmap with default value *)
(* for elements outside of the support. Contrarly to finmap, these are total *)
(* function, so we provide a coercion to Funclass                            *)
(*  {fsfun x : K => f x} := fsfun f == the type of fsfun with default f      *)
(*              [fsfun of default] == the default fsfun                      *)
(* [fsfun of default | x : A => F] == the fsfun which takes value F on A     *)
(*                                    x has type A                           *)
(* [fsfun of default | x in A => F] == the fsfun which takes value F on A    *)
(*                                    x has type T                           *)
(* we also provide untyped variants and variants where default is ommitted   *)
(* e.g.  [fsfun x : A => F] [fsfun of default | x => F] [fsfun]...           *)
(*     (f \o g)%fsfun == composition of fsfun                                *)
(*     fsinjectiveb f == boolean predicate of injectivity of f               *)
(*****************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Reserved Notation "{fset K }" (at level 0, format "{fset  K }").
Reserved Notation "A `&` B"  (at level 48, left associativity).
Reserved Notation "A `*` B"  (at level 46, left associativity).
Reserved Notation "A `+` B"  (at level 54, left associativity).
Reserved Notation "A +` B"  (at level 54, left associativity).
Reserved Notation "A `|` B" (at level 52, left associativity).
Reserved Notation "a |` A" (at level 52, left associativity).
Reserved Notation "A `\` B" (at level 50, left associativity).
Reserved Notation "A `\ b" (at level 50, left associativity).

Reserved Notation "{fmap T }" (at level 0, format "{fmap  T }").
Reserved Notation "x .[ k <- v ]"
  (at level 2, k at level 200, v at level 200, format "x .[ k  <-  v ]").
Reserved Notation "x .[~ k ]" (at level 2, k at level 200, format "x .[~  k ]").
Reserved Notation "x .[& k ]" (at level 2, k at level 200, format "x .[&  k ]").
Reserved Notation "x .[\ k ]" (at level 2, k at level 200, format "x .[\  k ]").
Reserved Notation "x .[? k ]" (at level 2, k at level 200, format "x .[?  k ]").
Reserved Infix "`~`" (at level 52).
Reserved Notation "[ 'fset' k ]" (at level 0, k at level 99, format "[ 'fset'  k ]").

Local Notation predOfType T := (sort_of_simpl_pred (@pred_of_argType T)).

Section extra.

Lemma mem_remF (T : eqType) (s : seq T) x : uniq s -> x \in rem x s = false.
Proof. by move=> us; rewrite mem_rem_uniq // inE eqxx. Qed.

Definition ffun0 (T : finType) (X : Type) : #|T| = 0 -> {ffun T -> X}.
Proof. by move=> T0; split; rewrite T0; exists nil. Defined.

Definition oextract (T : Type) (o : option T) : o -> T :=
  if o is Some t return o -> T then fun=> t else False_rect T \o notF.

Lemma oextractE (T : Type) (x : T) (xP : Some x) : oextract xP = x.
Proof. by []. Qed.

Lemma Some_oextract T (x : option T) (x_ex : x) : Some (oextract x_ex) = x.
Proof. by case: x x_ex. Qed.

Definition ojoin T (x : option (option T)) :=
  if x is Some y then y else None.

Lemma Some_ojoin T (x : option (option T)) : x -> Some (ojoin x) = x.
Proof. by case : x. Qed.

Lemma ojoinT T (x : option (option T)) : ojoin x -> x.
Proof. by case: x. Qed.

End extra.

Section ChoiceKeys.

Variable (K : choiceType).
Implicit Types (k : K) (ks : seq K).

Definition sort_keys (s : seq K) : seq K :=
   choose [pred t : seq K | perm_eq (undup s) t] (undup s).

Fact sort_keys_uniq s : uniq (sort_keys s).
Proof.
rewrite /sort_keys; set P := (X in choose X).
have : P (choose P (undup s)) by exact/chooseP/perm_eq_refl.
by move=> /perm_eq_uniq <-; rewrite undup_uniq.
Qed.

Fact sort_keysE (s : seq K) : sort_keys s =i s.
Proof.
rewrite /sort_keys; set P := (X in choose X) => x.
have : P (choose P (undup s)) by exact/chooseP/perm_eq_refl.
by move=> /perm_eq_mem <-; rewrite mem_undup.
Qed.
Hint Resolve sort_keysE.

Lemma eq_sort_keys (s s' : seq K) :
  s =i s' <-> sort_keys s = sort_keys s'.
Proof.
split=> [eq_ss'|eq_ss' k]; last by rewrite -sort_keysE eq_ss' sort_keysE.
rewrite /sort_keys; have peq_ss' : perm_eq (undup s) (undup s').
  by apply: uniq_perm_eq; rewrite ?undup_uniq // => x; rewrite !mem_undup.
rewrite (@choose_id _ _ _ (undup s')) //=; apply: eq_choose => x /=.
by apply: sym_left_transitive; [exact: perm_eq_sym|exact: perm_eq_trans|].
Qed.

Lemma mem_sort_keys ks k : k \in ks -> k \in sort_keys ks.
Proof. by rewrite sort_keysE. Qed.

Lemma mem_sort_keys_intro ks k : k \in sort_keys ks -> k \in ks.
Proof. by rewrite sort_keysE. Qed.

Lemma sort_keys_nil : sort_keys [::] = [::].
Proof.
have := sort_keysE [::].
by case: sort_keys => //= a l /(_ a); rewrite mem_head.
Qed.

Lemma sort_keys_id ks : sort_keys (sort_keys ks) = sort_keys ks.
Proof. by have /eq_sort_keys := sort_keysE ks. Qed.

Definition canonical_keys ks := sort_keys ks == ks.

Lemma canonical_uniq ks : canonical_keys ks -> uniq ks.
Proof. by move=> /eqP <-; exact: sort_keys_uniq. Qed.

Lemma canonical_sort_keys ks : canonical_keys (sort_keys ks).
Proof. by rewrite /canonical_keys sort_keys_id. Qed.

Lemma canonical_eq_keys ks ks' :
  canonical_keys ks -> canonical_keys ks' ->
  ks =i ks' -> ks = ks'.
Proof.
move=> /eqP; case: _ /; move=> /eqP; case: _ / => eq_ks_ks'.
by apply/eq_sort_keys => x; rewrite -sort_keysE eq_ks_ks' sort_keysE.
Qed.

Lemma size_sort_keys ks : size (sort_keys ks) = size (undup ks).
Proof.
rewrite -(iffLR (@eq_sort_keys _ _) (mem_undup _)); symmetry.
by apply/eqP; rewrite -uniq_size_uniq ?sort_keys_uniq ?undup_uniq.
Qed.

End ChoiceKeys.

Arguments eq_sort_keys {K s s'}.

Section Def.
Variables (K : choiceType).

Structure finSet : Type := mkFinSet {
  enum_fset : seq K;
  _ : canonical_keys enum_fset
}.

Definition finset_of (_ : phant K) := finSet.

End Def.

Identity Coercion type_of_finset : finset_of >-> finSet.
Notation "{fset T }" := (@finset_of _ (Phant T)) : type_scope.

Definition pred_of_finset (K : choiceType)
  (f : finSet K) : pred K := fun k => k \in (enum_fset f).
Canonical finSetPredType (K : choiceType) :=
  Eval hnf in mkPredType (@pred_of_finset K).

Section FinSetCanonicals.

Variable (K : choiceType).

Canonical fsetType := Eval hnf in [subType for (@enum_fset K)].
Definition fset_eqMixin := Eval hnf in [eqMixin of {fset K} by <:].
Canonical fset_eqType := Eval hnf in EqType {fset K} fset_eqMixin.
Definition fset_choiceMixin := Eval hnf in [choiceMixin of {fset K} by <:].
Canonical fset_choiceType := Eval hnf in ChoiceType {fset K} fset_choiceMixin.

End FinSetCanonicals.

Section FinTypeSet.

Variables (K : choiceType) (A : finSet K).

Record fset_sub_type : Type :=
  FSetSub {fsval : K; fsvalP : in_mem fsval (@mem K _ A)}.

Canonical fset_sub_subType := Eval hnf in [subType for fsval].
Definition fset_sub_eqMixin := Eval hnf in [eqMixin of fset_sub_type by <:].
Canonical fset_sub_eqType := Eval hnf in EqType fset_sub_type fset_sub_eqMixin.
Definition fset_sub_choiceMixin := Eval hnf in [choiceMixin of fset_sub_type by <:].
Canonical fset_sub_choiceType := Eval hnf in ChoiceType fset_sub_type fset_sub_choiceMixin.

Definition fset_sub_enum : seq fset_sub_type :=
  undup (pmap insub (enum_fset A)).

Lemma mem_fset_sub_enum x : x \in fset_sub_enum.
Proof. by rewrite mem_undup mem_pmap -valK map_f // fsvalP. Qed.

Lemma val_fset_sub_enum : uniq (enum_fset A) ->
  map val fset_sub_enum = enum_fset A.
Proof.
move=> Us; rewrite /fset_sub_enum undup_id ?pmap_sub_uniq //.
rewrite (pmap_filter (@insubK _ _ _)); apply/all_filterP.
by apply/allP => x; rewrite isSome_insub.
Qed.

Definition fset_sub_pickle x := index x fset_sub_enum.
Definition fset_sub_unpickle n := nth None (map some fset_sub_enum) n.
Lemma fset_sub_pickleK : pcancel fset_sub_pickle fset_sub_unpickle.
Proof.
rewrite /fset_sub_unpickle => x.
by rewrite (nth_map x) ?nth_index ?index_mem ?mem_fset_sub_enum.
Qed.

Definition fset_sub_countMixin := CountMixin fset_sub_pickleK.
Canonical fset_sub_countType := Eval hnf in CountType fset_sub_type fset_sub_countMixin.

Definition fset_sub_finMixin :=
  Eval hnf in UniqFinMixin (undup_uniq _) mem_fset_sub_enum.
Canonical fset_sub_finType := Eval hnf in FinType fset_sub_type fset_sub_finMixin.
Canonical fset_sub_subfinType := [subFinType of fset_sub_type].

Lemma card_fsetE : #|{: fset_sub_type}| = size (enum_fset A).
Proof.
rewrite cardE enumT -(size_map val) unlock val_fset_sub_enum //.
by rewrite canonical_uniq //; case: A.
Qed.

End FinTypeSet.

Identity Coercion finSet_sub_type : finset_of >-> finSet.
Coercion fset_sub_type : finSet >-> Sortclass.
Hint Resolve fsvalP.

Delimit Scope fset_scope with fset.
Local Open Scope fset_scope.

Notation "[` kf ]" := (FSetSub kf) (format "[`  kf ]") : fset_scope.

Lemma fsetsubE (T : choiceType) (A : {fset T}) (x : A) (xA : val x \in A) : [` xA] = x.
Proof. by apply/val_inj => /=. Qed.

Definition fset_predT {T : choiceType} {A : {fset T}} := @predT {: A}.
Notation "#|` A |" := #|@fset_predT _ A|
  (at level 0, A at level 99, format "#|`  A |") : nat_scope.
Coercion set_of_fset (K : choiceType) (A : {fset K}) : {set A} :=
   [set x | x \in {: A}].

Section Basics.
Variables (K : choiceType).

Lemma keys_canonical (f : {fset K}) : canonical_keys (enum_fset f).
Proof. by case: f. Qed.

Lemma enum_fset_uniq (f : {fset K}) : uniq (enum_fset f).
Proof. by rewrite canonical_uniq // keys_canonical. Qed.

End Basics.

Fact finset_key : unit. Proof. exact: tt. Qed.
Definition seq_fset : forall K : choiceType, seq K -> {fset K} :=
   locked_with finset_key (fun K s => mkFinSet (@canonical_sort_keys K s)).

Lemma seq_fsetE (K : choiceType) (s : seq K) : seq_fset s =i s.
Proof. by move=> a; rewrite [seq_fset]unlock sort_keysE. Qed.

Arguments pred_of_finset : simpl never.

Hint Resolve keys_canonical.
Hint Resolve sort_keys_uniq.

Canonical  finSetSubType K := [subType for (@enum_fset K)].
Definition finSetEqMixin (K : choiceType) := [eqMixin of {fset K} by <:].
Canonical  finSetEqType  (K : choiceType) := EqType {fset K} (finSetEqMixin K).
Definition finSetChoiceMixin (K : choiceType) := [choiceMixin of {fset K} by <:].
Canonical  finSetChoiceType  (K : choiceType) := ChoiceType {fset K} (finSetChoiceMixin K).

Section FinPredStruct.

Structure finpredType (T : choiceType) := FinPredType {
  finpred_sort :> Type;
  tofinpred : finpred_sort -> pred T;
  _ : {mem : finpred_sort -> mem_pred T | isMem tofinpred mem};
  _ : {pred_fset : finpred_sort -> {fset T} |
       forall p x, x \in pred_fset p = tofinpred p x}
}.

Canonical finpredType_predType (T : choiceType) (fpT : finpredType T) :=
  @PredType T (finpred_sort fpT) (@tofinpred T fpT)
  (let: FinPredType _ _ mem _ := fpT in mem).

Definition pred_fset  (T : choiceType) (fpT : finpredType T) :
  fpT -> {fset T} :=
  let: FinPredType _ _ _ (exist pred_fset _) := fpT in pred_fset.

Lemma pred_fsetE (T : choiceType) (fpT : finpredType T) (p : fpT) :
   pred_fset p =i p.
Proof.
by case: fpT p => ? ? ? [pred_fset pred_fsetE] p x; rewrite pred_fsetE -topredE.
Qed.

Lemma mkFinPredType_of_subproof (T : choiceType) (pT : predType T)
   (pred_fset : pT -> {fset T}) (pred_fsetE : forall p, pred_fset p =i p) :
  forall p x, x \in pred_fset p = topred p x.
Proof. by move=> p x; rewrite topredE pred_fsetE. Qed.

Definition mkFinPredType_of (T : choiceType) (U : Type) :=
  fun (pT : predType T) & pred_sort pT -> U =>
  fun a mP (pT' := @PredType T U a mP) & phant_id pT' pT =>
  fun (pred_fset : pT' -> {fset T}) (pred_fsetE : forall p, pred_fset p =i p) =>
  @FinPredType T U a mP (exist _ pred_fset (mkFinPredType_of_subproof pred_fsetE)).

Definition clone_finpredType (T : choiceType) (U : Type) :=
  fun (pT : finpredType T) & finpred_sort pT -> U =>
  fun a mP pP (pT' := @FinPredType T U a mP pP) & phant_id pT' pT => pT'.


Structure finpred (T : choiceType) (pT : predType T) (P : pred T) (A : {fset T}) :=
  FinPredTerm {
  pT_of_finpred :> pT;
  _ : forall x, x \in pT_of_finpred = P x;
  _ : forall x, x \in A = P x;
}.

Lemma finpredE (T : choiceType) (pT : predType T) (P : pred T) (A : {fset T})
 (ppT : finpred pT P A)  x :
  (x \in pT_of_finpred ppT = P x) * (x \in A = P x).
Proof. by case: ppT. Qed.

Structure finmempred (T : choiceType) (P : pred T) (A : {fset T}) := FinMemPred {
  pred_of_finmempred :> mem_pred T;
  _ : forall x : T, (in_mem x pred_of_finmempred) = P x;
  _ : forall x : T, (x \in A) = P x
}.

Lemma finmempredE (T : choiceType) (P : pred T)  (A : {fset T}) (mP : finmempred P A) :
  forall x, ((x \in A) = P x) * (in_mem x mP = P x).
Proof. by case: mP. Qed.

Lemma in_finmempred (T : choiceType) (P : pred T)  (A : {fset T}) (mP : finmempred P A) x :
  x \in mP = P x.
Proof. by rewrite [LHS]finmempredE. Qed.

Definition finmempred_of (T : choiceType) (P : pred T) (A : {fset T}) (mP : finmempred P A) &
           phantom (mem_pred T) mP : finmempred P A := mP.

Definition finpred_of (T : choiceType) (pT : predType T) (P : pred T) (A : {fset T})
 (fpT : @finpred T pT P A) & phantom (pred_sort pT) fpT := fpT.

End FinPredStruct.

Notation "[ 'finpredType' 'of' T ]" := (@clone_finpredType _ T _ id _ _ _ id)
  (at level 0, format "[ 'finpredType'  'of'  T ]") : form_scope.

Notation mkFinPredType T pred_fsetE :=
  (@mkFinPredType_of _ T _ id _ _ id _ pred_fsetE).

Section CanonicalFinPred.

(* This is en internal construciton, please use [fset x in A] instead of fset A. *)
Definition finset (T : finType) (P : pred T) := seq_fset (enum P).

Fact in_finset  (T : finType) (P : pred T) x : x \in finset P = P x.
Proof. by rewrite seq_fsetE mem_enum. Qed.

Canonical fset_finpredType (T: choiceType) :=
  mkFinPredType (finSet T) (fun _ _ => erefl).

Canonical pred_finpredType (T : finType) :=
   mkFinPredType (pred T) (@in_finset _).

Canonical simpl_pred_finpredType (T : finType) :=
   mkFinPredType (simpl_pred T) (@in_finset _).

Program Canonical mem_finmempred (T : choiceType)
  (pT : predType T) (P : pred T) (A : {fset T}) (p : finpred pT P A) :=
  @FinMemPred _ [pred x | P x] A (mem p) _ _.
Next Obligation. by rewrite finpredE. Qed.
Next Obligation. by rewrite (finpredE p). Qed.

Program Canonical finpredType_finpred (T : choiceType) (fpT : finpredType T)
   (A : finpred_sort fpT) :=
 @FinPredTerm _ _ [pred x in A] (pred_fset A) A (fun=> erefl) _.
Next Obligation. by rewrite pred_fsetE. Qed.

Program Canonical subfinset_finpred (T : choiceType) (A : {fset T}) (Q : pred T) :=
  @FinPredTerm _ _ [pred x in A | Q x]
               (seq_fset [seq x <- enum_fset A | Q x])
               [pred x in A | Q x] _ _.
Next Obligation. by rewrite seq_fsetE mem_filter andbC. Qed.

End CanonicalFinPred.

Local Notation imfset_def :=
  (fun (T K : choiceType) (f : T -> K) (P : pred T) (A : {fset T})
       (p : finmempred P A) of phantom (mem_pred T) p =>
  seq_fset [seq f x | x <- enum_fset A]).
Local Notation imfset2_def :=
  (fun (T1 T2 K : choiceType) (f : T1 -> T2 -> K)
       (P1 : pred T1) (A1 : {fset T1}) (P2 : T1 -> pred T2) (A2 : T1 -> {fset T2})
       (p1 : finmempred P1 A1) (p2 : forall x : T1, finmempred (P2 x) (A2 x))
   of phantom (mem_pred T1) p1 & phantom (T1 -> mem_pred T2) p2 =>
  seq_fset (flatten [seq [seq f x y | y <- enum_fset (A2 x)] | x <- enum_fset A1])).

Module Type ImfsetSig.
Parameter imfset : forall (T K : choiceType) (f : T -> K) (P : pred T) (A : {fset T})
  (p : finmempred P A), phantom (mem_pred T) p -> {fset K}.
Parameter imfset2 : forall (T1 T2 K : choiceType) (f : T1 -> T2 -> K)
  (P1 : pred T1) (A1 : {fset T1}) (P2 : T1 -> pred T2) (A2 : T1 -> {fset T2})
  (p1 : finmempred P1 A1) (p2 : forall x : T1, finmempred (P2 x) (A2 x)),
  phantom (mem_pred T1) p1 -> phantom (T1 -> mem_pred T2) p2 -> {fset K}.
Axiom imfsetE : imfset = imfset_def.
Axiom imfset2E : imfset2 = imfset2_def.
End ImfsetSig.

Module Imfset : ImfsetSig.
Definition imfset := imfset_def.
Definition imfset2 := imfset2_def.
Lemma imfsetE : imfset = imfset_def. Proof. by []. Qed.
Lemma imfset2E : imfset2 = imfset2_def. Proof. by []. Qed.
End Imfset.

Notation imfset f p := (Imfset.imfset f (Phantom _ (pred_of_finmempred p))).
Notation imfset2 f p q := (Imfset.imfset2 f (Phantom _ (pred_of_finmempred p))
                                         (Phantom _ (fun x => (pred_of_finmempred (q x))))).
Canonical imfset_unlock := Unlockable Imfset.imfsetE.
Canonical imfset2_unlock := Unlockable Imfset.imfset2E.

Notation "A `=` B" := (A = B :> {fset _})
  (at level 70, no associativity, only parsing) : fset_scope.
Notation "A `<>` B" := (A <> B :> {fset _})
  (at level 70, no associativity, only parsing) : fset_scope.
Notation "A `==` B" := (A == B :> {fset _})
  (at level 70, no associativity, only parsing) : fset_scope.
Notation "A `!=` B" := (A != B :> {fset _})
  (at level 70, no associativity, only parsing) : fset_scope.
Notation "A `=P` B" := (A =P B :> {fset _})
  (at level 70, no associativity, only parsing) : fset_scope.

Notation "f @` A" := (Imfset.imfset f (Phantom _ (mem A)))
  (at level 24) : fset_scope.
Notation "f @2` ( A , B )" := (Imfset.imfset2 f (Phantom _ (mem A)) (Phantom _ (fun _ => (mem B))))
  (at level 24, format "f  @2`  ( A ,  B )") : fset_scope.

Notation "[ 'fset' E | x : T 'in' A ]" :=
  ((fun x : T => E) @` A)
  (at level 0, E, x at level 99, only parsing) : fset_scope.
Notation "[ 'fset' E | x 'in' A ]" := [fset E | x : _ in A]
  (at level 0, E, x at level 99,
   format "[ '[hv' 'fset'  E '/ '  |  x  'in'  A ] ']'") : fset_scope.
Notation "[ 'fset' E | x : A ]" := [fset E | x : _ in {: A} ]
  (at level 0, E, x at level 99,
   format "[ '[hv' 'fset'  E '/ '  |  x  :  A ] ']'") : fset_scope.
Notation "[ 'fset'  x  :  T  'in'  A ]" := [fset (x : T) | x in A]
  (at level 0, x at level 99, only parsing) : fset_scope.
Notation "[ 'fset'  x  :  T  'in'  A  |  P ]" :=
  [fset (x : T) | x in [pred x in A | P]]
  (at level 0, x at level 99, only parsing) : fset_scope.
Notation "[ 'fset' x 'in' A | P ]" := [fset x : _ in A | P]
  (at level 0, x at level 99, format "[ 'fset'  x  'in'  A  |  P ]") : fset_scope.
Notation "[ 'fset' x 'in' A ]" := [fset x : _ in A ]
  (at level 0, x at level 99, format "[ 'fset'  x  'in'  A ]") : fset_scope.
Notation "[ 'fset' x : T | P ]" := [fset x in {: T} | P]
  (at level 0, x at level 99, format "[ 'fset'  x  :  T  |  P ]") : fset_scope.
Notation "[ 'fset' x : T | P & Q ]" := [fset x : T | P && Q]
  (at level 0, x at level 99, format "[ 'fset'  x  :  T  |  P  &  Q ]") : fset_scope.
Notation "[ 'fset'  x  :  T  'in' A  |  P  &  Q ]" := [fset x : T in A | P && Q]
  (at level 0, x at level 99, only parsing) : fset_scope.
Notation "[ 'fset' x 'in' A | P & Q ]" := [fset x in A | P && Q]
  (at level 0, x at level 99,
   format "[ 'fset'  x  'in'  A  |  P  &  Q ]") : fset_scope.

Section Ops.

Context {K K': choiceType}.
Implicit Types (a b c : K) (A B C D : {fset K}) (E : {fset K'}) (s : seq K).

Definition fset0 : {fset K} :=
  @mkFinSet K [::] (introT eqP (@sort_keys_nil K)).

Definition fset1U a A : {fset K} := seq_fset (a :: enum_fset A).

Definition fset1 a : {fset K} := seq_fset [:: a].

Definition fsetU A B := seq_fset (enum_fset A ++ enum_fset B).

Definition fsetI A B := [fset x in A | x \in B].

Definition fsetD A B := [fset x in A | x \notin B].

Definition fsetM A E := seq_fset
  [seq (x, y) | x <- enum_fset A, y <- enum_fset E].

Definition fsubset A B := fsetI A B == A.

Definition fproper A B := fsubset A B && ~~ fsubset B A.

Definition fdisjoint A B := (fsetI A B == fset0).

End Ops.

Notation "[ 'fset' a ]" := (fset1 a)
  (at level 0, a at level 99, format "[ 'fset'  a ]") : fset_scope.
Notation "[ 'fset' a : T ]" := [fset (a : T)]
  (at level 0, a at level 99, format "[ 'fset'  a   :  T ]") : fset_scope.
Notation "A `|` B" := (fsetU A B) : fset_scope.
Notation "a |` A" := ([fset a] `|` A) : fset_scope.

(* This is left-associative due to historical limitations of the .. Notation. *)
Notation "[ 'fset' a1 ; a2 ; .. ; an ]" := (fsetU .. (a1 |` [fset a2]) .. [fset an])
  (at level 0, a1 at level 99,
   format "[ 'fset'  a1 ;  a2 ;  .. ;  an ]") : fset_scope.
Notation "A `&` B" := (fsetI A B) : fset_scope.
Notation "A `*` B" := (fsetM A B) : fset_scope.
Notation "A `\` B" := (fsetD A B) : fset_scope.
Notation "A `\ a" := (A `\` [fset a]) : fset_scope.

Notation "A `<=` B" := (fsubset A B)
  (at level 70, no associativity) : fset_scope.

Notation "A `<` B" := (fproper A B)
  (at level 70, no associativity) : fset_scope.

Notation "[ 'disjoint' A & B ]" := (fdisjoint A B) : fset_scope.


(* Comprehensions *)
Notation "[ 'fset' E | x 'in' A & P ]" := [fset E | x in [pred x in A | P]]
  (at level 0, E, x at level 99,
   format "[ '[hv' 'fset'  E '/ '  |  x  'in'  A '/ '  &  P ] ']'") : fset_scope.
Notation "[ 'fset' E | x : A & P ]" := [fset E | x in {: A} & P]
  (at level 0, E, x at level 99,
   format "[ '[hv' 'fset'  E '/ '  |  x  :  A '/ '  &  P ] ']'") : fset_scope.
Notation "[ 'fset' E | x 'in' A , y 'in' B ]" :=
  (Imfset.imfset2 (fun x y => E) (Phantom _ (mem A)) (Phantom _ (fun x => (mem B))))
  (at level 0, E, x, y at level 99, format
   "[ '[hv' 'fset'  E '/ '  |  x  'in'  A , '/   '  y  'in'  B ] ']'"
  ) : fset_scope.
Notation "[ 'fset' E | x : A , y 'in' B ]" := [fset E | x in {: A}, y in B]
  (at level 0, E, x, y at level 99, format
   "[ '[hv' 'fset'  E '/ '  |  x  :  A , '/   '  y  'in'  B ] ']'"
  ) : fset_scope.
Notation "[ 'fset' E | x 'in' A , y : B ]" := [fset E | x in A, y in {: B}]
  (at level 0, E, x, y at level 99, format
   "[ '[hv' 'fset'  E '/ '  |  x  'in'  A , '/   '  y  :  B ] ']'"
  ) : fset_scope.
Notation "[ 'fset' E | x : A , y : B ]" := [fset E | x in {: A}, y in {: B}]
  (at level 0, E, x, y at level 99, format
   "[ '[hv' 'fset'  E '/ '  |  x  :  A , '/   '  y  :  B ] ']'"
  ) : fset_scope.
Notation "[ 'fset' E | x 'in' A , y 'in' B & P ]" :=
  [fset E | x in A, y in [pred y in B | P]]
  (at level 0, E, x, y at level 99, format
   "[ '[hv' 'fset'  E '/ '  |  x  'in'  A , '/   '  y  'in'  B '/ '  &  P ] ']'"
  ) : fset_scope.
Notation "[ 'fset' E | x : A , y 'in' B & P ]" := [fset E | x in {: A}, y in B & P]
  (at level 0, E, x, y at level 99, format
   "[ '[hv' 'fset'  E '/ '  |  x  :  A , '/   '  y  'in'  B  &  P ] ']'"
  ) : fset_scope.
Notation "[ 'fset' E | x 'in' A , y : B & P ]" := [fset E | x in A, y in {: B} & P]
  (at level 0, E, x, y at level 99, format
   "[ '[hv' 'fset'  E '/ '  |  x  'in'  A , '/   '  y  :  B  &  P ] ']'"
  ) : fset_scope.
Notation "[ 'fset' E | x : A , y : B & P ]" := [fset E | x in {: A}, y in {: B} & P]
  (at level 0, E, x, y at level 99, format
   "[ '[hv' 'fset'  E '/ '  |  x  :  A , '/   '  y  :  B  &  P ] ']'"
  ) : fset_scope.

Notation "[ 'fsetval' x 'in' A ]" := [fset val x | x in A]
  (at level 0, x at level 99, format "[ 'fsetval'  x  'in'  A ]") : fset_scope.
Notation "[ 'fsetval' x 'in' A | P ]" := [fset val x | x in A & P]
  (at level 0, x at level 99, format "[ 'fsetval'  x  'in'  A  |  P ]") : fset_scope.
Notation "[ 'fsetval' x 'in' A | P & Q ]" := [fsetval x in A | (P && Q)]
  (at level 0, x at level 99, format "[ 'fsetval'  x  'in'  A  |  P  &  Q ]") : fset_scope.
Notation "[ 'fsetval' x : A ]" := [fset val x | x in {: A}]
  (at level 0, x at level 99, format "[ 'fsetval'  x  :  A ]") : fset_scope.
Notation "[ 'fsetval' x : A | P ]" := [fset val x | x in {: A} & P]
  (at level 0, x at level 99, format "[ 'fsetval'  x  :  A  |  P ]") : fset_scope.
Notation "[ 'fsetval' x : A | P & Q ]" := [fsetval x in {: A} | (P && Q)]
  (at level 0, x at level 99, format "[ 'fsetval'  x  :  A  |  P  &  Q ]") : fset_scope.


(* Print-only variants to work around the Coq pretty-printer K-term kink. *)
Notation "[ 'fse' 't' E | x 'in' A , y 'in' B ]" :=
  ((fun x y => E) @2` (A, B))
  (at level 0, E, x, y at level 99, format
   "[ '[hv' 'fse' 't'  E '/ '  |  x  'in'  A , '/   '  y  'in'  B ] ']'")
   : fset_scope.
Notation "[ 'fse' 't' E | x 'in' A , y 'in' B & P ]" :=
  [fse t E | x in A, y in [fset y in B | P]]
  (at level 0, E, x, y at level 99, format
 "[ '[hv ' 'fse' 't'  E '/'  |  x  'in'  A , '/  '  y  'in'  B '/'  &  P ] ']'"
  ) : fset_scope.

Section imfset.

Variable (K : choiceType).
Implicit Types (A B : {fset K}).

Lemma imfsetP (T : choiceType) (f : T -> K) (P : pred T) (A : {fset T})
  (p : finmempred P A) (k : K) :
  reflect (exists2 x : T, P x & k = f x) (k \in imfset f p).
Proof.
rewrite unlock seq_fsetE /=; apply: (iffP mapP) => [] [x];
by rewrite ?(finmempredE p); exists x => //=; rewrite (finmempredE p).
Qed.

Lemma in_imfset (T : choiceType) (f : T -> K) (P : pred T) (A : {fset T})
  (p : finmempred P A) (x : T) : P x -> f x \in imfset f p.
Proof. by move=> xA; apply/imfsetP; exists x => //=; rewrite finmempredE. Qed.

Lemma imfset_rec (T : choiceType) (f : T -> K) (D : pred T) (A : {fset T})
  (p : finmempred D A) (P : imfset f p -> Prop) :
  (forall (x : T) (Dx : D x), P [` in_imfset f p Dx ]) -> forall k, P k.
Proof.
move=> PP v; have /imfsetP [k Dk vv_eq] := valP v.
pose vP := in_imfset f p Dk; suff -> : P v = P [` vP] by apply: PP.
by congr P; apply/val_inj => /=; rewrite vv_eq.
Qed.

Lemma mem_imfset (T : choiceType) (f : T -> K) (P : pred T) (A : {fset T}) (p : finmempred P A) :
 injective f -> forall (x : T), (f x \in imfset f p) = (P x).
Proof. by move=> f_inj k; rewrite unlock seq_fsetE mem_map // (finmempredE p). Qed.

Lemma imfset2P (T1 T2 : finType) (f : T1 -> T2 -> K)
      (D1 : pred T1) (D2 : T1 -> pred T2) (A1 : {fset T1}) (A2 : T1 -> {fset T2})
      (p1 : finmempred D1 A1) (p2 : forall x : T1, finmempred (D2 x) (A2 x)) (k : K) :
  reflect (exists2 x : T1, D1 x
         & exists2 y : T2, D2 x y & k = f x y)
          (k \in imfset2 f p1 p2).
Proof.
rewrite unlock !seq_fsetE.
apply: (iffP flatten_mapP) => [[x xD1 /mapP [y yD2]]|[x xD1 [y yD2]]] ->.
  rewrite !(finmempredE p1, finmempredE (p2 _)) in xD1 yD2;
  by exists x => //; exists y.
exists x; rewrite ?(finmempredE p1) //; apply/mapP.
by exists y; rewrite ?(finmempredE (p2 _)).
Qed.

Lemma in_imfset2 (T1 T2 : finType) (f : T1 -> T2 -> K)
      (D1 : pred T1) (D2 : T1 -> pred T2) (A1 : {fset T1}) (A2 : T1 -> {fset T2})
      (p1 : finmempred D1 A1) (p2 : forall x : T1, finmempred (D2 x) (A2 x)) (k : K)
      (x : T1) (y : T2) :
   x \in D1 -> y \in D2 x -> f x y \in imfset2 f p1 p2.
Proof. by move=> xD1 yD2; apply/imfset2P; exists x => //; exists y. Qed.

End imfset.

Section imfset2.

Variable (K : choiceType).
Implicit Types (A B : {fset K}).

Lemma in_fset (X : pred K) A (p : finmempred X A) (k : K) :
  (k \in imfset id p) = X k.
Proof. by rewrite mem_imfset; apply: inj_id. Qed.

Lemma val_in_fset A (X : pred A) (Y : {fset A}) (p : finmempred X Y) (k : A) :
  (val k \in imfset val p) = (k \in p).
Proof. by rewrite mem_imfset ?in_finmempred //; exact: val_inj. Qed.

Lemma in_fset_val A (X : pred A) (Y : {fset A}) (p : finmempred X Y) (k : K) :
  (k \in imfset val p) = if insub k is Some a then a \in p else false.
Proof.
have [a _ <- /=|kNA] := insubP; first by rewrite val_in_fset.
by apply/imfsetP => [] [a _ k_def]; move: kNA; rewrite k_def [_ \in _]valP.
Qed.

Lemma in_fset_valT A (X : pred A) (Y : {fset A}) (p : finmempred X Y) (k : K) (kA : k \in A) :
  (k \in imfset val p) = X [` kA].
Proof. by rewrite in_fset_val insubT in_finmempred. Qed.

Lemma in_fset_valP A (X : pred A) (Y : {fset A}) (p : finmempred X Y) (k : K) :
  reflect {kA : k \in A & X [` kA]} (k \in imfset val p).
Proof.
have [kX|kNX] := boolP (k \in imfset val p); constructor; last first.
  by move=> [kA]; move: kNX; rewrite in_fset_valT => /negPf->.
move: kX; rewrite in_fset_val; case: insubP => [[u uP] _ <- Xu|//]; exists uP.
by rewrite in_finmempred in Xu.
Qed.

Lemma in_fset_valF A (X : pred A) (Y : {fset A}) (p : finmempred X Y) (k : K) : k \notin A ->
  (k \in imfset val p) = false.
Proof. by apply: contraNF => /in_fset_valP []. Qed.

End imfset2.

Section Theory.

Variables (K K': choiceType).
Implicit Types (a b x : K) (A B C D : {fset K}) (E : {fset K'})
         (pA pB pC : pred K) (s : seq K).

Lemma fsetP {A B} : A =i B <-> A = B.
Proof. by split=> [eqAB|-> //]; apply/val_inj/canonical_eq_keys => //= a. Qed.

CoInductive in_fset_spec (A : {fset K}) (x : K) : K -> bool -> Prop :=
 | InFset (u : A) & x = val u : in_fset_spec A x (val u) true
 | OutFset of x \notin A : in_fset_spec A x x false.

Lemma in_fsetP A x : in_fset_spec A x x (x \in A).
Proof.
have [xA|xNA] := boolP (x \in A); last by constructor.
by have {2}-> : x = val [` xA] by []; constructor.
Qed.

Lemma fset_eqP {A B} : reflect (A =i B) (A == B).
Proof. exact: (equivP eqP (iff_sym fsetP)). Qed.

Lemma in_fset0 x : x \in fset0 = false. Proof. by []. Qed.

Lemma in_fset1U a' A a : (a \in a' |` A) = (a == a') || (a \in A).
Proof. by rewrite !(seq_fsetE, in_cons, mem_cat, orbF). Qed.

Lemma in_fset1 a' a : a \in [fset a'] = (a == a').
Proof. by rewrite !(seq_fsetE, sort_keysE, in_cons, mem_cat, orbF). Qed.

Lemma in_fsetU A B a : (a \in A `|` B) = (a \in A) || (a \in B).
Proof. by rewrite !(seq_fsetE, sort_keysE, mem_cat). Qed.

Lemma in_fsetI A B a : (a \in A `&` B) = (a \in A) && (a \in B).
Proof. by rewrite in_fset. Qed.

Lemma in_fsetD A B a : (a \in A `\` B) = (a \notin B) && (a \in A).
Proof. by rewrite in_fset andbC. Qed.

Lemma in_fsetD1 A b a : (a \in A `\ b) = (a != b) && (a \in A).
Proof. by rewrite in_fsetD in_fset1. Qed.

Lemma in_fsetM A E (u : K * K') : (u \in A `*` E) = (u.1 \in A) && (u.2 \in E).
Proof.
rewrite seq_fsetE; apply/allpairsP/idP => [[[/= a b] [aA bB -> /=]]|].
  by rewrite aA bB.
by case: u => a b /= /andP [aA bB]; exists (a, b); rewrite aA bB.
Qed.

Definition in_fsetE :=
  (in_fset, val_in_fset, in_fset0, in_fset1,
   in_fsetU, in_fsetI, in_fsetD, in_fsetM,
   in_fset1U, in_fsetD1, in_finset).

Let inE := (inE, in_fsetE).

Lemma fsetIC (A B : {fset K}) : A `&` B = B `&` A.
Proof. by apply/fsetP => a; rewrite !inE andbC. Qed.

Lemma fsetUC (A B : {fset K}) : A `|` B = B `|` A.
Proof. by apply/fsetP => a; rewrite !inE orbC. Qed.

Lemma fset0I A : fset0 `&` A = fset0.
Proof. by apply/fsetP => x; rewrite !inE andFb. Qed.

Lemma fsetI0 A : A `&` fset0 = fset0.
Proof. by rewrite fsetIC fset0I. Qed.

Lemma fsetIA A B C : A `&` (B `&` C) = A `&` B `&` C.
Proof. by apply/fsetP=> x; rewrite !inE andbA. Qed.

Lemma fsetICA A B C : A `&` (B `&` C) = B `&` (A `&` C).
Proof. by rewrite !fsetIA (fsetIC A). Qed.

Lemma fsetIAC A B C : A `&` B `&` C = A `&` C `&` B.
Proof. by rewrite -!fsetIA (fsetIC B). Qed.

Lemma fsetIACA A B C D : (A `&` B) `&` (C `&` D) = (A `&` C) `&` (B `&` D).
Proof. by rewrite -!fsetIA (fsetICA B). Qed.

Lemma fsetIid A : A `&` A = A.
Proof. by apply/fsetP=> x; rewrite inE andbb. Qed.

Lemma fsetIIl A B C : A `&` B `&` C = (A `&` C) `&` (B `&` C).
Proof. by rewrite fsetIA !(fsetIAC _ C) -(fsetIA _ C) fsetIid. Qed.

Lemma fsetIIr A B C : A `&` (B `&` C) = (A `&` B) `&` (A `&` C).
Proof. by rewrite !(fsetIC A) fsetIIl. Qed.

Lemma fsetUA A B C : A `|` (B `|` C) = A `|` B `|` C.
Proof. by apply/fsetP => x; rewrite !inE orbA. Qed.

Lemma fsetUCA A B C : A `|` (B `|` C) = B `|` (A `|` C).
Proof. by rewrite !fsetUA (fsetUC B). Qed.

Lemma fsetUAC A B C : A `|` B `|` C = A `|` C `|` B.
Proof. by rewrite -!fsetUA (fsetUC B). Qed.

Lemma fsetUACA A B C D : (A `|` B) `|` (C `|` D) = (A `|` C) `|` (B `|` D).
Proof. by rewrite -!fsetUA (fsetUCA B). Qed.

Lemma fsetUid A : A `|` A = A.
Proof. by apply/fsetP=> x; rewrite inE orbb. Qed.

Lemma fsetUUl A B C : A `|` B `|` C = (A `|` C) `|` (B `|` C).
Proof. by rewrite fsetUA !(fsetUAC _ C) -(fsetUA _ C) fsetUid. Qed.

Lemma fsetUUr A B C : A `|` (B `|` C) = (A `|` B) `|` (A `|` C).
Proof. by rewrite !(fsetUC A) fsetUUl. Qed.

(* distribute /cancel *)

Lemma fsetIUr A B C : A `&` (B `|` C) = (A `&` B) `|` (A `&` C).
Proof. by apply/fsetP=> x; rewrite !inE andb_orr. Qed.

Lemma fsetIUl A B C : (A `|` B) `&` C = (A `&` C) `|` (B `&` C).
Proof. by apply/fsetP=> x; rewrite !inE andb_orl. Qed.

Lemma fsetUIr A B C : A `|` (B `&` C) = (A `|` B) `&` (A `|` C).
Proof. by apply/fsetP=> x; rewrite !inE orb_andr. Qed.

Lemma fsetUIl A B C : (A `&` B) `|` C = (A `|` C) `&` (B `|` C).
Proof. by apply/fsetP=> x; rewrite !inE orb_andl. Qed.

Lemma fsetUKC A B : (A `|` B) `&` A = A.
Proof. by apply/fsetP=> x; rewrite !inE orbK. Qed.

Lemma fsetUK A B : (B `|` A) `&` A = A.
Proof. by rewrite fsetUC fsetUKC. Qed.

Lemma fsetKUC A B : A `&` (B `|` A) = A.
Proof. by rewrite fsetIC fsetUK. Qed.

Lemma fsetKU A B : A `&` (A `|` B) = A.
Proof. by rewrite fsetIC fsetUKC. Qed.

Lemma fsetIKC A B : (A `&` B) `|` A = A.
Proof. by apply/fsetP=> x; rewrite !inE andbK. Qed.

Lemma fsetIK A B : (B `&` A) `|` A = A.
Proof. by rewrite fsetIC fsetIKC. Qed.

Lemma fsetKIC A B : A `|` (B `&` A) = A.
Proof. by rewrite fsetUC fsetIK. Qed.

Lemma fsetKI A B : A `|` (A `&` B) = A.
Proof. by rewrite fsetIC fsetKIC. Qed.

Lemma fsetUKid A B : B `|` A `|` A = B `|` A.
Proof. by rewrite -fsetUA fsetUid. Qed.

Lemma fsetUKidC A B : A `|` B `|` A = A `|` B.
Proof. by rewrite fsetUAC fsetUid. Qed.

Lemma fsetKUid A B : A `|` (A `|` B) = A `|` B.
Proof. by rewrite fsetUA fsetUid. Qed.

Lemma fsetKUidC A B : A `|` (B `|` A) = B `|` A.
Proof. by rewrite fsetUCA fsetUid. Qed.

Lemma fsetIKid A B : B `&` A `&` A = B `&` A.
Proof. by rewrite -fsetIA fsetIid. Qed.

Lemma fsetIKidC A B : A `&` B `&` A = A `&` B.
Proof. by rewrite fsetIAC fsetIid. Qed.

Lemma fsetKIid A B : A `&` (A `&` B) = A `&` B.
Proof. by rewrite fsetIA fsetIid. Qed.

Lemma fsetKIidC A B : A `&` (B `&` A) = B `&` A.
Proof. by rewrite fsetICA fsetIid. Qed.

(* subset *)

Lemma fsubsetP {A B} : reflect {subset A <= B} (A `<=` B).
Proof.
apply: (iffP fset_eqP) => AsubB a; first by rewrite -AsubB inE => /andP[].
by rewrite inE; have [/AsubB|] := boolP (a \in A).
Qed.

Lemma fset_sub_val A (X : pred A) (Y : {fset A}) (p : finmempred X Y) :
   (imfset val p) `<=` A.
Proof. by apply/fsubsetP => k /in_fset_valP []. Qed.

Lemma fset_sub A (P : pred K) : [fset x in A | P x] `<=` A.
Proof. by apply/fsubsetP => k; rewrite inE /= => /andP []. Qed.

Lemma fsetD_eq0 (A B : {fset K}) : (A `\` B == fset0) = (A `<=` B).
Proof.
apply/fset_eqP/fsubsetP => sAB a.
  by move=> aA; have := sAB a; rewrite !inE aA andbT => /negPn.
by rewrite !inE andbC; apply/negP => /andP [/sAB ->].
Qed.

Lemma fsubset_refl A : A `<=` A. Proof. exact/fsubsetP. Qed.
Hint Resolve fsubset_refl.

Definition fincl A B (AsubB : A `<=` B) (a : A) : B :=
  [` (fsubsetP AsubB) _ (valP a)].

Definition fsub B A : {set B} := [set x : B | val x \in A].

Lemma fsubE A B (AsubB : A `<=` B) :
  fsub B A = [set fincl AsubB x | x : A].
Proof.
apply/setP => x; rewrite in_set; apply/idP/imsetP => [|[[a aA] aA' ->]] //.
by move=> xA; exists [` xA]=> //; apply: val_inj.
Qed.

Lemma fincl_fsub A B (AsubB : A `<=` B) (a : A) :
  fincl AsubB a \in fsub B A.
Proof. by rewrite inE /= (valP a). Qed.

Lemma in_fsub B A (b : B) : (b \in fsub B A) = (val b \in A).
Proof. by rewrite inE. Qed.

Lemma subset_fsubE C A B : A `<=` C -> B `<=` C ->
   (fsub C A \subset fsub C B) = (A `<=` B).
Proof.
move=> sAC sBC; apply/subsetP/fsubsetP => sAB a; last first.
  by rewrite !inE => /sAB.
by move=> aA; have := sAB _ (fincl_fsub sAC [` aA]); rewrite inE.
Qed.

Lemma fsubset_trans : transitive (@fsubset K).
Proof. by move=>??? s t ; apply/fsubsetP => a /(fsubsetP s) /(fsubsetP t). Qed.

Lemma subset_fsub A B C : A `<=` B -> B `<=` C ->
  fsub C A \subset fsub C B.
Proof. by move=> sAB sBC; rewrite subset_fsubE // (fsubset_trans sAB). Qed.

Lemma fsetIidPl {A B} : reflect (A `&` B = A) (A `<=` B).
Proof. exact: eqP. Qed.

Lemma fsetIidPr {A B} : reflect (A `&` B = B) (B `<=` A).
Proof. by rewrite fsetIC; apply: fsetIidPl. Qed.

Lemma fsubsetIidl A B : (A `<=` A `&` B) = (A `<=` B).
Proof.
by apply/fsubsetP/fsubsetP=> sAB a aA; have := sAB _ aA; rewrite !inE ?aA.
Qed.

Lemma fsubsetIidr A B : (B `<=` A `&` B) = (B `<=` A).
Proof. by rewrite fsetIC fsubsetIidl. Qed.

Lemma fsetUidPr A B : reflect (A `|` B = B) (A `<=` B).
Proof.
apply: (iffP fsubsetP) => sAB; last by move=> a aA; rewrite -sAB inE aA.
by apply/fsetP => b; rewrite inE; have [/sAB|//] := boolP (_ \in _).
Qed.

Lemma fsetUidPl A B : reflect (A `|` B = A) (B `<=` A).
Proof. by rewrite fsetUC; apply/fsetUidPr. Qed.

Lemma fsubsetUl A B : A `<=` A `|` B.
Proof. by apply/fsubsetP => a; rewrite inE => ->. Qed.
Hint Resolve fsubsetUl.

Lemma fsubsetUr A B : B `<=` A `|` B.
Proof. by rewrite fsetUC. Qed.
Hint Resolve fsubsetUr.

Lemma fsubsetU1 x A : A `<=` x |` A.
Proof. by rewrite fsubsetUr. Qed.
Hint Resolve fsubsetU1.

Lemma fsubsetU A B C : (A `<=` B) || (A `<=` C) -> A `<=` B `|` C.
Proof. by move=> /orP [] /fsubset_trans ->. Qed.

Lemma fincl_inj A B (AsubB : A `<=` B) : injective (fincl AsubB).
Proof. by move=> a b [eq_ab]; apply: val_inj. Qed.
Hint Resolve fincl_inj.

Lemma fsub_inj B : {in [pred A | A `<=` B] &, injective (fsub B)}.
Proof.
move=> A A'; rewrite -!topredE /= => sAB sA'B /setP eqAA'; apply/fsetP => a.
apply/idP/idP => mem_a.
  by have := eqAA' (fincl sAB [` mem_a]); rewrite !inE // => <-.
by have := eqAA' (fincl sA'B [` mem_a]); rewrite !inE // => ->.
Qed.
Hint Resolve fsub_inj.

Lemma eqEfsubset A B : (A == B) = (A `<=` B) && (B `<=` A).
Proof.
apply/eqP/andP => [-> //|[/fsubsetP AB /fsubsetP BA]].
by apply/fsetP=> x; apply/idP/idP=> [/AB|/BA].
Qed.

Lemma subEfproper A B : A `<=` B = (A == B) || (A `<` B).
Proof. by rewrite eqEfsubset -andb_orr orbN andbT. Qed.

Lemma fproper_sub A B : A `<` B -> A `<=` B.
Proof. by rewrite subEfproper orbC => ->. Qed.

Lemma eqVfproper A B : A `<=` B -> A = B \/ A `<` B.
Proof. by rewrite subEfproper => /predU1P. Qed.

Lemma fproperEneq A B : A `<` B = (A != B) && (A `<=` B).
Proof. by rewrite andbC eqEfsubset negb_and andb_orr andbN. Qed.

Lemma fproper_neq A B : A `<` B -> A != B.
Proof. by rewrite fproperEneq; case/andP. Qed.

Lemma eqEfproper A B : (A == B) = (A `<=` B) && ~~ (A `<` B).
Proof. by rewrite negb_and negbK andb_orr andbN eqEfsubset. Qed.

Lemma card_fsub B A : A `<=` B -> #|fsub B A| = #|` A|.
Proof. by move=> sAB; rewrite fsubE card_imset //; apply: fincl_inj. Qed.

Lemma eqEfcard A B : (A == B) = (A `<=` B) &&
  (#|` B| <= #|` A|)%N.
Proof.
rewrite -(inj_in_eq (@fsub_inj (A `|` B))) -?topredE //=.
by rewrite eqEcard !(@subset_fsubE (A `|` B)) ?(@card_fsub (A `|` B)).
Qed.

Lemma fproperEcard A B :
  (A `<` B) = (A `<=` B) && (#|` A| < #|` B|)%N.
Proof. by rewrite fproperEneq ltnNge andbC eqEfcard; case: (A `<=` B). Qed.

Lemma fsubset_leqif_cards A B : A `<=` B -> (#|` A| <= #|` B| ?= iff (A == B))%N.
Proof.
rewrite -!(@card_fsub (A `|` B)) // -(@subset_fsubE (A `|` B)) //.
by move=> /subset_leqif_cards; rewrite (inj_in_eq (@fsub_inj _)) -?topredE /=.
Qed.

Lemma fsub0set A : fset0 `<=` A.
Proof. by apply/fsubsetP=> x; rewrite inE. Qed.
Hint Resolve fsub0set.

Lemma fsubset0 A : (A `<=` fset0) = (A == fset0).
Proof. by rewrite eqEfsubset fsub0set andbT. Qed.

Lemma fproper0 A : (fset0 `<` A) = (A != fset0).
Proof. by rewrite /fproper fsub0set fsubset0. Qed.

Lemma fproperE A B : (A `<` B) = (A `<=` B) && ~~ (B `<=` A).
Proof. by []. Qed.

Lemma fsubEproper A B : (A `<=` B) = (A == B) || (A `<` B).
Proof. by rewrite fproperEneq; case: eqP => //= ->; apply: fsubset_refl. Qed.

Lemma fsubset_leq_card A B : A `<=` B -> (#|` A| <= #|` B|)%N.
Proof. by move=> /fsubset_leqif_cards ->. Qed.

Lemma fproper_ltn_card A B : A `<` B -> (#|` A| < #|` B|)%N.
Proof. by rewrite fproperEcard => /andP []. Qed.

Lemma fsubset_cardP A B : #|` A| = #|` B| ->
  reflect (A =i B) (A `<=` B).
Proof.
move=> eq_cardAB; apply: (iffP idP) => [/eqVfproper [->//|]|/fsetP -> //].
by rewrite fproperEcard eq_cardAB ltnn andbF.
Qed.

Lemma fproper_sub_trans B A C : A `<` B -> B `<=` C -> A `<` C.
Proof.
rewrite !fproperEcard => /andP [sAB lt_AB] sBC.
by rewrite (fsubset_trans sAB) //= (leq_trans lt_AB) // fsubset_leq_card.
Qed.

Lemma fsub_proper_trans B A C :
  A `<=` B -> B `<` C -> A `<` C.
Proof.
rewrite !fproperEcard => sAB /andP [sBC lt_BC].
by rewrite (fsubset_trans sAB) //= (leq_ltn_trans _ lt_BC) // fsubset_leq_card.
Qed.

Lemma fsubset_neq0 A B : A `<=` B -> A != fset0 -> B != fset0.
Proof. by rewrite -!fproper0 => sAB /fproper_sub_trans->. Qed.

(* fsub is a morphism *)

Lemma fsub0 A : fsub A fset0 = set0 :> {set A}.
Proof. by apply/setP => x; rewrite !inE. Qed.

Lemma fsubT A : fsub A A = [set : A].
Proof. by apply/setP => x; rewrite !inE (valP x). Qed.

Lemma fsub1 A a (aA : a \in A) : fsub A [fset a] = [set [` aA]] :> {set A}.
Proof. by apply/setP=> x; rewrite !inE; congr eq_op. Qed.

Lemma fsubU C A B : fsub C (A `|` B) = fsub C A :|: fsub C B.
Proof. by apply/setP => x; rewrite !inE. Qed.

Lemma fsubI C A B : fsub C (A `&` B) = fsub C A :&: fsub C B.
Proof. by apply/setP => x; rewrite !inE. Qed.

Lemma fsubD C A B : fsub C (A `\` B) = fsub C A :\: fsub C B.
Proof. by apply/setP => x; rewrite !inE andbC. Qed.

Lemma fsubD1 C A b (bC : b \in C) : fsub C (A `\ b) = fsub C A :\ [` bC].
Proof. by rewrite fsubD fsub1. Qed.

Lemma fsub_eq0 A B : A `<=` B -> (fsub B A == set0) = (A == fset0).
Proof.
by move=> sAB; rewrite -fsub0 (inj_in_eq (@fsub_inj _)) -?topredE /=.
Qed.

Lemma fset_0Vmem A : (A = fset0) + {x : K | x \in A}.
Proof.
have [|[x mem_x]] := set_0Vmem (fsub A A); last first.
  by right; exists (val x); rewrite inE // in mem_x.
by move=> /eqP; rewrite fsub_eq0 // => /eqP; left.
Qed.

Lemma fset1P x a : reflect (x = a) (x \in [fset a]).
Proof. by rewrite inE; exact: eqP. Qed.

Lemma fset11 x : x \in [fset x].
Proof. by rewrite inE. Qed.

Lemma fset1_inj : injective (@fset1 K).
Proof. by move=> a b eqsab; apply/fset1P; rewrite -eqsab fset11. Qed.

Lemma fset1UP x a B : reflect (x = a \/ x \in B) (x \in a |` B).
Proof. by rewrite !inE; exact: predU1P. Qed.

Lemma fset_cons a s : seq_fset (a :: s) = a |` (seq_fset s).
Proof. by apply/fsetP=> x; rewrite in_fset1U !seq_fsetE. Qed.

Lemma fset1U1 x B : x \in x |` B. Proof. by rewrite !inE eqxx. Qed.

Lemma fset1Ur x a B : x \in B -> x \in a |` B.
Proof. by move=> Bx; rewrite !inE predU1r. Qed.

(* We need separate lemmas for the explicit enumerations since they *)
(* associate on the left.                                           *)
Lemma fsetU1l x A b : x \in A -> x \in A `|` [fset b].
Proof. by move=> Ax; rewrite !inE Ax. Qed.

Lemma fsetU1r A b : b \in A `|` [fset b].
Proof. by rewrite !inE eqxx orbT. Qed.

Lemma fsetD1P x A b : reflect (x != b /\ x \in A) (x \in A `\ b).
Proof. by rewrite !inE; exact: andP. Qed.

Lemma fsetD11 b A : (b \in A `\ b) = false. Proof. by rewrite !inE eqxx. Qed.

Lemma fsetD1K a A : a \in A -> a |` (A `\ a) = A.
Proof.
by move=> Aa; apply/fsetP=> x; rewrite !inE; case: eqP => // ->.
Qed.

Lemma fsetU1K a B : a \notin B -> (a |` B) `\ a = B.
Proof.
by move/negPf=> nBa; apply/fsetP=> x; rewrite !inE; case: eqP => // ->.
Qed.

Lemma fset2P x a b : reflect (x = a \/ x = b) (x \in [fset a; b]).
Proof.
rewrite !inE; apply: (iffP orP) => [] [] /eqP ->. 
      by left. 
    by right. 
  by left. 
by right. 
Qed.

Lemma in_fset2 x a b : (x \in [fset a; b]) = (x == a) || (x == b).
Proof. by rewrite !inE. Qed.

Lemma fset21 a b : a \in [fset a; b]. Proof. by rewrite fset1U1. Qed.

Lemma fset22 a b : b \in [fset a; b]. Proof. by rewrite in_fset2 eqxx orbT. Qed.

Lemma fsetUP x A B : reflect (x \in A \/ x \in B) (x \in A `|` B).
Proof. by rewrite !inE; exact: orP. Qed.

Lemma fsetULVR x A B : x \in A `|` B -> (x \in A) + (x \in B).
Proof. by rewrite inE; case: (x \in A); [left|right]. Qed.

Lemma fsetUS A B C : A `<=` B -> C `|` A `<=` C `|` B.
Proof.
move=> sAB; apply/fsubsetP=> x; rewrite !inE.
by case: (x \in C) => //; exact: (fsubsetP sAB).
Qed.

Lemma fsetSU A B C : A `<=` B -> A `|` C `<=` B `|` C.
Proof. by move=> sAB; rewrite -!(fsetUC C) fsetUS. Qed.

Lemma fsetUSS A B C D : A `<=` C -> B `<=` D -> A `|` B `<=` C `|` D.
Proof. by move=> /(fsetSU B) /fsubset_trans sAC /(fsetUS C)/sAC. Qed.

Lemma fset0U A : fset0 `|` A = A.
Proof. by apply/fsetP => x; rewrite !inE orFb. Qed.

Lemma fsetU0 A : A `|` fset0 = A.
Proof. by rewrite fsetUC fset0U. Qed.

(* intersection *)

Lemma fsetIP x A B : reflect (x \in A /\ x \in B) (x \in A `&` B).
Proof. by rewrite inE; apply: andP. Qed.

Lemma fsetIS A B C : A `<=` B -> C `&` A `<=` C `&` B.
Proof.
move=> sAB; apply/fsubsetP=> x; rewrite !inE.
by case: (x \in C) => //; exact: (fsubsetP sAB).
Qed.

Lemma fsetSI A B C : A `<=` B -> A `&` C `<=` B `&` C.
Proof. by move=> sAB; rewrite -!(fsetIC C) fsetIS. Qed.

Lemma fsetISS A B C D : A `<=` C -> B `<=` D -> A `&` B `<=` C `&` D.
Proof. by move=> /(fsetSI B) /fsubset_trans sAC /(fsetIS C) /sAC. Qed.

(* difference *)

Lemma fsetDP A B x : reflect (x \in A /\ x \notin B) (x \in A `\` B).
Proof. by rewrite inE andbC; apply: andP. Qed.

Lemma fsetSD A B C : A `<=` B -> A `\` C `<=` B `\` C.
Proof.
move=> sAB; apply/fsubsetP=> x; rewrite !inE.
by case: (x \in C) => //; exact: (fsubsetP sAB).
Qed.

Lemma fsetDS A B C : A `<=` B -> C `\` B `<=` C `\` A.
Proof.
move=> sAB; apply/fsubsetP=> x; rewrite !inE ![_ && (_ \in _)]andbC.
by case: (x \in C) => //; apply: contra; exact: (fsubsetP sAB).
Qed.

Lemma fsetDSS A B C D : A `<=` C -> D `<=` B -> A `\` B `<=` C `\` D.
Proof. by move=> /(fsetSD B) /fsubset_trans sAC /(fsetDS C) /sAC. Qed.

Lemma fsetD0 A : A `\` fset0 = A.
Proof. by apply/fsetP=> x; rewrite !inE. Qed.

Lemma fset0D A : fset0 `\` A = fset0.
Proof. by apply/fsetP=> x; rewrite !inE andbF. Qed.

Lemma fsetDv A : A `\` A = fset0.
Proof. by apply/fsetP=> x; rewrite !inE andNb. Qed.

Lemma fsetID A B : A `&` B `|` A `\` B = A.
Proof. by apply/fsetP=> x; rewrite !inE; do ?case: (_ \in _). Qed.

Lemma fsetDUl A B C : (A `|` B) `\` C = (A `\` C) `|` (B `\` C).
Proof. by apply/fsetP=> x; rewrite !inE; do ?case: (_ \in _). Qed.

Lemma fsetDUr A B C : A `\` (B `|` C) = (A `\` B) `&` (A `\` C).
Proof. by apply/fsetP=> x; rewrite !inE; do ?case: (_ \in _). Qed.

Lemma fsetDIl A B C : (A `&` B) `\` C = (A `\` C) `&` (B `\` C).
Proof. by apply/fsetP=> x; rewrite !inE; do ?case: (_ \in _). Qed.

Lemma fsetIDA A B C : A `&` (B `\` C) = (A `&` B) `\` C.
Proof. by apply/fsetP=> x; rewrite !inE; do ?case: (_ \in _). Qed.

Lemma fsetIDAC A B C : (A `\` B) `&` C = (A `&` C) `\` B.
Proof. by apply/fsetP=> x; rewrite !inE; do ?case: (_ \in _). Qed.

Lemma fsetDIr A B C : A `\` (B `&` C) = (A `\` B) `|` (A `\` C).
Proof. by apply/fsetP=> x; rewrite !inE; do ?case: (_ \in _). Qed.

Lemma fsetDDl A B C : (A `\` B) `\` C = A `\` (B `|` C).
Proof. by apply/fsetP=> x; rewrite !inE; do ?case: (_ \in _). Qed.

Lemma fsetDDr A B C : A `\` (B `\` C) = (A `\` B) `|` (A `&` C).
Proof. by apply/fsetP=> x; rewrite !inE; do ?case: (_ \in _). Qed.

Lemma fsetUDl (A B C : {fset K}) : A `|` (B `\` C) = (A `|` B) `\` (C `\` A).
Proof. by apply/fsetP=> x; rewrite !inE; do ?case: (_ \in _). Qed.

Lemma fsetUDr (A B C : {fset K}) : (A `\` B) `|` C = (A `|` C) `\` (B `\` C).
Proof. by apply/fsetP=> x; rewrite !inE; do ?case: (_ \in _). Qed.

(* other inclusions *)

Lemma fsubsetIl A B : A `&` B `<=` A.
Proof. by apply/fsubsetP=> x; rewrite inE => /andP []. Qed.

Lemma fsubsetIr A B : A `&` B `<=` B.
Proof. by apply/fsubsetP=> x; rewrite inE => /andP []. Qed.

Lemma fsubsetDl A B : A `\` B `<=` A.
Proof. by apply/fsubsetP=> x; rewrite inE => /andP []. Qed.

Lemma fsubD1set A x : A `\ x `<=` A.
Proof. by rewrite fsubsetDl. Qed.

Hint Resolve fsubsetIl fsubsetIr fsubsetDl fsubD1set.

(* cardinal lemmas for fsets *)

Lemma cardfs0 : #|` @fset0 K| = 0.
Proof. by rewrite -(@card_fsub fset0) // fsub0 cards0. Qed.

Lemma cardfs_eq0 A : (#|` A| == 0) = (A == fset0).
Proof. by rewrite -(@card_fsub A) // cards_eq0 fsub_eq0. Qed.

Lemma cardfs0_eq A : #|` A| = 0 -> A = fset0.
Proof. by move=> /eqP; rewrite cardfs_eq0 => /eqP. Qed.

Lemma fset0Pn A : reflect (exists x, x \in A) (A != fset0).
Proof.
rewrite -cardfs_eq0; apply: (equivP existsP).
by split=> [] [a aP]; [exists (val a); apply: valP|exists [` aP]].
Qed.

Lemma cardfs_gt0 A : (0 < #|` A|)%N = (A != fset0).
Proof. by rewrite lt0n cardfs_eq0. Qed.

Lemma cardfsE s : #|` seq_fset s| = size (undup s).
Proof.
rewrite cardT enumT unlock /= undup_id ?pmap_sub_uniq ?[seq_fset]unlock //=.
by rewrite size_pmap_sub (@eq_in_count _ _ predT) ?count_predT ?size_sort_keys.
Qed.

Lemma cardfs1 x : #|` [fset x]| = 1.
Proof. by rewrite cardfsE undup_id. Qed.

Lemma cardfsUI A B : #|` A `|` B| + #|` A `&` B| = #|` A| + #|` B|.
Proof.
rewrite -!(@card_fsub (A `|` B)) ?(fsubset_trans (fsubsetIl _ _)) //.
by rewrite fsubU fsubI cardsUI.
Qed.

Lemma cardfsU A B : #|` A `|` B| = (#|` A| + #|` B| - #|` A `&` B|)%N.
Proof. by rewrite -cardfsUI addnK. Qed.

Lemma cardfsI A B : #|` A `&` B| = (#|` A| + #|` B| - #|` A `|` B|)%N.
Proof. by rewrite  -cardfsUI addKn. Qed.

Lemma cardfsID B A : #|` A `&` B| + #|` A `\` B| = #|` A|.
Proof. by rewrite -!(@card_fsub A) // fsubI fsubD cardsID. Qed.

Lemma cardfsD A B : #|` A `\` B| = (#|` A| - #|` A `&` B|)%N.
Proof. by rewrite -(cardfsID B A) addKn. Qed.

Lemma mem_fset1U a A : a \in A -> a |` A = A.
Proof.
move=> aA; apply/fsetP => x; rewrite !inE orbC.
by have [//|/=] := boolP (_ \in A); apply: contraNF => /eqP ->.
Qed.

Lemma mem_fsetD1 a A : a \notin A -> A `\ a = A.
Proof.
move=> aA; apply/fsetP => x; rewrite !inE andbC.
by have [/= xA|//] := boolP (_ \in A); apply: contraNneq aA => <-.
Qed.

Lemma fsetI1 a A : A `&` [fset a] = if a \in A then [fset a] else fset0.
Proof.
apply/fsetP => x; rewrite (fun_if (fun X => _ \in X)) !inE.
by have [[->|?] []] := (altP (x =P a), boolP (a \in A)); rewrite ?andbF.
Qed.

Lemma cardfsU1 a A : #|` a |` A| = (a \notin A) + #|` A|.
Proof.
have [aA|aNA] := boolP (a \in A); first by rewrite mem_fset1U.
rewrite cardfsU -addnBA ?fsubset_leq_card // fsetIC -cardfsD.
by rewrite mem_fsetD1 // cardfs1.
Qed.

Lemma cardfs2 a b : #|` [fset a; b]| = (a != b).+1.
Proof. by rewrite !cardfsU1 cardfs1 addn1 seq_fsetE in_cons orbF. Qed.

Lemma cardfsD1 a A : #|` A| = (a \in A) + #|` A `\ a|.
Proof.
rewrite -(cardfsID [fset a]) fsetI1 (fun_if (fun A => #|` A|)).
by rewrite cardfs0 cardfs1; case: (_ \in _).
Qed.

(* other inclusions *)

Lemma fsub1set A x : ([fset x] `<=` A) = (x \in A).
Proof.
rewrite -(@subset_fsubE (x |` A)) // fsub1 ?fset1U1 // => xxA.
by rewrite sub1set inE.
Qed.

Lemma cardfs1P A : reflect (exists x, A = [fset x]) (#|` A| == 1).
Proof.
apply: (iffP idP) => [|[x ->]]; last by rewrite cardfs1.
rewrite eq_sym eqn_leq cardfs_gt0=> /andP[/fset0Pn[x Ax] leA1].
by exists x; apply/eqP; rewrite eq_sym eqEfcard fsub1set cardfs1 leA1 Ax.
Qed.

Lemma fsubset1 A x : (A `<=` [fset x]) = (A == [fset x]) || (A == fset0).
Proof.
rewrite eqEfcard cardfs1 -cardfs_eq0 orbC andbC.
by case: posnP => // A0; rewrite (cardfs0_eq A0) fsub0set.
Qed.

Implicit Arguments fsetIidPl [A B].

Lemma cardfsDS A B : B `<=` A -> #|` A `\` B| = (#|` A| - #|` B|)%N.
Proof. by rewrite cardfsD => /fsetIidPr->. Qed.

Lemma fsubIset A B C : (B `<=` A) || (C `<=` A) -> (B `&` C `<=` A).
Proof. by case/orP; apply: fsubset_trans; rewrite (fsubsetIl, fsubsetIr). Qed.

Lemma fsubsetI A B C : (A `<=` B `&` C) = (A `<=` B) && (A `<=` C).
Proof.
rewrite !(sameP fsetIidPl eqP) fsetIA; have [-> //| ] := altP (A `&` B =P A).
by apply: contraNF => /eqP <-; rewrite -fsetIA -fsetIIl fsetIAC.
Qed.

Lemma fsubsetIP A B C : reflect (A `<=` B /\ A `<=` C) (A `<=` B `&` C).
Proof. by rewrite fsubsetI; exact: andP. Qed.

Lemma fsubUset A B C : (B `|` C `<=` A) = (B `<=` A) && (C `<=` A).
Proof.
apply/idP/idP => [subA|/andP [AB CA]]; last by rewrite -[A]fsetUid fsetUSS.
by rewrite !(fsubset_trans _ subA).
Qed.

Lemma fsubUsetP A B C : reflect (A `<=` C /\ B `<=` C) (A `|` B `<=` C).
Proof. by rewrite fsubUset; exact: andP. Qed.

Lemma fsubDset A B C : (A `\` B `<=` C) = (A `<=` B `|` C).
Proof.
apply/fsubsetP/fsubsetP=> sABC x; rewrite !inE.
  by case Bx: (x \in B) => // Ax; rewrite sABC ?in_fsetD ?Bx.
by case Bx: (x \in B) => //; move/sABC; rewrite inE Bx.
Qed.

Lemma fsetU_eq0 A B : (A `|` B == fset0) = (A == fset0) && (B == fset0).
Proof. by rewrite -!fsubset0 fsubUset. Qed.

Lemma fsubsetD1 A B x : (A `<=` B `\ x) = (A `<=` B) && (x \notin A).
Proof.
do !rewrite -(@subset_fsubE (x |` A `|` B)) ?fsubDset ?fsetUA // 1?fsetUAC //.
rewrite fsubD1 => [|mem_x]; first by rewrite -fsetUA fset1U1.
by rewrite subsetD1 // inE.
Qed.

Lemma fsubsetD1P A B x : reflect (A `<=` B /\ x \notin A) (A `<=` B `\ x).
Proof. by rewrite fsubsetD1; exact: andP. Qed.

Lemma fsubsetPn A B : reflect (exists2 x, x \in A & x \notin B) (~~ (A `<=` B)).
Proof.
 rewrite -fsetD_eq0; apply: (iffP (fset0Pn _)) => [[x]|[x xA xNB]].
  by rewrite inE => /andP[]; exists x.
by exists x; rewrite inE xA xNB.
Qed.

Lemma fproperD1 A x : x \in A -> A `\ x `<` A.
Proof.
move=> Ax; rewrite fproperE fsubsetDl; apply/fsubsetPn; exists x=> //.
by rewrite in_fsetD1 Ax eqxx.
Qed.

Lemma fproperIr A B : ~~ (B `<=` A) -> A `&` B `<` B.
Proof. by move=> nsAB; rewrite fproperE fsubsetIr fsubsetI negb_and nsAB. Qed.

Lemma fproperIl A B : ~~ (A `<=` B) -> A `&` B `<` A.
Proof. by move=> nsBA; rewrite fproperE fsubsetIl fsubsetI negb_and nsBA orbT. Qed.

Lemma fproperUr A B : ~~ (A `<=` B) ->  B `<` A `|` B.
Proof. by rewrite fproperE fsubsetUr fsubUset fsubset_refl /= andbT. Qed.

Lemma fproperUl A B : ~~ (B `<=` A) ->  A `<` A `|` B.
Proof. by move=> not_sBA; rewrite fsetUC fproperUr. Qed.

Lemma fproper1set A x : ([fset x] `<` A) -> (x \in A).
Proof. by move/fproper_sub; rewrite fsub1set. Qed.

Lemma fproperIset A B C : (B `<` A) || (C `<` A) -> (B `&` C `<` A).
Proof. by case/orP; apply: fsub_proper_trans; rewrite (fsubsetIl, fsubsetIr). Qed.

Lemma fproperI A B C : (A `<` B `&` C) -> (A `<` B) && (A `<` C).
Proof.
move=> pAI; apply/andP.
by split; apply: (fproper_sub_trans pAI); rewrite (fsubsetIl, fsubsetIr).
Qed.

Lemma fproperU A B C : (B `|` C `<` A) -> (B `<` A) && (C `<` A).
Proof.
move=> pUA; apply/andP.
by split; apply: fsub_proper_trans pUA; rewrite (fsubsetUr, fsubsetUl).
Qed.

Lemma fsetI_eq0 A B : (A `&` B == fset0) = [disjoint A & B].
Proof. by []. Qed.

Lemma fdisjoint_sub {A B} : [disjoint A & B]%fset ->
  forall C : {fset K}, [disjoint fsub C A & fsub C B]%bool.
Proof.
move=> disjointAB C; apply/pred0P => a /=; rewrite !inE.
by have /eqP /fsetP /(_ (val a)) := disjointAB; rewrite !inE.
Qed.

Lemma disjoint_fsub C A B : A `|` B `<=` C ->
  [disjoint fsub C A & fsub C B]%bool = [disjoint A & B].
Proof.
move=> ABsubC.
apply/idP/idP=> [/pred0P DAB|/fdisjoint_sub->//]; apply/eqP/fsetP=> a.
rewrite !inE; have [aC|] := boolP (a \in A `|` B); last first.
  by rewrite !inE => /norP [/negPf-> /negPf->].
by have /= := DAB [` fsubsetP ABsubC _ aC]; rewrite !inE.
Qed.

Lemma fdisjointP {A B} :
  reflect (forall a, a \in A -> a \notin B) [disjoint A & B]%fset.
Proof.
apply: (iffP eqP) => [AIB_eq0 a aA|neq_ab].
  by have /fsetP /(_ a) := AIB_eq0; rewrite !inE aA /= => ->.
apply/fsetP => a; rewrite !inE.
by case: (boolP (a \in A)) => // /neq_ab /negPf ->.
Qed.

Lemma fsetDidPl A B : reflect (A `\` B = A) [disjoint A & B]%fset.
Proof.
apply: (iffP fdisjointP)=> [NB|<- a]; last by rewrite inE => /andP[].
apply/fsetP => a; rewrite !inE andbC.
by case: (boolP (a \in A)) => //= /NB ->.
Qed.

Lemma disjoint_fsetI0 A B : [disjoint A & B] -> A `&` B = fset0.
Proof. by rewrite -fsetI_eq0; move/eqP. Qed.

Lemma fsubsetD A B C :
  (A `<=` (B `\` C)) = (A `<=` B) && [disjoint A & C]%fset.
Proof.
pose D := A `|` B `|` C.
have AD : A `<=` D by rewrite /D -fsetUA fsubsetUl.
have BD : B `<=` D by rewrite /D fsetUAC fsubsetUr.
rewrite -(@subset_fsubE D) //; last first.
  by rewrite fsubDset (fsubset_trans BD) // fsubsetUr.
rewrite fsubD subsetD !subset_fsubE // disjoint_fsub //.
by rewrite /D fsetUAC fsubsetUl.
Qed.

Lemma fsubsetDP A B C :
   reflect (A `<=` B /\ [disjoint A & C]%fset) (A `<=` (B `\` C)).
Proof. by rewrite fsubsetD; apply: andP. Qed.

Lemma fdisjoint_sym A B : [disjoint A & B] = [disjoint B & A].
Proof. by rewrite -!fsetI_eq0 fsetIC. Qed.

Lemma fdisjointP_sym {A B} :
  reflect (forall a, a \in A -> a \notin B) [disjoint B & A]%fset.
Proof. by rewrite fdisjoint_sym; apply: fdisjointP. Qed.

Lemma fdisjoint_trans A B C :
   A `<=` B -> [disjoint B & C] -> [disjoint A & C].
Proof.
move=> AsubB; rewrite -!(@disjoint_fsub (B `|` C)) ?fsetSU //.
by apply: disjoint_trans; rewrite subset_fsub.
Qed.

Lemma fdisjoint0X A : [disjoint fset0 & A].
Proof. by rewrite -fsetI_eq0 fset0I. Qed.

Lemma fdisjointX0 A : [disjoint A & fset0].
Proof. by rewrite -fsetI_eq0 fsetI0. Qed.

Lemma fdisjoint1X x A : [disjoint [fset x] & A] = (x \notin A).
Proof.
rewrite -(@disjoint_fsub (x |` A)) //.
by rewrite (@eq_disjoint1 _ [` fset1U1 _ _]) ?inE =>// ?; rewrite !inE.
Qed.

Lemma fdisjointX1 x A : [disjoint A & [fset x]] = (x \notin A).
Proof. by rewrite fdisjoint_sym fdisjoint1X. Qed.

Lemma fdisjointUX A B C :
   [disjoint A `|` B & C] = [disjoint A & C]%fset && [disjoint B & C]%fset.
Proof. by rewrite -!fsetI_eq0 fsetIUl fsetU_eq0. Qed.

Lemma fdisjointXU A B C :
   [disjoint A & B `|` C] = [disjoint A & B]%fset && [disjoint A & C]%fset.
Proof. by rewrite -!fsetI_eq0 fsetIUr fsetU_eq0. Qed.

Lemma fdisjointU1X x A B :
   [disjoint x |` A & B]%fset = (x \notin B) && [disjoint A & B]%fset.
Proof. by rewrite fdisjointUX fdisjoint1X. Qed.

Lemma fsubK A B : A `<=` B -> [fsetval k in fsub B A] = A.
Proof.
move=> AsubB; apply/fsetP => k /=; symmetry.
have [kB|kNB] := (boolP (k \in B)).
   by rewrite in_fset_valT /= inE.
by rewrite in_fset_valF //; apply: contraNF kNB; apply/fsubsetP.
Qed.

Lemma FSetK A (X : {set A}) : fsub A [fsetval k in X] = X.
Proof. by apply/setP => x; rewrite !inE. Qed.

End Theory.

Module Import FSetInE.
Definition inE := (inE, in_fsetE).
End FSetInE.

Lemma fset_in_finpred (T : finType) (P : pred T) : [fset x in P] = finset P.
Proof. by apply/fsetP => x; rewrite !(inE, in_fsetE). Qed.

Section Card.

Lemma card_finset (T : finType) (P : pred T) : #|` finset P | = #|P|.
Proof.
rewrite card_fsetE cardE; apply/eqP.
rewrite -uniq_size_uniq ?enum_fset_uniq ?enum_uniq // => x.
by rewrite !inE mem_enum.
Qed.

Lemma card_in_imfset (T K : choiceType) (f : T -> K)
   (P : pred T) (A : {fset T}) (p : finmempred P A) :
   {in P &, injective f} -> #|` (imfset f p)| = #|` A|.
Proof.
move=> f_inj; have vP (x : A) : P (val x) by rewrite -(finmempredE p) (valP x).
rewrite -[RHS](@card_in_imset _ _ (fun x : A => [` in_imfset f p (vP x)])).
  symmetry; apply: eq_card => /= k; rewrite !inE; apply/imsetP => /=.
  elim/imfset_rec: k => x Px; have xA : x \in A by rewrite (finmempredE p).
  by exists [` xA] => //; apply/val_inj.
move=> x y _ _ /eqP; rewrite -val_eqE => /eqP /f_inj /eqP.
by rewrite -!topredE /= -!(finmempredE p) val_eqE => /(_ _ _) /eqP; apply.
Qed.

Lemma card_imfset (T K : choiceType) (f : T -> K)
   (P : pred T) (A : {fset T}) (p : finmempred P A) :
   injective f -> #|` (imfset f p)| = #|` A|.
Proof. by move=> f_inj; rewrite card_in_imfset //= => x y ? ?; apply: f_inj. Qed.

Lemma leq_imfset_card (T K : choiceType) (f : T -> K) (P : pred T) (A : {fset T})
  (p : finmempred P A) : (#|` imfset f p| <= #|` A|)%N.
Proof.
have vP (x : A) : P (val x) by rewrite -(finmempredE p) (valP x).
rewrite (leq_trans _ (leq_imset_card (fun x : A => [` in_imfset f p (vP x)]) _)) //.
apply/subset_leq_card/subsetP=> /= x _; apply/imsetP => /=.
have /imfsetP [t Pt x_def] := valP x.
have tA : t \in A by rewrite (finmempredE p).
by exists [` tA] => //; apply/val_inj.
Qed.

End Card.

Section Enum.

Lemma enum_fset0 (T : choiceType) :
  enum [finType of fset0] = [::] :> seq (@fset0 T).
Proof. by rewrite enumT unlock. Qed.

Lemma enum_fset1 (T : choiceType) (x : T) :
  enum [finType of [fset x]] = [:: [`fset11 x]].
Proof.
apply/perm_eq_small=> //; apply/uniq_perm_eq => //.
  by apply/enum_uniq.
case=> [y hy]; rewrite mem_seq1 mem_enum /in_mem /=.
by rewrite eqE /=; rewrite in_fset1 in hy.
Qed.

End Enum.

Section ImfsetTh.
Variables (K V : choiceType).
Implicit Types (f : K -> V) (g : V -> K) (A : {fset K}).

Lemma imfset_id (A : {fset K}) : id @` A = A.
Proof. by apply/fsetP=> a; rewrite !inE. Qed.

Lemma imfset_comp f g A : (g \o f) @` A = g @` (f @` A).
Proof.
apply/fsetP=> a; apply/imfsetP/imfsetP=> [[/= x xA ->]|].
  by exists (f x); rewrite // in_imfset.
by move=> [/= x /imfsetP [/= y yA ->] ->]; exists y.
Qed.

Lemma subset_imfset f A B : A `<=` B -> f @` A `<=` f @` B.
Proof.
move=> /fsubsetP AB; apply/fsubsetP => x /imfsetP [y /= yA ->].
by rewrite in_imfset //= AB.
Qed.

Lemma eq_imfset (f f' : K -> V) (P Q : pred K) (A B : {fset K})
  (p : finmempred P A) (q : finmempred Q B):
  f =1 f' -> P =1 Q -> imfset f p = imfset f' q.
Proof.
move=> eq_f eqP; apply/fsetP => x; apply/imfsetP/imfsetP => /= [] [k Pk ->];
by exists k => //=; rewrite ?eq_f ?eqP in Pk *.
Qed.

End ImfsetTh.

Section PowerSetTheory.
Variable (K : choiceType).

Definition fpowerset (A : {fset K}) : {fset {fset K}} :=
  [fset [fsetval y in Y : {set A}] | Y in powerset [set: A]].

Lemma fpowersetE A B : (B \in fpowerset A) = (B `<=` A).
Proof.
apply/imfsetP/fsubsetP => /= [[Z _ -> y /in_fset_valP [] //]|/fsubsetP subYX].
exists (fsub _ B); last by rewrite fsubK.
by rewrite powersetE /= -fsubT subset_fsub ?fsubset_refl.
Qed.

Lemma fpowersetCE (X A B : {fset K}) :
 (A \in fpowerset (X `\` B)) = (A `<=` X) && [disjoint A & B]%fset.
Proof. by rewrite fpowersetE fsubsetD. Qed.

Lemma fpowersetS A B : (fpowerset A `<=` fpowerset B) = (A `<=` B).
Proof.
apply/fsubsetP/fsubsetP => [sub_pA_pB a|subAB X].
  by have := sub_pA_pB [fset a]; rewrite !fpowersetE !fsub1set.
by rewrite !fpowersetE => /fsubsetP XA; apply/fsubsetP => x /XA /subAB.
Qed.

Lemma fpowerset0 : fpowerset fset0 = [fset fset0].
Proof. by apply/fsetP=> X; rewrite inE fpowersetE fsubset0. Qed.

Lemma fpowerset1 (x : K) : fpowerset [fset x] = [fset fset0; [fset x]].
Proof. by apply/fsetP => X; rewrite !inE fpowersetE fsubset1 orbC. Qed.

Lemma fpowersetI A B : fpowerset (A `&` B) = fpowerset A `&` fpowerset B.
Proof. by apply/fsetP=> X; rewrite inE !fpowersetE fsubsetI. Qed.

Lemma card_fpowerset (A : {fset K}) : #|` fpowerset A| = 2 ^ #|` A|.
Proof.
rewrite card_imfset ?card_finset; first by rewrite card_powerset cardsE.
by move=> X Y /fsetP eqXY; apply/setP => x; have := eqXY (val x); rewrite !inE.
Qed.

End PowerSetTheory.

Section BigFSet.
Variable (R : Type) (idx : R) (op : Monoid.law idx).
Variable (I : choiceType).

Lemma big_fset0 (P : pred fset0) (F : @fset0 I -> R) :
  \big[op/idx]_(i : fset0 | P i) F i = idx.
Proof. by rewrite /index_enum -enumT /= enum_fset0 big_nil. Qed.

Lemma big_fset1 (a : I) (F : [fset a] -> R) :
  \big[op/idx]_(i : [fset a]) F i = F (FSetSub (fset11 a)).
Proof. by rewrite /index_enum -enumT enum_fset1 big_seq1. Qed.

End BigFSet.

Notation "\bigcup_ ( i <- r | P ) F" :=
  (\big[@fsetU _/fset0]_(i <- r | P%fset) F%fset) : fset_scope.

Notation "\bigcup_ ( i <- r ) F" :=
  (\big[@fsetU _/fset0]_(i <- r) F%fset) : fset_scope.

Notation "\bigcup_ ( i | P ) F" :=
  (\big[@fsetU _/fset0]_(i | P) F%fset) : fset_scope.

Notation "\bigcup_ ( i 'in' A | P ) F" :=
  (\big[@fsetU _/fset0]_(i in A | P) F%fset) : fset_scope.

Notation "\bigcup_ ( i 'in' A ) F" :=
  (\big[@fsetU _/fset0]_(i in A) F%fset) : fset_scope.

Section FSetMonoids.

Import Monoid.
Variable (T : choiceType).

Canonical fsetU_monoid := Law (@fsetUA T) (@fset0U T) (@fsetU0 T).
Canonical fsetU_comoid := ComLaw (@fsetUC T).

End FSetMonoids.
Section BigFOpsFin.

Variables (T : choiceType) (I : finType).
Implicit Types (P : pred I) (A B : {fset I}) (F :  I -> {fset T}).

Lemma bigfcup_sup j P F : P j -> F j `<=` \bigcup_(i | P i) F i.
Proof. by move=> Pj; rewrite (bigD1 j) //= fsubsetUl. Qed.

Lemma bigfcupP x F P :
  reflect (exists2 i : I, P i & x \in F i) (x \in (\bigcup_(i | P i) F i)).
Proof.
apply: (iffP idP) => [|[i Pi]]; last first.
  apply: fsubsetP x; exact: bigfcup_sup.
by elim/big_rec: _ => [|i _ Pi _ /fsetUP[|//]]; [rewrite in_fset0 | exists i].
Qed.

Lemma bigfcupsP (U : {fset T}) P F :
  reflect (forall i : I, P i -> F i `<=` U)
          (\bigcup_(i | P i) F i `<=` U).
Proof.
apply: (iffP idP) => [sFU i Pi| sFU].
  by apply: fsubset_trans sFU; apply: bigfcup_sup.
by apply/fsubsetP=> x /bigfcupP[i Pi]; apply: (fsubsetP (sFU i Pi)).
Qed.

End BigFOpsFin.

Section BigFSetIncl.
Variables (R : Type) (idx : R) (op : Monoid.com_law idx).
Variables (T : choiceType) (A B : {fset T}) (F : T -> R).

Lemma big_fset_incl :  A `<=` B ->
  (forall x, x \in B -> x \notin A -> F x = idx) ->
  \big[op/idx]_(x : A) F (val x) = \big[op/idx]_(x : B) F (val x).
Proof.
move=> subAB Fid; symmetry; rewrite [in LHS](bigID [pred x | val x \in A]).
rewrite [X in op _ X]big1 ?Monoid.mulm1; last by move=> x /Fid -> /= //.
have [->|/fset0Pn [a aA]] := eqVneq A fset0; first by rewrite big_fset0 big1.
have aB : a \in B by apply: fsubsetP aA.
pose h (x : A) : B := insubd [` aB] (val x).
pose h' (x : B) : A := insubd [` aA] (val x).
rewrite (reindex h) /=; last first.
  exists h' => x; rewrite !inE => xA; apply/val_inj; move: xA; rewrite !val_insubd.
    by rewrite (fsubsetP subAB) ?fsvalP.
  by move=> ->; rewrite fsvalP.
by apply: eq_big => x; rewrite -?val_eqE !val_insubd ?(fsubsetP subAB) ?fsvalP.
Qed.

End BigFSetIncl.

Implicit Arguments big_fset_incl [R idx op T A B].

Section DefMap.
Variables (K : choiceType) (V : Type).

Record finMap : Type := FinMap {
  domf : {fset K};
  ffun_of_fmap :> {ffun domf -> V}
}.

Definition finmap_of (_ : phant (K -> V)) := finMap.

Let T_ (domf : {fset K}) :=  {ffun domf -> V}.
Local Notation finMap' := {domf : _ & T_ domf}.

End DefMap.

Notation "{fmap T }" := (@finmap_of _ _ (Phant T)) : type_scope.

Definition pred_of_finmap (K : choiceType) (V : Type)
  (f : {fmap K -> V}) : pred K := mem (domf f).
Canonical finMapPredType (K : choiceType) (V : Type) :=
  Eval hnf in mkPredType (@pred_of_finmap K V).

Delimit Scope fmap_scope with fmap.
Local Open Scope fmap_scope.
Notation "f .[ kf ]" := (f [` kf]) : fmap_scope.
Arguments ffun_of_fmap : simpl never.

Notation "[ 'fmap' x : aT => F ]" := (FinMap [ffun x : aT => F])
  (at level 0, x ident, only parsing) : fun_scope.

Notation "[ 'fmap' : aT => F ]" := (FinMap [ffun : aT => F])
  (at level 0, only parsing) : fun_scope.

Notation "[ 'fmap' x => F ]" := [fmap x : _ => F]
  (at level 0, x ident, format "[ 'fmap'  x  =>  F ]") : fun_scope.

Notation "[ 'fmap' => F ]" := [fmap: _ => F]
  (at level 0, format "[ 'fmap' =>  F ]") : fun_scope.

Canonical finmap_of_finfun (K : choiceType) V (A : {fset K}) (f : {ffun A -> V}) := FinMap f.
Arguments finmap_of_finfun /.
Arguments ffun_of_fmap : simpl nomatch.

Section OpsMap.

Variables (K : choiceType).

Definition fmap0 V : {fmap K -> V} := FinMap (ffun0 _ (cardfs0 K)).

Definition fnd V (A : {fset K}) (f : {ffun A -> V}) (k : K) :=
  omap f (insub k).

Inductive fnd_spec V (A : {fset K}) (f : {ffun A -> V}) k :
  bool -> option A -> option V -> Type :=
| FndIn  (kf : k \in A) : fnd_spec f k true (some [` kf]) (some (f.[kf]))
| FndOut (kNf : k \notin A) : fnd_spec f k false None None.

Definition setf V (f : {fmap K -> V}) (k0 : K) (v0 : V) : {fmap K -> V} :=
  [fmap k : k0 |` domf f => if val k == k0 then v0
                            else odflt v0 (fnd f (val k))].

End OpsMap.

Prenex Implicits fnd setf.
Arguments fmap0 {K V}.
Arguments setf : simpl never.
Arguments fnd : simpl never.

Notation "[ 'fmap' 'of' T ]" := (fmap0 : {fmap T}) (only parsing) : fmap_scope.
Notation "[fmap]" := fmap0 : fmap_scope.
Notation "x .[ k <- v ]" := (setf x k v) : fmap_scope.
Notation "f .[? k ]" := (fnd f k) : fmap_scope.

Section FinMapCanonicals.
Variable K : choiceType.

Let finMap_on (V : Type) (d : {fset K}) := {ffun d -> V}.
Local Notation finMap_ V := {d : _ & finMap_on V d}.

Definition finMap_encode V (f : {fmap K -> V}) := Tagged (finMap_on V) (ffun_of_fmap f).
Definition finMap_decode V (f : finMap_ V) := FinMap (tagged f).
Lemma finMap_codeK V : cancel (@finMap_encode V) (@finMap_decode V).
Proof. by case. Qed.

Section FinMapEqType.
Variable V : eqType.

Definition finMap_eqMixin := CanEqMixin (@finMap_codeK V).
Canonical finMap_eqType := EqType {fmap K -> V} finMap_eqMixin.

End FinMapEqType.

Section FinMapChoiceType.
Variable V : choiceType.

Definition finMap_choiceMixin := CanChoiceMixin (@finMap_codeK V).
Canonical finMap_choiceType := ChoiceType {fmap K -> V} finMap_choiceMixin.

End FinMapChoiceType.

End FinMapCanonicals.

Section FinMapTheory.
Variables (K : choiceType).

Lemma fndP V (f : {fmap K -> V}) k :
  fnd_spec f k (k \in domf f) (insub k) (f.[? k]).
Proof.
rewrite /fnd; case: insubP=> [[k' k'f] _ {k} <- /=|kNf].
  by rewrite k'f; constructor.
by rewrite (negPf kNf); constructor.
Qed.

Lemma fndSome V (f : {fmap K -> V}) (k : K) :
  f.[? k] = (k \in f) :> bool.
Proof. by case: fndP. Qed.

Lemma not_fnd V (f : {fmap K -> V}) (k : K) :
  k \notin f -> f.[? k] = None.
Proof. by case: fndP. Qed.

Lemma getfE V (f : {fmap K -> V}) (k : domf f)
      (kf : val k \in domf f) : f.[kf] = f k :> V.
Proof. by congr (_ _); apply: val_inj. Qed.

Lemma eq_getf V (f : {fmap K -> V}) k (kf kf' : k \in domf f) :
  f.[kf] = f.[kf'] :> V.
Proof. by rewrite (@getfE _ _ [` kf']). Qed.

Lemma Some_fnd V (f : {fmap K -> V}) (k : domf f) :
  Some (f k) = f.[? val k].
Proof. by case: fndP (valP k) => // ? _; rewrite getfE. Qed.

Lemma in_fnd V (f : {fmap K -> V}) (k : K)
      (kf : k \in domf f) : f.[? k] = Some f.[kf].
Proof. by rewrite Some_fnd. Qed.

Lemma fnd_if V (cond : bool) (f g : {fmap K -> V}) (k : K) :
  ((if cond then f else g) : finMap _ _).[? k] =
  if cond then f.[? k] else g.[? k].
Proof. by case: cond. Qed.

Lemma getfP V (f g : {fmap K -> V}) : domf f = domf g ->
  (forall k (kMf : k \in f) (kMg : k \in g), f.[kMf] = g.[kMg]) -> f = g.
Proof.
move: f g => [kf f] [kg g] /= eq_kfg; case: _ / eq_kfg in g * => {kg}.
move=> eq_fg; congr FinMap; apply/ffunP => /= x.
by do [rewrite -!getfE; do ?exact: valP] => *.
Qed.

Lemma fmapP V (f g : {fmap K -> V}) :
      (forall k, f.[? k] = g.[? k]) <-> f = g.
Proof.
split=> [fnd_fg|-> //]; apply: getfP => [|k kMf kMg].
  by apply/fsetP => x; rewrite -!fndSome fnd_fg.
by apply: Some_inj; rewrite !Some_fnd.
Qed.

Lemma fnd_fmap0 V k : ([fmap] : {fmap K -> V}).[? k] = None.
Proof. by rewrite not_fnd // in_fset0. Qed.

Lemma mem_setf V (f : {fmap K -> V}) (k0 : K) (v0 : V) :
  f.[k0 <- v0] =i predU1 k0 (mem (domf f)).
Proof. by move=> k; rewrite !inE. Qed.

Lemma dom_setf V (f : {fmap K -> V}) (k0 : K) (v0 : V) :
  domf (f.[k0 <- v0]) = k0 |` domf f.
Proof. by apply/fsetP=> k; rewrite mem_setf. Qed.

Lemma fnd_set_in V (f : {fmap K -> V}) k0 v0 (x : domf f.[k0 <- v0]) :
  val x != k0 -> val x \in f.
Proof. by have := valP x; rewrite mem_setf inE; case: eqP. Qed.

Lemma setfK V (f : {fmap K -> V}) k0 v0 (x : domf f.[k0 <- v0]):
   f.[k0 <- v0] x = if eqVneq (val x) k0 is right xNk0
                    then f.[fnd_set_in xNk0] else v0.
Proof.
case: eqVneq => [|xNk0]; rewrite ?ffunE /=; first by move->; rewrite eqxx.
by rewrite (negPf xNk0) in_fnd ?fnd_set_in //= => xf; apply: eq_getf.
Qed.

Lemma fnd_set V (f : {fmap K -> V}) k0 v0 k :
   f.[k0 <- v0].[? k] = if k == k0 then Some v0 else f.[? k].
Proof.
case: fndP => [ksf|]; last first.
  by rewrite mem_setf inE negb_or => /andP [/negPf ->]; case: fndP.
rewrite setfK; case: eqVneq => //= [->|kNk0]; first by rewrite eqxx.
by rewrite Some_fnd (negPf kNk0).
Qed.

Lemma fmap_nil V (f : {fmap K -> V}) : domf f = fset0 -> f = [fmap].
Proof.
by move=> kf0; apply: getfP => //= k ? kMg; have := kMg; rewrite !inE.
Qed.

Lemma getf_set V (f : {fmap K -> V}) (k : K) (v : V) (kf' : k \in _) :
   f.[k <- v].[kf'] = v.
Proof. by apply: Some_inj; rewrite Some_fnd fnd_set eqxx. Qed.

Lemma setf_get V (f : {fmap K -> V}) (k : domf f) :
  f.[val k <- f k] = f.
Proof. by apply/fmapP=> k'; rewrite fnd_set Some_fnd; case: eqP => [->|]. Qed.

Lemma setfNK V (f : {fmap K -> V}) (k k' : K) (v : V)
      (k'f : k' \in _) (k'f' : k' \in _):
   f.[k <- v].[k'f'] = if k' == k then v else f.[k'f].
Proof. by apply: Some_inj; rewrite Some_fnd !fnd_set in_fnd; case: ifP. Qed.

Lemma domf0 V : domf [fmap of K -> V] = fset0. Proof. by apply/fsetP => x. Qed.

End FinMapTheory.

Section ReduceOp.

Variable (K : choiceType) (V : Type).
Implicit Types (f : {fmap K -> option V}).

Lemma reducef_subproof f (x : [fsetval x : domf f | f x]) :
  f (fincl (fset_sub_val _) x).
Proof.
set y := (y in f y); suff : val y \in [fsetval x : domf f | f x].
  by rewrite val_in_fset.
by suff -> : val y = val x by exact: valP.
Qed.

Definition reducef f : {fmap K -> V} :=
  [fmap x => oextract (@reducef_subproof f x)].

Lemma domf_reduce f : domf (reducef f) = [fsetval x : domf f | f x].
Proof. by []. Qed.

Lemma mem_reducef f k : k \in reducef f = ojoin f.[? k].
Proof.
rewrite inE; case: fndP => [kf|] /=; first by rewrite in_fset_valT.
by apply: contraNF; apply: (fsubsetP (fset_sub_val _)).
Qed.

Lemma fnd_reducef f k : (reducef f).[? k] = ojoin f.[? k].
Proof.
case: fndP => /= [kf|]; last by rewrite mem_reducef; case: ojoin.
rewrite ffunE /= Some_oextract; apply: Some_inj; rewrite Some_fnd.
by rewrite Some_ojoin // ojoinT // -mem_reducef.
Qed.

Lemma get_reducef f k (krf : k \in reducef f) (kf : k \in f):
  Some (reducef f).[krf] = f.[kf].
Proof. by rewrite Some_fnd fnd_reducef in_fnd. Qed.

End ReduceOp.

Arguments reducef : simpl never.

Section RestrictionOps.
Variable (K : choiceType) (V : Type).
Implicit Types (f g : {fmap K -> V}).

Definition filterf f (P : pred K) : {fmap K -> V} :=
   [fmap x : [fset x in domf f | P x] => f (fincl (fset_sub _ _) x)].

Definition restrictf f (A : {fset K}) : {fmap K -> V} :=
  filterf f (mem A).

Notation "x .[& A ]" := (restrictf x A) : fmap_scope.
Notation "x .[\ A ]" := (x.[& domf x `\` A]) : fmap_scope.
Notation "x .[~ k ]" := (x.[\ [fset k]]) : fmap_scope.

Lemma domf_filterf f (P : pred K) :
 domf (filterf f P) = [fset k in domf f | P k].
Proof. by []. Qed.

Lemma mem_filterf f (P : pred K) (k : K) :
  (k \in domf (filterf f P)) = (k \in f) && (P k) :> bool.
Proof. by rewrite !inE. Qed.

Lemma mem_restrictf f (A : {fset K}) (k : K) :
   k \in f.[& A] = (k \in A) && (k \in f) :> bool.
Proof. by rewrite mem_filterf andbC. Qed.

Lemma mem_remf f (A : {fset K}) (k : K) :
   k \in f.[\ A] = (k \notin A) && (k \in f) :> bool.
Proof. by rewrite mem_restrictf inE -andbA andbb. Qed.

Lemma mem_remf1 f (k' k : K) :
   k \in f.[~ k'] = (k != k') && (k \in f) :> bool.
Proof. by rewrite mem_remf inE. Qed.

Lemma domf_restrict f A : domf f.[& A] = A `&` domf f.
Proof. by apply/fsetP=> k'; rewrite mem_restrictf !inE. Qed.

Lemma domf_rem f A : domf f.[\ A] = domf f `\` A.
Proof. by rewrite domf_restrict fsetIDAC fsetIid. Qed.

Lemma mem_remfF f (k : K) : k \in f.[~ k] = false.
Proof. by rewrite mem_remf1 eqxx. Qed.

Lemma fnd_filterf f P k : (filterf f P).[? k] = if P k then f.[? k] else None.
Proof.
case: fndP => [kff|]; last first.
  by rewrite inE => /nandP [/not_fnd->|/negPf-> //]; rewrite if_same.
by have := kff; rewrite inE => /andP [kf ->]; rewrite ffunE Some_fnd.
Qed.

Lemma get_filterf f P k (kff : k \in filterf f P) (kf : k \in f) :
  (filterf f P).[kff] = f.[kf].
Proof.
apply: Some_inj; rewrite !Some_fnd /= fnd_filterf.
by move: kff; rewrite !inE => /andP [? ->].
Qed.

Lemma fnd_restrict f A (k : K) :
   f.[& A].[? k] = if k \in A then f.[? k] else None.
Proof. by rewrite fnd_filterf. Qed.

Lemma fnd_rem f A (k : K) : f.[\ A].[? k] = if k \in A then None else f.[? k].
Proof.
rewrite fnd_restrict inE.
by case: fndP => ?; rewrite ?(andbT, andbF) //=; case: (_ \in _).
Qed.

Lemma restrictf_comp f A B : f.[& A].[& B] = f.[& A `&` B].
Proof.
by apply/fmapP=> k; rewrite !fnd_restrict !inE; do !case: (_ \in _).
Qed.

Lemma remf_comp f A B : f.[\ A].[\ B] = f.[\ A `|` B].
Proof. by apply/fmapP=> k; rewrite !fnd_rem inE; do !case: (_ \in _). Qed.

Lemma restrictfT f : f.[& domf f] = f.
Proof. by apply/fmapP=> k; rewrite fnd_restrict; case: fndP. Qed.

Lemma restrictf0 f : f.[& fset0] = [fmap].
Proof. by apply/fmapP => k; rewrite fnd_restrict !(inE, not_fnd). Qed.

Lemma remf0 f : f.[\ fset0] = f. Proof. by rewrite fsetD0 restrictfT. Qed.

Lemma fnd_rem1 f (k k' : K) :
  f.[~ k].[? k'] = if k' != k then f.[? k'] else None.
Proof. by rewrite fnd_rem inE; case: eqP. Qed.

Lemma getf_restrict f A (k : K) (kf : k \in f) (kfA : k \in f.[& A]) :
      f.[& A].[kfA] = f.[kf].
Proof. by rewrite get_filterf. Qed.

Lemma setf_restrict f A (k : K) (v : V) :
  f.[& A].[k <- v] = f.[k <- v].[& k |` A].
Proof.
by apply/fmapP=> k'; rewrite !(fnd_set, fnd_restrict, inE); case: eqP.
Qed.

Lemma setf_rem f A (k : K) (v : V) :
  f.[\ A].[k <- v] = f.[k <- v].[\ (A `\ k)].
Proof. by rewrite setf_restrict fsetUDl. Qed.

Lemma setf_rem1 f (k : K) (v : V) : f.[~ k].[k <- v] = f.[k <- v].
Proof. by rewrite setf_rem fsetDv remf0. Qed.

Lemma setfC f k1 k2 v1 v2 : f.[k1 <- v1].[k2 <- v2] =
   if k2 == k1 then f.[k2 <- v2] else f.[k2 <- v2].[k1 <- v1].
Proof.
apply/fmapP => k. rewrite fnd_if !fnd_set.
have [[->|kNk2] [// <-|k2Nk1]] // := (altP (k =P k2), altP (k2 =P k1)).
by rewrite (negPf kNk2).
Qed.

Lemma restrictf_mkdom f A : f.[& A] = f.[& domf f `&` A].
Proof.
apply/fmapP=> k; rewrite !fnd_restrict inE.
by case: fndP => ?; rewrite ?(andbT, andbF) //=; case: (_ \in _).
Qed.

Lemma restrictf_id f A : [disjoint domf f & A] -> f.[& A] = [fmap].
Proof. by move=> dAf; rewrite restrictf_mkdom (eqP dAf) restrictf0. Qed.

Lemma remf_id f A : [disjoint domf f & A] -> f.[\ A] = f.
Proof. by move=> /fsetDidPl ->; rewrite restrictfT. Qed.

Lemma remf1_id f k : k \notin f -> f.[~ k] = f.
Proof. by move=> kNf; rewrite remf_id //= fdisjointX1. Qed.

Lemma restrictf_set f A (k : K) (v : V) :
  f.[k <- v].[& A] = if k \in A then f.[& A].[k <- v] else f.[& A].
Proof.
apply/fmapP => k' /=; rewrite !(fnd_if, fnd_set, fnd_restrict).
by case: eqP => [->|]; do !case: ifP.
Qed.

Lemma remf_set f A (k : K) (v : V) :
  f.[k <- v].[\ A] = if k \in A then f.[\ A] else f.[\ A].[k <- v].
Proof.
apply/fmapP => k' /=; rewrite !(fnd_if, fnd_rem, fnd_set, inE).
by case: eqP => [->|]; do !case: (_ \in _).
Qed.

Lemma remf1_set f (k k' : K) (v : V) :
  f.[k' <- v].[~ k] = if k == k' then f.[~ k] else f.[~ k].[k' <- v].
Proof. by rewrite remf_set inE eq_sym. Qed.

Lemma setf_inj f f' k v : k \notin f -> k \notin f' ->
                          f.[k <- v] = f'.[k <- v]-> f = f'.
Proof.
move=> kf kf' eq_fkv; apply/fmapP => k'.
have := congr1 (fun g => g.[? k']) eq_fkv.
by rewrite !fnd_set; case: eqP => // ->; rewrite !not_fnd.
Qed.

End RestrictionOps.

Arguments filterf : simpl never.
Arguments restrictf : simpl never.
Notation "x .[& A ]" := (restrictf x A) : fmap_scope.
Notation "x .[\ A ]" := (x.[& domf x `\` A]) : fmap_scope.
Notation "x .[~ k ]" := (x.[\ [fset k]]) : fmap_scope.

Section Cat.
Variables (K : choiceType) (V : Type).
Implicit Types (f g : {fmap K -> V}).

Definition catf (f g : {fmap K -> V}) :=
  [fmap k : (domf f `\` domf g) `|` domf g=>
          match fsetULVR (valP k) with
            | inl kfDg => f.[fsubsetP (fsubsetDl _ _) _ kfDg]
            | inr kg => g.[kg]
          end].

Local Notation "f + g" := (catf f g) : fset_scope.

Lemma domf_cat f g : domf (f + g) = domf f `|` domf g.
Proof.
by apply/fsetP=> x; rewrite !inE; case: (boolP (_ \in domf _)); rewrite ?orbT.
Qed.

Lemma mem_catf f g k : k \in domf (f + g) = (k \in f) || (k \in g).
Proof. by rewrite domf_cat inE. Qed.

Lemma fnd_cat f g k :
  (f + g).[? k] = if k \in domf g then g.[? k] else f.[? k].
Proof.
case: fndP => //= [kfg|]; rewrite /catf /=.
  rewrite ffunE /=; case: fsetULVR => [kf|kg]; last by rewrite Some_fnd kg.
  by rewrite -in_fnd; move: kf; rewrite inE => /andP[/negPf ->].
by rewrite mem_catf => /norP [kNf kNg]; rewrite !not_fnd // if_same.
Qed.

Lemma catfE f g : f + g = f.[\ domf g] + g.
Proof. by apply/fmapP=> k; rewrite !(fnd_cat, fnd_rem); case: ifP. Qed.

Lemma getf_catl f g k (kfg : k \in domf (f + g))
      (kf : k \in domf f) : k \notin domf g -> (f + g).[kfg] = f.[kf].
Proof.
by move=> kNg; apply: Some_inj; rewrite Some_fnd fnd_cat (negPf kNg) in_fnd.
Qed.

Lemma getf_catr f g k (kfg : k \in domf (f + g))
      (kg : k \in domf g) : (f + g).[kfg] = g.[kg].
Proof. by apply: Some_inj; rewrite Some_fnd fnd_cat kg in_fnd. Qed.

Lemma catf0 f : f + [fmap] = f.
Proof. by apply/fmapP => k; rewrite fnd_cat in_fset0. Qed.

Lemma cat0f f : [fmap] + f = f.
Proof.
apply/fmapP => k; rewrite fnd_cat; case: ifPn => //= kf.
by rewrite !not_fnd ?inE.
Qed.

Lemma catf_setl f g k (v : V) :
  f.[k <- v] + g = if k \in g then f + g else (f + g).[k <- v].
Proof.
apply/fmapP=> k'; rewrite !(fnd_if, fnd_cat, fnd_set).
by have [->|Nkk'] := altP eqP; do !case: (_ \in _).
Qed.

Lemma catf_setr f g k (v : V) : f + g.[k <- v] = (f + g).[k <- v].
Proof.
apply/fmapP=> k'; rewrite !(fnd_cat, fnd_set, mem_setf, inE).
by have [->|Nkk'] := altP eqP; do !case: (_ \in _).
Qed.

Lemma restrictf_cat f g A : (f + g).[& A] = f.[& A] + g.[& A].
Proof.
apply/fmapP => k'; rewrite !(fnd_cat, fnd_restrict) mem_restrictf.
by case: (_ \in _).
Qed.

Lemma restrictf_cat_domr f g : (f + g).[& domf g] = g.
Proof.
rewrite catfE restrictf_cat restrictf_comp.
by rewrite fsetIDAC fsetDIl fsetDv fsetI0 restrictf0 restrictfT cat0f.
Qed.

Lemma remf_cat f g A : (f + g).[\ A] = f.[\ A] + g.[\ A].
Proof.
by apply/fmapP => k'; rewrite !(fnd_cat, fnd_rem) mem_remf; case: (_ \in _).
Qed.

Lemma catf_restrictl A f g : f.[& A] + g = (f + g).[& A `|` domf g].
Proof.
apply/fmapP=> k; rewrite !(fnd_cat, fnd_restrict) !inE.
by do !case: (_ \in _).
Qed.

Lemma catf_reml A f g : f.[\ A] + g = (f + g).[\ A `\` domf g].
Proof.
by apply/fmapP=> k; rewrite !(fnd_cat, fnd_rem) inE; case: (_ \in _).
Qed.

Lemma catf_rem1l k f g :
  f.[~ k] + g = if k \in g then f + g else (f + g).[~ k].
Proof.
apply/fmapP => k'; rewrite !(fnd_if, fnd_cat, fnd_rem1).
by have [->|?] := altP eqP; do !case: (_ \in _).
Qed.

Lemma setf_catr f g k (v : V) : (f + g).[k <- v] = f + g.[k <- v].
Proof. by rewrite catf_setr. Qed.

Lemma setf_catl f g k (v : V) : (f + g).[k <- v] = f.[k <- v] + g.[~ k].
Proof. by rewrite catf_setl mem_remf1 eqxx /= !setf_catr setf_rem1. Qed.

Lemma catfA f g h : f + (g + h) = f + g + h.
Proof.
by apply/fmapP => k; rewrite !fnd_cat !mem_catf; do !case: (_ \in _).
Qed.

Lemma catfC f g : f + g = g + f.[\ domf g].
Proof.
apply/fmapP=> k; rewrite !fnd_cat fnd_rem domf_rem inE.
by have [|kNg] //= := boolP (_ \in domf g); rewrite (not_fnd kNg); case: fndP.
Qed.

Lemma disjoint_catfC f g : [disjoint domf f & domf g] -> f + g = g + f.
Proof. by move=> dfg; rewrite catfC remf_id. Qed.

Lemma catfAC f g h : f + g + h = f + h + g.[\ domf h].
Proof. by rewrite -!catfA [X in _ + X]catfC. Qed.

Lemma disjoint_catfAC f g h : [disjoint domf g & domf h]%fmap ->
     f + g + h = f + h + g.
Proof. by move=> dgh; rewrite catfAC remf_id. Qed.

Lemma catfCA f g h : f + (g + h) = g + (f.[\ domf g] + h).
Proof. by rewrite !catfA [X in X + _]catfC. Qed.

Lemma disjoint_catfCA f g h : [disjoint domf f & domf g]%fmap ->
     f + (g + h) = g + (f + h).
Proof. by move=> dfg; rewrite catfCA remf_id. Qed.

Lemma catfIs f g h : f + h = g + h -> f.[\ domf h] = g.[\ domf h].
Proof.
move=> /fmapP eq_fg_fh; apply/fmapP => k; have := eq_fg_fh k.
by rewrite !fnd_cat !fnd_rem; case: ifP.
Qed.

Lemma disjoint_catfIs h f g :
  [disjoint domf f & domf h] -> [disjoint domf g & domf h] ->
  f + h = g + h -> f = g.
Proof. by move=> dfg dgh /catfIs; rewrite !remf_id. Qed.

Lemma restrict_catfsI f g h : f + g = f + h -> g.[& domf h] = h.[& domf g].
Proof.
move=> /fmapP eq_fg_fh; apply/fmapP => k; have := eq_fg_fh k.
rewrite !fnd_cat !fnd_restrict.
by do ![case: (boolP (_ \in domf _)) => ? //=] => _; rewrite not_fnd.
Qed.

Lemma disjoint_catfsI h f g :
  [disjoint domf f & domf h] -> [disjoint domf g & domf h] ->
  h + f = h + g -> f = g.
Proof.
move=> dfg dgh; rewrite -disjoint_catfC // -[RHS]disjoint_catfC //.
by apply: disjoint_catfIs.
Qed.

End Cat.

Module Import FmapE.
Definition fmapE := (fndSome, getfE, setfK, fnd_set, getf_set,
  setfNK, fnd_reducef, get_reducef, fnd_filterf, get_filterf,
  fnd_restrict, getf_restrict, fnd_rem, fnd_rem1,
  restrictfT, restrictf0, restrictf_id, remf_id, remf1_id,
  fnd_cat).
End FmapE.

Arguments catf : simpl never.
Notation "f + g" := (catf f g) : fset_scope.

Section FinMapKeyType.
Variables (K V : choiceType).
Implicit Types (f g : {fmap K -> V}).

Definition codomf f : {fset V} := [fset f k | k : domf f].

Lemma mem_codomf f v : (v \in codomf f) = [exists x : domf f, f x == v].
Proof.
apply: sameP existsP.
by apply: (iffP (imfsetP _ _ _)) => /= [[x _ ->]|[x /eqP <-]]; exists x.
Qed.

Lemma codomfP f v : reflect (exists x, f.[? x] = Some v) (v \in codomf f).
Proof.
apply: (iffP (imfsetP _ _ _)) => /= [[x _ ->]|[k]].
  by exists (val x); rewrite Some_fnd.
by case: fndP => //= kf [<-]; exists [` kf].
Qed.

Lemma codomfPn f v : reflect (forall x, f.[? x] != Some v) (v \notin codomf f).
Proof.
rewrite mem_codomf negb_exists; apply: (iffP forallP) => f_eq_v x /=.
  by case: fndP => //= kf; rewrite f_eq_v.
by apply: contraNneq (f_eq_v (val x)) => <-; rewrite Some_fnd.
Qed.

Lemma codomf0 : codomf [fmap] = fset0.
Proof.
apply/fsetP=> k; rewrite inE; apply/negP => /codomfP [k'].
by rewrite not_fnd //= inE.
Qed.

Lemma in_codomf f (k : domf f) : f k \in codomf f.
Proof. by rewrite in_imfset. Qed.

Lemma fndSomeP f (k : K) (v : V):
  (f.[? k] = Some v) <-> {kf : k \in f & f.[kf] = v}.
Proof.
split => [fk|[kf fk]]; last by rewrite in_fnd fk.
have kf : k \in f by rewrite -fndSome fk.
by exists kf; apply: Some_inj; rewrite Some_fnd.
Qed.

Lemma codomf_restrict f (A : {fset K})  :
  codomf f.[& A] = [fset f k | k : domf f & val k \in A].
Proof.
apply/fsetP=> v; apply/imfsetP/imfsetP => /= [] [k kP ->].
  have := valP k; rewrite !inE => /andP [kf kA]; exists [` kf] => //.
  by rewrite ffunE /= -getfE.
have kA : val k \in [fset x | x in domf f & x \in A] by rewrite !inE (valP k).
by exists [` kA]; rewrite // ?ffunE !getfE.
Qed.

Lemma codomf_restrict_exists f (A : {fset K})  :
  codomf f.[& A] = [fset v in codomf f
                   | [exists k : domf f, (val k \in A) && (f k == v)]].
Proof.
rewrite codomf_restrict; apply/fsetP => v; rewrite !inE /=; apply/imfsetP/idP.
  by move=> [k kA ->]; rewrite in_codomf /=; apply/existsP; exists k; apply/andP.
by move=> /andP[fkdom /existsP [k /andP[kA /eqP<-]]]; exists k.
Qed.

Lemma codomf_rem f (A : {fset K})  :
  codomf f.[\ A] = [fset f k | k : domf f & val k \notin A].
Proof.
rewrite codomf_restrict.
by apply: eq_imfset => //= x /=; rewrite -!topredE /= !inE (valP x) andbT.
Qed.

Lemma codomf_rem_exists f (A : {fset K})  :
  codomf f.[\ A] = [fset v in codomf f
                   | [exists k : domf f, (val k \notin A) && (f k == v)]].
Proof.
rewrite codomf_restrict_exists; apply: eq_imfset => x //=; case: (_ \in _) => //=.
apply/existsP/existsP => [] /= [k]; rewrite ?inE;
by do 2?[move=>/andP []]; exists k; rewrite ?inE; do 2?[apply/andP; split].
Qed.

Lemma in_codomf_rem1 f (k : K) (kf : k \in domf f)  :
  codomf f.[~ k] =
  if [exists k' : domf f, (val k' != k) && (f k' == f.[kf])] then codomf f
  else codomf f `\ f.[kf].
Proof.
apply/fsetP => v; rewrite codomf_rem_exists (fun_if (fun x => v \in x)) !inE.
have [vf|vNf] := boolP (_ \in codomf f); rewrite /= ?(andbF,andbT) ?if_same //.
rewrite -/(_ || _); apply/existsP/idP => /= [[k' /andP[xk /eqP <-]]|].
  rewrite orbC -implybE; apply/implyP => eq_fk.
  by rewrite inE /= in xk; apply/existsP; exists k'; rewrite // xk eq_fk.
have /imfsetP /= [[l lf] _ ->] := vf; rewrite orbC.
have [->|neq_f _] := altP (f.[lf] =P _).
  by move=> /existsP [m /andP[Nmk /eqP <-]]; exists m; rewrite eqxx inE Nmk.
exists [` lf]; rewrite eqxx andbT inE /=.
apply: contra neq_f => /eqP eq_lk; rewrite eq_lk in lf *.
by apply/eqP; congr f.[_]; apply: bool_irrelevance.
Qed.

Lemma codomf_set f (k : K) (v : V) (kf : k \in domf f) :
  codomf f.[k <- v] = v |` codomf f.[~ k].
Proof.
rewrite -setf_rem1; apply/fsetP=> v'; rewrite !inE.
have [->|neq_v'v] /= := altP eqP.
  by apply/codomfP; exists k; rewrite fnd_set eqxx.
apply/codomfP/codomfP => [] [k' fk'_eq]; exists k';
move: fk'_eq; rewrite fnd_set.
  by have [_ [eq_vv']|//] := altP eqP; rewrite eq_vv' eqxx in neq_v'v *.
by have [->|//] := altP eqP; rewrite fnd_rem inE eqxx.
Qed.

End FinMapKeyType.

Module Import FinmapInE.
Definition inE := (inE, mem_codomf, mem_catf, mem_remfF,
                   mem_filterf, mem_reducef, mem_restrictf,
                   mem_remf, mem_remf1, mem_setf).
End FinmapInE.

Section FsfunDef.

Variables (K : choiceType) (V : eqType) (default : K -> V).

Record fsfun := Fsfun {
  fmap_of_fsfun : {fmap K -> V};
  _ : [forall k : domf fmap_of_fsfun,
       fmap_of_fsfun k != default (val k)]
}.

Canonical fsfun_subType := Eval hnf in [subType for fmap_of_fsfun].
Definition fsfun_eqMixin := [eqMixin of fsfun by <:].
Canonical  fsfun_eqType := EqType fsfun fsfun_eqMixin.

Fact fsfun_subproof (f : fsfun) :
  forall (k : K) (kf : k \in fmap_of_fsfun f),
  (fmap_of_fsfun f).[kf]%fmap != default k.
Proof.
case:f => f f_stable k kf /=.
exact: (forallP f_stable [` kf]).
Qed.

Definition fun_of_fsfun (f : fsfun) (k : K) :=
  odflt (default k) (fmap_of_fsfun f).[? k]%fmap.

Coercion fun_of_fsfun : fsfun >-> Funclass.

Definition finsupp f := domf (fmap_of_fsfun f).

Lemma mem_finsupp f (k : K) : (k \in finsupp f) = (f k != default k).
Proof.
rewrite /fun_of_fsfun; case: fndP; rewrite ?eqxx //=.
by move=> kf; rewrite fsfun_subproof.
Qed.

Lemma memNfinsupp f (k : K) : (k \notin finsupp f) = (f k == default k).
Proof. by rewrite mem_finsupp negbK. Qed.

Lemma fsfun_dflt f (k : K) : k \notin finsupp f -> f k = default k.
Proof. by rewrite mem_finsupp negbK => /eqP. Qed.

CoInductive fsfun_spec f (k : K) : V -> bool -> Type :=
  | FsfunOut : k \notin finsupp f -> fsfun_spec f k (default k) false
  | FsfunIn  (kf : k \in finsupp f) : fsfun_spec f k (f k) true.

Lemma finsuppP f (k : K) : fsfun_spec f k (f k) (k \in finsupp f).
Proof.
have [kf|kNf] := boolP (_ \in _); first by constructor.
by rewrite fsfun_dflt // ; constructor.
Qed.

Lemma fsfunP (f g : fsfun) : f =1 g <-> f = g.
Proof.
split=> [eq_fg|->//]; apply/val_inj/fmapP => k.
have := eq_fg k; rewrite /(f _) /(g _) /=.
case: fndP; case: fndP => //= kf kg; first by move->.
  by move/eqP/negPn; rewrite fsfun_subproof.
by move/eqP/negPn; rewrite eq_sym fsfun_subproof.
Qed.

Lemma fsfun_injective_inP  (f : fsfun) (T : {fset K}) :
  reflect {in T &, injective f} (injectiveb [ffun x : T => f (val x)]).
Proof.
apply: (iffP (@injectiveP _ _ _)) => f_inj a b; last first.
  by rewrite !ffunE => *; apply: val_inj; apply: f_inj => //; apply: valP.
move=> aT bT eq_ga_gb; have := f_inj.[aT].[bT]; rewrite !ffunE /=.
by move=> /(_ eq_ga_gb) /(congr1 val).
Qed.

Definition fsfun_of_can_ffun (T : {fset K}) (g : {ffun T -> V})
          (can_g : forall k : T,  g k != default (val k)) :=
  @Fsfun (FinMap g) (appP forallP idP can_g).

Lemma fsfun_of_can_ffunE (T : {fset K}) (g : {ffun T -> V})
          (can_g : forall k : T ,  g k != default (val k))
          (k : K) (kg : k \in T) :
  (fsfun_of_can_ffun can_g) k = g.[kg].
Proof. by rewrite/fun_of_fsfun in_fnd. Qed.

End FsfunDef.

Notation "{fsfun x : T => dflt }" := (fsfun (fun x : T => dflt))
  (x ident, only parsing) : type_scope.
Notation "{fsfun x => dflt }" := {fsfun x : _ => dflt}
  (x ident, only parsing) : type_scope.
Notation "{fsfun=> dflt }" := (fsfun (fun=> dflt))
  (format "{fsfun=> dflt }") : type_scope.

Module Type FsfunSig.
Section FsfunSig.
Variables (K : choiceType) (V : eqType) (default : K -> V).

Parameter of_ffun : forall (S : {fset K}), (S -> V) -> fsfun default.
Variables (S : {fset K}) (h : S -> V).
Axiom of_ffunE : forall x, of_ffun h x = odflt (default x) (omap h (insub x)).

End FsfunSig.
End FsfunSig.

Module Fsfun : FsfunSig.
Section FsfunOfFinfun.

Variables (K : choiceType) (V : eqType) (default : K -> V)
          (S : {fset K}) (h : S -> V).

Let fmap :=
  [fmap a : [fsetval a in {: S} | h a != default (val a)]
   => h (fincl (fset_sub_val _) a)].

Fact fmapP a : fmap a != default (val a).
Proof.
rewrite ffunE; have /in_fset_valP [a_in_S] := valP a.
by have -> : [` a_in_S] = fincl (fset_sub_val _) a by exact/val_inj.
Qed.

Definition of_ffun := fsfun_of_can_ffun fmapP.

Lemma of_ffunE x : of_ffun x = odflt (default x) (omap h (insub x)).
Proof.
rewrite /fun_of_fsfun /=.
case: insubP => /= [u _ <-|xNS]; last first.
  case: fndP => //= kf; rewrite !ffunE /=.
  by set y := (X in h X); rewrite (valP y) in xNS.
case: fndP => /= [kf|].
  by rewrite ffunE; congr (h _); apply/val_inj => //.
by rewrite inE /= -topredE /= negbK => /eqP ->.
Qed.

End FsfunOfFinfun.
End Fsfun.

Fact fsfun_key : unit. Proof. exact: tt. Qed.

Definition fsfun_of_ffun (K : choiceType) (V : eqType) (default : K -> V)
  key (S : {fset K}) (h : S -> V) := locked_with key (Fsfun.of_ffun default h).

Definition fsfun_choiceMixin (K V : choiceType) (d : K -> V) :=
  [choiceMixin of fsfun d by <:].
Canonical  fsfun_choiceType (K V : choiceType) (d : K -> V) :=
  ChoiceType (fsfun d) (fsfun_choiceMixin d).

Delimit Scope fsfun_scope with fsfun.

Notation "[ 'fsfun' 'of' default & key | x : aT => F ]" :=
  (fsfun_of_ffun default key (fun x : aT => F))
  (at level 0, x ident, only parsing) : fun_scope.

Notation "[ 'fsfun' 'of' default | x : aT => F ]" :=
  [fsfun of default & fsfun_key | x : aT => F]
  (at level 0, x ident, only parsing) : fun_scope.

Notation "[ 'fsfun' & key | x : aT => F ]" := [fsfun of _ & key | x : aT => F ]
  (at level 0, x ident, only parsing) : fun_scope.

Notation "[ 'fsfun' x : aT => F ]" := [fsfun of _ | x : aT => F ]
  (at level 0, x ident, only parsing) : fun_scope.

Notation "[ 'fsfun' 'of' default & key | : aT => F ]" :=
  [fsfun of default & key | _ : aT => F ]
  (at level 0, only parsing) : fun_scope.

Notation "[ 'fsfun' 'of' default | : aT => F ]" :=
  [fsfun of default | _ : aT => F ]
  (at level 0, only parsing) : fun_scope.

Notation "[ 'fsfun' & key | : aT => F ]" := [fsfun & key | _ : aT => F ]
  (at level 0, only parsing) : fun_scope.

Notation "[ 'fsfun' : aT => F ]" := [fsfun _ : aT => F ]
  (at level 0, only parsing) : fun_scope.

Notation "[ 'fsfun' 'of' default & key | x => F ]" :=
  [fsfun of default & key | x : _ => F ]
  (at level 0, x ident, only parsing) : fun_scope.

Notation "[ 'fsfun' 'of' default | x => F ]" :=
  [fsfun of default | x : _ => F ]
  (at level 0, x ident, only parsing) : fun_scope.

Notation "[ 'fsfun' & key | x => F ]" := [fsfun of _ & key | x : _ => F ]
  (at level 0, x ident, only parsing) : fun_scope.

Notation "[ 'fsfun' x => F ]" := [fsfun of _ | x : _ => F ]
  (at level 0, x ident, format "[ 'fsfun'  x  =>  F ]") : fun_scope.

Notation "[ 'fsfun' 'of' default & key | => F ]" :=
  [fsfun of default & key | _ => F]
  (at level 0, only parsing) : fun_scope.

Notation "[ 'fsfun' 'of' default | => F ]" := [fsfun of default | _ => F]
  (at level 0, only parsing) : fun_scope.

Notation "[ 'fsfun' & key | => F ]" := [fsfun of _ & key | => F]
  (at level 0, only parsing) : fun_scope.

Notation "[ 'fsfun' => F ]" := [fsfun of _ | => F]
  (at level 0, format "[ 'fsfun'  =>   F ]") : fun_scope.

Definition fsfun_of_fun (K : choiceType) (V : eqType)
  default key  (S : {fset K}) (h : K -> V) :=
  [fsfun of default & key | x : S => h (val x)].

Notation "[ 'fsfun' 'of' default & key | x 'in' aT => F ]" :=
  (fsfun_of_fun default key aT (fun x => F))
  (at level 0, x ident, only parsing) : fun_scope.

Notation "[ 'fsfun' 'of' default | x 'in' aT => F ]" :=
  [fsfun of default & fsfun_key | x in aT => F ]
  (at level 0, x ident, only parsing) : fun_scope.

Notation "[ 'fsfun' & key | x 'in' aT => F ]" := [fsfun of _ & key | x in aT => F ]
  (at level 0, x ident, only parsing) : fun_scope.

Notation "[ 'fsfun' x 'in' aT => F ]" := [fsfun of _ | x in aT => F ]
  (at level 0, x ident, format "[ 'fsfun'  x  'in'  aT  =>  F ]") : fun_scope.

Fact fsfun0_key : unit. Proof. exact: tt. Qed.
Notation "[ 'fsfun' 'of' default ]" := (fsfun_of_ffun default fsfun0_key [fmap])
  (at level 0, only parsing) : fun_scope.

Notation "[ 'fsfun' ]" := [fsfun of _]
 (at level 0, format "[ 'fsfun' ]") : fun_scope.

Section FsfunTheory.
Variables (K : choiceType) (V : eqType) (default : K -> V) (key : unit).

Lemma fsfun_ffun (S : {fset K}) (h : S -> V) (x : K) :
  [fsfun of default & key | a : S => h a] x =
  odflt (default x) (omap h (insub x)).
Proof. by rewrite locked_withE Fsfun.of_ffunE. Qed.

Lemma fsfun_fun (S : {fset K}) (h : K -> V) (x : K) :
  [fsfun of default & key | a in S => h a] x =
   if x \in S then h x else (default x).
Proof. by rewrite fsfun_ffun; case: insubP => //= [u -> ->|/negPf ->]. Qed.

Lemma fsfun0E : [fsfun of default] =1 default.
Proof. by move=> x; rewrite locked_withE Fsfun.of_ffunE insubF ?inE. Qed.

Definition fsfunE := (fsfun_fun, fsfun0E).

Lemma finsupp0 : finsupp [fsfun of default] = fset0.
Proof. by apply/fsetP => x; rewrite !inE mem_finsupp fsfunE eqxx. Qed.

Lemma fsfun0_inj : injective default -> injective [fsfun of default].
Proof. by move=> def_inj x y; rewrite !fsfunE => /def_inj. Qed.

Lemma in_finsupp0 x : x \in finsupp [fsfun of default] = false.
Proof. by rewrite finsupp0 inE. Qed.

End FsfunTheory.

Module Import FsfunInE2.
Definition inE := (inE, in_finsupp0).
End FsfunInE2.

Section FsfunIdTheory.

Variables (K : choiceType).
Implicit Types (f g : {fsfun x : K => x}).

Fact fsfun_comp_key : unit. Proof. exact: tt. Qed.
Definition fsfun_comp g f :=
  [fsfun of id & fsfun_comp_key | k in finsupp f `|` finsupp g => g (f k)].

Notation "g \o f" := (fsfun_comp g f) : fsfun_scope.

Lemma fscompE g f : (g \o f)%fsfun =1 g \o f.
Proof.
move=> k; rewrite fsfun_ffun; case: insubP => //= [u _ <- //|].
by rewrite inE => /norP [kNf kNg]; rewrite !fsfun_dflt.
Qed.

Lemma fscomp0f : left_id [fsfun of (@id K)] fsfun_comp.
Proof. by move=> f; apply/fsfunP=> k; rewrite fscompE /= fsfun0E. Qed.

Lemma fscompA : associative fsfun_comp.
Proof. by move=> f g h; apply/fsfunP => k; rewrite !fscompE /= !fscompE. Qed.

Lemma fscomp_inj g f : injective f -> injective g -> injective (g \o f)%fsfun.
Proof. by move=> f_inj g_inj k k'; rewrite !fscompE => /= /g_inj /f_inj. Qed.

Definition fsinjectiveb : pred {fsfun x : K => x} :=
  [pred f | (injectiveb [ffun a : finsupp f => f (val a)])
            && [forall a : finsupp f, f (val a) \in finsupp f]].

Let equivalent (Ps : seq Prop) :=
  if Ps is P0 :: Ps then
  let fix aux (P : Prop) (Qs : seq Prop) :=
      if Qs is Q :: Qs then (P -> Q) /\ (aux Q  Qs) else P -> P0
  in aux P0 Ps else True.

Lemma fsinjective_subproof f :
  equivalent [:: injective f
              ; let S := finsupp f in
                {in S &, injective f} /\ forall a : S, f (val a) \in S
              ; exists2 S : {fset K}, (finsupp f `<=` S)
                & {in S &, injective f} /\ forall a : S, f (val a) \in S].
Proof.
split => /= [f_inj|]; last split=> [[f_inj f_st]|[S fS [f_inj f_st]] a b].
- split=> [a b ? ?|a]; first exact: f_inj.
  rewrite mem_finsupp (inj_eq f_inj) -mem_finsupp; apply/valP.
- by exists (finsupp f)=> //; apply: fsubset_refl.
have Nfinsupp := contra (fsubsetP fS _).
wlog /andP [aS bNS] : a b / (a \in S) && (b \notin S) => [hwlog|]; last first.
  rewrite (fsfun_dflt (Nfinsupp _ bNS)) => fb_eq_a.
  by move: bNS; rewrite -fb_eq_a (f_st.[aS]).
have [[aS|aNS] [bS|bNS]] := (boolP (a \in S), boolP (b \in S)); first 3 last.
- by rewrite !fsfun_dflt // ?Nfinsupp.
- exact: f_inj.
- by apply: hwlog; rewrite aS.
by move=> fab; symmetry; apply: hwlog; rewrite // bS.
Qed.

Lemma fsinjectiveP f : reflect (injective f) (fsinjectiveb f).
Proof.
have [H1 [H2 H3]]:= fsinjective_subproof f.
rewrite /fsinjectiveb; apply: (iffP idP)=> [|].
  by move=> /andP [/fsfun_injective_inP ? /forallP ?]; apply/H3/H2.
by move=> /H1 [/fsfun_injective_inP ? /forallP ?]; apply/andP.
Qed.

Lemma fsinjectivebP f :
  reflect (exists2 S : {fset K}, (finsupp f `<=` S)
           & {in S &, injective f} /\ forall a : S, f (val a) \in S)
        (fsinjectiveb f).
Proof.
have [H1 [H2 H3]]:= fsinjective_subproof f.
by apply: (iffP (fsinjectiveP _)) => //; by move=> /H1 /H2.
Qed.

End FsfunIdTheory.

Definition inE := inE.
