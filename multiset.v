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
Require Import finmap.

(*****************************************************************************)
(* This file provides a representation of multisets based on fsfun           *)
(*   {mset T} == the type of multisets on a choiceType T                     *)
(* The following notations are in the %mset scope                            *)
(*             mset0 == the empty multiset                                   *)
(*          mset n a == the multiset with n times element a                  *)
(*          [mset a] == the singleton multiset {k} := mset 1 a               *)
(* [mset a1; ..; an] == the multiset obtained from the elements a1,..,an     *)
(*           A `&` B == the intersection of A and B (the min of each)        *)
(*           A `|` B == the union of A and B (the max of each)               *)
(*           A `+` B == the sum of A and B                                   *)
(*            a |` B == the union of singleton a and B                       *)
(*            a +` B == the addition of singleton a to B                     *)
(*           A `\` B == the difference A minus B                             *)
(*            A `\ b == A without one b                                      *)
(*           A `*` B == the product of A and B                               *)
(*  [disjoint A & B] := A `&` B == 0                                         *)
(*          A `<=` B == A is a sub-multiset of B                             *)
(*           A `<` B == A is a proper sub-multiset of B                      *)
(*****************************************************************************)

Delimit Scope mset_scope with mset.
Local Open Scope fset_scope.
Local Open Scope fmap_scope.
Local Open Scope mset_scope.
Local Open Scope nat_scope.

Definition multiset (T : choiceType) := {fsfun _ : T => 0 : nat}.
Definition multiset_of (T : choiceType) of phant T := @multiset T.
Notation "'{mset' T }" := (@multiset_of _ (Phant T))
  (format "'{mset'  T }") : mset_scope.

Notation "[ 'mset' & key | x 'in' aT => F ]" := ([fsfun & key | x in aT => F ] : {mset _})
  (at level 0, x ident, only parsing) : mset_scope.
Notation "[ 'mset' x 'in' aT => F ]" := ([fsfun x in aT => F ] : {mset _})
  (at level 0, x ident, format "[ 'mset'  x  'in'  aT  =>  F ]") : mset_scope.

Identity Coercion multiset_multiset_of : multiset_of >-> multiset.
Coercion fset_of_multiset (T : choiceType) (A : multiset T) : finSet T :=
  finsupp A.
Canonical multiset_predType (K : choiceType) :=  Eval hnf in mkPredType
  (@pred_of_finset K \o @fset_of_multiset K : multiset K -> pred K).
Canonical mset_finpredType (T: choiceType) :=
  mkFinPredType (multiset T) (fun _ _ => erefl).

Section MultisetOps.

Context {K : choiceType}.
Implicit Types (a b c : K) (A B C D : {mset K}) (s : seq K).

Definition mset0 : {mset K} := [fsfun].

Fact msetn_key : unit. Proof. exact: tt. Qed.
Definition msetn n a := [mset & msetn_key | x in [fset a] => n].

Fact seq_mset_key : unit. Proof. exact: tt. Qed.
Definition seq_mset (s : seq K) :=
  [mset & seq_mset_key | x in seq_fset s => count (pred1 x) s].

Fact msetU_key : unit. Proof. exact: tt. Qed.
Definition msetU A B := [mset & msetU_key | x in A `|` B => maxn (A x) (B x)].

Fact msetI_key : unit. Proof. exact: tt. Qed.
Definition msetI A B := [mset & msetI_key | x in A `|` B => minn (A x) (B x)].

Fact msetD_key : unit. Proof. exact: tt. Qed.
Definition msetD A B := [mset & msetD_key | x in A `|` B => A x + B x].

Fact msetB_key : unit. Proof. exact: tt. Qed.
Definition msetB A B := [mset & msetB_key | x in A `|` B => A x - B x].

Fact msetM_key : unit. Proof. exact: tt. Qed.
Definition msetM A B := [mset & msetM_key | x in A `*` B => A x.1 * B x.2].

Definition msubset A B := [forall x : A, A (val x) <= B (val x)].

Definition mproper A B := msubset A B && ~~ msubset B A.

Definition mdisjoint A B := (msetI A B == mset0).

End MultisetOps.

Notation "[ 'mset' a ]" := (msetn 1 a)
  (at level 0, a at level 99, format "[ 'mset'  a ]") : mset_scope.
Notation "[ 'mset' a : T ]" := [mset (a : T)]
  (at level 0, a at level 99, format "[ 'mset'  a   :  T ]") : mset_scope.
Notation "A `|` B" := (msetU A B) : mset_scope.
Notation "A `+` B" := (msetD A B) : mset_scope.
Notation "A `\` B" := (msetB A B) : mset_scope.
Notation "A `\ a" := (A `\` [mset a]) : mset_scope.
Notation "a |` A" := ([mset (a)] `|` A) : mset_scope.
Notation "a +` A" := ([mset (a)] `+` A) : mset_scope.
Notation "A `*` B" := (msetM A B) : mset_scope.

Notation "A `<=` B" := (msubset A B)
  (at level 70, no associativity) : mset_scope.

Notation "A `<` B" := (mproper A B)
  (at level 70, no associativity) : mset_scope.

(* This is left-associative due to historical limitations of the .. Notation. *)
Notation "[ 'mset' a1 ; a2 ; .. ; an ]" :=
  (msetD .. (a1 +` (msetn 1 a2)) .. (msetn 1 an))
  (at level 0, a1 at level 99,
   format "[ 'mset'  a1 ;  a2 ;  .. ;  an ]") : mset_scope.
Notation "A `&` B" := (msetI A B) : mset_scope.

Section MSetTheory.

Context {K : choiceType}.
Implicit Types (a b c : K) (A B C D : {mset K}) (s : seq K).

Lemma msetP {A B} : A =1 B <-> A = B.
Proof. exact: fsfunP. Qed.

Lemma in_mset a A : (a \in A) = (A a > 0).
Proof. by rewrite mem_finsupp lt0n. Qed.

Lemma mset_neq0 a A : (A a != 0) = (a \in A).
Proof. by rewrite mem_finsupp. Qed.

Lemma mset_eq0 a A : (A a == 0) = (a \notin A).
Proof. by rewrite mem_finsupp negbK. Qed.

Lemma mset_eq0P {a A} : reflect (A a = 0) (a \notin A).
Proof. by rewrite -mset_eq0; apply: eqP. Qed.

Lemma mset_gt0 a A : (A a > 0) = (a \in A).
Proof. by rewrite mem_finsupp lt0n. Qed.

Lemma mset_eqP {A B} : reflect (A =1 B) (A == B).
Proof. exact: (equivP eqP (iff_sym msetP)). Qed.

Lemma mset0E a : mset0 a = 0.
Proof. by rewrite /mset0 fsfunE. Qed.

Lemma msetnE n a b : (msetn n a) b = if b == a then n else 0.
Proof. by rewrite fsfunE inE. Qed.

Lemma msetnxx n a : (msetn n a) a = n. Proof. by rewrite msetnE eqxx. Qed.

Lemma msetE2 A B a :
 ((A `+` B) a = A a + B a) * ((A `|` B) a = maxn (A a) (B a))
* ((A `&` B) a = minn (A a) (B a)) * ((A `\` B) a = (A a) - (B a)).
Proof.
rewrite !fsfunE !inE -!mset_neq0; case: ifPn => //.
by rewrite negb_or !negbK => /andP [/eqP-> /eqP->].
Qed.

Lemma mset_seqE s a : (seq_mset s) a = count (pred1 a) s.
Proof. by rewrite fsfunE seq_fsetE; case: ifPn => // /count_memPn ->. Qed.

Lemma msetME A B (u : K * K) : (A `*` B) u = A u.1 * B u.2.
Proof.
rewrite !fsfunE inE; case: ifPn => //=.
by rewrite negb_and !memNfinsupp => /orP [] /eqP->; rewrite ?muln0.
Qed.

Lemma mset1DE a A b : (a +` A) b = (b == a) + A b.
Proof. by rewrite msetE2 msetnE; case: (b == a). Qed.

Lemma mset1UE a A b : (a |` A) b = maxn (b == a) (A b).
Proof. by rewrite msetE2 msetnE; case: (b == a). Qed.

Lemma msetB1E a A b : (A `\ a) b = (A b) - (b == a).
Proof. by rewrite msetE2 msetnE; case: (b == a). Qed.

Let msetE := (mset0E, msetE2, msetnE, msetnxx,
              mset1DE, mset1UE, msetB1E,
              mset_seqE, msetME).

Lemma in_mset0 a : a \in mset0 = false.
Proof. by rewrite in_mset !msetE. Qed.

Lemma in_msetn n a' a : a \in msetn n a' = (n > 0) && (a == a').
Proof. by rewrite in_mset msetE; case: (a == a'); rewrite ?andbT ?andbF. Qed.

Lemma in_mset1 a' a : a \in [mset a'] = (a == a').
Proof. by rewrite in_mset msetE; case: (a == _). Qed.

Lemma in_msetD A B a : (a \in A `+` B) = (a \in A) || (a \in B).
Proof. by rewrite !in_mset !msetE addn_gt0. Qed.

Lemma in_msetU A B a : (a \in A `|` B) = (a \in A) || (a \in B).
Proof. by rewrite !in_mset !msetE leq_max. Qed.

Lemma in_msetDU A B a : (a \in A `+` B) = (a \in A `|` B).
Proof. by rewrite in_msetU in_msetD. Qed.

Lemma in_msetI A B a : (a \in A `&` B) = (a \in A) && (a \in B).
Proof. by rewrite !in_mset msetE leq_min. Qed.

Lemma in_msetB A B a : (a \in A `\` B) = (B a < A a).
Proof. by rewrite -mset_neq0 msetE subn_eq0 ltnNge. Qed.

Lemma in_mset1U a' A a : (a \in a' |` A) = (a == a') || (a \in A).
Proof. by rewrite in_msetU in_mset msetE; case: (_ == _). Qed.

Lemma in_mset1D a' A a : (a \in a' +` A) = (a == a') || (a \in A).
Proof. by rewrite in_msetDU in_mset1U. Qed.

Lemma in_msetB1 A b a : (a \in A `\ b) = ((a == b) ==> (A a > 1)) && (a \in A).
Proof.
by rewrite in_msetB msetE in_mset; case: (_ == _); rewrite -?geq_max.
Qed.

Lemma in_msetM A B (u : K * K) : (u \in A `*` B) = (u.1 \in A) && (u.2 \in B).
Proof. by rewrite !mem_finsupp msetE muln_eq0 negb_or. Qed.

Definition in_msetE :=
  (in_mset0, in_mset1, in_msetn,
   in_mset1U, in_mset1D, in_msetB1,
   in_msetU, in_msetI, in_msetD, in_msetM
  ).

Let inE := (inE, in_msetE).

Lemma msetDC (A B : {mset K}) : A `+` B = B `+` A.
Proof. by apply/msetP=> a; rewrite !msetE addnC. Qed.

Lemma msetIC (A B : {mset K}) : A `&` B = B `&` A.
Proof. by apply/msetP=> a; rewrite !msetE minnC. Qed.

Lemma msetUC (A B : {mset K}) : A `|` B = B `|` A.
Proof. by apply/msetP => a; rewrite !msetE maxnC. Qed.

(* intersection *)

Lemma mset0I A : mset0 `&` A = mset0.
Proof. by apply/msetP => x; rewrite !msetE min0n. Qed.

Lemma msetI0 A : A `&` mset0 = mset0.
Proof. by rewrite msetIC mset0I. Qed.

Lemma msetIA A B C : A `&` (B `&` C) = A `&` B `&` C.
Proof. by apply/msetP=> x; rewrite !msetE minnA. Qed.

Lemma msetICA A B C : A `&` (B `&` C) = B `&` (A `&` C).
Proof. by rewrite !msetIA (msetIC A). Qed.

Lemma msetIAC A B C : A `&` B `&` C = A `&` C `&` B.
Proof. by rewrite -!msetIA (msetIC B). Qed.

Lemma msetIACA A B C D : (A `&` B) `&` (C `&` D) = (A `&` C) `&` (B `&` D).
Proof. by rewrite -!msetIA (msetICA B). Qed.

Lemma msetIid A : A `&` A = A.
Proof. by apply/msetP=> x; rewrite !msetE minnn. Qed.

Lemma msetIIl A B C : A `&` B `&` C = (A `&` C) `&` (B `&` C).
Proof. by rewrite msetIA !(msetIAC _ C) -(msetIA _ C) msetIid. Qed.

Lemma msetIIr A B C : A `&` (B `&` C) = (A `&` B) `&` (A `&` C).
Proof. by rewrite !(msetIC A) msetIIl. Qed.

(* union *)

Lemma mset0U A : mset0 `|` A = A.
Proof. by apply/msetP => x; rewrite !msetE max0n. Qed.

Lemma msetU0 A : A `|` mset0 = A.
Proof. by rewrite msetUC mset0U. Qed.

Lemma msetUA A B C : A `|` (B `|` C) = A `|` B `|` C.
Proof. by apply/msetP=> x; rewrite !msetE maxnA. Qed.

Lemma msetUCA A B C : A `|` (B `|` C) = B `|` (A `|` C).
Proof. by rewrite !msetUA (msetUC B). Qed.

Lemma msetUAC A B C : A `|` B `|` C = A `|` C `|` B.
Proof. by rewrite -!msetUA (msetUC B). Qed.

Lemma msetUACA A B C D : (A `|` B) `|` (C `|` D) = (A `|` C) `|` (B `|` D).
Proof. by rewrite -!msetUA (msetUCA B). Qed.

Lemma msetUid A : A `|` A = A.
Proof. by apply/msetP=> x; rewrite !msetE maxnn. Qed.

Lemma msetUUl A B C : A `|` B `|` C = (A `|` C) `|` (B `|` C).
Proof. by rewrite msetUA !(msetUAC _ C) -(msetUA _ C) msetUid. Qed.

Lemma msetUUr A B C : A `|` (B `|` C) = (A `|` B) `|` (A `|` C).
Proof. by rewrite !(msetUC A) msetUUl. Qed.

(* adjunction *)

Lemma mset0D A : mset0 `+` A = A.
Proof. by apply/msetP => x; rewrite !msetE add0n. Qed.

Lemma msetD0 A : A `+` mset0 = A.
Proof. by rewrite msetDC mset0D. Qed.

Lemma msetDA A B C : A `+` (B `+` C) = A `+` B `+` C.
Proof. by apply/msetP=> x; rewrite !msetE addnA. Qed.

Lemma msetDCA A B C : A `+` (B `+` C) = B `+` (A `+` C).
Proof. by rewrite !msetDA (msetDC B). Qed.

Lemma msetDAC A B C : A `+` B `+` C = A `+` C `+` B.
Proof. by rewrite -!msetDA (msetDC B). Qed.

Lemma msetDACA A B C D : (A `+` B) `+` (C `+` D) = (A `+` C) `+` (B `+` D).
Proof. by rewrite -!msetDA (msetDCA B). Qed.

(* adjunction, union and difference with one element *)

Lemma msetU1l x A b : x \in A -> x \in A `|` [mset b].
Proof. by move=> Ax; rewrite !inE Ax. Qed.

Lemma msetU1r A b : b \in A `|` [mset b].
Proof. by rewrite !inE eqxx orbT. Qed.

Lemma msetB1P x A b : reflect ((x = b -> A x > 1) /\ x \in A) (x \in A `\ b).
Proof.
rewrite !inE; apply: (iffP andP); first by move=> [/implyP Ax ->]; split => // /eqP.
by move=> [Ax ->]; split => //; apply/implyP => /eqP.
Qed.

Lemma msetB11 b A : (b \in A `\ b) = (A b > 1).
Proof. by rewrite inE eqxx /= in_mset -geq_max. Qed.

Lemma msetB1K a A : a \in A -> a +` (A `\ a) = A.
Proof.
move=> aA; apply/msetP=> x; rewrite !msetE subnKC //=.
by have [->|//] := altP eqP; rewrite mset_gt0.
Qed.

Lemma msetD1K a B : (a +` B) `\ a = B.
Proof. by apply/msetP => x; rewrite !msetE addKn. Qed.

Lemma msetU1K a B : a \notin B -> (a |` B) `\ a = B.
Proof.
move=> aB; apply/msetP=> x; rewrite !msetE.
have [->|] := altP eqP; first by rewrite (mset_eq0P _).
by rewrite max0n subn0.
Qed.

Lemma mset1U1 x B : x \in x |` B. Proof. by rewrite !inE eqxx. Qed.
Lemma mset1D1 x B : x \in x +` B. Proof. by rewrite !inE eqxx. Qed.

Lemma mset1Ur x a B : x \in B -> x \in a |` B.
Proof. by move=> Bx; rewrite !inE predU1r. Qed.
Lemma mset1Dr x a B : x \in B -> x \in a +` B.
Proof. by move=> Bx; rewrite !inE predU1r. Qed.

Lemma mset2P x a b : reflect (x = a \/ x = b) (x \in [mset a; b]).
Proof. by rewrite !inE; apply: (iffP orP) => [] [] /eqP; intuition. Qed.

Lemma in_mset2 x a b : (x \in [mset a; b]) = (x == a) || (x == b).
Proof. by rewrite !inE. Qed.

Lemma mset21 a b : a \in [mset a; b]. Proof. by rewrite mset1D1. Qed.

Lemma mset22 a b : b \in [mset a; b]. Proof. by rewrite in_mset2 eqxx orbT. Qed.

Lemma msetUP x A B : reflect (x \in A \/ x \in B) (x \in A `|` B).
Proof. by rewrite !inE; exact: orP. Qed.

Lemma msetDP x A B : reflect (x \in A \/ x \in B) (x \in A `+` B).
Proof. by rewrite !inE; exact: orP. Qed.

Lemma msetULVR x A B : x \in A `|` B -> (x \in A) + (x \in B).
Proof. by rewrite inE; case: (x \in A); [left|right]. Qed.

Lemma msetDLVR x A B : x \in A `+` B -> (x \in A) + (x \in B).
Proof. by rewrite inE; case: (x \in A); [left|right]. Qed.


(* distribute /cancel *)

Lemma msetIUr A B C : A `&` (B `|` C) = (A `&` B) `|` (A `&` C).
Proof. by apply/msetP=> x; rewrite !msetE minn_maxr. Qed.

Lemma msetIUl A B C : (A `|` B) `&` C = (A `&` C) `|` (B `&` C).
Proof. by apply/msetP=> x; rewrite !msetE minn_maxl. Qed.

Lemma msetUIr A B C : A `|` (B `&` C) = (A `|` B) `&` (A `|` C).
Proof. by apply/msetP=> x; rewrite !msetE maxn_minr. Qed.

Lemma msetUIl A B C : (A `&` B) `|` C = (A `|` C) `&` (B `|` C).
Proof. by apply/msetP=> x; rewrite !msetE maxn_minl. Qed.

Lemma msetUKC A B : (A `|` B) `&` A = A.
Proof. by apply/msetP=> x; rewrite !msetE maxnK. Qed.

Lemma msetUK A B : (B `|` A) `&` A = A.
Proof. by rewrite msetUC msetUKC. Qed.

Lemma msetKUC A B : A `&` (B `|` A) = A.
Proof. by rewrite msetIC msetUK. Qed.

Lemma msetKU A B : A `&` (A `|` B) = A.
Proof. by rewrite msetIC msetUKC. Qed.

Lemma msetIKC A B : (A `&` B) `|` A = A.
Proof. by apply/msetP=> x; rewrite !msetE minnK. Qed.

Lemma msetIK A B : (B `&` A) `|` A = A.
Proof. by rewrite msetIC msetIKC. Qed.

Lemma msetKIC A B : A `|` (B `&` A) = A.
Proof. by rewrite msetUC msetIK. Qed.

Lemma msetKI A B : A `|` (A `&` B) = A.
Proof. by rewrite msetIC msetKIC. Qed.

Lemma msetUKid A B : B `|` A `|` A = B `|` A.
Proof. by rewrite -msetUA msetUid. Qed.

Lemma msetUKidC A B : A `|` B `|` A = A `|` B.
Proof. by rewrite msetUAC msetUid. Qed.

Lemma msetKUid A B : A `|` (A `|` B) = A `|` B.
Proof. by rewrite msetUA msetUid. Qed.

Lemma msetKUidC A B : A `|` (B `|` A) = B `|` A.
Proof. by rewrite msetUCA msetUid. Qed.

Lemma msetIKid A B : B `&` A `&` A = B `&` A.
Proof. by rewrite -msetIA msetIid. Qed.

Lemma msetIKidC A B : A `&` B `&` A = A `&` B.
Proof. by rewrite msetIAC msetIid. Qed.

Lemma msetKIid A B : A `&` (A `&` B) = A `&` B.
Proof. by rewrite msetIA msetIid. Qed.

Lemma msetKIidC A B : A `&` (B `&` A) = B `&` A.
Proof. by rewrite msetICA msetIid. Qed.

Lemma msetDIr A B C : A `+` (B `&` C) = (A `+` B) `&` (A `+` C).
Proof. by apply/msetP=> x; rewrite !msetE addn_minr. Qed.

Lemma msetDIl A B C : (A `&` B) `+` C = (A `+` C) `&` (B `+` C).
Proof. by apply/msetP=> x; rewrite !msetE addn_minl. Qed.

Lemma msetDKIC A B : (A `+` B) `&` A = A.
Proof. by apply/msetP=> x; rewrite !msetE (minn_idPr _) // leq_addr. Qed.

Lemma msetDKI A B : (B `+` A) `&` A = A.
Proof. by rewrite msetDC msetDKIC. Qed.

Lemma msetKDIC A B : A `&` (B `+` A) = A.
Proof. by rewrite msetIC msetDKI. Qed.

Lemma msetKDI A B : A `&` (A `+` B) = A.
Proof. by rewrite msetDC msetKDIC. Qed.

(* adjunction / subtraction *)

Lemma msetDKB A : cancel (msetD A) (msetB^~ A).
Proof. by move=> B; apply/msetP => a; rewrite !msetE addKn. Qed.

Lemma msetDKBC A : cancel (msetD^~ A) (msetB^~ A).
Proof. by move=> B; rewrite msetDC msetDKB. Qed.

Lemma msetBSKl A B a : ((a +` A) `\` B) `\ a = A `\` B.
Proof.
apply/msetP=> b; rewrite !msetE; case: ifPn; rewrite ?add0n ?subn0 //.
by rewrite add1n subn1 subSKn.
Qed.

Lemma msetBDl C A B : (C `+` A) `\` (C `+` B) = A `\` B.
Proof. by apply/msetP=> a; rewrite !msetE subnDl. Qed.

Lemma msetBDr C A B : (A `+` C) `\` (B `+` C) = A `\` B.
Proof. by apply/msetP=> a; rewrite !msetE subnDr. Qed.

Lemma msetBDA A B C : B `\` (A `+` C) = B `\` A `\` C.
Proof. by apply/msetP=> a; rewrite !msetE subnDA. Qed.

Lemma msetUE A B C : msetU A B = A `+` (B `\` A).
Proof. by apply/msetP=> a; rewrite !msetE maxnE. Qed.

(* subset *)

Lemma msubsetP {A B} : reflect (forall x, A x <= B x) (A `<=` B).
Proof.
by apply: (iffP forallP)=> // ? x; case: (in_fsetP A x) => // /mset_eq0P->.
Qed.

Lemma msubset_subset {A B} : A `<=` B -> {subset A <= B}.
Proof.
by move=> /msubsetP AB x; rewrite !in_mset => ?; exact: (leq_trans _ (AB _)).
Qed.

Lemma msetB_eq0 (A B : {mset K}) : (A `\` B == mset0) = (A `<=` B).
Proof.
apply/mset_eqP/msubsetP => AB a;
by have := AB a; rewrite !msetE -subn_eq0 => /eqP.
Qed.

Lemma msubset_refl A : A `<=` A. Proof. exact/msubsetP. Qed.
Hint Resolve msubset_refl.

Lemma msubset_trans : transitive (@msubset K).
Proof.
move=> y x z /msubsetP xy /msubsetP yz ; apply/msubsetP => a.
by apply: (leq_trans (xy _)).
Qed.
Arguments msubset_trans {C A B} _ _ : rename.

Lemma msetUS C A B : A `<=` B -> C `|` A `<=` C `|` B.
Proof.
move=> sAB; apply/msubsetP=> x; rewrite !msetE.
by rewrite geq_max !leq_max leqnn (msubsetP sAB) orbT.
Qed.

Lemma msetDS C A B : A `<=` B -> C `+` A `<=` C `+` B.
Proof.
by move=> /msubsetP sAB; apply/msubsetP=> x; rewrite !msetE leq_add2l.
Qed.

Lemma msetSU C A B : A `<=` B -> A `|` C `<=` B `|` C.
Proof. by move=> sAB; rewrite -!(msetUC C) msetUS. Qed.

Lemma msetSD C A B : A `<=` B -> A `+` C `<=` B `+` C.
Proof. by move=> sAB; rewrite -!(msetDC C) msetDS. Qed.

Lemma msetUSS A B C D : A `<=` C -> B `<=` D -> A `|` B `<=` C `|` D.
Proof. by move=> /(msetSU B) /msubset_trans sAC /(msetUS C)/sAC. Qed.

Lemma msetDSS A B C D : A `<=` C -> B `<=` D -> A `+` B `<=` C `+` D.
Proof. by move=> /(msetSD B) /msubset_trans sAC /(msetDS C)/sAC. Qed.

Lemma msetIidPl {A B} : reflect (A `&` B = A) (A `<=` B).
Proof.
apply: (iffP msubsetP) => [?|<- a]; last by rewrite !msetE geq_min leqnn orbT.
by apply/msetP => a; rewrite !msetE (minn_idPl _).
Qed.

Lemma msetIidPr {A B} : reflect (A `&` B = B) (B `<=` A).
Proof. by rewrite msetIC; apply: msetIidPl. Qed.

Lemma msubsetIidl A B : (A `<=` A `&` B) = (A `<=` B).
Proof.
apply/msubsetP/msubsetP=> sAB a; have := sAB a; rewrite !msetE.
  by rewrite leq_min leqnn.
by move/minn_idPl->.
Qed.

Lemma msubsetIidr A B : (B `<=` A `&` B) = (B `<=` A).
Proof. by rewrite msetIC msubsetIidl. Qed.

Lemma msetUidPr A B : reflect (A `|` B = B) (A `<=` B).
Proof.
apply: (iffP msubsetP) => [AB|<- a]; last by rewrite !msetE leq_max leqnn.
by apply/msetP=> a; rewrite !msetE (maxn_idPr _).
Qed.

Lemma msetUidPl A B : reflect (A `|` B = A) (B `<=` A).
Proof. by rewrite msetUC; apply/msetUidPr. Qed.

Lemma msubsetUl A B : A `<=` A `|` B.
Proof. by apply/msubsetP=> a; rewrite !msetE leq_maxl. Qed.
Hint Resolve msubsetUl.

Lemma msubsetUr A B : B `<=` (A `|` B).
Proof. by rewrite msetUC. Qed.
Hint Resolve msubsetUr.

Lemma msubsetU1 x A : A `<=` (x |` A).
Proof. by rewrite msubsetUr. Qed.
Hint Resolve msubsetU1.

Lemma msubsetU A B C : (A `<=` B) || (A `<=` C) -> A `<=` (B `|` C).
Proof. by move=> /orP [] /msubset_trans ->. Qed.

Lemma eqEmsubset A B : (A == B) = (A `<=` B) && (B `<=` A).
Proof.
apply/eqP/andP => [<-|[/msubsetP AB /msubsetP BA]]; first by split.
by apply/msetP=> a; apply/eqP; rewrite eqn_leq AB BA.
Qed.

Lemma msubEproper A B : A `<=` B = (A == B) || (A `<` B).
Proof. by rewrite eqEmsubset -andb_orr orbN andbT. Qed.

Lemma mproper_sub A B : A `<` B -> A `<=` B.
Proof. by rewrite msubEproper orbC => ->. Qed.

Lemma eqVmproper A B : A `<=` B -> A = B \/ A `<` B.
Proof. by rewrite msubEproper => /predU1P. Qed.

Lemma mproperEneq A B : A `<` B = (A != B) && (A `<=` B).
Proof. by rewrite andbC eqEmsubset negb_and andb_orr andbN. Qed.

Lemma mproper_neq A B : A `<` B -> A != B.
Proof. by rewrite mproperEneq; case/andP. Qed.

Lemma eqEmproper A B : (A == B) = (A `<=` B) && ~~ (A `<` B).
Proof. by rewrite negb_and negbK andb_orr andbN eqEmsubset. Qed.

Lemma msub0set A : msubset mset0 A.
Proof. by apply/msubsetP=> x; rewrite msetE. Qed.
Hint Resolve msub0set.

Lemma msubset0 A : (A `<=` mset0) = (A == mset0).
Proof. by rewrite eqEmsubset msub0set andbT. Qed.

Lemma mproper0 A : (mproper mset0 A) = (A != mset0).
Proof. by rewrite /mproper msub0set msubset0. Qed.

Lemma mproperE A B : (A `<` B) = (A `<=` B) && ~~ (msubset B A).
Proof. by []. Qed.

Lemma mproper_sub_trans B A C : A `<` B -> B `<=` C -> A `<` C.
Proof.
move=> /andP [AB NBA] BC; rewrite /mproper (msubset_trans AB) //=.
by apply: contra NBA=> /(msubset_trans _)->.
Qed.

Lemma msub_proper_trans B A C :
  A `<=` B -> B `<` C -> A `<` C.
Proof.
move=> AB /andP [CB NCB]; rewrite /mproper (msubset_trans AB) //=.
by apply: contra NCB=> /msubset_trans->.
Qed.

Lemma msubset_neq0 A B : A `<=` B -> A != mset0 -> B != mset0.
Proof. by rewrite -!mproper0 => sAB /mproper_sub_trans->. Qed.

(* msub is a morphism *)

Lemma msetBDKC A B : A `<=` B -> A `+` (B `\` A) = B.
Proof. by move=> /msubsetP AB; apply/msetP=> a; rewrite !msetE subnKC. Qed.

Lemma msetBDK A B : A `<=` B -> B `\` A `+` A = B.
Proof. by move=> /msubsetP AB; apply/msetP => a; rewrite !msetE subnK. Qed.

Lemma msetBBK A B : A `<=` B -> B `\` (B `\` A) = A.
Proof. by move=> /msubsetP AB; apply/msetP => a; rewrite !msetE subKn. Qed.

Lemma msetBD1K A B a : A `<=` B -> A a < B a -> a +` (B `\` (a +` A)) = B `\` A.
Proof.
move=> /msubsetP AB ABa; apply/msetP => b; rewrite !msetE.
by case: ifP => //= /eqP->; rewrite !add1n subnSK.
Qed.

Lemma subset_msetBLR A B C : (msubset (A `\` B) C) = (A `<=` B `+` C).
Proof.
apply/msubsetP/msubsetP => [] sABC a;
by have := sABC a; rewrite !msetE ?leq_subLR.
Qed.

Lemma msetnP n x a : reflect (0 < n /\ x = a) (x \in msetn n a).
Proof. by do [apply: (iffP idP); rewrite !inE] => [/andP[]|[]] -> /eqP. Qed.

Lemma gt0_msetnP n x a : 0 < n -> reflect (x = a) (x \in msetn n a).
Proof. by move=> n_gt0; rewrite inE n_gt0 /=; exact: eqP. Qed.

Lemma msetn1 n a : a \in msetn n a = (n > 0).
Proof. by rewrite inE eqxx andbT. Qed.

Lemma mset1P x a : reflect (x = a) (x \in [mset a]).
Proof. by rewrite inE; exact: eqP. Qed.

Lemma mset11 a : a \in [mset a]. Proof. by rewrite inE /=. Qed.

Lemma msetn_inj n : n > 0 -> injective (@msetn K n).
Proof.
move=> n_gt0 a b eqsab; apply/(gt0_msetnP _ _ _ n_gt0).
by rewrite -eqsab inE n_gt0 eqxx.
Qed.

Lemma mset1UP x a B : reflect (x = a \/ x \in B) (x \in a |` B).
Proof. by rewrite !inE; exact: predU1P. Qed.

Lemma mset_cons a s : seq_mset (a :: s) = a +` (seq_mset s).
Proof. by apply/msetP=> x; rewrite !msetE /= eq_sym. Qed.

(* We need separate lemmas for the explicit enumerations since they *)
(* associate on the left.   *)

(* intersection *)

Lemma msetIP x A B : reflect (x \in A /\ x \in B) (x \in A `&` B).
Proof. by rewrite inE; apply: andP. Qed.

Lemma msetIS C A B : A `<=` B -> C `&` A `<=` C `&` B.
Proof.
move=> sAB; apply/msubsetP=> x; rewrite !msetE.
by rewrite leq_min !geq_min leqnn (msubsetP sAB) orbT.
Qed.

Lemma msetSI C A B : A `<=` B -> A `&` C `<=` B `&` C.
Proof. by move=> sAB; rewrite -!(msetIC C) msetIS. Qed.

Lemma msetISS A B C D : A `<=` C -> B `<=` D -> A `&` B `<=` C `&` D.
Proof. by move=> /(msetSI B) /msubset_trans sAC /(msetIS C) /sAC. Qed.

(* difference *)

Lemma msetSB C A B : A `<=` B -> A `\` C `<=` B `\` C.
Proof.
by move=> /msubsetP sAB; apply/msubsetP=> x; rewrite !msetE leq_sub2r.
Qed.

Lemma msetBS C A B : A `<=` B -> C `\` B `<=` C `\` A.
Proof.
by move=> /msubsetP sAB; apply/msubsetP=> x; rewrite !msetE leq_sub2l.
Qed.

Lemma msetBSS A B C D : A `<=` C -> D `<=` B -> A `\` B `<=` C `\` D.
Proof. by move=> /(msetSB B) /msubset_trans sAC /(msetBS C) /sAC. Qed.

Lemma msetB0 A : A `\` mset0 = A.
Proof. by apply/msetP=> x; rewrite !msetE subn0. Qed.

Lemma mset0B A : mset0 `\` A = mset0.
Proof. by apply/msetP=> x; rewrite !msetE sub0n. Qed.

Lemma msetBxx A : A `\` A = mset0.
Proof. by apply/msetP=> x; rewrite !msetE subnn. Qed.

(* other inclusions *)

Lemma msubsetIl A B : A `&` B `<=` A.
Proof. by apply/msubsetP=> x; rewrite msetE geq_minl. Qed.

Lemma msubsetIr A B : A `&` B `<=` B.
Proof. by apply/msubsetP=> x; rewrite msetE geq_minr. Qed.

Lemma msubsetDl A B : A `\` B `<=` A.
Proof. by apply/msubsetP=> x; rewrite msetE leq_subLR leq_addl. Qed.

Lemma msubD1set A x : A `\ x `<=` A.
Proof. by rewrite msubsetDl. Qed.

Hint Resolve msubsetIl msubsetIr msubsetDl msubD1set.

(* cardinal lemmas for msets *)

Lemma mem_mset1U a A : a \in A -> a |` A = A.
Proof.
rewrite in_mset => aA; apply/msetP => x; rewrite !msetE (maxn_idPr _) //.
by have [->|//] := altP eqP; rewrite (leq_trans _ aA).
Qed.

Lemma mem_msetD1 a A : a \notin A -> A `\ a = A.
Proof.
move=> /mset_eq0P aA; apply/msetP => x; rewrite !msetE.
by have [->|] := altP eqP; rewrite ?aA ?subn0.
Qed.

Lemma msetIn a A n : A `&` msetn n a = msetn (minn (A a) n) a.
Proof.
by apply/msetP => x; rewrite !msetE; have [->|] := altP eqP; rewrite ?minn0.
Qed.

Lemma msubIset A B C : (B `<=` A) || (C `<=` A) -> (B `&` C `<=` A).
Proof. by case/orP; apply: msubset_trans; rewrite (msubsetIl, msubsetIr). Qed.

Lemma msubsetI A B C : (A `<=` B `&` C) = (A `<=` B) && (A `<=` C).
Proof.
rewrite !(sameP msetIidPl eqP) msetIA; have [-> //| ] := altP (A `&` B =P A).
by apply: contraNF => /eqP <-; rewrite -msetIA -msetIIl msetIAC.
Qed.

Lemma msubsetIP A B C : reflect (A `<=` B /\ A `<=` C) (A `<=` B `&` C).
Proof. by rewrite msubsetI; exact: andP. Qed.

Lemma msubUset A B C : (B `|` C `<=` A) = (B `<=` A) && (C `<=` A).
Proof.
apply/idP/idP => [subA|/andP [AB CA]]; last by rewrite -[A]msetUid msetUSS.
by rewrite !(msubset_trans _ subA).
Qed.

Lemma msubUsetP A B C : reflect (A `<=` C /\ B `<=` C) (A `|` B `<=` C).
Proof. by rewrite msubUset; exact: andP. Qed.

Lemma msetU_eq0 A B : (A `|` B == mset0) = (A == mset0) && (B == mset0).
Proof. by rewrite -!msubset0 msubUset. Qed.

Lemma setD_eq0 A B : (A `\` B == mset0) = (A `<=` B).
Proof. by rewrite -msubset0 subset_msetBLR msetD0. Qed.

End MSetTheory.
