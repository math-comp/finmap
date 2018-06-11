From mathcomp
Require Import ssreflect ssrbool eqtype ssrfun ssrnat choice seq.
From mathcomp
Require Import fintype tuple bigop path.

From mathcomp
Require Import order.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Reserved Notation "x \subset y" (at level 70, y at next level).
Reserved Notation "x \contains y" (at level 70, y at next level, only parsing).
Reserved Notation "x \proper y" (at level 70, y at next level).
Reserved Notation "x \containsproper y" (at level 70, y at next level, only parsing).
Reserved Notation "x \subset y :> T" (at level 70, y at next level).
Reserved Notation "x \contains y :> T" (at level 70, y at next level, only parsing).
Reserved Notation "x \proper y :> T" (at level 70, y at next level).
Reserved Notation "x \containsproper y :> T" (at level 70, y at next level, only parsing).
Reserved Notation "\subsets y" (at level 35).
Reserved Notation "\supersets y" (at level 35).
Reserved Notation "\propersets y" (at level 35).
Reserved Notation "\superpropersets y" (at level 35).
Reserved Notation "\subsets y :> T" (at level 35, y at next level).
Reserved Notation "\supersets y :> T" (at level 35, y at next level).
Reserved Notation "\propersets y :> T" (at level 35, y at next level).
Reserved Notation "\superpropersets y :> T" (at level 35, y at next level).

Reserved Notation "x \subset y \subset z" (at level 70, y, z at next level).
Reserved Notation "x \proper y \subset z" (at level 70, y, z at next level).
Reserved Notation "x \subset y \proper z" (at level 70, y, z at next level).
Reserved Notation "x \proper y \proper z" (at level 70, y, z at next level).
Reserved Notation "x \subset y ?= 'iff' c" (at level 70, y, c at next level,
  format "x '[hv'  \subset  y '/'  ?=  'iff'  c ']'").
Reserved Notation "x \subset y ?= 'iff' c :> T" (at level 70, y, c at next level,
  format "x '[hv'  \subset  y '/'  ?=  'iff'  c  :> T ']'").

Reserved Notation "~: A" (at level 35, right associativity).
Reserved Notation "[ 'set' ~ a ]" (at level 0, format "[ 'set' ~  a ]").
Reserved Notation "[ 'set' a1 ; a2 ; .. ; an ]"
 (at level 0, a1 at level 99, format "[ 'set'  a1 ;  a2 ;  .. ;  an ]").

Delimit Scope abstract_set_scope with set.
Local Open Scope abstract_set_scope.

Module SET.
Import Order.Theory Order.Syntax Order.Def.

Fact display_set : unit -> unit. Proof. exact. Qed.

Module Import SetSyntax.

Notation "\sub%set" := (@le (display_set _) _) : abstract_set_scope.
Notation "\super%set" := (@ge (display_set _) _) : abstract_set_scope.
Notation "\proper%set" := (@lt (display_set _) _) : abstract_set_scope.
Notation "\superproper%set" := (@gt (display_set _) _) : abstract_set_scope.
Notation "\sub?%set" := (@leif (display_set _) _) : abstract_set_scope.

Notation "\subsets y" := (\super%set y) : abstract_set_scope.
Notation "\subsets y :> T" := (\subsets (y : T)) : abstract_set_scope.
Notation "\supersets y"  := (\sub%set y) : abstract_set_scope.
Notation "\supersets y :> T" := (\supersets (y : T)) : abstract_set_scope.

Notation "\propersets y" := (\superproper%set y) : abstract_set_scope.
Notation "\propersets y :> T" := (\propersets (y : T)) : abstract_set_scope.
Notation "\superpropersets y" := (\proper%set y) : abstract_set_scope.
Notation "\superpropersets y :> T" := (\superpropersets (y : T)) : abstract_set_scope.

Notation "x \subset y" := (\sub%set x y) : abstract_set_scope.
Notation "x \subset y :> T" := ((x : T) \subset (y : T)) : abstract_set_scope.
(* Notation "x \contains y" := (y \subset x) (only parsing) : abstract_set_scope. *)
(* Notation "x \contains y :> T" := ((x : T) \contains (y : T)) (only parsing) : abstract_set_scope. *)

Notation "x \proper y"  := (\proper%set x y) : abstract_set_scope.
Notation "x \proper y :> T" := ((x : T) \proper (y : T)) : abstract_set_scope.
(* Notation "x \containsproper y"  := (y \proper x) (only parsing) : abstract_set_scope. *)
(* Notation "x \containsproper y :> T" := ((x : T) \containsproper (y : T)) (only parsing) : abstract_set_scope *)

Notation "x \subset y \subset z" := ((x \subset y)%set && (y \subset z)%set) : abstract_set_scope.
Notation "x \proper y \subset z" := ((x \proper y)%set && (y \subset z)%set) : abstract_set_scope.
Notation "x \subset y \proper z" := ((x \subset y)%set && (y \proper z)%set) : abstract_set_scope.
Notation "x \proper y \proper z" := ((x \proper y)%set && (y \proper z)%set) : abstract_set_scope.

Notation "x \subset y ?= 'iff' C" := (\sub?%set x y C) : abstract_set_scope.
Notation "x \subset y ?= 'iff' C :> R" := ((x : R) \subset (y : R) ?= iff C)
  (only parsing) : abstract_set_scope.

Notation set0 := (@bottom (display_set _) _).
Notation setT := (@top (display_set _) _).
Notation setU := (@join (display_set _) _).
Notation setI := (@meet (display_set _) _).
Notation setD := (@sub (display_set _) _).
Notation setC := (@compl (display_set _) _).

Notation "x :&: y" := (setI x y).
Notation "x :|: y" := (setU x y).
Notation "x :\: y" := (setD x y).
Notation "~: x"    := (setC x).

Notation "x \subset y" := (\sub%set x y) : bool_scope.
Notation "x \proper y" := (\proper%set x y) : bool_scope.
End SetSyntax.

Module Semiset.
Section ClassDef.
Variable elementType : Type. (* Universe type *)
Variable eqType_of_elementType : elementType -> eqType.
Coercion eqType_of_elementType : elementType >-> eqType.
Implicit Types (X Y : elementType).

Structure mixin_of d (set : elementType -> (cblatticeType (display_set d))) :=
  Mixin {
  memset : forall X, set X -> X -> bool;
  set1 : forall X, X -> set X;
  _ : forall X (x : X), ~~ memset set0 x; (* set0 is empty instead *)
  _ : forall X (x y : X), memset (set1 y) x = (x == y);
  _ : forall X (x : X) A, (set1 x \subset A) = (memset A x);
  _ : forall X (A : set X), (set0 \proper A) -> {x | memset A x} ; (* exists or sig ?? *)
  _ : forall X (A B : set X), {subset memset A <= memset B} -> A \subset B;
  _ : forall X (x : X) A B, (memset (A :|: B) x) =
                    (memset A x) || (memset B x);
  (* there is no closure in a set *)

  funsort : elementType -> elementType -> Type;
  fun_of_funsort : forall X Y, funsort X Y -> X -> Y;
  imset : forall X Y, funsort X Y -> set X -> set Y;
  _ : forall X Y (f : funsort X Y) (A : set X) (y : Y),
    reflect (exists2 x : X, memset A x & y = fun_of_funsort f x)
            (memset (imset f A) y)
}.

Record class_of d (set : elementType -> Type) := Class {
  base  : forall X, @Order.CBLattice.class_of (display_set d) (set X);
  mixin : mixin_of (fun X => Order.CBLattice.Pack (base X) (set X))
}.

Local Coercion base : class_of >-> Funclass.

Structure type d := Pack { sort ; _ : class_of d sort;
                         _ : elementType -> Type }.

Local Coercion sort : type >-> Funclass.

Variables (set : elementType -> Type) (disp : unit) (cT : type disp).

Definition class := let: Pack _ c _ as cT' := cT return class_of _ cT' in c.
Definition clone disp' c of (disp = disp') & phant_id class c :=
  @Pack disp' set c set.
Let xset := let: Pack set _ _ := cT in set.
Notation xclass := (class : class_of _ xset).

Definition pack b0
  (m0 : mixin_of
 (fun X=> @Order.CBLattice.Pack (display_set disp) (set X) (b0 X) (set X))) :=
  fun bT b &
 (forall X, phant_id (@Order.CBLattice.class (display_set disp) (bT X)) (b X)) =>
  fun    m & phant_id m0 m => Pack (@Class disp set b m) set.
End ClassDef.

Section CanonicalDef.
Variable elementType : Type.
Variable eqType_of_elementType : elementType -> eqType.
Coercion eqType_of_elementType : elementType >-> eqType.
Notation type := (type eqType_of_elementType).
Local Coercion base : class_of >-> Funclass.
Local Coercion sort : type >-> Funclass.
Variables (set : elementType -> Type) (X : elementType).
Variables (disp : unit) (cT : type disp).
Local Notation ddisp := (display_set disp).

Let xset := let: Pack set _ _ := cT in set.
Notation xclass := (@class _ eqType_of_elementType _ cT : class_of eqType_of_elementType _ xset).

Definition eqType := @Equality.Pack (cT X) (xclass X) (xset X).
Definition choiceType := @Choice.Pack (cT X) (xclass X) (xset X).
Definition porderType :=
 @Order.POrder.Pack ddisp (cT X) (xclass X) (xset X).
Definition latticeType :=
  @Order.Lattice.Pack ddisp (cT X) (xclass X) (xset X).
Definition blatticeType :=
  @Order.BLattice.Pack ddisp (cT X) (xclass X) (xset X).
Definition cblatticeType :=
  @Order.CBLattice.Pack ddisp (cT X) (xclass X) (xset X).
End CanonicalDef.

Module Import Exports.
Coercion mixin      : class_of >-> mixin_of.
Coercion base       : class_of >-> Funclass.
Coercion sort       : type >-> Funclass.
Coercion eqType     : type >-> Equality.type.
Coercion choiceType : type >-> Choice.type.
Coercion porderType : type >-> Order.POrder.type.
Coercion latticeType : type >-> Order.Lattice.type.
Coercion blatticeType : type >-> Order.BLattice.type.
Coercion cblatticeType : type >-> Order.CBLattice.type.

Canonical eqType.
Canonical choiceType.
Canonical porderType.
Canonical latticeType.
Canonical blatticeType.
Canonical cblatticeType.

Notation semisetType  := type.
Notation semisetMixin := mixin_of.
Notation SemisetMixin := Mixin.
Notation SemisetType set m := (@pack _ _ set _ _ m _ _ (fun=> id) _ id).

Notation "[ 'semisetType' 'of' set 'for' cset ]" := (@clone _ _ set _ cset _ _ erefl id)
  (at level 0, format "[ 'semisetType'  'of'  set  'for'  cset ]") : form_scope.
Notation "[ 'semisetType' 'of' set 'for' cset 'with' disp ]" :=
  (@clone _ _ set _ cset disp _ (unit_irrelevance _ _) id)
  (at level 0, format "[ 'semisetType'  'of'  set  'for'  cset  'with'  disp ]") : form_scope.
Notation "[ 'semisetType' 'of' set ]" := [semisetType of set for _]
  (at level 0, format "[ 'semisetType'  'of'  set ]") : form_scope.
Notation "[ 'semisetType' 'of' set 'with' disp ]" := [semisetType of set for _ with disp]
  (at level 0, format "[ 'semisetType'  'of'  set  'with' disp ]") : form_scope.

End Exports.
End Semiset.

Import Semiset.Exports.

Section SemisetOperations.
Context {elementType : Type} {eqType_of_elementType : elementType -> eqType}.
Coercion eqType_of_elementType : elementType >-> eqType.
Context {disp : unit}.

Section setfun.
Variable (set : semisetType eqType_of_elementType disp).
Definition setfun := Semiset.funsort (Semiset.class set).
Definition fun_of_setfun X Y (f : setfun X Y) : X -> Y :=
  @Semiset.fun_of_funsort _ _ _ _ (Semiset.class set) _ _ f.
Coercion fun_of_setfun : setfun >-> Funclass.
End setfun.
Context {set : semisetType eqType_of_elementType disp}.
Variable X Y : elementType.

Definition memset : set X -> X -> bool :=
  @Semiset.memset _ _ _ _ (Semiset.class set) _.
Definition set1 : X -> set X :=
  @Semiset.set1 _ _ _ _ (Semiset.class set) _.
Definition imset : setfun set X Y -> set X -> set Y:=
  @Semiset.imset _ _ _ _ (Semiset.class set) _ _.

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
  (at level 0, x at level 99, only parsing) : abstract_set_scope.
Notation "[ 'set' x | P ]" := [set x : _ | P]
  (at level 0, x, P at level 99, format "[ 'set'  x  |  P ]") : abstract_set_scope.
Notation "[ 'set' x 'in' A ]" := [set x | x \in A]
  (at level 0, x at level 99, format "[ 'set'  x  'in'  A ]") : abstract_set_scope.
Notation "[ 'set' x : T 'in' A ]" := [set x : T | x \in A]
  (at level 0, x at level 99, only parsing) : abstract_set_scope.
Notation "[ 'set' x : T | P & Q ]" := [set x : T | P && Q]
  (at level 0, x at level 99, only parsing) : abstract_set_scope.
Notation "[ 'set' x | P & Q ]" := [set x | P && Q ]
  (at level 0, x, P at level 99, format "[ 'set'  x  |  P  &  Q ]") : abstract_set_scope.
Notation "[ 'set' x : T 'in' A | P ]" := [set x : T | x \in A & P]
  (at level 0, x at level 99, only parsing) : abstract_set_scope.
Notation "[ 'set' x 'in' A | P ]" := [set x | x \in A & P]
  (at level 0, x at level 99, format "[ 'set'  x  'in'  A  |  P ]") : abstract_set_scope.
Notation "[ 'set' x 'in' A | P & Q ]" := [set x in A | P && Q]
  (at level 0, x at level 99,
   format "[ 'set'  x  'in'  A  |  P  &  Q ]") : abstract_set_scope.
Notation "[ 'set' x : T 'in' A | P & Q ]" := [set x : T in A | P && Q]
  (at level 0, x at level 99, only parsing) : abstract_set_scope.

Notation "[ 'set' a ]" := (set1 a)
  (at level 0, a at level 99, format "[ 'set'  a ]") : abstract_set_scope.
Notation "[ 'set' a : T ]" := [set (a : T)]
  (at level 0, a at level 99, format "[ 'set'  a   :  T ]") : abstract_set_scope.

Notation "a |: y" := ([set a] :|: y) : abstract_set_scope.
Notation "x :\ a" := (x :\: [set a]) : abstract_set_scope.
Notation "[ 'set' a1 ; a2 ; .. ; an ]" := (setU .. (a1 |: [set a2]) .. [set an]).

Notation "f @: A" := (imset f A) (at level 24) : abstract_set_scope.

End SemisetSyntax.


Module Import SemisetTheory.
Section SemisetTheory.

Variable elementType : Type.
Variable eqType_of_elementType : elementType -> eqType.
Coercion eqType_of_elementType : elementType >-> eqType.
Variable disp : unit.
Variable set : semisetType eqType_of_elementType disp.

Section setX.

Variables X : elementType.
Implicit Types (x y : X) (A B C : set X).

Lemma notin_set0 (x : X) : x \notin (set0 : set X).
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

Lemma sub1set x A : ([set x] \subset A) = (x \in A).
Proof.
rewrite /set1 /in_mem /= /memset.
case: set A => [S [base [memset set1 /= ? ? H ? ? ? ? ? ? ?]] ?] A /=.
exact: H.
Qed.

Lemma set_gt0_ex A : set0 \proper A -> {x | x \in A}.
Proof.
rewrite /set1 /in_mem /= /memset.
case: set A => [S [base [memset set1 /= ? ? ? H ? ? ? ? ? ?]] ?] A /=.
exact: H.
Qed.

Lemma subsetP_subproof A B : {subset A <= B} -> A \subset B.
Proof.
rewrite /set1 /in_mem /= /memset.
case: set A B => [S [base [memset set1 /= ? ? ? ? H ? ? ? ? ?]] ?] /=.
exact: H.
Qed.

Lemma in_setU (x : X) A B : (x \in A :|: B) = (x \in A) || (x \in B).
Proof.
rewrite /set1 /in_mem /= /memset.
case: set A B => [S [base [memset set1 /= ? ? ? ? ? H ? ? ? ?]] ?] /=.
exact: H.
Qed.

Lemma in_set0 x : x \in (set0 : set X) = false.
Proof. by rewrite (negPf (notin_set0 _)). Qed.

Lemma subsetP {A B} : reflect {subset A <= B} (A <= B)%O.
Proof.
apply: (iffP idP) => [sAB x xA|/subsetP_subproof//].
by rewrite -sub1set (le_trans _ sAB) // sub1set.
Qed.

Lemma setP A B : A =i B <-> A = B.
Proof.
split=> [eqAB|->//]; apply/eqP; rewrite eq_le.
gen have leAB : A B eqAB / A \subset B; last by rewrite !leAB.
by apply/subsetP => x; rewrite eqAB.
Qed.

Lemma set1_neq0 (x : X) : [set x] != set0 :> set X.
Proof. by apply/negP=> /eqP /setP /(_ x); rewrite in_set0 in_set1 eqxx. Qed.

Lemma set1_eq0 x : ([set x] == set0 :> set X) = false.
Proof. by rewrite (negPf (set1_neq0 _)). Qed.

Lemma set11 x : x \in ([set x] : set X).
Proof. by rewrite -sub1set. Qed.
Hint Resolve set11.

Lemma set1_inj : injective (@set1 _ _ _ set X).
Proof.
move=> x y /eqP; rewrite eq_le sub1set => /andP [].
by rewrite in_set1 => /eqP.
Qed.

Lemma set_0Vmem A : (A = set0) + {x : X | x \in A}.
Proof.
have [|AN0] := eqVneq A set0; [left|right] => //.
by move: AN0; rewrite -lt0x => /set_gt0_ex.
Qed.

Lemma set0Pn A : reflect (exists x, x \in A) (A != set0).
Proof.
have [->|[x xA]] := set_0Vmem A; rewrite ?eqxx -?lt0x.
  by constructor=> [[x]]; rewrite in_set0.
suff -> : set0 \proper A by constructor; exists x.
by move: xA; rewrite -sub1set => /(lt_le_trans _)->; rewrite ?lt0x ?set1_eq0.
Qed.

Lemma subset1 A x : (A \subset [set x]) = (A == [set x]) || (A == set0).
Proof.
symmetry; rewrite eq_le; have [] /= := boolP (A \subset [set x]); last first.
  by apply: contraNF => /eqP ->; rewrite ?le0x.
have [/eqP->|[y yA]] := set_0Vmem A; rewrite ?orbT // ?sub1set.
by move=> /subsetP /(_ _ yA); rewrite in_set1 => /eqP<-; rewrite yA.
Qed.

Lemma eq_set1 (x : X) A : (A == [set x]) = (set0 \proper A \subset [set x]).
Proof.
by rewrite subset1; have [->|?] := posxP A; rewrite 1?eq_sym ?set1_eq0 ?orbF.
Qed.

Lemma in_setI A B (x : X) : (x \in A :&: B) = (x \in A) && (x \in B).
Proof.
apply/idP/idP => [xAB|?]; last by rewrite -sub1set lexI !sub1set.
by rewrite (subsetP (leIr _ _) _ xAB) (subsetP (leIl _ _) _ xAB).
Qed.

Lemma set1U A x : [set x] :&: A = if x \in A then [set x] else set0.
Proof.
apply/setP => y; rewrite (fun_if (fun E => y \in E)) in_setI in_set1 in_set0.
by have [->|] := altP (y =P x); rewrite ?if_same //; case: (_ \in A).
Qed.

Lemma set1U_eq0 A x : ([set x] :&: A == set0) = (x \notin A).
Proof. by rewrite set1U; case: (x \in A); rewrite ?set1_eq0 ?eqxx. Qed.

Lemma in_setD A B x : (x \in A :\: B) = (x \notin B) && (x \in A).
Proof.
apply/idP/idP => [|/andP[xNB xA]]; last first.
  by rewrite -sub1set leBRL sub1set xA set1U_eq0.
rewrite -sub1set leBRL sub1set => /andP [-> dxB].
by rewrite -sub1set disj_le ?set1_eq0.
Qed.

Definition inE := ((in_set0, in_set1, in_setU, in_setI, in_setD), inE).

Definition subset_trans B A C := (@le_trans _ _ B A C).
Definition proper_trans B A C := (@lt_trans _ _ B A C).
Definition sub_proper_trans B A C := (@le_lt_trans _ _ B A C).
Definition proper_sub_trans B A C := (@lt_le_trans _ _ B A C).
Definition proper_sub A B := (@ltW _ _ A B).

Lemma properP A B : reflect (A \subset B /\ (exists2 x, x \in B & x \notin A))
                            (A \proper B).
Proof.
apply: (iffP idP)=> [ltAB|[leAB [x xB xNA]]].
  rewrite ltW //; split => //; have := lt0B ltAB; rewrite lt0x.
  by move => /set0Pn [x]; rewrite in_setD => /andP [xNA xB]; exists x.
rewrite lt_neqAle leAB andbT; apply: contraTneq xNA.
by move=> /setP /(_ x) ->; rewrite xB.
Qed.

Lemma set1P x y : reflect (x = y) (x \in ([set y] : set X)).
Proof. by rewrite in_set1; apply/eqP. Qed.

Lemma subset_eqP A B : reflect (A =i B) (A \subset B \subset A)%set.
Proof.
apply: (iffP andP) => [[AB BA] x|eqAB]; first by apply/idP/idP; apply: subsetP.
by split; apply/subsetP=> x; rewrite !eqAB.
Qed.

Lemma eqEsubset A B : (A == B) = (A \subset B) && (B \subset A).
Proof. exact: eq_le. Qed.

Lemma properE A B : A \proper B = (A \subset B) && ~~ (B \subset A).
Proof. by case: comparableP. Qed.

Lemma subEproper A B : A \subset B = (A == B) || (A \proper B).
Proof. exact: le_eqVlt. Qed.

Lemma eqVproper A B : A \subset B -> A = B \/ A \proper B.
Proof. by rewrite subEproper => /predU1P. Qed.

Lemma properEneq A B : A \proper B = (A != B) && (A \subset B).
Proof. exact: lt_neqAle. Qed.

Lemma proper_neq A B : A \proper B -> A != B.
Proof. by rewrite properEneq; case/andP. Qed.

Lemma eqEproper A B : (A == B) = (A \subset B) && ~~ (A \proper B).
Proof. by case: comparableP. Qed.

Lemma sub0set A : set0 \subset A.
Proof. by apply/subsetP=> x; rewrite inE. Qed.

Lemma subset0 A : (A \subset set0) = (A == set0).
Proof. by rewrite eqEsubset sub0set andbT. Qed.

Lemma proper0 A : (set0 \proper A) = (A != set0).
Proof. by rewrite properE sub0set subset0. Qed.

Lemma subset_neq0 A B : A \subset B -> A != set0 -> B != set0.
Proof. by rewrite -!proper0 => sAB /proper_sub_trans->. Qed.

Lemma setU1r x a B : x \in B -> x \in a |: B.
Proof. by move=> Bx; rewrite !inE predU1r. Qed.

Lemma setU1P x a B : reflect (x = a \/ x \in B) (x \in a |: B).
Proof. by rewrite !inE; apply: predU1P. Qed.

(* Lemma set_cons a s : [set x in a :: s] = a |: [set x in s]. *)
(* Proof. by apply/setP=> x; rewrite !inE. Qed. *)


(* We need separate lemmas for the explicit enumerations since they *)
(* associate on the left.                                           *)
Lemma set1Ul x A b : x \in A -> x \in A :|: [set b].
Proof. by move=> Ax; rewrite !inE Ax. Qed.

Lemma set1Ur A b : b \in A :|: [set b].
Proof. by rewrite !inE eqxx orbT. Qed.

Lemma setD1P x A b : reflect (x != b /\ x \in A) (x \in A :\ b).
Proof. by rewrite !inE; apply: andP. Qed.

Lemma in_setD1 x A b : (x \in A :\ b) = (x != b) && (x \in A) .
Proof. by rewrite !inE. Qed.

Lemma setD11 b A : (b \in A :\ b) = false.
Proof. by rewrite !inE eqxx. Qed.

Lemma setD1K a A : a \in A -> a |: (A :\ a) = A.
Proof. by move=> Aa; apply/setP=> x; rewrite !inE; case: eqP => // ->. Qed.

Lemma setU1K a B : a \notin B -> (a |: B) :\ a = B.
Proof.
by move/negPf=> nBa; apply/setP=> x; rewrite !inE; case: eqP => // ->.
Qed.

Lemma set2P x a b : reflect (x = a \/ x = b) (x \in ([set a; b] : set X)).
Proof. by rewrite !inE; apply: pred2P. Qed.

Lemma in_set2 x a b : (x \in ([set a; b] : set X)) = (x == a) || (x == b).
Proof. by rewrite !inE. Qed.

Lemma set21 a b : a \in ([set a; b] : set X).
Proof. by rewrite !inE eqxx. Qed.

Lemma set22 a b : b \in ([set a; b] : set X).
Proof. by rewrite !inE eqxx orbT. Qed.

Lemma setUP x A B : reflect (x \in A \/ x \in B) (x \in A :|: B).
Proof. by rewrite !inE; apply: orP. Qed.

Lemma setUC A B : A :|: B = B :|: A.
Proof. by apply/setP => x; rewrite !inE orbC. Qed.

Lemma setUS A B C : A \subset B -> C :|: A \subset C :|: B.
Proof.
move=> sAB; apply/subsetP=> x; rewrite !inE.
by case: (x \in C) => //; apply: (subsetP sAB).
Qed.

Lemma setSU A B C : A \subset B -> A :|: C \subset B :|: C.
Proof. by move=> sAB; rewrite -!(setUC C) setUS. Qed.

Lemma setUSS A B C D : A \subset C -> B \subset D -> A :|: B \subset C :|: D.
Proof. by move=> /(setSU B) /subset_trans sAC /(setUS C)/sAC. Qed.

Lemma set0U A : set0 :|: A = A.
Proof. by apply/setP => x; rewrite !inE orFb. Qed.

Lemma setU0 A : A :|: set0 = A.
Proof. by rewrite setUC set0U. Qed.

Lemma setUA A B C : A :|: (B :|: C) = A :|: B :|: C.
Proof. by apply/setP => x; rewrite !inE orbA. Qed.

Lemma setUCA A B C : A :|: (B :|: C) = B :|: (A :|: C).
Proof. by rewrite !setUA (setUC B). Qed.

Lemma setUAC A B C : A :|: B :|: C = A :|: C :|: B.
Proof. by rewrite -!setUA (setUC B). Qed.

Lemma setUACA A B C D : (A :|: B) :|: (C :|: D) = (A :|: C) :|: (B :|: D).
Proof. by rewrite -!setUA (setUCA B). Qed.

Lemma setUid A : A :|: A = A.
Proof. by apply/setP=> x; rewrite inE orbb. Qed.

Lemma setUUl A B C : A :|: B :|: C = (A :|: C) :|: (B :|: C).
Proof. by rewrite setUA !(setUAC _ C) -(setUA _ C) setUid. Qed.

Lemma setUUr A B C : A :|: (B :|: C) = (A :|: B) :|: (A :|: C).
Proof. by rewrite !(setUC A) setUUl. Qed.

(* intersection *)

(* setIdP is a generalisation of setIP that applies to comprehensions. *)
(* Lemma setIdP x pA pB : reflect (pA x /\ pB x) (x \in [set y | pA y & pB y]). *)
(* Proof. by rewrite !inE; apply: andP. Qed. *)

(* Lemma setId2P x pA pB pC : *)
(*   reflect [/\ pA x, pB x & pC x] (x \in [set y | pA y & pB y && pC y]). *)
(* Proof. by rewrite !inE; apply: and3P. Qed. *)

(* Lemma setIdE A pB : [set x in A | pB x] = A :&: [set x | pB x]. *)
(* Proof. by apply/setP=> x; rewrite !inE. Qed. *)

Lemma setIP x A B : reflect (x \in A /\ x \in B) (x \in A :&: B).
Proof. by rewrite !inE; apply: andP. Qed.

Lemma setIC A B : A :&: B = B :&: A.
Proof. by apply/setP => x; rewrite !inE andbC. Qed.

Lemma setIS A B C : A \subset B -> C :&: A \subset C :&: B.
Proof.
move=> sAB; apply/subsetP=> x; rewrite !inE.
by case: (x \in C) => //; apply: (subsetP sAB).
Qed.

Lemma setSI A B C : A \subset B -> A :&: C \subset B :&: C.
Proof. by move=> sAB; rewrite -!(setIC C) setIS. Qed.

Lemma setISS A B C D : A \subset C -> B \subset D -> A :&: B \subset C :&: D.
Proof. by move=> /(setSI B) /subset_trans sAC /(setIS C) /sAC. Qed.

Lemma set0I A : set0 :&: A = set0.
Proof. by apply/setP => x; rewrite !inE andFb. Qed.

Lemma setI0 A : A :&: set0 = set0.

Proof. by rewrite setIC set0I. Qed.

Lemma setIA A B C : A :&: (B :&: C) = A :&: B :&: C.
Proof. by apply/setP=> x; rewrite !inE andbA. Qed.

Lemma setICA A B C : A :&: (B :&: C) = B :&: (A :&: C).
Proof. by rewrite !setIA (setIC A). Qed.

Lemma setIAC A B C : A :&: B :&: C = A :&: C :&: B.
Proof. by rewrite -!setIA (setIC B). Qed.

Lemma setIACA A B C D : (A :&: B) :&: (C :&: D) = (A :&: C) :&: (B :&: D).
Proof. by rewrite -!setIA (setICA B). Qed.

Lemma setIid A : A :&: A = A.
Proof. by apply/setP=> x; rewrite inE andbb. Qed.

Lemma setIIl A B C : A :&: B :&: C = (A :&: C) :&: (B :&: C).
Proof. by rewrite setIA !(setIAC _ C) -(setIA _ C) setIid. Qed.

Lemma setIIr A B C : A :&: (B :&: C) = (A :&: B) :&: (A :&: C).
Proof. by rewrite !(setIC A) setIIl. Qed.

(* distribute /cancel *)

Lemma setIUr A B C : A :&: (B :|: C) = (A :&: B) :|: (A :&: C).
Proof. by apply/setP=> x; rewrite !inE andb_orr. Qed.

Lemma setIUl A B C : (A :|: B) :&: C = (A :&: C) :|: (B :&: C).
Proof. by apply/setP=> x; rewrite !inE andb_orl. Qed.

Lemma setUIr A B C : A :|: (B :&: C) = (A :|: B) :&: (A :|: C).
Proof. by apply/setP=> x; rewrite !inE orb_andr. Qed.

Lemma setUIl A B C : (A :&: B) :|: C = (A :|: C) :&: (B :|: C).
Proof. by apply/setP=> x; rewrite !inE orb_andl. Qed.

Lemma setUK A B : (A :|: B) :&: A = A.
Proof. by apply/setP=> x; rewrite !inE orbK. Qed.

Lemma setKU A B : A :&: (B :|: A) = A.
Proof. by apply/setP=> x; rewrite !inE orKb. Qed.

Lemma setIK A B : (A :&: B) :|: A = A.
Proof. by apply/setP=> x; rewrite !inE andbK. Qed.

Lemma setKI A B : A :|: (B :&: A) = A.
Proof. by apply/setP=> x; rewrite !inE andKb. Qed.

(* difference *)

Lemma setDP A B x : reflect (x \in A /\ x \notin B) (x \in A :\: B).
Proof. by rewrite inE andbC; apply: andP. Qed.

Lemma setSD A B C : A \subset B -> A :\: C \subset B :\: C.
Proof.
by move=> /subsetP AB; apply/subsetP => x; rewrite !inE => /andP[-> /AB].
Qed.

Lemma setDS A B C : A \subset B -> C :\: B \subset C :\: A.
Proof.
move=> /subsetP AB; apply/subsetP => x; rewrite !inE => /andP[].
by move=> /(contra (AB _)) ->.
Qed.

Lemma setDSS A B C D : A \subset C -> D \subset B -> A :\: B \subset C :\: D.
Proof. by move=> /(setSD B) /subset_trans sAC /(setDS C) /sAC. Qed.

Lemma setD0 A : A :\: set0 = A.
Proof. exact: subx0. Qed.

Lemma set0D A : set0 :\: A = set0.
Proof. exact: sub0x. Qed.

Lemma setDv A : A :\: A = set0.
Proof. exact: subxx. Qed.

Lemma setID A B : A :&: B :|: A :\: B = A.
Proof. exact: joinIB. Qed.

Lemma setDUl A B C : (A :|: B) :\: C = (A :\: C) :|: (B :\: C).
Proof. exact: subUx. Qed.

Lemma setDUr A B C : A :\: (B :|: C) = (A :\: B) :&: (A :\: C).
Proof. exact: subxU. Qed.

Lemma setDIl A B C : (A :&: B) :\: C = (A :\: C) :&: (B :\: C).
Proof. exact: subIx. Qed.

Lemma setIDA A B C : A :&: (B :\: C) = (A :&: B) :\: C.
Proof. exact: meetxB. Qed.

Lemma setIDAC A B C : (A :\: B) :&: C = (A :&: C) :\: B.
Proof. exact: meetBx. Qed.

Lemma setDIr A B C : A :\: (B :&: C) = (A :\: B) :|: (A :\: C).
Proof. exact: subxI. Qed.

Lemma setDDl A B C : (A :\: B) :\: C = A :\: (B :|: C).
Proof. exact: subBx. Qed.

Lemma setDDr A B C : A :\: (B :\: C) = (A :\: B) :|: (A :&: C).
Proof. exact: subxB. Qed.

(* powerset *)

(* Lemma powersetE A B : (A \in powerset B) = (A \subset B). *)
(* Proof. by rewrite inE. Qed. *)

(* Lemma powersetS A B : (powerset A \subset powerset B) = (A \subset B). *)
(* Proof. *)
(* apply/subsetP/idP=> [sAB | sAB C]; last by rewrite !inE => /subset_trans ->. *)
(* by rewrite -powersetE sAB // inE. *)
(* Qed. *)

(* Lemma powerset0 : powerset set0 = [set set0] :> {set {set T}}. *)
(* Proof. by apply/setP=> A; rewrite !inE subset0. Qed. *)

(* Lemma powersetT : powerset [set: T] = [set: {set T}]. *)
(* Proof. by apply/setP=> A; rewrite !inE subsetT. Qed. *)

(* Lemma setI_powerset P A : P :&: powerset A = P ::&: A. *)
(* Proof. by apply/setP=> B; rewrite !inE. Qed. *)

(* cardinal lemmas for sets *)

(* Lemma cardsE pA : #|[set x in pA]| = #|pA|. *)
(* Proof. exact/eq_card/in_set. Qed. *)

(* Lemma sum1dep_card pA : \sum_(x | pA x) 1 = #|[set x | pA x]|. *)
(* Proof. by rewrite sum1_card cardsE. Qed. *)

(* Lemma sum_nat_dep_const pA n : \sum_(x | pA x) n = #|[set x | pA x]| * n. *)
(* Proof. by rewrite sum_nat_const cardsE. Qed. *)

(* Lemma cards0 : #|@set0 T| = 0. *)
(* Proof. by rewrite cardsE card0. Qed. *)

(* Lemma cards_eq0 A : (#|A| == 0) = (A == set0). *)
(* Proof. by rewrite (eq_sym A) eqEcard sub0set cards0 leqn0. Qed. *)

(* Lemma set0Pn A : reflect (exists x, x \in A) (A != set0). *)
(* Proof. by rewrite -cards_eq0; apply: existsP. Qed. *)

(* Lemma card_gt0 A : (0 < #|A|) = (A != set0). *)
(* Proof. by rewrite lt0n cards_eq0. Qed. *)

(* Lemma cards0_eq A : #|A| = 0 -> A = set0. *)
(* Proof. by move=> A_0; apply/setP=> x; rewrite inE (card0_eq A_0). Qed. *)

(* Lemma cards1 x : #|[set x]| = 1. *)
(* Proof. by rewrite cardsE card1. Qed. *)

(* Lemma cardsUI A B : #|A :|: B| + #|A :&: B| = #|A| + #|B|. *)
(* Proof. by rewrite !cardsE cardUI. Qed. *)

(* Lemma cardsU A B : #|A :|: B| = (#|A| + #|B| - #|A :&: B|)%N. *)
(* Proof. by rewrite -cardsUI addnK. Qed. *)

(* Lemma cardsI A B : #|A :&: B| = (#|A| + #|B| - #|A :|: B|)%N. *)
(* Proof. by rewrite  -cardsUI addKn. Qed. *)

(* Lemma cardsT : #|[set: T]| = #|T|. *)
(* Proof. by rewrite cardsE. Qed. *)

(* Lemma cardsID B A : #|A :&: B| + #|A :\: B| = #|A|. *)
(* Proof. by rewrite !cardsE cardID. Qed. *)

(* Lemma cardsD A B : #|A :\: B| = (#|A| - #|A :&: B|)%N. *)
(* Proof. by rewrite -(cardsID B A) addKn. Qed. *)

(* Lemma cardsC A : #|A| + #|~: A| = #|T|. *)
(* Proof. by rewrite cardsE cardC. Qed. *)

(* Lemma cardsCs A : #|A| = #|T| - #|~: A|. *)
(* Proof. by rewrite -(cardsC A) addnK. Qed. *)

(* Lemma cardsU1 a A : #|a |: A| = (a \notin A) + #|A|. *)
(* Proof. by rewrite -cardU1; apply: eq_card=> x; rewrite !inE. Qed. *)

(* Lemma cards2 a b : #|[set a; b]| = (a != b).+1. *)
(* Proof. by rewrite -card2; apply: eq_card=> x; rewrite !inE. Qed. *)

(* Lemma cardsC1 a : #|[set~ a]| = #|T|.-1. *)
(* Proof. by rewrite -(cardC1 a); apply: eq_card=> x; rewrite !inE. Qed. *)

(* Lemma cardsD1 a A : #|A| = (a \in A) + #|A :\ a|. *)
(* Proof. *)
(* by rewrite (cardD1 a); congr (_ + _); apply: eq_card => x; rewrite !inE. *)
(* Qed. *)

(* other inclusions *)

Lemma subsetIl A B : A :&: B \subset A.
Proof. by apply/subsetP=> x; rewrite inE; case/andP. Qed.

Lemma subsetIr A B : A :&: B \subset B.
Proof. by apply/subsetP=> x; rewrite inE; case/andP. Qed.

Lemma subsetUl A B : A \subset A :|: B.
Proof. by apply/subsetP=> x; rewrite inE => ->. Qed.

Lemma subsetUr A B : B \subset A :|: B.
Proof. by apply/subsetP=> x; rewrite inE orbC => ->. Qed.

Lemma subsetU1 x A : A \subset x |: A.
Proof. exact: subsetUr. Qed.

Lemma subsetDl A B : A :\: B \subset A.
Proof. exact: leBx. Qed.

Lemma subD1set A x : A :\ x \subset A.
Proof. by rewrite subsetDl. Qed.

(* Lemma subsetDr A B : A :\: B \subset ~: B. *)
(* Proof. by rewrite setDE subsetIr. Qed. *)

(* Lemma cards1P A : reflect (exists x, A = [set x]) (#|A| == 1). *)
(* Proof. *)
(* apply: (iffP idP) => [|[x ->]]; last by rewrite cards1. *)
(* rewrite eq_sym eqn_leq card_gt0 => /andP[/set0Pn[x Ax] leA1]. *)
(* by exists x; apply/eqP; rewrite eq_sym eqEcard sub1set Ax cards1 leA1. *)
(* Qed. *)

(* Lemma powerset1 x : powerset [set x] = [set set0; [set x]]. *)
(* Proof. by apply/setP=> A; rewrite !inE subset1 orbC. Qed. *)

Lemma setIidPl A B : reflect (A :&: B = A) (A \subset B).
Proof.
apply: (iffP subsetP) => [sAB | <- x /setIP[] //].
by apply/setP=> x; rewrite inE; apply/andb_idr/sAB.
Qed.
Arguments setIidPl {A B}.

Lemma setIidPr A B : reflect (A :&: B = B) (B \subset A).
Proof. by rewrite setIC; apply: setIidPl. Qed.

(* Lemma cardsDS A B : B \subset A -> #|A :\: B| = (#|A| - #|B|)%N. *)
(* Proof. by rewrite cardsD => /setIidPr->. Qed. *)

Lemma setUidPl A B : reflect (A :|: B = A) (B \subset A).
Proof. exact: join_idPr. Qed.

Lemma setUidPr A B : reflect (A :|: B = B) (A \subset B).
Proof. by rewrite setUC; apply: setUidPl. Qed.

(* Lemma setDidPl A B : reflect (A :\: B = A) [disjoint A & B]. *)
(* Proof. by rewrite setDE disjoints_subset; apply: setIidPl. Qed. *)

Lemma subIset A B C : (B \subset A) || (C \subset A) -> (B :&: C \subset A).
Proof. by case/orP; apply: subset_trans; rewrite (subsetIl, subsetIr). Qed.

Lemma subsetI A B C : (A \subset B :&: C) = (A \subset B) && (A \subset C).
Proof.
rewrite !(sameP setIidPl eqP) setIA; have [-> //| ] := altP (A :&: B =P A).
by apply: contraNF => /eqP <-; rewrite -setIA -setIIl setIAC.
Qed.

Lemma subsetIP A B C : reflect (A \subset B /\ A \subset C) (A \subset B :&: C).
Proof. by rewrite subsetI; apply: andP. Qed.

Lemma subsetIidl A B : (A \subset A :&: B) = (A \subset B).
Proof. by rewrite subsetI lexx. Qed.

Lemma subsetIidr A B : (B \subset A :&: B) = (B \subset A).
Proof. by rewrite setIC subsetIidl. Qed.

(* Lemma powersetI A B : powerset (A :&: B) = powerset A :&: powerset B. *)
(* Proof. by apply/setP=> C; rewrite !inE subsetI. Qed. *)

Lemma subUset A B C : (B :|: C \subset A) = (B \subset A) && (C \subset A).
Proof. exact: leUx. Qed.

Lemma subsetU A B C : (A \subset B) || (A \subset C) -> A \subset B :|: C.
Proof. exact: lexU. Qed.

Lemma subUsetP A B C : reflect (A \subset C /\ B \subset C) (A :|: B \subset C).
Proof. by rewrite subUset; apply: andP. Qed.

(* Lemma subsetC A B : (A \subset ~: B) = (B \subset ~: A). *)
(* Proof. by rewrite -setCS setCK. Qed. *)

(* Lemma subCset A B : (~: A \subset B) = (~: B \subset A). *)
(* Proof. by rewrite -setCS setCK. Qed. *)

(* Lemma subsetD A B C : (A \subset B :\: C) = (A \subset B) && [disjoint A & C]. *)
(* Proof. by rewrite setDE subsetI -disjoints_subset. Qed. *)

Lemma subDset A B C : (A :\: B \subset C) = (A \subset B :|: C).
Proof. exact: leBLR. Qed.

(* Lemma subsetDP A B C : *)
(*   reflect (A \subset B /\ [disjoint A & C]) (A \subset B :\: C). *)
(* Proof. by rewrite subsetD; apply: andP. Qed. *)

Lemma setU_eq0 A B : (A :|: B == set0) = (A == set0) && (B == set0).
Proof. by rewrite -!subset0 subUset. Qed.

Lemma setD_eq0 A B : (A :\: B == set0) = (A \subset B).
Proof. by rewrite -subset0 subDset setU0. Qed.

(* Lemma setI_eq0 A B : (A :&: B == set0) = [disjoint A & B]. *)
(* Proof. by rewrite disjoints_subset -setD_eq0 setDE setCK. Qed. *)

(* Lemma disjoint_setI0 A B : [disjoint A & B] -> A :&: B = set0. *)
(* Proof. by rewrite -setI_eq0; move/eqP. Qed. *)

Lemma subsetD1 A B x : (A \subset B :\ x) = (A \subset B) && (x \notin A).
Proof.
rewrite andbC; have [xA|] //= := boolP (x \in A).
  by apply: contraTF isT => /subsetP /(_ x xA); rewrite !inE eqxx.
move=> xNA; apply/subsetP/subsetP => sAB y yA.
  by have:= sAB y yA; rewrite !inE => /andP[].
by rewrite !inE sAB // andbT; apply: contraNneq xNA => <-.
Qed.

Lemma subsetD1P A B x : reflect (A \subset B /\ x \notin A) (A \subset B :\ x).
Proof. by rewrite subsetD1; apply: andP. Qed.

Lemma properD1 A x : x \in A -> A :\ x \proper A.
Proof. by move=> Ax; rewrite properE subsetDl /= subsetD1 Ax andbF. Qed.

Lemma properIr A B : ~~ (B \subset A) -> A :&: B \proper B.
Proof. by move=> nsAB; rewrite properE subsetIr subsetI negb_and nsAB. Qed.

Lemma properIl A B : ~~ (A \subset B) -> A :&: B \proper A.
Proof. by move=> nsBA; rewrite properE subsetIl subsetI negb_and nsBA orbT. Qed.

Lemma properUr A B : ~~ (A \subset B) ->  B \proper A :|: B.
Proof. by rewrite properE subsetUr subUset lexx /= andbT. Qed.

Lemma properUl A B : ~~ (B \subset A) ->  A \proper A :|: B.
Proof. by move=> not_sBA; rewrite setUC properUr. Qed.

Lemma proper1set A x : ([set x] \proper A) -> (x \in A).
Proof. by move/proper_sub; rewrite sub1set. Qed.

Lemma properIset A B C : (B \proper A) || (C \proper A) -> (B :&: C \proper A).
Proof. by case/orP; apply: sub_proper_trans; rewrite (subsetIl, subsetIr). Qed.

Lemma properI A B C : (A \proper B :&: C) -> (A \proper B) && (A \proper C).
Proof.
move=> pAI; apply/andP.
by split; apply: (proper_sub_trans pAI); rewrite (subsetIl, subsetIr).
Qed.

Lemma properU A B C : (B :|: C \proper A) -> (B \proper A) && (C \proper A).
Proof.
move=> pUA; apply/andP.
by split; apply: sub_proper_trans pUA; rewrite (subsetUr, subsetUl).
Qed.

(* Lemma properD A B C : (A \proper B :\: C) -> (A \proper B) && [disjoint A & C]. *)
(* Proof. by rewrite setDE disjoints_subset => /properI/andP[-> /proper_sub]. Qed. *)

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

Lemma imset0 f : imset f set0 = set0.
Proof.
apply/setP => y; rewrite in_set0.
by apply/imsetP => [[x]]; rewrite in_set0.
Qed.

Lemma imset_eq0 f A : (imset f A == set0) = (A == set0).
Proof.
have [->|/set_gt0_ex [x xA]] := posxP A; first by rewrite imset0 eqxx.
by apply/set0Pn; exists (f x); rewrite mem_imset.
Qed.

Lemma imset_set1 f x : imset f [set x] = [set f x].
Proof.
apply/setP => y.
by apply/imsetP/set1P=> [[x' /set1P-> //]| ->]; exists x; rewrite ?set11.
Qed.

Lemma imsetS f A A' : A \subset A' -> imset f A \subset imset f A'.
Proof.
move=> leAB; apply/subsetP => y /imsetP [x xA ->].
by rewrite mem_imset // (subsetP leAB).
Qed.

Lemma imset_proper f A A' :
   {in A' &, injective f} -> A \proper A' -> imset f A \proper imset f A'.
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

Record class_of d (set : elementType -> Type) := Class {
  base  : forall X, Order.CTBLattice.class_of (display_set d) (set X);
  mixin : Semiset.mixin_of eqType_of_elementType
                           (fun X => Order.CBLattice.Pack (base X) (set X))
}.

Local Coercion base : class_of >-> Funclass.
Definition base2 d (set : elementType -> Type)
         (c : class_of d set) := Semiset.Class (@mixin _ set c).
Local Coercion base2 : class_of >-> Semiset.class_of.

(* Local Coercion base : class_of >-> Order.CBLattice.class_of. *)

Structure type d := Pack { sort ; _ : class_of d sort;
                         _ : elementType -> Type }.

Local Coercion sort : type >-> Funclass.

Variables (set : elementType -> Type) (disp : unit) (cT : type disp).

Definition class := let: Pack _ c _ as cT' := cT return class_of _ cT' in c.
(* Definition clone c of phant_id class c := @Pack set c set. *)
Let xset := let: Pack set _ _ := cT in set.
Notation xclass := (class : class_of xset).

Definition pack :=
  fun bT (b : forall X, Order.CTBLattice.class_of _ _)
      & (forall X, phant_id (@Order.CTBLattice.class disp (bT X)) (b X)) =>
  fun mT m & phant_id (@Semiset.class _ eqType_of_elementType mT)
                      (@Semiset.Class _ _ disp set b m) =>
  Pack (@Class _ set (fun x => b x) m) set.

End ClassDef.

Section CanonicalDef.
Variable elementType : Type.
Variable eqType_of_elementType : elementType -> eqType.
Coercion eqType_of_elementType : elementType >-> eqType.
Notation type := (type eqType_of_elementType).
Local Coercion sort : type >-> Funclass.
Local Coercion base : class_of >-> Funclass.
Local Coercion base2 : class_of >-> Semiset.class_of.
Variables (set : elementType -> Type) (X : elementType).
Variable (disp : unit) (cT : type disp).
Local Notation ddisp := (display_set disp).

Let xset := let: Pack set _ _ := cT in set.
Notation xclass := (@class _ eqType_of_elementType _ cT : class_of eqType_of_elementType _ xset).

Definition eqType := @Equality.Pack (cT X) (xclass X) (xset X).
Definition choiceType := @Choice.Pack (cT X) (xclass X) (xset X).
Definition porderType := @Order.POrder.Pack ddisp (cT X) (xclass X) (xset X).
Definition latticeType :=
  @Order.Lattice.Pack ddisp (cT X) (xclass X) (xset X).
Definition blatticeType :=
  @Order.BLattice.Pack ddisp (cT X) (xclass X) (xset X).
Definition cblatticeType :=
  @Order.CBLattice.Pack ddisp (cT X) (xclass X) (xset X).
Definition ctblatticeType :=
  @Order.CTBLattice.Pack ddisp (cT X) (xclass X) (xset X).
Definition semisetType := @Semiset.Pack _ _ disp cT xclass xset.
Definition semiset_ctblatticeType :=
  @Order.CTBLattice.Pack ddisp (semisetType X) (xclass X) (xset X).
End CanonicalDef.

Module Import Exports.
Coercion base      : class_of >-> Funclass.
Coercion base2     : class_of >-> Semiset.class_of.
Coercion sort      : type >-> Funclass.
Coercion eqType    : type >-> Equality.type.
Coercion choiceType : type >-> Choice.type.
Coercion porderType : type >-> Order.POrder.type.
Coercion latticeType : type >-> Order.Lattice.type.
Coercion blatticeType : type >-> Order.BLattice.type.
Coercion cblatticeType : type >-> Order.CBLattice.type.
Coercion ctblatticeType : type >-> Order.CTBLattice.type.
Coercion semisetType : type >-> Semiset.type.

Canonical eqType.
Canonical choiceType.
Canonical porderType.
Canonical latticeType.
Canonical blatticeType.
Canonical cblatticeType.
Canonical ctblatticeType.
Canonical semisetType.

Notation setType  := type.

Notation "[ 'setType' 'of' set ]" :=
  (@pack _ _ set _ _ _ (fun=> id) _ _ id)
  (at level 0, format "[ 'setType'  'of'  set ]") : form_scope.

End Exports.
End set.

Import set.Exports.

Module Import setTheory.
Section setTheory.

Variable elementType : Type.
Variable eqType_of_elementType : elementType -> eqType.
Coercion eqType_of_elementType : elementType >-> eqType.
Variable disp : unit.
Variable set : setType eqType_of_elementType disp.

Section setX.

Variables X : elementType.
Implicit Types (x y : X) (A B : set X).

(* Lemma subsetT A : A \subset setT. *)
(* Proof. by apply/subsetP=> x; rewrite inE. Qed. *)

(* Lemma subsetT_hint mA : subset mA (mem [set: T]). *)
(* Proof. by rewrite unlock; apply/pred0P=> x; rewrite !inE. Qed. *)
(* Hint Resolve subsetT_hint. *)

(* Lemma subTset A : (setT \subset A) = (A == setT). *)
(* Proof. by rewrite eqEsubset subsetT. Qed. *)

(* Lemma properT A : (A \proper setT) = (A != setT). *)
(* Proof. by rewrite properEneq subsetT andbT. Qed. *)

(* Lemma enum_setT : enum [set: T] = Finite.enum T. *)
(* Proof. by rewrite (eq_enum (in_set _)) enumT. Qed. *)

(* Lemma in_setC1 x a : (x \in [set~ a]) = (x != a). *)
(* Proof. by rewrite !inE. Qed. *)

(* Lemma setC11 x : (x \in [set~ x]) = false. *)
(* Proof. by rewrite !inE eqxx. Qed. *)

(* Lemma setTU A : setT :|: A = setT. *)
(* Proof. by apply/setP => x; rewrite !inE orTb. Qed. *)

(* Lemma setUT A : A :|: setT = setT. *)
(* Proof. by rewrite setUC setTU. Qed. *)

(* Lemma setTI A : setT :&: A = A. *)
(* Proof. by apply/setP => x; rewrite !inE andTb. Qed. *)

(* Lemma setIT A : A :&: setT = A. *)
(* Proof. by rewrite setIC setTI. Qed. *)

(* Lemma setCP x A : reflect (~ x \in A) (x \in ~: A). *)
(* Proof. by rewrite !inE; apply: negP. Qed. *)

(* Lemma in_setC x A : (x \in ~: A) = (x \notin A). *)
(* Proof. exact: in_set. Qed. *)

(* Lemma setCK : involutive (@setC T). *)
(* Proof. by move=> A; apply/setP=> x; rewrite !inE negbK. Qed. *)

(* Lemma setC_inj : injective (@setC T). *)
(* Proof. exact: can_inj setCK. Qed. *)


(* (* complement *) *)

(* Lemma subsets_disjoint A B : (A \subset B) = [disjoint A & ~: B]. *)
(* Proof. by rewrite subset_disjoint; apply: eq_disjoint_r => x; rewrite !inE. Qed. *)

(* Lemma disjoints_subset A B : [disjoint A & B] = (A \subset ~: B). *)
(* Proof. by rewrite subsets_disjoint setCK. Qed. *)

(* Lemma powersetCE A B : (A \in powerset (~: B)) = [disjoint A & B]. *)
(* Proof. by rewrite inE disjoints_subset. Qed. *)

(* Lemma setCS A B : (~: A \subset ~: B) = (B \subset A). *)
(* Proof. by rewrite !subsets_disjoint setCK disjoint_sym. Qed. *)

(* Lemma setCU A B : ~: (A :|: B) = ~: A :&: ~: B. *)
(* Proof. by apply/setP=> x; rewrite !inE negb_or. Qed. *)

(* Lemma setCI A B : ~: (A :&: B) = ~: A :|: ~: B. *)
(* Proof. by apply/setP=> x; rewrite !inE negb_and. Qed. *)

(* Lemma setUCr A : A :|: ~: A = setT. *)
(* Proof. by apply/setP=> x; rewrite !inE orbN. Qed. *)

(* Lemma setICr A : A :&: ~: A = set0. *)
(* Proof. by apply/setP=> x; rewrite !inE andbN. Qed. *)

(* Lemma setC0 : ~: set0 = [set: T]. *)
(* Proof. by apply/setP=> x; rewrite !inE. Qed. *)

(* Lemma setCT : ~: [set: T] = set0. *)
(* Proof. by rewrite -setC0 setCK. Qed. *)

(* Lemma setDE A B : A :\: B = A :&: ~: B. *)
(* Proof. by apply/setP => x; rewrite !inE andbC. Qed. *)

(* Lemma setDT A : A :\: setT = set0. *)
(* Proof. by apply/setP=> x; rewrite !inE. Qed. *)

(* Lemma setTD A : setT :\: A = ~: A. *)
(* Proof. by apply/setP=> x; rewrite !inE andbT. Qed. *)

(* Lemma setCD A B : ~: (A :\: B) = ~: A :|: B. *)
(* Proof. by rewrite !setDE setCI setCK. Qed. *)

End setX.

End setTheory.
End setTheory.


(* Module FinSemiset. *)
(* Section ClassDef. *)
(* Variable elementType : Type. *)
(* Variable eqType_of_elementType : elementType -> eqType. *)
(* Coercion eqType_of_elementType : elementType >-> eqType. *)
(* Implicit Types (X Y : elementType). *)

(* Structure mixin_of d (set : semisetType eqType_of_elementType d) := *)
(*   Mixin { *)
(*     card : forall X, set X -> nat; *)
(*     enum : forall X, set X -> seq X; *)
(*     overenum : forall X, set X -> seq X; *)
(*     _ : forall X (A : set X), enum A =i mem A; *)
(*     _ : forall X (A : set X), card A = size (enum A); *)
(*     _ : forall X (A : set X), {subset enum A <= overenum A}; *)
(*   }. *)

(* Record class_of d (set : elementType -> Type) := Class { *)
(*   base  : Semiset.class_of eqType_of_elementType (display_set d) set; *)
(*   mixin : mixin_of (Semiset.Pack base set) *)
(* }. *)

(* Local Coercion base : class_of >-> Semiset.class_of. *)

(* Structure type d := Pack { sort ; _ : class_of d sort; *)
(*                          _ : elementType -> Type }. *)

(* Local Coercion sort : type >-> Funclass. *)

(* Variables (set : elementType -> Type) (disp : unit) (cT : type disp). *)

(* Definition class := let: Pack _ c _ as cT' := cT return class_of _ cT' in c. *)
(* Definition clone disp' c of (disp = disp') & phant_id class c := *)
(*   @Pack disp' set c set. *)
(* Let xset := let: Pack set _ _ := cT in set. *)
(* Notation xclass := (class : class_of _ xset). *)

(* Definition pack b0 *)
(*   (m0 : mixin_of (@Semiset.Pack _ _ disp set b0 set)) := *)
(*   fun bT b & phant_id (@Semiset.class _ eqType_of_elementType disp bT) b => *)
(*   fun    m & phant_id m0 m => Pack (@Class disp set b m) set. *)

(* End ClassDef. *)

(* Section CanonicalDef. *)
(* Variable elementType : Type. *)
(* Variable eqType_of_elementType : elementType -> eqType. *)
(* Coercion eqType_of_elementType : elementType >-> eqType. *)
(* Notation type := (type eqType_of_elementType). *)
(* Local Coercion base : class_of >-> Funclass. *)
(* Local Coercion sort : type >-> Funclass. *)
(* Variables (set : elementType -> Type) (X : elementType). *)
(* Variables (disp : unit) (cT : type disp). *)
(* Local Notation ddisp := (display_set disp). *)

(* Let xset := let: Pack set _ _ := cT in set. *)
(* Notation xclass := (@class _ eqType_of_elementType _ cT : class_of eqType_of_elementType _ xset). *)

(* Definition eqType := @Equality.Pack (cT X) (xclass X) (xset X). *)
(* Definition choiceType := @Choice.Pack (cT X) (xclass X) (xset X). *)
(* Definition porderType := *)
(*  @Order.POrder.Pack ddisp (cT X) (xclass X) (xset X). *)
(* Definition latticeType := *)
(*   @Order.Lattice.Pack ddisp (cT X) (xclass X) (xset X). *)
(* Definition blatticeType := *)
(*   @Order.BLattice.Pack ddisp (cT X) (xclass X) (xset X). *)
(* Definition cblatticeType := *)
(*   @Order.CBLattice.Pack ddisp (cT X) (xclass X) (xset X). *)
(* End CanonicalDef. *)

(* Module Import Exports. *)
(* Coercion mixin      : class_of >-> mixin_of. *)
(* Coercion base       : class_of >-> Funclass. *)
(* Coercion sort       : type >-> Funclass. *)
(* Coercion eqType     : type >-> Equality.type. *)
(* Coercion choiceType : type >-> Choice.type. *)
(* Coercion porderType : type >-> Order.POrder.type. *)
(* Coercion latticeType : type >-> Order.Lattice.type. *)
(* Coercion blatticeType : type >-> Order.BLattice.type. *)
(* Coercion cblatticeType : type >-> Order.CBLattice.type. *)

(* Canonical eqType. *)
(* Canonical choiceType. *)
(* Canonical porderType. *)
(* Canonical latticeType. *)
(* Canonical blatticeType. *)
(* Canonical cblatticeType. *)

(* Notation semisetType  := type. *)
(* Notation semisetMixin := mixin_of. *)
(* Notation SemisetMixin := Mixin. *)
(* Notation SemisetType set m := (@pack _ _ _ set _ m _ _ (fun=> id) _ id). *)

(* Notation "[ 'semisetType' 'of' set 'for' cset ]" := (@clone _ _ set _ cset _ _ erefl id) *)
(*   (at level 0, format "[ 'semisetType'  'of'  set  'for'  cset ]") : form_scope. *)
(* Notation "[ 'semisetType' 'of' set 'for' cset 'with' disp ]" := *)
(*   (@clone _ _ set _ cset disp _ (unit_irrelevance _ _) id) *)
(*   (at level 0, format "[ 'semisetType'  'of'  set  'for'  cset  'with'  disp ]") : form_scope. *)
(* Notation "[ 'semisetType' 'of' set ]" := [semisetType of set for _] *)
(*   (at level 0, format "[ 'semisetType'  'of'  set ]") : form_scope. *)
(* Notation "[ 'semisetType' 'of' set 'with' disp ]" := [semisetType of set for _ with disp] *)
(*   (at level 0, format "[ 'semisetType'  'of'  set  'with' disp ]") : form_scope. *)

(* End Exports. *)
(* End Semiset. *)

(* Import Semiset.Exports. *)

(* Section SemisetOperations. *)
(* Context {elementType : Type} {eqType_of_elementType : elementType -> eqType}. *)
(* Coercion eqType_of_elementType : elementType >-> eqType. *)
(* Context {disp : unit}. *)

(* Section setfun. *)
(* Variable (set : semisetType eqType_of_elementType disp). *)
(* Definition setfun := Semiset.funsort (Semiset.class set). *)
(* Definition fun_of_setfun X Y (f : setfun X Y) : X -> Y := *)
(*   @Semiset.fun_of_funsort _ _ _ _ (Semiset.class set) _ _ f. *)
(* Coercion fun_of_setfun : setfun >-> Funclass. *)
(* End setfun. *)
(* Context {set : semisetType eqType_of_elementType disp}. *)
(* Variable X Y : elementType. *)

(* Definition memset : set X -> X -> bool := *)
(*   @Semiset.memset _ _ _ _ (Semiset.class set) _. *)
(* Definition set1 : X -> set X := *)
(*   @Semiset.set1 _ _ _ _ (Semiset.class set) _. *)
(* Definition imset : setfun set X Y -> set X -> set Y:= *)
(*   @Semiset.imset _ _ _ _ (Semiset.class set) _ _. *)

(* Canonical set_predType := Eval hnf in mkPredType memset. *)

(* Structure setpredType := SetPredType { *)
(*   setpred_sort :> Type; *)
(*   tosetpred : setpred_sort -> pred X; *)
(*   _ : {mem : setpred_sort -> mem_pred X | isMem tosetpred mem}; *)
(*   _ : {pred_fset : setpred_sort -> set X | *)
(*        forall p x, x \in pred_fset p = tosetpred p x} *)
(* }. *)

(* Canonical setpredType_predType (fpX : setpredType) := *)
(*   @PredType X (setpred_sort fpX) (@tosetpred fpX) *)
(*   (let: SetPredType _ _ mem _ := fpX in mem). *)

(* Definition predset (fpX : setpredType) : fpX -> set X := *)
(*   let: SetPredType _ _ _ (exist pred_fset _) := fpX in pred_fset. *)

(* End SemisetOperations. *)

(* Module Import SemisetSyntax. *)

(* Notation "[ 'set' x : T | P ]" := (predset (fun x : T => P%B)) *)
(*   (at level 0, x at level 99, only parsing) : abstract_set_scope. *)
(* Notation "[ 'set' x | P ]" := [set x : _ | P] *)
(*   (at level 0, x, P at level 99, format "[ 'set'  x  |  P ]") : abstract_set_scope. *)
(* Notation "[ 'set' x 'in' A ]" := [set x | x \in A] *)
(*   (at level 0, x at level 99, format "[ 'set'  x  'in'  A ]") : abstract_set_scope. *)
(* Notation "[ 'set' x : T 'in' A ]" := [set x : T | x \in A] *)
(*   (at level 0, x at level 99, only parsing) : abstract_set_scope. *)
(* Notation "[ 'set' x : T | P & Q ]" := [set x : T | P && Q] *)
(*   (at level 0, x at level 99, only parsing) : abstract_set_scope. *)
(* Notation "[ 'set' x | P & Q ]" := [set x | P && Q ] *)
(*   (at level 0, x, P at level 99, format "[ 'set'  x  |  P  &  Q ]") : abstract_set_scope. *)
(* Notation "[ 'set' x : T 'in' A | P ]" := [set x : T | x \in A & P] *)
(*   (at level 0, x at level 99, only parsing) : abstract_set_scope. *)
(* Notation "[ 'set' x 'in' A | P ]" := [set x | x \in A & P] *)
(*   (at level 0, x at level 99, format "[ 'set'  x  'in'  A  |  P ]") : abstract_set_scope. *)
(* Notation "[ 'set' x 'in' A | P & Q ]" := [set x in A | P && Q] *)
(*   (at level 0, x at level 99, *)
(*    format "[ 'set'  x  'in'  A  |  P  &  Q ]") : abstract_set_scope. *)
(* Notation "[ 'set' x : T 'in' A | P & Q ]" := [set x : T in A | P && Q] *)
(*   (at level 0, x at level 99, only parsing) : abstract_set_scope. *)

(* Notation "[ 'set' a ]" := (set1 a) *)
(*   (at level 0, a at level 99, format "[ 'set'  a ]") : abstract_set_scope. *)
(* Notation "[ 'set' a : T ]" := [set (a : T)] *)
(*   (at level 0, a at level 99, format "[ 'set'  a   :  T ]") : abstract_set_scope. *)

(* End SemisetSyntax. *)

(* Module Import SemisetTheory. *)
(* Section SemisetTheory. *)

(* Variable elementType : Type. *)
(* Variable eqType_of_elementType : elementType -> eqType. *)
(* Coercion eqType_of_elementType : elementType >-> eqType. *)
(* Variable disp : unit. *)
(* Variable set : semisetType eqType_of_elementType disp. *)

(* Section setX. *)

(* Variables X : elementType. *)
(* Implicit Types (x y : X) (A B : set X). *)

(* Lemma set1_neq0 (x : X) : [set x] != set0 :> set X. *)
(* Proof. *)
(* rewrite /set1 /in_mem /= /memset. *)
(* case: set => [S [base [memset set1 /= H ? ? ? ? ? ? ? ? ?]] ?] /=. *)
(* exact: H. *)
(* Qed. *)

(* Lemma in_set1 x y : x \in ([set y] : set X) = (x == y). *)
(* Proof. *)
(* rewrite /set1 /in_mem /= /memset. *)
(* case: set => [S [base [memset set1 /= ? H ? ? ? ? ? ? ? ?]] ?] /=. *)
(* exact: H. *)
(* Qed. *)

(* Lemma sub1set x A : ([set x] \subset A) = (x \in A). *)
(* Proof. *)
(* rewrite /set1 /in_mem /= /memset. *)
(* case: set A => [S [base [memset set1 /= ? ? H ? ? ? ? ? ? ?]] ?] A /=. *)
(* exact: H. *)
(* Qed. *)

(* Lemma set_gt0_ex A : set0 \proper A -> {x | x \in A}. *)
(* Proof. *)
(* rewrite /set1 /in_mem /= /memset. *)
(* case: set A => [S [base [memset set1 /= ? ? ? H ? ? ? ? ? ?]] ?] A /=. *)
(* exact: H. *)
(* Qed. *)

(* Lemma subsetP_subproof A B : {subset A <= B} -> A \subset B. *)
(* Proof. *)
(* rewrite /set1 /in_mem /= /memset. *)
(* case: set A B => [S [base [memset set1 /= ? ? ? ? H ? ? ? ? ?]] ?] /=. *)
(* exact: H. *)
(* Qed. *)

(* Lemma in_setU (x : X) A B : (x \in A :|: B) = (x \in A) || (x \in B). *)
(* Proof. *)
(* rewrite /set1 /in_mem /= /memset. *)
(* case: set A B => [S [base [memset set1 /= ? ? ? ? ? H ? ? ? ?]] ?] /=. *)
(* exact: H. *)
(* Qed. *)

(* Lemma set1_eq0 x : ([set x] == set0 :> set X) = false. *)
(* Proof. by rewrite (negPf (set1_neq0 _)). Qed. *)

(* Lemma in_set0 x : x \in (set0 : set X) = false. *)
(* Proof. by rewrite -sub1set lex0 set1_eq0. Qed. *)

(* Lemma set11 x : x \in ([set x] : set X). *)
(* Proof. by rewrite -sub1set. Qed. *)
(* Hint Resolve set11. *)

(* Lemma set1_inj : injective (@set1 _ _ _ set X). *)
(* Proof. *)
(* move=> x y /eqP; rewrite eq_le sub1set => /andP []. *)
(* by rewrite in_set1 => /eqP. *)
(* Qed. *)

(* Lemma set_0Vmem A : (A = set0) + {x : X | x \in A}. *)
(* Proof. *)
(* have [|AN0] := eqVneq A set0; [left|right] => //. *)
(* by move: AN0; rewrite -lt0x => /set_gt0_ex. *)
(* Qed. *)

(* Lemma set0Pn A : reflect (exists x, x \in A) (A != set0). *)
(* Proof. *)
(* have [->|[x xA]] := set_0Vmem A; rewrite ?eqxx -?lt0x. *)
(*   by constructor=> [[x]]; rewrite in_set0. *)
(* suff -> : set0 \proper A by constructor; exists x. *)
(* by move: xA; rewrite -sub1set => /(lt_le_trans _)->; rewrite ?lt0x ?set1_eq0. *)
(* Qed. *)

(* Lemma subsetP {A B} : reflect {subset A <= B} (A \subset B). *)
(* Proof. *)
(* apply: (iffP idP) => [sAB x xA|/subsetP_subproof//]. *)
(* by rewrite -sub1set (le_trans _ sAB) // sub1set. *)
(* Qed. *)

(* Lemma setP A B : A =i B <-> A = B. *)
(* Proof. *)
(* split; last by move->. *)
(* move=> eqAB; apply/eqP; rewrite eq_le. *)
(* gen have leAB : A B eqAB / A \subset B; last by rewrite !leAB. *)
(* by apply/subsetP => x; rewrite eqAB. *)
(* Qed. *)

(* Lemma subset1 A x : (A \subset [set x]) = (A == [set x]) || (A == set0). *)
(* Proof. *)
(* symmetry; rewrite eq_le; have [] /= := boolP (A \subset [set x]); last first. *)
(*   by apply: contraNF => /eqP ->; rewrite ?le0x. *)
(* have [/eqP->|[y yA]] := set_0Vmem A; rewrite ?orbT // ?sub1set. *)
(* by move=> /subsetP /(_ _ yA); rewrite in_set1 => /eqP<-; rewrite yA. *)
(* Qed. *)

(* Lemma eq_set1 (x : X) A : (A == [set x]) = (set0 \proper A \subset [set x]). *)
(* Proof. *)
(* by rewrite subset1; have [->|?] := posxP A; rewrite 1?eq_sym ?set1_eq0 ?orbF. *)
(* Qed. *)

(* Lemma in_setI A B (x : X) : (x \in A :&: B) = (x \in A) && (x \in B). *)
(* Proof. *)
(* apply/idP/idP => [xAB|?]; last by rewrite -sub1set lexI !sub1set. *)
(* by rewrite (subsetP (leIr _ _) _ xAB) (subsetP (leIl _ _) _ xAB). *)
(* Qed. *)

(* Lemma set1U A x : [set x] :&: A = if x \in A then [set x] else set0. *)
(* Proof. *)
(* apply/setP => y; rewrite (fun_if (fun E => y \in E)) in_setI in_set1 in_set0. *)
(* by have [->|] := altP (y =P x); rewrite ?if_same //; case: (_ \in A). *)
(* Qed. *)

(* Lemma set1U_eq0 A x : ([set x] :&: A == set0) = (x \notin A). *)
(* Proof. by rewrite set1U; case: (x \in A); rewrite ?set1_eq0 ?eqxx. Qed. *)

(* Lemma in_setD A B x : (x \in A :\: B) = (x \notin B) && (x \in A). *)
(* Proof. *)
(* apply/idP/idP => [|/andP[xNB xA]]; last first. *)
(*   by rewrite -sub1set leBRL sub1set xA set1U_eq0. *)
(* rewrite -sub1set leBRL sub1set => /andP [-> dxB]. *)
(* by rewrite -sub1set disj_le ?set1_eq0. *)
(* Qed. *)

(* Lemma properP A B : reflect (A \subset B /\ (exists2 x, x \in B & x \notin A)) *)
(*                             (A \proper B). *)
(* Proof. *)
(* apply: (iffP idP)=> [ltAB|[leAB [x xB xNA]]]. *)
(*   rewrite ltW //; split => //; have := lt0B ltAB; rewrite lt0x. *)
(*   by move => /set0Pn [x]; rewrite in_setD => /andP [xNA xB]; exists x. *)
(* rewrite lt_neqAle leAB andbT; apply: contraTneq xNA. *)
(* by move=> /setP /(_ x) ->; rewrite xB. *)
(* Qed. *)

(* Lemma set1P x y : reflect (x = y) (x \in ([set y] : set X)). *)
(* Proof. by rewrite in_set1; apply/eqP. Qed. *)

(* End setX. *)

(* Section setXY. *)

(* Variables X Y : elementType. *)
(* Implicit Types (x : X) (y : Y) (A : set X) (B : set Y) (f : setfun set X Y). *)

(* Lemma imsetP (f : setfun set X Y) A y : *)
(*     reflect (exists2 x : X, x \in A & y = f x) (y \in imset f A). *)
(* Proof. *)
(* move: A f; rewrite /set1 /in_mem /= /memset /imset /setfun. *)
(* case: set => [S [base [memset set1 /= ? ? ? ? ? ? ? ? ? H]]] ? /= A f. *)
(* exact: H. *)
(* Qed. *)

(* Lemma mem_imset f A x : x \in A -> f x \in imset f A. *)
(* Proof. by move=> Dx; apply/imsetP; exists x. Qed. *)

(* Lemma imset0 f : imset f set0 = set0. *)
(* Proof. *)
(* apply/setP => y; rewrite in_set0. *)
(* by apply/imsetP => [[x]]; rewrite in_set0. *)
(* Qed. *)

(* Lemma imset_eq0 f A : (imset f A == set0) = (A == set0). *)
(* Proof. *)
(* have [->|/set_gt0_ex [x xA]] := posxP A; first by rewrite imset0 eqxx. *)
(* by apply/set0Pn; exists (f x); rewrite mem_imset. *)
(* Qed. *)

(* Lemma imset_set1 f x : imset f [set x] = [set f x]. *)
(* Proof. *)
(* apply/setP => y. *)
(* by apply/imsetP/set1P=> [[x' /set1P-> //]| ->]; exists x; rewrite ?set11. *)
(* Qed. *)

(* Lemma imsetS f A A' : A \subset A' -> imset f A \subset imset f A'. *)
(* Proof. *)
(* move=> leAB; apply/subsetP => y /imsetP [x xA ->]. *)
(* by rewrite mem_imset // (subsetP leAB). *)
(* Qed. *)

(* Lemma imset_proper f A A' : *)
(*    {in A' &, injective f} -> A \proper A' -> imset f A \proper imset f A'. *)
(* Proof. *)
(* move=> injf /properP[sAB [x Bx nAx]]; rewrite lt_leAnge imsetS //=. *)
(* apply: contra nAx => sfBA. *)
(* have: f x \in imset f A by rewrite (subsetP sfBA) ?mem_imset. *)
(* by case/imsetP=> y Ay /injf-> //; apply: subsetP sAB y Ay. *)
(* Qed. *)

(* End setXY. *)

(* End SemisetTheory. *)
(* End SemisetTheory. *)

(* (* Module Import FinsetSemiset. *) *)
(* (* Section FinsetSemiset. *) *)
(* (* Variable *) *)

(* (* End FinsetSemiset. *) *)
(* (* End FinsetSemiset. *) *)

(* Module set. *)
(* Section ClassDef. *)
(* Variable elementType : Type. *)
(* Variable eqType_of_elementType : elementType -> eqType. *)
(* Coercion eqType_of_elementType : elementType >-> eqType. *)
(* Implicit Types (X Y : elementType). *)

(* Record class_of d (set : elementType -> Type) := Class { *)
(*   base  : forall X, Order.CTBLattice.class_of (display_set d) (set X); *)
(*   mixin : Semiset.mixin_of eqType_of_elementType *)
(*                            (fun X => Order.CBLattice.Pack (base X) (set X)) *)
(* }. *)

(* Local Coercion base : class_of >-> Funclass. *)
(* Definition base2 d (set : elementType -> Type) *)
(*          (c : class_of d set) := Semiset.Class (@mixin _ set c). *)
(* Local Coercion base2 : class_of >-> Semiset.class_of. *)

(* (* Local Coercion base : class_of >-> Order.CBLattice.class_of. *) *)

(* Structure type d := Pack { sort ; _ : class_of d sort; *)
(*                          _ : elementType -> Type }. *)

(* Local Coercion sort : type >-> Funclass. *)

(* Variables (set : elementType -> Type) (disp : unit) (cT : type disp). *)

(* Definition class := let: Pack _ c _ as cT' := cT return class_of _ cT' in c. *)
(* (* Definition clone c of phant_id class c := @Pack set c set. *) *)
(* Let xset := let: Pack set _ _ := cT in set. *)
(* Notation xclass := (class : class_of xset). *)

(* Definition pack := *)
(*   fun bT (b : forall X, Order.CTBLattice.class_of _ _) *)
(*       & (forall X, phant_id (@Order.CTBLattice.class disp (bT X)) (b X)) => *)
(*   fun mT m & phant_id (@Semiset.class _ eqType_of_elementType mT) *)
(*                       (@Semiset.Class _ _ disp set b m) => *)
(*   Pack (@Class _ set (fun x => b x) m) set. *)

(* End ClassDef. *)

(* Section CanonicalDef. *)
(* Variable elementType : Type. *)
(* Variable eqType_of_elementType : elementType -> eqType. *)
(* Coercion eqType_of_elementType : elementType >-> eqType. *)
(* Notation type := (type eqType_of_elementType). *)
(* Local Coercion sort : type >-> Funclass. *)
(* Local Coercion base : class_of >-> Funclass. *)
(* Local Coercion base2 : class_of >-> Semiset.class_of. *)
(* Variables (set : elementType -> Type) (X : elementType). *)
(* Variable (disp : unit) (cT : type disp). *)
(* Local Notation ddisp := (display_set disp). *)

(* Let xset := let: Pack set _ _ := cT in set. *)
(* Notation xclass := (@class _ eqType_of_elementType _ cT : class_of eqType_of_elementType _ xset). *)

(* Definition eqType := @Equality.Pack (cT X) (xclass X) (xset X). *)
(* Definition choiceType := @Choice.Pack (cT X) (xclass X) (xset X). *)
(* Definition porderType := @Order.POrder.Pack ddisp (cT X) (xclass X) (xset X). *)
(* Definition latticeType := *)
(*   @Order.Lattice.Pack ddisp (cT X) (xclass X) (xset X). *)
(* Definition blatticeType := *)
(*   @Order.BLattice.Pack ddisp (cT X) (xclass X) (xset X). *)
(* Definition cblatticeType := *)
(*   @Order.CBLattice.Pack ddisp (cT X) (xclass X) (xset X). *)
(* Definition ctblatticeType := *)
(*   @Order.CTBLattice.Pack ddisp (cT X) (xclass X) (xset X). *)
(* Definition semisetType := @Semiset.Pack _ _ disp cT xclass xset. *)
(* Definition semiset_ctblatticeType := *)
(*   @Order.CTBLattice.Pack ddisp (semisetType X) (xclass X) (xset X). *)
(* End CanonicalDef. *)

(* Module Import Exports. *)
(* Coercion base      : class_of >-> Funclass. *)
(* Coercion base2     : class_of >-> Semiset.class_of. *)
(* Coercion sort      : type >-> Funclass. *)
(* Coercion eqType    : type >-> Equality.type. *)
(* Coercion choiceType : type >-> Choice.type. *)
(* Coercion porderType : type >-> Order.POrder.type. *)
(* Coercion latticeType : type >-> Order.Lattice.type. *)
(* Coercion blatticeType : type >-> Order.BLattice.type. *)
(* Coercion cblatticeType : type >-> Order.CBLattice.type. *)
(* Coercion ctblatticeType : type >-> Order.CTBLattice.type. *)
(* Coercion semisetType : type >-> Semiset.type. *)

(* Canonical eqType. *)
(* Canonical choiceType. *)
(* Canonical porderType. *)
(* Canonical latticeType. *)
(* Canonical blatticeType. *)
(* Canonical cblatticeType. *)
(* Canonical ctblatticeType. *)
(* Canonical semisetType. *)

(* Notation setType  := type. *)

(* Notation "[ 'setType' 'of' set ]" := *)
(*   (@pack _ _ set _ _ _ (fun=> id) _ _ id) *)
(*   (at level 0, format "[ 'setType'  'of'  set ]") : form_scope. *)

(* End Exports. *)
(* End set. *)

(* Import set.Exports. *)

(* Module Import setTheory. *)
(* Section setTheory. *)

(* Variable elementType : Type. *)
(* Variable eqType_of_elementType : elementType -> eqType. *)
(* Coercion eqType_of_elementType : elementType >-> eqType. *)
(* Variable disp : unit. *)
(* Variable set : setType eqType_of_elementType disp. *)

(* Section setX. *)

(* Variables X : elementType. *)
(* Implicit Types (x y : X) (A B : set X). *)

(* End setX. *)

(* End setTheory. *)
(* End setTheory. *)


(* cardinals *)
(* Lemma eqEcard A B : (A == B) = (A \subset B) && (#|B| <= #|A|). *)
(* Proof. *)
(* rewrite eqEsubset; apply: andb_id2l => sAB. *)
(* by rewrite (geq_leqif (subset_leqif_card sAB)). *)
(* Qed. *)

(* Lemma properEcard A B : (A \proper B) = (A \subset B) && (#|A| < #|B|). *)
(* Proof. by rewrite properEneq ltnNge andbC eqEcard; case: (A \subset B). Qed. *)

(* Lemma subset_leqif_cards A B : A \subset B -> (#|A| <= #|B| ?= iff (A == B)). *)
(* Proof. by move=> sAB; rewrite eqEsubset sAB; apply: subset_leqif_card. Qed. *)

(* Lemma enum_set0 : enum set0 = [::] :> seq T. *)
(* Proof. by rewrite (eq_enum (in_set _)) enum0. Qed. *)

(* Lemma enum_set1 a : enum [set a] = [:: a]. *)
(* Proof. by rewrite (eq_enum (in_set _)) enum1. Qed. *)

Module Theory.

Export Semiset.Exports.
Export set.Exports.
Export SetSyntax.
Export SemisetSyntax.
Export SemisetTheory.
Export setTheory.

End Theory.

End SET.

(* Section Finset. *)
(* Require Import finmap. *)
(* Import SET.Theory. *)

(* Definition finset_latticeMixin *)

(* Definition finset_semisetType := SemisetType finSet . *)

(* End Finset. *)