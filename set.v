From mathcomp
Require Import ssreflect ssrbool eqtype ssrfun ssrnat choice seq.
From mathcomp
Require Import fintype tuple bigop path finset.

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
Notation "x \subset y" := (\sub%set x y) : bool_scope.
Notation "x \subset y :> T" := ((x : T) \subset (y : T)) : abstract_set_scope.
Notation "x \contains y" := (y \subset x) (only parsing) : abstract_set_scope.
Notation "x \contains y :> T" := ((x : T) \contains (y : T)) (only parsing) : abstract_set_scope.

Notation "x \proper y"  := (\proper%set x y) : abstract_set_scope.
Notation "x \proper y"  := (\proper%set x y) : bool_scope.
Notation "x \proper y :> T" := ((x : T) \proper (y : T)) : abstract_set_scope.
Notation "x \containsproper y"  := (y \proper x) (only parsing) : abstract_set_scope.
Notation "x \containsproper y :> T" := ((x : T) \containsproper (y : T)) (only parsing) : abstract_set_scope.

Notation "x \subset y \subset z" := ((x \subset y) && (y \subset z)) : abstract_set_scope.
Notation "x \proper y \subset z" := ((x \proper y) && (y \subset z)) : abstract_set_scope.
Notation "x \subset y \proper z" := ((x \subset y) && (y \proper z)) : abstract_set_scope.
Notation "x \proper y \proper z" := ((x \proper y) && (y \proper z)) : abstract_set_scope.

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

End SetSyntax.

Module Semiset.
Section ClassDef.
Variable elementType : Type.
Variable eqType_of_elementType : elementType -> eqType.
Coercion eqType_of_elementType : elementType >-> eqType.
Implicit Types (X Y : elementType).

Structure mixin_of d (set : elementType -> (cblatticeType (display_set d))) :=
  Mixin {
  memset : forall X, set X -> X -> bool;
  set1 : forall X, X -> set X;
  _ : forall X (x : X), set1 x != set0;
  _ : forall X (x y : X), memset (set1 y) x = (x == y);
  _ : forall X (x : X) A, (set1 x \subset A) = (memset A x);
  _ : forall X (A : set X), (set0 \proper A) -> {x | memset A x} ;
  _ : forall X (A B : set X), (forall x, memset A x -> memset B x) -> A \subset B;
  _ : forall X (x : X) A B, (memset (A :|: B) x) =
                    (memset A x) || (memset B x);

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
  fun bT b & (forall X, phant_id (@Order.CBLattice.class disp (bT X)) (b X)) =>
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
Notation SemisetType set m := (@pack _ _ _ set _ m _ _ (fun=> id) _ id).

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
Implicit Types (x y : X) (A B : set X).

Lemma set1_neq0 (x : X) : [set x] != set0 :> set X.
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

Lemma set1_eq0 x : ([set x] == set0 :> set X) = false.
Proof. by rewrite (negPf (set1_neq0 _)). Qed.

Lemma in_set0 x : x \in (set0 : set X) = false.
Proof. by rewrite -sub1set lex0 set1_eq0. Qed.

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

Lemma subsetP {A B} : reflect {subset A <= B} (A \subset B).
Proof.
apply: (iffP idP) => [sAB x xA|/subsetP_subproof//].
by rewrite -sub1set (le_trans _ sAB) // sub1set.
Qed.

Lemma setP A B : A =i B <-> A = B.
Proof.
split; last by move->.
move=> eqAB; apply/eqP; rewrite eq_le.
gen have leAB : A B eqAB / A \subset B; last by rewrite !leAB.
by apply/subsetP => x; rewrite eqAB.
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

Lemma in_setI A B (x : X) : (x \in A `&` B) = (x \in A) && (x \in B).
Proof.
apply/idP/idP => [xAB|?]; last by rewrite -sub1set lexI !sub1set.
by rewrite (subsetP (leIr _ _) _ xAB) (subsetP (leIl _ _) _ xAB).
Qed.

Lemma set1U A x : [set x] `&` A = if x \in A then [set x] else set0.
Proof.
apply/setP => y; rewrite (fun_if (fun E => y \in E)) in_setI in_set1 in_set0.
by have [->|] := altP (y =P x); rewrite ?if_same //; case: (_ \in A).
Qed.

Lemma set1U_eq0 A x : ([set x] `&` A == set0) = (x \notin A).
Proof. by rewrite set1U; case: (x \in A); rewrite ?set1_eq0 ?eqxx. Qed.

Lemma in_setD A B x : (x \in A `\` B) = (x \notin B) && (x \in A).
Proof.
apply/idP/idP => [|/andP[xNB xA]]; last first.
  by rewrite -sub1set leBRL sub1set xA set1U_eq0.
rewrite -sub1set leBRL sub1set => /andP [-> dxB].
by rewrite -sub1set disj_le ?set1_eq0.
Qed.

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

End setX.

End setTheory.
End setTheory.

End SET.
