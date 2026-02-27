From HB Require Import structures.
From mathcomp Require Import
  ssreflect ssrfun ssrbool ssrnat eqtype seq choice fintype path bigop
  finset finfun.

From mathcomp.finmap Require Import finmap.

(******************************************************************************)
(*   This file defines the type {fperm T} of finite permutations of a         *)
(* choiceType T.  By "finite", we mean that that there are only finitely many *)
(* x such that s x != x.  Permutations are a subtype of finite functions and  *)
(* thus support extensional equality (cf. fpermP).                            *)
(*                                                                            *)
(*         fperm_one, 1 == Identity permutation.                              *)
(*            finsupp s == The support of s (the set of elements that are not *)
(*                         fixed by s).                                       *)
(*            fperm X f == Builds a permutation out of a function f.  If f is *)
(*                         bijective on X and x \in X, then fperm X f x = f x *)
(*     fperm_rename X Y == A permutation that maps X to Y                     *)
(*    fperm_inv s, s^-1 == Inverse of a permutation.                          *)
(*              s1 * s2 == Permutation composition.                           *)
(*           fperm2 x y == Transposition of x and y (i.e. the permutation     *)
(*                         that swaps these elements)                         *)
(*          fperm2_rect == Induction on the number of transpositions          *)
(*           fperm_on X == The set of all permutations with support in X      *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module FPerm.

Section Def.

Variables (T : choiceType).

Local Open Scope fset_scope.

Record fperm_type := FPerm {
  fpval : {fsfun T -> T};
  _ : fsinjectiveb fpval
}.

Definition fperm_of & phant T := fperm_type.

End Def.

Module Exports.

Identity Coercion fperm_of_fperm : fperm_of >-> fperm_type.
Coercion fpval : fperm_type >-> fsfun.
Notation "{ 'fperm' T }" := (@fperm_of _ (Phant T))
  (at level 0, format "{ 'fperm'  T }") : type_scope.

Section WithChoiceType.

Variable T : choiceType.
HB.instance Definition _ := [isSub of fperm_type T for @fpval T].
HB.instance Definition _ := [Equality of fperm_type T by <:].
#[hnf] HB.instance Definition _ := [Choice of fperm_type T by <:].
HB.instance Definition _ := SubType.copy {fperm T} (fperm_type T).
HB.instance Definition _ := Equality.copy {fperm T} (fperm_type T).
HB.instance Definition _ := Choice.copy {fperm T} (fperm_type T).

End WithChoiceType.

Section WithCountableType.

Variable T : countType.
#[hnf] HB.instance Definition _ := [Countable of fperm_type T by <:].
HB.instance Definition _ := Countable.copy {fperm T} (fperm_type T).

End WithCountableType.

Section WithFiniteType.

Variable T : finType.
#[hnf] HB.instance Definition _ := [Finite of fperm_type T by <:].
HB.instance Definition _ := Finite.copy {fperm T} (fperm_type T).

End WithFiniteType.

End Exports.

End FPerm.

Export FPerm.Exports.

Declare Scope fperm_scope.
Delimit Scope fperm_scope with fperm.

Section Operations.

Variable T : choiceType.

Implicit Types (s : {fperm T}) (x : T) (X Y : {fset T}).

Local Open Scope fset_scope.

Lemma fpermP s1 s2 : s1 =1 s2 <-> s1 = s2.
Proof.
split; last congruence; by move=> /fsfunP /val_inj.
Qed.

Lemma imfset_finsuppfp s : s @` finsupp s = finsupp s.
Proof. exact/imfset_eq_fsinjectiveP/valP. Qed.

Lemma imfset_finsuppfpS s X : finsupp s `<=` X -> s @` X = X.
Proof.
move=> subX; rewrite -(fsetID (finsupp s) X) imfsetU.
rewrite (fsetIidPr subX) imfset_finsuppfp; congr fsetU.
under eq_in_imfset => x /fsetDP [] _ /fsfun_dflt -> do [].
by rewrite imfset_id.
Qed.

Lemma fperm_inj s : injective s.
Proof. exact/fsinjectiveP/valP. Qed.

Lemma fperm_finsupp s x : (s x \in finsupp s) = (x \in finsupp s).
Proof. rewrite -{1}imfset_finsuppfp mem_imfset //; exact: fperm_inj. Qed.

Lemma card_finsuppfpN1 s : #|` finsupp s| != 1.
Proof.
apply/cardfs1P=> - [x s_x].
have x_s: x \in finsupp s by rewrite s_x in_fset1.
have: s x \in finsupp s by rewrite fperm_finsupp.
by rewrite s_x in_fset1 -memNfinsupp x_s.
Qed.

Fact fperm_one_key : unit. exact: tt. Qed.

Lemma fperm_one_subproof : fsinjectiveb ([fsfun] : {fsfun T -> T}).
Proof. by apply/fsinjectiveP => ??; rewrite !fsfunE. Qed.

Definition fperm_one : {fperm T} :=
  locked_with fperm_one_key
    (@FPerm.FPerm T [fsfun] fperm_one_subproof).
Notation "1" := fperm_one.

Lemma fperm1 x : 1 x = x.
Proof. by rewrite /fperm_one unlock fsfunE. Qed.

Lemma finsupp1 : finsupp 1 = fset0.
Proof. rewrite [1]unlock; exact: finsupp0. Qed.

Lemma finsuppfp_eq0 s : (finsupp s == fset0) = (s == 1).
Proof.
apply/(sameP idP)/(iffP idP)=> [/eqP->|]; first by rewrite finsupp1.
move=> /eqP e; apply/eqP/fpermP=> x; rewrite fperm1; case: (finsuppP s) => //.
by rewrite e in_fset0.
Qed.

Section Build.

Implicit Types (f : T -> T).

Definition fperm_def (X : {fset T}) (f : T -> T) x :=
  let Y1 : {fset T} := [fset f x | x in X] `\` X in
  let Y2 : {fset T} := X `\` [fset f x | x in X] in
  if x \in Y1 then nth x Y2 (index x Y1) else f x.

Definition fperm X f :=
  odflt 1 (insub [fsfun x in (X `|` f @` X) => fperm_def X f x]).

Lemma fpermE f X : {in X &, injective f} -> {in X, fperm X f =1 f}.
Proof.
move=> /card_in_imfsetP inj; rewrite /fperm insubT /=; last first.
  by move=> _ x x_X; rewrite fsfunE in_fsetU /fperm_def /= in_fsetD x_X.
set D := X `|` _; apply/fsinjectivebP; exists D; rewrite ?finsupp_sub //.
rewrite /fperm_def; set Y1 := f @` X `\` X; set Y2 := X `\` f @` X.
have sY12 : #|` Y1| = #|` Y2|.
  apply: (@addnI #|` f @` X `&` X|).
  rewrite cardfsID fsetIC cardfsID; exact/eqP.
have nY1_X x : x \in D -> x \notin Y1 -> x \in X.
  case/fsetUP=> //; by rewrite in_fsetD => ->; rewrite andbT negbK.
have nth_Y2 x : x \in D -> x \in Y1 -> nth x Y2 (index x Y1) \in Y2.
  move=> ??; by rewrite mem_nth // -sY12 index_mem.
split=> [x y x_D y_D|x]; last first.
  rewrite fsfunE (valP x); case: ifPn=> [x_in|x_out].
    have ? := nth_Y2 _ (valP x) x_in; suff /fsubsetP: Y2 `<=` D by exact.
    by rewrite fsubDset fsubsetU // fsubsetU ?orbT // fsubset_refl.
  apply/fsetUP; right; apply/imfsetP; exists (\val x) => //.
  exact: nY1_X (valP x) x_out.
rewrite !fsfunE x_D y_D; case: ifPn => x_Y1; case: ifPn => y_Y1.
- rewrite (set_nth_default y) -?sY12 ?index_mem // => exy.
  suff: index x Y1 = index y Y1 by exact: index_inj.
  by apply/uniqP; eauto; rewrite ?uniq_fset // -?sY12 inE ?index_mem.
- move=> exy; move: (nth_Y2 _ x_D x_Y1).
  by rewrite in_fsetD exy in_imfset // nY1_X.
- move=> exy; move: (nth_Y2 _ y_D y_Y1).
  by rewrite in_fsetD -exy in_imfset // nY1_X.
- by apply: (card_in_imfsetP _ _ inj); rewrite nY1_X.
Qed.

Lemma finsupp_fperm f X : finsupp (fperm X f) `<=` X `|` f @` X.
Proof.
rewrite /fperm; case: insubP => /= [g _ ->|_]; first exact: finsupp_sub.
by rewrite finsupp1 fsub0set.
Qed.

Lemma fpermEst f X x : f @` X = X -> fperm X f x = if x \in X then f x else x.
Proof.
move=> st; case: ifPn=> /= [|x_nin].
  by apply/fpermE/card_in_imfsetP/eqP; rewrite st.
suff: x \notin finsupp (fperm X f) by case: finsuppP.
apply: contra x_nin; apply/fsubsetP.
by rewrite -{2}[X]fsetUid -{3}st finsupp_fperm.
Qed.

End Build.

Section Renaming.

Definition fperm_rename (X Y : {fset T}) : {fperm T} :=
  fperm X (fun x => nth x Y (index x X)).

Lemma fperm_renameP X Y :
  let s := fperm_rename X Y in
  #|` X| = #|` Y| ->
  finsupp s `<=` X `|` Y /\ s @` X = Y.
Proof.
move=> s size_X; pose f x := nth x Y (index x X).
have f_inj: {in X &, injective f} => [x y xX yX /eqP|].
  rewrite /f (set_nth_default x y) -?size_X ?index_mem //.
  rewrite nth_uniq ?fset_uniq // -?size_X ?index_mem //.
  move/eqP; exact: index_inj.
have im_f: f @` X = Y.
  apply/fsetP=> y; apply/(sameP idP)/(iffP idP) => /= y_in.
    apply/imfsetP; exists (nth y X (index y Y)) => //=.
      by rewrite mem_nth // size_X index_mem.
    by rewrite /f nthK ?fset_uniq //= ?inE ?size_X ?index_mem // nth_index.
  by case/imfsetP: y_in => x /= x_in ->; rewrite mem_nth // -size_X index_mem.
rewrite -im_f; split; first by rewrite finsupp_fperm.
by apply: eq_in_imfset; apply: fpermE.
Qed.

End Renaming.

Section Inverse.

Variable s : {fperm T}.

Local Notation inv_def :=
  (fun x => oapp \val x [pick y : finsupp s | x == s (\val y)]).

Lemma fperm_inv_subproof : inv_def @` finsupp s = finsupp s.
Proof.
apply/fsetP=> x; apply/(sameP idP)/(iffP idP).
  move=> x_in_supp; apply/imfsetP; exists (s x).
    by rewrite -imfset_finsuppfp (in_imfset _ _ x_in_supp).
  case: pickP=> /= [y' /eqP/fperm_inj //|/(_ (Sub x x_in_supp))].
  by rewrite eqxx.
by case/imfsetP=> [y Py -> {x}]; case: pickP => /=.
Qed.

Definition fperm_inv := locked (fperm (finsupp s) inv_def).

Lemma fpermK : cancel s fperm_inv.
Proof.
move=> x; rewrite /fperm_inv -lock fpermEst; last exact: fperm_inv_subproof.
rewrite fperm_finsupp; case: finsuppP => // x_in_supp.
case: pickP => [y /= /eqP/esym /fperm_inj-> //|/(_ (Sub x x_in_supp)) /=].
by rewrite eqxx.
Qed.

Lemma fpermKV : cancel fperm_inv s.
Proof.
move=> x; rewrite /fperm_inv -lock fpermEst; last exact: fperm_inv_subproof.
case: ifPn=> [x_in_sup|].
  case: pickP=> [x' /= /eqP/esym -> //|/=].
  rewrite -imfset_finsuppfp in x_in_sup; case/imfsetP: x_in_sup=> [x' Px' ->].
  by move/(_ (Sub x' Px')); rewrite eqxx.
by rewrite mem_finsupp negbK => /eqP.
Qed.

Lemma finsupp_inv : finsupp fperm_inv = finsupp s.
Proof.
apply/fsetP=> x; apply/(sameP idP)/(iffP idP).
  by rewrite !mem_finsupp; apply: contra => /eqP {1}<-; rewrite fpermKV eqxx.
by rewrite !mem_finsupp; apply: contra=> /eqP {1}<-; rewrite fpermK eqxx.
Qed.

Lemma fperm_finsuppV x : (fperm_inv x \in finsupp s) = (x \in finsupp s).
Proof. by rewrite -{1}finsupp_inv fperm_finsupp finsupp_inv. Qed.

End Inverse.

Lemma fperm_mul_subproof s1 s2 :
  (s1 \o s2) @` (finsupp s1 `|` finsupp s2) = finsupp s1 `|` finsupp s2.
Proof.
by rewrite imfset_comp !imfset_finsuppfpS // ?fsubsetUr // fsubsetUl.
Qed.

Fact fperm_mul_key : unit. exact: tt. Qed.

Definition fperm_mul s1 s2 :=
  locked_with fperm_mul_key (fperm (finsupp s1 `|` finsupp s2) (s1 \o s2)).

Infix "*" := fperm_mul.
Notation "x ^-1" := (fperm_inv x).

Lemma fpermM s1 s2 : s1 * s2 =1 s1 \o s2.
Proof.
move=> x; rewrite /fperm_mul locked_withE fpermEst; last first.
  exact: fperm_mul_subproof.
have [|nin_supp] //= := boolP (x \in _).
rewrite in_fsetU negb_or !mem_finsupp !negbK in nin_supp.
by case/andP: nin_supp=> [/eqP h1 /eqP ->]; rewrite h1.
Qed.

Lemma finsupp_mul s1 s2 : finsupp (s1 * s2) `<=` finsupp s1 `|` finsupp s2.
Proof.
apply/fsubsetP=> x; rewrite in_fsetU !mem_finsupp fpermM /=.
have [-> -> //|] := altP (s2 x =P x).
by rewrite orbT.
Qed.

Lemma finsuppJ s1 s2 : finsupp (s1 * s2 * s1^-1) = s1 @` finsupp s2.
Proof.
apply/fsetP=> x; apply/esym/imfsetP; rewrite mem_finsupp fpermM /= fpermM /=.
rewrite (can2_eq (fpermK s1) (fpermKV s1)).
have [e|ne] /= := altP eqP.
  case=> [y Py e']; move: e Py.
  by rewrite e' fpermK mem_finsupp=> ->; rewrite eqxx.
exists (s1^-1 x); last by rewrite fpermKV.
by rewrite mem_finsupp.
Qed.

Lemma fperm_mulC s1 s2 :
  [disjoint finsupp s1 & finsupp s2] ->
  s1 * s2 = s2 * s1.
Proof.
move=> dis; apply/fpermP=> x; rewrite !fpermM /=.
have [|ins1] := finsuppP s1 x.
  have [//|ins1'] := finsuppP s1 (s2 x).
  move/(fdisjointP dis): ins1'; rewrite fperm_finsupp (memNfinsupp s1).
  by case: (finsuppP s2) => // _ _ /eqP.
move/(fdisjointP dis): (ins1); case: (finsuppP s2) => // nins2 _.
rewrite -fperm_finsupp in ins1.
by move/(fdisjointP dis): (ins1); case: (finsuppP s2) => // nins2 _.
Qed.

Lemma fperm_mul1s : left_id 1 fperm_mul.
Proof. by move=> s; apply/fpermP=> x; rewrite fpermM /= fperm1. Qed.

Lemma fperm_muls1 : right_id 1 fperm_mul.
Proof. by move=> s; apply/fpermP=> x; rewrite fpermM /= fperm1. Qed.

Lemma fperm_mulsV : right_inverse 1 fperm_inv fperm_mul.
Proof. by move=> s; apply/fpermP=> x; rewrite fpermM /= fpermKV fperm1. Qed.

Lemma fperm_mulVs : left_inverse 1 fperm_inv fperm_mul.
Proof. by move=> s; apply/fpermP=> x; rewrite fpermM /= fpermK fperm1. Qed.

Lemma fperm_mulA : associative fperm_mul.
Proof. by move=> s1 s2 s3; apply/fpermP=> x; rewrite !fpermM /= !fpermM. Qed.

Lemma fperm_inv_mul : {morph fperm_inv : s1 s2 / s1 * s2 >-> s2 * s1}.
Proof.
move=> s1 s2 /=.
rewrite -[s2^-1 * _]fperm_mul1s -(fperm_mulVs (s1 * s2)) -2!fperm_mulA.
by rewrite (fperm_mulA s2) fperm_mulsV fperm_mul1s fperm_mulsV fperm_muls1.
Qed.

Lemma fperm_mulsK : right_loop fperm_inv fperm_mul.
Proof. by move=> s1 s2; rewrite -fperm_mulA fperm_mulsV fperm_muls1. Qed.

Lemma fperm_mulKs : left_loop fperm_inv fperm_mul.
Proof. by move=> s1 s2; rewrite fperm_mulA fperm_mulVs fperm_mul1s. Qed.

Lemma fperm_mulsI : right_injective fperm_mul.
Proof. by move=> s1 s2 s3 e; rewrite -(fperm_mulKs s1 s2) e fperm_mulKs. Qed.

Lemma fperm_mulIs : left_injective fperm_mul.
Proof. by move=> s1 s2 s3 e; rewrite -(fperm_mulsK s1 s2) e fperm_mulsK. Qed.

Lemma fperm_invK : involutive fperm_inv.
Proof.
by move=> s; apply (@fperm_mulsI s^-1); rewrite fperm_mulsV fperm_mulVs.
Qed.

Lemma fperm_mulsKV : rev_right_loop fperm_inv fperm_mul.
Proof. by move=> s1 s2; rewrite -{2}(fperm_invK s1) fperm_mulsK. Qed.

Lemma fperm_mulKVs : rev_left_loop fperm_inv fperm_mul.
Proof. by move=> s1 s2; rewrite -{1}(fperm_invK s1) fperm_mulKs. Qed.

Lemma fperm1V : 1^-1 = 1 :> {fperm T}.
Proof.
by apply: (@fperm_mulIs 1); rewrite fperm_mul1s fperm_mulVs.
Qed.

Notation fperm2_def x y := [fun z => z with x |-> y, y |-> x].

Lemma fperm2_subproof x y :
   fperm2_def x y @` [fset x; y] = [fset x; y].
Proof.
apply/fsetP=> z; apply/(sameP idP)/(iffP idP).
  case/fset2P=> [->|->] /=; apply/imfsetP;
  [exists y; try apply fset22|exists x; try apply fset21].
    by rewrite /= eqxx; have [->|] //= := altP eqP.
  by rewrite /= eqxx.
case/imfsetP=> [w /fset2P [->|->] ->] /=; rewrite eqxx ?fset22 //.
case: ifP=> ?; by [apply fset21|apply fset22].
Qed.

Definition fperm2 x y := fperm [fset x; y] (fperm2_def x y).

Lemma fperm2E x y : fperm2 x y =1 [fun z => z with x |-> y, y |-> x].
Proof.
move=> z; rewrite fpermEst; last exact: fperm2_subproof.
rewrite /= in_fset2.
have [->|] := altP eqP => //= ?.
by have [?|] := altP eqP => //= ?.
Qed.

CoInductive fperm2_spec x y z : T -> Type :=
| FPerm2First  of z = x : fperm2_spec x y z y
| FPerm2Second of z = y : fperm2_spec x y z x
| FPerm2None   of z <> x & z <> y : fperm2_spec x y z z.

Lemma fperm2P x y z : fperm2_spec x y z (fperm2 x y z).
Proof. by rewrite fperm2E /=; do 2?[case: eqP=> //]; constructor; auto. Qed.

Lemma fperm2L x y : fperm2 x y x = y.
Proof. by rewrite fperm2E /= eqxx. Qed.

Lemma fperm2R x y : fperm2 x y y = x.
Proof. by rewrite fperm2E /= eqxx; case: eqP=> [->|]. Qed.

Lemma fperm2D x y z : z != x -> z != y -> fperm2 x y z = z.
Proof. by rewrite fperm2E /= => /negbTE-> /negbTE->. Qed.

Lemma fperm2C x y : fperm2 x y = fperm2 y x.
Proof. apply/fpermP=> z; do 2?[case: fperm2P=> //]; congruence. Qed.

Lemma fperm2V x y : (fperm2 x y)^-1 = fperm2 x y.
Proof.
rewrite -[in LHS](fperm_muls1 _^-1).
apply/(canLR (fperm_mulKs (fperm2 x y)))/fpermP=> z.
rewrite fperm1 fpermM /= !fperm2E /=; have [->{z}|] := altP (z =P x).
  by rewrite eqxx; case: ifP=> // /eqP ->.
have [->{z}|] := altP (z =P y); first by rewrite eqxx.
by move=> /negbTE -> /negbTE ->.
Qed.

Lemma fperm2xx x : fperm2 x x = 1.
Proof.
apply/fpermP=> y; rewrite fperm2E fperm1 /=.
by have [->|] := altP (y =P x).
Qed.

Lemma finsupp_fperm2 x y :
  finsupp (fperm2 x y) = if x == y then fset0 else [fset x; y].
Proof.
have [<-{y}|ne] := altP eqP; first by rewrite fperm2xx finsupp1.
apply/fsetP=> z; rewrite mem_finsupp /= in_fset2.
case: fperm2P => [->|->|]; [rewrite eq_sym| |]; rewrite ?ne ?eqxx ?orbT //.
by move=> /eqP/negbTE-> /eqP/negbTE->.
Qed.

Lemma fsubset_finsupp_fperm2 x y : finsupp (fperm2 x y) `<=` [fset x; y].
Proof.
by rewrite finsupp_fperm2 fun_if if_arg fsub0set fsubset_refl; case: (_ == _).
Qed.

Lemma fperm2_rect (P : {fperm T} -> Type) :
  P 1 ->
  (forall x y s, x \notin finsupp s -> y \in finsupp (fperm2 x y * s) ->
                 P s -> P (fperm2 x y * s)) ->
  forall s, P s.
Proof.
move=> P1 PM s; have [n n_s] := ubnP (size (finsupp s)).
elim: n=> //= n IH in s n_s *; have [-> //|] := altP (s =P 1).
rewrite -finsuppfp_eq0 => /fset0Pn/sigW [x x_s].
pose y := s x; pose t := fperm2 x y; pose s' := t * s; have es: s = t * s'.
  by rewrite -[LHS](fperm_mulKs t) fperm2V.
have x_s' : x \notin finsupp s' by rewrite mem_finsupp fpermM /= fperm2R eqxx.
have y_s : y \in finsupp (t * s') by rewrite -es fperm_finsupp.
suff /fproper_ltn_card s_s' : finsupp s' `<` finsupp s.
  rewrite es; apply: PM => //; apply: IH; exact: (leq_trans s_s').
rewrite (fsub_proper_trans _ (fproperD1 x_s)) // fsubsetD1 x_s'.
rewrite (fsubset_trans (finsupp_mul t s)) // fsubUset fsubset_refl.
rewrite (fsubset_trans (fsubset_finsupp_fperm2 x y)) //.
by rewrite fsubUset !fsub1set x_s es.
Qed.

Fact fperm_exp_key : unit. exact: tt. Qed.

Definition fperm_exp s n :=
  locked_with fperm_exp_key (iter n (fperm_mul s) 1).

Infix "^+" := fperm_exp.

Lemma fperm_expE s n : (s ^+ n) = iter n (fperm_mul s) 1.
Proof. exact: locked_withE. Qed.

Canonical fperm_exp_unlockable s n := Unlockable (fperm_expE s n).

Lemma fpermX s n x : (s ^+ n) x = iter n s x.
Proof.
rewrite unlock; by elim: n => /= [|n IH]; rewrite ?fperm1 // fpermM /= IH.
Qed.

Lemma fperm_expSl s n : s ^+ n.+1 = s * s ^+ n.
Proof. by rewrite !unlock. Qed.

Lemma fperm_expSr s n : s ^+ n.+1 = s ^+ n * s.
Proof.
by apply/fpermP => x; rewrite fpermX iterSr fpermM -fpermX.
Qed.

Lemma fperm_exp0 s : s ^+ 0 = 1.
Proof. by rewrite unlock. Qed.

Lemma fperm_expsD s n m : s ^+ (n + m) = s ^+ n * s ^+ m.
Proof.
elim: n => [|n IH]; rewrite ?fperm_exp0 ?fperm_mul1s //.
by rewrite addSn !fperm_expSl IH fperm_mulA.
Qed.

Lemma fperm_exp_com s1 s2 n :
  s1 * s2 = s2 * s1 ->
  s1 * s2 ^+ n = s2 ^+ n * s1.
Proof.
move=> com; elim: n => [|n IH].
- by rewrite fperm_exp0 fperm_mul1s fperm_muls1.
- by rewrite fperm_expSl fperm_mulA com -fperm_mulA IH fperm_mulA.
Qed.

Lemma fperm_expDs s1 s2 n :
  s1 * s2 = s2 * s1 ->
  (s1 * s2) ^+ n = s1 ^+ n * s2 ^+ n.
Proof.
move=> com; elim: n => [|n IH]; first by rewrite !fperm_exp0 fperm_mul1s.
rewrite !fperm_expSl {}IH [s1 * s2 * _]fperm_mulA -[s1 * s2 * _]fperm_mulA.
rewrite (@fperm_exp_com s2 s1); first by rewrite -!fperm_mulA.
by rewrite com.
Qed.

Lemma fperm_exps1 s : s ^+ 1 = s.
Proof. by rewrite fperm_expSl fperm_exp0 /= fperm_muls1. Qed.

Lemma fperm_exp1n n : 1 ^+ n = 1.
Proof. by apply/fpermP=> x; rewrite fpermX iter_fix fperm1. Qed.

Lemma fperm_expV s n : s^-1 ^+ n = (s ^+ n) ^-1.
Proof.
elim: n => [|n IH]; first by rewrite ?fperm_exp0 ?fperm1V.
by rewrite !fperm_expSl IH -fperm_inv_mul -fperm_expSl -fperm_expSr.
Qed.

Lemma fperm_exp_mul s n m : s ^+ (n * m)%N = s ^+ n ^+ m.
Proof.
elim: n => [|n IH]; rewrite ?fperm_exp0 ?fperm_exp1n //.
rewrite mulSn fperm_expsD {}IH fperm_expSl fperm_expDs //.
by rewrite -fperm_expSl fperm_expSr.
Qed.

Lemma finsupp_exp s n : finsupp (s ^+ n) `<=` finsupp s.
Proof.
elim: n => /= [|n IH]; rewrite ?fperm_exp0 ?finsupp1 // fperm_expSl.
by rewrite (fsubset_trans (finsupp_mul _ _)) // fsubUset fsubset_refl /=.
Qed.

End Operations.

Arguments fperm_one {_}.
Prenex Implicits fperm_inv fperm_mul fperm2.

Delimit Scope fperm_scope with fperm.

Notation "1" := fperm_one : fperm_scope.
Infix "*" := fperm_mul : fperm_scope.
Infix "^+" := fperm_exp : fperm_scope.
Notation "x ^-1" := (fperm_inv x) : fperm_scope.

Section Extend.

Local Open Scope fset_scope.
Local Open Scope fperm_scope.

Variables (T S : choiceType) (f : T -> S).
Hypothesis (f_inj : injective f).
Implicit Types (x : T) (y : S) (s : {fperm T}).

Let g s y := [pick xx : finsupp s | f (\val xx) == y].

Local Lemma fK s x (x_s : x \in finsupp s) : g s (f x) = Some (Sub x x_s).
Proof.
rewrite /g; case: pickP => [xx /eqP/f_inj e|/(_ (Sub x x_s))].
- by congr Some; apply/val_inj.
- by rewrite eqxx.
Qed.

Local Lemma gK s y : oapp (f \o \val) y (g s y) = y.
Proof. by rewrite /g; case: pickP => //= xx /eqP. Qed.

Definition ext_fperm s : {fperm S} :=
  fperm (f @` finsupp s)
    (fun y => oapp (fun xx => f (s (\val xx))) y (g s y)).

Lemma ext_fpermE s y :
  ext_fperm s y =
    if g s y is Some xx then f (s (\val xx)) else y.
Proof.
rewrite fpermEst /=.
  case g_y: (g s y) => [xx|]; rewrite ?if_same //=.
  move: (gK s y); rewrite g_y /= => <-.
  by rewrite mem_imfset //= (valP xx).
apply/fsetP=> {}x; apply/(sameP (imfsetP _ _ _ _))/(iffP (imfsetP _ _ _ _)).
- case=> {}x /= x_s ->.
  exists (f (s^-1 x)); rewrite ?in_imfset //= ?fperm_finsuppV //.
  by rewrite fK ?fperm_finsuppV //= fpermKV.
- case=> _ /= /imfsetP [{}x /= ? ->] ->.
  by exists (s x); rewrite ?fperm_finsupp // fK.
Qed.

Lemma finsupp_ext_fperm s : finsupp (ext_fperm s) = f @` finsupp s.
Proof.
apply/fsetP=> x; rewrite mem_finsupp ext_fpermE.
apply/(sameP idP)/(iffP (imfsetP _ _ _ _)).
  by case=> {}x /= x_s ->; rewrite fK inj_eq //=; rewrite mem_finsupp in x_s.
case e: (g s x) => /= [y|]; last by rewrite eqxx.
rewrite -(gK s x) e /= inj_eq // => yP.
by exists (\val y); rewrite // mem_finsupp.
Qed.

End Extend.

Section ExtendSub.

Variables (T : choiceType) (P : pred T) (sT : subChoiceType P).

Lemma ext_fpermE_sub (s : {fperm sT}) (y : T) :
  ext_fperm \val s y = if insub y is Some x then \val (s x) else y.
Proof.
rewrite ext_fpermE; last exact: val_inj.
case: pickP=> /= [x /eqP <-|yP].
- rewrite insubT ?valP //= => ?; congr (\val (s _)).
  by apply/val_inj; rewrite SubK.
- case: insubP => //= x Px <- {y Px} in yP *; congr \val.
  apply/esym/eqP; rewrite -memNfinsupp; apply/negP => x_s.
  by move/(_ (Sub x x_s)): yP; rewrite eqxx.
Qed.

Lemma ext_fperm_val (s : {fperm sT}) (x : sT) :
  ext_fperm \val s (\val x) = \val (s x).
Proof. by rewrite ext_fpermE_sub ?valK. Qed.

End ExtendSub.

Section Enumeration.

Local Open Scope fset_scope.
Local Open Scope fperm_scope.

Variable (T : choiceType) (X : {fset T}).
Implicit Types (s : {fperm T}).

Definition fperm_on : {fset {fperm T}} :=
  [fset ext_fperm \val s | s : {fperm X}].

Lemma in_fperm_on s : (s \in fperm_on) = (finsupp s `<=` X).
Proof.
apply/(sameP (imfsetP _ _ _ _))/(iffP idP); last first.
  case=> /= {}s _ ->; apply/fsubsetP => x.
  rewrite mem_finsupp ext_fpermE_sub.
  by case: insubP=> //= _; rewrite eqxx.
move=> s_X; have s_X1: forall x : X, s (\val x) \in X.
  move=> x; case: (finsuppP s (\val x)) => [_|x_s]; first exact: valP.
  by move/fsubsetP: s_X; apply; rewrite fperm_finsupp.
have s_X2: forall x : X, s^-1 (\val x) \in X.
  move=> x; case: (finsuppP s^-1 (\val x)) => [_|x_s]; first exact: valP.
  move: s_X; rewrite -finsupp_inv.
  by move/fsubsetP; apply; rewrite fperm_finsupp.
exists (fperm [fset x | x : X] (fun x => Sub (s (\val x)) (s_X1 x))) => //=.
apply/fpermP => x; rewrite ext_fpermE_sub.
case: insubP => /= [y /= x_X x_y|x_X]; last first.
  by apply/eqP; rewrite -memNfinsupp; apply: contraNN x_X; apply/fsubsetP.
have sx_X: s^-1 x \in X := s_X2 (Sub x x_X).
rewrite fpermEst ?in_imfset //= ?x_y //= {x y x_X x_y sx_X}.
apply/fsetP => /= x; rewrite [in RHS]in_imfset //.
apply/imfsetP.
exists (Sub (s^-1 (\val x)) (s_X2 x)); rewrite /= ?in_imfset //.
by apply: val_inj; rewrite /= fpermKV.
Qed.

Lemma fperm_on1 : 1 \in fperm_on.
Proof. by rewrite in_fperm_on finsupp1. Qed.

Lemma fperm_onM s1 s2 :
  s1 \in fperm_on -> s2 \in fperm_on -> s1 * s2 \in fperm_on.
Proof.
rewrite !in_fperm_on => sub1 sub2.
by rewrite (fsubset_trans (finsupp_mul s1 s2))// fsubUset sub1.
Qed.

Lemma fperm_onV s : s \in fperm_on -> s^-1 \in fperm_on.
Proof. by rewrite !in_fperm_on finsupp_inv. Qed.

Lemma fperm_onX s n : s \in fperm_on -> s ^+ n \in fperm_on.
Proof.
by rewrite !in_fperm_on => /(fsubset_trans _) -> //; rewrite finsupp_exp.
Qed.

End Enumeration.

Section Order.

Local Open Scope fset_scope.
Local Open Scope fperm_scope.

Variables (T : choiceType).
Implicit Types (x y : T) (s : {fperm T}).

Lemma order_aux s : exists n, (0 < n) && (s ^+ n == 1).
Proof.
pose X := fperm_on (finsupp s).
pose k := #|` X|.+1; rewrite cardfE in k.
have fP (i : 'I_k) : s ^+ i \in X by rewrite fperm_onX // in_fperm_on.
pose f (i : 'I_k) : X := Sub (s ^+ i) (fP i).
have /injectivePn /= [n [m ne_nm es]]: ~~ injectiveb f.
  by apply/injectiveP => /leq_card /=; rewrite card_ord ltnn.
wlog: n m {ne_nm} es / n < m => [H|nm].
  rewrite -(inj_eq val_inj) in ne_nm; case: ltngtP => // nm in ne_nm *;
  exact: (H _ _ _ nm).
move/(congr1 val): es => /=; rewrite -(subnK nm) addnS -addSn.
set p := (m - _).+1; rewrite fperm_expsD -[LHS]fperm_mul1s => /fperm_mulIs ->.
by exists p; rewrite eqxx.
Qed.

Definition order s : nat := ex_minn (order_aux s).

Lemma order_gt0 s : 0 < order s.
Proof. by rewrite /order; case: ex_minnP => n /andP []. Qed.

Lemma fperm_exp_order s : s ^+ order s = 1.
Proof. by rewrite /order; case: ex_minnP => n /andP [] _ /eqP ->. Qed.

Lemma fperm_exp_orderV s : s ^+ (order s).-1 = s^-1.
Proof.
apply: (@fperm_mulsI _ s); rewrite fperm_mulsV -(fperm_exp_order s).
by rewrite -[order s in RHS]prednK ?fperm_expSl // order_gt0.
Qed.

End Order.

Section Generation.

Local Open Scope fset_scope.
Local Open Scope fperm_scope.

Variable (T : choiceType) (A : {fset {fperm T}}).
Implicit Types (x y : T) (S : {fset {fperm T}}).

Let F :=
  (fun S : {fset {fperm T}} => 1 |` fperm_mul @2`(A, (fun=> S))).

Let U : {fset {fperm T}} := fperm_on (\bigcup_(s <- A) finsupp s).

Fact generate_key : unit. exact: tt. Qed.

Definition generate : {fset {fperm T}} :=
  locked_with generate_key (fixfset U F).

Local Lemma generateF_mono : {homo F : X Y / X `<=` Y}.
Proof.
move=> X Y /fsubsetP XY; rewrite fsetUS //=.
apply/fsubsetP=> _ /imfset2P /= [s1 s1_in [s2 /XY s2_in ->]].
by apply/imfset2P; exists s1 => //; exists s2.
Qed.

Local Lemma generateF_bounded : {homo F : X / X `<=` U}.
Proof.
move=> S /fsubsetP SU; rewrite fsubUset fsub1set in_fperm_on finsupp1 fsub0set.
apply/fsubsetP=> _ /imfset2P /= [s1 s1_in [s2 /SU s2_in ->]].
have {}s1_in: s1 \in U by rewrite in_fperm_on bigfcup_sup.
rewrite in_fperm_on (fsubset_trans (finsupp_mul _ _)) //=.
by rewrite fsubUset -!in_fperm_on s1_in s2_in.
Qed.

Lemma generateE : generate = 1 |` fperm_mul @2`(A, (fun=> generate)).
Proof.
rewrite /generate locked_withE -{1}fixfsetK //=.
- exact: generateF_mono.
- exact: generateF_bounded.
Qed.

Lemma generateP s :
  reflect (exists2 ss : seq {fperm T},
             {subset ss <= A} &
             s = foldr fperm_mul 1 ss)
          (s \in generate).
Proof.
apply/(iffP idP) => [|[{s} ss ss_A ->]].
- rewrite /generate locked_withE.
  rewrite -in_iter_ffix_orderE; last exact: generateF_bounded.
  move: (ffix_order _ _ _) => n; elim: n => //= n IH in s *.
  case/fset1UP => [->|]; first by exists [::].
  case/imfset2P=> /= s1 s1_in [s2 s2_in ->].
  have [{}ss ss_A ->] := IH _ s2_in; exists (s1 :: ss) => //.
  move=> ?; rewrite in_cons; case/orP => [/eqP -> //|]; exact: ss_A.
- elim: ss => //= [|s ss IH] in ss_A *; rewrite generateE.
    by rewrite fsetU11.
  rewrite fset1Ur //=; apply/imfset2P.
  have s_A: s \in A by rewrite ss_A // inE eqxx.
  exists s => //; exists (foldr fperm_mul 1 ss) => //.
  by rewrite IH // => ? H; rewrite ss_A // inE H orbT.
Qed.

Lemma fsubset_generate : A `<=` generate.
Proof.
apply/fsubsetP=> s s_A; apply/generateP; exists [:: s] => /= [s'|].
- by rewrite inE => /eqP ->.
- by rewrite fperm_muls1.
Qed.

Lemma generate1 : 1 \in generate.
Proof. by apply/generateP; exists [::]. Qed.

Lemma generate_mul s1 s2 :
  s1 \in generate -> s2 \in generate -> s1 * s2 \in generate.
Proof.
case/generateP=> ss1 ss1_A ->; case/generateP=> ss2 ss2_A -> {s1 s2}.
apply/generateP; exists (ss1 ++ ss2) => [?|{ss1_A ss2_A}].
  by rewrite mem_cat; case/orP; [exact: ss1_A|exact: ss2_A].
by elim: ss1 => [|s1 ss1 IH] //=; rewrite ?fperm_mul1s // -IH fperm_mulA.
Qed.

Lemma generate_exp s n : s \in generate -> s ^+ n \in generate.
Proof.
move=> s_in; elim: n => [|n IH]; rewrite ?fperm_exp0 ?generate1 //.
by rewrite fperm_expSl generate_mul.
Qed.

Lemma generate_inv s : s \in generate -> s^-1 \in generate.
Proof. rewrite -fperm_exp_orderV; exact: generate_exp. Qed.

End Generation.

Arguments generateP {T A s}.

Section GenerateTheory.

Local Open Scope fset_scope.
Local Open Scope fperm_scope.

Variables (T : choiceType).
Implicit Types (s : {fperm T}) (x y : T).

Lemma generate1P s s' :
  reflect (exists n, s' = s ^+ n) (s' \in generate [fset s]).
Proof.
apply/(iffP generateP) => [[ss ss_s ->]|[n ->]] {s'}.
  exists (size ss); elim: ss => /= [|s' ss IH] in ss_s *.
    by rewrite fperm_exp0.
  rewrite fperm_expSl.
  have /fset1P -> : s' \in [fset s] by apply: ss_s; rewrite inE eqxx.
  by rewrite IH // => ? H; apply: ss_s; rewrite inE H orbT.
exists (nseq n s).
- by move=> ?; rewrite mem_nseq in_fset1 => /andP [_ /eqP ->].
- by elim: n => [|n IH]; rewrite ?fperm_exp0 // ?fperm_expSl // IH.
Qed.

End GenerateTheory.

Section Orbit.

Local Open Scope fset_scope.
Local Open Scope fperm_scope.

Variable (T : choiceType) (s : {fperm T}) (x : T).
Implicit Types (y : T) (X Y : {fset T}).

Definition orbit :=
  (fun s' : {fperm T} => s' x) @` generate [fset s].

Lemma orbitP y : reflect (exists n, y = (s ^+ n) x) (y \in orbit).
Proof.
apply/(iffP (imfsetP _ _ _ _)) => /= [[_ /generate1P [n ->] ->]|[n ->]];
first (by exists n); exists (s ^+ n); rewrite // generate_exp //.
by apply/generate1P; exists 1%N; rewrite fperm_exps1.
Qed.

Lemma mem_orbit_id : x \in orbit.
Proof. by apply/orbitP; exists 0; rewrite fpermX. Qed.

Lemma mul_orbit y : (s y \in orbit) = (y \in orbit).
Proof.
apply/(sameP (orbitP _))/(iffP (orbitP _)) => [[n ->]|[n e]].
  by exists n.+1; rewrite !fpermX.
rewrite fpermX in e; case: n => /= [|n] in e *.
- by exists (order s).-1; rewrite fperm_exp_orderV -e fpermK.
- by move/fperm_inj: e => ->; exists n; rewrite fpermX.
Qed.

Lemma exp_orbit n y : ((s ^+ n) y \in orbit) = (y \in orbit).
Proof.
elim: n => [|n IH]; first by rewrite fperm_exp0 fperm1.
by rewrite fperm_expSl fpermM /= mul_orbit IH.
Qed.

Lemma inv_orbit y : (s^-1 y \in orbit) = (y \in orbit).
Proof. by rewrite -[LHS]mul_orbit fpermKV. Qed.

Lemma fset1_orbit : (orbit == [fset x]) = (x \notin finsupp s).
Proof.
rewrite memNfinsupp; apply/(sameP eqP)/(iffP eqP) => Hx.
- apply/eqP; rewrite eqEfsubset fsub1set mem_orbit_id andbT.
  apply/fsubsetP => _ /orbitP [n ->]; rewrite fpermX; exact/fset1P/iter_fix.
- have: s x \in orbit by apply/orbitP; exists 1%N; rewrite fpermX.
  by rewrite Hx => /fset1P.
Qed.

End Orbit.

Arguments orbitP {T s x y}.

Section OrbitTheory.

Local Open Scope fset_scope.
Local Open Scope fperm_scope.

Variables (T : choiceType).
Implicit Types (s : {fperm T}) (x y : T).

Lemma imfset_orbit s x : s @` orbit s x = orbit s x.
Proof.
apply/fsetP=> y; apply/(sameP (imfsetP _ _ _ _))/(iffP idP) => /= [y_x|].
- by exists (s^-1 y); rewrite ?inv_orbit // fpermKV.
- by case=> z z_x ->; rewrite mul_orbit.
Qed.

Lemma eq_orbit s x y : y \in orbit s x -> orbit s x = orbit s y.
Proof.
case/orbitP => {y} n ->; apply/fsetP => y.
apply/(sameP orbitP)/(iffP orbitP)=> [[m ->]|[m ->]].
  by exists (m + n)%N; rewrite fperm_expsD fpermM.
have [nm|/ltnW nm] := leqP n m.
- by exists (m - n); rewrite -[RHS]fpermM -fperm_expsD subnK.
- exists (m + (order s).-1 * n)%N.
  rewrite fperm_expsD fperm_exp_mul fperm_exp_orderV fperm_expV fpermM /=.
  by rewrite fpermK.
Qed.

Lemma fdisjoint_orbit s x y :
  reflect (orbit s x = orbit s y) (orbit s x `&` orbit s y != fset0).
Proof.
apply/(iffP (fset0Pn _)).
- by case=> z /fsetIP [/eq_orbit -> /eq_orbit ->].
- by move=> e; exists x; rewrite in_fsetI -e mem_orbit_id.
Qed.

Lemma orbit1 x : orbit 1 x = [fset x].
Proof. by apply/eqP; rewrite fset1_orbit finsupp1. Qed.

Lemma orbitV s x : orbit s^-1 x = orbit s x.
Proof.
apply/fsetP=> y; apply/(sameP orbitP)/(iffP orbitP)=> [[n ->]|[n ->]].
- exists ((order s^-1).-1 * n)%N; rewrite fperm_exp_mul fperm_exp_orderV.
  by rewrite fperm_invK.
- by exists ((order s).-1 * n)%N; rewrite fperm_exp_mul fperm_exp_orderV.
Qed.

End OrbitTheory.

Section Cyclic.

Local Open Scope fset_scope.
Local Open Scope fperm_scope.

Variables (T : choiceType).
Implicit Types (x y : T) (s : {fperm T}).

Definition is_cyclic s :=
  [forall a : finsupp s, orbit s (val a) == finsupp s].

Fact cycle_at_key : unit. exact: tt. Qed.

Definition cycle_at :=
  locked_with cycle_at_key (fun s x => fperm (orbit s x) s).

Lemma cycle_atE s x y :
  cycle_at s x y = if y \in orbit s x then s y else y.
Proof. by rewrite /cycle_at locked_withE fpermEst ?imfset_orbit. Qed.

Lemma finsupp_cycle_at s x :
  finsupp (cycle_at s x) = if x \in finsupp s then orbit s x else fset0.
Proof.
apply/fsetP=> y; rewrite mem_finsupp cycle_atE; case: (ifPn (x \in finsupp s)).
- case: orbitP => [[n ->] x_s|]; rewrite ?eqxx //.
  rewrite -[X in X != _]fpermM -fperm_expSl fperm_expSr fpermM /=.
  rewrite inj_eq -?mem_finsupp //; exact: fperm_inj.
- move=> x_s; have /eqP ->: orbit s x == [fset x] by rewrite fset1_orbit.
  rewrite in_fset1 in_fset0; case: (y =P x) => [->|_]; rewrite ?eqxx //.
  by rewrite -mem_finsupp (negbTE x_s).
Qed.

Lemma fsubset_finsupp_cycle_at s x :
  finsupp (cycle_at s x) `<=` orbit s x.
Proof. by rewrite finsupp_cycle_at; case: ifP. Qed.

Lemma orbit_cycle_at s x y :
  orbit (cycle_at s x) y =
  if y \in orbit s x then orbit s x else [fset y].
Proof.
have cycle_atXE n z :
    (cycle_at s x ^+ n) z = if z \in orbit s x then (s ^+ n) z else z.
  elim: n => [|n IH]; first by rewrite !fperm_exp0 fperm1 if_same.
  rewrite fperm_expSl fpermM /= fperm_expSl fpermM /= IH cycle_atE.
  have [z_x|-> //] := ifP (z \in orbit s x); by rewrite exp_orbit z_x.
case: ifP => [y_x|y_x].
- rewrite (eq_orbit y_x).
  by apply/fsetP=> z; apply/(sameP orbitP)/(iffP orbitP)=> - [n ->]; exists n;
  rewrite cycle_atXE y_x.
- apply/eqP; rewrite eqEfsubset fsub1set mem_orbit_id andbT.
  by apply/fsubsetP=> _ /orbitP [n ->]; rewrite cycle_atXE y_x in_fset1.
Qed.

Lemma is_cyclic_cycle_at s x : is_cyclic (cycle_at s x).
Proof.
apply/forallP=> /= - [y] /=.
rewrite finsupp_cycle_at; case: ifP => [x_s y_x|//].
by rewrite orbit_cycle_at y_x.
Qed.

Lemma cycle_at1 x : cycle_at 1 x = 1.
Proof. by apply/fpermP=> y; rewrite cycle_atE fperm1 if_same. Qed.

Lemma cycle_atV s x : cycle_at s^-1 x = (cycle_at s x)^-1.
Proof.
apply: (@fperm_mulsI _ (cycle_at s x)); rewrite fperm_mulsV.
apply/fpermP=> y; rewrite fpermM /= fperm1 [cycle_at s^-1 x y]cycle_atE.
rewrite orbitV; case: ifP => y_x; rewrite cycle_atE ?y_x //.
by rewrite inv_orbit y_x fpermKV.
Qed.

Definition cycles s := cycle_at s @` finsupp s.

End Cyclic.

Section Trans.

Local Open Scope fperm_scope.

Lemma inj_fperm2 (T T' : choiceType) (f : T -> T') x y z :
  injective f -> f (fperm2 x y z) = fperm2 (f x) (f y) (f z).
Proof.
move=> f_inj; case: (fperm2P x)=> [->|->| ]; rewrite ?fperm2L ?fperm2R //.
by move=>/eqP hx /eqP hy; apply/esym/fperm2D; rewrite (inj_eq f_inj).
Qed.

Lemma fperm2J (T : choiceType) s (x y : T) :
  s * fperm2 x y * s^-1 = fperm2 (s x) (s y).
Proof.
apply/fpermP=> z; rewrite fpermM /= fpermM /= inj_fperm2 ?fpermKV //.
exact: fperm_inj.
Qed.

End Trans.
