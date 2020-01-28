From mathcomp Require Import all_ssreflect order.

(******************************************************************************)
(* This files provides support for tabulating ordered numbers, such as in sign*)
(* tables of functions.                                                       *)
(*    ext T == the type of ordered types extended with two formal infinities, *)
(*             such that -oo <= x    <= +oo for all x of type ext T,          *)
(*                   and -oo <  t%:x  < +oo for all t of type T.              *)
(*     t%:x == the injection of t of type T in ext T, through the constructor *)
(*             Fin of ext T                                                   *)
(*          := @Fin T t                                                       *)
(*      -oo == the formal minimum element of ext T                            *)
(*          := Infty false                                                    *)
(*      +oo == the formal maximu element of ext T                             *)
(*          := Infty true                                                     *)
(*                                                                            *)
(* Given a sequence s, which is sometimes supposed totally ordered using, and *)
(* sometimes also such that uniq s.                                           *)
(*         s`[i] == | -oo                       if i = 0,                     *)
(*                  | +oo                       if i > size s,                *)
(*                  | the i.-1th element of s   otherwise                     *)
(*               := nth +oo (-oo :: s) i                                      *)
(*    rindex s t == the unique natural number such that                       *)
(*                  s`[rindex s t] < t%:x <= s`[(rindex s t).+1]                *)
(*                  (under total and uniq ordering of rindex)                 *)
(*               := find (>= t) s                                             *)
(*     rprev s t == the last element u of s s.t. u < t, otherwise -oo         *)
(*               := s`[index s t]                                             *)
(*     rnext s t == the first element u of s s.t. t <= u, otherwise +oo       *)
(*               := s`[(index s t).+1]                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.Syntax Order.Def Order.Theory.

Delimit Scope ext_scope with x.
Local Open Scope ext_scope.

Reserved Notation "s `[ i ]" (at level 3, i at level 2, left associativity,
  format "s `[ i ]").

Section extra.

Definition relpre T' T (f : T' -> T) (r : rel T) := [rel x y | r (f x) (f y)].

Lemma nth_rcons_default T (x0 : T) s i : nth x0 (rcons s x0) i = nth x0 s i.
Proof.
by rewrite nth_rcons; case: ltngtP => //[/ltnW ?|->]; rewrite nth_default.
Qed.

Lemma hasNfind (T : Type) (a : pred T) (s : seq T) : ~~ has a s -> find a s = size s.
Proof. by rewrite has_find; case: ltngtP (find_size a s). Qed.

Lemma nth_cons_scanl (T1 : Type) (x1 : T1) (T2 : Type) (g : T1 -> T2 -> T1) (s : seq T2) (n : nat) :
   n <= size s -> forall x : T1, nth x1 (x :: scanl g x s) n = foldl g x (take n s).
Proof. by case: n => //=; [rewrite take0|exact: nth_scanl]. Qed.

Variables (T T' : eqType) (f : T' -> T).

Section mono.
Variables (leT' : rel T') (leT : rel T).

Hypothesis f_mono : {mono f : x y / leT' x y >-> leT x y}.

Lemma mono_path x s :
  path leT (f x) (map f s) = path leT' x s.
Proof. by elim: s => //= y s IHs in x *; rewrite f_mono IHs. Qed.

Lemma mono_sorted : {mono map f : s / sorted leT' s >-> sorted leT s}.
Proof. by case=> //= x s; rewrite mono_path. Qed.
End mono.

Lemma sorted_map leT s : sorted leT (map f s) = sorted (relpre f leT) s.
Proof. exact: mono_sorted. Qed.

End extra.

Section FindSpec.
Variable (T : Type) (a : predPredType T) (s : seq T).

Variant find_spec : bool -> nat -> Type :=
| NotFound of ~~ has a s : find_spec false (size s)
| Found (i : nat) of (i < size s)%N & (forall x0, a (nth x0 s i)) &
  (forall x0 j, j < i -> a (nth x0 s j) = false) : find_spec true i.

Lemma findP : find_spec (has a s) (find a s).
Proof.
have [a_s|aNs] := boolP (has a s); last by rewrite hasNfind//; constructor.
by constructor=> [|x0|x0]; rewrite -?has_find ?nth_find//; apply: before_find.
Qed.

End FindSpec.
Arguments findP {T}.

Local Open Scope order_scope.

Section ext.
Variable (T : Type).

Inductive ext := Infty of bool | Fin of T.

Lemma Fin_inj : injective Fin. Proof. by move=> ? ? []. Qed.
Lemma Infty_inj : injective Infty. Proof. by move=> ? ? []. Qed.

Definition ext_encode x := match x with Infty b => inl b | Fin t => inr t end.
Definition ext_decode a := match a with inl b => Infty b | inr t => Fin t end.
Lemma ext_encodeK : cancel ext_encode ext_decode. Proof. by case. Qed.

Definition finite := [qualify x : ext | if x is Fin _ then true else false].
Coercion is_finite x := x \is finite.

End ext.

Arguments Infty {T}.
Arguments Fin {T}.
Arguments ext_encodeK {T}.
Arguments finite {T}.
Arguments is_finite T /.

Notation "x %:x" := (Fin x) (format "x %:x", left associativity, at level 2) : ext_scope.
Notation "+oo" := (Infty true) (at level 0) : ext_scope.
Notation "-oo" := (Infty false) (at level 0) : ext_scope.
Hint Resolve Fin_inj Infty_inj.

Canonical ext_eqType (T : eqType) := EqType (ext T) (CanEqMixin ext_encodeK).
Canonical ext_choiceType (T : choiceType) :=
  ChoiceType (ext T) (CanChoiceMixin ext_encodeK).
Canonical ext_countType (T : countType) :=
  CountType (ext T) (CanCountMixin ext_encodeK).
Canonical ext_finType (T : finType) :=
  FinType (ext T) (CanFinMixin ext_encodeK).

Section rindex.

Variables (d : unit) (T : orderType d).

Notation ext := (ext T).
Implicit Types (t u v : T) (x y z : ext).

Lemma meetEtotal t u : t `&` u = if t <= u then t else u.
Proof. by case: ltgtP. Qed.

Lemma joinEtotal t u : t `|` u = if u <= t then t else u.
Proof. by case: ltgtP. Qed.

Let FinT_inj := @Fin_inj T.

Definition ext_le x y := match x, y with
  | Infty bl, Infty br => bl ==> br | Fin t, Fin u => t <= u
  | Infty bl, _ => ~~ bl            | _, Infty br => br
end.

Definition ext_lt x y := match x, y with
  | Infty bl, Infty br => ~~ bl && br  | Fin t, Fin u => t < u
  | Infty bl, _ => ~~ bl               | _ , Infty br => br
end.

Definition ext_meet x y := match x, y with
  | Infty bl, Infty br => Infty (bl && br)
  | Infty b, Fin t | Fin t, Infty b => if b then Fin t else Infty b
  | Fin t, Fin u => Fin (t `&` u)
end.

Definition ext_join x y := match x, y with
  | Infty bl, Infty br => Infty (bl || br)
  | Infty b, Fin t | Fin t, Infty b => if b then Infty b else Fin t
  | Fin t, Fin u => Fin (t `|` u)
end.

Lemma ext_lt_def : forall x y, ext_lt x y = (y != x) && ext_le x y.
Proof. by move=> [[]|t] [[]|u]//=; rewrite inj_eq ?lt_def => // ? ? []. Qed.

Lemma ext_meet_def : forall x y, ext_meet x y = if ext_le x y then x else y.
Proof. by move=> [[]|t] [[]|u]//=; rewrite -fun_if meetEtotal. Qed.

Lemma ext_join_def : forall x y, ext_join x y = if ext_le y x then x else y.
Proof. by move=> [[]|t] [[]|u]//=; rewrite -fun_if joinEtotal. Qed.

Lemma ext_le_anti : antisymmetric ext_le.
Proof. by move=> [[]|t] [[]|u]//= /le_anti->. Qed.

Lemma ext_le_trans : transitive ext_le.
Proof. by move=> [[]|t] [[]|u] [[]|v]//=; apply: le_trans. Qed.

Lemma ext_le_total : total ext_le.
Proof. by move=> [[]|t] [[]|u]//=; apply: le_total. Qed.

Definition ext_orderMixin :=
  LeOrderMixin ext_lt_def ext_meet_def ext_join_def ext_le_anti ext_le_trans ext_le_total.

Canonical ext_porderType := POrderType d ext ext_orderMixin.
Canonical ext_latticeType := LatticeType ext ext_orderMixin.
Canonical ext_orderType := OrderType ext ext_orderMixin.

Lemma leEext x y : (x <= y) = (ext_le x y). Proof. by []. Qed.
Lemma ltEext x y : (x < y) = (ext_lt x y). Proof. by []. Qed.
Lemma meetEext x y : (x `&` y) = (ext_meet x y). Proof. by []. Qed.
Lemma joinEext x y : (x `|` y) = (ext_join x y). Proof. by []. Qed.

Lemma ge_xmin x : -oo <= x. Proof. by case: x => [[]|]. Qed.
Lemma le_xmax x : x <= +oo. Proof. by case: x => [[]|]. Qed.
Lemma gt_xmin x : x -> -oo < x. Proof. by case: x. Qed.
Lemma lt_xmax x : x -> x < +oo. Proof. by case: x. Qed.

Lemma meetxmax x : x `&` +oo = x. Proof. by case: x => [[]|]. Qed.
Lemma meetmaxx x : +oo `&` x = x. Proof. by case: x => [[]|]. Qed.
Lemma meetxmin x : x `&` -oo = -oo. Proof. by case: x => [[]|]. Qed.
Lemma meetminx x : -oo `&` x = -oo. Proof. by case: x => [[]|]. Qed.

Lemma joinxmax x : x `|` +oo = +oo. Proof. by case: x => [[]|]. Qed.
Lemma joinmaxx x : +oo `|` x = +oo. Proof. by case: x => [[]|]. Qed.
Lemma joinxmin x : x `|` -oo = x. Proof. by case: x => [[]|]. Qed.
Lemma joinminx x : -oo `|` x = x. Proof. by case: x => [[]|]. Qed.

Section rindex_def.
Variable (x0 : T) (s : seq T).
Hypothesis s_sorted : sorted <=%O s.
Hypothesis s_uniq : uniq s.

Definition rindex t := find (>= t) s.

Lemma rindex_size t : (rindex t <= size s)%N. Proof. exact: find_size. Qed.

(* ---- t -- i ----- j ---- *)
Lemma rindex_le t j : (j < size s)%N -> (rindex t <= j)%N = (t <= nth x0 s j)%O.
Proof.
rewrite /rindex => j_lt; symmetry.
case: findP => [/hasPn/= ltsx|i i_lt x_le xNle].
  by rewrite ltn_geF//; apply/negbTE/ltsx/mem_nth.
case: (leqP i) => [le_ij|/xNle->//].
by rewrite (le_trans (x_le x0))// sorted_le_nth//; apply: le_trans.
Qed.

Lemma rindex_gt t j : j < size s -> (j < rindex t)%N = (nth x0 s j < t)%O.
Proof. by move=> j_lt; rewrite ltnNge rindex_le// ltNge. Qed.

Lemma rindex_ge t j : (0 < j <= size s)%N ->
  (j <= rindex t)%N = (nth x0 s j.-1 < t)%O.
Proof. by case: j => //= j; apply: rindex_gt. Qed.

Lemma rindex_lt t j : (0 < j <= size s)%N ->
  (rindex t < j)%N = (t <= nth x0 s j.-1)%O.
Proof. by move=> jP; rewrite ltnNge rindex_ge// leNgt. Qed.

End rindex_def.
Hint Resolve rindex_size.

Section rindex_theory.
Variable (s : seq T).
Hypothesis s_sorted : sorted <=%O s.
Hypothesis s_uniq : uniq s.

Lemma le_rindex t : all (>= t)%O s -> rindex s t = 0.
Proof. by case: s => //= y s'; case: ltgtP. Qed.

Lemma gt_rindex t : all (< t)%O s -> rindex s t = size s.
Proof. by move=> /allP/= lt_st; apply/hasNfind/hasPn=> y /lt_st; case: ltP. Qed.

Lemma rindex_rcons t u : all (<= t)%O s ->
  rindex (rcons s t) u = if (u <= t)%O then rindex s u else (size s).+1.
Proof.
move=> /allP/= le_st; rewrite /rindex -cats1 find_cat/=.
case: ifPn => [|/hasNfind->]; last by case: ifP; rewrite ?(addn0, addn1).
by move=> /hasP[z zs /le_trans->]//; apply: le_st.
Qed.

End rindex_theory.

Section rindex_take_drop.

Lemma take_rindex s t : sorted <=%O%O s ->
  take (rindex s t) s = [seq y <- s | (y < t)%O].
Proof.
elim: s => //= a s IHs pas; rewrite -IHs ?(path_sorted pas)//.
case: leP => //= le_ta; rewrite le_rindex ?take0//.
by have /(order_path_min le_trans) := pas; apply/sub_all => y; apply: le_trans.
Qed.

Lemma drop_rindex s t : sorted <=%O%O s ->
  drop (rindex s t) s = [seq y <- s | (y >= t)%O].
Proof.
elim: s => //= a s IHs pas; rewrite -IHs ?(path_sorted pas)//.
case: leP => //= le_ta; rewrite le_rindex ?drop0//.
by have /(order_path_min le_trans) := pas; apply/sub_all => y; apply: le_trans.
Qed.

End rindex_take_drop.

Section rindex_seq.

Variable (s : seq T).
Hypothesis s_sorted : sorted <=%O s.
Hypothesis s_uniq : uniq s.

Definition rindex_seq := -oo :: map Fin s.
Local Notation "[ i ]" := (nth +oo rindex_seq i).
Local Notation rprev t := [rindex s t].
Local Notation rnext t := [(rindex s t).+1].

Let s_lt_sorted : sorted <%O s.
Proof. by rewrite lt_sorted_uniq_le s_uniq. Qed.
Hint Resolve le_trans lt_trans.

Lemma rindex_seq_sorted : sorted <=%O rindex_seq.
Proof. by rewrite /= path_min_sorted ?sorted_map// => x; rewrite ge_xmin. Qed.
Hint Resolve rindex_seq_sorted.

Lemma rindex_seq_uniq : uniq rindex_seq.
Proof. by rewrite /= map_inj_uniq ?s_uniq ?andbT//; apply/negP=> /mapP[]. Qed.
Hint Resolve rindex_seq_uniq.

Lemma rindex_seq_lt_sorted : sorted <%O rindex_seq.
Proof. by rewrite lt_sorted_uniq_le rindex_seq_uniq. Qed.
Hint Resolve rindex_seq_lt_sorted.

Lemma eq_from_rindex i j x : (i <= size s)%N -> (j <= size s)%N ->
  ([i] < x <= [i.+1]) -> ([j] < x <= [j.+1]) -> i = j.
Proof.
move=> i_lt j_lt.
wlog lt_ij : i j i_lt j_lt / (i < j)%N => [hw ti tj|/andP[it ti] /andP[jt tj]].
  by have [/hw->//|/hw->//|//] := ltngtP i j.
suff /(le_trans ti) /le_lt_trans /(_ jt) : [i.+1] <= [j] by rewrite ltxx.
by rewrite sorted_le_nth -?topredE//= ?size_map ?ltnS// (leq_trans lt_ij)//.
Qed.

Lemma mem_rnext t : t \in s -> rnext t = t%:x.
Proof.
rewrite /rindex_seq /rindex; elim: (s) (s_sorted) => //= y s' ihs' pys'.
rewrite in_cons => /predU1P [->|ts']; rewrite ?(lexx, eqxx)//.
rewrite le_eqVlt ltNge;  have [->//|/= neq_ty] := altP (t =P y).
rewrite (allP (order_path_min (@le_trans _ _) pys')) //= ihs' //.
exact: path_sorted pys'.
Qed.

Lemma in_rprev t : rprev t \in -oo :: map Fin s.
Proof.
rewrite /= in_cons; case: rindex (rindex_size s t) => //= n n_lt.
by rewrite (nth_map t)// mem_map// mem_nth.
Qed.

Lemma in_rnext t : rnext t \in +oo :: map Fin s.
Proof.
rewrite /= in_cons; case: (ltnP (rindex s t) (size (map Fin s))).
  by move=> /mem_nth->; rewrite orbT.
by move=> /(nth_default _)->.
Qed.

Lemma rindexP t : rprev t < t%:x <= rnext t.
Proof.
rewrite /rindex_seq /=.
have find_small : (rindex s t <= size s)%N by apply: find_size.
apply/andP; split; last first.
  case: ltngtP (find_small) => [//|i_lt|<-] _; last first.
    by rewrite nth_default// ?size_map.
  by rewrite /rindex (nth_map t)// leEext/= nth_find// has_find.
have /= := @before_find _ t (>= t) s (rindex s t).-1; rewrite -/(rindex s t).
case: (rindex _) => [_//|i/=] in find_small * => /(_ (ltnSn _))/negbT.
by rewrite (nth_map t)// ltEext/= -ltNge.
Qed.
Hint Resolve rindexP.

Lemma eq_rindex t u : rprev t < u%:x <= rnext t -> rindex s t = rindex s u.
Proof. by move=> /eq_from_rindex; apply. Qed.

Lemma lt_rprev_rnext t : rprev t < rnext t.
Proof. by have /andP[p_lt /lt_le_trans->] := rindexP t. Qed.
Hint Resolve lt_rprev_rnext.

Section sorted_mono.
Variables (d' : unit) (T' : orderType d) (t0 : T')
  (s' : seq T') (ss : sorted <%O s') (ssle : sorted <=%O s').
Definition toatl_sorted_le_nthW := sorted_le_nth (@le_trans _ _) (@lexx _ _) t0 ssle.
Let sorted_lt_nthW := sorted_lt_nth (@lt_trans _ _) t0 ss.
Definition total_sorted_le_nth := le_mono_in sorted_lt_nthW.
Definition total_sorted_lt_nth := leW_mono_in total_sorted_le_nth.
End sorted_mono.

Lemma rindex_notin i :
  {in [pred t | [i] < t%:x < [i.+1]], forall t, t \in s = false}.
Proof.
move=> t; rewrite inE; have [i_small|i_big] := leqP i (size s); last first.
  by rewrite !nth_default//= ?size_map// 1?ltnW//.
apply: contraTF => /mem_rnext <-.
have rindex_seqmax_sorted : sorted <%O (rcons rindex_seq +oo).
  rewrite -[rcons _ _]revK rev_sorted rev_rcons/=.
  rewrite path_min_sorted// ?rev_sorted//.
  by move=> y; rewrite mem_rev// in_cons => /predU1P[->//|/mapP[? ? ->]].
by rewrite -![[_]]nth_rcons_default !total_sorted_lt_nth ?[_ && _]le_lt_asym//;
   rewrite ?inE/= ?size_rcons ?size_map ?ltnS// ?find_size// 1?leqW//=.
Qed.

Lemma rindexE i : {in [pred t | [i] < t%:x <= [i.+1]], forall t, rindex s t = i}.
Proof.
move=> t; have [i_le|i_gt] := leqP i (size s); first exact: eq_from_rindex.
by rewrite !nth_default//= ?size_map// ltnW.
Qed.

Lemma rindex_next t tnext : rnext t = tnext%:x -> rindex s tnext = rindex s t.
Proof. by move=> sneq; apply: rindexE; rewrite inE -sneq lexx andbT. Qed.

End rindex_seq.
End rindex.

Bind Scope ext_scope with ext.

Notation "s `[ i ]" := (nth +oo%x (rindex_seq s) i) : ext_scope.
Notation rprev s t := s`[rindex s t].
Notation rnext s t := s`[(rindex s t).+1].

Hint Resolve Fin_inj Infty_inj.
Hint Resolve rindex_size rindexP lt_rprev_rnext.
