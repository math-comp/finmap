From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat choice seq.
From mathcomp Require Import path fintype tuple bigop finset div prime order.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import Order.Theory.
Local Open Scope order_scope.

Section SetOrder.
Variable (d : unit) (T : finOrderType d).
Implicit Types (a b c t : T) (A B C I J : {set T}).

Definition is_interval I :=
  [forall a in I, forall b in I, forall t, (a <= t <= b) ==> (t \in I)].

Lemma is_intervalP I :
  reflect {in I &, forall a b t, a <= t <= b -> t \in I} (is_interval I).
Proof.
by apply: (iffP 'forall_in_'forall_in_'forall_implyP) => hyp ? ? ?; apply: hyp.
Qed.

Definition set_min A := (\meet_(x in A) x).
Definition set_max A := (\join_(x in A) x).

Lemma mem_set_min A : A != set0 -> set_min A \in A.
Proof.
rewrite /set_min => A_neq0; rewrite -big_enum.
have: all (mem A) (enum A) by apply/allP => a; rewrite mem_enum.
have: size (enum A) != 0 by rewrite -cardE cards_eq0.
elim: (enum A) => //= x [|y s] IHs _ /andP[xA ysA]; first by rewrite big_seq1.
by rewrite big_cons/=; case: leP => // _; apply: IHs.
Qed.

Lemma set_min_le A a : a \in A -> set_min A <= a.
Proof. exact: meets_inf. Qed.

Lemma mem_set_max A : A != set0 -> set_max A \in A.
Proof.
rewrite /set_max => A_neq0; rewrite -big_enum.
have: all (mem A) (enum A) by apply/allP => a; rewrite mem_enum.
have: size (enum A) != 0 by rewrite -cardE cards_eq0.
elim: (enum A) => //= x [|y s] IHs _ /andP[xA ysA]; first by rewrite big_seq1.
by rewrite big_cons/=; case: leP => // _; apply: IHs.
Qed.

Lemma set_max_ge A a : a \in A -> a <= set_max A.
Proof. exact: join_sup. Qed.

Definition set_le A B := [forall a in A, forall b in B, (a <= b)].
Notation ":<=:%set" := set_le (at level 0) : form_scope.
Notation "A :<=: B" := (set_le A B)
  (at level 70, format "A  :<=:  B") : set_scope.
Notation "a <=: B" := ([set a] :<=: B)
  (at level 70, format "a  <=:  B") : set_scope.
Notation "A :<= b" := (A :<=: [set b])
  (at level 70, format "A  :<=  b") : set_scope.
Notation "A :<=: B :<=: C" := ((A :<=: B) && (B :<=: C))
  (at level 70, B at next level, C at next level, format "A  :<=:  B  :<=:  C").

Lemma set_leP A B : reflect {in A & B, forall a b, (a <= b)} (A :<=: B).
Proof. by apply: (iffP 'forall_in_'forall_in_idP) => hyp ? ? ?; apply: hyp. Qed.

Definition set_lt A B := [forall a in A, forall b in B, (a < b)].
Notation ":<:%set" := set_lt (at level 0) : form_scope.
Notation "A :<: B" := (set_lt A B) (at level 70, format "A  :<:  B") : set_scope.
Notation "a <: B" := ([set a] :<: B)
  (at level 70, format "a  <:  B") : set_scope.
Notation "A :< b" := (A :<: [set b])
  (at level 70, format "A  :<  b") : set_scope.
Notation "A :<: B :<: C" := ((A :<: B) && (B :<: C))
  (at level 70, B at next level, C at next level, format "A  :<:  B  :<:  C").
Notation "A :<=: B :<: C" := ((A :<=: B) && (B :<: C))
  (at level 70, B at next level, C at next level, format "A  :<=:  B  :<:  C").
Notation "A :<: B :<=: C" := ((A :<: B) && (B :<=: C))
  (at level 70, B at next level, C at next level, format "A  :<:  B  :<=:  C").

Lemma set_ltP A B : reflect {in A & B, forall a b, (a < b)} (A :<: B).
Proof. by apply: (iffP 'forall_in_'forall_in_idP) => hyp ? ? ?; apply: hyp. Qed.

Definition set_glued A B := (A :<=: B) && (set_max A < set_min B).
Notation ":<|:%set" := set_glued (at level 0).
Notation "A :<|: B" := (set_glued A B) (at level 70, format "A  :<|:  B").
Notation "A :<|: B :<|: C" := ((A :<|: B) && (B :<|: C))
  (at level 70, B at next level, C at next level, format "A  :<|:  B  :<|:  C").

Lemma set_glued_lt A B : A :<|: B -> A :<: B.
Proof.
move=> /andP[/set_leP leAB lt_MA_mB]; apply/set_ltP=> a b aA bB.
by rewrite (le_lt_trans (set_max_ge aA))// (lt_le_trans _ (set_min_le bB)).
Qed.

Definition set_between A B := [set t | A :<: [set t] :<: B].
Notation "A :<_<: B" := (set_between A B)
  (B at next level, at level 52, format "A  :<_<:  B").

Lemma set_glue_between A B C : reflect (B = A :<_<: C) (A :<|: B :<|: C).
Proof.
apply: (iffP idP) => [/andP[AB BC]|->]; last first.
  rewrite /:<|:%set -!andbA; apply/and4P; split.
  - apply/set_leP => a b aA.
    by rewrite !inE => /andP[/set_ltP] /(_ _ b aA _) /ltW->//; rewrite inE.
  - admit.
  - admit.
  - admit.
apply/setP => x; rewrite !inE.
Admitted.


End SetOrder.
