(* -#- mode:coq coding:utf-8 -#- *)
Require Import Lists.ListSet.
Require Import Lists.List.
Require Import Util.
Require Import GC.

(** invariant *)
Definition invariant {A : Type} (m : Mem) : Prop :=
  Included (roots m) (nodes m) /\
  Included (frees m) (nodes m) /\
  forall (x y :A), In x (nodes m) -> Some y = pointer m x -> In y (nodes m).

Lemma marker_invariant : forall A (m1 m2 : Mem (A:=A)),
  Marker m1 m2 -> invariant m1 -> invariant m2.
Proof.
unfold Marker, invariant.
intros.
decompose [and] H.
decompose [and] H0.
rewrite <-H1, <-H2, <-H3, <-H4.
repeat split; auto.
Qed.

Lemma Marks_include : forall A xs marker m,
  Included (marks A marker m xs) xs.
Proof.
unfold Included, marks, In, set_In.
intros.
apply filter_In in H.
decompose [and] H.
tauto.
Qed.

Lemma sweeper_invariant: forall A (dec : x_dec A) (m1 m2 : Mem (A:=A)),
  Sweeper dec m1 m2 -> invariant m1 -> invariant m2.
Proof.
unfold Sweeper, invariant, Union.
intros.
decompose [and] H.
decompose [and] H0.
rewrite <- H1, <- H2, <- H3, H4.
repeat split; auto.
unfold Included.
intros.
unfold In in H7.
apply set_union_elim in H7.
decompose [or] H7.
 apply H8 in H10.
 tauto.

 apply (Marks_include _ _ (marker m1) Unmarked _).
 tauto.
Qed.

Theorem gc_invariant : forall A (dec : x_dec A) (m1 m2 : Mem (A:=A)),
  invariant m1 -> GC dec m1 m2 -> invariant m2.
Proof.
unfold GC.
intros.
decompose [ex and] H0; auto.
apply marker_invariant in H2; auto.
apply sweeper_invariant in H3; auto.
Qed.

(** safety *)
Definition disjoint (P Q : Prop) :=
  (P -> ~ Q) /\ (Q -> ~ P).

Definition Safety {A : Type} (m : Mem) : Prop := forall x : A,
  disjoint (In x (frees m)) (ConnectM m x).

Definition MarksAll {A : Type} (m : Mem) : Prop := forall x : A,
  disjoint (In x (marksM Unmarked m)) (ConnectM m x).

Lemma sweeper_safety : forall A (dec : x_dec A) (m1 m2 : Mem (A:=A)),
  Safety m1 -> MarksAll m1 -> Sweeper dec m1 m2 -> Safety m2.
Proof.
unfold Safety, MarksAll, Sweeper, ConnectM, disjoint, Union, In.
intros.
decompose [and] (H x).
decompose [and] (H0 x).
decompose [and] H1.
rewrite <- H6, <- H7, H9.
split; intros.
apply set_union_elim in H10.
 decompose [or] H10.
  apply H2 in H12.
  tauto.

  apply H4 in H12.
  tauto.

 intro.
 apply set_union_elim in H12.
 decompose [or] H12.
  apply H2 in H13.
  contradiction.

  apply H4 in H13.
  contradiction.
Qed.

Lemma marker_safety : forall A (m1 m2 : Mem (A:=A)),
  Safety m1 -> Marker m1 m2 -> Safety m2 /\ MarksAll m2.
Proof.
unfold Safety, MarksAll, Marker, ConnectM, disjoint, Union, In.
intros.
decompose [and] H0.
rewrite <- H1, <- H2, <- H4.
rewrite <- H1, <-H4 in H6.
repeat split; intros; decompose [and] (H x); intro.
 apply H8 in H9.
 contradiction.

 apply H7 in H9.
 contradiction.

 generalize H9; intro.
 apply (H6 x) in H9.
 unfold marksM, marks in H5.
 apply filter_In in H5.
 decompose [and] H5.
 destruct (mark_dec (marker m2 x)).
  rewrite H9 in e.
  discriminate.

  discriminate.

 apply H6 in H5.
 unfold marksM, marks in H9.
 apply filter_In in H9.
 decompose [and] H9.
 destruct (mark_dec (marker m2 x)).
  rewrite H5 in e.
  discriminate.

  discriminate.
Qed.

Theorem gc_safety: forall A (dec : x_dec A) (m1 m2 : Mem (A:=A)),
  Safety m1 -> GC dec m1 m2 -> Safety m2.
Proof.
unfold GC.
intros.
decompose [ex and] H0; auto.
apply marker_safety in H2; auto.
decompose [and] H2.
apply sweeper_safety in H3; auto.
Qed.
