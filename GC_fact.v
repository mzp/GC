(* -#- mode:coq coding:utf-8 -#- *)
Require Import Lists.ListSet.
Require Import Lists.List.
Require Import Util.
Require Import GC.

(** Invariant *)
Definition Invariant {A : Type} (m : Mem) : Prop :=
  Included (roots m) (nodes m) /\
  Included (frees m) (nodes m) /\
  forall (x y :A), In x (nodes m) -> Some y = pointer m x -> In y (nodes m).

Lemma marker_invariant : forall A dec (m1 m2 : Mem (A:=A)),
  Marker dec m1 m2 -> Invariant m1 -> Invariant m2.
Proof.
unfold Marker, Invariant.
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
apply filter_dec_In_elim in H.
decompose [and] H.
tauto.
Qed.

Lemma sweeper_invariant: forall A (dec : x_dec A) (m1 m2 : Mem (A:=A)),
  Sweeper dec m1 m2 -> Invariant m1 -> Invariant m2.
Proof.
unfold Sweeper, Invariant, Union.
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
  Invariant m1 -> GC dec m1 m2 -> Invariant m2.
Proof.
unfold GC.
intros.
decompose [ex and] H0; auto.
apply marker_invariant in H2; auto.
apply sweeper_invariant in H3; auto.
Qed.

(** safety *)
Definition Disjoint {A : Type} (xs ys : set A) := forall x,
  (set_In x xs -> ~ set_In x ys) /\ (set_In x ys -> ~ set_In x xs).

Definition Safety {A : Type} (dec : x_dec A) (m : Mem) : Prop :=
  Disjoint (frees m) (closuresM dec m).

Definition MarksAll {A : Type} (dec : x_dec A) (m : Mem) : Prop :=
  Disjoint (marksM Unmarked m) (closuresM dec m).

Lemma sweeper_safety : forall A (dec : x_dec A) (m1 m2 : Mem (A:=A)),
  Safety dec m1 -> MarksAll dec m1 -> Sweeper dec m1 m2 -> Safety dec m2.
Proof.
unfold Safety, MarksAll, Sweeper, closuresM, Disjoint, Union, In.
intros.
decompose [and] (H x).
decompose [and] (H0 x).
decompose [and] H1.
rewrite <- H6, <- H7, <- H8, H9.
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

Lemma marks_In : forall A m ma (x : A),
  In x (marksM ma m) -> marker m x = ma.
Proof.
unfold In, marksM, marks.
intros.
apply filter_dec_In_elim in H.
decompose [and] H.
assumption.
Qed.

Lemma marker_safety : forall A (dec : x_dec A) (m1 m2 : Mem (A:=A)),
  Safety dec m1 -> Marker dec m1 m2 -> Safety dec m2 /\ MarksAll dec m2.
Proof.
unfold Safety, MarksAll, Marker, closuresM, Disjoint, Union, In, Included.
intros.
decompose [and] H0.
rewrite <- H1, <- H2,<- H3, <- H4.
rewrite <- H1, <- H3, <-H4 in H6.
repeat split; intros; decompose [and] (H x); intro.
 apply H8 in H9.
 contradiction.

 apply H7 in H9.
 contradiction.

 apply (H6 x) in H9.
 apply marks_In in H5.
 apply marks_In in H9.
 rewrite H9 in H5.
 discriminate.

 apply H6 in H5.
 apply marks_In in H5.
 apply marks_In in H9.
 rewrite H9 in H5.
 discriminate.
Qed.

Theorem gc_safety: forall A (dec : x_dec A) (m1 m2 : Mem (A:=A)),
  Safety dec m1 -> GC dec m1 m2 -> Safety dec m2.
Proof.
unfold GC.
intros.
decompose [ex and] H0; auto.
apply marker_safety in H2; auto.
decompose [and] H2.
apply sweeper_safety in H3; auto.
Qed.
