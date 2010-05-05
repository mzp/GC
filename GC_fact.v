(* -#- mode:coq coding:utf-8 -#- *)
Require Import Lists.ListSet.
Require Import Lists.List.
Require Import Util.
Require Import GC.

(** * Invariantの証明 *)

(**
   手始めに簡単な性質を示してみる。

   GCの前後で、ルートオブジェクトやフリーリスト、オブジェクト同士のつなが
   りが変化しないことを示す。
*)
Definition Invariant {A : Type} (m : Mem) : Prop :=
  Included (roots m) (nodes m) /\
  Included (frees m) (nodes m) /\
  forall (x y :A), In x (nodes m) -> Some y = next m x -> In y (nodes m).

(** マークフェーズの前後でInvariantが保たれることを証明する。 *)
Lemma MarkPhase_Invariant : forall A (dec : x_dec A) (m1 m2 : Mem),
  MarkPhase dec m1 m2 -> Invariant m1 -> Invariant m2.
Proof.
unfold MarkPhase, Invariant.
intros.
decompose [and] H.
decompose [and] H0.
rewrite <-H1, <-H2, <-H3, <-H4.
repeat split; auto.
Qed.

(** スイープフェーズの前後でInvariantが保たれることを証明する。 *)
Lemma marks_Include : forall A ma (m : Mem (A:=A)),
  Included (marksM ma m) (nodes m).
Proof.
unfold Included, marksM, In, set_In.
intros.
apply filter_dec_In_elim in H.
decompose [and] H.
tauto.
Qed.

Lemma SweepPhase_Invariant: forall A (dec : x_dec A) (m1 m2 : Mem (A:=A)),
  SweepPhase dec m1 m2 -> Invariant m1 -> Invariant m2.
Proof.
unfold SweepPhase, Invariant.
intros.
decompose [and] H.
decompose [and] H0.
rewrite <- H1, <- H2, <- H3, H4.
repeat split; auto.
unfold Included.
intros.
apply union_elim in H7.
decompose [or] H7.
 apply H8 in H10.
 tauto.

 apply (marks_Include A Unmarked _).
 tauto.
Qed.

(** GCの前後でInvariantが保たれることを証明する。 *)
Theorem GC_Invariant : forall A (dec : x_dec A) (m1 m2 : Mem (A:=A)),
  Invariant m1 -> GC dec m1 m2 -> Invariant m2.
Proof.
unfold GC.
intros.
decompose [ex and] H0; auto.
apply MarkPhase_Invariant in H2; auto.
apply SweepPhase_Invariant in H3; auto.
Qed.

(** Safetyの証明 *)

(**
   フリーリストにあるオブジェクトと、ルートから辿れる
   オブジェクトには重複がないことを証明する。
   *)
Definition Safety {A : Type} (dec : x_dec A) (m : Mem) : Prop :=
  Disjoint (frees m) (closuresM dec m).

(**
   Safetyを直接示すことはできない。
   マークフェーズの直後では、ルートから辿れるオブジェクトにはマークがついていない
   ことを示す必要がある。
*)
Definition MarksAll {A : Type} (dec : x_dec A) (m : Mem) : Prop :=
  Disjoint (marksM Unmarked m) (closuresM dec m).

(** SweepPhaseの前後でSafetyが成り立つことを示す。 *)
Lemma SweepPhase_Safety : forall A (dec : x_dec A) (m1 m2 : Mem (A:=A)),
  SweepPhase dec m1 m2 -> Safety dec m1 -> MarksAll dec m1 -> Safety dec m2.
Proof.
unfold Safety, MarksAll, SweepPhase, closuresM, Disjoint.
intros.
decompose [and] H.
decompose [and] (H0 x).
decompose [and] (H1 x).
rewrite <- H2, <- H3, <- H4, H5.
split; intros.
apply union_elim in H11.
 decompose [or] H11;
   [ apply H6 in H12 | apply H9 in H12 ];
   tauto.

 intro.
 apply union_elim in H12.
 decompose [or] H12;
   [ apply H6 in H13 | apply H9 in H13];
  contradiction.
Qed.

Lemma marks_In : forall A m ma (x : A),
  In x (marksM ma m) -> marker m x = ma.
Proof.
unfold In, marksM.
intros.
apply filter_dec_In_elim in H.
decompose [and] H.
assumption.
Qed.

(** マークフェーズの前後でSafetyとMarksAllが成り立つことを示す。 *)
Lemma MarkPhase_Safety : forall A (dec : x_dec A) (m1 m2 : Mem (A:=A)),
  MarkPhase dec m1 m2 -> Safety dec m1 -> Safety dec m2 /\ MarksAll dec m2.
Proof.
unfold Safety, MarksAll, MarkPhase, closuresM, Disjoint.
intros.
decompose [and] H.
rewrite <- H1, <- H2,<- H3, <- H4.
rewrite <- H1, <- H3, <-H4 in H6.
repeat split; intros; decompose [and] (H0 x); intro.
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

(** GCの前後でSafetyが成り立つことを示す。 *)
Theorem GC_Safety: forall A (dec : x_dec A) (m1 m2 : Mem (A:=A)),
  GC dec m1 m2 -> Safety dec m1 -> Safety dec m2.
Proof.
unfold GC.
intros.
decompose [ex and] H; auto.
apply MarkPhase_Safety in H2; auto.
decompose [and] H2.
apply SweepPhase_Safety in H3; auto.
Qed.
