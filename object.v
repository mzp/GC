Require Import Sets.Finite_sets.
Require Import Sets.Ensembles.
Inductive mark :=
  | Marked : mark
  | Unmarked : mark.

Definition In {A : Type} elem sets := Sets.Ensembles.In A sets elem.
Implicit Arguments Sets.Ensembles.Included [U].
Implicit Arguments Sets.Ensembles.Add [U].
Implicit Arguments Sets.Ensembles.Union [U].
Implicit Arguments Sets.Ensembles.Intersection [U].
Implicit Arguments Sets.Finite_sets.Finite [U].

Record Mem (A : Type) := mkMem {
  roots   : Ensemble A;
  nodes   : Ensemble A;
  frees   : Ensemble A;
  marker  : A -> mark;
  pointer : A -> option A
}.
Implicit Arguments roots [A].
Implicit Arguments nodes [A].
Implicit Arguments frees [A].
Implicit Arguments marker [A].
Implicit Arguments pointer [A].
Implicit Arguments mkMem [A].

Inductive Closure (A : Type) (pointer : A -> option A) (root : A) : Ensemble A :=
  | CRefl  : In root (Closure A pointer root)
  | CTrans : forall n m, Some n = pointer root -> In m (Closure A pointer n) -> In m (Closure A pointer root).

Inductive Closures (A : Type) (pointer : A -> option A) (roots : Ensemble A) : Ensemble A :=
  | Closures_intro  : forall n m, In m roots -> In n (Closure A pointer m) -> In n (Closures A pointer roots).
Implicit Arguments Closures [A].

Inductive Marks (A : Type) (marker : A -> mark) (m : mark) (xs : Ensemble A) : Ensemble A :=
  | Marks_intro : forall x, In x xs -> marker x = m -> In x (Marks A marker m xs).

Definition Marker {A : Type} (m1 m2 : Mem A) : Prop :=
  roots   m1 = roots   m2 /\
  nodes   m1 = nodes   m2 /\
  frees   m1 = frees   m2 /\
  pointer m1 = pointer m2 /\
  Included (Closures (pointer m2) (roots m2)) (Marks A (marker m2) Marked (nodes m2)).

Definition Sweeper {A : Type} (m1 m2 : Mem A) : Prop :=
  roots   m1 = roots   m2 /\
  nodes   m1 = nodes   m2 /\
  pointer m1 = pointer m2 /\
  frees   m2 = Union (frees m1) (Marks A (marker m1) Unmarked (nodes m1)) /\
  forall n, In n (nodes m2) -> marker m2 n = Unmarked.

Definition invariant {A : Type} (m : Mem A) : Prop :=
  Included (roots m) (nodes m) /\
  Included (frees m) (nodes m) /\
  forall x y, In x (nodes m) -> Some y = pointer m x -> In y (nodes m).

Lemma marker_invariant : forall A (m1 m2 : Mem A),
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
  Included (Marks A marker m xs) xs.
Proof.
unfold Included.
intros.
inversion H.
tauto.
Qed.

Lemma sweeper_invariant: forall A (m1 m2 : Mem A),
  Sweeper m1 m2 -> invariant m1 -> invariant m2.
Proof.
unfold Sweeper, invariant.
intros.
decompose [and] H.
decompose [and] H0.
rewrite <- H1, <- H2, <- H3, H4.
repeat split; auto.
unfold Included.
intros.
inversion H7; auto.
generalize Marks_include.
intros.
unfold Included in H12.
apply (H12 _ _ (marker m1) Unmarked _).
tauto.
Qed.

Definition frees_invariant {A : Type} (m : Mem A) :=
  Disjoint A (frees m) (Closures (pointer m) (roots m)).

Definition marks_all {A : Type} (m : Mem A) :=
  Disjoint A (Marks A (marker m) Unmarked (nodes m)) (Closures (pointer m) (roots m)).

Lemma sweeper_frees : forall A (m1 m2 : Mem A),
  frees_invariant m1 -> marks_all m1 -> Sweeper m1 m2 -> frees_invariant m2.
Proof.
unfold frees_invariant, marks_all, Sweeper.
intros.
decompose [and] H1.
rewrite <- H2, <- H3, H5.
apply Disjoint_intro; intros.
inversion H.
inversion H0.
specialize (H6 x).
specialize (H8 x).
intro.
inversion H9.
inversion H10.
 apply H6.
 apply Intersection_intro; auto.

 apply H8.
 apply Intersection_intro; auto.
Qed.

Lemma disjoint_include: forall A (B C D : Ensemble A),
  Disjoint A B C -> Included D C -> Disjoint A B D.
Proof.
intros.
inversion H.
apply Disjoint_intro; intros.
intro.
apply (H1 x).
inversion H2.
apply Intersection_intro; auto.
Qed.


Lemma marker_frees : forall A (m1 m2 : Mem A),
  frees_invariant m1 -> Marker m1 m2 -> frees_invariant m2 /\ marks_all m2.
Proof.
unfold frees_invariant, Marker, marks_all.
split; intros.
 decompose [and] H0.
 rewrite <- H1, <- H2, <- H4.
 tauto.

 decompose [and] H0.
 apply (disjoint_include _ _ (Marks A (marker m2) Marked (nodes m2))); auto.
 apply Disjoint_intro.
 intros.
 intro.
 inversion H5.
 inversion H7.
 inversion H8.
 rewrite H11 in H14.
 inversion H14.
Qed.

Definition GC {A : Type} (m1 m2 : Mem A) := exists m : Mem A,
  Marker m1 m /\ Sweeper m m2.
Theorem gc_invariant : forall A (m1 m2 : Mem A),
  invariant m1 -> GC m1 m2 -> invariant m2.
Proof.
unfold GC.
intros.
decompose [ex and] H0.
 apply marker_invariant in H2.
 apply sweeper_invariant in H3.
 tauto.

 tauto.

 tauto.
Qed.

Theorem gc_free: forall A (m1 m2 : Mem A),
  frees_invariant m1 -> GC m1 m2 -> frees_invariant m2.
Proof.
unfold GC.
intros.
decompose [ex and] H0.
 apply marker_frees in H2.
 decompose [and] H2.
 apply sweeper_frees in H3.
  tauto.

  tauto.

 tauto.

 tauto.
Qed.
