Require Import Sets.Ensembles.

(** * operations of set *)
Definition set A := Ensemble A.
Definition In {A : Type} elem sets := Sets.Ensembles.In A sets elem.
Implicit Arguments Sets.Ensembles.Included [U].
Implicit Arguments Sets.Ensembles.Union [U].

(** * Memory *)
Inductive mark :=
  | Marked   : mark
  | Unmarked : mark.

Record Mem {A : Type} := mkMem {
  roots   : set A;          (** root objects *)
  nodes   : set A;          (** all objects in memory *)
  frees   : set A;          (** free list *)
  marker  : A -> mark;      (** get mark of the object *)
  pointer : A -> option A   (** get next object of the object *)
}.

(** * GC *)

(** ** closure *)
(** [Closure A next x] means a set: {x, next x, next (next x), ... }. *)
Inductive Closure (A : Type) (next : A -> option A) : A -> set A :=
  | CRoot  : forall x,
    In x (Closure A next x)
  | CTrans : forall x y z,
    Some y = next x -> In z (Closure A next y) -> In z (Closure A next x).

Inductive Closures (A : Type) (next : A -> option A) (roots : set A) : set A :=
  | Closures_intro  : forall n m,
    In m roots -> In n (Closure A next m) -> In n (Closures A next roots).
Implicit Arguments Closures [A].

Definition ClosuresM {A : Type} (m : Mem) :=
  Closures (A:=A) (pointer m) (roots m).

(** ** Marker utility *)
Inductive Marks (A : Type) (marker : A -> mark) (m : mark) (xs : set A) : set A :=
  | Marks_intro : forall x,
    In x xs -> marker x = m -> In x (Marks A marker m xs).

Definition MarksM {A : Type} (ma : mark) (m : Mem) :=
  Marks A (marker m) ma (nodes m).

(** ** main GC *)
(** marker *)
Definition Marker {A : Type} (m1 m2 : Mem (A:=A)) : Prop :=
  roots   m1 = roots   m2 /\
  nodes   m1 = nodes   m2 /\
  frees   m1 = frees   m2 /\
  pointer m1 = pointer m2 /\
  Included (ClosuresM m2) (MarksM Marked m2).

(** sweeper *)
Definition Sweeper {A : Type} (m1 m2 : Mem) : Prop :=
  roots   m1 = roots   m2 /\
  nodes   m1 = nodes   m2 /\
  pointer m1 = pointer m2 /\
  frees   m2 = Union (frees m1) (MarksM Unmarked m1) /\
  forall (n : A), In n (nodes m2) -> marker m2 n = Unmarked.

(** mark & sweep GC *)
Definition GC {A : Type} (m1 m2 : Mem (A:=A)) := exists m : Mem,
  Marker m1 m /\ Sweeper m m2.

(** * Spec *)
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
  Included (Marks A marker m xs) xs.
Proof.
unfold Included.
intros.
inversion H.
tauto.
Qed.

Lemma sweeper_invariant: forall A (m1 m2 : Mem (A:=A)),
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

Theorem gc_invariant : forall A (m1 m2 : Mem (A:=A)),
  invariant m1 -> GC m1 m2 -> invariant m2.
Proof.
unfold GC.
intros.
decompose [ex and] H0; auto.
apply marker_invariant in H2; auto.
apply sweeper_invariant in H3; auto.
Qed.

(** safety *)
Definition Safety {A : Type} (m : Mem) : Prop :=
  Disjoint A (frees m) (Closures (pointer m) (roots m)).

Definition MarksAll {A : Type} (m : Mem) : Prop :=
  Disjoint A (Marks A (marker m) Unmarked (nodes m))
             (Closures (pointer m) (roots m)).

Lemma sweeper_safety : forall A (m1 m2 : Mem (A:=A)),
  Safety m1 -> MarksAll m1 -> Sweeper m1 m2 -> Safety m2.
Proof.
unfold Safety, MarksAll, Sweeper.
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

Lemma disjoint_include: forall A (B C D : set A),
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

Lemma marker_safety : forall A (m1 m2 : Mem (A:=A)),
  Safety m1 -> Marker m1 m2 -> Safety m2 /\ MarksAll m2.
Proof.
unfold Safety, Marker, MarksAll.
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

Theorem gc_safety: forall A (m1 m2 : Mem (A:=A)),
  Safety m1 -> GC m1 m2 -> Safety m2.
Proof.
unfold GC.
intros.
decompose [ex and] H0; auto.
apply marker_safety in H2; auto.
decompose [and] H2.
apply sweeper_safety in H3; auto.
Qed.
