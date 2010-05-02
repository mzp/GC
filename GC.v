(* -#- mode:coq coding:utf-8 -#- *)
Require Import Lists.ListSet.
Require Import Lists.List.
Require Import Util.

(** * operations of set *)
Definition In {A : Type} (elem : A) (sets : set A) :=
  set_In elem sets.
Definition Included {A : Type} (B C : set A) : Prop :=
  forall x, In x B -> In x C.
Definition Union {A : Type} (dec : x_dec A) (B C : set A) : set A :=
  set_union dec B C.

(** * Memory *)
Inductive mark :=
  | Marked   : mark
  | Unmarked : mark.

Definition mark_dec : forall (m1 m2 : mark), { m1 = m2} + { m1 <> m2}.
Proof.
decide equality.
Qed.

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
Inductive Connect (A : Type) (next : A -> option A) (root : A) : A -> Prop:=
  | CRoot  :
    Connect A next root root
  | CTrans : forall x y,
    Some y = next x -> Connect A next y x -> Connect A next root x.

Inductive ConnectS (A : Type) (next : A -> option A) (roots : set A) : A -> Prop :=
  | ConnectSet_intro  : forall n m,
    In m roots -> Connect A next m n -> ConnectS A next roots n.

Definition ConnectM {A : Type} (m : Mem) :=
  ConnectS A (pointer m) (roots m).

(** ** Marker utility *)
Definition marks (A : Type) (marker : A -> mark) (ma : mark) (xs : set A) : set A :=
  filter (fun x => if mark_dec (marker x) ma then true else false) xs.

Definition marksM {A : Type} (ma : mark) (m : Mem) :=
  marks A (marker m) ma (nodes m).

(** ** main GC *)
(** marker *)
Definition Marker {A : Type} (m1 m2 : Mem (A:=A)) : Prop :=
  roots   m1 = roots   m2 /\
  nodes   m1 = nodes   m2 /\
  frees   m1 = frees   m2 /\
  pointer m1 = pointer m2 /\
  forall x, ConnectM m2 x -> marker m2 x = Marked.

(** sweeper *)
Definition Sweeper {A : Type} (dec : x_dec A) (m1 m2 : Mem) : Prop :=
  roots   m1 = roots   m2 /\
  nodes   m1 = nodes   m2 /\
  pointer m1 = pointer m2 /\
  frees   m2 = Union dec (frees m1) (marksM Unmarked m1) /\
  forall (n : A), In n (nodes m2) -> marker m2 n = Unmarked.

(** mark & sweep GC *)
Definition GC {A : Type} (dec : x_dec A) (m1 m2 : Mem (A:=A)) := exists m : Mem,
  Marker m1 m /\ Sweeper dec m m2.
