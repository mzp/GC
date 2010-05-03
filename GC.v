(* -#- mode:coq coding:utf-8 -#- *)
Require Import Lists.ListSet.
Require Import Lists.List.
Require Import Util.
Require Import Closure.

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

Lemma destruct_mem : forall A m,
  m = mkMem A (roots m) (nodes m) (frees m) (marker m) (pointer m).
Proof.
intros.
destruct m.
simpl.
reflexivity.
Qed.


(** * GC *)

(** ** closure *)
Definition closures (A : Type) (dec : x_dec A) (next : A -> option A) (roots : set A) (nodes : set A) : set A :=
  fold_left (set_union dec)
            (map (fun x => closure A dec next x nodes) roots)
                 (empty_set A).

Definition closuresM {A : Type} (dec : x_dec A) (m : Mem) :=
  closures A dec (pointer m) (roots m) (nodes m).

(** ** Marker utility *)
Definition marks (A : Type) (marker : A -> mark) (ma : mark) (xs : set A) : set A :=
  filter_dec (fun x => mark_dec (marker x) ma) xs.

Definition marksM {A : Type} (ma : mark) (m : Mem) :=
  marks A (marker m) ma (nodes m).

(** ** main GC *)
(** marker *)
Definition Marker {A : Type} (dec : x_dec A) (m1 m2 : Mem (A:=A)) : Prop :=
  roots   m1 = roots   m2 /\
  nodes   m1 = nodes   m2 /\
  frees   m1 = frees   m2 /\
  pointer m1 = pointer m2 /\
  Included (closuresM dec m2) (marksM Marked m2).

(** sweeper *)
Definition Sweeper {A : Type} (dec : x_dec A) (m1 m2 : Mem) : Prop :=
  roots   m1 = roots   m2 /\
  nodes   m1 = nodes   m2 /\
  pointer m1 = pointer m2 /\
  frees   m2 = Union dec (frees m1) (marksM Unmarked m1) /\
  forall (n : A), In n (nodes m2) -> marker m2 n = Unmarked.

(** mark & sweep GC *)
Definition GC {A : Type} (dec : x_dec A) (m1 m2 : Mem (A:=A)) := exists m : Mem,
  Marker dec m1 m /\ Sweeper dec m m2.
