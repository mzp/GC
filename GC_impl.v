Require Import Lists.ListSet.
Require Import Lists.List.
Require Import GC.
Require Import Util.

Definition marker {A : Type} (dec : x_dec A) (m : Mem) :=
  let marks :=
    closuresM dec m
  in
    mkMem A (roots m)
            (nodes m)
            (frees m)
            (fun x => if set_In_dec dec x marks then Marked else Unmarked)
            (pointer m).

Definition sweeper {A : Type} (dec : x_dec A) (m : Mem) : Mem :=
  mkMem A (roots m)
          (nodes m)
          (set_union dec (frees m) (filter_dec (fun n => mark_dec (GC.marker m n) Marked) @@ nodes m))
          (fun _ => Unmarked)
          (pointer m).

Lemma closure_In: forall A (dec : x_dec A) next x xs,
  In x (Closure.closure A dec next x xs) -> In x xs.
Proof.
intros until xs.
pattern x,xs,(Closure.closure A dec next x xs).
apply Closure.closure_ind; simpl; intros; auto; try contradiction.


Theorem marker_correct: forall A (dec : x_dec A) m1 m2,
  m2 = marker dec m1 -> Marker dec m1 m2.
Proof.
unfold marker, Marker.
intros.
destruct m2.
inversion H.
repeat split; auto.
unfold closuresM, marksM, Included.
simpl.
intros.
unfold marks.
apply filter_dec_In_intro.
 unfold closures in H0.

