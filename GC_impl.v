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

Theorem marker_correct: forall A (dec : x_dec A) m1 m2,
  Marker dec m1 m2 <-> m2 = marker dec m1.
Proof.
unfold Marker, marker.
split; intros.
 decompose [and] H.
 rewrite (destruct_mem _ m2).
 rewrite H0,H2,H1,H3.
 unfold Included in H5.

