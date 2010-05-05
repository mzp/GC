Require Import Lists.ListSet.
Require Import Lists.List.
Require Import GC.
Require Import Closure.
Require Import Util.
Require Import ExtractUtil.

Definition markerPhase {A : Type} (dec : x_dec A) (m : Mem) :=
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
          (set_union dec (frees m) (filter_dec (fun n => mark_dec (GC.marker m n) Unmarked) @@ nodes m))
          (fun _ => Unmarked)
          (pointer m).

Definition gc {A : Type} (dec : x_dec A) (m : Mem) : Mem :=
  sweeper dec (markerPhase dec m).

Lemma marker_correct: forall A (dec : x_dec A) m1 m2,
  m2 = markerPhase dec m1 -> Marker dec m1 m2.
Proof.
unfold markerPhase, Marker.
intros.
destruct m2.
inversion H.
repeat split; auto.
unfold closuresM, marksM, Included.
simpl.
intros.
unfold marks.
apply filter_dec_In_intro.
 unfold In in H0.
 apply closures_In in H0.
 assumption.

 destruct (set_In_dec dec x).
  reflexivity.

  contradiction.
Qed.

Lemma sweeper_correct: forall A (dec : x_dec A) m1 m2,
  m2 = sweeper dec m1 -> Sweeper dec m1 m2.
Proof.
unfold sweeper, Sweeper.
intros.
destruct m2; simpl.
inversion H.
repeat split; auto.
Qed.

Theorem gc_correct : forall A (dec : x_dec A) m1 m2,
  m2 = gc dec m1 -> GC dec m1 m2.
Proof.
unfold gc, GC.
intros.
exists (markerPhase dec m1).
split.
 apply marker_correct.
 reflexivity.

 apply sweeper_correct.
 assumption.
Qed.

Extraction "myGc.ml" markerPhase sweeper gc.
