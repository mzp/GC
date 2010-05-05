Require Import Lists.ListSet.
Require Import Lists.List.
Require Import GC.
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


Lemma remove_In : forall A (dec : x_dec A) x y xs,
  set_In y (set_remove dec x xs) -> set_In y xs.
Proof.
induction xs; simpl; intros.
 contradiction.

 destruct (dec x a).
  right.
  assumption.

  inversion H.
   left.
   assumption.

   apply IHxs in H0.
   right.
   assumption.
Qed.

Lemma closure_In: forall A (dec : x_dec A) next x y xs,
  set_In y (closure A dec next x xs) -> set_In y xs.
Proof.
intros until xs.
pattern x, xs, (closure A dec next x xs).
apply closure_ind; simpl; intros.
 contradiction.

 rewrite <- e.
 decompose [or] H.
  rewrite <- H0.
  assumption.

  contradiction.

 rewrite <- e.
 decompose [or] H0.
  rewrite <- H1.
  assumption.

  apply H in H1.
  apply remove_In in H1.
  assumption.

 contradiction.
Qed.

Lemma closures_In: forall A (dec : x_dec A) next x xs ys,
  set_In x (closures A dec next xs ys) -> set_In x ys.
Proof.
unfold closures.
induction xs; simpl; intros.
 contradiction.

 apply set_union_elim in H.
 elim H; intros.
  apply closure_In in H0.
  assumption.

  apply IHxs.
  assumption.
Qed.

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
