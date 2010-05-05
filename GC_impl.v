Require Import Lists.ListSet.
Require Import Lists.List.
Require Import GC.
Require Import Util.

(** * GCの定義 *)

(** 実際に実行できる形でmark_phaseとsweepr_phaseを実装する。 *)
Definition mark_phase {A : Type} (dec : x_dec A) (m : Mem) :=
  let marks :=
    closuresM dec m
  in
    mkMem A (nodes m)
            (roots m)
            (frees m)
            (fun x => if In_dec dec x marks then Marked else Unmarked)
            (next m).

Definition sweep_phase {A : Type} (dec : x_dec A) (m : Mem) : Mem :=
  mkMem A (nodes m)
          (roots m)
          (union dec (frees m) (filter_dec (fun n => mark_dec (GC.marker m n) Unmarked) @@ nodes m))
          (fun _ => Unmarked)
          (next m).

Definition gc {A : Type} (dec : x_dec A) (m : Mem) : Mem :=
  sweep_phase dec (mark_phase dec m).

(** * 正当性の証明

実装の正当性を示すために、makr_phaseの結果がMarkPhaseを満すことを示す。
*)
Lemma remove_In : forall A (dec : x_dec A) x y xs,
  In y (remove dec x xs) -> In y xs.
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
  In y (closure A dec next x xs) -> In y xs.
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
  In x (closures A dec next xs ys) -> In x ys.
Proof.
unfold closures.
induction xs; simpl; intros.
 contradiction.

 apply union_elim in H.
 elim H; intros.
  apply closure_In in H0.
  assumption.

  apply IHxs.
  assumption.
Qed.

Lemma mark_phase_correct: forall A (dec : x_dec A) m1 m2,
  m2 = mark_phase dec m1 -> MarkPhase dec m1 m2.
Proof.
unfold mark_phase, MarkPhase.
intros.
destruct m2.
inversion H.
repeat split; auto.
unfold closuresM, marksM, Included.
simpl.
intros.
apply filter_dec_In_intro.
 unfold In in H0.
 apply closures_In in H0.
 assumption.

 destruct (In_dec dec x).
  reflexivity.

  contradiction.
Qed.

Lemma sweep_phase_correct: forall A (dec : x_dec A) m1 m2,
  m2 = sweep_phase dec m1 -> SweepPhase dec m1 m2.
Proof.
unfold sweep_phase, SweepPhase.
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
exists (mark_phase dec m1).
split.
 apply mark_phase_correct.
 reflexivity.

 apply sweep_phase_correct.
 assumption.
Qed.

(** extract *)
Require Import ExtractUtil.
Extraction "myGc.ml" gc.
