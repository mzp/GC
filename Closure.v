Require Import Lists.ListSet.
Require Import Lists.List.
Require Import Util.
Require Import Recdef.

Lemma remove_dec : forall A (dec : x_dec A) x xs,
  set_In x xs -> length (set_remove dec x xs) < length xs.
Proof.
intros.
induction xs.
 inversion H.

 simpl.
 destruct (dec x a).
  apply Lt.lt_n_Sn.

  simpl.
  apply Lt.lt_n_S.
  apply IHxs.
  inversion H.
   rewrite H0 in n.
   assert False.
    apply n.
    reflexivity.

    contradiction.

   apply H0.
Qed.

Function closure (A : Type) (dec : x_dec A) (next : A -> option A) (x : A) (xs : set A) {measure length xs} : set A :=
  match xs with
    | nil =>
      empty_set A
    | _ =>
      if set_In_dec dec x xs then
        match next x with
          | None   => x :: empty_set A
          | Some y => x :: closure A dec next y (set_remove dec x xs)
        end
      else
        empty_set A
  end.
Proof.
intros.
simpl.
destruct (dec x a).
 apply Lt.lt_n_Sn.

 simpl.
 apply Lt.lt_n_S.
 apply remove_dec.
 destruct (set_In_dec dec x (a :: l)).
  inversion s.
   rewrite H in n.
   assert False.
    apply n.
    reflexivity.
     contradiction.

     tauto.

  discriminate.
Qed.

Definition closures (A : Type) (dec : x_dec A) (next : A -> option A) (roots : set A) (nodes : set A) : set A :=
  fold_right (set_union dec)
             (empty_set A)
             (map (fun x => closure A dec next x nodes) roots).


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

 apply set_union_elim in H.
 elim H; intros.
  apply closure_In in H0.
  assumption.

  apply IHxs.
  assumption.
Qed.