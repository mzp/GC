Require Import GC.
Require Import Lists.ListSet.
Require Import Lists.List.
Require Import Util.
Require Import Recdef.

Variable A : Type.
Variable dec : x_dec A.

Lemma remove_dec : forall x xs,
  set_In x xs ->
  length (set_remove dec x xs) < length xs.
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

Function closure (next : A -> option A) (x : A) (xs : set A) {measure length xs} : set A :=
  match xs with
    | nil =>
      empty_set A
    | _ =>
      if set_In_dec dec x xs then
        match next x with
          | None   => empty_set A
          | Some y => closure next y (set_remove dec x xs)
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

