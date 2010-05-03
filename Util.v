Require Import List.
Require Import Sumbool.

Definition atat {A B:Type} (f: A -> B) x := f x.
Infix "@@" := atat (at level 60).

Definition doll {A B C: Type} (g: B -> C) (f: A -> B) (x: A) := g (f x).
Infix "$" := doll (at level 60).

Definition x_dec A :=
  forall x y : A, {x = y} + {x <> y}.

Fixpoint filter_dec {A : Type} {P Q: A -> Prop} (dec : forall x,{P x} + {Q x}) (l : list A) : list A :=
  match l with
    | nil => nil
    | x :: xs =>
      if dec x then
        x::(filter_dec dec xs)
      else
        filter_dec dec xs
  end.

Lemma filter_dec_In : forall {A: Type} {P Q: A -> Prop} (f : forall x, {P x} + {Q x}) x l,
  In x (filter_dec f l) -> In x l /\ P x.
Proof.
intros A P Q f.
induction l; simpl.
 intro H; elim H.

 case (f a); simpl in |- *.
  intros H _H; elim _H; intros.
  split; [ left | rewrite <- H0 in |- * ]; assumption.

  elim (IHl H0); intros.
  split; [ right | idtac ]; assumption.

  intros _ H; elim (IHl H); intros.
  split; [ right | idtac ]; assumption.
Qed.

