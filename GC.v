(* -#- mode:coq coding:utf-8 -#- *)
Require Import Lists.ListSet.
Require Import Lists.List.
Require Import Util.
Require Import Recdef.

(** * 集合操作の定義 *)

(**
   集合の実装をListSet以外にしてもGC本体を修正しなくてすむように、
   集合に対する操作を定義する。

   できれば、集合関連の補題もここで定義しておきたいところ。面倒なので、後回し。
 *)
Definition In {A : Type} (b : A) (B : set A) : Prop :=
  set_In b B.

Definition In_dec {A : Type} (dec : x_dec A) (b : A) (B : set A) : {In b B} + {~ In b B} :=
  set_In_dec dec b B.

Definition Included {A : Type} (B C : set A) : Prop :=
  forall x, In x B -> In x C.

Definition union {A : Type} (dec : x_dec A) (B C : set A) : set A :=
  set_union dec B C.

Definition empty {A : Type} : set A :=
  empty_set A.

Definition remove {A : Type} (dec : x_dec A) b B : set A :=
  set_remove dec b B.

Definition Disjoint {A : Type} (xs ys : set A) := forall x,
  (In x xs -> ~ In x ys) /\ (In x ys -> ~ In x xs).

Lemma union_elim: forall A (dec : x_dec A) (a : A) (B C : set A),
  In a (union dec B C) -> In a B \/ set_In a C.
Proof.
unfold In, union.
apply set_union_elim.
Qed.

(** * メモリのモデル化 *)

(**
   オブジェクトにつけられるマークを定義する。
   比較関数 [mark_dec] も一緒に定義する。
 *)
Inductive mark :=
  | Marked   : mark
  | Unmarked : mark.

Definition mark_dec : forall (m1 m2 : mark), { m1 = m2} + { m1 <> m2}.
Proof.
decide equality.
Qed.

(** メモリはレコードとして定義する。 *)
Record Mem {A : Type} := mkMem {
  nodes  : set A;          (* メモリ内の全オブジェクト *)
  roots  : set A;          (* ルートオブジェクト *)
  frees  : set A;          (* フリーリスト *)
  marker : A -> mark;      (* オブジェクトからマークへの写像 *)
  next   : A -> option A   (* "次"のオブジェクトへの写像 *)
}.

(** * 閉包の定義 *)

(**
ルートオブジェクトから辿れるオブジェクトの集合を、メモリの閉包(closure)として定義する。

閉包は、ルートオブジェクトに [next] を再帰的に適用することで求める。
そのため、単純には停止性が示せない。

引数にメモリ内の全オブジェクトを与える。
閉包に加えたオブジェクトをそこから削除することで、停止性を示す。
 *)
Lemma remove_dec : forall A (dec : x_dec A) x xs,
  In x xs -> length (remove dec x xs) < length xs.
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

(**
   ルートオブジェクトxの閉包を求める。

   閉包に追加したオブジェクトをxsから削除することで、xsの長さが必ず減少するようにした。
*)
Function closure (A : Type) (dec : x_dec A) (next : A -> option A) (x : A) (xs : set A) {measure length xs} : set A :=
  match xs with
    | nil =>
      empty
    | _ =>
      if In_dec dec x xs then
        match next x with
          | None   => x :: empty
          | Some y => x :: closure A dec next y (remove dec x xs)
        end
      else
        empty
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
 simpl in s.
 decompose [or] s.
  rewrite H in n.
  assert False.
   apply n.
   reflexivity.

   contradiction.

 assumption.

 contradiction.
Qed.

(** [closure] を複数のルートオブジェクトに拡張する。 *)
Definition closures (A : Type) (dec : x_dec A) (next : A -> option A) (roots : set A) (nodes : set A) : set A :=
  fold_right (union dec)
             (empty_set A)
             (map (fun x => closure A dec next x nodes) roots).

(** メモリに対して直接、閉包を求めれるようにする。 *)
Definition closuresM {A : Type} (dec : x_dec A) (m : Mem) :=
  closures A dec (next m) (roots m) (nodes m).

(** * GC本体の定義 *)

(**
   指定したマークを持つオブジェクトのみを取りだす関数。
   [marks Marked m]でマークのついたオブジェクトのみを取り出せる。
   *)
Definition marksM {A : Type} (ma : mark) (m : Mem (A:=A)) :=
  filter_dec (fun x => mark_dec (marker m x) ma) (nodes m).

(**
   マークフェーズの前と後のメモリの関係をPropとして定義する。
   具体的な実装を定義してしまうと証明が面倒。ここでは計算できるかなどは気にしない。

   [closuresM dec m2 = marksM Marked m2]でないのは、ルートから辿れないオブジェクトに
   マークがついている場合を許容するため。
   遅延マークスイープの場合だと、マークづけが何度にわけて行なわれる可能性がある。
   その場合、途中でミューテータがメモリ構造を変化させ、ルートから辿れないオブジェクトに
   マークがついている場合が発生する可能性がある。
 *)
Definition MarkPhase {A : Type} (dec : x_dec A) (m1 m2 : Mem) : Prop :=
  roots m1 = roots m2 /\
  nodes m1 = nodes m2 /\
  frees m1 = frees m2 /\
  next  m1 = next  m2 /\
  Included (closuresM dec m2) (marksM Marked m2).

(** 同様にスイープフェーズ前後のメモリの関係を定義する。 *)
Definition SweepPhase {A : Type} (dec : x_dec A) (m1 m2 : Mem) : Prop :=
  roots m1 = roots m2 /\
  nodes m1 = nodes m2 /\
  next  m1 = next  m2 /\
  frees m2 = union dec (frees m1) (marksM Unmarked m1) /\
  forall (n : A), In n (nodes m2) -> marker m2 n = Unmarked.

(** GC前後のメモリの関係を定義する。 *)
Definition GC {A : Type} (dec : x_dec A) (m1 m2 : Mem) := exists m : Mem,
  MarkPhase dec m1 m /\ SweepPhase dec m m2.
