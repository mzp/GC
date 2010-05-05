let __ = let rec f _ = Obj.repr f in Obj.repr f

type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
  | [] -> []
  | a :: t -> (f a) :: (map f t)

(** val fold_right : ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 list -> 'a1 **)

let rec fold_right f a0 = function
  | [] -> a0
  | b :: t -> f b (fold_right f a0 t)

type 'a set = 'a list

(** val empty_set : 'a1 set **)

let empty_set =
  []

(** val set_add : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 set -> 'a1 set **)

let rec set_add aeq_dec a = function
  | [] -> a :: []
  | a1 :: x1 ->
      if aeq_dec a a1 then a1 :: x1 else a1 :: (set_add aeq_dec a x1)

(** val set_remove : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 set -> 'a1 set **)

let rec set_remove aeq_dec a = function
  | [] -> empty_set
  | a1 :: x1 -> if aeq_dec a a1 then x1 else a1 :: (set_remove aeq_dec a x1)

(** val set_union : ('a1 -> 'a1 -> bool) -> 'a1 set -> 'a1 set -> 'a1 set **)

let rec set_union aeq_dec x = function
  | [] -> x
  | a1 :: y1 -> set_add aeq_dec a1 (set_union aeq_dec x y1)

(** val set_In_dec : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 set -> bool **)

let rec set_In_dec aeq_dec a = function
  | [] -> false
  | a0 :: l -> if aeq_dec a a0 then true else set_In_dec aeq_dec a l

type 'a x_dec = 'a -> 'a -> bool

(** val filter_dec : ('a1 -> bool) -> 'a1 list -> 'a1 list **)

let rec filter_dec dec = function
  | [] -> []
  | x :: xs -> if dec x then x :: (filter_dec dec xs) else filter_dec dec xs

type mark =
  | Marked
  | Unmarked

(** val mark_dec : mark -> mark -> bool **)

let mark_dec m1 m2 =
  match m1 with
    | Marked -> (match m2 with
                   | Marked -> true
                   | Unmarked -> false)
    | Unmarked -> (match m2 with
                     | Marked -> false
                     | Unmarked -> true)

type 'a mem = { roots : 'a set; nodes : 'a set; frees : 
                'a set; marker : ('a -> mark); pointer : 
                ('a -> 'a option) }

(** val roots : 'a1 mem -> 'a1 set **)

let roots x = x.roots

(** val nodes : 'a1 mem -> 'a1 set **)

let nodes x = x.nodes

(** val frees : 'a1 mem -> 'a1 set **)

let frees x = x.frees

(** val marker : 'a1 mem -> 'a1 -> mark **)

let marker x = x.marker

(** val pointer : 'a1 mem -> 'a1 -> 'a1 option **)

let pointer x = x.pointer

(** val closure_terminate :
    'a1 x_dec -> ('a1 -> 'a1 option) -> 'a1 -> 'a1 set -> 'a1 set **)

let rec closure_terminate dec next x = function
  | [] -> empty_set
  | a :: l ->
      if set_In_dec dec x (a :: l)
      then (match next x with
              | Some y -> x ::
                  (Obj.magic (fun _ dec0 next0 x0 xs0 _ ->
                    closure_terminate dec0 next0 x0 xs0) __ dec next y
                    (set_remove (Obj.magic dec) (Obj.magic x) (a :: l)) __)
              | None -> (Obj.magic x) :: empty_set)
      else empty_set

(** val closure :
    'a1 x_dec -> ('a1 -> 'a1 option) -> 'a1 -> 'a1 set -> 'a1 set **)

let closure x0 x1 x2 x3 =
  closure_terminate x0 x1 x2 x3

(** val closures :
    'a1 x_dec -> ('a1 -> 'a1 option) -> 'a1 set -> 'a1 set -> 'a1 set **)

let closures dec next roots0 nodes0 =
  fold_right (fun x x0 -> set_union dec x x0) empty_set
    (map (fun x -> closure dec next x nodes0) roots0)

(** val closuresM : 'a1 x_dec -> 'a1 mem -> 'a1 set **)

let closuresM dec m =
  closures dec (fun x -> m.pointer x) m.roots m.nodes

(** val markerPhase : 'a1 x_dec -> 'a1 mem -> 'a1 mem **)

let markerPhase dec m =
  { roots = m.roots; nodes = m.nodes; frees = m.frees; marker = (fun x ->
    if set_In_dec dec x (closuresM dec m) then Marked else Unmarked);
    pointer = (fun x -> m.pointer x) }

(** val sweeper : 'a1 x_dec -> 'a1 mem -> 'a1 mem **)

let sweeper dec m =
  { roots = m.roots; nodes = m.nodes; frees =
    (set_union dec m.frees
      (filter_dec (fun n -> mark_dec (m.marker n) Unmarked) m.nodes));
    marker = (fun x -> Unmarked); pointer = (fun x -> 
    m.pointer x) }

(** val gc : 'a1 x_dec -> 'a1 mem -> 'a1 mem **)

let gc dec m =
  sweeper dec (markerPhase dec m)

