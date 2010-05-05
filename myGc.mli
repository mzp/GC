type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)

val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

val fold_right : ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 list -> 'a1

type 'a set = 'a list

val empty_set : 'a1 set

val set_add : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 set -> 'a1 set

val set_remove : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 set -> 'a1 set

val set_union : ('a1 -> 'a1 -> bool) -> 'a1 set -> 'a1 set -> 'a1 set

val set_In_dec : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 set -> bool

type 'a x_dec = 'a -> 'a -> bool

val filter_dec : ('a1 -> bool) -> 'a1 list -> 'a1 list

val in_dec : 'a1 x_dec -> 'a1 -> 'a1 set -> bool

val union : 'a1 x_dec -> 'a1 set -> 'a1 set -> 'a1 set

val empty : 'a1 set

val remove : 'a1 x_dec -> 'a1 -> 'a1 set -> 'a1 set

type mark =
  | Marked
  | Unmarked

val mark_dec : mark -> mark -> bool

type 'a mem = { nodes : 'a set; roots : 'a set; frees : 
                'a set; marker : ('a -> mark); next : 
                ('a -> 'a option) }

val nodes : 'a1 mem -> 'a1 set

val roots : 'a1 mem -> 'a1 set

val frees : 'a1 mem -> 'a1 set

val marker : 'a1 mem -> 'a1 -> mark

val next : 'a1 mem -> 'a1 -> 'a1 option

val closure_terminate :
  'a1 x_dec -> ('a1 -> 'a1 option) -> 'a1 -> 'a1 set -> 'a1 set

val closure : 'a1 x_dec -> ('a1 -> 'a1 option) -> 'a1 -> 'a1 set -> 'a1 set

val closures :
  'a1 x_dec -> ('a1 -> 'a1 option) -> 'a1 set -> 'a1 set -> 'a1 set

val closuresM : 'a1 x_dec -> 'a1 mem -> 'a1 set

val mark_phase : 'a1 x_dec -> 'a1 mem -> 'a1 mem

val sweep_phase : 'a1 x_dec -> 'a1 mem -> 'a1 mem

val gc : 'a1 x_dec -> 'a1 mem -> 'a1 mem

