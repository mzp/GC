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

type mark =
  | Marked
  | Unmarked

val mark_dec : mark -> mark -> bool

type 'a mem = { roots : 'a set; nodes : 'a set; frees : 
                'a set; marker : ('a -> mark); pointer : 
                ('a -> 'a option) }

val roots : 'a1 mem -> 'a1 set

val nodes : 'a1 mem -> 'a1 set

val frees : 'a1 mem -> 'a1 set

val marker : 'a1 mem -> 'a1 -> mark

val pointer : 'a1 mem -> 'a1 -> 'a1 option

val closure_terminate :
  'a1 x_dec -> ('a1 -> 'a1 option) -> 'a1 -> 'a1 set -> 'a1 set

val closure : 'a1 x_dec -> ('a1 -> 'a1 option) -> 'a1 -> 'a1 set -> 'a1 set

val closures :
  'a1 x_dec -> ('a1 -> 'a1 option) -> 'a1 set -> 'a1 set -> 'a1 set

val closuresM : 'a1 x_dec -> 'a1 mem -> 'a1 set

val markerPhase : 'a1 x_dec -> 'a1 mem -> 'a1 mem

val sweeper : 'a1 x_dec -> 'a1 mem -> 'a1 mem

val gc : 'a1 x_dec -> 'a1 mem -> 'a1 mem

