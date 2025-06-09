module Bachelor_formally_verified_stuff.Convert
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let max
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core.Cmp.t_PartialOrd v_T v_T)
      (a b: v_T)
    : v_T = if Core.Cmp.f_gt #v_T #v_T #FStar.Tactics.Typeclasses.solve a b then a else b

let min
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core.Cmp.t_PartialOrd v_T v_T)
      (a b: v_T)
    : v_T = if Core.Cmp.f_lt #v_T #v_T #FStar.Tactics.Typeclasses.solve a b then a else b
