module Bachelor_formally_verified_stuff
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let p: u8 = mk_u8 10

type t_Polynomium (v_T: Type0) = { f_coeffs:Alloc.Vec.t_Vec v_T Alloc.Alloc.t_Global }

let impl_5 (#v_T: Type0) (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core.Clone.t_Clone v_T)
    : Core.Clone.t_Clone (t_Polynomium v_T) = { f_clone = (fun x -> x) }

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_6': #v_T: Type0 -> {| i1: Core.Fmt.t_Debug v_T |} -> Core.Fmt.t_Debug (t_Polynomium v_T)

unfold
let impl_6 (#v_T: Type0) (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core.Fmt.t_Debug v_T) =
  impl_6' #v_T #i1

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_7': #v_T: Type0 -> Core.Marker.t_StructuralPartialEq (t_Polynomium v_T)

unfold
let impl_7 (#v_T: Type0) = impl_7' #v_T

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_8': #v_T: Type0 -> {| i1: Core.Cmp.t_PartialEq v_T v_T |}
  -> Core.Cmp.t_PartialEq (t_Polynomium v_T) (t_Polynomium v_T)

unfold
let impl_8
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core.Cmp.t_PartialEq v_T v_T)
     = impl_8' #v_T #i1

type t_Scalar = { f_v:f_v: u8{b2t (f_v <. p <: bool)} }

let impl__len (v_T: usize) (self: t_Polynomium (t_Array t_Scalar v_T)) : usize =
  Alloc.Vec.impl_1__len #(t_Array t_Scalar v_T) #Alloc.Alloc.t_Global self.f_coeffs

let impl_Polynomium_of_Scalar__len (self: t_Polynomium t_Scalar) : usize =
  Alloc.Vec.impl_1__len #t_Scalar #Alloc.Alloc.t_Global self.f_coeffs

let impl_10: Core.Clone.t_Clone t_Scalar = { f_clone = (fun x -> x) }

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_9': Core.Marker.t_Copy t_Scalar

unfold
let impl_9 = impl_9'

let impl_Scalar__ZERO: t_Scalar = { f_v = mk_u8 0 } <: t_Scalar

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_3: Core.Ops.Arith.t_Add t_Scalar t_Scalar =
  {
    f_Output = t_Scalar;
    f_add_pre = (fun (self: t_Scalar) (rhs: t_Scalar) -> true);
    f_add_post = (fun (self: t_Scalar) (rhs: t_Scalar) (out: t_Scalar) -> true);
    f_add
    =
    fun (self: t_Scalar) (rhs: t_Scalar) -> { f_v = (self.f_v +! rhs.f_v <: u8) %! p } <: t_Scalar
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_4: Core.Ops.Arith.t_Sub t_Scalar t_Scalar =
  {
    f_Output = t_Scalar;
    f_sub_pre = (fun (self: t_Scalar) (rhs: t_Scalar) -> true);
    f_sub_post = (fun (self: t_Scalar) (rhs: t_Scalar) (out: t_Scalar) -> true);
    f_sub
    =
    fun (self: t_Scalar) (rhs: t_Scalar) ->
      { f_v = ((self.f_v +! p <: u8) -! rhs.f_v <: u8) %! p } <: t_Scalar
  }

#push-options "--z3rlimit 100"

let add_vec (v_T: usize) (lhs rhs: t_Array t_Scalar v_T)
    : Prims.Pure (t_Array t_Scalar v_T)
      (requires
        (Core.Slice.impl__len #t_Scalar (lhs <: t_Slice t_Scalar) <: usize) =.
        (Core.Slice.impl__len #t_Scalar (rhs <: t_Slice t_Scalar) <: usize))
      (ensures
        fun res ->
          let res:t_Array t_Scalar v_T = res in
          (Core.Slice.impl__len #t_Scalar (res <: t_Slice t_Scalar) <: usize) >=. mk_usize 0 &&
          (Core.Slice.impl__len #t_Scalar (res <: t_Slice t_Scalar) <: usize) <=.
          Core.Num.impl_usize__MAX) =
  let res:t_Array t_Scalar v_T = Rust_primitives.Hax.repeat impl_Scalar__ZERO v_T in
  let res:t_Array t_Scalar v_T =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      v_T
      (fun res temp_1_ ->
          let res:t_Array t_Scalar v_T = res in
          let _:usize = temp_1_ in
          true)
      res
      (fun res i ->
          let res:t_Array t_Scalar v_T = res in
          let i:usize = i in
          Rust_primitives.Hax.Monomorphized_update_at.update_at_usize res
            i
            (Core.Ops.Arith.f_add #t_Scalar
                #t_Scalar
                #FStar.Tactics.Typeclasses.solve
                (Core.Clone.f_clone #t_Scalar
                    #FStar.Tactics.Typeclasses.solve
                    (lhs.[ i ] <: t_Scalar)
                  <:
                  t_Scalar)
                (Core.Clone.f_clone #t_Scalar
                    #FStar.Tactics.Typeclasses.solve
                    (rhs.[ i ] <: t_Scalar)
                  <:
                  t_Scalar)
              <:
              t_Scalar)
          <:
          t_Array t_Scalar v_T)
  in
  res

#pop-options

let get_summed
      (v_T: usize)
      (v: Alloc.Vec.t_Vec (t_Array t_Scalar v_T & t_Array t_Scalar v_T) Alloc.Alloc.t_Global)
    : Alloc.Vec.t_Vec (t_Array t_Scalar v_T) Alloc.Alloc.t_Global =
  Core.Iter.Traits.Iterator.f_collect #(Core.Iter.Adapters.Map.t_Map
        (Core.Slice.Iter.t_Iter (t_Array t_Scalar v_T & t_Array t_Scalar v_T))
        ((t_Array t_Scalar v_T & t_Array t_Scalar v_T) -> t_Array t_Scalar v_T))
    #FStar.Tactics.Typeclasses.solve
    #(Alloc.Vec.t_Vec (t_Array t_Scalar v_T) Alloc.Alloc.t_Global)
    (Core.Iter.Traits.Iterator.f_map #(Core.Slice.Iter.t_Iter
          (t_Array t_Scalar v_T & t_Array t_Scalar v_T))
        #FStar.Tactics.Typeclasses.solve
        #(t_Array t_Scalar v_T)
        (Core.Slice.impl__iter #(t_Array t_Scalar v_T & t_Array t_Scalar v_T)
            (Core.Ops.Deref.f_deref #(Alloc.Vec.t_Vec (t_Array t_Scalar v_T & t_Array t_Scalar v_T)
                    Alloc.Alloc.t_Global)
                #FStar.Tactics.Typeclasses.solve
                v
              <:
              t_Slice (t_Array t_Scalar v_T & t_Array t_Scalar v_T))
          <:
          Core.Slice.Iter.t_Iter (t_Array t_Scalar v_T & t_Array t_Scalar v_T))
        (fun temp_0_ ->
            let l, r:(t_Array t_Scalar v_T & t_Array t_Scalar v_T) = temp_0_ in
            add_vec v_T l r <: t_Array t_Scalar v_T)
      <:
      Core.Iter.Adapters.Map.t_Map
        (Core.Slice.Iter.t_Iter (t_Array t_Scalar v_T & t_Array t_Scalar v_T))
        ((t_Array t_Scalar v_T & t_Array t_Scalar v_T) -> t_Array t_Scalar v_T))

let get_zipped (v_T: usize) (lhs rhs: Alloc.Vec.t_Vec (t_Array t_Scalar v_T) Alloc.Alloc.t_Global)
    : Alloc.Vec.t_Vec (t_Array t_Scalar v_T & t_Array t_Scalar v_T) Alloc.Alloc.t_Global =
  Core.Iter.Traits.Iterator.f_collect #(Core.Iter.Adapters.Map.t_Map
        (Core.Iter.Adapters.Zip.t_Zip (Core.Slice.Iter.t_Iter (t_Array t_Scalar v_T))
            (Core.Slice.Iter.t_Iter (t_Array t_Scalar v_T)))
        ((t_Array t_Scalar v_T & t_Array t_Scalar v_T)
            -> (t_Array t_Scalar v_T & t_Array t_Scalar v_T)))
    #FStar.Tactics.Typeclasses.solve
    #(Alloc.Vec.t_Vec (t_Array t_Scalar v_T & t_Array t_Scalar v_T) Alloc.Alloc.t_Global)
    (Core.Iter.Traits.Iterator.f_map #(Core.Iter.Adapters.Zip.t_Zip
            (Core.Slice.Iter.t_Iter (t_Array t_Scalar v_T))
            (Core.Slice.Iter.t_Iter (t_Array t_Scalar v_T)))
        #FStar.Tactics.Typeclasses.solve
        #(t_Array t_Scalar v_T & t_Array t_Scalar v_T)
        (Core.Iter.Traits.Iterator.f_zip #(Core.Slice.Iter.t_Iter (t_Array t_Scalar v_T))
            #FStar.Tactics.Typeclasses.solve
            #(Core.Slice.Iter.t_Iter (t_Array t_Scalar v_T))
            (Core.Slice.impl__iter #(t_Array t_Scalar v_T)
                (Core.Ops.Deref.f_deref #(Alloc.Vec.t_Vec (t_Array t_Scalar v_T)
                        Alloc.Alloc.t_Global)
                    #FStar.Tactics.Typeclasses.solve
                    lhs
                  <:
                  t_Slice (t_Array t_Scalar v_T))
              <:
              Core.Slice.Iter.t_Iter (t_Array t_Scalar v_T))
            (Core.Slice.impl__iter #(t_Array t_Scalar v_T)
                (Core.Ops.Deref.f_deref #(Alloc.Vec.t_Vec (t_Array t_Scalar v_T)
                        Alloc.Alloc.t_Global)
                    #FStar.Tactics.Typeclasses.solve
                    rhs
                  <:
                  t_Slice (t_Array t_Scalar v_T))
              <:
              Core.Slice.Iter.t_Iter (t_Array t_Scalar v_T))
          <:
          Core.Iter.Adapters.Zip.t_Zip (Core.Slice.Iter.t_Iter (t_Array t_Scalar v_T))
            (Core.Slice.Iter.t_Iter (t_Array t_Scalar v_T)))
        (fun temp_0_ ->
            let a, b:(t_Array t_Scalar v_T & t_Array t_Scalar v_T) = temp_0_ in
            (Core.Clone.f_clone #(t_Array t_Scalar v_T) #FStar.Tactics.Typeclasses.solve a
              <:
              t_Array t_Scalar v_T),
            (Core.Clone.f_clone #(t_Array t_Scalar v_T) #FStar.Tactics.Typeclasses.solve b
              <:
              t_Array t_Scalar v_T)
            <:
            (t_Array t_Scalar v_T & t_Array t_Scalar v_T))
      <:
      Core.Iter.Adapters.Map.t_Map
        (Core.Iter.Adapters.Zip.t_Zip (Core.Slice.Iter.t_Iter (t_Array t_Scalar v_T))
            (Core.Slice.Iter.t_Iter (t_Array t_Scalar v_T)))
        ((t_Array t_Scalar v_T & t_Array t_Scalar v_T)
            -> (t_Array t_Scalar v_T & t_Array t_Scalar v_T)))

#push-options "--z3rlimit 100"

let test2 (v_T: usize) (lhs rhs: Alloc.Vec.t_Vec (t_Array t_Scalar v_T) Alloc.Alloc.t_Global)
    : Prims.Pure (Alloc.Vec.t_Vec (t_Array t_Scalar v_T) Alloc.Alloc.t_Global)
      (requires
        (let _, out:(Core.Iter.Adapters.Zip.t_Zip (Core.Slice.Iter.t_Iter (t_Array t_Scalar v_T))
              (Core.Slice.Iter.t_Iter (t_Array t_Scalar v_T)) &
            bool) =
            Core.Iter.Traits.Iterator.f_all #(Core.Iter.Adapters.Zip.t_Zip
                  (Core.Slice.Iter.t_Iter (t_Array t_Scalar v_T))
                  (Core.Slice.Iter.t_Iter (t_Array t_Scalar v_T)))
              #FStar.Tactics.Typeclasses.solve
              (Core.Iter.Traits.Iterator.f_zip #(Core.Slice.Iter.t_Iter (t_Array t_Scalar v_T))
                  #FStar.Tactics.Typeclasses.solve
                  #(Core.Slice.Iter.t_Iter (t_Array t_Scalar v_T))
                  (Core.Slice.impl__iter #(t_Array t_Scalar v_T)
                      (Core.Ops.Deref.f_deref #(Alloc.Vec.t_Vec (t_Array t_Scalar v_T)
                              Alloc.Alloc.t_Global)
                          #FStar.Tactics.Typeclasses.solve
                          lhs
                        <:
                        t_Slice (t_Array t_Scalar v_T))
                    <:
                    Core.Slice.Iter.t_Iter (t_Array t_Scalar v_T))
                  (Core.Slice.impl__iter #(t_Array t_Scalar v_T)
                      (Core.Ops.Deref.f_deref #(Alloc.Vec.t_Vec (t_Array t_Scalar v_T)
                              Alloc.Alloc.t_Global)
                          #FStar.Tactics.Typeclasses.solve
                          rhs
                        <:
                        t_Slice (t_Array t_Scalar v_T))
                    <:
                    Core.Slice.Iter.t_Iter (t_Array t_Scalar v_T))
                <:
                Core.Iter.Adapters.Zip.t_Zip (Core.Slice.Iter.t_Iter (t_Array t_Scalar v_T))
                  (Core.Slice.Iter.t_Iter (t_Array t_Scalar v_T)))
              (fun temp_0_ ->
                  let a, b:(t_Array t_Scalar v_T & t_Array t_Scalar v_T) = temp_0_ in
                  (Core.Slice.impl__len #t_Scalar (a <: t_Slice t_Scalar) <: usize) =.
                  (Core.Slice.impl__len #t_Scalar (b <: t_Slice t_Scalar) <: usize)
                  <:
                  bool)
          in
          out))
      (fun _ -> Prims.l_True) =
  let zipped:Alloc.Vec.t_Vec (t_Array t_Scalar v_T & t_Array t_Scalar v_T) Alloc.Alloc.t_Global =
    get_zipped v_T lhs rhs
  in
  let summed:Alloc.Vec.t_Vec (t_Array t_Scalar v_T) Alloc.Alloc.t_Global = get_summed v_T zipped in
  Alloc.Vec.impl__new #(t_Array t_Scalar v_T) ()

#pop-options

let all_vecs_eq_len (v_T: usize) (l r: Alloc.Vec.t_Vec (t_Array t_Scalar v_T) Alloc.Alloc.t_Global)
    : Prims.Pure bool
      (requires
        (Alloc.Vec.impl_1__len #(t_Array t_Scalar v_T) #Alloc.Alloc.t_Global l <: usize) >.
        mk_usize 0 &&
        (Alloc.Vec.impl_1__len #(t_Array t_Scalar v_T) #Alloc.Alloc.t_Global r <: usize) >.
        mk_usize 0)
      (fun _ -> Prims.l_True) =
  let _, out:(Core.Iter.Adapters.Zip.t_Zip (Core.Slice.Iter.t_Iter (t_Array t_Scalar v_T))
      (Core.Slice.Iter.t_Iter (t_Array t_Scalar v_T)) &
    bool) =
    Core.Iter.Traits.Iterator.f_all #(Core.Iter.Adapters.Zip.t_Zip
          (Core.Slice.Iter.t_Iter (t_Array t_Scalar v_T))
          (Core.Slice.Iter.t_Iter (t_Array t_Scalar v_T)))
      #FStar.Tactics.Typeclasses.solve
      (Core.Iter.Traits.Iterator.f_zip #(Core.Slice.Iter.t_Iter (t_Array t_Scalar v_T))
          #FStar.Tactics.Typeclasses.solve
          #(Core.Slice.Iter.t_Iter (t_Array t_Scalar v_T))
          (Core.Slice.impl__iter #(t_Array t_Scalar v_T)
              (Core.Ops.Deref.f_deref #(Alloc.Vec.t_Vec (t_Array t_Scalar v_T) Alloc.Alloc.t_Global)
                  #FStar.Tactics.Typeclasses.solve
                  l
                <:
                t_Slice (t_Array t_Scalar v_T))
            <:
            Core.Slice.Iter.t_Iter (t_Array t_Scalar v_T))
          (Core.Slice.impl__iter #(t_Array t_Scalar v_T)
              (Core.Ops.Deref.f_deref #(Alloc.Vec.t_Vec (t_Array t_Scalar v_T) Alloc.Alloc.t_Global)
                  #FStar.Tactics.Typeclasses.solve
                  r
                <:
                t_Slice (t_Array t_Scalar v_T))
            <:
            Core.Slice.Iter.t_Iter (t_Array t_Scalar v_T))
        <:
        Core.Iter.Adapters.Zip.t_Zip (Core.Slice.Iter.t_Iter (t_Array t_Scalar v_T))
          (Core.Slice.Iter.t_Iter (t_Array t_Scalar v_T)))
      (fun temp_0_ ->
          let a, b:(t_Array t_Scalar v_T & t_Array t_Scalar v_T) = temp_0_ in
          (Core.Slice.impl__len #t_Scalar (a <: t_Slice t_Scalar) <: usize) =.
          (Core.Slice.impl__len #t_Scalar (b <: t_Slice t_Scalar) <: usize)
          <:
          bool)
  in
  (Alloc.Vec.impl_1__len #(t_Array t_Scalar v_T) #Alloc.Alloc.t_Global l <: usize) =.
  (Alloc.Vec.impl_1__len #(t_Array t_Scalar v_T) #Alloc.Alloc.t_Global r <: usize) &&
  out

#push-options "--z3rlimit 100"

let add_vec_vec (v_T: usize) (lhs rhs: Alloc.Vec.t_Vec (t_Array t_Scalar v_T) Alloc.Alloc.t_Global)
    : Prims.Pure (Alloc.Vec.t_Vec (t_Array t_Scalar v_T) Alloc.Alloc.t_Global)
      (requires
        (Alloc.Vec.impl_1__len #(t_Array t_Scalar v_T) #Alloc.Alloc.t_Global lhs <: usize) =.
        (Alloc.Vec.impl_1__len #(t_Array t_Scalar v_T) #Alloc.Alloc.t_Global rhs <: usize))
      (ensures
        fun res ->
          let res:Alloc.Vec.t_Vec (t_Array t_Scalar v_T) Alloc.Alloc.t_Global = res in
          (Alloc.Vec.impl_1__len #(t_Array t_Scalar v_T) #Alloc.Alloc.t_Global res <: usize) >=.
          mk_usize 0 &&
          (Alloc.Vec.impl_1__len #(t_Array t_Scalar v_T) #Alloc.Alloc.t_Global res <: usize) <=.
          Core.Num.impl_usize__MAX) =
  let res:Alloc.Vec.t_Vec (t_Array t_Scalar v_T) Alloc.Alloc.t_Global =
    Alloc.Vec.impl__new #(t_Array t_Scalar v_T) ()
  in
  let res:Alloc.Vec.t_Vec (t_Array t_Scalar v_T) Alloc.Alloc.t_Global =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      (Alloc.Vec.impl_1__len #(t_Array t_Scalar v_T) #Alloc.Alloc.t_Global lhs <: usize)
      (fun res temp_1_ ->
          let res:Alloc.Vec.t_Vec (t_Array t_Scalar v_T) Alloc.Alloc.t_Global = res in
          let _:usize = temp_1_ in
          true)
      res
      (fun res i ->
          let res:Alloc.Vec.t_Vec (t_Array t_Scalar v_T) Alloc.Alloc.t_Global = res in
          let i:usize = i in
          Alloc.Vec.impl_1__push #(t_Array t_Scalar v_T)
            #Alloc.Alloc.t_Global
            res
            (add_vec v_T (lhs.[ i ] <: t_Array t_Scalar v_T) (rhs.[ i ] <: t_Array t_Scalar v_T)
              <:
              t_Array t_Scalar v_T)
          <:
          Alloc.Vec.t_Vec (t_Array t_Scalar v_T) Alloc.Alloc.t_Global)
  in
  res

#pop-options

#push-options "--z3rlimit 100"

let sub_vec (v_T: usize) (lhs rhs: t_Array t_Scalar v_T)
    : Prims.Pure (t_Array t_Scalar v_T)
      (requires
        (Core.Slice.impl__len #t_Scalar (lhs <: t_Slice t_Scalar) <: usize) =.
        (Core.Slice.impl__len #t_Scalar (rhs <: t_Slice t_Scalar) <: usize))
      (ensures
        fun res ->
          let res:t_Array t_Scalar v_T = res in
          (Core.Slice.impl__len #t_Scalar (res <: t_Slice t_Scalar) <: usize) >=. mk_usize 0 &&
          (Core.Slice.impl__len #t_Scalar (res <: t_Slice t_Scalar) <: usize) <=.
          Core.Num.impl_usize__MAX) =
  let res:t_Array t_Scalar v_T = Rust_primitives.Hax.repeat impl_Scalar__ZERO v_T in
  let res:t_Array t_Scalar v_T =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      (if
          (Core.Slice.impl__len #t_Scalar (lhs <: t_Slice t_Scalar) <: usize) <.
          (Core.Slice.impl__len #t_Scalar (rhs <: t_Slice t_Scalar) <: usize)
          <:
          bool
        then Core.Slice.impl__len #t_Scalar (lhs <: t_Slice t_Scalar) <: usize
        else Core.Slice.impl__len #t_Scalar (rhs <: t_Slice t_Scalar) <: usize)
      (fun res temp_1_ ->
          let res:t_Array t_Scalar v_T = res in
          let _:usize = temp_1_ in
          true)
      res
      (fun res i ->
          let res:t_Array t_Scalar v_T = res in
          let i:usize = i in
          Rust_primitives.Hax.Monomorphized_update_at.update_at_usize res
            i
            (Core.Ops.Arith.f_sub #t_Scalar
                #t_Scalar
                #FStar.Tactics.Typeclasses.solve
                (lhs.[ i ] <: t_Scalar)
                (rhs.[ i ] <: t_Scalar)
              <:
              t_Scalar)
          <:
          t_Array t_Scalar v_T)
  in
  res

#pop-options

/// For extending a polynomial of scalars.
let extend_from (lhs rhs: Alloc.Vec.t_Vec t_Scalar Alloc.Alloc.t_Global)
    : Alloc.Vec.t_Vec t_Scalar Alloc.Alloc.t_Global =
  let res:Alloc.Vec.t_Vec t_Scalar Alloc.Alloc.t_Global =
    Core.Clone.f_clone #(Alloc.Vec.t_Vec t_Scalar Alloc.Alloc.t_Global)
      #FStar.Tactics.Typeclasses.solve
      lhs
  in
  let res:Alloc.Vec.t_Vec t_Scalar Alloc.Alloc.t_Global =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      (Alloc.Vec.impl_1__len #t_Scalar #Alloc.Alloc.t_Global rhs <: usize)
      (fun res temp_1_ ->
          let res:Alloc.Vec.t_Vec t_Scalar Alloc.Alloc.t_Global = res in
          let _:usize = temp_1_ in
          true)
      res
      (fun res i ->
          let res:Alloc.Vec.t_Vec t_Scalar Alloc.Alloc.t_Global = res in
          let i:usize = i in
          Alloc.Vec.impl_1__push #t_Scalar #Alloc.Alloc.t_Global res (rhs.[ i ] <: t_Scalar)
          <:
          Alloc.Vec.t_Vec t_Scalar Alloc.Alloc.t_Global)
  in
  res

#push-options "--z3rlimit 100"

let add_scalar_polynomium (lhs rhs: t_Polynomium t_Scalar)
    : Prims.Pure (t_Polynomium t_Scalar)
      (requires
        (impl_Polynomium_of_Scalar__len lhs <: usize) >=. mk_usize 0 &&
        (impl_Polynomium_of_Scalar__len lhs <: usize) <=. Core.Num.impl_usize__MAX &&
        (impl_Polynomium_of_Scalar__len rhs <: usize) >=. mk_usize 0 &&
        (impl_Polynomium_of_Scalar__len rhs <: usize) <=. Core.Num.impl_usize__MAX)
      (ensures
        fun res ->
          let res:t_Polynomium t_Scalar = res in
          (impl_Polynomium_of_Scalar__len res <: usize) >=. mk_usize 0 &&
          (impl_Polynomium_of_Scalar__len res <: usize) <=. Core.Num.impl_usize__MAX) =
  let min_len:usize =
    if
      (impl_Polynomium_of_Scalar__len lhs <: usize) <. (impl_Polynomium_of_Scalar__len rhs <: usize)
    then impl_Polynomium_of_Scalar__len lhs
    else impl_Polynomium_of_Scalar__len rhs
  in
  let coeffs:Alloc.Vec.t_Vec t_Scalar Alloc.Alloc.t_Global = Alloc.Vec.impl__new #t_Scalar () in
  let coeffs:Alloc.Vec.t_Vec t_Scalar Alloc.Alloc.t_Global =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      min_len
      (fun coeffs temp_1_ ->
          let coeffs:Alloc.Vec.t_Vec t_Scalar Alloc.Alloc.t_Global = coeffs in
          let _:usize = temp_1_ in
          true)
      coeffs
      (fun coeffs i ->
          let coeffs:Alloc.Vec.t_Vec t_Scalar Alloc.Alloc.t_Global = coeffs in
          let i:usize = i in
          Alloc.Vec.impl_1__push #t_Scalar
            #Alloc.Alloc.t_Global
            coeffs
            (Core.Ops.Arith.f_add #t_Scalar
                #t_Scalar
                #FStar.Tactics.Typeclasses.solve
                (lhs.f_coeffs.[ i ] <: t_Scalar)
                (rhs.f_coeffs.[ i ] <: t_Scalar)
              <:
              t_Scalar)
          <:
          Alloc.Vec.t_Vec t_Scalar Alloc.Alloc.t_Global)
  in
  {
    f_coeffs
    =
    if min_len <. (impl_Polynomium_of_Scalar__len lhs <: usize)
    then
      extend_from (Alloc.Slice.impl__to_vec #t_Scalar
            (Core.Ops.Deref.f_deref #(Alloc.Vec.t_Vec t_Scalar Alloc.Alloc.t_Global)
                #FStar.Tactics.Typeclasses.solve
                coeffs
              <:
              t_Slice t_Scalar)
          <:
          Alloc.Vec.t_Vec t_Scalar Alloc.Alloc.t_Global)
        (Alloc.Slice.impl__to_vec #t_Scalar
            (Core.Ops.Deref.f_deref #(Alloc.Vec.t_Vec t_Scalar Alloc.Alloc.t_Global)
                #FStar.Tactics.Typeclasses.solve
                lhs.f_coeffs
              <:
              t_Slice t_Scalar)
          <:
          Alloc.Vec.t_Vec t_Scalar Alloc.Alloc.t_Global)
    else
      if min_len <. (impl_Polynomium_of_Scalar__len rhs <: usize)
      then
        extend_from (Alloc.Slice.impl__to_vec #t_Scalar
              (Core.Ops.Deref.f_deref #(Alloc.Vec.t_Vec t_Scalar Alloc.Alloc.t_Global)
                  #FStar.Tactics.Typeclasses.solve
                  coeffs
                <:
                t_Slice t_Scalar)
            <:
            Alloc.Vec.t_Vec t_Scalar Alloc.Alloc.t_Global)
          (Alloc.Slice.impl__to_vec #t_Scalar
              (Core.Ops.Deref.f_deref #(Alloc.Vec.t_Vec t_Scalar Alloc.Alloc.t_Global)
                  #FStar.Tactics.Typeclasses.solve
                  rhs.f_coeffs
                <:
                t_Slice t_Scalar)
            <:
            Alloc.Vec.t_Vec t_Scalar Alloc.Alloc.t_Global)
      else
        Alloc.Slice.impl__to_vec #t_Scalar
          (Core.Ops.Deref.f_deref #(Alloc.Vec.t_Vec t_Scalar Alloc.Alloc.t_Global)
              #FStar.Tactics.Typeclasses.solve
              coeffs
            <:
            t_Slice t_Scalar)
  }
  <:
  t_Polynomium t_Scalar

#pop-options

/// The same but with a vector of vectors
let extend_from_vec
      (v_T: usize)
      (lhs rhs: Alloc.Vec.t_Vec (t_Array t_Scalar v_T) Alloc.Alloc.t_Global)
    : Alloc.Vec.t_Vec (t_Array t_Scalar v_T) Alloc.Alloc.t_Global =
  let res:Alloc.Vec.t_Vec (t_Array t_Scalar v_T) Alloc.Alloc.t_Global =
    Core.Clone.f_clone #(Alloc.Vec.t_Vec (t_Array t_Scalar v_T) Alloc.Alloc.t_Global)
      #FStar.Tactics.Typeclasses.solve
      lhs
  in
  let res:Alloc.Vec.t_Vec (t_Array t_Scalar v_T) Alloc.Alloc.t_Global =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      (Alloc.Vec.impl_1__len #(t_Array t_Scalar v_T) #Alloc.Alloc.t_Global rhs <: usize)
      (fun res temp_1_ ->
          let res:Alloc.Vec.t_Vec (t_Array t_Scalar v_T) Alloc.Alloc.t_Global = res in
          let _:usize = temp_1_ in
          true)
      res
      (fun res i ->
          let res:Alloc.Vec.t_Vec (t_Array t_Scalar v_T) Alloc.Alloc.t_Global = res in
          let i:usize = i in
          Alloc.Vec.impl_1__push #(t_Array t_Scalar v_T)
            #Alloc.Alloc.t_Global
            res
            (Core.Clone.f_clone #(t_Array t_Scalar v_T)
                #FStar.Tactics.Typeclasses.solve
                (rhs.[ i ] <: t_Array t_Scalar v_T)
              <:
              t_Array t_Scalar v_T)
          <:
          Alloc.Vec.t_Vec (t_Array t_Scalar v_T) Alloc.Alloc.t_Global)
  in
  res
