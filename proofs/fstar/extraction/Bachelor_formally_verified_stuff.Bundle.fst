module Bachelor_formally_verified_stuff.Bundle
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let v_PRIME: u128 = mk_u128 17

type t_Scalar = { f_v:f_v: u128{b2t (f_v <. v_PRIME <: bool)} }

let impl_6: Core.Clone.t_Clone t_Scalar = { f_clone = (fun x -> x) }

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_5': Core.Marker.t_Copy t_Scalar

unfold
let impl_5 = impl_5'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_7': Core.Marker.t_StructuralPartialEq t_Scalar

unfold
let impl_7 = impl_7'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_8': Core.Cmp.t_PartialEq t_Scalar t_Scalar

unfold
let impl_8 = impl_8'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_9': Core.Fmt.t_Debug t_Scalar

unfold
let impl_9 = impl_9'

let impl__ZERO: t_Scalar = { f_v = mk_u128 0 } <: t_Scalar

let impl__ONE: t_Scalar = { f_v = mk_u128 1 } <: t_Scalar

let impl__from (n: u128) : t_Scalar = { f_v = n %! v_PRIME } <: t_Scalar

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_1: Core.Ops.Arith.t_Add t_Scalar t_Scalar =
  {
    f_Output = t_Scalar;
    f_add_pre = (fun (self: t_Scalar) (rhs: t_Scalar) -> true);
    f_add_post = (fun (self: t_Scalar) (rhs: t_Scalar) (out: t_Scalar) -> true);
    f_add
    =
    fun (self: t_Scalar) (rhs: t_Scalar) ->
      { f_v = (self.f_v +! rhs.f_v <: u128) %! v_PRIME } <: t_Scalar
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_2: Core.Ops.Arith.t_Sub t_Scalar t_Scalar =
  {
    f_Output = t_Scalar;
    f_sub_pre = (fun (self: t_Scalar) (rhs: t_Scalar) -> true);
    f_sub_post = (fun (self: t_Scalar) (rhs: t_Scalar) (out: t_Scalar) -> true);
    f_sub
    =
    fun (self: t_Scalar) (rhs: t_Scalar) ->
      { f_v = ((self.f_v +! v_PRIME <: u128) -! rhs.f_v <: u128) %! v_PRIME } <: t_Scalar
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_3: Core.Ops.Arith.t_Mul t_Scalar t_Scalar =
  {
    f_Output = t_Scalar;
    f_mul_pre = (fun (self: t_Scalar) (rhs: t_Scalar) -> true);
    f_mul_post = (fun (self: t_Scalar) (rhs: t_Scalar) (out: t_Scalar) -> true);
    f_mul
    =
    fun (self: t_Scalar) (rhs: t_Scalar) ->
      Core.Iter.Traits.Iterator.f_fold #(Core.Ops.Range.t_Range u128)
        #FStar.Tactics.Typeclasses.solve
        #t_Scalar
        ({ Core.Ops.Range.f_start = mk_u128 0; Core.Ops.Range.f_end = rhs.f_v }
          <:
          Core.Ops.Range.t_Range u128)
        impl__ZERO
        (fun acc temp_1_ ->
            let acc:t_Scalar = acc in
            let _:u128 = temp_1_ in
            Core.Ops.Arith.f_add #t_Scalar #t_Scalar #FStar.Tactics.Typeclasses.solve acc self
            <:
            t_Scalar)
  }

let impl__pow (self: t_Scalar) (n: u128) : t_Scalar =
  let res:t_Scalar = impl__ONE in
  let res:t_Scalar =
    Rust_primitives.Hax.Folds.fold_range (mk_u128 0)
      n
      (fun res temp_1_ ->
          let res:t_Scalar = res in
          let _:u128 = temp_1_ in
          true)
      res
      (fun res temp_1_ ->
          let res:t_Scalar = res in
          let _:u128 = temp_1_ in
          Core.Ops.Arith.f_mul #t_Scalar #t_Scalar #FStar.Tactics.Typeclasses.solve res self
          <:
          t_Scalar)
  in
  res

let impl__invert (self: t_Scalar) : t_Scalar = impl__pow self (v_PRIME -! mk_u128 2 <: u128)

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_4: Core.Fmt.t_Display t_Scalar =
  {
    f_fmt_pre = (fun (self: t_Scalar) (f: Core.Fmt.t_Formatter) -> true);
    f_fmt_post
    =
    (fun
        (self: t_Scalar)
        (f: Core.Fmt.t_Formatter)
        (out1: (Core.Fmt.t_Formatter & Core.Result.t_Result Prims.unit Core.Fmt.t_Error))
        ->
        true);
    f_fmt
    =
    fun (self: t_Scalar) (f: Core.Fmt.t_Formatter) ->
      let tmp0, out:(Core.Fmt.t_Formatter & Core.Result.t_Result Prims.unit Core.Fmt.t_Error) =
        Core.Fmt.impl_11__write_fmt f
          (Core.Fmt.impl_4__new_v1 (mk_usize 1)
              (mk_usize 1)
              (let list = [""] in
                FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                Rust_primitives.Hax.array_of_list 1 list)
              (let list =
                  [Core.Fmt.Rt.impl_1__new_display #u128 self.f_v <: Core.Fmt.Rt.t_Argument]
                in
                FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                Rust_primitives.Hax.array_of_list 1 list)
            <:
            Core.Fmt.t_Arguments)
      in
      let f:Core.Fmt.t_Formatter = tmp0 in
      let hax_temp_output:Core.Result.t_Result Prims.unit Core.Fmt.t_Error = out in
      f, hax_temp_output
      <:
      (Core.Fmt.t_Formatter & Core.Result.t_Result Prims.unit Core.Fmt.t_Error)
  }

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

class t_Scalable (v_Self: Type0) = {
  f_mul_vec_scalar_pre:v_Self -> t_Scalar -> Type0;
  f_mul_vec_scalar_post:v_Self -> t_Scalar -> v_Self -> Type0;
  f_mul_vec_scalar:x0: v_Self -> x1: t_Scalar
    -> Prims.Pure v_Self
        (f_mul_vec_scalar_pre x0 x1)
        (fun result -> f_mul_vec_scalar_post x0 x1 result)
}

class t_EqLen (v_Self: Type0) (v_T: usize) = {
  f_hadamard_pre:v_Self -> t_Array t_Scalar v_T -> Type0;
  f_hadamard_post:v_Self -> t_Array t_Scalar v_T -> v_Self -> Type0;
  f_hadamard:x0: v_Self -> x1: t_Array t_Scalar v_T
    -> Prims.Pure v_Self (f_hadamard_pre x0 x1) (fun result -> f_hadamard_post x0 x1 result)
}

class t_AddSub (v_Self: Type0) (v_T: usize) = {
  f_add_vec_pre:v_Self -> t_Array t_Scalar v_T -> Type0;
  f_add_vec_post:v_Self -> t_Array t_Scalar v_T -> t_Array t_Scalar v_T -> Type0;
  f_add_vec:x0: v_Self -> x1: t_Array t_Scalar v_T
    -> Prims.Pure (t_Array t_Scalar v_T)
        (f_add_vec_pre x0 x1)
        (fun result -> f_add_vec_post x0 x1 result);
  f_sub_vec_pre:v_Self -> t_Array t_Scalar v_T -> Type0;
  f_sub_vec_post:v_Self -> t_Array t_Scalar v_T -> t_Array t_Scalar v_T -> Type0;
  f_sub_vec:x0: v_Self -> x1: t_Array t_Scalar v_T
    -> Prims.Pure (t_Array t_Scalar v_T)
        (f_sub_vec_pre x0 x1)
        (fun result -> f_sub_vec_post x0 x1 result)
}

class t_Matrix (v_Self: Type0) = {
  f_dims_pre:v_Self -> Type0;
  f_dims_post:v_Self -> (usize & usize) -> Type0;
  f_dims:x0: v_Self
    -> Prims.Pure (usize & usize) (f_dims_pre x0) (fun result -> f_dims_post x0 result)
}

/// Computes the inner product between two vectors
/// of scalars, e.g. [1, 2, 3] x [4, 5, 6] = 32.
let inner_prod_scalars (v_T: usize) (v_A v_B: t_Array t_Scalar v_T) : t_Scalar =
  let acc:t_Scalar = impl__ZERO in
  let acc:t_Scalar =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter #(Core.Iter.Adapters.Zip.t_Zip
              (Core.Slice.Iter.t_Iter t_Scalar) (Core.Slice.Iter.t_Iter t_Scalar))
          #FStar.Tactics.Typeclasses.solve
          (Core.Iter.Traits.Iterator.f_zip #(Core.Slice.Iter.t_Iter t_Scalar)
              #FStar.Tactics.Typeclasses.solve
              #(Core.Slice.Iter.t_Iter t_Scalar)
              (Core.Slice.impl__iter #t_Scalar (v_A <: t_Slice t_Scalar)
                <:
                Core.Slice.Iter.t_Iter t_Scalar)
              (Core.Slice.impl__iter #t_Scalar (v_B <: t_Slice t_Scalar)
                <:
                Core.Slice.Iter.t_Iter t_Scalar)
            <:
            Core.Iter.Adapters.Zip.t_Zip (Core.Slice.Iter.t_Iter t_Scalar)
              (Core.Slice.Iter.t_Iter t_Scalar))
        <:
        Core.Iter.Adapters.Zip.t_Zip (Core.Slice.Iter.t_Iter t_Scalar)
          (Core.Slice.Iter.t_Iter t_Scalar))
      acc
      (fun acc temp_1_ ->
          let acc:t_Scalar = acc in
          let a, b:(t_Scalar & t_Scalar) = temp_1_ in
          Core.Ops.Arith.f_add #t_Scalar
            #t_Scalar
            #FStar.Tactics.Typeclasses.solve
            acc
            (Core.Ops.Arith.f_mul #t_Scalar
                #t_Scalar
                #FStar.Tactics.Typeclasses.solve
                (Core.Clone.f_clone #t_Scalar #FStar.Tactics.Typeclasses.solve a <: t_Scalar)
                (Core.Clone.f_clone #t_Scalar #FStar.Tactics.Typeclasses.solve b <: t_Scalar)
              <:
              t_Scalar)
          <:
          t_Scalar)
  in
  acc

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
  let res:t_Array t_Scalar v_T = Rust_primitives.Hax.repeat impl__ZERO v_T in
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
  let res:t_Array t_Scalar v_T = Rust_primitives.Hax.repeat impl__ZERO v_T in
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

let main (_: Prims.unit) : Prims.unit =
  let e_1_:t_Scalar = { f_v = mk_u128 1 } <: t_Scalar in
  let e_2_:t_Scalar = { f_v = mk_u128 2 } <: t_Scalar in
  let e_3_:t_Scalar = { f_v = mk_u128 3 } <: t_Scalar in
  let e_4_:t_Scalar = { f_v = mk_u128 4 } <: t_Scalar in
  let e_5_:t_Scalar = { f_v = mk_u128 5 } <: t_Scalar in
  let e_6_:t_Scalar = { f_v = mk_u128 6 } <: t_Scalar in
  let (l: t_Array t_Scalar (mk_usize 3)):t_Array t_Scalar (mk_usize 3) =
    let list = [e_1_; e_2_; e_3_] in
    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 3);
    Rust_primitives.Hax.array_of_list 3 list
  in
  let (r: t_Array t_Scalar (mk_usize 3)):t_Array t_Scalar (mk_usize 3) =
    let list = [e_1_; e_2_; e_3_] in
    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 3);
    Rust_primitives.Hax.array_of_list 3 list
  in
  let _:t_Array t_Scalar (mk_usize 3) = add_vec (mk_usize 3) l r in
  ()

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

type t_Polynomium (v_T: Type0) = { f_coeffs:Alloc.Vec.t_Vec v_T Alloc.Alloc.t_Global }

let impl_11 (#v_T: Type0) (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core.Clone.t_Clone v_T)
    : Core.Clone.t_Clone (t_Polynomium v_T) = { f_clone = (fun x -> x) }

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_12': #v_T: Type0 -> {| i1: Core.Fmt.t_Debug v_T |} -> Core.Fmt.t_Debug (t_Polynomium v_T)

unfold
let impl_12 (#v_T: Type0) (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core.Fmt.t_Debug v_T) =
  impl_12' #v_T #i1

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_13': #v_T: Type0 -> Core.Marker.t_StructuralPartialEq (t_Polynomium v_T)

unfold
let impl_13 (#v_T: Type0) = impl_13' #v_T

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_14': #v_T: Type0 -> {| i1: Core.Cmp.t_PartialEq v_T v_T |}
  -> Core.Cmp.t_PartialEq (t_Polynomium v_T) (t_Polynomium v_T)

unfold
let impl_14
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core.Cmp.t_PartialEq v_T v_T)
     = impl_14' #v_T #i1

/// Makes it so that a polynomial can be trimmed
class t_Trim (v_Self: Type0) (v_T: Type0) = {
  f_trim_pre:v_Self -> Type0;
  f_trim_post:v_Self -> v_T -> Type0;
  f_trim:x0: v_Self -> Prims.Pure v_T (f_trim_pre x0) (fun result -> f_trim_post x0 result)
}

/// Makes it so that a polynomial can be evaluated
class t_Eval (v_Self: Type0) (v_T: Type0) = {
  f_eval_pre:v_Self -> t_Scalar -> Type0;
  f_eval_post:v_Self -> t_Scalar -> v_T -> Type0;
  f_eval:x0: v_Self -> x1: t_Scalar
    -> Prims.Pure v_T (f_eval_pre x0 x1) (fun result -> f_eval_post x0 x1 result)
}

let new_zero_slice (v_T: usize) (_: Prims.unit) : t_Array t_Scalar v_T =
  Rust_primitives.Hax.repeat impl__ZERO v_T

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl (v_T: usize) : t_AddSub (t_Array t_Scalar v_T) v_T =
  {
    f_add_vec_pre = (fun (self: t_Array t_Scalar v_T) (rhs: t_Array t_Scalar v_T) -> true);
    f_add_vec_post
    =
    (fun (self: t_Array t_Scalar v_T) (rhs: t_Array t_Scalar v_T) (out: t_Array t_Scalar v_T) ->
        true);
    f_add_vec
    =
    (fun (self: t_Array t_Scalar v_T) (rhs: t_Array t_Scalar v_T) ->
        let res:t_Array t_Scalar v_T = new_zero_slice v_T () in
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
                      (self.[ i ] <: t_Scalar)
                      (rhs.[ i ] <: t_Scalar)
                    <:
                    t_Scalar)
                <:
                t_Array t_Scalar v_T)
        in
        res);
    f_sub_vec_pre = (fun (self: t_Array t_Scalar v_T) (rhs: t_Array t_Scalar v_T) -> true);
    f_sub_vec_post
    =
    (fun (self: t_Array t_Scalar v_T) (rhs: t_Array t_Scalar v_T) (out: t_Array t_Scalar v_T) ->
        true);
    f_sub_vec
    =
    fun (self: t_Array t_Scalar v_T) (rhs: t_Array t_Scalar v_T) ->
      let res:t_Array t_Scalar v_T = new_zero_slice v_T () in
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
                (Core.Ops.Arith.f_sub #t_Scalar
                    #t_Scalar
                    #FStar.Tactics.Typeclasses.solve
                    (self.[ i ] <: t_Scalar)
                    (rhs.[ i ] <: t_Scalar)
                  <:
                  t_Scalar)
              <:
              t_Array t_Scalar v_T)
      in
      res
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_1__from__linalg (v_T: usize) : t_Scalable (t_Array t_Scalar v_T) =
  {
    f_mul_vec_scalar_pre = (fun (self: t_Array t_Scalar v_T) (rhs: t_Scalar) -> true);
    f_mul_vec_scalar_post
    =
    (fun (self: t_Array t_Scalar v_T) (rhs: t_Scalar) (out: t_Array t_Scalar v_T) -> true);
    f_mul_vec_scalar
    =
    fun (self: t_Array t_Scalar v_T) (rhs: t_Scalar) ->
      let res:t_Array t_Scalar v_T = new_zero_slice v_T () in
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
                (Core.Ops.Arith.f_mul #t_Scalar
                    #t_Scalar
                    #FStar.Tactics.Typeclasses.solve
                    (self.[ i ] <: t_Scalar)
                    rhs
                  <:
                  t_Scalar)
              <:
              t_Array t_Scalar v_T)
      in
      res
  }

/// Hadamard product of two vectors of scalars
let hadamard_vec (v_T: usize) (a b: t_Array t_Scalar v_T) : t_Array t_Scalar v_T =
  let res:t_Array t_Scalar v_T = new_zero_slice v_T () in
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
            (Core.Ops.Arith.f_mul #t_Scalar
                #t_Scalar
                #FStar.Tactics.Typeclasses.solve
                (Core.Clone.f_clone #t_Scalar #FStar.Tactics.Typeclasses.solve (a.[ i ] <: t_Scalar)
                  <:
                  t_Scalar)
                (Core.Clone.f_clone #t_Scalar #FStar.Tactics.Typeclasses.solve (b.[ i ] <: t_Scalar)
                  <:
                  t_Scalar)
              <:
              t_Scalar)
          <:
          t_Array t_Scalar v_T)
  in
  res

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_2__from__linalg (v_T: usize) : t_EqLen (t_Array t_Scalar v_T) v_T =
  {
    f_hadamard_pre = (fun (self: t_Array t_Scalar v_T) (rhs: t_Array t_Scalar v_T) -> true);
    f_hadamard_post
    =
    (fun (self: t_Array t_Scalar v_T) (rhs: t_Array t_Scalar v_T) (out: t_Array t_Scalar v_T) ->
        true);
    f_hadamard
    =
    fun (self: t_Array t_Scalar v_T) (rhs: t_Array t_Scalar v_T) -> hadamard_vec v_T self rhs
  }

let impl_5__len (self: t_Polynomium t_Scalar) : usize =
  Alloc.Vec.impl_1__len #t_Scalar #Alloc.Alloc.t_Global self.f_coeffs

/// In order to have all inputs give a valid group element we make it zero if
/// the given vector is empty.
let impl_5__new_from_scalar (v: Alloc.Vec.t_Vec t_Scalar Alloc.Alloc.t_Global)
    : t_Polynomium t_Scalar =
  {
    f_coeffs
    =
    if Alloc.Vec.impl_1__is_empty #t_Scalar #Alloc.Alloc.t_Global v
    then
      Alloc.Slice.impl__into_vec #t_Scalar
        #Alloc.Alloc.t_Global
        (Rust_primitives.unsize (Rust_primitives.Hax.box_new (let list =
                    [impl__from (mk_u128 0) <: t_Scalar]
                  in
                  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                  Rust_primitives.Hax.array_of_list 1 list)
              <:
              Alloc.Boxed.t_Box (t_Array t_Scalar (mk_usize 1)) Alloc.Alloc.t_Global)
          <:
          Alloc.Boxed.t_Box (t_Slice t_Scalar) Alloc.Alloc.t_Global)
    else
      Alloc.Slice.impl__to_vec #t_Scalar
        (Core.Ops.Deref.f_deref #(Alloc.Vec.t_Vec t_Scalar Alloc.Alloc.t_Global)
            #FStar.Tactics.Typeclasses.solve
            v
          <:
          t_Slice t_Scalar)
  }
  <:
  t_Polynomium t_Scalar

let impl_8__len (v_T: usize) (self: t_Polynomium (t_Array t_Scalar v_T)) : usize =
  Alloc.Vec.impl_1__len #(t_Array t_Scalar v_T) #Alloc.Alloc.t_Global self.f_coeffs

/// In order to have all inputs give a valid group element we make it zero if
/// the given vector is empty.
let impl_8__new_from_vec
      (v_T: usize)
      (v: Alloc.Vec.t_Vec (t_Array t_Scalar v_T) Alloc.Alloc.t_Global)
    : t_Polynomium (t_Array t_Scalar v_T) =
  {
    f_coeffs
    =
    if Alloc.Vec.impl_1__is_empty #(t_Array t_Scalar v_T) #Alloc.Alloc.t_Global v
    then
      Alloc.Slice.impl__into_vec #(t_Array t_Scalar v_T)
        #Alloc.Alloc.t_Global
        (Rust_primitives.unsize (Rust_primitives.Hax.box_new (let list =
                    [new_zero_slice v_T () <: t_Array t_Scalar v_T]
                  in
                  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                  Rust_primitives.Hax.array_of_list 1 list)
              <:
              Alloc.Boxed.t_Box (t_Array (t_Array t_Scalar v_T) (mk_usize 1)) Alloc.Alloc.t_Global)
          <:
          Alloc.Boxed.t_Box (t_Slice (t_Array t_Scalar v_T)) Alloc.Alloc.t_Global)
    else v
  }
  <:
  t_Polynomium (t_Array t_Scalar v_T)

let trim (v: Alloc.Vec.t_Vec t_Scalar Alloc.Alloc.t_Global)
    : Alloc.Vec.t_Vec t_Scalar Alloc.Alloc.t_Global =
  let filtered_rev:Core.Iter.Adapters.Rev.t_Rev (Core.Slice.Iter.t_Iter t_Scalar) =
    Core.Iter.Traits.Iterator.f_rev #(Core.Slice.Iter.t_Iter t_Scalar)
      #FStar.Tactics.Typeclasses.solve
      (Core.Slice.impl__iter #t_Scalar
          (Core.Ops.Deref.f_deref #(Alloc.Vec.t_Vec t_Scalar Alloc.Alloc.t_Global)
              #FStar.Tactics.Typeclasses.solve
              v
            <:
            t_Slice t_Scalar)
        <:
        Core.Slice.Iter.t_Iter t_Scalar)
  in
  let res:Alloc.Vec.t_Vec t_Scalar Alloc.Alloc.t_Global = Alloc.Vec.impl__new #t_Scalar () in
  let is_trailing:bool = true in
  let is_trailing, res:(bool & Alloc.Vec.t_Vec t_Scalar Alloc.Alloc.t_Global) =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter #(Core.Iter.Adapters.Rev.t_Rev
            (Core.Slice.Iter.t_Iter t_Scalar))
          #FStar.Tactics.Typeclasses.solve
          filtered_rev
        <:
        Core.Iter.Adapters.Rev.t_Rev (Core.Slice.Iter.t_Iter t_Scalar))
      (is_trailing, res <: (bool & Alloc.Vec.t_Vec t_Scalar Alloc.Alloc.t_Global))
      (fun temp_0_ e ->
          let is_trailing, res:(bool & Alloc.Vec.t_Vec t_Scalar Alloc.Alloc.t_Global) = temp_0_ in
          let e:t_Scalar = e in
          let is_trailing:bool = is_trailing && e =. impl__ZERO in
          if ~.is_trailing
          then
            let res:Alloc.Vec.t_Vec t_Scalar Alloc.Alloc.t_Global =
              Alloc.Vec.impl_1__push #t_Scalar
                #Alloc.Alloc.t_Global
                res
                (Core.Clone.f_clone #t_Scalar #FStar.Tactics.Typeclasses.solve e <: t_Scalar)
            in
            is_trailing, res <: (bool & Alloc.Vec.t_Vec t_Scalar Alloc.Alloc.t_Global)
          else is_trailing, res <: (bool & Alloc.Vec.t_Vec t_Scalar Alloc.Alloc.t_Global))
  in
  Core.Iter.Traits.Iterator.f_collect #(Core.Iter.Adapters.Map.t_Map
        (Core.Iter.Adapters.Rev.t_Rev (Core.Slice.Iter.t_Iter t_Scalar)) (t_Scalar -> t_Scalar))
    #FStar.Tactics.Typeclasses.solve
    #(Alloc.Vec.t_Vec t_Scalar Alloc.Alloc.t_Global)
    (Core.Iter.Traits.Iterator.f_map #(Core.Iter.Adapters.Rev.t_Rev
          (Core.Slice.Iter.t_Iter t_Scalar))
        #FStar.Tactics.Typeclasses.solve
        #t_Scalar
        (Core.Iter.Traits.Iterator.f_rev #(Core.Slice.Iter.t_Iter t_Scalar)
            #FStar.Tactics.Typeclasses.solve
            (Core.Slice.impl__iter #t_Scalar
                (Core.Ops.Deref.f_deref #(Alloc.Vec.t_Vec t_Scalar Alloc.Alloc.t_Global)
                    #FStar.Tactics.Typeclasses.solve
                    res
                  <:
                  t_Slice t_Scalar)
              <:
              Core.Slice.Iter.t_Iter t_Scalar)
          <:
          Core.Iter.Adapters.Rev.t_Rev (Core.Slice.Iter.t_Iter t_Scalar))
        (fun e ->
            let e:t_Scalar = e in
            Core.Clone.f_clone #t_Scalar #FStar.Tactics.Typeclasses.solve e <: t_Scalar)
      <:
      Core.Iter.Adapters.Map.t_Map (Core.Iter.Adapters.Rev.t_Rev (Core.Slice.Iter.t_Iter t_Scalar))
        (t_Scalar -> t_Scalar))

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_6__from__polynomium: t_Trim (t_Polynomium t_Scalar) (t_Polynomium t_Scalar) =
  {
    f_trim_pre = (fun (self: t_Polynomium t_Scalar) -> true);
    f_trim_post = (fun (self: t_Polynomium t_Scalar) (out: t_Polynomium t_Scalar) -> true);
    f_trim
    =
    fun (self: t_Polynomium t_Scalar) ->
      let res:Alloc.Vec.t_Vec t_Scalar Alloc.Alloc.t_Global = trim self.f_coeffs in
      {
        f_coeffs
        =
        if Alloc.Vec.impl_1__is_empty #t_Scalar #Alloc.Alloc.t_Global res
        then
          Alloc.Slice.impl__into_vec #t_Scalar
            #Alloc.Alloc.t_Global
            (Rust_primitives.unsize (Rust_primitives.Hax.box_new (let list = [impl__ZERO] in
                      FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                      Rust_primitives.Hax.array_of_list 1 list)
                  <:
                  Alloc.Boxed.t_Box (t_Array t_Scalar (mk_usize 1)) Alloc.Alloc.t_Global)
              <:
              Alloc.Boxed.t_Box (t_Slice t_Scalar) Alloc.Alloc.t_Global)
        else res
      }
      <:
      t_Polynomium t_Scalar
  }

let trim_vec (v_T: usize) (v: Alloc.Vec.t_Vec (t_Array t_Scalar v_T) Alloc.Alloc.t_Global)
    : Alloc.Vec.t_Vec (t_Array t_Scalar v_T) Alloc.Alloc.t_Global =
  let filtered_rev:Core.Iter.Adapters.Rev.t_Rev (Core.Slice.Iter.t_Iter (t_Array t_Scalar v_T)) =
    Core.Iter.Traits.Iterator.f_rev #(Core.Slice.Iter.t_Iter (t_Array t_Scalar v_T))
      #FStar.Tactics.Typeclasses.solve
      (Core.Slice.impl__iter #(t_Array t_Scalar v_T)
          (Core.Ops.Deref.f_deref #(Alloc.Vec.t_Vec (t_Array t_Scalar v_T) Alloc.Alloc.t_Global)
              #FStar.Tactics.Typeclasses.solve
              v
            <:
            t_Slice (t_Array t_Scalar v_T))
        <:
        Core.Slice.Iter.t_Iter (t_Array t_Scalar v_T))
  in
  let res:Alloc.Vec.t_Vec (t_Array t_Scalar v_T) Alloc.Alloc.t_Global =
    Alloc.Vec.impl__new #(t_Array t_Scalar v_T) ()
  in
  let is_trailing:bool = true in
  let is_trailing, res:(bool & Alloc.Vec.t_Vec (t_Array t_Scalar v_T) Alloc.Alloc.t_Global) =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter #(Core.Iter.Adapters.Rev.t_Rev
            (Core.Slice.Iter.t_Iter (t_Array t_Scalar v_T)))
          #FStar.Tactics.Typeclasses.solve
          filtered_rev
        <:
        Core.Iter.Adapters.Rev.t_Rev (Core.Slice.Iter.t_Iter (t_Array t_Scalar v_T)))
      (is_trailing, res <: (bool & Alloc.Vec.t_Vec (t_Array t_Scalar v_T) Alloc.Alloc.t_Global))
      (fun temp_0_ e ->
          let is_trailing, res:(bool & Alloc.Vec.t_Vec (t_Array t_Scalar v_T) Alloc.Alloc.t_Global)
          =
            temp_0_
          in
          let e:t_Array t_Scalar v_T = e in
          let _, out:(Core.Slice.Iter.t_Iter t_Scalar & bool) =
            Core.Iter.Traits.Iterator.f_all #(Core.Slice.Iter.t_Iter t_Scalar)
              #FStar.Tactics.Typeclasses.solve
              (Core.Slice.impl__iter #t_Scalar (e <: t_Slice t_Scalar)
                <:
                Core.Slice.Iter.t_Iter t_Scalar)
              (fun e ->
                  let e:t_Scalar = e in
                  e =. impl__ZERO <: bool)
          in
          let is_trailing:bool = is_trailing && out in
          if ~.is_trailing
          then
            let res:Alloc.Vec.t_Vec (t_Array t_Scalar v_T) Alloc.Alloc.t_Global =
              Alloc.Vec.impl_1__push #(t_Array t_Scalar v_T)
                #Alloc.Alloc.t_Global
                res
                (Core.Clone.f_clone #(t_Array t_Scalar v_T) #FStar.Tactics.Typeclasses.solve e
                  <:
                  t_Array t_Scalar v_T)
            in
            is_trailing, res <: (bool & Alloc.Vec.t_Vec (t_Array t_Scalar v_T) Alloc.Alloc.t_Global)
          else
            is_trailing, res <: (bool & Alloc.Vec.t_Vec (t_Array t_Scalar v_T) Alloc.Alloc.t_Global)
      )
  in
  Core.Iter.Traits.Iterator.f_collect #(Core.Iter.Adapters.Map.t_Map
        (Core.Iter.Adapters.Rev.t_Rev (Core.Slice.Iter.t_Iter (t_Array t_Scalar v_T)))
        (t_Array t_Scalar v_T -> t_Array t_Scalar v_T))
    #FStar.Tactics.Typeclasses.solve
    #(Alloc.Vec.t_Vec (t_Array t_Scalar v_T) Alloc.Alloc.t_Global)
    (Core.Iter.Traits.Iterator.f_map #(Core.Iter.Adapters.Rev.t_Rev
          (Core.Slice.Iter.t_Iter (t_Array t_Scalar v_T)))
        #FStar.Tactics.Typeclasses.solve
        #(t_Array t_Scalar v_T)
        (Core.Iter.Traits.Iterator.f_rev #(Core.Slice.Iter.t_Iter (t_Array t_Scalar v_T))
            #FStar.Tactics.Typeclasses.solve
            (Core.Slice.impl__iter #(t_Array t_Scalar v_T)
                (Core.Ops.Deref.f_deref #(Alloc.Vec.t_Vec (t_Array t_Scalar v_T)
                        Alloc.Alloc.t_Global)
                    #FStar.Tactics.Typeclasses.solve
                    res
                  <:
                  t_Slice (t_Array t_Scalar v_T))
              <:
              Core.Slice.Iter.t_Iter (t_Array t_Scalar v_T))
          <:
          Core.Iter.Adapters.Rev.t_Rev (Core.Slice.Iter.t_Iter (t_Array t_Scalar v_T)))
        (fun e ->
            let e:t_Array t_Scalar v_T = e in
            Core.Clone.f_clone #(t_Array t_Scalar v_T) #FStar.Tactics.Typeclasses.solve e
            <:
            t_Array t_Scalar v_T)
      <:
      Core.Iter.Adapters.Map.t_Map
        (Core.Iter.Adapters.Rev.t_Rev (Core.Slice.Iter.t_Iter (t_Array t_Scalar v_T)))
        (t_Array t_Scalar v_T -> t_Array t_Scalar v_T))

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_9__from__polynomium (v_T: usize)
    : t_Trim (t_Polynomium (t_Array t_Scalar v_T)) (t_Polynomium (t_Array t_Scalar v_T)) =
  {
    f_trim_pre = (fun (self: t_Polynomium (t_Array t_Scalar v_T)) -> true);
    f_trim_post
    =
    (fun (self: t_Polynomium (t_Array t_Scalar v_T)) (out: t_Polynomium (t_Array t_Scalar v_T)) ->
        true);
    f_trim
    =
    fun (self: t_Polynomium (t_Array t_Scalar v_T)) ->
      let res:Alloc.Vec.t_Vec (t_Array t_Scalar v_T) Alloc.Alloc.t_Global =
        trim_vec v_T self.f_coeffs
      in
      {
        f_coeffs
        =
        if Alloc.Vec.impl_1__is_empty #(t_Array t_Scalar v_T) #Alloc.Alloc.t_Global res
        then
          Alloc.Slice.impl__into_vec #(t_Array t_Scalar v_T)
            #Alloc.Alloc.t_Global
            (Rust_primitives.unsize (Rust_primitives.Hax.box_new (let list =
                        [new_zero_slice v_T () <: t_Array t_Scalar v_T]
                      in
                      FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                      Rust_primitives.Hax.array_of_list 1 list)
                  <:
                  Alloc.Boxed.t_Box (t_Array (t_Array t_Scalar v_T) (mk_usize 1))
                    Alloc.Alloc.t_Global)
              <:
              Alloc.Boxed.t_Box (t_Slice (t_Array t_Scalar v_T)) Alloc.Alloc.t_Global)
        else res
      }
      <:
      t_Polynomium (t_Array t_Scalar v_T)
  }

/// Evaluates the polynomial given by a[0] + a[1]u + a[2]u^2 ...
let evaluate_polynomial (a: Alloc.Vec.t_Vec t_Scalar Alloc.Alloc.t_Global) (u: t_Scalar) : t_Scalar =
  let result:t_Scalar = impl__ZERO in
  let result:t_Scalar =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter #(Core.Iter.Adapters.Rev.t_Rev
            (Core.Slice.Iter.t_Iter t_Scalar))
          #FStar.Tactics.Typeclasses.solve
          (Core.Iter.Traits.Iterator.f_rev #(Core.Slice.Iter.t_Iter t_Scalar)
              #FStar.Tactics.Typeclasses.solve
              (Core.Slice.impl__iter #t_Scalar
                  (Core.Ops.Deref.f_deref #(Alloc.Vec.t_Vec t_Scalar Alloc.Alloc.t_Global)
                      #FStar.Tactics.Typeclasses.solve
                      a
                    <:
                    t_Slice t_Scalar)
                <:
                Core.Slice.Iter.t_Iter t_Scalar)
            <:
            Core.Iter.Adapters.Rev.t_Rev (Core.Slice.Iter.t_Iter t_Scalar))
        <:
        Core.Iter.Adapters.Rev.t_Rev (Core.Slice.Iter.t_Iter t_Scalar))
      result
      (fun result coef ->
          let result:t_Scalar = result in
          let coef:t_Scalar = coef in
          Core.Ops.Arith.f_add #t_Scalar
            #t_Scalar
            #FStar.Tactics.Typeclasses.solve
            (Core.Ops.Arith.f_mul #t_Scalar #t_Scalar #FStar.Tactics.Typeclasses.solve u result
              <:
              t_Scalar)
            coef
          <:
          t_Scalar)
  in
  result

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_7__from__polynomium: t_Eval (t_Polynomium t_Scalar) t_Scalar =
  {
    f_eval_pre = (fun (self: t_Polynomium t_Scalar) (x: t_Scalar) -> true);
    f_eval_post = (fun (self: t_Polynomium t_Scalar) (x: t_Scalar) (out: t_Scalar) -> true);
    f_eval
    =
    fun (self: t_Polynomium t_Scalar) (x: t_Scalar) ->
      evaluate_polynomial (Core.Clone.f_clone #(Alloc.Vec.t_Vec t_Scalar Alloc.Alloc.t_Global)
            #FStar.Tactics.Typeclasses.solve
            self.f_coeffs
          <:
          Alloc.Vec.t_Vec t_Scalar Alloc.Alloc.t_Global)
        x
  }

let evaluate_vector_polynomial
      (v_T: usize)
      (a: Alloc.Vec.t_Vec (t_Array t_Scalar v_T) Alloc.Alloc.t_Global)
      (u: t_Scalar)
    : t_Array t_Scalar v_T =
  if Alloc.Vec.impl_1__is_empty #(t_Array t_Scalar v_T) #Alloc.Alloc.t_Global a
  then new_zero_slice v_T ()
  else
    let result:t_Array t_Scalar v_T = new_zero_slice v_T () in
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter #(Core.Iter.Adapters.Rev.t_Rev
            (Core.Slice.Iter.t_Iter (t_Array t_Scalar v_T)))
          #FStar.Tactics.Typeclasses.solve
          (Core.Iter.Traits.Iterator.f_rev #(Core.Slice.Iter.t_Iter (t_Array t_Scalar v_T))
              #FStar.Tactics.Typeclasses.solve
              (Core.Slice.impl__iter #(t_Array t_Scalar v_T)
                  (Core.Ops.Deref.f_deref #(Alloc.Vec.t_Vec (t_Array t_Scalar v_T)
                          Alloc.Alloc.t_Global)
                      #FStar.Tactics.Typeclasses.solve
                      a
                    <:
                    t_Slice (t_Array t_Scalar v_T))
                <:
                Core.Slice.Iter.t_Iter (t_Array t_Scalar v_T))
            <:
            Core.Iter.Adapters.Rev.t_Rev (Core.Slice.Iter.t_Iter (t_Array t_Scalar v_T)))
        <:
        Core.Iter.Adapters.Rev.t_Rev (Core.Slice.Iter.t_Iter (t_Array t_Scalar v_T)))
      result
      (fun result coef ->
          let result:t_Array t_Scalar v_T = result in
          let coef:t_Array t_Scalar v_T = coef in
          f_add_vec #(t_Array t_Scalar v_T)
            #v_T
            #FStar.Tactics.Typeclasses.solve
            (f_mul_vec_scalar #(t_Array t_Scalar v_T) #FStar.Tactics.Typeclasses.solve result u
              <:
              t_Array t_Scalar v_T)
            coef
          <:
          t_Array t_Scalar v_T)

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_10 (v_T: usize) : t_Eval (t_Polynomium (t_Array t_Scalar v_T)) (t_Array t_Scalar v_T) =
  {
    f_eval_pre = (fun (self: t_Polynomium (t_Array t_Scalar v_T)) (x: t_Scalar) -> true);
    f_eval_post
    =
    (fun (self: t_Polynomium (t_Array t_Scalar v_T)) (x: t_Scalar) (out: t_Array t_Scalar v_T) ->
        true);
    f_eval
    =
    fun (self: t_Polynomium (t_Array t_Scalar v_T)) (x: t_Scalar) ->
      evaluate_vector_polynomial v_T
        (Core.Clone.f_clone #(Alloc.Vec.t_Vec (t_Array t_Scalar v_T) Alloc.Alloc.t_Global)
            #FStar.Tactics.Typeclasses.solve
            self.f_coeffs
          <:
          Alloc.Vec.t_Vec (t_Array t_Scalar v_T) Alloc.Alloc.t_Global)
        x
  }

/// Returns [1, 2, 3] x [1, 2, 3] => 1 * 3 + 2 * 2 + 3 * 1
let cross_product (l r: Alloc.Vec.t_Vec t_Scalar Alloc.Alloc.t_Global) : t_Scalar =
  Core.Iter.Traits.Iterator.f_fold #(Core.Iter.Adapters.Zip.t_Zip
        (Core.Iter.Adapters.Rev.t_Rev (Core.Slice.Iter.t_Iter t_Scalar))
        (Core.Slice.Iter.t_Iter t_Scalar))
    #FStar.Tactics.Typeclasses.solve
    #t_Scalar
    (Core.Iter.Traits.Iterator.f_zip #(Core.Iter.Adapters.Rev.t_Rev
          (Core.Slice.Iter.t_Iter t_Scalar))
        #FStar.Tactics.Typeclasses.solve
        #(Core.Slice.Iter.t_Iter t_Scalar)
        (Core.Iter.Traits.Iterator.f_rev #(Core.Slice.Iter.t_Iter t_Scalar)
            #FStar.Tactics.Typeclasses.solve
            (Core.Slice.impl__iter #t_Scalar
                (Core.Ops.Deref.f_deref #(Alloc.Vec.t_Vec t_Scalar Alloc.Alloc.t_Global)
                    #FStar.Tactics.Typeclasses.solve
                    l
                  <:
                  t_Slice t_Scalar)
              <:
              Core.Slice.Iter.t_Iter t_Scalar)
          <:
          Core.Iter.Adapters.Rev.t_Rev (Core.Slice.Iter.t_Iter t_Scalar))
        (Core.Slice.impl__iter #t_Scalar
            (Core.Ops.Deref.f_deref #(Alloc.Vec.t_Vec t_Scalar Alloc.Alloc.t_Global)
                #FStar.Tactics.Typeclasses.solve
                r
              <:
              t_Slice t_Scalar)
          <:
          Core.Slice.Iter.t_Iter t_Scalar)
      <:
      Core.Iter.Adapters.Zip.t_Zip (Core.Iter.Adapters.Rev.t_Rev (Core.Slice.Iter.t_Iter t_Scalar))
        (Core.Slice.Iter.t_Iter t_Scalar))
    impl__ZERO
    (fun acc temp_1_ ->
        let acc:t_Scalar = acc in
        let a, b:(t_Scalar & t_Scalar) = temp_1_ in
        Core.Ops.Arith.f_add #t_Scalar
          #t_Scalar
          #FStar.Tactics.Typeclasses.solve
          acc
          (Core.Ops.Arith.f_mul #t_Scalar #t_Scalar #FStar.Tactics.Typeclasses.solve a b <: t_Scalar
          )
        <:
        t_Scalar)

/// The Johnnyboi algorithm for multiplying polynomials. FORMALLY VERIFIED
let jonamul (lhs rhs: t_Polynomium t_Scalar) : t_Polynomium t_Scalar =
  let min_len:usize =
    Bachelor_formally_verified_stuff.Convert.min #usize
      (impl_5__len lhs <: usize)
      (impl_5__len rhs <: usize)
  in
  let max_len:usize =
    Bachelor_formally_verified_stuff.Convert.max #usize
      (impl_5__len lhs <: usize)
      (impl_5__len rhs <: usize)
  in
  let max_ptr:usize = mk_usize 0 in
  let lower_bound:usize = mk_usize 0 in
  let coeffs:Alloc.Vec.t_Vec t_Scalar Alloc.Alloc.t_Global = Alloc.Vec.impl__new #t_Scalar () in
  let coeffs, max_ptr:(Alloc.Vec.t_Vec t_Scalar Alloc.Alloc.t_Global & usize) =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 1)
      min_len
      (fun temp_0_ temp_1_ ->
          let coeffs, max_ptr:(Alloc.Vec.t_Vec t_Scalar Alloc.Alloc.t_Global & usize) = temp_0_ in
          let _:usize = temp_1_ in
          true)
      (coeffs, max_ptr <: (Alloc.Vec.t_Vec t_Scalar Alloc.Alloc.t_Global & usize))
      (fun temp_0_ i ->
          let coeffs, max_ptr:(Alloc.Vec.t_Vec t_Scalar Alloc.Alloc.t_Global & usize) = temp_0_ in
          let i:usize = i in
          let res:t_Scalar =
            cross_product (Alloc.Slice.impl__to_vec #t_Scalar
                  (lhs.f_coeffs.[ { Core.Ops.Range.f_end = i } <: Core.Ops.Range.t_RangeTo usize ]
                    <:
                    t_Slice t_Scalar)
                <:
                Alloc.Vec.t_Vec t_Scalar Alloc.Alloc.t_Global)
              (Alloc.Slice.impl__to_vec #t_Scalar
                  (rhs.f_coeffs.[ { Core.Ops.Range.f_end = i } <: Core.Ops.Range.t_RangeTo usize ]
                    <:
                    t_Slice t_Scalar)
                <:
                Alloc.Vec.t_Vec t_Scalar Alloc.Alloc.t_Global)
          in
          let coeffs:Alloc.Vec.t_Vec t_Scalar Alloc.Alloc.t_Global =
            Alloc.Vec.impl_1__push #t_Scalar #Alloc.Alloc.t_Global coeffs res
          in
          let max_ptr:usize = i in
          coeffs, max_ptr <: (Alloc.Vec.t_Vec t_Scalar Alloc.Alloc.t_Global & usize))
  in
  let largest:t_Polynomium t_Scalar =
    if (impl_5__len rhs <: usize) >. (impl_5__len lhs <: usize) then rhs else lhs
  in
  let smallest:t_Polynomium t_Scalar =
    if (impl_5__len lhs <: usize) <. (impl_5__len rhs <: usize) then lhs else rhs
  in
  let last_in_min:t_Scalar = impl__ZERO in
  let remainder:Alloc.Vec.t_Vec t_Scalar Alloc.Alloc.t_Global = Alloc.Vec.impl__new #t_Scalar () in
  let curr_win:Core.Ops.Range.t_Range usize =
    {
      Core.Ops.Range.f_start = lower_bound;
      Core.Ops.Range.f_end
      =
      cast (Bachelor_formally_verified_stuff.Convert.min #u128
            ((cast (lower_bound <: usize) <: u128) +! (cast (min_len <: usize) <: u128) <: u128)
            (cast (impl_5__len rhs <: usize) <: u128)
          <:
          u128)
      <:
      usize
    }
    <:
    Core.Ops.Range.t_Range usize
  in
  let coeffs, curr_win, lower_bound, remainder:(Alloc.Vec.t_Vec t_Scalar Alloc.Alloc.t_Global &
    Core.Ops.Range.t_Range usize &
    usize &
    Alloc.Vec.t_Vec t_Scalar Alloc.Alloc.t_Global) =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      (Alloc.Vec.impl_1__len #t_Scalar #Alloc.Alloc.t_Global largest.f_coeffs <: usize)
      (fun temp_0_ temp_1_ ->
          let coeffs, curr_win, lower_bound, remainder:(Alloc.Vec.t_Vec t_Scalar
              Alloc.Alloc.t_Global &
            Core.Ops.Range.t_Range usize &
            usize &
            Alloc.Vec.t_Vec t_Scalar Alloc.Alloc.t_Global) =
            temp_0_
          in
          let _:usize = temp_1_ in
          true)
      (coeffs, curr_win, lower_bound, remainder
        <:
        (Alloc.Vec.t_Vec t_Scalar Alloc.Alloc.t_Global & Core.Ops.Range.t_Range usize & usize &
          Alloc.Vec.t_Vec t_Scalar Alloc.Alloc.t_Global))
      (fun temp_0_ i ->
          let coeffs, curr_win, lower_bound, remainder:(Alloc.Vec.t_Vec t_Scalar
              Alloc.Alloc.t_Global &
            Core.Ops.Range.t_Range usize &
            usize &
            Alloc.Vec.t_Vec t_Scalar Alloc.Alloc.t_Global) =
            temp_0_
          in
          let i:usize = i in
          let lower_bound:usize = i in
          let remainder:Alloc.Vec.t_Vec t_Scalar Alloc.Alloc.t_Global =
            Alloc.Slice.impl__to_vec #t_Scalar
              (largest.f_coeffs.[ { Core.Ops.Range.f_start = i } <: Core.Ops.Range.t_RangeFrom usize
                ]
                <:
                t_Slice t_Scalar)
          in
          let curr_win:Core.Ops.Range.t_Range usize =
            {
              Core.Ops.Range.f_start = i;
              Core.Ops.Range.f_end
              =
              Alloc.Vec.impl_1__len #t_Scalar #Alloc.Alloc.t_Global largest.f_coeffs
            }
            <:
            Core.Ops.Range.t_Range usize
          in
          let largest_slice:Alloc.Vec.t_Vec t_Scalar Alloc.Alloc.t_Global =
            Alloc.Slice.impl__to_vec #t_Scalar (largest.f_coeffs.[ curr_win ] <: t_Slice t_Scalar)
          in
          let smallest_slice:Alloc.Vec.t_Vec t_Scalar Alloc.Alloc.t_Global =
            Alloc.Slice.impl__to_vec #t_Scalar
              (smallest.f_coeffs.[ Core.Ops.Range.RangeFull <: Core.Ops.Range.t_RangeFull ]
                <:
                t_Slice t_Scalar)
          in
          let res:t_Scalar = cross_product smallest_slice largest_slice in
          let coeffs:Alloc.Vec.t_Vec t_Scalar Alloc.Alloc.t_Global =
            Alloc.Vec.impl_1__push #t_Scalar #Alloc.Alloc.t_Global coeffs res
          in
          coeffs, curr_win, lower_bound, remainder
          <:
          (Alloc.Vec.t_Vec t_Scalar Alloc.Alloc.t_Global & Core.Ops.Range.t_Range usize & usize &
            Alloc.Vec.t_Vec t_Scalar Alloc.Alloc.t_Global))
  in
  let last_in_min:t_Scalar =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter #(Alloc.Vec.t_Vec
              t_Scalar Alloc.Alloc.t_Global)
          #FStar.Tactics.Typeclasses.solve
          smallest.f_coeffs
        <:
        Core.Slice.Iter.t_Iter t_Scalar)
      last_in_min
      (fun last_in_min e ->
          let last_in_min:t_Scalar = last_in_min in
          e)
  in
  if min_len =. max_len
  then { f_coeffs = coeffs } <: t_Polynomium t_Scalar
  else
    let coeffs:Alloc.Vec.t_Vec t_Scalar Alloc.Alloc.t_Global =
      Rust_primitives.Hax.Folds.fold_range (mk_usize 1)
        (Alloc.Vec.impl_1__len #t_Scalar #Alloc.Alloc.t_Global remainder <: usize)
        (fun coeffs temp_1_ ->
            let coeffs:Alloc.Vec.t_Vec t_Scalar Alloc.Alloc.t_Global = coeffs in
            let _:usize = temp_1_ in
            true)
        coeffs
        (fun coeffs i ->
            let coeffs:Alloc.Vec.t_Vec t_Scalar Alloc.Alloc.t_Global = coeffs in
            let i:usize = i in
            let res:t_Scalar =
              Core.Ops.Arith.f_mul #t_Scalar
                #t_Scalar
                #FStar.Tactics.Typeclasses.solve
                last_in_min
                (remainder.[ i ] <: t_Scalar)
            in
            let coeffs:Alloc.Vec.t_Vec t_Scalar Alloc.Alloc.t_Global =
              Alloc.Vec.impl_1__push #t_Scalar #Alloc.Alloc.t_Global coeffs res
            in
            coeffs)
    in
    { f_coeffs = coeffs } <: t_Polynomium t_Scalar

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl__from__polynomium: Core.Ops.Arith.t_Mul (t_Polynomium t_Scalar) (t_Polynomium t_Scalar) =
  {
    f_Output = t_Polynomium t_Scalar;
    f_mul_pre = (fun (self: t_Polynomium t_Scalar) (rhs: t_Polynomium t_Scalar) -> true);
    f_mul_post
    =
    (fun (self: t_Polynomium t_Scalar) (rhs: t_Polynomium t_Scalar) (out: t_Polynomium t_Scalar) ->
        true);
    f_mul = fun (self: t_Polynomium t_Scalar) (rhs: t_Polynomium t_Scalar) -> jonamul self rhs
  }

/// Returns [1, 2, 3] x [1, 2, 3] => 1 * 3 + 2 * 2 + 3 * 1
let cross_product_vec
      (v_T: usize)
      (l r: Alloc.Vec.t_Vec (t_Array t_Scalar v_T) Alloc.Alloc.t_Global)
    : t_Scalar =
  Core.Iter.Traits.Iterator.f_fold #(Core.Iter.Adapters.Zip.t_Zip
        (Core.Iter.Adapters.Rev.t_Rev (Core.Slice.Iter.t_Iter (t_Array t_Scalar v_T)))
        (Core.Slice.Iter.t_Iter (t_Array t_Scalar v_T)))
    #FStar.Tactics.Typeclasses.solve
    #t_Scalar
    (Core.Iter.Traits.Iterator.f_zip #(Core.Iter.Adapters.Rev.t_Rev
          (Core.Slice.Iter.t_Iter (t_Array t_Scalar v_T)))
        #FStar.Tactics.Typeclasses.solve
        #(Core.Slice.Iter.t_Iter (t_Array t_Scalar v_T))
        (Core.Iter.Traits.Iterator.f_rev #(Core.Slice.Iter.t_Iter (t_Array t_Scalar v_T))
            #FStar.Tactics.Typeclasses.solve
            (Core.Slice.impl__iter #(t_Array t_Scalar v_T)
                (Core.Ops.Deref.f_deref #(Alloc.Vec.t_Vec (t_Array t_Scalar v_T)
                        Alloc.Alloc.t_Global)
                    #FStar.Tactics.Typeclasses.solve
                    l
                  <:
                  t_Slice (t_Array t_Scalar v_T))
              <:
              Core.Slice.Iter.t_Iter (t_Array t_Scalar v_T))
          <:
          Core.Iter.Adapters.Rev.t_Rev (Core.Slice.Iter.t_Iter (t_Array t_Scalar v_T)))
        (Core.Slice.impl__iter #(t_Array t_Scalar v_T)
            (Core.Ops.Deref.f_deref #(Alloc.Vec.t_Vec (t_Array t_Scalar v_T) Alloc.Alloc.t_Global)
                #FStar.Tactics.Typeclasses.solve
                r
              <:
              t_Slice (t_Array t_Scalar v_T))
          <:
          Core.Slice.Iter.t_Iter (t_Array t_Scalar v_T))
      <:
      Core.Iter.Adapters.Zip.t_Zip
        (Core.Iter.Adapters.Rev.t_Rev (Core.Slice.Iter.t_Iter (t_Array t_Scalar v_T)))
        (Core.Slice.Iter.t_Iter (t_Array t_Scalar v_T)))
    impl__ZERO
    (fun acc temp_1_ ->
        let acc:t_Scalar = acc in
        let a, b:(t_Array t_Scalar v_T & t_Array t_Scalar v_T) = temp_1_ in
        Core.Ops.Arith.f_add #t_Scalar
          #t_Scalar
          #FStar.Tactics.Typeclasses.solve
          acc
          (inner_prod_scalars v_T a b <: t_Scalar)
        <:
        t_Scalar)

/// The Johnnyboi algorithm for multiplying polynomials. FORMALLY VERIFIED
let jonamul_vec (v_T: usize) (lhs rhs: t_Polynomium (t_Array t_Scalar v_T)) : t_Polynomium t_Scalar =
  let min_len:usize =
    Bachelor_formally_verified_stuff.Convert.min #usize
      (impl_8__len v_T lhs <: usize)
      (impl_8__len v_T rhs <: usize)
  in
  let max_len:usize =
    Bachelor_formally_verified_stuff.Convert.max #usize
      (impl_8__len v_T lhs <: usize)
      (impl_8__len v_T rhs <: usize)
  in
  let max_ptr:usize = mk_usize 0 in
  let lower_bound:usize = mk_usize 0 in
  let coeffs:Alloc.Vec.t_Vec t_Scalar Alloc.Alloc.t_Global = Alloc.Vec.impl__new #t_Scalar () in
  let coeffs, max_ptr:(Alloc.Vec.t_Vec t_Scalar Alloc.Alloc.t_Global & usize) =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 1)
      min_len
      (fun temp_0_ temp_1_ ->
          let coeffs, max_ptr:(Alloc.Vec.t_Vec t_Scalar Alloc.Alloc.t_Global & usize) = temp_0_ in
          let _:usize = temp_1_ in
          true)
      (coeffs, max_ptr <: (Alloc.Vec.t_Vec t_Scalar Alloc.Alloc.t_Global & usize))
      (fun temp_0_ i ->
          let coeffs, max_ptr:(Alloc.Vec.t_Vec t_Scalar Alloc.Alloc.t_Global & usize) = temp_0_ in
          let i:usize = i in
          let res:t_Scalar =
            cross_product_vec v_T
              (Alloc.Slice.impl__to_vec #(t_Array t_Scalar v_T)
                  (lhs.f_coeffs.[ { Core.Ops.Range.f_end = i } <: Core.Ops.Range.t_RangeTo usize ]
                    <:
                    t_Slice (t_Array t_Scalar v_T))
                <:
                Alloc.Vec.t_Vec (t_Array t_Scalar v_T) Alloc.Alloc.t_Global)
              (Alloc.Slice.impl__to_vec #(t_Array t_Scalar v_T)
                  (rhs.f_coeffs.[ { Core.Ops.Range.f_end = i } <: Core.Ops.Range.t_RangeTo usize ]
                    <:
                    t_Slice (t_Array t_Scalar v_T))
                <:
                Alloc.Vec.t_Vec (t_Array t_Scalar v_T) Alloc.Alloc.t_Global)
          in
          let coeffs:Alloc.Vec.t_Vec t_Scalar Alloc.Alloc.t_Global =
            Alloc.Vec.impl_1__push #t_Scalar #Alloc.Alloc.t_Global coeffs res
          in
          let max_ptr:usize = i in
          coeffs, max_ptr <: (Alloc.Vec.t_Vec t_Scalar Alloc.Alloc.t_Global & usize))
  in
  let largest:t_Polynomium (t_Array t_Scalar v_T) =
    if (impl_8__len v_T rhs <: usize) >. (impl_8__len v_T lhs <: usize) then rhs else lhs
  in
  let smallest:t_Polynomium (t_Array t_Scalar v_T) =
    if (impl_8__len v_T lhs <: usize) <. (impl_8__len v_T rhs <: usize) then lhs else rhs
  in
  let last_in_min:t_Array t_Scalar v_T = new_zero_slice v_T () in
  let remainder:Alloc.Vec.t_Vec (t_Array t_Scalar v_T) Alloc.Alloc.t_Global =
    Alloc.Vec.impl__new #(t_Array t_Scalar v_T) ()
  in
  let curr_win:Core.Ops.Range.t_Range usize =
    {
      Core.Ops.Range.f_start = lower_bound;
      Core.Ops.Range.f_end
      =
      cast (Bachelor_formally_verified_stuff.Convert.min #u128
            ((cast (lower_bound <: usize) <: u128) +! (cast (min_len <: usize) <: u128) <: u128)
            (cast (impl_8__len v_T rhs <: usize) <: u128)
          <:
          u128)
      <:
      usize
    }
    <:
    Core.Ops.Range.t_Range usize
  in
  let coeffs, curr_win, lower_bound, remainder:(Alloc.Vec.t_Vec t_Scalar Alloc.Alloc.t_Global &
    Core.Ops.Range.t_Range usize &
    usize &
    Alloc.Vec.t_Vec (t_Array t_Scalar v_T) Alloc.Alloc.t_Global) =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      (Alloc.Vec.impl_1__len #(t_Array t_Scalar v_T) #Alloc.Alloc.t_Global largest.f_coeffs <: usize
      )
      (fun temp_0_ temp_1_ ->
          let coeffs, curr_win, lower_bound, remainder:(Alloc.Vec.t_Vec t_Scalar
              Alloc.Alloc.t_Global &
            Core.Ops.Range.t_Range usize &
            usize &
            Alloc.Vec.t_Vec (t_Array t_Scalar v_T) Alloc.Alloc.t_Global) =
            temp_0_
          in
          let _:usize = temp_1_ in
          true)
      (coeffs, curr_win, lower_bound, remainder
        <:
        (Alloc.Vec.t_Vec t_Scalar Alloc.Alloc.t_Global & Core.Ops.Range.t_Range usize & usize &
          Alloc.Vec.t_Vec (t_Array t_Scalar v_T) Alloc.Alloc.t_Global))
      (fun temp_0_ i ->
          let coeffs, curr_win, lower_bound, remainder:(Alloc.Vec.t_Vec t_Scalar
              Alloc.Alloc.t_Global &
            Core.Ops.Range.t_Range usize &
            usize &
            Alloc.Vec.t_Vec (t_Array t_Scalar v_T) Alloc.Alloc.t_Global) =
            temp_0_
          in
          let i:usize = i in
          let lower_bound:usize = i in
          let remainder:Alloc.Vec.t_Vec (t_Array t_Scalar v_T) Alloc.Alloc.t_Global =
            Alloc.Slice.impl__to_vec #(t_Array t_Scalar v_T)
              (largest.f_coeffs.[ { Core.Ops.Range.f_start = i } <: Core.Ops.Range.t_RangeFrom usize
                ]
                <:
                t_Slice (t_Array t_Scalar v_T))
          in
          let curr_win:Core.Ops.Range.t_Range usize =
            {
              Core.Ops.Range.f_start = i;
              Core.Ops.Range.f_end
              =
              Alloc.Vec.impl_1__len #(t_Array t_Scalar v_T) #Alloc.Alloc.t_Global largest.f_coeffs
            }
            <:
            Core.Ops.Range.t_Range usize
          in
          let largest_slice:Alloc.Vec.t_Vec (t_Array t_Scalar v_T) Alloc.Alloc.t_Global =
            Alloc.Slice.impl__to_vec #(t_Array t_Scalar v_T)
              (largest.f_coeffs.[ curr_win ] <: t_Slice (t_Array t_Scalar v_T))
          in
          let smallest_slice:Alloc.Vec.t_Vec (t_Array t_Scalar v_T) Alloc.Alloc.t_Global =
            Alloc.Slice.impl__to_vec #(t_Array t_Scalar v_T)
              (smallest.f_coeffs.[ Core.Ops.Range.RangeFull <: Core.Ops.Range.t_RangeFull ]
                <:
                t_Slice (t_Array t_Scalar v_T))
          in
          let res:t_Scalar = cross_product_vec v_T smallest_slice largest_slice in
          let coeffs:Alloc.Vec.t_Vec t_Scalar Alloc.Alloc.t_Global =
            Alloc.Vec.impl_1__push #t_Scalar #Alloc.Alloc.t_Global coeffs res
          in
          coeffs, curr_win, lower_bound, remainder
          <:
          (Alloc.Vec.t_Vec t_Scalar Alloc.Alloc.t_Global & Core.Ops.Range.t_Range usize & usize &
            Alloc.Vec.t_Vec (t_Array t_Scalar v_T) Alloc.Alloc.t_Global))
  in
  let last_in_min:t_Array t_Scalar v_T =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter #(Alloc.Vec.t_Vec
              (t_Array t_Scalar v_T) Alloc.Alloc.t_Global)
          #FStar.Tactics.Typeclasses.solve
          smallest.f_coeffs
        <:
        Core.Slice.Iter.t_Iter (t_Array t_Scalar v_T))
      last_in_min
      (fun last_in_min e ->
          let last_in_min:t_Array t_Scalar v_T = last_in_min in
          e)
  in
  if min_len =. max_len
  then { f_coeffs = coeffs } <: t_Polynomium t_Scalar
  else
    let coeffs:Alloc.Vec.t_Vec t_Scalar Alloc.Alloc.t_Global =
      Rust_primitives.Hax.Folds.fold_range (mk_usize 1)
        (Alloc.Vec.impl_1__len #(t_Array t_Scalar v_T) #Alloc.Alloc.t_Global remainder <: usize)
        (fun coeffs temp_1_ ->
            let coeffs:Alloc.Vec.t_Vec t_Scalar Alloc.Alloc.t_Global = coeffs in
            let _:usize = temp_1_ in
            true)
        coeffs
        (fun coeffs i ->
            let coeffs:Alloc.Vec.t_Vec t_Scalar Alloc.Alloc.t_Global = coeffs in
            let i:usize = i in
            let res:t_Scalar =
              inner_prod_scalars v_T last_in_min (remainder.[ i ] <: t_Array t_Scalar v_T)
            in
            let coeffs:Alloc.Vec.t_Vec t_Scalar Alloc.Alloc.t_Global =
              Alloc.Vec.impl_1__push #t_Scalar #Alloc.Alloc.t_Global coeffs res
            in
            coeffs)
    in
    { f_coeffs = coeffs } <: t_Polynomium t_Scalar

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_3__from__polynomium (v_T: usize)
    : Core.Ops.Arith.t_Mul (t_Polynomium (t_Array t_Scalar v_T))
      (t_Polynomium (t_Array t_Scalar v_T)) =
  {
    f_Output = t_Polynomium t_Scalar;
    f_mul_pre
    =
    (fun (self: t_Polynomium (t_Array t_Scalar v_T)) (rhs: t_Polynomium (t_Array t_Scalar v_T)) ->
        true);
    f_mul_post
    =
    (fun
        (self: t_Polynomium (t_Array t_Scalar v_T))
        (rhs: t_Polynomium (t_Array t_Scalar v_T))
        (out: t_Polynomium t_Scalar)
        ->
        true);
    f_mul
    =
    fun (self: t_Polynomium (t_Array t_Scalar v_T)) (rhs: t_Polynomium (t_Array t_Scalar v_T)) ->
      jonamul_vec v_T self rhs
  }

/// For extending a polynomial of scalars. If the RHS is longer, extends the lhs with the diff
let extend_from (lhs rhs: Alloc.Vec.t_Vec t_Scalar Alloc.Alloc.t_Global)
    : Alloc.Vec.t_Vec t_Scalar Alloc.Alloc.t_Global =
  let res:Alloc.Vec.t_Vec t_Scalar Alloc.Alloc.t_Global =
    Core.Clone.f_clone #(Alloc.Vec.t_Vec t_Scalar Alloc.Alloc.t_Global)
      #FStar.Tactics.Typeclasses.solve
      lhs
  in
  if
    (Alloc.Vec.impl_1__len #t_Scalar #Alloc.Alloc.t_Global lhs <: usize) >.
    (Alloc.Vec.impl_1__len #t_Scalar #Alloc.Alloc.t_Global rhs <: usize)
  then
    Alloc.Slice.impl__to_vec #t_Scalar
      (Core.Ops.Deref.f_deref #(Alloc.Vec.t_Vec t_Scalar Alloc.Alloc.t_Global)
          #FStar.Tactics.Typeclasses.solve
          lhs
        <:
        t_Slice t_Scalar)
  else
    Rust_primitives.Hax.Folds.fold_range (Alloc.Vec.impl_1__len #t_Scalar #Alloc.Alloc.t_Global lhs
        <:
        usize)
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

#push-options "--z3rlimit 100"

let add_scalar_polynomium (lhs rhs: t_Polynomium t_Scalar)
    : Prims.Pure (t_Polynomium t_Scalar)
      (requires
        (impl_5__len lhs <: usize) >=. mk_usize 0 &&
        (impl_5__len lhs <: usize) <=. Core.Num.impl_usize__MAX &&
        (impl_5__len rhs <: usize) >=. mk_usize 0 &&
        (impl_5__len rhs <: usize) <=. Core.Num.impl_usize__MAX)
      (ensures
        fun res ->
          let res:t_Polynomium t_Scalar = res in
          (impl_5__len res <: usize) >=. mk_usize 0 &&
          (impl_5__len res <: usize) <=. Core.Num.impl_usize__MAX) =
  let min_len:usize =
    if (impl_5__len lhs <: usize) <. (impl_5__len rhs <: usize)
    then impl_5__len lhs
    else impl_5__len rhs
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
    if min_len <. (impl_5__len lhs <: usize)
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
      if min_len <. (impl_5__len rhs <: usize)
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

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_1__from__polynomium: Core.Ops.Arith.t_Add (t_Polynomium t_Scalar) (t_Polynomium t_Scalar) =
  {
    f_Output = t_Polynomium t_Scalar;
    f_add_pre = (fun (self: t_Polynomium t_Scalar) (rhs: t_Polynomium t_Scalar) -> true);
    f_add_post
    =
    (fun (self: t_Polynomium t_Scalar) (rhs: t_Polynomium t_Scalar) (out: t_Polynomium t_Scalar) ->
        true);
    f_add
    =
    fun (self: t_Polynomium t_Scalar) (rhs: t_Polynomium t_Scalar) -> add_scalar_polynomium self rhs
  }

/// For extending a polynomial of scalars with the negation. If the RHS is longer, extends the lhs with the diff
let extend_from_neg (lhs rhs: Alloc.Vec.t_Vec t_Scalar Alloc.Alloc.t_Global)
    : Alloc.Vec.t_Vec t_Scalar Alloc.Alloc.t_Global =
  let res:Alloc.Vec.t_Vec t_Scalar Alloc.Alloc.t_Global =
    Core.Clone.f_clone #(Alloc.Vec.t_Vec t_Scalar Alloc.Alloc.t_Global)
      #FStar.Tactics.Typeclasses.solve
      lhs
  in
  if
    (Alloc.Vec.impl_1__len #t_Scalar #Alloc.Alloc.t_Global lhs <: usize) >.
    (Alloc.Vec.impl_1__len #t_Scalar #Alloc.Alloc.t_Global rhs <: usize)
  then
    Alloc.Slice.impl__to_vec #t_Scalar
      (Core.Ops.Deref.f_deref #(Alloc.Vec.t_Vec t_Scalar Alloc.Alloc.t_Global)
          #FStar.Tactics.Typeclasses.solve
          lhs
        <:
        t_Slice t_Scalar)
  else
    Rust_primitives.Hax.Folds.fold_range (Alloc.Vec.impl_1__len #t_Scalar #Alloc.Alloc.t_Global lhs
        <:
        usize)
      (Alloc.Vec.impl_1__len #t_Scalar #Alloc.Alloc.t_Global rhs <: usize)
      (fun res temp_1_ ->
          let res:Alloc.Vec.t_Vec t_Scalar Alloc.Alloc.t_Global = res in
          let _:usize = temp_1_ in
          true)
      res
      (fun res i ->
          let res:Alloc.Vec.t_Vec t_Scalar Alloc.Alloc.t_Global = res in
          let i:usize = i in
          Alloc.Vec.impl_1__push #t_Scalar
            #Alloc.Alloc.t_Global
            res
            (Core.Ops.Arith.f_sub #t_Scalar
                #t_Scalar
                #FStar.Tactics.Typeclasses.solve
                impl__ZERO
                (rhs.[ i ] <: t_Scalar)
              <:
              t_Scalar)
          <:
          Alloc.Vec.t_Vec t_Scalar Alloc.Alloc.t_Global)

#push-options "--z3rlimit 100"

let sub_scalar_polynomium (lhs rhs: t_Polynomium t_Scalar)
    : Prims.Pure (t_Polynomium t_Scalar)
      (requires
        (impl_5__len lhs <: usize) >=. mk_usize 0 &&
        (impl_5__len lhs <: usize) <=. Core.Num.impl_usize__MAX &&
        (impl_5__len rhs <: usize) >=. mk_usize 0 &&
        (impl_5__len rhs <: usize) <=. Core.Num.impl_usize__MAX)
      (ensures
        fun res ->
          let res:t_Polynomium t_Scalar = res in
          (impl_5__len res <: usize) >=. mk_usize 0 &&
          (impl_5__len res <: usize) <=. Core.Num.impl_usize__MAX) =
  let min_len:usize =
    if (impl_5__len lhs <: usize) <. (impl_5__len rhs <: usize)
    then impl_5__len lhs
    else impl_5__len rhs
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
            (Core.Ops.Arith.f_sub #t_Scalar
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
    if min_len <. (impl_5__len lhs <: usize)
    then
      extend_from_neg (Alloc.Slice.impl__to_vec #t_Scalar
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
      if min_len <. (impl_5__len rhs <: usize)
      then
        extend_from_neg (Alloc.Slice.impl__to_vec #t_Scalar
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

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_2__from__polynomium: Core.Ops.Arith.t_Sub (t_Polynomium t_Scalar) (t_Polynomium t_Scalar) =
  {
    f_Output = t_Polynomium t_Scalar;
    f_sub_pre = (fun (self: t_Polynomium t_Scalar) (rhs: t_Polynomium t_Scalar) -> true);
    f_sub_post
    =
    (fun (self: t_Polynomium t_Scalar) (rhs: t_Polynomium t_Scalar) (out: t_Polynomium t_Scalar) ->
        true);
    f_sub
    =
    fun (self: t_Polynomium t_Scalar) (rhs: t_Polynomium t_Scalar) -> sub_scalar_polynomium self rhs
  }

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
  if
    (Alloc.Vec.impl_1__len #(t_Array t_Scalar v_T) #Alloc.Alloc.t_Global lhs <: usize) <.
    (Alloc.Vec.impl_1__len #(t_Array t_Scalar v_T) #Alloc.Alloc.t_Global rhs <: usize)
  then
    Alloc.Slice.impl__to_vec #(t_Array t_Scalar v_T)
      (Core.Ops.Deref.f_deref #(Alloc.Vec.t_Vec (t_Array t_Scalar v_T) Alloc.Alloc.t_Global)
          #FStar.Tactics.Typeclasses.solve
          lhs
        <:
        t_Slice (t_Array t_Scalar v_T))
  else
    Rust_primitives.Hax.Folds.fold_range (Alloc.Vec.impl_1__len #(t_Array t_Scalar v_T)
          #Alloc.Alloc.t_Global
          lhs
        <:
        usize)
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

#push-options "--z3rlimit 100"

let add_vector_polynomium (v_T: usize) (lhs rhs: t_Polynomium (t_Array t_Scalar v_T))
    : Prims.Pure (t_Polynomium (t_Array t_Scalar v_T))
      (requires
        (impl_8__len v_T lhs <: usize) >=. mk_usize 0 &&
        (impl_8__len v_T lhs <: usize) <=. Core.Num.impl_usize__MAX &&
        (impl_8__len v_T rhs <: usize) >=. mk_usize 0 &&
        (impl_8__len v_T rhs <: usize) <=. Core.Num.impl_usize__MAX)
      (ensures
        fun res ->
          let res:t_Polynomium (t_Array t_Scalar v_T) = res in
          (impl_8__len v_T res <: usize) >=. mk_usize 0 &&
          (impl_8__len v_T res <: usize) <=. Core.Num.impl_usize__MAX) =
  let min_len:usize =
    if (impl_8__len v_T lhs <: usize) <. (impl_8__len v_T rhs <: usize)
    then impl_8__len v_T lhs
    else impl_8__len v_T rhs
  in
  let coeffs:Alloc.Vec.t_Vec (t_Array t_Scalar v_T) Alloc.Alloc.t_Global =
    add_vec_vec v_T
      (Alloc.Slice.impl__to_vec #(t_Array t_Scalar v_T)
          (lhs.f_coeffs.[ { Core.Ops.Range.f_end = min_len } <: Core.Ops.Range.t_RangeTo usize ]
            <:
            t_Slice (t_Array t_Scalar v_T))
        <:
        Alloc.Vec.t_Vec (t_Array t_Scalar v_T) Alloc.Alloc.t_Global)
      (Alloc.Slice.impl__to_vec #(t_Array t_Scalar v_T)
          (rhs.f_coeffs.[ { Core.Ops.Range.f_end = min_len } <: Core.Ops.Range.t_RangeTo usize ]
            <:
            t_Slice (t_Array t_Scalar v_T))
        <:
        Alloc.Vec.t_Vec (t_Array t_Scalar v_T) Alloc.Alloc.t_Global)
  in
  {
    f_coeffs
    =
    if min_len <. (impl_8__len v_T lhs <: usize)
    then extend_from_vec v_T coeffs lhs.f_coeffs
    else
      if min_len <. (impl_8__len v_T rhs <: usize)
      then extend_from_vec v_T coeffs rhs.f_coeffs
      else coeffs
  }
  <:
  t_Polynomium (t_Array t_Scalar v_T)

#pop-options

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_4__from__polynomium (v_T: usize)
    : Core.Ops.Arith.t_Add (t_Polynomium (t_Array t_Scalar v_T))
      (t_Polynomium (t_Array t_Scalar v_T)) =
  {
    f_Output = t_Polynomium (t_Array t_Scalar v_T);
    f_add_pre
    =
    (fun (self: t_Polynomium (t_Array t_Scalar v_T)) (rhs: t_Polynomium (t_Array t_Scalar v_T)) ->
        true);
    f_add_post
    =
    (fun
        (self: t_Polynomium (t_Array t_Scalar v_T))
        (rhs: t_Polynomium (t_Array t_Scalar v_T))
        (out: t_Polynomium (t_Array t_Scalar v_T))
        ->
        true);
    f_add
    =
    fun (self: t_Polynomium (t_Array t_Scalar v_T)) (rhs: t_Polynomium (t_Array t_Scalar v_T)) ->
      add_vector_polynomium v_T self rhs
  }
