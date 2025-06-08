module Bachelor_formally_verified_stuff
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

include Bachelor_formally_verified_stuff.Bundle {v_PRIME as v_PRIME}

include Bachelor_formally_verified_stuff.Bundle {main as main}

include Bachelor_formally_verified_stuff.Bundle {t_Scalar as t_Scalar}

include Bachelor_formally_verified_stuff.Bundle {impl_4 as impl_4}

include Bachelor_formally_verified_stuff.Bundle {impl_5 as impl_5}

include Bachelor_formally_verified_stuff.Bundle {impl_6 as impl_6}

include Bachelor_formally_verified_stuff.Bundle {impl_7 as impl_7}

include Bachelor_formally_verified_stuff.Bundle {impl_8 as impl_8}

include Bachelor_formally_verified_stuff.Bundle {impl__ZERO as impl_Scalar__ZERO}

include Bachelor_formally_verified_stuff.Bundle {impl__from as impl_Scalar__from}

include Bachelor_formally_verified_stuff.Bundle {impl_1 as impl_1}

include Bachelor_formally_verified_stuff.Bundle {impl_2 as impl_2}

include Bachelor_formally_verified_stuff.Bundle {impl_3 as impl_3}

include Bachelor_formally_verified_stuff.Bundle {add_vec as add_vec}

include Bachelor_formally_verified_stuff.Bundle {get_summed as get_summed}

include Bachelor_formally_verified_stuff.Bundle {get_zipped as get_zipped}

include Bachelor_formally_verified_stuff.Bundle {all_vecs_eq_len as all_vecs_eq_len}

include Bachelor_formally_verified_stuff.Bundle {add_vec_vec as add_vec_vec}

include Bachelor_formally_verified_stuff.Bundle {sub_vec as sub_vec}

include Bachelor_formally_verified_stuff.Bundle {add_scalar_polynomium as add_scalar_polynomium}

include Bachelor_formally_verified_stuff.Bundle {extend_from as extend_from}

include Bachelor_formally_verified_stuff.Bundle {add_vector_polynomium as add_vector_polynomium}

include Bachelor_formally_verified_stuff.Bundle {extend_from_vec as extend_from_vec}

include Bachelor_formally_verified_stuff.Bundle {simple_polynomial_mul as simple_polynomial_mul}

include Bachelor_formally_verified_stuff.Bundle {simple_vector_polynomial_mul as simple_vector_polynomial_mul}

include Bachelor_formally_verified_stuff.Bundle {inner_prod_scalars as inner_prod_scalars}
