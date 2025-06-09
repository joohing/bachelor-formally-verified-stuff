module Bachelor_formally_verified_stuff.Polynomium
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

include Bachelor_formally_verified_stuff.Bundle {t_Polynomium as t_Polynomium}

include Bachelor_formally_verified_stuff.Bundle {impl_11 as impl_11}

include Bachelor_formally_verified_stuff.Bundle {impl_12 as impl_12}

include Bachelor_formally_verified_stuff.Bundle {impl_13 as impl_13}

include Bachelor_formally_verified_stuff.Bundle {impl_14 as impl_14}

include Bachelor_formally_verified_stuff.Bundle {f_trim_pre as f_trim_pre}

include Bachelor_formally_verified_stuff.Bundle {f_trim_post as f_trim_post}

include Bachelor_formally_verified_stuff.Bundle {f_trim as f_trim}

include Bachelor_formally_verified_stuff.Bundle {f_eval_pre as f_eval_pre}

include Bachelor_formally_verified_stuff.Bundle {f_eval_post as f_eval_post}

include Bachelor_formally_verified_stuff.Bundle {f_eval as f_eval}

include Bachelor_formally_verified_stuff.Bundle {impl__from__polynomium as impl}

include Bachelor_formally_verified_stuff.Bundle {impl_1__from__polynomium as impl_1}

include Bachelor_formally_verified_stuff.Bundle {impl_2__from__polynomium as impl_2}

include Bachelor_formally_verified_stuff.Bundle {impl_3__from__polynomium as impl_3}

include Bachelor_formally_verified_stuff.Bundle {impl_4__from__polynomium as impl_4}

include Bachelor_formally_verified_stuff.Bundle {new_zero_slice as new_zero_slice}

include Bachelor_formally_verified_stuff.Bundle {impl_5__len as impl_5__len}

include Bachelor_formally_verified_stuff.Bundle {impl_5__new_from_scalar as impl_5__new_from_scalar}

include Bachelor_formally_verified_stuff.Bundle {impl_6__from__polynomium as impl_6}

include Bachelor_formally_verified_stuff.Bundle {impl_7__from__polynomium as impl_7}

include Bachelor_formally_verified_stuff.Bundle {impl_8__len as impl_8__len}

include Bachelor_formally_verified_stuff.Bundle {impl_8__new_from_vec as impl_8__new_from_vec}

include Bachelor_formally_verified_stuff.Bundle {impl_9__from__polynomium as impl_9}

include Bachelor_formally_verified_stuff.Bundle {impl_10 as impl_10}

include Bachelor_formally_verified_stuff.Bundle {trim as trim}

include Bachelor_formally_verified_stuff.Bundle {trim_vec as trim_vec}

include Bachelor_formally_verified_stuff.Bundle {evaluate_polynomial as evaluate_polynomial}

include Bachelor_formally_verified_stuff.Bundle {evaluate_vector_polynomial as evaluate_vector_polynomial}

include Bachelor_formally_verified_stuff.Bundle {jonamul as jonamul}

include Bachelor_formally_verified_stuff.Bundle {cross_product as cross_product}

include Bachelor_formally_verified_stuff.Bundle {jonamul_vec as jonamul_vec}

include Bachelor_formally_verified_stuff.Bundle {cross_product_vec as cross_product_vec}

include Bachelor_formally_verified_stuff.Bundle {add_scalar_polynomium as add_scalar_polynomium}

include Bachelor_formally_verified_stuff.Bundle {sub_scalar_polynomium as sub_scalar_polynomium}

include Bachelor_formally_verified_stuff.Bundle {extend_from as extend_from}

include Bachelor_formally_verified_stuff.Bundle {extend_from_neg as extend_from_neg}

include Bachelor_formally_verified_stuff.Bundle {add_vector_polynomium as add_vector_polynomium}

include Bachelor_formally_verified_stuff.Bundle {extend_from_vec as extend_from_vec}
