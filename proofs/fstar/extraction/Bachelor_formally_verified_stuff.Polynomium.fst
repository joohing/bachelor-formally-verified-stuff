module Bachelor_formally_verified_stuff.Polynomium
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

include Bachelor_formally_verified_stuff.Bundle {t_Polynomium as t_Polynomium}

include Bachelor_formally_verified_stuff.Bundle {impl_6__from__polynomium as impl_6}

include Bachelor_formally_verified_stuff.Bundle {impl_7__from__polynomium as impl_7}

include Bachelor_formally_verified_stuff.Bundle {impl_8__from__polynomium as impl_8}

include Bachelor_formally_verified_stuff.Bundle {impl_9 as impl_9}

include Bachelor_formally_verified_stuff.Bundle {impl__from__polynomium as impl}

include Bachelor_formally_verified_stuff.Bundle {impl_1__from__polynomium as impl_1}

include Bachelor_formally_verified_stuff.Bundle {impl_2__from__polynomium as impl_2}

include Bachelor_formally_verified_stuff.Bundle {impl_3__from__polynomium as impl_3}

include Bachelor_formally_verified_stuff.Bundle {new_zero_slice as new_zero_slice}

include Bachelor_formally_verified_stuff.Bundle {impl_4__len as impl_4__len}

include Bachelor_formally_verified_stuff.Bundle {impl_4__new_from_scalar as impl_4__new_from_scalar}

include Bachelor_formally_verified_stuff.Bundle {impl_4__trim as impl_4__trim}

include Bachelor_formally_verified_stuff.Bundle {impl_4__eval as impl_4__eval}

include Bachelor_formally_verified_stuff.Bundle {impl_5__len as impl_5__len}

include Bachelor_formally_verified_stuff.Bundle {impl_5__new_from_vec as impl_5__new_from_vec}

include Bachelor_formally_verified_stuff.Bundle {impl_5__trim as impl_5__trim}

include Bachelor_formally_verified_stuff.Bundle {impl_5__eval as impl_5__eval}

include Bachelor_formally_verified_stuff.Bundle {trim_rec as trim_rec}

include Bachelor_formally_verified_stuff.Bundle {trim_vec_rec as trim_vec_rec}

include Bachelor_formally_verified_stuff.Bundle {evaluate_polynomial as evaluate_polynomial}

include Bachelor_formally_verified_stuff.Bundle {evaluate_vector_polynomial as evaluate_vector_polynomial}
