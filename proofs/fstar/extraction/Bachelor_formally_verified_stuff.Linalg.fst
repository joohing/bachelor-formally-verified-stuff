module Bachelor_formally_verified_stuff.Linalg
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

include Bachelor_formally_verified_stuff.Bundle {f_mul_vec_scalar_pre as f_mul_vec_scalar_pre}

include Bachelor_formally_verified_stuff.Bundle {f_mul_vec_scalar_post as f_mul_vec_scalar_post}

include Bachelor_formally_verified_stuff.Bundle {f_mul_vec_scalar as f_mul_vec_scalar}

include Bachelor_formally_verified_stuff.Bundle {f_hadamard_pre as f_hadamard_pre}

include Bachelor_formally_verified_stuff.Bundle {f_hadamard_post as f_hadamard_post}

include Bachelor_formally_verified_stuff.Bundle {f_hadamard as f_hadamard}

include Bachelor_formally_verified_stuff.Bundle {f_add_vec_pre as f_add_vec_pre}

include Bachelor_formally_verified_stuff.Bundle {f_add_vec_post as f_add_vec_post}

include Bachelor_formally_verified_stuff.Bundle {f_add_vec as f_add_vec}

include Bachelor_formally_verified_stuff.Bundle {f_sub_vec_pre as f_sub_vec_pre}

include Bachelor_formally_verified_stuff.Bundle {f_sub_vec_post as f_sub_vec_post}

include Bachelor_formally_verified_stuff.Bundle {f_sub_vec as f_sub_vec}

include Bachelor_formally_verified_stuff.Bundle {f_dims_pre as f_dims_pre}

include Bachelor_formally_verified_stuff.Bundle {f_dims_post as f_dims_post}

include Bachelor_formally_verified_stuff.Bundle {f_dims as f_dims}

include Bachelor_formally_verified_stuff.Bundle {impl as impl}

include Bachelor_formally_verified_stuff.Bundle {impl_1__from__linalg as impl_1}

include Bachelor_formally_verified_stuff.Bundle {impl_2__from__linalg as impl_2}

include Bachelor_formally_verified_stuff.Bundle {inner_prod_scalars__from__linalg as inner_prod_scalars}

include Bachelor_formally_verified_stuff.Bundle {hadamard_vec as hadamard_vec}
