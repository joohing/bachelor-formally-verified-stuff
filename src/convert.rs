#![allow(non_camel_case_types)]
#![allow(unused_imports)]
#![allow(unused_assignments)]

use hax_lib::{requires, exclude, attributes, ensures, fstar, fstar::options};
use crate::{Scalar, polynomium::*, linalg::*};

/// This lets you go `scalar_vec![1, 2, 3]` and get a vec of scalars.
/// As such, you might say this is a pretty cool macro.
#[macro_export]
macro_rules! scalar_vec {
    ( $( $x:expr ),* ) => {
        {
            let mut v = Vec::new();
            $(
                let s = Scalar::from($x as u128);
                v.push(s);
            )*
            v
        }
    }
}

/// Same as scalar_vec but the sized type instead
#[macro_export]
macro_rules! scalar_vec_sized {
    ( $( $x:expr ),* ) => {
        {
            let mut v = new_zero_slice();
            let mut idx: usize = 0;
            $(
                let s = Scalar::from($x as u128);
                v[idx] = s;
                idx = idx + 1;
            )*
            v
        }
    }
}

pub fn max<T>(a: T, b: T) -> T where T: PartialOrd {
    if a > b { a } else { b }
}

pub fn min<T>(a: T, b: T) -> T where T: PartialOrd {
    if a < b { a } else { b }
}
