#![allow(unused_imports)]
#![allow(nonstandard_style)]
#![allow(dead_code)]
#![allow(unused_variables)]

use crate::*;

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

pub trait Scalable {
    fn mul_vec_scalar(&self, rhs: Scalar) -> Self;
}

pub trait EqLen<'a, const T: usize> {
    fn hadamard(&self, rhs: &vec<'a, T>) -> Self;
}

pub trait AddSub<'a, const T: usize> {
    fn add_vec(&self, rhs: &vec<'a, T>) -> vec<'a, T>;
    fn sub_vec(&self, rhs: &vec<'a, T>) -> vec<'a, T>;
}

pub trait Matrix {
    fn dims(&self) -> (usize, usize);
}

impl<'a, const T: usize> AddSub<'a, T> for vec<'a, T> {
    fn add_vec(&self, rhs: &vec<'a, T>) -> vec<'a, T> {
        let mut res = new_zero_slice();
        for i in 0..T {
            res[i] = self[i] + rhs[i];
        }
        res
    }

    fn sub_vec(&self, rhs: &vec<'a, T>) -> vec<'a, T> {
        let mut res = new_zero_slice();
        for i in 0..T {
            res[i] = self[i] - rhs[i];
        }
        res
    }
}

impl<'a, const T: usize> Scalable for vec<'a, T> {
    fn mul_vec_scalar(&self, rhs: Scalar) -> vec<'a, T> {
        let mut res = new_zero_slice();
        for i in 0..T {
            res[i] = self[i] * rhs;
        }
        res
    }
}

impl<'a, const T: usize> EqLen<'a, T> for vec<'a, T> {
    fn hadamard(&self, rhs: &vec<T>) -> Self {
        hadamard_vec(&self, rhs)
    }
}

/// Computes the inner product between two vectors
/// of scalars, e.g. [1, 2, 3] x [4, 5, 6] = 32.
pub fn inner_prod_scalars<'a, const T: usize>(A: &vec<'a, T>, B: &vec<'a, T>) -> Scalar {
	let mut acc = Scalar::ZERO;
    for (a, b) in A.iter().zip(B.iter()) {
        acc = acc + a.clone() * b.clone();
    }
    acc
}

/// Hadamard product of two vectors of scalars
fn hadamard_vec<'a, const T: usize>(a: &vec<'a, T>, b: &vec<'a, T>) -> vec<'a, T> {
    let mut res = new_zero_slice();
    for i in 0..T {
        res[i] = a[i].clone() * b[i].clone();
    }
    res
}
