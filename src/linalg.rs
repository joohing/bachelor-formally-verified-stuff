#![allow(unused_imports)]
#![allow(nonstandard_style)]
#![allow(dead_code)]
#![allow(unused_variables)]

use crate::*;

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
    #[hax_lib::fstar::options("--z3rlimit 100")]
    #[ensures(|res| res.len() == T)]
    fn add_vec(&self, rhs: &vec<'a, T>) -> vec<'a, T> {
        let mut res = new_zero_slice();
        for i in 0..T {
            res[i] = self[i] + rhs[i];
        }
        res
    }

    #[hax_lib::fstar::options("--z3rlimit 100")]
    #[ensures(|res| res.len() == T)]
    fn sub_vec(&self, rhs: &vec<'a, T>) -> vec<'a, T> {
        let mut res = new_zero_slice();
        for i in 0..T {
            res[i] = self[i] - rhs[i];
        }
        res
    }
}

impl<'a, const T: usize> Scalable for vec<'a, T> {
    #[hax_lib::fstar::options("--z3rlimit 100")]
    #[requires(rhs.v < PRIME)]
    #[ensures(|res| res.len() == T)]
    fn mul_vec_scalar(&self, rhs: Scalar) -> vec<'a, T> {
        let mut res = new_zero_slice();
        for i in 0..T {
            res[i] = self[i] * rhs;
        }
        res
    }
}

impl<'a, const T: usize> EqLen<'a, T> for vec<'a, T> {
    #[hax_lib::fstar::options("--z3rlimit 100")]
    #[ensures(|res| res.len() == T)]
    fn hadamard(&self, rhs: &vec<T>) -> Self {
        hadamard_vec(&self, rhs)
    }
}

/// Computes the inner product between two vectors
/// of scalars, e.g. [1, 2, 3] x [4, 5, 6] = 32.
#[hax_lib::fstar::options("--z3rlimit 100")]
#[requires(A.len() == B.len())]
#[ensures(|res| res.v < PRIME)]
pub fn inner_prod_scalars<'a, const T: usize>(A: &vec<'a, T>, B: &vec<'a, T>) -> Scalar {
	let mut acc = Scalar::ZERO;
    for (a, b) in A.iter().zip(B.iter()) {
        acc = acc + a.clone() * b.clone();
    }
    acc
}

/// Hadamard product of two vectors of scalars
#[hax_lib::fstar::options("--z3rlimit 100")]
#[requires(a.len() == b.len())]
#[ensures(|res| res.len() == T)]
fn hadamard_vec<'a, const T: usize>(a: &vec<'a, T>, b: &vec<'a, T>) -> vec<'a, T> {
    let mut res = new_zero_slice();
    for i in 0..T {
        res[i] = a[i].clone() * b[i].clone();
    }
    res
}

#[hax_lib::fstar::options("--z3rlimit 100")]
#[requires(lhs.len() == rhs.len())]
#[ensures(|res| res.len() >= 0 && res.len() <= usize::MAX)]
pub fn add_vec_vec<'a, const T: usize>(lhs: &Vec<vec<'a, T>>, rhs: &Vec<vec<'a, T>>) -> Vec<vec<'a, T>> {
    let mut res = vec![];
    for i in 0..lhs.len() {
        res.push(add_vec(&lhs[i], &rhs[i]));
    }
    res
}

#[hax_lib::fstar::options("--z3rlimit 100")]
#[requires(lhs.len() == rhs.len())]
#[ensures(|res| res.len() >= 0 && res.len() <= usize::MAX)]
fn sub_vec<'a, const T: usize>(lhs: &vec<'a, T>, rhs: &vec<'a, T>) -> vec<'a, T> {
    let mut res = [Scalar::ZERO; T];
    for i in 0..(if lhs.len() < rhs.len() { lhs.len() } else { rhs.len() }) {
        res[i] = lhs[i] - rhs[i];
    }
    res
}

#[hax_lib::fstar::options("--z3rlimit 100")]
#[requires(lhs.len() == rhs.len())]
#[ensures(|res| res.len() >= 0 && res.len() <= usize::MAX)]
pub fn add_vec<'a, const T: usize>(lhs: &vec<'a, T>, rhs: &vec<'a, T>) -> vec<'a, T> {
    let mut res = [Scalar::ZERO; T];
    for i in 0..T { res[i] = lhs[i].clone() + rhs[i].clone(); }
    res
}
