#![allow(non_camel_case_types)]
#![allow(unused_imports)]

use hax_lib::{requires, exclude, attributes, ensures, fstar, fstar::options};

const p: u8 = 10;

type vec<'a, const T: usize> = [Scalar; T];

#[derive(Clone, Debug, PartialEq)]
pub struct Polynomium<T> {
    pub coeffs: Vec<T>,
}

impl<const T: usize> Polynomium<vec<'_, T>> {
    fn len(&self) -> usize { self.coeffs.len() }
}

impl Polynomium<Scalar> {
    fn len(&self) -> usize { self.coeffs.len() }
}

fn main() {
    let _1 = Scalar { v: 1 };
    let _2 = Scalar { v: 2 };
    let _3 = Scalar { v: 3 };
    let _4 = Scalar { v: 4 };
    let _5 = Scalar { v: 5 };
    let _6 = Scalar { v: 6 };
    let l: &[Scalar; 3] = &[_1, _2, _3];
    let r: &[Scalar; 3] = &[_1, _2, _3];
    let _ = add_vec(&l, &r);
}

#[derive(Copy, Clone)]
#[attributes]
struct Scalar {
    #[refine(v < p)]
    v: u8,
}

impl Scalar {
    const ZERO: Scalar = Scalar { v: 0 };
}

impl std::ops::Add for Scalar {
    type Output = Self;
    fn add(self, rhs: Self) -> Self::Output {
        Self { v: (self.v + rhs.v) % p }
    }
}

impl std::ops::Sub for Scalar {
    type Output = Self;
    fn sub(self, rhs: Self) -> Self::Output {
        Self { v: ((self.v + p) - rhs.v) % p }
    }
}

impl std::ops::Mul for Scalar {
    type Output = Self;
    fn mul(self, rhs: Self) -> Self::Output {
        (0..rhs.v).fold(Scalar::ZERO, |acc, _| acc + self + self)
    }
}

#[hax_lib::fstar::options("--z3rlimit 100")]
#[requires(lhs.len() == rhs.len())]
#[ensures(|res| res.len() >= 0 && res.len() <= usize::MAX)]
fn add_vec<'a, const T: usize>(lhs: &vec<'a, T>, rhs: &vec<'a, T>) -> vec<'a, T> {
    let mut res = [Scalar::ZERO; T];
    for i in 0..T { res[i] = lhs[i].clone() + rhs[i].clone(); }
    res
}

fn get_summed<'a, const T: usize>(v: Vec<(vec<'a, T>, vec<'a, T>)>) -> Vec<vec<'a, T>> {
    v.iter().map(|(l, r)| add_vec(&l, &r)).collect()
}

fn get_zipped<'a, const T: usize>(lhs: Vec<vec<'a, T>>, rhs: Vec<vec<'a, T>>) -> Vec<(vec<'a, T>, vec<'a, T>)> {
    lhs.iter().zip(rhs.iter()).map(|(a, b)| (a.clone(), b.clone())).collect()
}

#[requires(l.len() > 0 && r.len() > 0)]
fn all_vecs_eq_len<'a, const T: usize>(l: &Vec<vec<'a, T>>, r: &Vec<vec<'a, T>>) -> bool {
    l.len() == r.len() && l.iter().zip(r.iter()).all(|(a, b)| a.len() == b.len())
}

#[hax_lib::fstar::options("--z3rlimit 100")]
#[requires(lhs.len() == rhs.len())]
#[ensures(|res| res.len() >= 0 && res.len() <= usize::MAX)]
fn add_vec_vec<'a, const T: usize>(lhs: &Vec<vec<'a, T>>, rhs: &Vec<vec<'a, T>>) -> Vec<vec<'a, T>> {
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

#[options("--z3rlimit 100")]
#[requires(lhs.len() >= 0 && lhs.len() <= usize::MAX
        && rhs.len() >= 0 && rhs.len() <= usize::MAX)]
#[ensures(|res| res.len() >= 0 && res.len() <= usize::MAX)]
fn add_scalar_polynomium(lhs: &Polynomium<Scalar>, rhs: &Polynomium<Scalar>) -> Polynomium<Scalar> {
    let min_len = if lhs.len() < rhs.len() { lhs.len() } else { rhs.len() };
    let mut coeffs = vec![];
    for i in 0..min_len {
        coeffs.push(lhs.coeffs[i] + rhs.coeffs[i]);
    }
    Polynomium {
        coeffs: if min_len < lhs.len() {
            extend_from(&coeffs.to_vec(), &lhs.coeffs.to_vec())
        } else if min_len < rhs.len() {
            extend_from(&coeffs.to_vec(), &rhs.coeffs.to_vec())
        } else { coeffs.to_vec() }
    }
}

/// For extending a polynomial of scalars.
fn extend_from(lhs: &Vec<Scalar>, rhs: &Vec<Scalar>) -> Vec<Scalar> {
    let mut res = lhs.clone();
    for i in 0..rhs.len() {
        res.push(rhs[i]);
    }
    res
}

#[options("--z3rlimit 100")]
#[requires(lhs.len() >= 0 && lhs.len() <= usize::MAX
        && rhs.len() >= 0 && rhs.len() <= usize::MAX)]
#[ensures(|res| res.len() >= 0 && res.len() <= usize::MAX)]
fn add_vector_polynomium<'a, const T: usize>(lhs: &Polynomium<vec<'a, T>>, rhs: &Polynomium<vec<'a, T>>) -> Polynomium<vec<'a, T>> {
    let min_len = if lhs.len() < rhs.len() { lhs.len() } else { rhs.len() };
    let coeffs = add_vec_vec(&lhs.coeffs[..min_len].to_vec(), &rhs.coeffs[..min_len].to_vec());
    i + j > usize::MAX ? overflow
    Polynomium {
        coeffs: if min_len < lhs.len() {
            extend_from_vec(&coeffs, &lhs.coeffs)
        } else if min_len < rhs.len() {
            extend_from_vec(&coeffs, &rhs.coeffs)
        } else { coeffs }
    }
}

/// The same but with a vector of vectors
fn extend_from_vec<'a, const T: usize>(lhs: &Vec<vec<'a, T>>, rhs: &Vec<vec<'a, T>>) -> Vec<vec<'a, T>> {
    let mut res = lhs.clone();
    for i in 0..rhs.len() {
        res.push(rhs[i].clone());
    }
    res
}

/// A simple, O(n²) algorithm for multiplying polynomials together.
#[options("--z3rlimit 100")]
#[requires(l.len() >= 0 && l.len() <= usize::MAX
        && r.len() >= 0 && r.len() <= usize::MAX)]
#[ensures(|res| res.len() >= 0 && res.len() <= usize::MAX)]
fn simple_polynomial_mul(l: &Polynomium<Scalar>, r: &Polynomium<Scalar>) -> Polynomium<Scalar> {
    if l.coeffs.is_empty() || r.coeffs.is_empty() {
        return Polynomium { coeffs: vec![] };
    }

    let min_len = if l.len() < r.len() { l.len() } else { r.len() };
    let mut coeffs = vec![];

    for i in 0..min_len {
        let sum = r.coeffs.iter().fold(Scalar::ZERO, |acc, e| acc + e.clone() * l.coeffs[i]);
        coeffs.push(sum);
    }

    if min_len == l.len() {
        for i in min_len..r.len() {
            let sum = l.coeffs.iter().fold(Scalar::ZERO, |acc, e| acc + e.clone() * r.coeffs[i]);
            coeffs.push(sum);
        }
    } else if min_len == r.len() {
        for i in min_len..l.len() {
            let sum = r.coeffs.iter().fold(Scalar::ZERO, |acc, e| acc + e.clone() * l.coeffs[i]);
            coeffs.push(sum);
        }
    }

    Polynomium { coeffs }
}

fn simple_vector_polynomial_mul<'a, const T: usize>(l: &Polynomium<vec<'a, T>>, r: &Polynomium<vec<'a, T>>) -> Polynomium<Scalar> {
    if l.coeffs.is_empty() || r.coeffs.is_empty() {
        return Polynomium { coeffs: vec![] };
    }

    let min_len = if l.len() < r.len() { l.len() } else { r.len() };
    let mut coeffs = vec![];

    for i in min_len..l.len() {
        let sum = r.coeffs.iter().fold(Scalar::ZERO, |acc, e| acc + inner_prod_scalars(e, &l.coeffs[i]));
        coeffs.push(sum);
    }

    if min_len == l.len() {
        for i in min_len..r.len() {
            let sum = l.coeffs.iter().fold(Scalar::ZERO, |acc, e| acc + inner_prod_scalars(e, &r.coeffs[i]));
            coeffs.push(sum);
        }
    } else if min_len == r.len() {
        for i in min_len..l.len() {
            let sum = r.coeffs.iter().fold(Scalar::ZERO, |acc, e| acc + inner_prod_scalars(e, &l.coeffs[i]));
            coeffs.push(sum);
        }
    }

    Polynomium { coeffs }
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
