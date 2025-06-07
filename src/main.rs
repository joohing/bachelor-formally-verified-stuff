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

#[exclude()]
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

#[hax_lib::fstar::options("--z3rlimit 100")]
#[requires(lhs.len() == rhs.len())]
#[ensures(|res| res.len() >= 0 && res.len() <= usize::MAX)]
fn add_vec<'a, const T: usize>(lhs: &vec<'a, T>, rhs: &vec<'a, T>) -> vec<'a, T> {
    let mut res = [Scalar::ZERO; T];
    for i in 0..T { res[i] = lhs[i].clone() + rhs[i].clone(); }
    res
}

#[requires(lhs.iter().zip(rhs.iter()).all(|(a, b)| a.len() == b.len()))]
#[hax_lib::fstar::options("--z3rlimit 100")]
fn test2<'a, const T: usize>(lhs: Vec<vec<'a, T>>, rhs: Vec<vec<'a, T>>) -> Vec<vec<'a, T>> {
    let zipped = get_zipped(lhs, rhs);
    let summed = get_summed(zipped);
    vec![]
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

/*
#[hax_lib::fstar::options("--z3rlimit 100")]
#[requires(lhs.len() == rhs.len())]
#[ensures(|res| res.len() >= 0 && res.len() <= usize::MAX)]
fn sub_vec<'a, const T: usize>(lhs: &vec<'a, T>, rhs: &vec<'a, T>) -> vec<'a, T> {
    let mut res = &[Scalar::ZERO; T];
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
    let coeffs = add_vec(&lhs.coeffs[..min_len].to_vec(), &rhs.coeffs[..min_len].to_vec());
    Polynomium {
        coeffs: if min_len < lhs.len() {
            extend_from(&coeffs, &lhs.coeffs)
        } else if min_len < rhs.len() {
            extend_from(&coeffs, &rhs.coeffs)
        } else { coeffs }
    }
}

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
#[exclude()]
fn add_vector_polynomium<'a>(lhs: &Polynomium<vec<'a>>, rhs: &Polynomium<vec<'a>>) -> Polynomium<vec<'a>> {
    let min_len = if lhs.len() < rhs.len() { lhs.len() } else { rhs.len() };
    let coeffs = add_vec_vec(&lhs.coeffs[..min_len].to_vec(), &rhs.coeffs[..min_len].to_vec());
    Polynomium {
        coeffs: if min_len < lhs.len() {
            extend_from_vec(&coeffs, &lhs.coeffs)
        } else if min_len < rhs.len() {
            extend_from_vec(&coeffs, &rhs.coeffs)
        } else { coeffs }
    }
}

/// The same but with a vector of vectors
fn extend_from_vec<'a>(lhs: &Vec<vec<'a>>, rhs: &Vec<vec<'a>>) -> Vec<vec<'a>> {
    let mut res = lhs.clone();
    for i in 0..rhs.len() {
        res.push(rhs[i].clone());
    }
    res
}
*/
