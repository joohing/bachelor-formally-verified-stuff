#![allow(non_camel_case_types)]
#![allow(unused_imports)]

use hax_lib::{requires, exclude, attributes, ensures, fstar, fstar::options};
use crate::{*, linalg::*};

#[derive(Clone, Debug, PartialEq)]
pub struct Polynomium<T> {
    pub coeffs: Vec<T>,
}

/// Makes it so that a polynomial can be trimmed
pub trait Trim<T> {
    fn trim(&self) -> T;
}

/// Makes it so that a polynomial can be evaluated
pub trait Eval<T> {
    fn eval(&self, s: Scalar) -> T;
}

impl std::ops::Mul for Polynomium<Scalar> {
    type Output = Self;
    fn mul(self, rhs: Self) -> Self::Output {
        jonamul(&self, &rhs)
    }
}

impl std::ops::Add for Polynomium<Scalar> {
    type Output = Self;
    fn add(self, rhs: Self) -> Self::Output {
        add_scalar_polynomium(&self, &rhs)
    }
}

impl std::ops::Sub for Polynomium<Scalar> {
    type Output = Self;
    fn sub(self, rhs: Self) -> Self::Output {
        sub_scalar_polynomium(&self, &rhs)
    }
}

impl<'a, const T: usize> std::ops::Mul for Polynomium<vec<'a, T>> {
    type Output = Polynomium<Scalar>;
    fn mul(self, rhs: Self) -> Self::Output {
        jonamul_vec(&self, &rhs)
    }
}

impl<'a, const T: usize> std::ops::Add for Polynomium<vec<'a, T>> {
    type Output = Self;
    fn add(self, rhs: Self) -> Self::Output {
        add_vector_polynomium(&self, &rhs)
    }
}

pub fn new_zero_slice<'a, const T: usize>() -> vec<'a, T> { [Scalar::ZERO; T] }

impl Polynomium<Scalar> {
    pub fn len(&self) -> usize { self.coeffs.len() }

    /// In order to have all inputs give a valid group element we make it zero if
    /// the given vector is empty.
    pub fn new_from_scalar(v: &Vec<Scalar>) -> Self {
        Self {
            coeffs: if v.is_empty() {
                vec![Scalar::from(0u128)]
            } else {
                v.to_vec()
            }
        }
    }
}

impl Trim<Polynomium<Scalar>> for Polynomium<Scalar> {
    fn trim(&self) -> Self {
        Polynomium {
            coeffs: {
                let res = trim(&self.coeffs);
                if res.is_empty() { vec![Scalar::ZERO] } else { res }
            }
        }
    }
}

impl Eval<Scalar> for Polynomium<Scalar> {
    fn eval(&self, x: Scalar) -> Scalar {
        evaluate_polynomial(self.coeffs.clone(), x)
    }
}

impl<'a, const T: usize> Polynomium<vec<'_, T>> {
    fn len(&self) -> usize { self.coeffs.len() }

    /// In order to have all inputs give a valid group element we make it zero if
    /// the given vector is empty.
    pub fn new_from_vec(v: Vec<vec<'a, T>>) -> Self {
        Self {
            coeffs: if v.is_empty() {
                vec![new_zero_slice()]
            } else {
                v
            }
        }
    }
}

impl<'a, const T: usize> Trim<Polynomium<vec<'a, T>>> for Polynomium<vec<'a, T>> {
    /// Remove all trailing zero vectors from the polynomium's coefficients
    fn trim(&self) -> Self {
        Polynomium {
            coeffs: {
                let res = trim_vec(&self.coeffs);
                if res.is_empty() { vec![new_zero_slice()] } else { res }
            }
        }
    }
}

impl<'a, const T: usize> Eval<vec<'a, T>> for Polynomium<vec<'a, T>> {
    fn eval(&self, x: Scalar) -> vec<'a, T> {
        evaluate_vector_polynomial(self.coeffs.clone(), x)
    }
}

fn trim(v: &Vec<Scalar>) -> Vec<Scalar> {
    let filtered_rev = v.iter().rev();
    let mut res = vec![];
    let mut is_trailing = true;
    for e in filtered_rev {
        is_trailing = is_trailing && *e == Scalar::ZERO;
        if !is_trailing {
            res.push(e.clone());
        }
    }
    res.iter().rev().map(|e| e.clone()).collect()
}

fn trim_vec<'a, const T: usize>(v: &Vec<vec<'a, T>>) -> Vec<vec<'a, T>> {
    let filtered_rev = v.iter().rev();
    let mut res = vec![];
    let mut is_trailing = true;
    for e in filtered_rev {
        is_trailing = is_trailing && e.iter().all(|e| *e == Scalar::ZERO);
        if !is_trailing {
            res.push(e.clone());
        }
    }
    res.iter().rev().map(|e| e.clone()).collect()
}

/// Evaluates the polynomial given by a[0] + a[1]u + a[2]u^2 ...
pub fn evaluate_polynomial(a: Vec<Scalar>, u: Scalar) -> Scalar {
    let mut result = Scalar::ZERO;
    for &coef in a.iter().rev() {
        result = u * result + coef;
    }
    result
}

pub fn evaluate_vector_polynomial<'a, const T: usize>(a: Vec<vec<'a, T>>, u: Scalar) -> vec<'a, T> {
    if a.is_empty() { return new_zero_slice(); }
    let mut result = new_zero_slice();
    for coef in a.iter().rev() {
        result = result.mul_vec_scalar(u).add_vec(&coef);
    }
    result
}

// -------- NOT CORRECT :( ----------
// fn simple_vector_polynomial_mul<'a, const T: usize>(l: &Polynomium<vec<'a, T>>, r: &Polynomium<vec<'a, T>>) -> Polynomium<Scalar> {
//     if l.coeffs.is_empty() || r.coeffs.is_empty() {
//         return Polynomium { coeffs: vec![] };
//     }

//     let min_len = if l.len() < r.len() { l.len() } else { r.len() };
//     let mut coeffs = vec![];

//     for i in min_len..l.len() {
//         let sum = r.coeffs.iter().fold(Scalar::ZERO, |acc, e| acc + inner_prod_scalars(e, &l.coeffs[i]));
//         coeffs.push(sum);
//     }

//     if min_len == l.len() {
//         for i in min_len..r.len() {
//             let sum = l.coeffs.iter().fold(Scalar::ZERO, |acc, e| acc + inner_prod_scalars(e, &r.coeffs[i]));
//             coeffs.push(sum);
//         }
//     } else if min_len == r.len() {
//         for i in min_len..l.len() {
//             let sum = r.coeffs.iter().fold(Scalar::ZERO, |acc, e| acc + inner_prod_scalars(e, &l.coeffs[i]));
//             coeffs.push(sum);
//         }
//     }

//     Polynomium { coeffs }
// }

// ------- NOT CORRECT :( -------
// /// A simple, O(n²) algorithm for multiplying polynomials together.
// #[options("--z3rlimit 100")]
// #[requires(l.len() >= 0 && l.len() <= usize::MAX
//         && r.len() >= 0 && r.len() <= usize::MAX)]
// #[ensures(|res| res.len() >= 0 && res.len() <= usize::MAX)]
// fn simple_polynomial_mul(l: &Polynomium<Scalar>, r: &Polynomium<Scalar>) -> Polynomium<Scalar> {
//     if l.coeffs.is_empty() || r.coeffs.is_empty() {
//         return Polynomium { coeffs: vec![Scalar::ZERO] };
//     }

//     let min_len = if l.len() < r.len() { l.len() } else { r.len() };
//     let max_len = if l.len() > r.len() { l.len() } else { r.len() };
//     let mut coeffs = Vec::with_capacity(max_len);

//     for i in 0..min_len {
//         let sum = r.coeffs.iter().fold(Scalar::ZERO, |acc, e| acc + *e * l.coeffs[i]);
//         coeffs.push(sum);
//     }

//     if min_len == l.len() {
//         for i in min_len..r.len() {
//             let sum = l.coeffs.iter().fold(Scalar::ZERO, |acc, e| acc + *e * r.coeffs[i]);
//             coeffs.push(sum);
//         }
//     } else if min_len == r.len() {
//         for i in min_len..l.len() {
//             let sum = r.coeffs.iter().fold(Scalar::ZERO, |acc, e| acc + *e * l.coeffs[i]);
//             coeffs.push(sum);
//         }
//     }

//     Polynomium { coeffs }
// }

/// The Johnnyboi algorithm for multiplying polynomials. FORMALLY VERIFIED
fn jonamul(lhs: &Polynomium<Scalar>, rhs: &Polynomium<Scalar>) -> Polynomium<Scalar> {
    let min_len = min(lhs.len(), rhs.len());
    let max_len = max(lhs.len(), rhs.len());
    let mut max_ptr = 0;
    let mut lower_bound = 0;
    let mut coeffs = vec![];

    // 3 parts; first add cross products until min_len is reached
    for i in 1..min_len {
        let res = cross_product(&lhs.coeffs[..i].to_vec(), &rhs.coeffs[..i].to_vec());
        coeffs.push(res);
        max_ptr = i;
    }

    let largest = if rhs.len() > lhs.len() { rhs } else { lhs };
    let smallest = if lhs.len() < rhs.len() { lhs } else { rhs };
    let mut last_in_min = Scalar::ZERO;
    let mut remainder = vec![];
    let mut curr_win = lower_bound..min((lower_bound as u128) + (min_len as u128), rhs.len() as u128) as usize;

    // Then add cross products while increasing the lower bound
    for i in 0..largest.coeffs.len() {
        lower_bound = i;
        remainder = largest.coeffs[i..].to_vec();
        curr_win = i..largest.coeffs.len();
        let largest_slice = &largest.coeffs[curr_win].to_vec();
        let smallest_slice = &smallest.coeffs[..].to_vec();
        let res = cross_product(smallest_slice, largest_slice);
        println!("mid: {:?}", res);
        coeffs.push(res);
    }

    // Quick sidequest to find the last entry in the smallest one
    for e in &smallest.coeffs {
        last_in_min = *e;
    }

    if min_len == max_len { return Polynomium { coeffs };}

    // Then add products between smallest.last() and largest[...]
    for i in 1..remainder.len() {
        let res = last_in_min * remainder[i];
        coeffs.push(res);
    }

    Polynomium { coeffs }
}

/// Returns [1, 2, 3] x [1, 2, 3] => 1 * 3 + 2 * 2 + 3 * 1
fn cross_product(l: &Vec<Scalar>, r: &Vec<Scalar>) -> Scalar {
    l.iter().rev().zip(r.iter()).fold(Scalar::ZERO, |acc, (&a, &b)| acc + a * b)
}

/// The Johnnyboi algorithm for multiplying polynomials. FORMALLY VERIFIED
fn jonamul_vec<'a, const T: usize>(lhs: &Polynomium<vec<'a, T>>, rhs: &Polynomium<vec<'a, T>>) -> Polynomium<Scalar> {
    let min_len = min(lhs.len(), rhs.len());
    let max_len = max(lhs.len(), rhs.len());
    let mut max_ptr = 0;
    let mut lower_bound = 0;
    let mut coeffs = vec![];

    // 3 parts; first add cross products until min_len is reached
    for i in 1..min_len {
        let res = cross_product_vec(&lhs.coeffs[..i].to_vec(), &rhs.coeffs[..i].to_vec());
        coeffs.push(res);
        max_ptr = i;
    }

    let largest = if rhs.len() > lhs.len() { rhs } else { lhs };
    let smallest = if lhs.len() < rhs.len() { lhs } else { rhs };
    let mut last_in_min = new_zero_slice();
    let mut remainder = vec![];
    let mut curr_win = lower_bound..min((lower_bound as u128) + (min_len as u128), rhs.len() as u128) as usize;

    // Then add cross products while increasing the lower bound
    for i in 0..largest.coeffs.len() {
        lower_bound = i;
        remainder = largest.coeffs[i..].to_vec();
        curr_win = i..largest.coeffs.len();
        let largest_slice = &largest.coeffs[curr_win].to_vec();
        let smallest_slice = &smallest.coeffs[..].to_vec();
        let res = cross_product_vec(smallest_slice, largest_slice);
        println!("mid: {:?}", res);
        coeffs.push(res);
    }

    // Quick sidequest to find the last entry in the smallest one
    for e in &smallest.coeffs {
        last_in_min = *e;
    }

    if min_len == max_len { return Polynomium { coeffs };}

    // Then add products between smallest.last() and largest[...]
    for i in 1..remainder.len() {
        let res = inner_prod_scalars(&last_in_min, &remainder[i]);
        coeffs.push(res);
    }

    Polynomium { coeffs }
}

/// Returns [1, 2, 3] x [1, 2, 3] => 1 * 3 + 2 * 2 + 3 * 1
fn cross_product_vec<'a, const T: usize>(l: &Vec<vec<'a, T>>, r: &Vec<vec<'a, T>>) -> Scalar {
    l.iter().rev().zip(r.iter()).fold(Scalar::ZERO, |acc, (&a, &b)| acc + inner_prod_scalars(&a, &b))
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

#[options("--z3rlimit 100")]
#[requires(lhs.len() >= 0 && lhs.len() <= usize::MAX
        && rhs.len() >= 0 && rhs.len() <= usize::MAX)]
#[ensures(|res| res.len() >= 0 && res.len() <= usize::MAX)]
fn sub_scalar_polynomium(lhs: &Polynomium<Scalar>, rhs: &Polynomium<Scalar>) -> Polynomium<Scalar> {
    let min_len = if lhs.len() < rhs.len() { lhs.len() } else { rhs.len() };
    let mut coeffs = vec![];
    for i in 0..min_len {
        coeffs.push(lhs.coeffs[i] - rhs.coeffs[i]);
    }
    Polynomium {
        coeffs: if min_len < lhs.len() {
            extend_from_neg(&coeffs.to_vec(), &lhs.coeffs.to_vec())
        } else if min_len < rhs.len() {
            extend_from_neg(&coeffs.to_vec(), &rhs.coeffs.to_vec())
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

/// For extending a polynomial of scalars with the negation.
fn extend_from_neg(lhs: &Vec<Scalar>, rhs: &Vec<Scalar>) -> Vec<Scalar> {
    let mut res = lhs.clone();
    for i in 0..rhs.len() {
        res.push(Scalar::ZERO - rhs[i]);
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

