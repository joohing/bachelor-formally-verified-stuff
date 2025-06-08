#![allow(non_camel_case_types)]
#![allow(unused_imports)]

use hax_lib::{requires, exclude, attributes, ensures, fstar, fstar::options};
use crate::{*, linalg::*};

#[derive(Clone, Debug, PartialEq)]
pub struct Polynomium<T> {
    pub coeffs: Vec<T>,
}

impl std::ops::Mul for Polynomium<Scalar> {
    type Output = Self;
    fn mul(self, rhs: Self) -> Self::Output {
        simple_polynomial_mul(&self, &rhs)
    }
}

impl std::ops::Add for Polynomium<Scalar> {
    type Output = Self;
    fn add(self, rhs: Self) -> Self::Output {
        add_scalar_polynomium(&self, &rhs)
    }
}

impl<'a, const T: usize> std::ops::Mul for Polynomium<vec<'a, T>> {
    type Output = Polynomium<Scalar>;
    fn mul(self, rhs: Self) -> Self::Output {
        simple_vector_polynomial_mul(&self, &rhs)
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
    fn new_from_scalar(v: &Vec<Scalar>) -> Self {
        Self {
            coeffs: if v.is_empty() {
                vec![Scalar::from(0u128)]
            } else {
                v.to_vec()
            }
        }
    }

    pub fn trim(&self) -> Self {
        Polynomium {
            coeffs: {
                let res = trim_rec(&self.coeffs);
                if res.is_empty() { vec![Scalar::ZERO] } else { res }
            }
        }
    }

    pub fn eval(self, x: Scalar) -> Scalar {
        evaluate_polynomial(self.coeffs, x)
    }
}

impl<'a, const T: usize> Polynomium<vec<'_, T>> {
    pub fn len(&self) -> usize { self.coeffs.len() }

    /// In order to have all inputs give a valid group element we make it zero if
    /// the given vector is empty.
    fn new_from_vec(v: Vec<vec<'a, T>>) -> Self {
        Self {
            coeffs: if v.is_empty() {
                vec![new_zero_slice()]
            } else {
                v
            }
        }
    }

    /// Remove all trailing zero vectors from the polynomium's coefficients
    pub fn trim(&self) -> Self {
        Polynomium {
            coeffs: {
                let res = trim_vec_rec(&self.coeffs);
                if res.is_empty() { vec![new_zero_slice()] } else { res }
            }
        }
    }

    pub fn eval(self, x: Scalar) -> vec<'a, T> {
        evaluate_vector_polynomial(self.coeffs, x)
    }
}

/// Recursive trim trailing zeroes.
fn trim_rec(v: &Vec<Scalar>) -> Vec<Scalar> {
    let filtered_rev = v.iter().rev();
    let mut res = vec![];
    let mut is_trailing = true;
    for e in filtered_rev {
        if !(is_trailing && *e == Scalar::ZERO) {
            res.push(e.clone());
        } else {
            is_trailing = false;
        }
    }
    res
}

fn trim_vec_rec<'a, const T: usize>(v: &Vec<vec<'a, T>>) -> Vec<vec<'a, T>> {
    let filtered_rev = v.iter().rev();
    let mut res = vec![];
    let mut is_trailing = true;
    for e in filtered_rev {
        if !(is_trailing && e.iter().all(|e| *e == Scalar::ZERO)) {
            res.push(e.clone());
        } else {
            is_trailing = false;
        }
    }
    res
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

