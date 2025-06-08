#![allow(non_camel_case_types)]
#![allow(unused_imports)]

use hax_lib::{requires, exclude, attributes, ensures, fstar, fstar::options};

const p: u128 = 123456789;

type vec<'a, const T: usize> = [Scalar; T];

#[derive(Clone, Debug, PartialEq)]
pub struct Polynomium<T> {
    pub coeffs: Vec<T>,
}

impl<'a, const T: usize> Polynomium<vec<'_, T>> {
    fn len(&self) -> usize { self.coeffs.len() }

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
}

fn new_zero_slice<'a, const T: usize>() -> vec<'a, T> { [Scalar::ZERO; T] }

impl Polynomium<Scalar> {
    fn len(&self) -> usize { self.coeffs.len() }

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
}

/// Recursive trim trailing zeroes.
fn trim_rec(v: &Vec<Scalar>) -> Vec<Scalar> {
    let filtered_rev = v.iter().rev();
    let mut res = vec![];
    let mut is_trailing = true;
    for e in filtered_rev {
        if !(is_trailing && *e == Scalar::ZERO) {
            res.push(e.clone());
        }
    }
    res
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

#[derive(Copy, Clone, PartialEq)]
#[attributes]
struct Scalar {
    #[refine(v < p)]
    v: u128,
}

impl Scalar {
    const ZERO: Scalar = Scalar { v: 0 };

    fn from(n: u128) -> Self {
        Self { v: (n % p) }
    }
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::pedersen_commitment::*;
    use crate::polynomium::*;
    use crate::{convert::*, linalg::*};
    use curve25519_dalek::{constants::RISTRETTO_BASEPOINT_POINT as G, scalar::Scalar};
    use libcrux::{
        digest::{sha3_512, Algorithm},
        drbg::*,
    };
    use quickcheck_macros::quickcheck;

    #[test]
    /// Tests the trim method for scalar polynomiums.
    fn test_polynomium_trim() {
        let p = Polynomium { coeffs: scalar_vec![1, 0, 0, 2, 0, 0, 3, 0, 0] };
        let res = p.trim();
        let exp = Polynomium { coeffs: scalar_vec![1, 0, 0, 2, 0, 0, 3] };
        println!("res: {}", res);
        println!("exp: {}", exp);
        assert_eq!(res, exp);
    }

    #[test]
    /// Tests the trim method for scalar polynomiums.
    fn test_vector_polynomium_trim() {
        let p = Polynomium {
            coeffs: vec![
                scalar_vec![1, 0, 0],
                scalar_vec![0, 0, 0],
                scalar_vec![0, 0, 0],
                scalar_vec![2, 0, 0],
                scalar_vec![0, 0, 0],
                scalar_vec![0, 0, 0],
                scalar_vec![0, 0, 3],
                scalar_vec![0, 0, 0],
                scalar_vec![0, 0, 0]
            ]
        };
        let res = p.trim();
        let exp = Polynomium {
            coeffs: vec![
                scalar_vec![1, 0, 0],
                scalar_vec![0, 0, 0],
                scalar_vec![0, 0, 0],
                scalar_vec![2, 0, 0],
                scalar_vec![0, 0, 0],
                scalar_vec![0, 0, 0],
                scalar_vec![0, 0, 3]
            ]
        };
        println!("res: {}", res);
        println!("exp: {}", exp);
        assert_eq!(res, exp);
    }

    #[test]
    /// A simple polynomial evaluation test. Coefficients [1, 2, 3], and u = 2.
    /// So p(x) = 1 + 2u + 3u^2, and p(2) = 1 + 4 + 12 = 17
    fn test_simple_polynomial_evaluation() {
        let coeffs = scalar_vec![1, 2, 3];
        let u = Scalar::from(2 as u128);
        let res = evaluate_polynomial(coeffs, u);

        assert_eq!(res, Scalar::from(17u128));
    }

    #[quickcheck]
    /// Test multiplication of scalar polynomials, uses Karatsuba.
    fn test_scalar_polynomial_multiplication(cl: Vec<u128>, cr: Vec<u128>) {
        let cl = vec_to_scalar_vec(cl);
        let cr = vec_to_scalar_vec(cr);

        let l = Polynomium { coeffs: cl };
        let r = Polynomium { coeffs: cr };

        let t = l.clone() * r.clone();
        let x = Scalar::from(2 as u128);

        let l_x = l.clone().eval(x);
        let r_x = r.clone().eval(x);
        let t_x = t.clone().eval(x);

        assert_eq!(t_x, l_x * r_x);
    }

    #[quickcheck]
    /// Test multiplication of vector polynomials.
    fn test_vector_polynomial_multiplication(m: u128, n: u128, i: u128) {
        let m = m % 30;
        let n = n % 30;
        let i = i % 40;

        let cl: Vec<vec> = (0..m+1).map(|_| random_vec(i as usize)).collect();
        let cr: Vec<vec> = (0..n+1).map(|_| random_vec(i as usize)).collect();

        println!("cl len: {}", cl.len());
        println!("cr len: {}", cr.len());

        let l = Polynomium::new_from_vec(cl, Scalar::from(i));
        let r = Polynomium::new_from_vec(cr, Scalar::from(i));

        println!("l: {}", l);
        println!("r: {}", r);

        let t = l.clone() * r.clone();
        let x = Scalar::from(2 as u128);

        println!("t: {}", t);

        let l_x = l.clone().eval(x);
        let r_x = r.clone().eval(x);
        let t_x = t.clone().eval(x);

        let res = inner_prod_scalars(&l_x, &r_x);
        assert_eq!(t_x, res);
    }

    #[quickcheck]
    /// Simple test for comparing the karatsuba method, against the simple implementation
    fn test_karatsuba_versus_simple(m: u128, n: u128, i: u128) {
        let m = m % 30;
        let n = n % 30;
        let i = i % 40;

        let cl: Vec<Vec<Scalar>> = (0..=m).map(|_| random_vec(i as usize)).collect();
        let cr: Vec<Vec<Scalar>> = (0..=n).map(|_| random_vec(i as usize)).collect();

        let l = Polynomium::new_from_vec(cl, Scalar::from(i));
        let r = Polynomium::new_from_vec(cr, Scalar::from(i));

        println!("karatsuba calculation running");
        let karatsuba_result = karatsuba_vector_polynomial_mul(&l, &r);
        println!("Simple calculation running");
        let simple_result = simple_vector_polynomial_mul(&l, &r);

        assert_eq!(simple_result, karatsuba_result.trim());
    }
    #[quickcheck]
    /// Tests the trim method for scalar polynomiums.
    fn test_polynomium_trims(n: u128, i: u128) {
        let n = n % 20;
        let i = i % 20;

        let c: Vec<Vec<Scalar>> = (0..n+1).map(|_| random_vec(i as usize)).collect();

        let p = Polynomium::new_from_vec(c, Scalar::from(i));
        let trimmed = p.clone().trim();

        let c: Vec<Scalar> = random_vec((n+1) as usize);
        for i in c{
            assert_eq!(trimmed.clone().eval(i), p.clone().eval(i));
        }
    }
    #[quickcheck]
    /// Test for associativy of polynomials under addition
    fn test_polynomial_associativity(i: u128, o: u128, p: u128) {
        let i = i % 10;
        let p = p % 10;
        let o = o % 15;

        let cm: Vec<Scalar> = random_vec(i as usize);
        let co: Vec<Scalar> = random_vec(o as usize);
        let cn: Vec<Scalar> = random_vec(p as usize);

        let pm = Polynomium::new_from_scalar(cm);
        let pn = Polynomium::new_from_scalar(cn);
        let po = Polynomium::new_from_scalar(co);

        assert_eq!((pm.clone() + pn.clone()) + po.clone(), pm + (pn + po))
    }
    #[quickcheck]
    /// Test for associativy of vector polynomials under addition
    fn test_polynomial_vec_associativity(m:u128, n:u128, o:u128, i: u128) {
        let i = i % 10;
        let m = m % 5;
        let n = n % 10;
        let o = o % 8;

        let cm: Vec<Vec<Scalar>> = (0..=m).map(|_| random_vec(i as usize)).collect();
        let co: Vec<Vec<Scalar>> = (0..=o).map(|_| random_vec(i as usize)).collect();
        let cn: Vec<Vec<Scalar>> = (0..=n).map(|_| random_vec(i as usize)).collect();

        let pm = Polynomium::new_from_vec(cm, Scalar::from(i)).trim();
        let pn = Polynomium::new_from_vec(cn, Scalar::from(i)).trim();
        let po = Polynomium::new_from_vec(co, Scalar::from(i)).trim();

        assert_eq!((pm.clone() + pn.clone()) + po.clone(), pm + (pn + po))
    }
    #[quickcheck]
    /// Test for associativy of polynomials under addition
    fn test_polynomial_commutativity(m: u128, p: u128) {
        let m = m % 10;
        let p = p % 10;

        let cm: Vec<Scalar> = random_vec(p as usize);
        let cp: Vec<Scalar> = random_vec(p as usize);

        let pm = Polynomium::new_from_scalar(cm);
        let pp = Polynomium::new_from_scalar(cp);

        assert_eq!(pm.clone() + pp.clone(), pp + pm)
    }
    #[quickcheck]
    /// Test for associativy of vector polynomials under addition
    fn test_polynomial_vec_commutativity(m:u128, n:u128, o:u128, i: u128) {
        let i = i % 10;
        let m = m % 5;
        let o = o % 8;

        let cm: Vec<Vec<Scalar>> = (0..=m).map(|_| random_vec(i as usize)).collect();
        let co: Vec<Vec<Scalar>> = (0..=o).map(|_| random_vec(i as usize)).collect();

        let pm = Polynomium::new_from_vec(cm, Scalar::from(i)).trim();
        let po = Polynomium::new_from_vec(co, Scalar::from(i)).trim();

        assert_eq!(pm.clone() + po.clone(), po + pm)
    }
    #[quickcheck]
    /// Test for identity element, for polynomials this is simply the polynomial: f(x)=0
    fn test_polynomial_identity_element(m: u128, p: u128, i: u128) {
        let m = m % 3;
        let p = p % 3;
        let i = i % 4;

        let cm: Vec<Scalar> = random_vec(p as usize);
        let cp: Vec<Vec<Scalar>> = (0..=p).map(|_| random_vec(i as usize)).collect();

        let pm = Polynomium::new_from_scalar(cm);
        let pp = Polynomium::new_from_vec(cp, Scalar::from(i));
        let id = Polynomium::new_from_scalar(vec![Scalar::ZERO]);
        let idv = Polynomium::new_from_vec(vec![vec![Scalar::ZERO]; i as usize], Scalar::from(i));

        assert_eq!(pm.clone() + id, pm);
        assert_eq!((pp.clone() + idv).trim(), pp.trim());
    }
    #[quickcheck]
    /// Test
    fn test_polynomial_inverse_elements(m:u128) {
        let m = m % 10;
        let cm: Vec<Scalar> = random_vec(m as usize);
        let mut im: Vec<Scalar> = vec![Scalar::ZERO; cm.len()];
        for i in 0..cm.len() {
            im[i] -= cm[i];
        }
        let pm = Polynomium::new_from_scalar(cm);
        let pi = Polynomium::new_from_scalar(im);
        assert_eq!((pm.clone() + pi.clone()).trim(), Polynomium::new_from_scalar(vec![Scalar::ZERO]));
    }

    #[quickcheck]
    fn test_polynomial_monoid(m:u128, p: u128, n:u128, i:u128) {
        let m = m % 3;
        let p = p % 3;
        let i = i % 3;
        let n = n % 3;

        let cm: Vec<Scalar> = random_vec(m as usize);
        let cp: Vec<Scalar> = random_vec(p as usize);
        let cn: Vec<Scalar> = random_vec(n as usize);
        let cvm: Vec<Vec<Scalar>> = (0..=m).map(|_| random_vec(i as usize)).collect();
        let cvp: Vec<Vec<Scalar>> = (0..=p).map(|_| random_vec(i as usize)).collect();
        let cvn: Vec<Vec<Scalar>> = (0..=n).map(|_| random_vec(i as usize)).collect();

        let pm = Polynomium::new_from_scalar(cm);
        let pp = Polynomium::new_from_scalar(cp);
        let pn = Polynomium::new_from_scalar(cn);
        let pvm = Polynomium::new_from_vec(cvm, Scalar::from(i));
        let pvp = Polynomium::new_from_vec(cvp, Scalar::from(i));
        let pvn = Polynomium::new_from_vec(cvn, Scalar::from(i));

        assert_eq!(((pm.clone() * pp.clone()) * pn.clone()).trim(), (pm.clone() * (pp.clone() * pn.clone())).trim());
        //assert_eq!(((pvm.clone() * pvp.clone()) * pvn.clone()).trim(), pvm.clone() * (pvp.clone() * pvn.clone()));
    }
    #[quickcheck]
    /// Test for multiplicative identity element, for polynomials this is simply the polynomial: f(x)=1
    fn test_polynomial_multiplicative_identitiy(m: u128, p: u128, i: u128) {
        let m = m % 3;
        let p = p % 3;
        let i = i % 4;

        let cm: Vec<Scalar> = random_vec(p as usize);
        let cp: Vec<Vec<Scalar>> = (0..=p).map(|_| random_vec(i as usize)).collect();

        let pm = Polynomium::new_from_scalar(cm);
        let pp = Polynomium::new_from_vec(cp);
        let id = Polynomium::new_from_scalar(vec![Scalar::from(1 as u32)]);
        let idv = Polynomium::new_from_vec(vec![vec![Scalar::ZERO]; i as usize]);

        assert_eq!((pm.clone() * id).trim(), pm.trim());
        //assert_eq!((pp.clone() * idv).trim(), pp.trim());
    }
}
