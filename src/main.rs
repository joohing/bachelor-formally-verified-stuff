#![allow(non_camel_case_types)]
#![allow(unused_imports)]
#![allow(unused_assignments)]

mod polynomium;
mod linalg;
mod convert;

use hax_lib::{requires, exclude, attributes, ensures, fstar, fstar::options};
use crate::{polynomium::*, linalg::*, convert::*};

const PRIME: u128 = 123456789;

type vec<'a, const T: usize> = [Scalar; T];

fn main() {
    let _1 = Scalar { v: 1 };
    let _2 = Scalar { v: 2 };
    let _3 = Scalar { v: 3 };
    let _4 = Scalar { v: 4 };
    let _5 = Scalar { v: 5 };
    let _6 = Scalar { v: 6 };
    let l: &vec<'static, 3> = &[_1, _2, _3];
    let r: &vec<'static, 3> = &[_1, _2, _3];
    let _ = add_vec(&l, &r);
}

#[derive(Copy, Clone, PartialEq, Debug)]
#[attributes]
struct Scalar {
    #[refine(v < PRIME)]
    v: u128,
}

impl Scalar {
    const ZERO: Scalar = Scalar { v: 0 };

    fn from(n: u128) -> Self {
        Self { v: (n % PRIME) }
    }
}

impl std::ops::Add for Scalar {
    type Output = Self;
    fn add(self, rhs: Self) -> Self::Output {
        Self { v: (self.v + rhs.v) % PRIME }
    }
}

impl std::ops::Sub for Scalar {
    type Output = Self;
    fn sub(self, rhs: Self) -> Self::Output {
        Self { v: ((self.v + PRIME) - rhs.v) % PRIME }
    }
}

impl std::ops::Mul for Scalar {
    type Output = Self;
    fn mul(self, rhs: Self) -> Self::Output {
        (0..rhs.v).fold(Scalar::ZERO, |acc, _| acc + self + self)
    }
}

pub fn get_summed<'a, const T: usize>(v: Vec<(vec<'a, T>, vec<'a, T>)>) -> Vec<vec<'a, T>> {
    v.iter().map(|(l, r)| add_vec(&l, &r)).collect()
}

pub fn get_zipped<'a, const T: usize>(lhs: Vec<vec<'a, T>>, rhs: Vec<vec<'a, T>>) -> Vec<(vec<'a, T>, vec<'a, T>)> {
    lhs.iter().zip(rhs.iter()).map(|(a, b)| (a.clone(), b.clone())).collect()
}

#[cfg(test)]
mod tests {
    use crate::{vec, Scalar};
    use crate::polynomium::*;
    use crate::{convert::*, linalg::*};
    use crate::{scalar_vec, scalar_vec_sized};
    use curve25519_dalek::{constants::RISTRETTO_BASEPOINT_POINT as G, scalar::Scalar};
    use libcrux::{
        digest::{sha3_512, Algorithm},
        drbg::*,
    };
    use quickcheck_macros::quickcheck;

    pub fn vec_to_scalar_vec<T>(v: Vec<T>) -> Vec<Scalar> where u128: From<T> {
        let mut res = vec![];
        for e in v {
            res.push(Scalar::from(u128::from(e)));
        }
        res
    }

    /// Random vector of scalars, sized 
    pub fn random_vec_sized<'a, const T: usize>() -> vec<'a, T> {
        let mut rng = Drbg::new(Algorithm::Sha512).unwrap();
        let mut v = new_zero_slice();
        for i in 0..T {
            let num = rng.next_u32();
            v[i] = Scalar::from(num);
        }
        v
    }

    /// Random vector of scalars 
    pub fn random_vec<T>(n: T) -> Vec<Scalar> where usize: From<T>{
        let mut rng = Drbg::new(Algorithm::Sha512).unwrap();
        let n = usize::from(n);
        let mut v = Vec::with_capacity(n);
        for _ in 0..n {
            let num = rng.next_u32();
            v.push(Scalar::from(num));
        }
        v
    }

    #[test]
    /// Tests the trim method for scalar polynomiums.
    fn test_polynomium_trim() {
        let p = Polynomium { coeffs: scalar_vec![1, 0, 0, 2, 0, 0, 3, 0, 0] };
        let res = p.trim();
        let exp = Polynomium { coeffs: scalar_vec![1, 0, 0, 2, 0, 0, 3] };
        assert_eq!(res, exp);
    }

    #[test]
    /// Tests the trim method for scalar polynomiums.
    fn test_vector_polynomium_trim() {
        let p: Polynomium<vec<'static, 9>> = Polynomium {
            coeffs: vec![
                scalar_vec_sized![1, 0, 0],
                scalar_vec_sized![0, 0, 0],
                scalar_vec_sized![0, 0, 0],
                scalar_vec_sized![2, 0, 0],
                scalar_vec_sized![0, 0, 0],
                scalar_vec_sized![0, 0, 0],
                scalar_vec_sized![0, 0, 3],
                scalar_vec_sized![0, 0, 0],
                scalar_vec_sized![0, 0, 0]
            ]
        };
        let res = p.trim();
        let exp = Polynomium {
            coeffs: vec![
                scalar_vec_sized![1, 0, 0],
                scalar_vec_sized![0, 0, 0],
                scalar_vec_sized![0, 0, 0],
                scalar_vec_sized![2, 0, 0],
                scalar_vec_sized![0, 0, 0],
                scalar_vec_sized![0, 0, 0],
                scalar_vec_sized![0, 0, 3]
            ]
        };
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

        let l_x: vec<'static, { cl.len() }> = l.clone().eval(x);
        let r_x: vec<'static, { cl.len() }> = r.clone().eval(x);
        let t_x: vec<'static, { cl.len() }> = t.clone().eval(x);

        assert_eq!(t_x, l_x * r_x);
    }

    #[quickcheck]
    /// Test multiplication of vector polynomials.
    fn test_vector_polynomial_multiplication<'a, const T: usize>(m: u128, n: u128, i: u128) {
        let m = m % 30;
        let n = n % 30;
        let i = i % 40;

        let cl: Vec<vec<'a, { T }>> = (0..m+1).map(|_| random_vec_sized()).collect();
        let cr: Vec<vec<'a, { T }>> = (0..n+1).map(|_| random_vec_sized()).collect();

        let l = Polynomium::new_from_vec(cl);
        let r = Polynomium::new_from_vec(cr);

        let t = l.clone() * r.clone();
        let x = Scalar::from(2 as u128);

        let l_x = l.clone().eval(x);
        let r_x = r.clone().eval(x);
        let t_x = t.clone().eval(x);

        let res = inner_prod_scalars(&l_x, &r_x);
        assert_eq!(t_x, res);
    }

    #[quickcheck]
    /// Tests the trim method for scalar polynomiums.
    fn test_polynomium_trims(n: u128, i: u128) {
        let n = n % 20;
        let i = i % 20;

        let c: Vec<vec<'static, { T }>> = (0..n+1).map(|_| random_vec(i as usize)).collect();

        let p = Polynomium::new_from_vec(c);
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

        let pm = Polynomium::new_from_scalar(&cm);
        let pn = Polynomium::new_from_scalar(&cn);
        let po = Polynomium::new_from_scalar(&co);

        assert_eq!((pm.clone() + pn.clone()) + po.clone(), pm + (pn + po))
    }

    #[quickcheck]
    /// Test for associativy of vector polynomials under addition
    fn test_polynomial_vec_associativity(m:u128, n:u128, o:u128, i: u128) {
        let i = i % 10;
        let m = m % 5;
        let n = n % 10;
        let o = o % 8;

        let cm: Vec<vec<'static, { T }>> = (0..=m).map(|_| random_vec(i as usize)).collect();
        let co: Vec<vec<'static, { T }>> = (0..=o).map(|_| random_vec(i as usize)).collect();
        let cn: Vec<vec<'static, { T }>> = (0..=n).map(|_| random_vec(i as usize)).collect();

        let pm = Polynomium::new_from_vec(cm).trim();
        let pn = Polynomium::new_from_vec(cn).trim();
        let po = Polynomium::new_from_vec(co).trim();

        assert_eq!((pm.clone() + pn.clone()) + po.clone(), pm + (pn + po))
    }
    #[quickcheck]
    /// Test for associativy of polynomials under addition
    fn test_polynomial_commutativity(m: u128, p: u128) {
        let m = m % 10;
        let p = p % 10;

        let cm: Vec<Scalar> = random_vec(p as usize);
        let cp: Vec<Scalar> = random_vec(p as usize);

        let pm = Polynomium::new_from_scalar(&cm);
        let pp = Polynomium::new_from_scalar(&cp);

        assert_eq!(pm.clone() + pp.clone(), pp + pm)
    }
    #[quickcheck]
    /// Test for associativy of vector polynomials under addition
    fn test_polynomial_vec_commutativity(m:u128, n:u128, o:u128, i: u128) {
        let i = i % 10;
        let m = m % 5;
        let o = o % 8;

        let cm: Vec<vec<'static, { T }>> = (0..=m).map(|_| random_vec(i as usize)).collect();
        let co: Vec<vec<'static, { T }>> = (0..=o).map(|_| random_vec(i as usize)).collect();

        let pm = Polynomium::new_from_vec(cm).trim();
        let po = Polynomium::new_from_vec(co).trim();

        assert_eq!(pm.clone() + po.clone(), po + pm)
    }

    #[quickcheck]
    /// Test for identity element, for polynomials this is simply the polynomial: f(x)=0
    fn test_polynomial_identity_element(m: u128, p: u128, i: u128) {
        let m = m % 3;
        let p = p % 3;
        let i = i % 4;

        let cm: Vec<Scalar> = random_vec(p as usize);
        let cp: Vec<vec<'static, { T }>> = (0..=p).map(|_| random_vec_sized()).collect();

        let pm = Polynomium::new_from_scalar(&cm);
        let pp = Polynomium::new_from_vec(cp);
        let id = Polynomium::new_from_scalar(&vec![Scalar::ZERO]);
        let idv = Polynomium::new_from_vec(vec![new_zero_slice(); i as usize]);

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
            im[i] = im[i] - cm[i];
        }
        let pm = Polynomium::new_from_scalar(&cm);
        let pi = Polynomium::new_from_scalar(&im);
        assert_eq!((pm.clone() + pi.clone()).trim(), Polynomium::new_from_scalar(&vec![Scalar::ZERO]));
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
        let cvm: Vec<vec<'static, { T }>> = (0..=m).map(|_| random_vec_sized()).collect();
        let cvp: Vec<vec<'static, { T }>> = (0..=p).map(|_| random_vec_sized()).collect();
        let cvn: Vec<vec<'static, { T }>> = (0..=n).map(|_| random_vec_sized()).collect();

        let pm = Polynomium::new_from_scalar(&cm);
        let pp = Polynomium::new_from_scalar(&cp);
        let pn = Polynomium::new_from_scalar(&cn);
        let pvm = Polynomium::new_from_vec(cvm);
        let pvp = Polynomium::new_from_vec(cvp);
        let pvn = Polynomium::new_from_vec(cvn);

        assert_eq!(((pm.clone() * pp.clone()) * pn.clone()).trim(), (pm.clone() * (pp.clone() * pn.clone())).trim());
        //assert_eq!(((pvm.clone() * pvp.clone()) * pvn.clone()).trim(), pvm.clone() * (pvp.clone() * pvn.clone()));
    }

    #[quickcheck]
    /// Test for multiplicative identity element, for polynomials this is simply the polynomial: f(x)=1
    fn test_polynomial_multiplicative_identity<'a, const T: usize>(m: u128, p: u128, i: u128) {
        let m = m % 3;
        let p = p % 3;
        let i = i % 4;

        let cm: Vec<Scalar> = random_vec(p as usize);
        let cp: Vec<vec<'static, { T }>> = (0..=p).map(|_| random_vec_sized()).collect();

        let pm = Polynomium::new_from_scalar(&cm);
        let pp = Polynomium::new_from_vec(cp);
        let id = Polynomium::new_from_scalar(&vec![Scalar::from(1u128)]);
        let idv: Polynomium<vec<'static, T>> = Polynomium::new_from_vec(vec![new_zero_slice(); i as usize]);

        assert_eq!((pm.clone() * id).trim(), pm.trim());
        //assert_eq!((pp.clone() * idv).trim(), pp.trim());
    }
}
