#![allow(non_camel_case_types)]
#![allow(unused_imports)]
#![allow(unused_assignments)]
#![allow(unused_variables)]
#![allow(dead_code)]
#![allow(private_interfaces)]

mod polynomium;
mod linalg;
mod convert;
mod scalar_test;

use hax_lib::{requires, exclude, attributes, ensures, fstar, fstar::options};
use crate::{polynomium::*, linalg::*, convert::*};

const PRIME: u128 = 17;

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
    const ONE: Scalar = Scalar { v: 1 };

    fn from(n: u128) -> Self {
        Self { v: (n % PRIME) }
    }

    fn pow(&self, n: u128) -> Self {
        let mut res = Scalar::ONE;
        for _ in 0..n {
            res = res * *self;
        }
        res
    }

    fn invert(&self) -> Self {
        self.pow(PRIME - 2)
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
        (0..rhs.v).fold(Scalar::ZERO, |acc, _| acc + self)
    }
}

impl std::fmt::Display for Scalar {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.v)
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
    use libcrux::{digest::Algorithm, drbg::{Drbg, RngCore}};
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
            v[i] = Scalar::from(u128::from(num));
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
            v.push(Scalar::from(u128::from(num)));
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

    #[test]
    /// Test simple case
    fn test_scalar_simple_polynomial_multiplication() {
        let cl = vec![Scalar::from(1u128), Scalar::from(2u128)];
        let cr = vec![Scalar::from(3u128), Scalar::from(4u128)];
        let res = vec![Scalar::from(3u128), Scalar::from(10u128), Scalar::from(8u128)];

        let l = Polynomium::new_from_scalar(&cl);
        let r = Polynomium::new_from_scalar(&cr);

        let t = l.clone() * r.clone();
        assert_eq!(t, Polynomium { coeffs: res });

        let x = Scalar::from(2 as u128);

        println!("l: {:?}", l);
        println!("r: {:?}", r);
        println!("t: {:?}", t);

        let l_x = l.eval(x);
        let r_x = r.eval(x);
        let t_x = t.eval(x);

        println!("l eval: {:?}", l.eval(x));
        println!("r eval: {:?}", r.eval(x));
        println!("t eval: {:?}", t.eval(x));

        assert_eq!(t_x, l_x * r_x);
    }

    #[test]
    /// Test yet another simple case
    fn test_weird_shape_scalar_polynomial_multiplication() {
        let cl = vec![Scalar::from(15u128)];
        let cr = vec![Scalar::from(1u128), Scalar::from(9u128)];
        let res = vec![Scalar::from(15u128), Scalar::from(16u128)];

        let l = Polynomium::new_from_scalar(&cl);
        let r = Polynomium::new_from_scalar(&cr);

        let t = l.clone() * r.clone();
        assert_eq!(t, Polynomium { coeffs: res });

        let x = Scalar::from(2 as u128);

        println!("l: {:?}", l);
        println!("r: {:?}", r);
        println!("t: {:?}", t);

        let l_x = l.eval(x);
        let r_x = r.eval(x);
        let t_x = t.eval(x);

        println!("l eval: {:?}", l.eval(x));
        println!("r eval: {:?}", r.eval(x));
        println!("t eval: {:?}", t.eval(x));

        // Should be 13
        assert_eq!(t_x, l_x * r_x);
    }

    #[test]
    /// Okay last one i promise
    fn test_another_weird_shape_scalar_polynomial_multiplication() {
        let cl = vec![Scalar::from(3u128), Scalar::from(4u128)];
        let cr = vec![Scalar::from(14u128), Scalar::from(6u128), Scalar::from(7u128)];
        let res = vec![Scalar::from(8u128), Scalar::from(6u128), Scalar::from(11u128), Scalar::from(11u128)];

        let l = Polynomium::new_from_scalar(&cl);
        let r = Polynomium::new_from_scalar(&cr);

        let t = l.clone() * r.clone();
        assert_eq!(t, Polynomium { coeffs: res });

        let x = Scalar::from(2 as u128);

        println!("l: {:?}", l);
        println!("r: {:?}", r);
        println!("t: {:?}", t);

        let l_x = l.eval(x);
        let r_x = r.eval(x);
        let t_x = t.eval(x);

        println!("l eval: {:?}", l.eval(x));
        println!("r eval: {:?}", r.eval(x));
        println!("t eval: {:?}", t.eval(x));

        // Should be 13
        assert_eq!(t_x, l_x * r_x);
    }

    #[test]
    /// Another edge case
    fn test_another_another_weird_shape_scalar_polynomial_multiplication() {
        let cl = vec![Scalar { v: 11 }, Scalar { v: 8 }];
        let cr = vec![Scalar { v: 14 }, Scalar { v: 6 }, Scalar { v: 8 }, Scalar { v: 6 }, Scalar { v: 12 }, Scalar { v: 3 }, Scalar { v: 5 }, Scalar { v: 11 }];

        // 154 + 178 x + 136 x^2 + 130 x^3 + 180 x^4 + 129 x^5 + 79 x^6 + 161 x^7 + 88 x^8
        let res = vec![
            Scalar::from(154),
            Scalar::from(178),
            Scalar::from(136),
            Scalar::from(130),
            Scalar::from(180),
            Scalar::from(129),
            Scalar::from(79),
            Scalar::from(161),
            Scalar::from(88),
        ];

        let l = Polynomium::new_from_scalar(&cl);
        let r = Polynomium::new_from_scalar(&cr);

        let t = l.clone() * r.clone();
        assert_eq!(t, Polynomium { coeffs: res });

        let x = Scalar::from(2 as u128);

        println!("l: {:?}", l);
        println!("r: {:?}", r);
        println!("t: {:?}", t);

        let l_x = l.eval(x);
        let r_x = r.eval(x);
        let t_x = t.eval(x);

        println!("l eval: {:?}", l.eval(x));
        println!("r eval: {:?}", r.eval(x));
        println!("t eval: {:?}", t.eval(x));

        // Should be 13
        assert_eq!(t_x, l_x * r_x);
    }

    #[quickcheck]
    /// Test multiplication of scalar polynomials
    fn test_scalar_polynomial_multiplication(m: u128, n: u128) -> bool {
        let m = (m % 10) as usize;
        let n = (n % 10) as usize;

        println!("m: {}, n: {}", m, n);

        let cl = random_vec(m);
        let cr = random_vec(n);

        let l = Polynomium::new_from_scalar(&cl);
        let r = Polynomium::new_from_scalar(&cr);

        let t = l.clone() * r.clone();
        let x = Scalar::from(2 as u128);

        let l_x = l.eval(x);
        let r_x = r.eval(x);
        let t_x = t.eval(x);

        println!("l: {:?}", l);
        println!("r: {:?}", r);
        println!("t: {:?}", t);

        println!("l eval: {:?}", l_x);
        println!("r eval: {:?}", r_x);
        println!("l * r: {:?}", l_x * r_x);
        println!("t eval: {:?}", t_x);

        t_x == l_x * r_x
    }

    #[quickcheck]
    /// Test multiplication of vector polynomials.
    fn test_vector_polynomial_multiplication(m: u128, n: u128, i: u128) {
        let m = m % 30;
        let n = n % 30;
        let i = i % 40;

        let cl: Vec<vec<'static, 10>> = (0..m+1).map(|_| random_vec_sized()).collect();
        let cr: Vec<vec<'static, 10>> = (0..n+1).map(|_| random_vec_sized()).collect();

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

/*
    #[quickcheck]
    /// Tests the trim method for scalar polynomiums.
    fn test_polynomium_trims<'a, const T: usize>(n: u128, i: u128) {
        let n = n % 20;
        let i = i % 20;

        let c: Vec<vec<'static, { T }>> = (0..n+1).map(|_| random_vec_sized()).collect();

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
    fn test_polynomial_vec_associativity<'a, const T: usize>(m:u128, n:u128, o:u128, i: u128) {
        let i = i % 10;
        let m = m % 5;
        let n = n % 10;
        let o = o % 8;

        let cm: Vec<vec<'static, { T }>> = (0..=m).map(|_| random_vec_sized()).collect();
        let co: Vec<vec<'static, { T }>> = (0..=o).map(|_| random_vec_sized()).collect();
        let cn: Vec<vec<'static, { T }>> = (0..=n).map(|_| random_vec_sized()).collect();

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
    fn test_polynomial_vec_commutativity<'a, const T: usize>(m:u128, n:u128, o:u128, i: u128) {
        let i = i % 10;
        let m = m % 5;
        let o = o % 8;

        let cm: Vec<vec<'static, { T }>> = (0..=m).map(|_| random_vec_sized()).collect();
        let co: Vec<vec<'static, { T }>> = (0..=o).map(|_| random_vec_sized()).collect();

        let pm = Polynomium::new_from_vec(cm).trim();
        let po = Polynomium::new_from_vec(co).trim();

        assert_eq!(pm.clone() + po.clone(), po + pm)
    }

    #[quickcheck]
    /// Test for identity element, for polynomials this is simply the polynomial: f(x)=0
    fn test_polynomial_identity_element<'a, const T: usize>(m: u128, p: u128, i: u128) {
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
    fn test_polynomial_monoid<'a, const T: usize>(m:u128, p: u128, n:u128, i:u128) {
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
*/
}
