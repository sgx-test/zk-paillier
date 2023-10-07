use std::iter;

use curv::arithmetic::traits::*;
use curv::BigInt;
use serde::{Deserialize, Serialize};

// jacobi
use curv::arithmetic::{Converter, Modulo};
use num_bigint::{BigInt as numtrait_bigint, Sign};
use num_integer::Integer;
use num_traits::{cast::ToPrimitive, sign::Signed};

//openssl
use openssl;
use openssl::bn::{BigNum, BigNumContext};

const ITERATIONS_BLUM_INT_PROOF: usize = 128;
const ITERATIONS_PAIL_N_PROOF: usize = 11;
const PRIME_UTIL: usize = 6370;

#[derive(Debug, Serialize, Deserialize, Clone)]
pub struct BlumModulesProof {
    pub x_arr: Vec<BigInt>,
    pub a_arr: Vec<u32>,
    pub b_arr: Vec<u32>,
    pub z_arr: Vec<BigInt>,
    pub w: BigInt,
}

impl BlumModulesProof {
    pub fn prove(n: BigInt, p: BigInt, q: BigInt) -> Option<Self> {
        if n != p.clone() * q.clone() {
            return None;
        }

        let mut x_arr = Vec::new();
        let mut a_arr = Vec::new();
        let mut b_arr = Vec::new();
        let mut z_arr = Vec::new();

        let mut w = BigInt::sample_range(&BigInt::zero(), &n);
        while jacobi(&w, &n) != -1 {
            w = BigInt::sample_range(&BigInt::zero(), &n);
        }

        let y_arr = generate_ys(n.clone(), w.clone());
        for i in 0..ITERATIONS_BLUM_INT_PROOF {
            //bool ok = GetQuarticSqrt(N, p, q, p.InvM(q), q.InvM(p), w_, y_arr[i], root, a, b);
            let (root, a, b) = match get_quartic_sqrt(
                &n,
                &p,
                &q,
                BigInt::mod_inv(&p, &q).unwrap(),
                BigInt::mod_inv(&q, &p).unwrap(),
                &w,
                y_arr[i].clone(),
            ) {
                Some(data) => data,
                None => return None,
            };
            x_arr.push(root);
            a_arr.push(a);
            b_arr.push(b);
        }

        let lambda = (p - 1) * (q - 1);
        let n_inv = BigInt::mod_inv(&n, &lambda).unwrap();
        for i in 0..ITERATIONS_BLUM_INT_PROOF {
            let z = BigInt::mod_pow(&y_arr[i], &n_inv, &n);
            z_arr.push(z);
        }

        Some(BlumModulesProof {
            x_arr,
            a_arr,
            b_arr,
            z_arr,
            w,
        })
    }

    pub fn verify(&self, n: BigInt) -> bool {
        if self.x_arr.len() < ITERATIONS_BLUM_INT_PROOF {
            return false;
        }
        if self.a_arr.len() < ITERATIONS_BLUM_INT_PROOF {
            return false;
        }
        if self.b_arr.len() < ITERATIONS_BLUM_INT_PROOF {
            return false;
        }
        if self.z_arr.len() < ITERATIONS_BLUM_INT_PROOF {
            return false;
        }
        if n < BigInt::one() || n.bit_length() < 2046 {
            return false;
        }
        if self.w <= BigInt::zero() || self.w >= n {
            return false;
        }
        assert_eq!(jacobi(&self.w, &n), -1);

        let y_arr = generate_ys(n.clone(), self.w.clone());

        for i in 0..ITERATIONS_BLUM_INT_PROOF {
            let expect_y_prime = BigInt::mod_pow(&self.x_arr[i], &BigInt::from(4), &n.clone()); //x_arr_[i].PowM(BN(4), N);

            let x1 = if self.a_arr[i] != 0 {
                BigInt::from(-1)
            } else {
                BigInt::one()
            };
            let x2 = if self.b_arr[i] != 0 {
                self.w.clone()
            } else {
                BigInt::one()
            };
            let y_prime = ((&y_arr[i] * &x1 * &x2) % &n + &n) % &n;
            if expect_y_prime != y_prime {
                return false;
            }
        }

        // Check the pail N
        let prime_arr = prime_util(PRIME_UTIL as i32).unwrap();
        for p in prime_arr {
            if n.clone() % BigInt::from(p) == BigInt::zero() {
                return false;
            }
        }

        for i in 0..ITERATIONS_BLUM_INT_PROOF {
            if self.z_arr[i] <= BigInt::one() || self.z_arr[i] >= n.clone() {
                return false;
            }
            if self.z_arr[i].gcd(&n) != BigInt::one() {
                return false;
            }
            let z = BigInt::mod_pow(&self.z_arr[i], &n, &n); //self.z_arr_[i].PowM(N, N);
            if z != y_arr[i] {
                return false;
            }
        }

        true
    }
}

/// Jacobi returns the Jacobi symbol (x/y), either +1, -1, or 0.
/// The y argument must be an odd integer.
pub fn jacobi(x: &BigInt, y: &BigInt) -> isize {
    let x_bytes = x.to_bytes();
    let x = num_bigint::BigInt::from_bytes_be(Sign::Plus, &x_bytes);
    let y_bytes = y.to_bytes();
    let y = num_bigint::BigInt::from_bytes_be(Sign::Plus, &y_bytes);

    if !y.is_odd() {
        panic!(
            "invalid arguments, y must be an odd integer,but got {:?}",
            y
        );
    }

    let mut a = x.clone();
    let mut b = y.clone();
    let mut j = 1;

    if b.is_negative() {
        if a.is_negative() {
            j = -1;
        }
        b = -b;
    }

    loop {
        if b.is_one() {
            return j;
        }
        if a.is_zero() {
            return 0;
        }

        a = a.mod_floor(&b);
        if a.is_zero() {
            return 0;
        }

        // handle factors of 2 in a
        let s = a.trailing_zeros().unwrap();
        if s & 1 != 0 {
            let bmod8 = (&b & numtrait_bigint::from(7)).to_u64().unwrap();
            if bmod8 == 3 || bmod8 == 5 {
                j = -j;
            }
        }

        let c = &a >> s; // a = 2^s*c

        // swap numerator and denominator
        if &b & numtrait_bigint::from(3) == numtrait_bigint::from(3)
            && &c & numtrait_bigint::from(3) == numtrait_bigint::from(3)
        {
            j = -j
        }

        a = b;
        b = c;
    }
}

pub fn get_quartic_sqrt(
    n: &BigInt,
    p: &BigInt,
    q: &BigInt,
    p_inv: BigInt,
    q_inv: BigInt,
    w: &BigInt,
    r: BigInt,
) -> Option<(BigInt, u32, u32)> {
    // root,a,b
    let mut a = 0;
    let mut b = 0;

    // one of {r, -1 * r, w * r, -1 * w * r } is a quadratic residue
    let mut r_arr = Vec::new();
    r_arr.push(r.clone()); // (a, b) = (0, 0)
    r_arr.push(-r.clone()); // (a, b) = (1, 0)
    r_arr.push(r.clone() * w); // (a, b) = (0, 1)
    r_arr.push(-r.clone() * w); // (a, b) = (1, 1)

    // Group Zpq is isomorphic to group Zp * Zq
    let mut a1_arr = Vec::new();
    let mut a2_arr = Vec::new();
    for r_arr in r_arr {
        a1_arr.push(r_arr.clone() % p);
        a2_arr.push(r_arr.clone() % q);
    }

    let mut quadratic_root_1 = BigInt::from(0);
    let mut quadratic_root_2 = BigInt::from(0);
    let mut flag_2 = false;
    for i in 0..a1_arr.len() {
        if !exist_sqrt_m(&a1_arr[i], p) {
            continue;
        }
        flag_2 = exist_sqrt_m(&a2_arr[i], q);
        if !flag_2 {
            continue;
        }
        quadratic_root_1 = bn_mod_sqrt(&a1_arr[i], p).unwrap();
        quadratic_root_2 = bn_mod_sqrt(&a2_arr[i], q).unwrap();

        a = if i & 0x01 != 0 { 1 } else { 0 };
        b = if i & 0x02 != 0 { 1 } else { 0 };
        break;
    }
    if !flag_2 {
        return None;
    }

    // Group Zpq is isomorphic to group Zp * Zq
    // (a1, a2) is an element in Zp * Zq.
    // if (a1, a2) is a quadratic residue in Zp * Zq, then one of {(a1, a2), (-a1, a2), (a1, -a2), (-a1, -a2)} is a quartic residue.
    a1_arr.clear();
    a2_arr.clear();
    a1_arr.push(quadratic_root_1.clone());
    a2_arr.push(quadratic_root_2.clone());
    a1_arr.push(-quadratic_root_1.clone());
    a2_arr.push(quadratic_root_2.clone());
    a1_arr.push(quadratic_root_1.clone());
    a2_arr.push(-quadratic_root_2.clone());
    a1_arr.push(-quadratic_root_1.clone());
    a2_arr.push(-quadratic_root_2.clone());

    for (a1_arr, a2_arr) in a1_arr.iter().zip(a2_arr) {
        if !exist_sqrt_m(&a1_arr, p) {
            continue;
        }
        flag_2 = exist_sqrt_m(&a2_arr, q);
        if !flag_2 {
            continue;
        }
        quadratic_root_1 = bn_mod_sqrt(&a1_arr, p).unwrap();
        quadratic_root_2 = bn_mod_sqrt(&a2_arr, q).unwrap();
        let root = (quadratic_root_1 * q_inv * q + quadratic_root_2 * p_inv * p) % n;
        return Some((root, a, b));
    }

    None
}

pub fn generate_ys(n: BigInt, w: BigInt) -> Vec<BigInt> {
    let mut y_vec = Vec::new();
    for i in 0..ITERATIONS_BLUM_INT_PROOF {
        let n = n.clone();
        let w = w.clone();
        let mut e = super::compute_digest(
            iter::once(BigInt::from(i as u64))
                .chain(iter::once(n.clone()))
                .chain(iter::once(w)),
        );
        e = e % n;
        y_vec.push(e);
    }
    y_vec
}

fn exist_sqrt_m(n: &BigInt, p: &BigInt) -> bool {
    let p_minus_1 = p - BigInt::one();
    let lpow = &p_minus_1 >> 1;

    let b = n % p;
    if b.is_zero() {
        return true;
    }

    if BigInt::mod_pow(&b, &lpow, &p) == BigInt::one() {
        return true;
    } else {
        return false;
    }
}

pub fn bn_mod_pow(a: &BigInt, exp: &BigInt, n: &BigInt) -> Option<BigInt> {
    let mut ctx = BigNumContext::new().unwrap();
    let s = BigNum::from_hex_str(&a.to_hex()).unwrap();
    let exp = BigNum::from_hex_str(&exp.to_hex()).unwrap();

    let p = BigNum::from_hex_str(&n.to_hex()).unwrap();
    let mut out = BigNum::new().unwrap();

    out.mod_exp(&s, &exp, &p, &mut ctx).unwrap();

    Some(BigInt::from_hex(&out.to_hex_str().unwrap()).unwrap())
}

fn bn_mod_sqrt(a: &BigInt, n: &BigInt) -> Option<BigInt> {
    let mut ctx = BigNumContext::new().unwrap();
    let s = BigNum::from_hex_str(&a.to_hex()).unwrap();
    let p = BigNum::from_hex_str(&n.to_hex()).unwrap();
    let mut out = BigNum::new().unwrap();

    out.mod_sqrt(&s, &p, &mut ctx).unwrap();

    Some(BigInt::from_hex(&out.to_hex_str().unwrap()).unwrap())
}

fn prime_util(n: i32) -> Option<Vec<i32>> {
    let mut prime_arr = Vec::new();
    assert!(n > 0);
    prime_arr.clear();
    if n < 2 {
        return None;
    }
    for i in 3..=n {
        let mut is_prime = true;
        for &p in prime_arr.iter() {
            if p * p >= i {
                break;
            }
            if i % p == 0 {
                is_prime = false;
                break;
            }
        }
        if is_prime {
            prime_arr.push(i);
        }
    }
    Some(prime_arr)
}

#[cfg(test)]
mod tests {
    use super::*;
    use openssl::bn::{BigNum, BigNumContext};
    use paillier::{KeyGeneration, Keypair, Paillier};

    fn test_keypair() -> Keypair {
        let p = BigInt::from_str_radix("94808559127643069137967701413021262669271681989872481252137606187104323195389315579631304550201592597155979929630493326471094077416315879302371151434799499853615693537532375765853484684044766690335637566890359161081063645959945872867607497017297340279575405261796348122464082763478688308521153150165455345431", 10).unwrap();
        let q = BigInt::from_str_radix("151832855028521674676882970549101536705718714735289079096163150692690442009949623482407903925614020818477019919153350126038625817453868519611795652081831554915963219116036533251149890747884334737945707970113199306152158377454497122667479812914035608347360543824938423903071244379556750177251598641333081518727", 10).unwrap();
        Keypair { p, q }
    }

    fn test_keypair_2() -> Keypair {
        let p = BigInt::from_hex("3").unwrap();
        let q = BigInt::from_hex("7").unwrap();
        Keypair { p, q }
    }

    #[test]
    fn openssl_bignum() {
        let bigint_a = BigInt::from(500);
        let bigint_b = BigInt::from(600);
        let bigint_c = &bigint_a + &bigint_b;
        println!("{:?}", bigint_c);
        let bytes = bigint_a.to_string();
        println!("bytes{:?}", bytes);

        let bignum_a = BigNum::from_dec_str(&bytes).unwrap();
        println!("bignum_a {:?}", bignum_a);

        let data0 = BigInt::mod_pow(&BigInt::from(3), &BigInt::from(8), &BigInt::from(17));
        let data = bn_mod_pow(&BigInt::from(15), &BigInt::from(-15), &BigInt::from(17));
        println!("data0 {:?} data {:?}", data0, data);
    }

    use curv::arithmetic::Converter;
    #[test]
    fn openssl_bignum_convert() {
        let mut ctx = BigNumContext::new().unwrap();
        let a = BigNum::from_hex_str("47A8DD7626B9908C80ACD7E0D3344D69").unwrap();
        let p = BigNum::from_hex_str("81EF47265B58BCE5").unwrap();
        let m = BigNum::from_hex_str("45482121EFG").unwrap();

        let mut out = BigNum::new().unwrap();

        out.mod_exp(&a, &p, &m, &mut ctx).unwrap();

        let a_b = BigInt::from_hex(&a.to_hex_str().unwrap()).unwrap();
        let p_b = BigInt::from_hex(&p.to_hex_str().unwrap()).unwrap();
        let m_b = BigInt::from_hex(&m.to_hex_str().unwrap()).unwrap();
        let out2 = BigInt::mod_pow(&a_b, &p_b, &m_b);

        assert_eq!(out.to_string(), out2.to_string());

        let mut ctx = BigNumContext::new().unwrap();
        let s = BigNum::from_hex_str("47A8DD7626B9908C80ACD7E0D3344D69").unwrap();
        let p = BigNum::from_hex_str("81EF47265B58BCE5").unwrap();
        let mut out = BigNum::new().unwrap();

        out.mod_sqrt(&s, &p, &mut ctx).unwrap();
        println!("mod_sqrt");
        assert_eq!(out, BigNum::from_hex_str("7C6D179E19B97BDD").unwrap());
    }

    #[test]
    fn test_correct_blum_modules_proof() {
        //let (ek, dk) = test_keypair().keys();
        let (ek, dk) = Paillier::keypair_safe_primes().keys();
        println!("======start======");
        assert_eq!(&dk.p % 4, BigInt::from(3));
        assert_eq!(&dk.q % 4, BigInt::from(3));
        let proof = BlumModulesProof::prove(ek.n.clone(), dk.p.clone(), dk.q.clone()).unwrap();
        assert!(proof.verify(ek.n));
    }
}
