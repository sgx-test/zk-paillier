use curv::arithmetic::traits::*;
use curv::BigInt;
use rand::{thread_rng, RngCore};
use serde::{Deserialize, Serialize};
use std::iter;

#[derive(Clone, Deserialize, Serialize)]
pub struct NoSmallFactorSetUp {
    pub n_tilde: BigInt,
    pub s: BigInt,
    pub t: BigInt,
}

#[derive(Clone, Deserialize, Serialize)]
pub struct NoSmallFactorWitness {
    pub p_: BigInt,
    pub q_: BigInt,
}

#[derive(Clone, Deserialize, Serialize)]
pub struct NoSmallFactorStatement {
    pub n0: BigInt,
    pub l: usize,
    pub varepsilon: usize,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct NoSmallFactorProof {
    pub P_: BigInt,
    pub Q_: BigInt,
    pub A_: BigInt,
    pub B_: BigInt,
    pub T_: BigInt,
    pub sigma_: BigInt,
    pub z1_: BigInt,
    pub z2_: BigInt,
    pub w1_: BigInt,
    pub w2_: BigInt,
    pub v_: BigInt,
    salt: String,
}

impl NoSmallFactorProof {
    pub fn prove(
        setup: &NoSmallFactorSetUp,
        statement: &NoSmallFactorStatement,
        witness: &NoSmallFactorWitness,
    ) -> Self {
        let NoSmallFactorSetUp {
            n_tilde: N_tilde,
            s,
            t,
            ..
        } = setup;
        let NoSmallFactorStatement {
            n0: N0,
            l,
            varepsilon,
            ..
        } = statement;
        let NoSmallFactorWitness { p_: p, q_: q, .. } = witness;
        let l = l.clone();
        let varepsilon = varepsilon.clone();

        let sqrt_N0 = N0.sqrt();
        let limit_alpha_beta = (BigInt::one() << (l + varepsilon)) * sqrt_N0;
        // 2^l * N_tilde
        let limit_mu_nu = (BigInt::one() << l) * N_tilde;
        // 2^l * N0 * N_tilde
        let limit_sigma = &limit_mu_nu * N0;
        // 2^(l + varepsilon) * N0 * N_tilde
        let limit_r = &limit_sigma << varepsilon;
        // 2^(l + varepsilon) * N_tilde
        let limit_x_y = &limit_mu_nu << varepsilon;

        let alpha = random_neg_bnin_sym_interval(&limit_alpha_beta);
        let beta = random_neg_bnin_sym_interval(&limit_alpha_beta);
        let mu = random_neg_bnin_sym_interval(&limit_mu_nu);
        let nu = random_neg_bnin_sym_interval(&limit_mu_nu);
        let sigma_ = random_neg_bnin_sym_interval(&limit_sigma);
        let r = random_neg_bnin_sym_interval(&limit_r);
        let x = random_neg_bnin_sym_interval(&limit_x_y);
        let y = random_neg_bnin_sym_interval(&limit_x_y);

        // P = s^p * t^mu  mod N_tilde
        let P_ = (bn_mod_pow(&s, &p, N_tilde) * bn_mod_pow(&t, &mu, N_tilde)) % N_tilde;
        // Q = s^q * t^nu  mod N_tilde
        let Q_ = (bn_mod_pow(&s, &q, N_tilde) * bn_mod_pow(&t, &nu, N_tilde)) % N_tilde;
        // A = s^alpha * t^x  mod N_tilde
        let A_ = (bn_mod_pow(&s, &alpha, N_tilde) * bn_mod_pow(&t, &x, N_tilde)) % N_tilde;
        // B = s^beta * t^y  mod N_tilde
        let B_ = (bn_mod_pow(&s, &beta, N_tilde) * bn_mod_pow(&t, &y, N_tilde)) % N_tilde;
        // T = Q^alpha * t^r  mod N_tilde
        let T_ = (bn_mod_pow(&Q_, &alpha, N_tilde) * bn_mod_pow(&t, &r, N_tilde)) % N_tilde;

        let e = super::compute_digest(
            iter::once(BigInt::zero())
                .chain(iter::once(N0.clone()))
                .chain(iter::once(P_.clone()))
                .chain(iter::once(Q_.clone()))
                .chain(iter::once(A_.clone()))
                .chain(iter::once(B_.clone()))
                .chain(iter::once(T_.clone()))
                .chain(iter::once(sigma_.clone())),
        );

        let sigma_tilde = &sigma_ - &nu * p;
        let z1_ = &alpha + &e * p;
        let z2_ = &beta + &e * q;
        let w1_ = &x + &e * &mu;
        let w2_ = &y + &e * &nu;
        let v_ = &r + &e * &sigma_tilde;

        Self {
            P_,
            Q_,
            A_,
            B_,
            T_,
            sigma_,
            z1_,
            z2_,
            w1_,
            w2_,
            v_,
            salt: "".to_string(),
        }
    }
    pub fn verify(&self, setup: &NoSmallFactorSetUp, statement: &NoSmallFactorStatement) -> bool {
        let NoSmallFactorSetUp {
            n_tilde: N_tilde,
            s,
            t,
            ..
        } = setup;
        let NoSmallFactorStatement {
            n0: N0,
            l,
            varepsilon,
            ..
        } = statement;
        let l = l.clone();
        let varepsilon = varepsilon.clone();

        let NoSmallFactorProof {
            P_,
            Q_,
            A_,
            B_,
            T_,
            sigma_,
            z1_,
            z2_,
            w1_,
            w2_,
            v_,
            salt: _,
        } = self;

        let sqrt_N0 = N0.sqrt();
        let limit_alpha_beta = (BigInt::one() << (l + varepsilon)) * sqrt_N0;
        if z1_ > &limit_alpha_beta || z1_ < &(&BigInt::zero() - &limit_alpha_beta) {
            return false;
        }
        if z2_ > &limit_alpha_beta || z2_ < &(&BigInt::zero() - &limit_alpha_beta) {
            return false;
        }

        if N_tilde.bit_length() < 2046 {
            return false;
        }

        if P_ % N_tilde == BigInt::zero() {
            return false;
        }
        if Q_ % N_tilde == BigInt::zero() {
            return false;
        }
        if A_ % N_tilde == BigInt::zero() {
            return false;
        }
        if B_ % N_tilde == BigInt::zero() {
            return false;
        }
        if T_ % N_tilde == BigInt::zero() {
            return false;
        }

        if P_.gcd(N_tilde) != BigInt::one() {
            return false;
        }
        if Q_.gcd(N_tilde) != BigInt::one() {
            return false;
        }
        if A_.gcd(N_tilde) != BigInt::one() {
            return false;
        }
        if B_.gcd(N_tilde) != BigInt::one() {
            return false;
        }
        if T_.gcd(N_tilde) != BigInt::one() {
            return false;
        }

        let e = super::compute_digest(
            iter::once(BigInt::zero())
                .chain(iter::once(N0.clone()))
                .chain(iter::once(P_.clone()))
                .chain(iter::once(Q_.clone()))
                .chain(iter::once(A_.clone()))
                .chain(iter::once(B_.clone()))
                .chain(iter::once(T_.clone()))
                .chain(iter::once(sigma_.clone())),
        );

        let R = (bn_mod_pow(s, N0, N_tilde) * bn_mod_pow(t, sigma_, N_tilde)) % N_tilde;

        // s^z1 * t^w1 = A * P^e  mod N_tilde
        let mut left_num = (bn_mod_pow(s, z1_, N_tilde) * bn_mod_pow(t, w1_, N_tilde)) % N_tilde;
        let mut right_num = (A_ * bn_mod_pow(P_, &e, N_tilde)) % N_tilde;
        if left_num != right_num {
            return false;
        }

        // s^z2 * t^w2 = B * Q^e  mod N_tilde
        left_num = (bn_mod_pow(s, z2_, N_tilde) * bn_mod_pow(t, w2_, N_tilde)) % N_tilde;
        right_num = (B_ * bn_mod_pow(Q_, &e, N_tilde)) % N_tilde;
        if left_num != right_num {
            return false;
        }

        // Q^z1 * t^v = T * R^e  mod N_tilde
        left_num = (bn_mod_pow(Q_, z1_, N_tilde) * bn_mod_pow(t, v_, N_tilde)) % N_tilde;
        right_num = (T_ * bn_mod_pow(&R, &e, N_tilde)) % N_tilde;
        if left_num != right_num {
            return false;
        }

        return true;
    }
}

fn random_bnlt_gcd(max: &BigInt) -> BigInt {
    loop {
        let n = random_bnl_t(max);
        if n.gcd(max) == BigInt::one() {
            return n;
        }
    }
}

fn random_bnl_t(max: &BigInt) -> BigInt {
    let bits = max.bit_length();
    loop {
        let n: BigInt = BigInt::sample(bits);
        if n < *max {
            return n;
        }
    }
}

fn random_neg_bnin_sym_interval(limit: &BigInt) -> BigInt {
    assert!(limit > &BigInt::zero());
    let r = random_bnl_t(&BigInt::from(50));
    let mut sign = vec![0u8; 1];
    thread_rng().fill_bytes(&mut *sign);
    if sign[0] & 0x01 != 0 {
        return r;
    } else {
        return -r;
    }
}

fn bn_mod_pow(a: &BigInt, exp: &BigInt, n: &BigInt) -> BigInt {
    if BigInt::is_negative(exp) {
        let a_inv = BigInt::mod_inv(a, n).unwrap();
        BigInt::mod_pow(&a_inv, &-exp, n)
    } else {
        BigInt::mod_pow(&a, exp, n)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use paillier::{KeyGeneration, Keypair, Paillier};

    fn test_keypair() -> Keypair {
        let p = BigInt::from_str_radix("94808559127643069137967701413021262669271681989872481252137606187104323195389315579631304550201592597155979929630493326471094077416315879302371151434799499853615693537532375765853484684044766690335637566890359161081063645959945872867607497017297340279575405261796348122464082763478688308521153150165455345431", 10).unwrap();
        let q = BigInt::from_str_radix("151832855028521674676882970549101536705718714735289079096163150692690442009949623482407903925614020818477019919153350126038625817453868519611795652081831554915963219116036533251149890747884334737945707970113199306152158377454497122667479812914035608347360543824938423903071244379556750177251598641333081518727", 10).unwrap();
        Keypair { p, q }
    }

    fn test_keypair2() -> Keypair {
        let p = BigInt::from_str_radix("3", 10).unwrap();
        let q = BigInt::from_str_radix("7", 10).unwrap();
        Keypair { p, q }
    }

    pub fn generate_h1_h2_N_tilde() -> (BigInt, BigInt, BigInt, BigInt, BigInt) {
        // note, should be safe primes:
        //let (ek_tilde, dk_tilde) = Paillier::keypair_safe_primes().keys();;
        let (ek_tilde, dk_tilde) = Paillier::keypair().keys();
        //let (ek_tilde, dk_tilde) = test_keypair().keys();

        let one = BigInt::one();
        let phi = (&dk_tilde.p - &one) * (&dk_tilde.q - &one);
        let h1 = BigInt::sample_below(&ek_tilde.n);
        let (mut xhi, mut xhi_inv) = loop {
            let xhi_ = BigInt::sample_below(&phi);
            match BigInt::mod_inv(&xhi_, &phi) {
                Some(inv) => break (xhi_, inv),
                None => continue,
            }
        };
        let h2 = BigInt::mod_pow(&h1, &xhi, &ek_tilde.n);
        xhi = BigInt::sub(&phi, &xhi);
        xhi_inv = BigInt::sub(&phi, &xhi_inv);

        (ek_tilde.n, h1, h2, xhi, xhi_inv)
    }

    #[test]
    fn test_no_small_factors() {
        let n_tilde_hex = "C11A2F1A0EA592008BAFCAE756038DE028BA195E73B60F773F7399B4B94E26F8F90C488DEEA7ADB6910BCBCA8BA558E527B67B0B098420D4282411863B3FF39049C420CEB61D4C3683D2264957E583066F9C08C71E7A2A9E8E628E7853C962C4240E2E6FDB1F0F547A33EF0C31BD2B9739E0191AAF948AADE86519CD01A7B944A37C7150DF78A6E6FF4E5B8598F06334374BA068316C73484A07C2A0DF96DFE25931D0C67CE3A8B0E14635F0B34C1937F376EAB077281553F9F81E563DE7111136D95C8A5F9B87D91681AB412A8B62409CD2A2C3386E9B3E2FA3A7B7BE75368415315C1F905B7F38F4ED6758AD88563C41F28B717C7C13573062E6A6D4AA2A8D";
        let N_tilde = BigInt::from_hex(n_tilde_hex).unwrap();
        let mut h1 = random_bnlt_gcd(&N_tilde);
        h1 = (&h1 * &h1) % &N_tilde;
        let mut h2 = random_bnlt_gcd(&N_tilde);
        h2 = (&h2 * &h2) % &N_tilde;

        let (ek, dk) = test_keypair().keys();

        let P = dk.p;
        let Q = dk.q;
        let N = ek.n;

        let set_up: NoSmallFactorSetUp = NoSmallFactorSetUp {
            n_tilde: N_tilde,
            s: h1,
            t: h2,
        };
        let statement: NoSmallFactorStatement = NoSmallFactorStatement {
            n0: N,
            l: 256,
            varepsilon: 512,
        };
        let witness: NoSmallFactorWitness = NoSmallFactorWitness { p_: P, q_: Q };
        let proof = NoSmallFactorProof::prove(&set_up, &statement, &witness);
        assert!(proof.verify(&set_up, &statement));
    }

    #[test]
    fn test_no_small_factors_mpc() {
        let (N_tilde, h1, h2, _xhi, _xhi_inv) = generate_h1_h2_N_tilde();
        let (ek, dk) = test_keypair().keys();

        let P = dk.p;
        let Q = dk.q;
        // let N = ek.n;
        let N = ek.n + BigInt::from_str_radix("7", 10).unwrap();

        let set_up: NoSmallFactorSetUp = NoSmallFactorSetUp {
            n_tilde: N_tilde,
            s: h1,
            t: h2,
        };
        let statement: NoSmallFactorStatement = NoSmallFactorStatement {
            n0: N,
            l: 256,
            varepsilon: 512,
        };
        let witness: NoSmallFactorWitness = NoSmallFactorWitness { p_: P, q_: Q };
        let proof = NoSmallFactorProof::prove(&set_up, &statement, &witness);
        assert!(proof.verify(&set_up, &statement));
    }
}
