/*
    zk-paillier

    Copyright 2018 by Kzen Networks

    zk-paillier is free software: you can redistribute
    it and/or modify it under the terms of the GNU General Public
    License as published by the Free Software Foundation, either
    version 3 of the License, or (at your option) any later version.

    @license GPL-3.0+ <https://github.com/KZen-networks/zk-paillier/blob/master/LICENSE>
*/
#![allow(non_snake_case)]
#![allow(dead_code)]

mod zero_enc_proof;
pub use self::zero_enc_proof::*;

mod correct_ciphertext;
pub use self::correct_ciphertext::*;

mod multiplication_proof;
pub use self::multiplication_proof::*;

mod verlin_proof;
pub use self::verlin_proof::*;

mod wi_dlog_proof;
pub use self::wi_dlog_proof::*;

mod correct_opening;
pub use self::correct_opening::CorrectOpening;

pub use self::correct_key::Challenge;
pub use self::correct_key::CorrectKeyProof;
pub use self::correct_key::VerificationAid;
mod correct_key;
pub use self::correct_key::CorrectKey;
pub use self::correct_key_ni::SALT_STRING;

mod correct_key_ni;
pub use self::correct_key_ni::CorrectKeyProofError;
pub use self::correct_key_ni::NICorrectKeyProof;
mod range_proof;
pub use self::range_proof::RangeProof;
pub use self::range_proof::RangeProofTrait;

pub use self::range_proof::ChallengeBits;
pub use self::range_proof::EncryptedPairs;
pub use self::range_proof::Proof;
mod range_proof_ni;
pub use self::range_proof_ni::RangeProofError;
pub use self::range_proof_ni::RangeProofNi;

mod correct_message;
mod blum_modules_proof;
mod no_small_factors;

pub use self::correct_message::CorrectMessageProof;
pub use self::correct_message::CorrectMessageProofError;

use std::borrow::Borrow;

use curv::arithmetic::traits::*;
use curv::BigInt;

use digest::Digest;
use sha2::Sha256;

pub fn compute_digest<'a, IT>(it: IT) -> BigInt
where
    IT: Iterator,
    IT::Item: Borrow<BigInt>,
{
    let mut hasher = Sha256::new();
    for value in it {
        let bytes: Vec<u8> = value.borrow().to_bytes();
        hasher.input(&bytes);
    }

    let result_bytes = hasher.result();
    BigInt::from_bytes(&result_bytes[..])
}
