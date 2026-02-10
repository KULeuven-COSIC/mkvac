use ark_ff::PrimeField;
use ark_serialize::CanonicalSerialize;
use ark_std::rand::{CryptoRng, RngCore};
use ark_std::UniformRand;
use sha2::{Digest, Sha256};
use rayon::prelude::*;

use crate::mkvak::mkvak::{IssuerPublic, PublicParams};
use crate::saga::bbs_saga::{
    smul, Params as VkaParams, Point, Scalar,
};

const PROT_NAME_REQ_FISCHLIN: &[u8] = b"AKVAC-REQ";


/// One Fischlin round: (c^(i), s^(i)) where s^(i) is the whole response vector.
#[derive(Clone, Debug)]
pub struct ReqProofRound {
    pub c: Scalar,

    // responses (same as FS version) + s_zeta
    pub s_s: Scalar,
    pub s_attrs: Vec<Scalar>,         // len n
    pub s_xi_prime: Vec<Scalar>,      // len n
    pub s_bar_x0: Scalar,
    pub s_bar_nu: Scalar,
    pub s_r: Scalar,
    pub s_e: Scalar,
    pub s_xi: Vec<Scalar>,            // len l = n+2
    pub s_eta: Scalar,
    pub s_zeta: Scalar,               // NEW
    pub s_prod: Scalar,
    pub s_prod_prime: Scalar,
}


/// Fischlin proof for AKVAC request:
/// - includes commitments ProdCom and Com once
/// - includes R rounds (c^(i), s^(i))
#[derive(Clone, Debug)]
pub struct ReqProofFischlin {
    pub prod_com: Point, // = eG + eta H
    pub com: Point,      // = sum attr_j G_j + zeta G
    pub rounds: Vec<ReqProofRound>, // len R
}

/// Serialize a Scalar into the transcript (deterministic).
#[inline]
fn absorb_scalar(buf: &mut Vec<u8>, x: &Scalar) {
    // For arkworks fields: use canonical serialization if available;
    // else you can switch to x.into_bigint().to_bytes_le()
    x.serialize_compressed(buf).unwrap();
}

/// Hash transcript to "work" value in {0,..,W-1}.
#[inline]
fn hash_to_work(transcript: &[u8], W: u64) -> u64 {
    debug_assert!(W >= 2);
    let d = Sha256::digest(transcript);
    let mut tmp = [0u8; 8];
    tmp.copy_from_slice(&d[..8]);
    let v = u64::from_le_bytes(tmp);
    v % W
}

/// Hash used in Fischlin rounds:
/// H(ProtName, ctx, derived_statement, all_announcements, i, c_i, s_i) mod W
fn fischlin_hash_req(
    nizkctx: &[u8],
    W: u64,

    // derived statement image S = (s1..s7)
    s1: &Point, s2: &Point, s3: &Point, s4: &Point, s5: &Point, s6: &Point, s7: &Point,

    // all announcements for all rounds, in order (u^(1),...,u^(R)),
    // each u^(j) is a 7-tuple of Points
    all_u: &[(Point, Point, Point, Point, Point, Point, Point)],

    // round index i in [0..R-1]
    i: usize,

    // round challenge and responses
    c_i: &Scalar,
    s_i: &ReqProofRound,
) -> u64 {
    let mut buf = Vec::new();
    buf.extend_from_slice(PROT_NAME_REQ_FISCHLIN);
    buf.extend_from_slice(nizkctx);

    // derived statement
    s1.serialize_compressed(&mut buf).unwrap();
    s2.serialize_compressed(&mut buf).unwrap();
    s3.serialize_compressed(&mut buf).unwrap();
    s4.serialize_compressed(&mut buf).unwrap();
    s5.serialize_compressed(&mut buf).unwrap();
    s6.serialize_compressed(&mut buf).unwrap();
    s7.serialize_compressed(&mut buf).unwrap();

    // all announcements (binds all rounds together)
    for (u1,u2,u3,u4,u5,u6,u7) in all_u.iter() {
        u1.serialize_compressed(&mut buf).unwrap();
        u2.serialize_compressed(&mut buf).unwrap();
        u3.serialize_compressed(&mut buf).unwrap();
        u4.serialize_compressed(&mut buf).unwrap();
        u5.serialize_compressed(&mut buf).unwrap();
        u6.serialize_compressed(&mut buf).unwrap();
        u7.serialize_compressed(&mut buf).unwrap();
    }

    // round index
    buf.extend_from_slice(&(i as u32).to_le_bytes());

    // challenge c_i
    absorb_scalar(&mut buf, c_i);

    // responses s_i (entire vector)
    absorb_scalar(&mut buf, &s_i.s_s);

    for x in s_i.s_attrs.iter()      { absorb_scalar(&mut buf, x); }
    for x in s_i.s_xi_prime.iter()   { absorb_scalar(&mut buf, x); }

    absorb_scalar(&mut buf, &s_i.s_bar_x0);
    absorb_scalar(&mut buf, &s_i.s_bar_nu);
    absorb_scalar(&mut buf, &s_i.s_r);
    absorb_scalar(&mut buf, &s_i.s_e);

    for x in s_i.s_xi.iter()         { absorb_scalar(&mut buf, x); }

    absorb_scalar(&mut buf, &s_i.s_eta);
    absorb_scalar(&mut buf, &s_i.s_zeta);
    absorb_scalar(&mut buf, &s_i.s_prod);
    absorb_scalar(&mut buf, &s_i.s_prod_prime);

    hash_to_work(&buf, W)
}