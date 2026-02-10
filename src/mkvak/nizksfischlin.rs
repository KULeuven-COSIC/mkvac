use ark_ff::{PrimeField, Zero};
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



/// Prover for cmzcpzrec (request proof) using randomized Fischlin transform.
///
/// Parameters:
/// - R: number of parallel Schnorr instances
/// - W: proof-of-work difficulty; accept if hash mod W == 0
///
/// This matches your LaTeX:
/// For each i in [R], pick random a^(i), compute announcement.
/// Then repeat: sample random c^(i), compute s^(i)=a^(i)+c^(i)*w, until hash==0.
pub fn nizk_prove_req_fischlin<RNG: RngCore + CryptoRng>(
    rng: &mut RNG,
    pp: &PublicParams,
    ipk: &IssuerPublic,
    params: &VkaParams,

    // public statement inputs:
    vka_pres: &crate::saga::bbs_saga::SAGAPres, // has C_A, T
    C_j_vec: &[Point], // C_1..C_{n+2}
    bar_X0: &Point,
    bar_Z0: &Point,
    C_attr: &Point,

    // secret witness inputs:
    s: &Scalar,
    attrs: &[Scalar],      // attr_j, j=1..n
    bar_x0: &Scalar,
    bar_nu: &Scalar,
    r: &Scalar,
    e: &Scalar,            // BBS signature scalar
    xi_vec: &[Scalar],     // xi_1..xi_{n+2}

    // Fischlin params + context
    nizkctx: &[u8],
    R_par: usize,
    W_work: u64,
) -> ReqProofFischlin {
    let l = params.G_vec.len(); // l = n + 2
    let n = l - 2;

    assert_eq!(C_j_vec.len(), l);
    assert_eq!(attrs.len(), n);
    assert_eq!(xi_vec.len(), l);
    assert!(R_par >= 1);
    assert!(W_work >= 2);

    // --- commitments for product-check and collision-resistance ---
    let eta = Scalar::rand(rng);
    let prod_com = smul(&pp.G, e) + smul(&pp.H, &eta);

    let zeta = Scalar::rand(rng);
    // Com = sum_{j in [n]} attr_j * G_j + zeta * G
    let sum_attrGj: Point = params.G_vec[..n]
        .par_iter()
        .zip(attrs.par_iter())
        .map(|(Gj, aj)| smul(Gj, aj))
        .reduce(Point::zero, |acc, p| acc + p);
    let com = sum_attrGj + smul(&pp.G, &zeta);

    let prod = *e * *r;          // e * r
    let prod_prime = *r * eta;   // r * eta

    // --- derived statement image S = (s1..s7) ---
    let s1 = *bar_X0 - C_j_vec[n];
    let s2 = *bar_Z0 - C_j_vec[n + 1];
    let s3 = *C_attr;
    let s4 = vka_pres.T;
    let s5 = prod_com;
    let s6 = Point::zero();
    let s7 = com;

    // --- Step 1: sample all a^(i) and compute announcements t^(i) = φ(a^(i)) ---
    // We store the a-values for each round so we can form s^(i)=a^(i)+c^(i)*witness later.
    #[derive(Clone)]
    struct RoundA {
        a_s: Scalar,
        a_attrs: Vec<Scalar>,
        a_xi_prime: Vec<Scalar>,
        a_bar_x0: Scalar,
        a_bar_nu: Scalar,
        a_r: Scalar,
        a_e: Scalar,
        a_xi: Vec<Scalar>,
        a_eta: Scalar,
        a_zeta: Scalar,
        a_prod: Scalar,
        a_prod_prime: Scalar,
    }

    let mut a_rounds: Vec<RoundA> = Vec::with_capacity(R_par);
    let mut announcements: Vec<(Point,Point,Point,Point,Point,Point,Point)> = Vec::with_capacity(R_par);

    for _i in 0..R_par {
        let a_s = Scalar::rand(rng);
        let a_attrs: Vec<Scalar>    = (0..n).map(|_| Scalar::rand(rng)).collect();
        let a_xi_prime: Vec<Scalar> = (0..n).map(|_| Scalar::rand(rng)).collect();
        let a_bar_x0 = Scalar::rand(rng);
        let a_bar_nu = Scalar::rand(rng);
        let a_r = Scalar::rand(rng);
        let a_e = Scalar::rand(rng);
        let a_xi: Vec<Scalar>       = (0..l).map(|_| Scalar::rand(rng)).collect();
        let a_eta = Scalar::rand(rng);
        let a_zeta = Scalar::rand(rng);
        let a_prod = Scalar::rand(rng);
        let a_prod_prime = Scalar::rand(rng);

        // t1..t6 are same shape as your FS version, but computed from a-values.
        let t1 = -smul(&params.G_vec[n],   &a_xi[n])
            + smul(&params.G, &a_bar_x0)
            + smul(&ipk.E,    &a_bar_nu);

        let t2 = -smul(&params.G_vec[n+1], &a_xi[n+1])
            + smul(&params.G, &a_bar_nu);

        let sum_Ca: Point = C_j_vec[..n]
            .par_iter()
            .zip(a_attrs.par_iter())
            .map(|(Cj, a)| smul(Cj, a))
            .reduce(Point::zero, |acc, p| acc + p);

        let sum_Gxi: Point = params.G_vec[..n]
            .par_iter()
            .zip(a_xi_prime.par_iter())
            .map(|(Gj, xi)| smul(Gj, xi))
            .reduce(Point::zero, |acc, p| acc + p);

        let t3 = smul(&pp.G, &a_s) + sum_Ca - sum_Gxi;

        let sum_Yxi: Point = ipk.saga_pk.Y_vec[..l]
            .par_iter()
            .zip(a_xi.par_iter())
            .map(|(Yj, xi)| smul(Yj, xi))
            .reduce(Point::zero, |acc, p| acc + p);

        let mut t4 = smul(&ipk.saga_pk.X, &a_r);
        t4 -= smul(&vka_pres.C_A, &a_e);
        t4 += smul(&pp.G, &a_prod);
        t4 -= sum_Yxi;

        let t5 = smul(&pp.G, &a_e) + smul(&pp.H, &a_eta);

        let t6 = smul(&pp.G, &a_prod) + smul(&pp.H, &a_prod_prime) - smul(&prod_com, &a_r);

        // NEW: t7 = sum_j a_attr_j * G_j + a_zeta * G
        let sum_aGj: Point = params.G_vec[..n]
            .par_iter()
            .zip(a_attrs.par_iter())
            .map(|(Gj, aj)| smul(Gj, aj))
            .reduce(Point::zero, |acc, p| acc + p);
        let t7 = sum_aGj + smul(&pp.G, &a_zeta);

        announcements.push((t1,t2,t3,t4,t5,t6,t7));
        a_rounds.push(RoundA{
            a_s, a_attrs, a_xi_prime, a_bar_x0, a_bar_nu, a_r, a_e, a_xi,
            a_eta, a_zeta, a_prod, a_prod_prime
        });
    }

    // --- Step 2: for each round i, search random c^(i) until hash==0 ---
    let max_tries_per_round: usize = (W_work as usize) * 64; // conservative cap

    let mut rounds: Vec<ReqProofRound> = Vec::with_capacity(R_par);

    for i in 0..R_par {
        let a = &a_rounds[i];

        // witness-derived values used in responses
        // xi'_j = attr_j * xi_j
        let xi_prime_wit: Vec<Scalar> = attrs.iter().zip(xi_vec.iter()).map(|(aj, xij)| (*aj) * (*xij)).collect();

        let mut found: Option<(Scalar, ReqProofRound)> = None;

        for _try in 0..max_tries_per_round {
            let c_i = Scalar::rand(rng);

            // responses s^(i) = a^(i) + c^(i) * witness
            let s_s = a.a_s + c_i * *s;

            let s_attrs: Vec<Scalar> = a.a_attrs
                .iter()
                .zip(attrs.iter())
                .map(|(aa, wj)| *aa + c_i * *wj)
                .collect();

            let s_xi_prime: Vec<Scalar> = a.a_xi_prime
                .iter()
                .zip(xi_prime_wit.iter())
                .map(|(aa, wj)| *aa + c_i * *wj)
                .collect();

            let s_bar_x0 = a.a_bar_x0 + c_i * *bar_x0;
            let s_bar_nu = a.a_bar_nu + c_i * *bar_nu;
            let s_r = a.a_r + c_i * *r;
            let s_e = a.a_e + c_i * *e;

            let s_xi: Vec<Scalar> = a.a_xi
                .iter()
                .zip(xi_vec.iter())
                .map(|(aa, wj)| *aa + c_i * *wj)
                .collect();

            let s_eta = a.a_eta + c_i * eta;
            let s_zeta = a.a_zeta + c_i * zeta;
            let s_prod = a.a_prod + c_i * prod;
            let s_prod_prime = a.a_prod_prime + c_i * prod_prime;

            let round = ReqProofRound {
                c: c_i,
                s_s,
                s_attrs,
                s_xi_prime,
                s_bar_x0,
                s_bar_nu,
                s_r,
                s_e,
                s_xi,
                s_eta,
                s_zeta,
                s_prod,
                s_prod_prime,
            };

            // Fischlin condition: hash(...) == 0 mod W
            let work = fischlin_hash_req(
                nizkctx, W_work,
                &s1,&s2,&s3,&s4,&s5,&s6,&s7,
                &announcements,
                i,
                &round.c,
                &round
            );

            if work == 0 {
                found = Some((c_i, round));
                break;
            }
        }

        let (_c, round) = found.expect("Fischlin search failed: increase max tries or check transcript");
        rounds.push(round);
    }

    ReqProofFischlin { prod_com, com, rounds }
}




/// Verifier for cmzcpzrec (request proof) using randomized Fischlin transform.
///
/// Verifier recomputes u^(i) = φ(s^(i)) - c^(i)·S for each round i,
/// then checks that for all i: H(..., (u^(j))_j, i, c^(i), s^(i)) mod W == 0.
pub fn nizk_verify_req_fischlin(
    pp: &PublicParams,
    ipk: &IssuerPublic,
    params: &VkaParams,
    vka_pres: &crate::saga::bbs_saga::SAGAPres,
    C_j_vec: &[Point],
    bar_X0: &Point,
    bar_Z0: &Point,
    C_attr: &Point,

    nizkctx: &[u8],
    W_work: u64,

    proof: &ReqProofFischlin,
) -> bool {
    let l = params.G_vec.len();
    let n = l - 2;

    if C_j_vec.len() != l { return false; }
    if proof.rounds.is_empty() { return false; }
    if W_work < 2 { return false; }

    // derived statement image S = (s1..s7)
    let s1 = *bar_X0 - C_j_vec[n];
    let s2 = *bar_Z0 - C_j_vec[n+1];
    let s3 = *C_attr;
    let s4 = vka_pres.T;
    let s5 = proof.prod_com;
    let s6 = Point::zero();
    let s7 = proof.com;

    let R_par = proof.rounds.len();

    // recompute all accepting announcements u^(i) (must equal φ(a^(i)) for accepting rounds)
    let mut all_u: Vec<(Point,Point,Point,Point,Point,Point,Point)> = Vec::with_capacity(R_par);

    for (i, rd) in proof.rounds.iter().enumerate() {
        if rd.s_attrs.len() != n || rd.s_xi_prime.len() != n || rd.s_xi.len() != l {
            return false;
        }

        // u1..u6 same as FS verify, but parameterized by round (c, s)
        let mut u1 = -smul(&params.G_vec[n], &rd.s_xi[n]);
        u1 += smul(&params.G, &rd.s_bar_x0);
        u1 += smul(&ipk.E, &rd.s_bar_nu);
        u1 -= smul(&s1, &rd.c);

        let mut u2 = -smul(&params.G_vec[n+1], &rd.s_xi[n+1]);
        u2 += smul(&params.G, &rd.s_bar_nu);
        u2 -= smul(&s2, &rd.c);

        let mut u3 = smul(&pp.G, &rd.s_s);
        for j in 0..n {
            u3 += smul(&C_j_vec[j], &rd.s_attrs[j]);
            u3 -= smul(&params.G_vec[j], &rd.s_xi_prime[j]);
        }
        u3 -= smul(&s3, &rd.c);

        let mut u4 = smul(&ipk.saga_pk.X, &rd.s_r);
        u4 -= smul(&vka_pres.C_A, &rd.s_e);
        u4 += smul(&pp.G, &rd.s_prod);
        for j in 0..l {
            u4 -= smul(&ipk.saga_pk.Y_vec[j], &rd.s_xi[j]);
        }
        u4 -= smul(&s4, &rd.c);

        let mut u5 = smul(&pp.G, &rd.s_e) + smul(&pp.H, &rd.s_eta);
        u5 -= smul(&s5, &rd.c);

        let u6 = smul(&pp.G, &rd.s_prod)
            + smul(&pp.H, &rd.s_prod_prime)
            - smul(&proof.prod_com, &rd.s_r);
        // s6=0 => no "- c*s6" term

        // NEW u7 = (sum_j s_attr_j G_j + s_zeta G) - c * Com
        let sum_attrGj: Point = params.G_vec[..n]
            .par_iter()
            .zip(rd.s_attrs.par_iter())
            .map(|(Gj, aj)| smul(Gj, aj))
            .reduce(Point::zero, |acc, p| acc + p);
        let mut u7 = sum_attrGj + smul(&pp.G, &rd.s_zeta);
        u7 -= smul(&proof.com, &rd.c);

        all_u.push((u1,u2,u3,u4,u5,u6,u7));

        // (Optional) you can early-check here that all_u[i] hash will be tested later.
        let _ = i;
    }

    // Now check Fischlin hash condition for each round i
    for i in 0..R_par {
        let rd = &proof.rounds[i];
        let work = fischlin_hash_req(
            nizkctx, W_work,
            &s1,&s2,&s3,&s4,&s5,&s6,&s7,
            &all_u,
            i,
            &rd.c,
            rd
        );
        if work != 0 {
            return false;
        }
    }

    true
}
