use ark_ff::{PrimeField, Zero};
use ark_serialize::CanonicalSerialize;
use ark_std::rand::{CryptoRng, RngCore};
use ark_std::UniformRand;
use sha2::{Digest, Sha256};
use rayon::prelude::*;
use ark_std::rand::{SeedableRng, rngs::StdRng};

use crate::mkvak::mkvak::{IssuerPublic, PublicParams};
use crate::saga::bbs_saga::{ smul, Params as VkaParams, Point, Scalar };

use ark_std::io::{self, Write};

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

/// A small adapter so we can `serialize_compressed` directly into a Sha256 state
/// without building temporary Vec<u8> buffers.
struct HashWriter<'a> {
    h: &'a mut Sha256,
}
impl<'a> Write for HashWriter<'a> {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        self.h.update(buf);
        Ok(buf.len())
    }
    fn flush(&mut self) -> io::Result<()> { Ok(()) }
}

#[inline]
fn absorb_point(h: &mut Sha256, p: &Point) {
    let mut w = HashWriter { h };
    p.serialize_compressed(&mut w).unwrap();
}

#[inline]
fn absorb_scalar(h: &mut Sha256, x: &Scalar) {
    let mut w = HashWriter { h };
    x.serialize_compressed(&mut w).unwrap();
}

/// Returns true iff digest interpreted as u64 (little-endian from first 8 bytes)
/// is 0 mod W.
///
/// Fast-path when W is power-of-two: check low bits via mask.
#[inline]
fn digest_is_zero_mod_w(digest32: &[u8; 32], W: u64) -> bool {
    debug_assert!(W >= 2);
    let mut tmp = [0u8; 8];
    tmp.copy_from_slice(&digest32[..8]);
    let v = u64::from_le_bytes(tmp);

    if W.is_power_of_two() {
        (v & (W - 1)) == 0
    } else {
        (v % W) == 0
    }
}

/// Build the base hasher for the *common prefix* of Fischlin:
/// ProtName || nizkctx || derived_statement (s1..s7) || all_u (all announcements)
///
/// This corresponds exactly to your old fischlin_hash_req transcript *up to* the round index.
fn build_req_base_hasher(
    nizkctx: &[u8],
    // derived statement
    s1: &Point, s2: &Point, s3: &Point, s4: &Point, s5: &Point, s6: &Point, s7: &Point,
    // all announcements for all rounds
    all_u: &[(Point, Point, Point, Point, Point, Point, Point)],
) -> Sha256 {
    let mut h = Sha256::new();

    h.update(PROT_NAME_REQ_FISCHLIN);
    h.update(nizkctx);

    // derived statement (s1..s7)
    absorb_point(&mut h, s1);
    absorb_point(&mut h, s2);
    absorb_point(&mut h, s3);
    absorb_point(&mut h, s4);
    absorb_point(&mut h, s5);
    absorb_point(&mut h, s6);
    absorb_point(&mut h, s7);

    // all announcements (binds all rounds together)
    for (u1,u2,u3,u4,u5,u6,u7) in all_u.iter() {
        absorb_point(&mut h, u1);
        absorb_point(&mut h, u2);
        absorb_point(&mut h, u3);
        absorb_point(&mut h, u4);
        absorb_point(&mut h, u5);
        absorb_point(&mut h, u6);
        absorb_point(&mut h, u7);
    }

    h
}

/// Hash used in Fischlin rounds:
/// H(ProtName, ctx, derived_statement, all_announcements, i, c_i, s_i) mod W
///
/// Optimized version: takes a precomputed base hasher and only appends i, c_i, and s_i.
#[inline]
fn fischlin_accepts_from_base(
    base: &Sha256,
    W: u64,
    i: usize,
    c_i: &Scalar,
    s_i: &ReqProofRound,
) -> bool {
    // round index i (keep exact encoding: u32 little-endian)
    let mut h_i = base.clone();
    h_i.update(&(i as u32).to_le_bytes());

    // append c_i and full response vector
    absorb_scalar(&mut h_i, c_i);

    absorb_scalar(&mut h_i, &s_i.s_s);

    for x in s_i.s_attrs.iter()    { absorb_scalar(&mut h_i, x); }
    for x in s_i.s_xi_prime.iter() { absorb_scalar(&mut h_i, x); }

    absorb_scalar(&mut h_i, &s_i.s_bar_x0);
    absorb_scalar(&mut h_i, &s_i.s_bar_nu);
    absorb_scalar(&mut h_i, &s_i.s_r);
    absorb_scalar(&mut h_i, &s_i.s_e);

    for x in s_i.s_xi.iter()       { absorb_scalar(&mut h_i, x); }

    absorb_scalar(&mut h_i, &s_i.s_eta);
    absorb_scalar(&mut h_i, &s_i.s_zeta);
    absorb_scalar(&mut h_i, &s_i.s_prod);
    absorb_scalar(&mut h_i, &s_i.s_prod_prime);

    let dig = h_i.finalize();
    let mut d32 = [0u8; 32];
    d32.copy_from_slice(&dig[..]);
    digest_is_zero_mod_w(&d32, W)
}

/// Prover for cmzcpzrec (request proof) using randomized Fischlin transform.
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

    // 1) Pre-sample per-round RNG seeds (sequential, cheap, keeps determinism)
    let mut seeds: Vec<[u8; 32]> = Vec::with_capacity(R_par);
    for _ in 0..R_par {// for _i in 0..R_par {
        let mut seed = [0u8; 32];//     let a_s = Scalar::rand(rng);
        rng.fill_bytes(&mut seed);//     let a_attrs: Vec<Scalar>    = (0..n).map(|_| Scalar::rand(rng)).collect();
        seeds.push(seed);//     let a_xi_prime: Vec<Scalar> = (0..n).map(|_| Scalar::rand(rng)).collect();
    }

    // 2) Parallelize the rounds: each round uses its own StdRng
    let per_round: Vec<(
        (Point, Point, Point, Point, Point, Point, Point), // announcements (t1..t7)
        RoundA
    )> = seeds
        .par_iter()
        .map(|seed| {
            let mut lrng = StdRng::from_seed(*seed);

            let a_s = Scalar::rand(&mut lrng);
            let a_attrs: Vec<Scalar>    = (0..n).map(|_| Scalar::rand(&mut lrng)).collect();
            let a_xi_prime: Vec<Scalar> = (0..n).map(|_| Scalar::rand(&mut lrng)).collect();
            let a_bar_x0 = Scalar::rand(&mut lrng);
            let a_bar_nu = Scalar::rand(&mut lrng);
            let a_r = Scalar::rand(&mut lrng);
            let a_e = Scalar::rand(&mut lrng);
            let a_xi: Vec<Scalar>       = (0..l).map(|_| Scalar::rand(&mut lrng)).collect();
            let a_eta = Scalar::rand(&mut lrng);
            let a_zeta = Scalar::rand(&mut lrng);
            let a_prod = Scalar::rand(&mut lrng);
            let a_prod_prime = Scalar::rand(&mut lrng);

            let t1 = -smul(&params.G_vec[n],   &a_xi[n])
                + smul(&params.G, &a_bar_x0)
                + smul(&ipk.E,    &a_bar_nu);

            let t2 = -smul(&params.G_vec[n + 1], &a_xi[n + 1])
                + smul(&params.G, &a_bar_nu);

            // IMPORTANT: since we parallelize outside, use iter() inside to avoid nested rayon overhead
            let sum_Ca: Point = C_j_vec[..n]
                .iter()
                .zip(a_attrs.iter())
                .map(|(Cj, a)| smul(Cj, a))
                .fold(Point::zero(), |acc, p| acc + p);

            let sum_Gxi: Point = params.G_vec[..n]
                .iter()
                .zip(a_xi_prime.iter())
                .map(|(Gj, xi)| smul(Gj, xi))
                .fold(Point::zero(), |acc, p| acc + p);

            let t3 = smul(&pp.G, &a_s) + sum_Ca - sum_Gxi;

            let sum_Yxi: Point = ipk.saga_pk.Y_vec[..l]
                .iter()
                .zip(a_xi.iter())
                .map(|(Yj, xi)| smul(Yj, xi))
                .fold(Point::zero(), |acc, p| acc + p);

            let mut t4 = smul(&ipk.saga_pk.X, &a_r);
            t4 -= smul(&vka_pres.C_A, &a_e);
            t4 += smul(&pp.G, &a_prod);
            t4 -= sum_Yxi;

            let t5 = smul(&pp.G, &a_e) + smul(&pp.H, &a_eta);

            let t6 = smul(&pp.G, &a_prod) + smul(&pp.H, &a_prod_prime) - smul(&prod_com, &a_r);

            // t7 = sum_j a_attr_j * G_j + a_zeta * G
            let sum_aGj: Point = params.G_vec[..n]
                .iter()
                .zip(a_attrs.iter())
                .map(|(Gj, aj)| smul(Gj, aj))
                .fold(Point::zero(), |acc, p| acc + p);

            let t7 = sum_aGj + smul(&pp.G, &a_zeta);

            let ann = (t1, t2, t3, t4, t5, t6, t7);

            let round_a = RoundA {
                a_s,
                a_attrs,
                a_xi_prime,
                a_bar_x0,
                a_bar_nu,
                a_r,
                a_e,
                a_xi,
                a_eta,
                a_zeta,
                a_prod,
                a_prod_prime,
            };

            (ann, round_a)
        })
        .collect();

    // 3) Unzip into your two vectors (same order as seeds, deterministic)
    let (announcements, a_rounds): (Vec<_>, Vec<_>) = per_round.into_iter().unzip();

    // Precompute witness-derived xi'_j once (constant across rounds)
    let xi_prime_wit: Vec<Scalar> = attrs
        .iter()
        .zip(xi_vec.iter().take(n))
        .map(|(aj, xij)| (*aj) * (*xij))
        .collect();

    // Build base hasher once: ProtName||ctx||S||all_u
    let base = build_req_base_hasher(
        nizkctx,
        &s1,&s2,&s3,&s4,&s5,&s6,&s7,
        &announcements,
    );

    // --- Step 2: for each round i, search random c^(i) until hash==0 ---
    let max_tries_per_round: usize = (W_work as usize) * 64; // conservative cap

    let mut rounds: Vec<ReqProofRound> = Vec::with_capacity(R_par);



    // --- before the loop ---
    let xi_prime_wit: Vec<Scalar> = attrs
        .iter()
        .zip(xi_vec.iter())
        .map(|(aj, xij)| *aj * *xij)
        .collect();

// seeds for each round's RNG
    let mut seeds: Vec<[u8; 32]> = Vec::with_capacity(R_par);
    for _ in 0..R_par {
        let mut seed = [0u8; 32];
        rng.fill_bytes(&mut seed);
        seeds.push(seed);
    }

    // --- parallel outer: compute one accepting round per i ---
    let rounds: Vec<ReqProofRound> = (0..R_par)
        .into_par_iter()
        .map(|i| {
            let a = &a_rounds[i];
            let mut lrng = StdRng::from_seed(seeds[i]);

            for _try in 0..max_tries_per_round {
                let c_i = Scalar::rand(&mut lrng);

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

                if fischlin_accepts_from_base(&base, W_work, i, &round.c, &round) {
                    return round;
                }
            }

            panic!("Fischlin search failed at round {i}: increase max_tries_per_round or adjust W_work/R_par");
        })
        .collect();

    ReqProofFischlin { prod_com, com, rounds }
}

/// Verifier for cmzcpzrec (request proof) using randomized Fischlin transform.
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

    // recompute all accepting announcements u^(i)
    let mut all_u: Vec<(Point,Point,Point,Point,Point,Point,Point)> = Vec::with_capacity(R_par);

    for (i, rd) in proof.rounds.iter().enumerate() {
        if rd.s_attrs.len() != n || rd.s_xi_prime.len() != n || rd.s_xi.len() != l {
            return false;
        }

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

        // u7 = (sum_j s_attr_j G_j + s_zeta G) - c * Com
        let sum_attrGj: Point = params.G_vec[..n]
            .par_iter()
            .zip(rd.s_attrs.par_iter())
            .map(|(Gj, aj)| smul(Gj, aj))
            .reduce(Point::zero, |acc, p| acc + p);
        let mut u7 = sum_attrGj + smul(&pp.G, &rd.s_zeta);
        u7 -= smul(&proof.com, &rd.c);

        all_u.push((u1,u2,u3,u4,u5,u6,u7));

        let _ = i;
    }

    // Build base hasher once: ProtName||ctx||S||all_u
    let base = build_req_base_hasher(
        nizkctx,
        &s1,&s2,&s3,&s4,&s5,&s6,&s7,
        &all_u,
    );

    // Now check Fischlin hash condition for each round i
    for i in 0..R_par {
        let rd = &proof.rounds[i];
        if !fischlin_accepts_from_base(&base, W_work, i, &rd.c, rd) {
            return false;
        }
    }

    true
}