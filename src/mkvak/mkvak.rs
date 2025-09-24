use ark_ff::{PrimeField, Zero};
use ark_std::rand::{CryptoRng, RngCore};
use ark_std::UniformRand;
use ark_serialize::CanonicalSerialize;
use sha2::{Digest, Sha256};
use crate::vka::bbs_vka::{
    smul, vka_keygen, vka_mac, vka_setup, Params as VkaParams, Point, Scalar, SecretKey as VkaSK,
    PublicKey as VkaPK, Signature as VkaSig, VkaError,
};

const PROT_NAME_REQ: &[u8] = b"AKVAC-REQ";

/// Public parameters for AKVAC
#[derive(Clone, Debug)]
pub struct PublicParams {
    /// Group base (G) carried from VKA params
    pub G: Point,
    /// Random presentation base H
    pub H: Point,
    /// VKA params with ℓ = n + 2; contains:
    ///   - pp_vka = G_0
    ///   - G_vec = [G_1..G_{n+2}]
    pub vka_params: VkaParams,
}

#[derive(thiserror::Error, Debug)]
pub enum AkvacError {
    #[error("length mismatch: expected {expected}, got {got}")]
    LengthMismatch { expected: usize, got: usize },
    #[error("VKA error: {0}")]
    Vka(#[from] VkaError),
}

/// AKVAC issuer key material
#[derive(Clone, Debug)]
pub struct IssuerSecret {
    pub vka_sk: VkaSK,
    pub e: Scalar,
}

#[derive(Clone, Debug)]
pub struct IssuerPublic {
    pub vka_pk: VkaPK,
    pub E: Point, // E = e * G
}

/// AKVAC verifier key material
#[derive(Clone, Debug)]
pub struct VerifierSecret {
    /// x_0..x_n
    pub x_0_to_x_n: Vec<Scalar>,
}

#[derive(Clone, Debug)]
pub struct VerifierPublic {
    /// (X_1..X_n, X_0, Z_0)
    pub X_1_to_n: Vec<Point>,
    pub X_0: Point,
    pub Z_0: Point,
    /// τ (VKA MAC over X_1..X_n, X_0, Z_0)
    pub tau: VkaSig,
}

#[derive(Clone, Debug)]
pub struct ReceiveCredState {
    pub s: Scalar,
    pub bar_x0: Scalar,
    pub bar_X0: Point,
    pub bar_Z0: Point,
    // not strictly required by the LaTeX to be stored;
    // keeping attrs here is handy for the final output:
    pub attrs: Vec<Scalar>,
}

#[derive(Clone, Debug)]
pub struct CredReq {
    pub vka_pres: crate::vka::bbs_vka::VkaPres,
    pub C_j_vec: Vec<Point>,
    // C_1..C_{n+2}
    pub bar_X0: Point,
    pub bar_Z0: Point,
    pub C_attr: Point,
    pub nizk: ReqProof,
}

#[derive(Clone, Debug)]
pub struct BlindCred {
    pub bar_U: Point,
    pub bar_V: Point,
    pub nizk: Proof32, // placeholder proof for "cmzcpzissue" // TODO: real proof
}

#[derive(Clone, Debug)]
pub struct Credential {
    pub U: Point,
    pub V: Point,
    pub attrs: Vec<Scalar>,
}

// simple 32-byte digest proof
#[derive(Clone, Debug)]
pub struct Proof32 {
    pub digest: [u8; 32],
}

#[derive(Clone, Debug)]
pub struct Presentation {
    pub tilde_U: Point,
    pub Z: Point,
    pub C_v: Point,
    pub C_j_vec: Vec<Point>,
    // C_1..C_n
    pub nizk: Proof32,        // cmzcpzshow
}

/// Schnorr-style NIZK for AKVAC request (cmzcpzrec)
#[derive(Clone, Debug)]
pub struct ReqProof {
    pub c: Scalar,

    // responses
    pub s_s: Scalar,                  // for s
    pub s_attrs: Vec<Scalar>,         // for a_j, j=1..n
    pub s_xi_prime: Vec<Scalar>,      // for xi'_j = a_j * xi_j, j=1..n
    pub s_bar_x0: Scalar,             // for \bar x_0
    pub s_bar_nu: Scalar,             // for \bar \nu
    pub s_r: Scalar,                  // for r
    pub s_e: Scalar,                  // for e  (BBS signature scalar)
    pub s_xi: Vec<Scalar>,            // for xi_j, j=1..n+2  (from VKA present)
    pub s_eta: Scalar,                // for \eta
    pub s_prod: Scalar,               // for prod   = e * r
    pub s_prod_prime: Scalar,         // for prod'  = r * \eta

    // include ProdCom in the proof (part of the statement hash)
    pub prod_com: Point,              // eG + eta H
}

#[inline]
fn hash_to_scalar(bytes: &[u8]) -> Scalar {
    let d = Sha256::digest(bytes);
    Scalar::from_le_bytes_mod_order(&d)
}

fn hash_challenge_req(
    // derived statement (6 group elements):
    s1: &Point, s2: &Point, s3: &Point, s4: &Point, s5: &Point, s6: &Point,
    // accepting announcement (6 group elements):
    t1: &Point, t2: &Point, t3: &Point, t4: &Point, t5: &Point, t6: &Point,
) -> Scalar {
    let mut buf = Vec::new();
    buf.extend_from_slice(PROT_NAME_REQ);

    // statement
    s1.serialize_compressed(&mut buf).unwrap();
    s2.serialize_compressed(&mut buf).unwrap();
    s3.serialize_compressed(&mut buf).unwrap();
    s4.serialize_compressed(&mut buf).unwrap();
    s5.serialize_compressed(&mut buf).unwrap();
    s6.serialize_compressed(&mut buf).unwrap();

    // announcement
    t1.serialize_compressed(&mut buf).unwrap();
    t2.serialize_compressed(&mut buf).unwrap();
    t3.serialize_compressed(&mut buf).unwrap();
    t4.serialize_compressed(&mut buf).unwrap();
    t5.serialize_compressed(&mut buf).unwrap();
    t6.serialize_compressed(&mut buf).unwrap();

    hash_to_scalar(&buf)
}

/// Prover for cmzcpzrec (request proof)
fn nizk_prove_req<R: RngCore + CryptoRng>(
    rng: &mut R,
    pp: &PublicParams,
    ipk: &IssuerPublic,                  // for E and (X, Y_j)
    params: &VkaParams,                  // for G, G_j
    // public statement inputs:
    vka_pres: &crate::vka::bbs_vka::VkaPres, // has C_A, T
    C_j_vec: &[Point],                   // C_1..C_{n+2}
    bar_X0: &Point,
    bar_Z0: &Point,
    C_attr: &Point,
    // secret witness inputs:
    s: &Scalar,
    attrs: &[Scalar],                    // a_j, j=1..n
    bar_x0: &Scalar,
    bar_nu: &Scalar,
    r: &Scalar,
    e: &Scalar,                          // BBS signature e
    xi_vec: &[Scalar],                   // xi_1..xi_{n+2}
) -> ReqProof {
    let l = params.G_vec.len();                   // l = n + 2
    let n = l - 2;
    debug_assert_eq!(C_j_vec.len(), l);
    debug_assert_eq!(attrs.len(), n);
    debug_assert_eq!(xi_vec.len(), l);

    // prod commitments
    let eta = Scalar::rand(rng);
    let prod_com = smul(&pp.G, e) + smul(&pp.H, &eta);
    let prod = *e * *r;
    let prod_prime = *r * eta;

    // 1) randomizers (a-values)
    let a_s = Scalar::rand(rng);
    let a_attrs: Vec<Scalar>       = (0..n).map(|_| Scalar::rand(rng)).collect();
    let a_xi_prime: Vec<Scalar>    = (0..n).map(|_| Scalar::rand(rng)).collect();
    let a_bar_x0 = Scalar::rand(rng);
    let a_bar_nu = Scalar::rand(rng);
    let a_r = Scalar::rand(rng);
    let a_e = Scalar::rand(rng);
    let a_xi: Vec<Scalar>          = (0..l).map(|_| Scalar::rand(rng)).collect();
    let a_eta = Scalar::rand(rng);
    let a_prod = Scalar::rand(rng);
    let a_prod_prime = Scalar::rand(rng);

    // 2) announcement T = φ(a)
    // T1 = - a_xi_{n+1} G_{n+1} + a_bar_x0 G + a_bar_nu E
    let t1 = -smul(&params.G_vec[n], &a_xi[n]) + smul(&params.G, &a_bar_x0) + smul(&ipk.E, &a_bar_nu);
    // T2 = - a_xi_{n+2} G_{n+2} + a_bar_nu G
    let t2 = -smul(&params.G_vec[n+1], &a_xi[n+1]) + smul(&params.G, &a_bar_nu);
    // T3 = a_s G + sum_j a_j C_j - sum_j a_xi'_j G_j  (j in 1..n; our arrays are 0..n-1)
    let mut t3 = smul(&pp.G, &a_s);
    for j in 0..n {
        t3 += smul(&C_j_vec[j], &a_attrs[j]);
        t3 -= smul(&params.G_vec[j], &a_xi_prime[j]);
    }
    // T4 = a_r X - a_e C_A + a_prod G - sum_{j=1..l} a_xi_j Y_j
    let mut t4 = smul(&ipk.vka_pk.X, &a_r);
    t4 -= smul(&vka_pres.C_A, &a_e);
    t4 += smul(&pp.G, &a_prod);
    for j in 0..l {
        t4 -= smul(&ipk.vka_pk.Y_vec[j], &a_xi[j]);
    }
    // T5 = a_e G + a_eta H
    let t5 = smul(&pp.G, &a_e) + smul(&pp.H, &a_eta);
    // T6 = a_prod G + a_prod' H - a_r * ProdCom
    let t6 = smul(&pp.G, &a_prod) + smul(&pp.H, &a_prod_prime) - smul(&prod_com, &a_r);

    // 3) derive statement image S = (S1..S6)
    let s1 = *bar_X0 - C_j_vec[n];       // \bar X_0 - C_{n+1}
    let s2 = *bar_Z0 - C_j_vec[n+1];     // \bar Z_0 - C_{n+2}
    let s3 = *C_attr;                     // C_attr
    let s4 = vka_pres.T;                  // T
    let s5 = prod_com;                    // ProdCom = eG + eta H
    let s6 = Point::zero();               // 0

    // 4) FS challenge
    let c = hash_challenge_req(&s1, &s2, &s3, &s4, &s5, &s6, &t1, &t2, &t3, &t4, &t5, &t6);

    // 5) responses s = a + c * witness
    let s_s = a_s + c * *s;
    let mut s_attrs: Vec<Scalar> = Vec::with_capacity(n);
    let mut s_xi_prime: Vec<Scalar> = Vec::with_capacity(n);
    for j in 0..n {
        s_attrs.push(a_attrs[j] + c * attrs[j]);
        // xi'_j = a_j * xi_j  (witness value)
        let xi_prime_j = attrs[j] * xi_vec[j];
        s_xi_prime.push(a_xi_prime[j] + c * xi_prime_j);
    }
    let s_bar_x0 = a_bar_x0 + c * *bar_x0;
    let s_bar_nu = a_bar_nu + c * *bar_nu;
    let s_r = a_r + c * *r;
    let s_e = a_e + c * *e;

    let mut s_xi: Vec<Scalar> = Vec::with_capacity(l);
    for j in 0..l {
        s_xi.push(a_xi[j] + c * xi_vec[j]);
    }

    let s_eta = a_eta + c * eta;
    let s_prod = a_prod + c * prod;
    let s_prod_prime = a_prod_prime + c * prod_prime;

    ReqProof {
        c,
        s_s,
        s_attrs,
        s_xi_prime,
        s_bar_x0,
        s_bar_nu,
        s_r,
        s_e,
        s_xi,
        s_eta,
        s_prod,
        s_prod_prime,
        prod_com,
    }
}


/// Verifier for cmzcpzrec
fn nizk_verify_req(
    pp: &PublicParams,
    ipk: &IssuerPublic,
    params: &VkaParams,
    vka_pres: &crate::vka::bbs_vka::VkaPres,
    C_j_vec: &[Point],
    bar_X0: &Point,
    bar_Z0: &Point,
    C_attr: &Point,
    proof: &ReqProof,
) -> bool {
    let l = params.G_vec.len();
    let n = l - 2;
    if C_j_vec.len() != l { return false; }
    if proof.s_attrs.len() != n || proof.s_xi_prime.len() != n || proof.s_xi.len() != l { return false; }

    // Statement image S
    let s1 = *bar_X0 - C_j_vec[n];
    let s2 = *bar_Z0 - C_j_vec[n+1];
    let s3 = *C_attr;
    let s4 = vka_pres.T;
    let s5 = proof.prod_com;
    let s6 = Point::zero();

    // φ(s) - c S  (component-wise)
    // U1 = - s_xi_{n+1} G_{n+1} + s_bar_x0 G + s_bar_nu E  - c*s1
    let mut u1 = -smul(&params.G_vec[n], &proof.s_xi[n]);
    u1 += smul(&params.G, &proof.s_bar_x0);
    u1 += smul(&ipk.E, &proof.s_bar_nu);
    u1 -= smul(&s1, &proof.c);

    // U2 = - s_xi_{n+2} G_{n+2} + s_bar_nu G  - c*s2
    let mut u2 = -smul(&params.G_vec[n+1], &proof.s_xi[n+1]);
    u2 += smul(&params.G, &proof.s_bar_nu);
    u2 -= smul(&s2, &proof.c);

    // U3 = s_s G + Σ s_attrs_j C_j - Σ s_xi'_j G_j  - c*s3
    let mut u3 = smul(&pp.G, &proof.s_s);
    for j in 0..n {
        u3 += smul(&C_j_vec[j], &proof.s_attrs[j]);
        u3 -= smul(&params.G_vec[j], &proof.s_xi_prime[j]);
    }
    u3 -= smul(&s3, &proof.c);

    // U4 = s_r X - s_e C_A + s_prod G - Σ s_xi_j Y_j  - c*s4
    let mut u4 = smul(&ipk.vka_pk.X, &proof.s_r);
    u4 -= smul(&vka_pres.C_A, &proof.s_e);
    u4 += smul(&pp.G, &proof.s_prod);
    for j in 0..l {
        u4 -= smul(&ipk.vka_pk.Y_vec[j], &proof.s_xi[j]);
    }
    u4 -= smul(&s4, &proof.c);

    // U5 = s_e G + s_eta H  - c*s5
    let mut u5 = smul(&pp.G, &proof.s_e) + smul(&pp.H, &proof.s_eta);
    u5 -= smul(&s5, &proof.c);

    // U6 = s_prod G + s_prod' H - s_r * ProdCom  - c*s6 (s6=0)
    let u6 = smul(&pp.G, &proof.s_prod) + smul(&pp.H, &proof.s_prod_prime) - smul(&proof.prod_com, &proof.s_r);

    // Recompute challenge
    let c_prime = hash_challenge_req(&s1, &s2, &s3, &s4, &s5, &s6, &u1, &u2, &u3, &u4, &u5, &u6);
    c_prime == proof.c
}


// ------------------------------------
// Placeholder proof helpers (INSECURE)
// ------------------------------------
/// Hash points and scalars into a 32-byte digest
fn hash_points_scalars(points: &[Point], scalars: &[Scalar]) -> [u8; 32] {
    let mut buf = Vec::new();
    for p in points {
        p.serialize_compressed(&mut buf).unwrap();
    }
    for s in scalars {
        s.serialize_compressed(&mut buf).unwrap();
    }
    let d = Sha256::digest(&buf);
    let mut out = [0u8; 32];
    out.copy_from_slice(&d[..]);
    out
}

// cmzcpzrec: prove correctness of (C_j, bar_X0, bar_Z0, C_attr) & possession of VKA witness
fn prove_cmzcpzrec(
    vkapres: &crate::vka::bbs_vka::VkaPres,
    C_j_vec: &[Point],
    bar_X0: &Point,
    bar_Z0: &Point,
    C_attr: &Point,
    witness_scalars: &[Scalar],
) -> Proof32 {
    let mut points = Vec::new();
    points.extend(C_j_vec.iter().cloned());
    points.push(*bar_X0);
    points.push(*bar_Z0);
    points.push(*C_attr);
    points.push(vkapres.C_A);
    points.push(vkapres.T);
    Proof32 {
        digest: hash_points_scalars(&points, witness_scalars),
    }
}

fn verify_cmzcpzrec(
    vkapres: &crate::vka::bbs_vka::VkaPres,
    C_j_vec: &[Point],
    bar_X0: &Point,
    bar_Z0: &Point,
    C_attr: &Point,
    proof: &Proof32,
) -> bool {
    let mut points = Vec::new();
    points.extend(C_j_vec.iter().cloned());
    points.push(*bar_X0);
    points.push(*bar_Z0);
    points.push(*C_attr);
    points.push(vkapres.C_A);
    points.push(vkapres.T);
    hash_points_scalars(&points, &[]) == proof.digest
}

// cmzcpzissue: prove knowledge of (e, u) in relations to (E, bar_U, bar_V, …)
fn prove_cmzcpzissue(
    E: &Point,
    bar_U: &Point,
    bar_V: &Point,
    bar_X0: &Point,
    bar_Z0: &Point,
    C_attr: &Point,
    e: &Scalar,
    u: &Scalar,
) -> Proof32 {
    let points = [*E, *bar_U, *bar_V, *bar_X0, *bar_Z0, *C_attr];
    let scalars = [*e, *u];
    Proof32 {
        digest: hash_points_scalars(&points, &scalars),
    }
}

fn verify_cmzcpzissue(
    E: &Point,
    bar_U: &Point,
    bar_V: &Point,
    bar_X0: &Point,
    bar_Z0: &Point,
    C_attr: &Point,
    proof: &Proof32,
) -> bool {
    let points = [*E, *bar_U, *bar_V, *bar_X0, *bar_Z0, *C_attr];
    hash_points_scalars(&points, &[]) == proof.digest
}

// ------------------------------------
// Helper: vfcred (wraps VKA.verify)
// ------------------------------------
fn vfcred(
    isk: &IssuerSecret,
    pp: &PublicParams,
    vkapres: &crate::vka::bbs_vka::VkaPres,
    C_j_vec: &[Point],
) -> Result<bool, AkvacError> {
    use crate::vka::bbs_vka::pres_verify;
    Ok(pres_verify(&isk.vka_sk, &pp.vka_params, vkapres, C_j_vec)?)
}


/// AKVAC.setup(λ, 1^n)
/// Internally sets ℓ = n + 2 for the underlying VKA.
pub fn akvac_setup<R: RngCore + CryptoRng>(rng: &mut R, n: usize) -> PublicParams {
    let l = n + 2;
    let vka_params = vka_setup(rng, l);

    // Sample H as a random multiple of G (prime-order group)
    let H = smul(&vka_params.G, &Scalar::rand(rng));

    PublicParams {
        G: vka_params.G,
        H: H,
        vka_params,
    }
}


/// AKVAC.issuerkg()
pub fn issuer_keygen<R: RngCore + CryptoRng>(
    rng: &mut R,
    pp: &PublicParams,
) -> (IssuerSecret, IssuerPublic) {
    let (vka_sk, vka_pk) = vka_keygen(rng, &pp.vka_params);

    let e = Scalar::rand(rng);
    let E = smul(&pp.G, &e);

    (
        IssuerSecret { vka_sk, e },
        IssuerPublic { vka_pk, E },
    )
}


/// AKVAC.verifierkg(isk, ipk)
/// Builds (X_1..X_n, X_0, Z_0) and requests a VKA MAC τ from the issuer.
pub fn verifier_keygen<R: RngCore + CryptoRng>(
    rng: &mut R,
    pp: &PublicParams,
    isk: &IssuerSecret,
    ipk: &IssuerPublic,
) -> Result<(VerifierSecret, VerifierPublic), AkvacError> {
    // ℓ = n + 2  ⇒  n = ℓ - 2
    let l = pp.vka_params.G_vec.len();
    assert!(l >= 2, "VKA was not set with ℓ = n + 2");
    let n = l - 2;

    // Sample x_0..x_n, ν, x_r
    let mut x_0_to_x_n = Vec::with_capacity(n + 1);
    for _ in 0..=n {
        x_0_to_x_n.push(Scalar::rand(rng));
    }
    assert_eq!(x_0_to_x_n.len(), n + 1);
    let v = Scalar::rand(rng);

    // Compute X_i = x_i * G for i=1..n
    let mut X_1_to_n = Vec::with_capacity(n);
    for i in 1..=n {
        X_1_to_n.push(smul(&pp.G, &x_0_to_x_n[i]));
    }
    assert_eq!(X_1_to_n.len(), n);

    // Z_0 = ν G
    let Z_0 = smul(&pp.G, &v);

    // X_0 = x_0 G + ν E
    // let X_0 = smul(&pp.G, &x_vec[0]) + smul(&ipk.E, &Scalar::from(1u64)); // E already has e folded into it
    // let X_0 = X_0 + smul(&pp.G, &(v * isk.e)); // equivalently: x0*G + ν*(eG) = x0*G + (νe)*G
    let mut X_0 = smul(&pp.G, &x_0_to_x_n[0]);
    X_0 += smul(&pp.G, &(v * isk.e)); // equivalently: x0*G + ν*(eG) = x0*G + (νe)*G


    // Assemble messages for VKA MAC in the order: (X_1..X_n, X_0, Z_0)
    let mut msgs = X_1_to_n.clone();
    msgs.push(X_0);
    msgs.push(Z_0);

    // Ask issuer to MAC (using issuer's VKA secret)
    let tau = vka_mac(rng, &isk.vka_sk, &pp.vka_params, &msgs, &ipk.vka_pk)?;

    let vsk = VerifierSecret { x_0_to_x_n: x_0_to_x_n };
    let vpk = VerifierPublic {
        X_1_to_n: X_1_to_n,
        X_0: X_0,
        Z_0: Z_0,
        tau: tau,
    };
    Ok((vsk, vpk))
}


/// Client side (verifier) prepares a blinded request.
/// attrs: a_1..a_n in the paper; commitment C_attr = sum a_j X_j + s G
pub fn receive_cred_1<R: RngCore + CryptoRng>(
    rng: &mut R,
    pp: &PublicParams,
    ipk: &IssuerPublic,
    vpk: &VerifierPublic,
    attrs: &[Scalar],
) -> Result<(ReceiveCredState, CredReq), AkvacError> {
    // n = ℓ - 2
    let l = pp.vka_params.G_vec.len();
    let n = l - 2;
    if attrs.len() != n {
        return Err(AkvacError::LengthMismatch {
            expected: n,
            got: attrs.len(),
        });
    }

    // Present the issuer MAC τ on (X_1..X_n, X_0, Z_0)
    // messages in the same order as when it was MACed
    let mut msgs = vpk.X_1_to_n.clone();
    msgs.push(vpk.X_0);
    msgs.push(vpk.Z_0);

    let vka_pres = crate::vka::bbs_vka::vka_present(
        rng,
        &ipk.vka_pk,
        &pp.vka_params,
        &vpk.tau,
        &msgs,
    )?;

    // Sample s, bar_x0, bar_v and compute the blinding of (X_0, Z_0)
    let s = Scalar::rand(rng);
    let bar_x0 = Scalar::rand(rng);
    let bar_v = Scalar::rand(rng);

    // bar_X0 = X_0 + bar_x0 * G + bar_v * E
    let bar_X0 = vpk.X_0 + smul(&pp.G, &bar_x0) + smul(&ipk.E, &bar_v);
    // bar_Z0 = Z_0 + bar_v * G
    let bar_Z0 = vpk.Z_0 + smul(&pp.G, &bar_v);

    // Commitment to attributes: C_attr = sum_j attr_j * X_j + s G
    let mut C_attr = smul(&pp.G, &s);
    for (a, Xj) in attrs.iter().zip(vpk.X_1_to_n.iter()) {
        C_attr += smul(Xj, a);
    }

    // Build C_j = M_j + ξ_j G_j were returned already in pres.C_j_vec
    // Assemble statement and placeholder proof
    assert_eq!(vka_pres.C_j_vec.len(), n + 2);
    let stmt_Cs = vka_pres.C_j_vec.clone();

    // Witness scalars fed into the placeholder hash:
    // include s, bar_x0, bar_v, r, e, xi_1..xi_{n+2}, and (a_j * xi_j) if you like
    let mut witness_scalars = vec![s, bar_x0, bar_v, vka_pres.witness_r, vka_pres.witness_e];
    witness_scalars.extend_from_slice(&vka_pres.xi_vec);

    // TODO: NIZK proof
    // let nizk = prove_cmzcpzrec(&vka_pres.vka_pres, &stmt_Cs, &bar_X0, &bar_Z0, &C_attr, &witness_scalars);
    let nizk = nizk_prove_req(
        rng, pp, ipk, &pp.vka_params,
        &vka_pres.vka_pres,        // has C_A, T
        &stmt_Cs,                  // C_1..C_{n+2}
        &bar_X0, &bar_Z0, &C_attr,
        &s, &attrs, &bar_x0, &bar_v,            // note: bar_v is \bar\nu
        &vka_pres.witness_r, &vka_pres.witness_e,
        &vka_pres.xi_vec,
    );

    let state = ReceiveCredState {
        s: s,
        bar_x0: bar_x0,
        bar_X0: bar_X0,
        bar_Z0: bar_Z0,
        attrs: attrs.to_vec(),
    };

    let credreq = CredReq {
        vka_pres: vka_pres.vka_pres,
        C_j_vec: stmt_Cs,
        bar_X0,
        bar_Z0,
        C_attr,
        nizk,
    };

    Ok((state, credreq))
}


pub fn issue_cred<R: RngCore + CryptoRng>(
    rng: &mut R,
    pp: &PublicParams,
    isk: &IssuerSecret,
    ipk: &IssuerPublic,
    cred_req: &CredReq,
) -> Result<BlindCred, AkvacError> {
    if !nizk_verify_req(
        pp, ipk, &pp.vka_params,
        &cred_req.vka_pres,
        &cred_req.C_j_vec,
        &cred_req.bar_X0,
        &cred_req.bar_Z0,
        &cred_req.C_attr,
        &cred_req.nizk,
    ) {
        println!("AKVAC request proof does not verify");
        return Err(AkvacError::Vka(VkaError::NonInvertible));
    }

    // Verify the VKA presentation (MAC correctness over C_j etc.)
    let verified = vfcred(isk, pp, &cred_req.vka_pres, &cred_req.C_j_vec)?;
    if !verified {
        return Err(AkvacError::Vka(VkaError::NonInvertible));
    } else { println!("VKA presentation verified"); }

    // u ← Z_p,  ȗ = u G,  V̄ = u((X̄0 − e Z̄0) + C_attr)
    let u = Scalar::rand(rng);
    let bar_U = smul(&pp.G, &u);

    // (bar_X0 - e * bar_Z0)
    let x0_part = cred_req.bar_X0 - smul(&cred_req.bar_Z0, &isk.e);
    let bar_V = smul(&(x0_part + cred_req.C_attr), &u);

    // TODO
    // NIZK over (E, Ū, V̄, X̄0, Z̄0, C_attr) with witness (e,u)
    let nizk = prove_cmzcpzissue(&ipk.E, &bar_U, &bar_V, &cred_req.bar_X0, &cred_req.bar_Z0, &cred_req.C_attr, &isk.e, &u);

    Ok(BlindCred { bar_U: bar_U, bar_V: bar_V, nizk: nizk })
}

pub fn receive_cred_2(
    pp: &PublicParams,
    ipk: &IssuerPublic,
    state: &ReceiveCredState,
    credreq: &CredReq,
    blind: &BlindCred,
) -> Result<Credential, AkvacError> {
    // TODO
    // Verify issuer proof (placeholder)
    // if !verify_cmzcpzissue(
    //     &ipk.E,
    //     &blind.bar_U,
    //     &blind.bar_V,
    //     &credreq.bar_X0,
    //     &credreq.bar_Z0,
    //     &credreq.C_attr,
    //     &blind.nizk,
    // ) {
    //     // return Err(AkvacError::Vka(VkaError::NonInvertible));
    //     println!("the dummy proof does not verify");
    // }

    // γ ← Z_p^*,  U = γ Ū,  V = γ ( V̄ − (s − \bar x0) Ū )
    // ensure non-zero gamma
    // let mut gamma = Scalar::rand(&mut ark_std::rand::rngs::OsRng);
    // while gamma.is_zero() {
    //     gamma = Scalar::rand(&mut ark_std::rand::rngs::OsRng);
    // }
    let mut gamma = rand_nonzero(&mut ark_std::rand::rngs::OsRng);

    let U = smul(&blind.bar_U, &gamma);
    let correction = state.s + state.bar_x0;
    let V_inner = blind.bar_V - smul(&blind.bar_U, &correction);
    let V = smul(&V_inner, &gamma);

    Ok(Credential {
        U,
        V,
        attrs: state.attrs.clone(),
    })
}

fn hash_points_scalars_with_ctx(points: &[Point], scalars: &[Scalar], pres_ctx: &[u8]) -> [u8; 32] {
    let mut buf = Vec::new();
    for p in points {
        p.serialize_compressed(&mut buf).unwrap();
    }
    for s in scalars {
        s.serialize_compressed(&mut buf).unwrap();
    }
    buf.extend_from_slice(pres_ctx);
    let d = Sha256::digest(&buf);
    let mut out = [0u8; 32];
    out.copy_from_slice(&d[..]);
    out
}

/// Prover: include witness scalars and pres_ctx in the digest
fn prove_cmzcpzshow(
    X_1_to_n: &[Point],
    tilde_U: &Point,
    tilde_gamma: &Scalar,
    attrs: &[Scalar],
    gamma_js: &[Scalar],
    pres_ctx: &[u8],
) -> Proof32 {
    let mut points = Vec::with_capacity(X_1_to_n.len() + 1);
    points.extend_from_slice(X_1_to_n);
    points.push(*tilde_U);

    // witness order: [tilde_gamma, attrs..., gamma_js...]
    let mut ws: Vec<Scalar> = Vec::with_capacity(1 + attrs.len() + gamma_js.len());
    ws.push(*tilde_gamma);
    ws.extend_from_slice(attrs);
    ws.extend_from_slice(gamma_js);

    Proof32 {
        digest: hash_points_scalars_with_ctx(&points, &ws, pres_ctx),
    }
}


/// Verifier: only statement + ctx (INSECURE placeholder)
fn verify_cmzcpzshow(
    X_1_to_n: &[Point],
    tilde_U: &Point,
    pres_ctx: &[u8],
    proof: &Proof32,
) -> bool {
    let mut points = Vec::with_capacity(X_1_to_n.len() + 1);
    points.extend_from_slice(X_1_to_n);
    points.push(*tilde_U);

    hash_points_scalars_with_ctx(&points, &[], pres_ctx) == proof.digest
}

#[inline]
fn rand_nonzero<R: RngCore + CryptoRng>(rng: &mut R) -> Scalar {
    loop {
        let s = Scalar::rand(rng);
        if !s.is_zero() {
            return s;
        }
    }
}

/// Show credential:
/// - Randomize (U,V) -> (tilde_U, tilde_V)
/// - Sample tilde_gamma, gamma_j in Z_p^*
/// - Compute:
///   Z  = sum_j gamma_j * X_j  - tilde_gamma * H
///   C_V = tilde_V + tilde_gamma * H
///   C_j = attr_j * tilde_U + gamma_j * G
/// - Produce placeholder NIZK bound to (X_1..X_n, tilde_U, pres_ctx)
pub fn show_cred<R: RngCore + CryptoRng>(
    rng: &mut R,
    pp: &PublicParams,
    _ipk: &IssuerPublic,
    vpk: &VerifierPublic,
    cred: &Credential,
    pres_ctx: &[u8],
) -> Presentation {
    // γ, \tildeγ, γ_j ∈ Z_p^*
    let gamma = rand_nonzero(rng);
    let tilde_gamma = rand_nonzero(rng);
    let gamma_j_vec: Vec<Scalar> = (0..vpk.X_1_to_n.len()).map(|_| rand_nonzero(rng)).collect();

    // (tilde_U, tilde_V) = (γU, γV)
    let tilde_U = smul(&cred.U, &gamma);
    let tilde_V = smul(&cred.V, &gamma);

    // Z = sum_j γ_j X_j - tildeγ * H
    let mut Z = Point::zero();
    for (gamma_j, Xj) in gamma_j_vec.iter().zip(vpk.X_1_to_n.iter()) {
        Z += smul(Xj, gamma_j);
    }
    Z -= smul(&pp.H, &tilde_gamma);

    // C_V = tilde_V + tildeγ * H
    let C_v = tilde_V + smul(&pp.H, &tilde_gamma);

    // C_j = attr_j * tilde_U + γ_j * G
    let mut C_j_vec = Vec::with_capacity(cred.attrs.len());
    assert_eq!(cred.attrs.len(), gamma_j_vec.len());
    for (attr, gamma_j) in cred.attrs.iter().zip(gamma_j_vec.iter()) {
        C_j_vec.push(smul(&tilde_U, attr) + smul(&pp.G, gamma_j));
    }

    // Placeholder NIZK bound to (X_1..X_n, tilde_U, pres_ctx)
    let nizk = prove_cmzcpzshow(&vpk.X_1_to_n, &tilde_U, &tilde_gamma, &cred.attrs, &gamma_j_vec, pres_ctx);

    Presentation {
        tilde_U: tilde_U,
        Z: Z,
        C_v: C_v,
        C_j_vec: C_j_vec,
        nizk: nizk,
    }
}


/// Verify presentation:
/// - Check placeholder cmzcpzshow over (X_1..X_n, tilde_U, pres_ctx)
/// - Check Z == x0*tilde_U + sum_j xj * C_j - C_V
pub fn verify_cred_show(
    vsk: &VerifierSecret,
    vpk: &VerifierPublic,
    pres: &Presentation,
    pres_ctx: &[u8],
) -> bool {
    // NIZK check (placeholder)
    // if !verify_cmzcpzshow(&vpk.X_1_to_n, &pres.tilde_U, pres_ctx, &pres.nizk) {
    //     return false;
    // }

    // Equation: Z ?= x0 * tilde_U + sum_j xj * C_j - C_V
    let mut rhs = smul(&pres.tilde_U, &vsk.x_0_to_x_n[0]);
    // for (xj, Cj) in vsk.x_0_to_x_n.iter().skip(1).zip(pres.C_j_vec.iter()) {
    //     rhs += smul(Cj, xj);
    // }
    println!(" x length = {}", vsk.x_0_to_x_n.len());
    println!(" C length = {}", pres.C_j_vec.len());
    for i in 1..vsk.x_0_to_x_n.len() {
        println!("verifier x_{} = {:?}", i, vsk.x_0_to_x_n[i]);
        let xj = &vsk.x_0_to_x_n[i];
        println!("pres.C_j_vec[{}] = {:?}", i - 1, pres.C_j_vec[i - 1]);
        let Cj = &pres.C_j_vec[i - 1];
        rhs += smul(Cj, xj);
    }
    rhs -= pres.C_v;

    pres.Z == rhs
}


#[cfg(test)]
mod akvac_tests {
    use ark_ff::Zero;
    use ark_std::rand::{rngs::StdRng, SeedableRng};
    use ark_std::UniformRand;
    use crate::mkvak::mkvak::{akvac_setup, AkvacError, issue_cred, issuer_keygen, receive_cred_1, receive_cred_2, show_cred, verifier_keygen, verify_cred_show};
    use crate::vka::bbs_vka::Scalar;

    #[test]
    fn setup_receive1() -> anyhow::Result<()> {
        let mut rng = StdRng::seed_from_u64(42);
        let n = 3;

        let pp = akvac_setup(&mut rng, n);
        assert_eq!(pp.vka_params.G_vec.len(), n + 2);

        let (isk, ipk) = issuer_keygen(&mut rng, &pp);

        let (_vsk, vpk) = verifier_keygen(&mut rng, &pp, &isk, &ipk)?;
        // Tuple has n+3 points: X_1..X_n, X_0, Z_0
        assert_eq!(vpk.X_1_to_n.len(), n);

        let attrs: Vec<Scalar> = (0..n).map(|_| Scalar::rand(&mut rng)).collect();
        let (state, cred_req) = receive_cred_1(&mut rng, &pp, &ipk, &vpk, &attrs)?;
        assert_eq!(state.attrs.len(), n);
        assert!(!state.bar_X0.is_zero());
        assert!(!state.bar_Z0.is_zero());
        assert_eq!(cred_req.C_j_vec.len(), n + 2);

        Ok(())
    }

    #[test]
    fn setup_receive1_issue_cred() -> anyhow::Result<()> {
        let mut rng = StdRng::seed_from_u64(7);
        let n = 3;

        let pp = akvac_setup(&mut rng, n);
        assert_eq!(pp.vka_params.G_vec.len(), n + 2);

        let (isk, ipk) = issuer_keygen(&mut rng, &pp);

        let (_vsk, vpk) = verifier_keygen(&mut rng, &pp, &isk, &ipk)?;
        // Tuple has n+3 points: X_1..X_n, X_0, Z_0
        assert_eq!(vpk.X_1_to_n.len(), n);

        let attrs: Vec<Scalar> = (0..n).map(|_| Scalar::rand(&mut rng)).collect();
        let (state, cred_req) = receive_cred_1(&mut rng, &pp, &ipk, &vpk, &attrs)?;
        assert_eq!(state.attrs.len(), n);
        assert!(!state.bar_X0.is_zero());
        assert!(!state.bar_Z0.is_zero());
        assert_eq!(cred_req.C_j_vec.len(), n + 2);

        let blind = issue_cred(&mut rng, &pp, &isk, &ipk, &cred_req)?;
        assert!(!blind.bar_U.is_zero());
        assert!(!blind.bar_V.is_zero());

        Ok(())
    }

    #[test]
    fn setup_receive1_issue_cred_receive2() -> anyhow::Result<()> {
        let mut rng = StdRng::seed_from_u64(7);
        let n = 3;

        let pp = akvac_setup(&mut rng, n);
        assert_eq!(pp.vka_params.G_vec.len(), n + 2);

        let (isk, ipk) = issuer_keygen(&mut rng, &pp);

        let (_vsk, vpk) = verifier_keygen(&mut rng, &pp, &isk, &ipk)?;
        // Tuple has n+3 points: X_1..X_n, X_0, Z_0
        assert_eq!(vpk.X_1_to_n.len(), n);

        let attrs: Vec<Scalar> = (0..n).map(|_| Scalar::rand(&mut rng)).collect();
        let (state, cred_req) = receive_cred_1(&mut rng, &pp, &ipk, &vpk, &attrs)?;
        assert_eq!(state.attrs.len(), n);
        assert!(!state.bar_X0.is_zero());
        assert!(!state.bar_Z0.is_zero());
        assert_eq!(cred_req.C_j_vec.len(), n + 2);

        let blind = issue_cred(&mut rng, &pp, &isk, &ipk, &cred_req)?;
        assert!(!blind.bar_U.is_zero());
        assert!(!blind.bar_V.is_zero());

        let cred = receive_cred_2(&pp, &ipk, &state, &cred_req, &blind)?;
        assert!(!cred.U.is_zero());
        assert!(!cred.V.is_zero());
        assert_eq!(cred.attrs, attrs);

        Ok(())
    }

    #[test]
    fn setup_receive1_issue_cred_receive2_show_cred_verify() -> anyhow::Result<()> {
        let mut rng = StdRng::seed_from_u64(7);
        let n = 3;

        let pp = akvac_setup(&mut rng, n);
        assert_eq!(pp.vka_params.G_vec.len(), n + 2);

        let (isk, ipk) = issuer_keygen(&mut rng, &pp);

        let (vsk, vpk) = verifier_keygen(&mut rng, &pp, &isk, &ipk)?;
        // Tuple has n+3 points: X_1..X_n, X_0, Z_0
        assert_eq!(vpk.X_1_to_n.len(), n);

        let attrs: Vec<Scalar> = (0..n).map(|_| Scalar::rand(&mut rng)).collect();
        let (state, cred_req) = receive_cred_1(&mut rng, &pp, &ipk, &vpk, &attrs)?;
        assert_eq!(state.attrs.len(), n);
        assert!(!state.bar_X0.is_zero());
        assert!(!state.bar_Z0.is_zero());
        assert_eq!(cred_req.C_j_vec.len(), n + 2);

        let blind = issue_cred(&mut rng, &pp, &isk, &ipk, &cred_req)?;
        assert!(!blind.bar_U.is_zero());
        assert!(!blind.bar_V.is_zero());

        let cred = receive_cred_2(&pp, &ipk, &state, &cred_req, &blind)?;
        assert!(!cred.U.is_zero());
        assert!(!cred.V.is_zero());
        assert_eq!(cred.attrs, attrs);

        let pres_ctx = b"presentation context";
        let pres = show_cred(&mut rng, &pp, &ipk, &vpk, &cred, pres_ctx);

        assert!(verify_cred_show(&vsk, &vpk, &pres, pres_ctx));

        Ok(())
    }

    #[test]
    fn akvac_setup_issuer_verifier_kg() -> anyhow::Result<()> {
        let mut rng = StdRng::seed_from_u64(7);
        let n = 3;

        let pp = akvac_setup(&mut rng, n);
        assert_eq!(pp.vka_params.G_vec.len(), n + 2);

        let (isk, ipk) = issuer_keygen(&mut rng, &pp);

        let (_vsk, vpk) = verifier_keygen(&mut rng, &pp, &isk, &ipk)?;
        // Tuple has n+2 points: X_1..X_n, X_0, Z_0
        assert_eq!(vpk.X_1_to_n.len(), n);

        Ok(())
    }

    fn rand_attrs(rng: &mut StdRng, n: usize) -> Vec<Scalar> {
        (0..n).map(|_| Scalar::rand(rng)).collect()
    }

    #[test]
    fn akvac_end_to_end_ok() -> anyhow::Result<()> {
        let mut rng = StdRng::seed_from_u64(12345);
        let n = 3;

        // Setup
        let pp = akvac_setup(&mut rng, n);
        assert_eq!(pp.vka_params.G_vec.len(), n + 2);

        // Issuer & Verifier keygen
        let (isk, ipk) = issuer_keygen(&mut rng, &pp);
        let (vsk, vpk) = verifier_keygen(&mut rng, &pp, &isk, &ipk)?;
        assert_eq!(vpk.X_1_to_n.len(), n);
        assert!(!vpk.X_0.is_zero());
        assert!(!vpk.Z_0.is_zero());

        // Client request (receivecred_1)
        let attrs = rand_attrs(&mut rng, n);
        let (state, cred_req) = receive_cred_1(&mut rng, &pp, &ipk, &vpk, &attrs)?;
        assert_eq!(state.attrs.len(), n);
        assert!(!state.bar_X0.is_zero());
        assert!(!state.bar_Z0.is_zero());
        assert_eq!(cred_req.C_j_vec.len(), n + 2);

        // Issuer issues blind credential
        let blind = issue_cred(&mut rng, &pp, &isk, &ipk, &cred_req)?;
        assert!(!blind.bar_U.is_zero());
        assert!(!blind.bar_V.is_zero());

        // Client finalizes
        let cred = receive_cred_2(&pp, &ipk, &state, &cred_req, &blind)?;
        assert!(!cred.U.is_zero());
        assert!(!cred.V.is_zero());
        assert_eq!(cred.attrs, attrs);

        Ok(())
    }

    #[test]
    fn receivecred_1_rejects_wrong_attr_len() {
        let mut rng = StdRng::seed_from_u64(7);
        let n = 2;

        let pp = akvac_setup(&mut rng, n);
        let (isk, ipk) = issuer_keygen(&mut rng, &pp);
        let (_vsk, vpk) = verifier_keygen(&mut rng, &pp, &isk, &ipk).unwrap();

        // Wrong length (n-1)
        let attrs = rand_attrs(&mut rng, n - 1);
        let err = receive_cred_1(&mut rng, &pp, &ipk, &vpk, &attrs).unwrap_err();
        match err {
            AkvacError::LengthMismatch { expected, got } => {
                assert_eq!(expected, n);
                assert_eq!(got, n - 1);
            }
            _ => panic!("expected LengthMismatch, got {err:?}"),
        }
    }

    #[test]
    fn issue_cred_rejects_tampered_cj_vector() -> anyhow::Result<()> {
        let mut rng = StdRng::seed_from_u64(99);
        let n = 2;

        let pp = akvac_setup(&mut rng, n);
        let (isk, ipk) = issuer_keygen(&mut rng, &pp);
        let (_vsk, vpk) = verifier_keygen(&mut rng, &pp, &isk, &ipk)?;

        let attrs = rand_attrs(&mut rng, n);
        let (_state, mut credreq) = receive_cred_1(&mut rng, &pp, &ipk, &vpk, &attrs)?;

        // Tamper one C_j to break the VKA verification
        credreq.C_j_vec[0] = credreq.C_j_vec[0] + pp.G;

        // The issuer should reject during vfcred or (earlier) proof check
        let err = issue_cred(&mut rng, &pp, &isk, &ipk, &credreq).unwrap_err();
        matches!(err, AkvacError::Vka(_));
        Ok(())
    }

    #[test]
    fn akvac_show_verify_ok() -> anyhow::Result<()> {
        use super::*;
        use ark_std::rand::{rngs::StdRng, SeedableRng};

        let mut rng = StdRng::seed_from_u64(4242);
        let n = 3;

        // Setup + issuance (reuse your flow)
        let pp = akvac_setup(&mut rng, n);
        let (isk, ipk) = issuer_keygen(&mut rng, &pp);
        let (vsk, vpk) = verifier_keygen(&mut rng, &pp, &isk, &ipk)?;
        let attrs: Vec<Scalar> = (0..n).map(|_| Scalar::rand(&mut rng)).collect();

        let (state, cred_req) = receive_cred_1(&mut rng, &pp, &ipk, &vpk, &attrs)?;
        let blind = issue_cred(&mut rng, &pp, &isk, &ipk, &cred_req)?;
        let cred = receive_cred_2(&pp, &ipk, &state, &cred_req, &blind)?;

        // Show
        let pres_ctx = b"demo-context-123";
        let pres = show_cred(&mut rng, &pp, &ipk, &vpk, &cred, pres_ctx);

        // Verify
        assert!(verify_cred_show(&vsk, &vpk, &pres, pres_ctx));
        Ok(())
    }
}