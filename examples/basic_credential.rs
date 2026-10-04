use akvac::mkvak::mkvak::{
    akvac_setup, issue_cred_fiatshamir, issuer_keygen, receive_cred_1_fiat_shamir, receive_cred_2,
    show_cred, verifier_keygen, verify_cred_show,
};
use akvac::saga::bbs_saga::Scalar;
use ark_std::rand::{rngs::StdRng, SeedableRng};
use ark_std::UniformRand;

fn main() -> anyhow::Result<()> {
    let mut rng = StdRng::seed_from_u64(42);
    let attribute_count = 4;

    // 1. Generate public parameters for credentials with four attributes.
    let public_params = akvac_setup(&mut rng, attribute_count);

    // 2. Generate the issuer and verifier key pairs.
    let (issuer_secret, issuer_public) = issuer_keygen(&mut rng, &public_params);
    let (verifier_secret, verifier_public) =
        verifier_keygen(&mut rng, &public_params, &issuer_secret, &issuer_public)?;

    // 3. The user chooses the attributes to certify.
    let attributes: Vec<Scalar> = (0..attribute_count)
        .map(|_| Scalar::rand(&mut rng))
        .collect();

    // 4. The user creates a verifier-specific blinded credential request.
    let (receive_state, credential_request) = receive_cred_1_fiat_shamir(
        &mut rng,
        &public_params,
        &issuer_public,
        &verifier_public,
        &attributes,
    )?;

    // 5. The issuer validates the request and returns a blind credential.
    let blind_credential = issue_cred_fiatshamir(
        &mut rng,
        &public_params,
        &issuer_secret,
        &issuer_public,
        &credential_request,
    )?;

    // 6. The user unblinds and finalizes the credential.
    let credential = receive_cred_2(
        &public_params,
        &issuer_public,
        &receive_state,
        &blind_credential,
        &credential_request.bar_X0,
        &credential_request.bar_Z0,
        &credential_request.C_attr,
    )?;

    // 7. The user presents the credential in a context chosen by the verifier.
    let presentation_context = b"example-session";
    let presentation = show_cred(
        &mut rng,
        &public_params,
        &issuer_public,
        &verifier_public,
        &credential,
        presentation_context,
    );

    // 8. The designated verifier checks the presentation with its secret key.
    let accepted = verify_cred_show(
        &public_params,
        &verifier_secret,
        &verifier_public,
        &presentation,
        presentation_context,
    );
    assert!(accepted, "the credential presentation must verify");

    println!("Anonymous credential presentation verified.");
    Ok(())
}
