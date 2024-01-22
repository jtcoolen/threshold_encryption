use ark_ec::hashing::{
    curve_maps::wb::{WBConfig, WBMap},
    map_to_curve_hasher::MapToCurveBasedHasher,
    HashToCurve,
};
use ark_ec::pairing::Pairing;
use ark_ec::short_weierstrass::{Affine, Projective, SWCurveConfig};
use ark_ff::field_hashers::DefaultFieldHasher;
use ark_ff::{BigInteger, Field, PrimeField};
use ark_serialize::{CanonicalSerialize, Compress, SerializationError};
use ark_std::UniformRand;
use ark_std::Zero;

// TODO implement Pedersen DKG
// TODO write traits for the DKG and the IBE
// TODO: write struct for common input

type Transaction = Vec<u8>;
type Ciphertext<P> = (<P as Pairing>::G2, Vec<u8>);

fn xor_bytes(v1: &[u8], v2: &[u8]) -> Vec<u8> {
    v1.iter().zip(v2.iter()).map(|(&x1, &x2)| x1 ^ x2).collect()
}

pub fn pow<G: SWCurveConfig, N: BigInteger>(x: &Projective<G>, n: &mut N) -> Projective<G> {
    G::mul_projective(x, n.as_mut())
}

fn wb_hash_arbitrary_bytes_to_curve<WBCurve: WBConfig>(
    data: &[u8],
) -> ark_ec::short_weierstrass::Affine<WBCurve> {
    use sha2::Sha256;
    let test_wb_to_curve_hasher = MapToCurveBasedHasher::<
        Projective<WBCurve>,
        DefaultFieldHasher<Sha256, 128>,
        WBMap<WBCurve>,
    >::new(&[1])
    .unwrap();

    let hash_result = test_wb_to_curve_hasher
        .hash(data)
        .expect("fail to hash the bytes to curve");

    assert!(
        hash_result.x != WBCurve::BaseField::zero() && hash_result.y != WBCurve::BaseField::zero(),
        "we assume that not both a and b coefficients are zero for the test curve"
    );

    assert!(
        hash_result.is_on_curve(),
        "hash results into a point off the curve"
    );
    hash_result
}

fn hash_pairing_output<G: SWCurveConfig, P: Pairing<G2 = Projective<G>>>(
    hash_size: usize,
    pairing: P::TargetField,
) -> Result<Vec<u8>, SerializationError> {
    let mut compressed_bytes = Vec::new();
    pairing.serialize_with_mode(&mut compressed_bytes, Compress::Yes)?;
    let mut hasher = blake3::Hasher::new();
    hasher.update(&compressed_bytes);
    let mut output = vec![0; hash_size];
    let mut output_reader = hasher.finalize_xof();
    output_reader.fill(&mut output);
    Ok(output)
}

pub fn encrypt<
    G1Cfg: SWCurveConfig + WBConfig,
    G2Cfg: SWCurveConfig + WBConfig,
    P: Pairing<G1 = Projective<G1Cfg>, G2 = Projective<G2Cfg>>,
>(
    tx: &Transaction,
    id: u64,
    mpk: P::G2,
    generator: P::G2,
) -> Result<Ciphertext<P>, SerializationError> {
    let p: Affine<G1Cfg> = wb_hash_arbitrary_bytes_to_curve::<G1Cfg>(&id.to_ne_bytes());
    let mut rng = ark_std::rand::thread_rng();
    let mut r = P::ScalarField::rand(&mut rng).into_bigint();
    let pairing = P::pairing(P::G1::from(p), mpk).0.pow(r);
    let h = hash_pairing_output::<G2Cfg, P>(tx.len(), pairing)?;
    Ok((pow(&generator, &mut r), xor_bytes(tx, &h)))
}

pub fn key_share<G: SWCurveConfig + WBConfig, P: Pairing<G1 = Projective<G>>, N: BigInteger>(
    id: u64,
    secret_key_share: &mut N,
) -> Result<P::G1, SerializationError> {
    let p: Affine<G> = wb_hash_arbitrary_bytes_to_curve::<G>(&id.to_ne_bytes());
    Ok(pow(&p.into(), secret_key_share))
}

pub fn extract_key<
    G: SWCurveConfig,
    P: Pairing<G1 = Projective<G>>,
    N: BigInteger,
    F: PrimeField<BigInt = N>,
>(
    key_shares: Vec<(usize, P::G1)>,
    threshold: usize,
    domain: Vec<F>,
) -> Option<P::G1> {
    // TODO better error type than option
    // TODO replace with sum: in-place `+` should be implemented to move the left side
    if threshold == key_shares.len() {
        // vector of products, then pointwise multiplication with key_shares, then sum of the result
        let len = domain.len();
        let indices: Vec<usize> = key_shares.iter().map(|(i, _)| *i).collect();
        let lagrange_coeffs: Vec<N> = key_shares
            .iter()
            .map(|(i, _)| {
                indices
                    .iter()
                    .filter_map(|j| {
                        if *j != *i {
                            Some(
                                F::inverse(
                                    &(F::one()
                                        - domain[(*i as i64 - *j as i64).rem_euclid(len as i64)
                                            as usize]),
                                )
                                .unwrap(),
                            )
                        } else {
                            None
                        }
                    })
                    .reduce(|a, b| a * b)
                    .unwrap()
                    .into_bigint()
            })
            .collect();
        Some(
            key_shares
                .into_iter()
                .zip(lagrange_coeffs)
                .map(|((_, i1), i2)| pow(&i1, &mut i2.clone()))
                .sum(),
        )
    } else {
        None
    }
}

pub fn decrypt<
    G1Cfg: SWCurveConfig + WBConfig,
    G2Cfg: SWCurveConfig + WBConfig,
    P: Pairing<G1 = Projective<G1Cfg>, G2 = Projective<G2Cfg>>,
>(
    encrypted_tx: Ciphertext<P>,
    extracted_key: P::G1,
) -> Result<Transaction, SerializationError> {
    let (r, u) = encrypted_tx;
    use std::time::Instant;
    let now = Instant::now();
    let pairing = P::pairing(extracted_key, r).0;
    let elapsed = now.elapsed();
    println!("pairing: {:.2?}", elapsed);
    let h = hash_pairing_output::<G2Cfg, P>(u.len(), pairing)?;
    Ok(xor_bytes(&u, &h))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::BigInteger;
    use ark_ec::short_weierstrass::{Projective, SWCurveConfig};
    use ark_ec::Group;
    use ark_ff::PrimeField;
    use ark_poly::{
        univariate::DensePolynomial, DenseUVPolynomial, EvaluationDomain, Radix2EvaluationDomain,
    };
    use rand::distributions::Standard;
    use rand::seq::SliceRandom;
    use rand::Rng;

    fn mock_key_shares<
        N: BigInteger,
        G1Cfg: SWCurveConfig,
        G2Cfg: SWCurveConfig,
        F: PrimeField<BigInt = N>,
    >(
        validators: usize,
        threshold: usize,
        generator: Projective<G2Cfg>,
    ) -> (Projective<G2Cfg>, N, Vec<N>, Vec<F>) {
        let mut rng = ark_std::rand::thread_rng();
        let msk = F::rand(&mut rng);
        let mpk = pow(&generator, &mut msk.into_bigint());
        let mut p: DensePolynomial<F> = DenseUVPolynomial::<F>::rand(threshold - 1, &mut rng);
        p.coeffs[0] = msk;
        let domain_size = validators.next_power_of_two();
        let domain: Radix2EvaluationDomain<F> = EvaluationDomain::new(domain_size).unwrap();
        let v: Vec<N> = p
            .evaluate_over_domain(domain)
            .evals
            .iter()
            .map(|c| c.into_bigint())
            .collect();
        (mpk, msk.into(), v, domain.elements().collect())
    }

    fn test_ibe<
        F: PrimeField<BigInt = N>,
        N: BigInteger,
        G1Cfg: SWCurveConfig + WBConfig,
        G2Cfg: SWCurveConfig + WBConfig,
        P: Pairing<G1 = Projective<G1Cfg>, G2 = Projective<G2Cfg>>,
    >() {
        use std::time::Instant;
        let validators = 10;
        let threshold = 4;
        let g = Projective::<G2Cfg>::generator();
        let (mpk, mut _msk, mut dkg_key_shares, domain) =
            mock_key_shares::<N, G1Cfg, G2Cfg, F>(validators, threshold, g);

        let tx_size = 256;
        let mut rng = rand::thread_rng();
        let tx: Transaction = (&mut rng).sample_iter(Standard).take(tx_size).collect();
        let id: u64 = (&mut rng.gen_range(0u64..u64::MAX)).clone();

        let now = Instant::now();
        let enc = encrypt::<G1Cfg, G2Cfg, P>(&tx, id, mpk, g).unwrap();
        let elapsed = now.elapsed();
        println!("encrypt 256 bytes tx: {:.2?}", elapsed);

        let mut numbers: Vec<usize> = (0..validators).collect();
        numbers.shuffle(&mut rng);
        let indices = &numbers[0..threshold];

        let key_shares: Vec<(usize, P::G1)> = indices
            .into_iter()
            .map(|s| {
                (
                    *s,
                    key_share::<G1Cfg, P, N>(id, &mut dkg_key_shares[*s]).unwrap(),
                )
            })
            .collect();

        let now = Instant::now();
        let k = extract_key::<G1Cfg, P, N, F>(key_shares, threshold, domain).unwrap();
        let elapsed = now.elapsed();
        println!("extract key: {:.2?}", elapsed);

        let p: Affine<G1Cfg> = wb_hash_arbitrary_bytes_to_curve::<G1Cfg>(&id.to_ne_bytes());
        let k2 = pow(&p.into(), &mut _msk);
        assert_eq!(k, k2);
        let now = Instant::now();
        let dec = decrypt::<G1Cfg, G2Cfg, P>(enc, k).unwrap();
        let elapsed = now.elapsed();
        println!("decrypt 256 bytes tx: {:.2?}", elapsed);
        assert_eq!(tx, dec)
    }

    use ark_bls12_381::*;
    use ark_ff::BigInt;

    //quickcheck! {
    #[test]
    fn prop() {
        test_ibe::<
            Fr,
            BigInt<4>,
            ark_bls12_381::g1::Config,
            ark_bls12_381::g2::Config,
            ark_ec::bls12::Bls12<ark_bls12_381::Config>,
        >()
    }
    //}
}
