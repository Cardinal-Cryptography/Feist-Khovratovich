mod circulant;
mod toeplitz;
mod utils;

use ark_bn254::{Fr, G1Projective};
use ark_poly::{EvaluationDomain, GeneralEvaluationDomain, Polynomial};
use ark_poly::univariate::DensePolynomial;
pub use utils::*;
use crate::toeplitz::UpperToeplitz;

pub fn fk_classic(srs: &[G1Projective], poly: &DensePolynomial<Fr>, domain: &GeneralEvaluationDomain<Fr>) -> Vec<G1Projective> {
    let d = poly.degree();
    let d_cap = next_pow2(d);

    let toeplitz = UpperToeplitz::from_poly(poly);

    let mut srs = srs[..d_cap].to_vec();
    srs.reverse();
    let h_commitments = &toeplitz.mul_by_vec(&srs)[..d_cap];

    domain.fft(h_commitments)
}

#[cfg(test)]
mod tests {
    use std::iter;

    use ark_bn254::{Bn254, Fr, G1Affine, G1Projective};
    use ark_ec::{msm::VariableBaseMSM, AffineCurve, PairingEngine};
    use ark_ff::{One, PrimeField, UniformRand};
    use ark_poly::{
        univariate::DensePolynomial, EvaluationDomain, GeneralEvaluationDomain, Polynomial,
        UVPolynomial,
    };
    use ark_std::test_rng;

    use crate::{fk_classic};

    pub fn commit<E: PairingEngine>(
        srs: &[E::G1Affine],
        poly: &DensePolynomial<E::Fr>,
    ) -> E::G1Projective {
        if srs.len() - 1 < poly.degree() {
            panic!(
                "SRS size to small! Can't commit to polynomial of degree {} with srs of size {}",
                poly.degree(),
                srs.len()
            );
        }
        let coeff_scalars: Vec<_> = poly.coeffs.iter().map(|c| c.into_repr()).collect();
        VariableBaseMSM::multi_scalar_mul(srs, &coeff_scalars)
    }

    pub fn open<E: PairingEngine>(
        srs: &[E::G1Affine],
        poly: &DensePolynomial<E::Fr>,
        challenge: E::Fr,
    ) -> (E::Fr, E::G1Affine) {
        let q = poly / &DensePolynomial::from_coefficients_slice(&[-challenge, E::Fr::one()]);
        if srs.len() - 1 < q.degree() {
            panic!(
                "Open g1: SRS size to small! Can't commit to polynomial of degree {} with srs of size {}",
                q.degree(),
                srs.len()
            );
        }
        let proof: E::G1Affine = commit::<E>(srs, &q).into();
        (poly.evaluate(&challenge), proof)
    }

    fn commit_in_each_omega_i<E: PairingEngine>(
        srs: &[E::G1Affine],
        domain: &GeneralEvaluationDomain<E::Fr>,
        poly: &DensePolynomial<E::Fr>,
    ) -> Vec<E::G1Affine> {
        domain
            .elements()
            .map(|omega_pow_i| open::<E>(srs, poly, omega_pow_i).1)
            .collect()
    }

    fn srs(n: usize) -> (Vec<G1Affine>, Vec<G1Projective>) {
        let mut rng = test_rng();
        let tau = Fr::rand(&mut rng);

        let powers_of_tau: Vec<Fr> = iter::successors(Some(Fr::one()), |p| Some(*p * tau))
            .take(n)
            .collect();

        let g1_gen = G1Affine::prime_subgroup_generator();
        let srs: Vec<G1Affine> = powers_of_tau
            .iter()
            .take(n)
            .map(|tp| g1_gen.mul(tp.into_repr()).into())
            .collect();
        let srs_proj: Vec<G1Projective> = srs
            .iter()
            .map(|t| t.into_projective())
            .collect();
        (srs, srs_proj)
    }

    #[test]
    fn test_multipoint_commitment() {
        let n = 64;

        let mut rng = test_rng();
        let poly = DensePolynomial::<Fr>::rand(n, &mut rng);

        let domain = GeneralEvaluationDomain::<Fr>::new(n).unwrap();
        let (srs, srs_proj) = srs(n);

        let qs_fast = fk_classic(&srs_proj, &poly, &domain);
        let qs_slow = commit_in_each_omega_i::<Bn254>(&srs, &domain, &poly);
        assert_eq!(qs_fast, qs_slow);
    }

    #[test]
    fn test_smaller_degree() {
        let n = 32;
        let d = 5;

        let mut rng = test_rng();
        let poly = DensePolynomial::<Fr>::rand(d, &mut rng);

        let domain = GeneralEvaluationDomain::<Fr>::new(n).unwrap();
        let (srs, srs_proj) = srs(n);

        let qs_fast = fk_classic(&srs_proj, &poly, &domain);
        let qs_slow = commit_in_each_omega_i::<Bn254>(&srs, &domain, &poly);
        assert_eq!(qs_fast, qs_slow);
    }
}
