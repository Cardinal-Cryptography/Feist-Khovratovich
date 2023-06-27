mod circulant;
mod toeplitz;
mod utils;

use ark_bn254::{Fr, G1Affine, G1Projective};
use ark_ec::{AffineCurve, ProjectiveCurve};
use ark_ff::{One};
use ark_poly::{EvaluationDomain, GeneralEvaluationDomain, Polynomial, UVPolynomial};
use ark_poly::univariate::DensePolynomial;
pub use utils::*;
use crate::toeplitz::UpperToeplitz;

pub trait FK {
    fn fk(srs: &SRS, poly: &DensePolynomial<Fr>, domain: &GeneralEvaluationDomain<Fr>) -> Vec<G1Projective>;
}

pub enum ClassicFk {}

impl FK for ClassicFk {
    fn fk(srs: &SRS, poly: &DensePolynomial<Fr>, domain: &GeneralEvaluationDomain<Fr>) -> Vec<G1Projective> {
        let d = poly.degree();
        let d_cap = next_pow2(d);

        let toeplitz = UpperToeplitz::from_poly(poly);

        let mut srs = srs.projective[..d_cap].to_vec();
        srs.reverse();
        let h_commitments = &toeplitz.mul_by_vec(&srs)[..d_cap];

        domain.fft(h_commitments)
    }
}

pub enum CqLinFk {}

impl FK for CqLinFk {
    fn fk(srs: &SRS, poly: &DensePolynomial<Fr>, domain: &GeneralEvaluationDomain<Fr>) -> Vec<G1Projective> {
        let n = domain.size();
        let aux_domain = GeneralEvaluationDomain::<Fr>::new(2*n).unwrap();

        ///////////////////////////////////////////////////////////////
        ///// Computing srs*

        // T is a poly of degree n-1; its i-th coefficient is tau ^ {n-1-i}
        let mut t_coeffs = vec![Fr::one(); n];
        for i in 1..n {
            t_coeffs[i] = t_coeffs[i - 1] * srs.tau
        }
        t_coeffs.reverse();

        // Evaluate T on V (2n values)
        // todo: This can be done in linear time (very special case of FFT).
        let t_evals = aux_domain.fft(&t_coeffs);

        // We could get `g1_gen` knowing `srs` and `tau` already.
        let g1_gen = G1Affine::prime_subgroup_generator();

        // srs* is just the embedding of T's evaluations via `g1_gen`
        let srs_star = t_evals.iter()
            .map(|t| g1_gen.mul(*t).into_affine());

        ///////////////////////////////////////////////////////////////
        ///// Computing {[D·T]}

        let d_evals = aux_domain.fft(poly.coeffs());
        let dt_evals = srs_star
            .zip(d_evals.iter())
            .map(|(t, d)| t.mul(*d))
            .collect::<Vec<_>>();

        ///////////////////////////////////////////////////////////////
        ///// Computing h's evaluations

        let dt_coeffs = aux_domain.ifft(&dt_evals);
        let h_coeffs = dt_coeffs[n..].to_vec();

        domain.fft(&h_coeffs)
    }
}

#[derive(Clone)]
pub struct SRS {
    tau: Fr,
    affine: Vec<G1Affine>,
    projective: Vec<G1Projective>,
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

    use crate::{ClassicFk, CqLinFk, FK, SRS};

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

    fn srs(n: usize) -> SRS {
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
        SRS {
            tau,
            affine: srs,
            projective: srs_proj,
        }
    }

    fn test<FKEngine: FK>(poly: DensePolynomial<Fr>, n: usize) {
        let domain = GeneralEvaluationDomain::<Fr>::new(n).unwrap();
        let srs = srs(n);

        let qs_fast = FKEngine::fk(&srs, &poly, &domain);
        let qs_slow = commit_in_each_omega_i::<Bn254>(&srs.affine, &domain, &poly);
        assert_eq!(qs_fast, qs_slow);
    }

    #[test]
    fn test_multipoint_commitment() {
        let n = 64;
        let poly = DensePolynomial::<Fr>::rand(n, &mut test_rng());
        test::<ClassicFk>(poly.clone(), n);
        test::<CqLinFk>(poly, n);
    }

    #[test]
    fn test_smaller_degree() {
        let n = 32;
        let d = 5;
        let poly = DensePolynomial::<Fr>::rand(d, &mut test_rng());
        test::<ClassicFk>(poly.clone(), n);
        test::<CqLinFk>(poly, n);
    }
}
