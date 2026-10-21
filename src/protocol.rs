//! The Σ-protocol over a validated [`Instance`] (draft-irtf-cfrg-sigma-protocols,
//! Section "The Sigma Protocol"): prover commitment and response, the
//! verifier, the verifier as one random linear combination (batchable
//! proofs), the simulator, and the checks of compact proofs.
//!
//! The prover nonces and the simulator randomness are inputs; upstream draws
//! them from a `PrivateRng`.
//!
//! Each linear combination is one MSM, as upstream: the prover's commitment
//! in constant time ([`SigmaGroup::msm`], through [`Instance::map`]), the
//! verifier and the simulator in variable time (challenge, response and
//! randomness are public). The simulated commitment, which the verifier of
//! one equation and the compact verifier recompute, evaluates its rows by
//! one call of [`SigmaGroup::msm_rows_vartime`]; the verifier of a batchable
//! proof of several equations is one [`SigmaGroup::msm_vartime`].

use crate::group::SigmaGroup;
use crate::types::{
    Element, Equation, Instance, InvalidWitness, ProverState, Scalar, VerificationError,
};

/// A copy of a scalar slice.
pub fn copy_scalars(xs: &[Scalar]) -> Vec<Scalar> {
    let mut out = Vec::new();
    for i in 0..xs.len() {
        out.push(xs[i]);
    }
    out
}

impl Equation {
    /// Adds this equation's verification row, scaled by `randomness`, to the
    /// per-element weights: the coefficients that
    /// `randomness * (challenge * image - map(response))` puts on the
    /// instance's elements. Returns the updated weights.
    pub fn accumulate_weights<C: SigmaGroup>(
        &self,
        randomness: &Scalar,
        challenge: &Scalar,
        response: &[Scalar],
        weights: Vec<Scalar>,
    ) -> Vec<Scalar> {
        let mut acc = weights;
        let image_weight = C::scalar_mul(randomness, challenge);
        for k in 0..self.image.len() {
            let (element_index, coeff) = self.image[k];
            let delta = C::scalar_mul(&image_weight, &coeff);
            acc[element_index as usize] = C::scalar_add(&acc[element_index as usize], &delta);
        }
        for k in 0..self.terms.len() {
            let (scalar_index, element_index, coeff) = self.terms[k];
            let scaled = C::scalar_mul(randomness, &coeff);
            let delta = C::scalar_mul(&scaled, &response[scalar_index as usize]);
            acc[element_index as usize] = C::scalar_sub(&acc[element_index as usize], &delta);
        }
        acc
    }
}

impl Instance {
    /// `ProverCommitment`: the commitment `map(nonces)` and the prover state.
    /// The witness and the nonces have `num_scalars()` entries each.
    pub fn prover_commit<C: SigmaGroup>(
        &self,
        witness: &[Scalar],
        nonces: &[Scalar],
    ) -> Result<(Vec<Element>, ProverState), InvalidWitness> {
        if witness.len() != self.num_scalars || nonces.len() != self.num_scalars {
            return Err(InvalidWitness);
        }
        let commitment = self.map::<C>(nonces);
        let state = ProverState {
            nonces: copy_scalars(nonces),
            witness: copy_scalars(witness),
        };
        Ok((commitment, state))
    }

    /// `ProverResponse`: `response[i] = nonces[i] + witness[i] * challenge`.
    pub fn prover_response<C: SigmaGroup>(
        &self,
        state: &ProverState,
        challenge: &Scalar,
    ) -> Result<Vec<Scalar>, InvalidWitness> {
        if state.witness.len() != self.num_scalars || state.nonces.len() != self.num_scalars {
            return Err(InvalidWitness);
        }
        let mut response = Vec::new();
        for i in 0..self.num_scalars {
            let product = C::scalar_mul(&state.witness[i], challenge);
            response.push(C::scalar_add(&state.nonces[i], &product));
        }
        Ok(response)
    }

    /// `SimulateCommitment`: the commitment for which `(challenge, response)`
    /// verifies, `commitment[j] = map(response)[j] - challenge * image[j]`.
    /// Entry `j` is the variable-time MSM of the row `j`: the terms of
    /// equation `j` ([`Instance::evaluation_pairs`]) followed by the term
    /// `(-challenge, image[j])`. The rows are evaluated by one call of
    /// [`SigmaGroup::msm_rows_vartime`].
    pub fn simulate_commitment<C: SigmaGroup>(
        &self,
        challenge: &Scalar,
        response: &[Scalar],
    ) -> Result<Vec<Element>, VerificationError> {
        if response.len() != self.num_scalars {
            return Err(VerificationError);
        }
        let negated = C::scalar_neg(challenge);
        let mut rows = Vec::new();
        for j in 0..self.equations.len() {
            let (row_scalars, row_bases) = self.evaluation_pairs::<C>(j, response);
            let mut scalars = row_scalars;
            let mut bases = row_bases;
            scalars.push(negated);
            bases.push(self.image[j]);
            rows.push((scalars, bases));
        }
        Ok(C::msm_rows_vartime(&rows))
    }

    /// `Verifier`: checks `map(response) = commitment + challenge * image`.
    pub fn verifier<C: SigmaGroup>(
        &self,
        commitment: &[Element],
        challenge: &Scalar,
        response: &[Scalar],
    ) -> Result<(), VerificationError> {
        if commitment.len() != self.equations.len() || response.len() != self.num_scalars {
            return Err(VerificationError);
        }
        let expected = self.simulate_commitment::<C>(challenge, response)?;
        let mut accept = true;
        for j in 0..expected.len() {
            if !C::group_eq(&expected[j], &commitment[j]) {
                accept = false;
            }
        }
        if accept {
            Ok(())
        } else {
            Err(VerificationError)
        }
    }

    /// The verifier as one multi-scalar multiplication, the check of a
    /// batchable proof: with `E[j] = map(response)[j] - challenge * image[j]
    /// - commitment[j]`, accepts when `Σ randomness^j * E[j]` is the
    /// identity, computed by one variable-time MSM
    /// ([`SigmaGroup::msm_vartime`]) over the commitments and the instance's
    /// elements. One equation is checked by [`Instance::verifier`].
    pub fn verifier_with_randomness<C: SigmaGroup>(
        &self,
        commitment: &[Element],
        challenge: &Scalar,
        response: &[Scalar],
        randomness: &Scalar,
    ) -> Result<(), VerificationError> {
        if commitment.len() != self.equations.len() || response.len() != self.num_scalars {
            return Err(VerificationError);
        }
        if self.equations.len() == 1 {
            return self.verifier::<C>(commitment, challenge, response);
        }
        let mut weights = Vec::new();
        for _k in 0..self.elements.len() {
            weights.push(C::scalar_zero());
        }
        let mut scalars = Vec::new();
        let mut bases = Vec::new();
        let mut power = C::scalar_one();
        for j in 0..self.equations.len() {
            weights =
                self.equations[j].accumulate_weights::<C>(&power, challenge, response, weights);
            scalars.push(power);
            bases.push(commitment[j]);
            power = C::scalar_mul(&power, randomness);
        }
        for k in 0..self.elements.len() {
            scalars.push(weights[k]);
            bases.push(self.elements[k]);
        }
        let total = C::msm_vartime(&scalars, &bases);
        if C::group_eq(&total, &C::identity()) {
            Ok(())
        } else {
            Err(VerificationError)
        }
    }

    /// `SimulateResponse`: the simulated response is the simulator's
    /// randomness, `num_scalars()` scalars.
    pub fn simulate_response<C: SigmaGroup>(
        &self,
        randomness: &[Scalar],
    ) -> Result<Vec<Scalar>, VerificationError> {
        if randomness.len() != self.num_scalars {
            return Err(VerificationError);
        }
        Ok(copy_scalars(randomness))
    }

    /// A simulated transcript `(commitment, challenge, response)` from the
    /// response randomness and the challenge.
    pub fn simulate_transcript<C: SigmaGroup>(
        &self,
        randomness: &[Scalar],
        challenge: &Scalar,
    ) -> Result<(Vec<Element>, Scalar, Vec<Scalar>), VerificationError> {
        let response = self.simulate_response::<C>(randomness)?;
        let commitment = self.simulate_commitment::<C>(challenge, &response)?;
        Ok((commitment, *challenge, response))
    }

    /// The commitment a compact proof `(challenge, response)` stands for, the
    /// input of the challenge recomputation.
    pub fn compact_commitment<C: SigmaGroup>(
        &self,
        challenge: &Scalar,
        response: &[Scalar],
    ) -> Result<Vec<Element>, VerificationError> {
        self.simulate_commitment::<C>(challenge, response)
    }
}

/// The last check of a compact proof: the transmitted challenge equals the
/// challenge recomputed from [`Instance::compact_commitment`].
pub fn compact_accept<C: SigmaGroup>(
    challenge: &Scalar,
    expected_challenge: &Scalar,
) -> Result<(), VerificationError> {
    if C::scalar_eq(challenge, expected_challenge) {
        Ok(())
    } else {
        Err(VerificationError)
    }
}
