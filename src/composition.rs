//! AND composition: an [`AndInstance`] is proved with one shared challenge,
//! one commitment and one response per branch, in branch order.
//!
//! The nonces have the witness's shape ([`AndWitness`]) and the simulator
//! randomness the response's shape ([`AndResponse`]).

use crate::group::SigmaGroup;
use crate::types::{
    AndCommitment, AndInstance, AndProverState, AndResponse, AndWitness, Instance, InvalidWitness,
    Scalar, VerificationError,
};

impl AndInstance {
    /// The AND of `branches`; the empty AND is true.
    pub fn and(branches: Vec<Instance>) -> AndInstance {
        AndInstance { branches }
    }

    /// Whether every branch's witness satisfies it; a witness of another
    /// shape does not.
    pub fn is_witness_valid<C: SigmaGroup>(&self, witness: &AndWitness) -> bool {
        if self.branches.len() != witness.branches.len() {
            return false;
        }
        let mut valid = true;
        for i in 0..self.branches.len() {
            let branch = &self.branches[i];
            if witness.branches[i].len() != branch.num_scalars()
                || !branch.is_witness_valid::<C>(&witness.branches[i])
            {
                valid = false;
            }
        }
        valid
    }

    /// The prover's commitment, one per branch. A witness or nonces with
    /// another number of branches, or a branch of the wrong length, is
    /// [`InvalidWitness`].
    pub fn prover_commit<C: SigmaGroup>(
        &self,
        witness: &AndWitness,
        nonces: &AndWitness,
    ) -> Result<(AndCommitment, AndProverState), InvalidWitness> {
        if self.branches.len() != witness.branches.len()
            || self.branches.len() != nonces.branches.len()
        {
            return Err(InvalidWitness);
        }
        let mut ok = true;
        let mut commitments = Vec::new();
        let mut states = Vec::new();
        for i in 0..self.branches.len() {
            if ok {
                match self.branches[i].prover_commit::<C>(&witness.branches[i], &nonces.branches[i])
                {
                    Ok((commitment, state)) => {
                        commitments.push(commitment);
                        states.push(state);
                    }
                    Err(_) => {
                        ok = false;
                    }
                }
            }
        }
        if ok {
            Ok((
                AndCommitment {
                    branches: commitments,
                },
                AndProverState { branches: states },
            ))
        } else {
            Err(InvalidWitness)
        }
    }

    /// The prover's response, every branch answering the same challenge.
    pub fn prover_response<C: SigmaGroup>(
        &self,
        state: &AndProverState,
        challenge: &Scalar,
    ) -> Result<AndResponse, InvalidWitness> {
        if self.branches.len() != state.branches.len() {
            return Err(InvalidWitness);
        }
        let mut ok = true;
        let mut responses = Vec::new();
        for i in 0..self.branches.len() {
            if ok {
                match self.branches[i].prover_response::<C>(&state.branches[i], challenge) {
                    Ok(response) => responses.push(response),
                    Err(_) => {
                        ok = false;
                    }
                }
            }
        }
        if ok {
            Ok(AndResponse {
                branches: responses,
            })
        } else {
            Err(InvalidWitness)
        }
    }

    /// The verifier: every branch verifies under the same challenge.
    pub fn verifier<C: SigmaGroup>(
        &self,
        commitment: &AndCommitment,
        challenge: &Scalar,
        response: &AndResponse,
    ) -> Result<(), VerificationError> {
        if self.branches.len() != commitment.branches.len()
            || commitment.branches.len() != response.branches.len()
        {
            return Err(VerificationError);
        }
        let mut accept = true;
        for i in 0..self.branches.len() {
            if accept {
                match self.branches[i].verifier::<C>(
                    &commitment.branches[i],
                    challenge,
                    &response.branches[i],
                ) {
                    Ok(()) => {}
                    Err(_) => {
                        accept = false;
                    }
                }
            }
        }
        if accept {
            Ok(())
        } else {
            Err(VerificationError)
        }
    }

    /// The verifier of a batchable proof; a composition checks it with
    /// [`AndInstance::verifier`], as upstream does.
    pub fn verifier_with_randomness<C: SigmaGroup>(
        &self,
        commitment: &AndCommitment,
        challenge: &Scalar,
        response: &AndResponse,
        _randomness: &Scalar,
    ) -> Result<(), VerificationError> {
        self.verifier::<C>(commitment, challenge, response)
    }

    /// The commitment for which `(challenge, response)` verifies.
    pub fn simulate_commitment<C: SigmaGroup>(
        &self,
        challenge: &Scalar,
        response: &AndResponse,
    ) -> Result<AndCommitment, VerificationError> {
        if self.branches.len() != response.branches.len() {
            return Err(VerificationError);
        }
        let mut ok = true;
        let mut commitments = Vec::new();
        for i in 0..self.branches.len() {
            if ok {
                match self.branches[i].simulate_commitment::<C>(challenge, &response.branches[i]) {
                    Ok(commitment) => commitments.push(commitment),
                    Err(_) => {
                        ok = false;
                    }
                }
            }
        }
        if ok {
            Ok(AndCommitment {
                branches: commitments,
            })
        } else {
            Err(VerificationError)
        }
    }

    /// The simulated response: the randomness, checked against the shape.
    pub fn simulate_response<C: SigmaGroup>(
        &self,
        randomness: &AndResponse,
    ) -> Result<AndResponse, VerificationError> {
        if self.branches.len() != randomness.branches.len() {
            return Err(VerificationError);
        }
        let mut ok = true;
        let mut responses = Vec::new();
        for i in 0..self.branches.len() {
            if ok {
                match self.branches[i].simulate_response::<C>(&randomness.branches[i]) {
                    Ok(response) => responses.push(response),
                    Err(_) => {
                        ok = false;
                    }
                }
            }
        }
        if ok {
            Ok(AndResponse {
                branches: responses,
            })
        } else {
            Err(VerificationError)
        }
    }

    /// A simulated transcript from the response randomness and the challenge.
    pub fn simulate_transcript<C: SigmaGroup>(
        &self,
        randomness: &AndResponse,
        challenge: &Scalar,
    ) -> Result<(AndCommitment, Scalar, AndResponse), VerificationError> {
        let response = self.simulate_response::<C>(randomness)?;
        let commitment = self.simulate_commitment::<C>(challenge, &response)?;
        Ok((commitment, *challenge, response))
    }
}
