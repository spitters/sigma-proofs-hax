//! The non-interactive layer of upstream `sigma-proofs` 0.4.1 over the core:
//! batchable and compact NARG strings through the `spongefish` duplex sponge,
//! with the upstream encodings, so that a proof made here is byte-for-byte
//! the upstream proof and either side verifies the other's.
//!
//! The layer is generic in the sponge (`H`: upstream's `DefaultHash`, or the
//! `Shake128` of the specification's ciphersuites) and, through
//! [`NargProtocol::Group`], in the group and its wire codec ([`GroupWire`]).
//! [`Instance`] and [`AndTree`] are the Ristretto255 statements with the
//! upstream instance encoding (the core's draft-03 indices shifted by one,
//! [`InstanceFormat::ImplicitIdentity`]); [`WireInstance`] is a statement over
//! any [`GroupWire`] in either instance encoding of [`crate::wire`] (upstream
//! 0.4.1, or draft-irtf-cfrg-sigma-protocols-03). In every case the element
//! codec is draft-03's: the identity has no encoding, so a commitment that
//! contains it is neither sent nor accepted (draft-03, Sections 2.3.1 and
//! 5.5, step 7).
//!
//! Compiled only outside the hax view (`cfg(not(hax))`). The core supplies
//! everything but the sponge and the byte codecs: the commitment and the
//! response from given nonces, the verifiers, the simulated commitment of a
//! compact proof, and the validated instance.

use spongefish::{
    DuplexSpongeInit, Encoding, NargReader, PrivateRng, ProverState as SpongeProver, SessionId,
    VerificationError as SpongeError, VerifierState,
};

use crate::codec::{push_u32_le, serialize_elements, serialize_scalars};
use crate::protocol::compact_accept;
use crate::ristretto::Ristretto255;
use crate::types::{
    AndCommitment, AndInstance, AndProverState, AndResponse, AndWitness, Element, Instance,
    InvalidWitness, Scalar, VerificationError,
};
use crate::wire::{
    read_elements, read_scalar, read_scalars, serialize_elements as serialize_wire_elements,
    serialize_instance, GroupWire, InstanceFormat, WireInstance, CHALLENGE_LEN,
};

type C = Ristretto255;

/// The upstream instance encoding of the Ristretto255 statements.
const RISTRETTO_FORMAT: InstanceFormat = InstanceFormat::ImplicitIdentity;

/// The upstream encoding of a validated Ristretto255 instance. It exists:
/// no element is the identity (check 8), and an element index of `2^32 - 1`
/// would need `2^32` elements.
fn upstream_encoding(instance: &Instance) -> Vec<u8> {
    serialize_instance::<C>(instance, RISTRETTO_FORMAT)
        .expect("a validated instance has an upstream encoding")
}

/// Bytes absorbed as they are (upstream `PrefixFree`).
struct PrefixFree<'a>(&'a [u8]);

impl Encoding<u8> for PrefixFree<'_> {
    fn encode(&self) -> impl AsRef<[u8]> {
        self.0
    }
}

/// A uniformly random scalar of the group `W` drawn from `rng` exactly as
/// upstream `ScalarCodec::sample` draws it.
pub fn sample_scalar_of<W: GroupWire, H: DuplexSpongeInit<U = u8>>(
    rng: &mut PrivateRng<H>,
) -> Scalar {
    let mut buf = [0u8; CHALLENGE_LEN];
    rng.fill_bytes(&mut buf);
    W::scalar_from_uniform_bytes(&buf)
}

/// `n` scalars drawn by [`sample_scalar_of`].
pub fn sample_scalars_of<W: GroupWire, H: DuplexSpongeInit<U = u8>>(
    rng: &mut PrivateRng<H>,
    n: usize,
) -> Vec<Scalar> {
    (0..n).map(|_| sample_scalar_of::<W, H>(rng)).collect()
}

/// A uniformly random Ristretto255 scalar ([`sample_scalar_of`]).
pub fn sample_scalar<H: DuplexSpongeInit<U = u8>>(rng: &mut PrivateRng<H>) -> Scalar {
    sample_scalar_of::<C, H>(rng)
}

/// `n` Ristretto255 scalars drawn by [`sample_scalar`].
pub fn sample_scalars<H: DuplexSpongeInit<U = u8>>(
    rng: &mut PrivateRng<H>,
    n: usize,
) -> Vec<Scalar> {
    sample_scalars_of::<C, H>(rng, n)
}

/// An upstream composition tree of AND nodes. Its protocol is that of the
/// [`AndInstance`] of its leaves in depth-first order ([`AndTree::flatten`]);
/// the tree enters only the instance label ([`NargProtocol::encode_instance`]).
#[derive(Clone, Debug)]
pub enum AndTree {
    Simple(Instance),
    And(Vec<AndTree>),
}

impl AndTree {
    fn push_leaves(&self, out: &mut Vec<Instance>) {
        match self {
            AndTree::Simple(leaf) => out.push(leaf.clone()),
            AndTree::And(branches) => {
                for branch in branches {
                    branch.push_leaves(out);
                }
            }
        }
    }

    /// The AND of the leaves, in depth-first order.
    pub fn flatten(&self) -> AndInstance {
        let mut leaves = Vec::new();
        self.push_leaves(&mut leaves);
        AndInstance { branches: leaves }
    }
}

/// One scalar vector per leaf of `instance`, drawn in upstream's order.
pub fn sample_per_leaf<H: DuplexSpongeInit<U = u8>>(
    instance: &AndInstance,
    rng: &mut PrivateRng<H>,
) -> Vec<Vec<Scalar>> {
    instance
        .branches
        .iter()
        .map(|leaf| sample_scalars(rng, leaf.num_scalars()))
        .collect()
}

/// A Σ-protocol over the core with the upstream NARG codec.
pub trait NargProtocol {
    /// The group, with its wire codec.
    type Group: GroupWire;
    type Witness;
    type Nonces;
    type Commitment;
    type ProverState;
    type Response;

    /// The encoded instance, absorbed first.
    fn encode_instance(&self) -> Vec<u8>;
    fn draw_nonces<H: DuplexSpongeInit<U = u8>>(&self, rng: &mut PrivateRng<H>) -> Self::Nonces;
    fn commit(
        &self,
        witness: &Self::Witness,
        nonces: &Self::Nonces,
    ) -> Result<(Self::Commitment, Self::ProverState), InvalidWitness>;
    fn respond(
        &self,
        state: &Self::ProverState,
        challenge: &Scalar,
    ) -> Result<Self::Response, InvalidWitness>;
    /// The encoded commitment; `None` if an element has no encoding (the
    /// identity).
    fn serialize_commitment(&self, commitment: &Self::Commitment) -> Option<Vec<u8>>;
    fn serialize_response(&self, response: &Self::Response) -> Vec<u8>;
    fn read_commitment(
        &self,
        reader: &mut NargReader<'_>,
    ) -> Result<Self::Commitment, VerificationError>;
    fn read_response(
        &self,
        reader: &mut NargReader<'_>,
    ) -> Result<Self::Response, VerificationError>;
    fn verify_randomized(
        &self,
        commitment: &Self::Commitment,
        challenge: &Scalar,
        response: &Self::Response,
        randomness: &Scalar,
    ) -> Result<(), VerificationError>;
    fn simulate_commitment(
        &self,
        challenge: &Scalar,
        response: &Self::Response,
    ) -> Result<Self::Commitment, VerificationError>;
}

impl NargProtocol for Instance {
    type Group = C;
    type Witness = Vec<Scalar>;
    type Nonces = Vec<Scalar>;
    type Commitment = Vec<Element>;
    type ProverState = crate::types::ProverState;
    type Response = Vec<Scalar>;

    fn encode_instance(&self) -> Vec<u8> {
        upstream_encoding(self)
    }
    fn draw_nonces<H: DuplexSpongeInit<U = u8>>(&self, rng: &mut PrivateRng<H>) -> Vec<Scalar> {
        sample_scalars(rng, self.num_scalars())
    }
    fn commit(
        &self,
        witness: &Vec<Scalar>,
        nonces: &Vec<Scalar>,
    ) -> Result<(Vec<Element>, crate::types::ProverState), InvalidWitness> {
        self.prover_commit::<C>(witness, nonces)
    }
    fn respond(
        &self,
        state: &crate::types::ProverState,
        challenge: &Scalar,
    ) -> Result<Vec<Scalar>, InvalidWitness> {
        self.prover_response::<C>(state, challenge)
    }
    fn serialize_commitment(&self, commitment: &Vec<Element>) -> Option<Vec<u8>> {
        serialize_elements::<C>(commitment)
    }
    fn serialize_response(&self, response: &Vec<Scalar>) -> Vec<u8> {
        serialize_scalars(response)
    }
    fn read_commitment(
        &self,
        reader: &mut NargReader<'_>,
    ) -> Result<Vec<Element>, VerificationError> {
        read_elements::<C>(reader, self.num_equations())
    }
    fn read_response(&self, reader: &mut NargReader<'_>) -> Result<Vec<Scalar>, VerificationError> {
        read_scalars::<C>(reader, self.num_scalars())
    }
    fn verify_randomized(
        &self,
        commitment: &Vec<Element>,
        challenge: &Scalar,
        response: &Vec<Scalar>,
        randomness: &Scalar,
    ) -> Result<(), VerificationError> {
        self.verifier_with_randomness::<C>(commitment, challenge, response, randomness)
    }
    fn simulate_commitment(
        &self,
        challenge: &Scalar,
        response: &Vec<Scalar>,
    ) -> Result<Vec<Element>, VerificationError> {
        self.compact_commitment::<C>(challenge, response)
    }
}

const LABEL_SIMPLE: &[u8] = b"sigma-proofs composition SIMPLE";
const LABEL_AND: &[u8] = b"sigma-proofs composition AND";

fn extend_prefixed(bytes: Vec<u8>, label: &[u8]) -> Vec<u8> {
    let mut bytes = push_u32_le(bytes, label.len() as u32);
    bytes.extend_from_slice(label);
    bytes
}

impl NargProtocol for AndTree {
    type Group = C;
    type Witness = AndWitness;
    type Nonces = AndWitness;
    type Commitment = AndCommitment;
    type ProverState = AndProverState;
    type Response = AndResponse;

    fn encode_instance(&self) -> Vec<u8> {
        match self {
            AndTree::Simple(leaf) => {
                extend_prefixed(LABEL_SIMPLE.to_vec(), &upstream_encoding(leaf))
            }
            AndTree::And(branches) => {
                let mut bytes = push_u32_le(LABEL_AND.to_vec(), branches.len() as u32);
                for branch in branches {
                    bytes = extend_prefixed(bytes, &branch.encode_instance());
                }
                bytes
            }
        }
    }
    fn draw_nonces<H: DuplexSpongeInit<U = u8>>(&self, rng: &mut PrivateRng<H>) -> AndWitness {
        AndWitness {
            branches: sample_per_leaf(&self.flatten(), rng),
        }
    }
    fn commit(
        &self,
        witness: &AndWitness,
        nonces: &AndWitness,
    ) -> Result<(AndCommitment, AndProverState), InvalidWitness> {
        self.flatten().prover_commit::<C>(witness, nonces)
    }
    fn respond(
        &self,
        state: &AndProverState,
        challenge: &Scalar,
    ) -> Result<AndResponse, InvalidWitness> {
        self.flatten().prover_response::<C>(state, challenge)
    }
    fn serialize_commitment(&self, commitment: &AndCommitment) -> Option<Vec<u8>> {
        let mut bytes = Vec::new();
        for branch in &commitment.branches {
            bytes.extend_from_slice(&serialize_elements::<C>(branch)?);
        }
        Some(bytes)
    }
    fn serialize_response(&self, response: &AndResponse) -> Vec<u8> {
        response
            .branches
            .iter()
            .flat_map(|r| serialize_scalars(r))
            .collect()
    }
    fn read_commitment(
        &self,
        reader: &mut NargReader<'_>,
    ) -> Result<AndCommitment, VerificationError> {
        let branches = self
            .flatten()
            .branches
            .iter()
            .map(|leaf| read_elements::<C>(reader, leaf.num_equations()))
            .collect::<Result<Vec<_>, _>>()?;
        Ok(AndCommitment { branches })
    }
    fn read_response(&self, reader: &mut NargReader<'_>) -> Result<AndResponse, VerificationError> {
        let branches = self
            .flatten()
            .branches
            .iter()
            .map(|leaf| read_scalars::<C>(reader, leaf.num_scalars()))
            .collect::<Result<Vec<_>, _>>()?;
        Ok(AndResponse { branches })
    }
    fn verify_randomized(
        &self,
        commitment: &AndCommitment,
        challenge: &Scalar,
        response: &AndResponse,
        randomness: &Scalar,
    ) -> Result<(), VerificationError> {
        self.flatten()
            .verifier_with_randomness::<C>(commitment, challenge, response, randomness)
    }
    fn simulate_commitment(
        &self,
        challenge: &Scalar,
        response: &AndResponse,
    ) -> Result<AndCommitment, VerificationError> {
        self.flatten().simulate_commitment::<C>(challenge, response)
    }
}

impl<W: GroupWire> NargProtocol for WireInstance<W> {
    type Group = W;
    type Witness = Vec<Scalar>;
    type Nonces = Vec<Scalar>;
    type Commitment = Vec<Element>;
    type ProverState = crate::types::ProverState;
    type Response = Vec<Scalar>;

    fn encode_instance(&self) -> Vec<u8> {
        self.encoded().to_vec()
    }
    fn draw_nonces<H: DuplexSpongeInit<U = u8>>(&self, rng: &mut PrivateRng<H>) -> Vec<Scalar> {
        sample_scalars_of::<W, H>(rng, self.instance().num_scalars())
    }
    fn commit(
        &self,
        witness: &Vec<Scalar>,
        nonces: &Vec<Scalar>,
    ) -> Result<(Vec<Element>, crate::types::ProverState), InvalidWitness> {
        self.instance().prover_commit::<W>(witness, nonces)
    }
    fn respond(
        &self,
        state: &crate::types::ProverState,
        challenge: &Scalar,
    ) -> Result<Vec<Scalar>, InvalidWitness> {
        self.instance().prover_response::<W>(state, challenge)
    }
    fn serialize_commitment(&self, commitment: &Vec<Element>) -> Option<Vec<u8>> {
        serialize_wire_elements::<W>(commitment)
    }
    fn serialize_response(&self, response: &Vec<Scalar>) -> Vec<u8> {
        serialize_scalars(response)
    }
    fn read_commitment(
        &self,
        reader: &mut NargReader<'_>,
    ) -> Result<Vec<Element>, VerificationError> {
        read_elements::<W>(reader, self.instance().num_equations())
    }
    fn read_response(&self, reader: &mut NargReader<'_>) -> Result<Vec<Scalar>, VerificationError> {
        read_scalars::<W>(reader, self.instance().num_scalars())
    }
    fn verify_randomized(
        &self,
        commitment: &Vec<Element>,
        challenge: &Scalar,
        response: &Vec<Scalar>,
        randomness: &Scalar,
    ) -> Result<(), VerificationError> {
        self.instance()
            .verifier_with_randomness::<W>(commitment, challenge, response, randomness)
    }
    fn simulate_commitment(
        &self,
        challenge: &Scalar,
        response: &Vec<Scalar>,
    ) -> Result<Vec<Element>, VerificationError> {
        self.instance().compact_commitment::<W>(challenge, response)
    }
}

/// A batchable proof: the commitment, then the response. A commitment with
/// no encoding is [`InvalidWitness`].
pub fn prove_batchable_with<H, R, P>(
    session_id: &SessionId,
    instance: &P,
    witness: &P::Witness,
    rng: &mut PrivateRng<R>,
) -> Result<Vec<u8>, InvalidWitness>
where
    H: DuplexSpongeInit<U = u8>,
    R: DuplexSpongeInit<U = u8>,
    P: NargProtocol,
{
    let instance_bytes = instance.encode_instance();
    let mut prover = SpongeProver::<H>::new(session_id, &PrefixFree(&instance_bytes));
    let nonces = instance.draw_nonces(rng);
    let (commitment, state) = instance.commit(witness, &nonces)?;
    let commitment_bytes = instance
        .serialize_commitment(&commitment)
        .ok_or(InvalidWitness)?;
    prover.prover_message_as(&commitment_bytes, Vec::as_slice);
    let challenge =
        prover.verifier_message_as(CHALLENGE_LEN, P::Group::scalar_from_uniform_bytes);
    let response = instance.respond(&state, &challenge)?;
    let response_bytes = instance.serialize_response(&response);
    Ok(prover.last_prover_message_as(&response_bytes, Vec::as_slice))
}

/// Verifies a batchable proof: the transcript, then one squeezed scalar for
/// the random linear combination of the verification equations.
pub fn verify_batchable_with<H, P>(
    session_id: &SessionId,
    instance: &P,
    narg_string: &[u8],
) -> Result<(), VerificationError>
where
    H: DuplexSpongeInit<U = u8>,
    P: NargProtocol,
{
    let instance_bytes = instance.encode_instance();
    let mut verifier =
        VerifierState::<H>::new(session_id, &PrefixFree(&instance_bytes), narg_string);
    let commitment = verifier
        .prover_message_as(|reader| instance.read_commitment(reader).map_err(|_| SpongeError))
        .map_err(|_| VerificationError)?;
    let challenge =
        verifier.verifier_message_as(CHALLENGE_LEN, P::Group::scalar_from_uniform_bytes);
    let response = verifier
        .prover_message_as(|reader| instance.read_response(reader).map_err(|_| SpongeError))
        .map_err(|_| VerificationError)?;
    let randomness =
        verifier.verifier_message_as(CHALLENGE_LEN, P::Group::scalar_from_uniform_bytes);
    verifier.check_eof().map_err(|_| VerificationError)?;
    instance.verify_randomized(&commitment, &challenge, &response, &randomness)
}

fn compact_challenge<H, P>(session_id: &SessionId, instance: &P, commitment_bytes: &[u8]) -> Scalar
where
    H: DuplexSpongeInit<U = u8>,
    P: NargProtocol,
{
    let instance_bytes = instance.encode_instance();
    let mut state = VerifierState::<H>::new(session_id, &PrefixFree(&instance_bytes), &[]);
    state.public_message(&PrefixFree(commitment_bytes));
    state.verifier_message_as(CHALLENGE_LEN, P::Group::scalar_from_uniform_bytes)
}

/// A compact proof: the challenge, then the response. A commitment with no
/// encoding is [`InvalidWitness`].
pub fn prove_compact_with<H, R, P>(
    session_id: &SessionId,
    instance: &P,
    witness: &P::Witness,
    rng: &mut PrivateRng<R>,
) -> Result<Vec<u8>, InvalidWitness>
where
    H: DuplexSpongeInit<U = u8>,
    R: DuplexSpongeInit<U = u8>,
    P: NargProtocol,
{
    let nonces = instance.draw_nonces(rng);
    let (commitment, state) = instance.commit(witness, &nonces)?;
    let commitment_bytes = instance
        .serialize_commitment(&commitment)
        .ok_or(InvalidWitness)?;
    let challenge = compact_challenge::<H, P>(session_id, instance, &commitment_bytes);
    let response = instance.respond(&state, &challenge)?;
    let mut narg_string = challenge.to_vec();
    narg_string.extend_from_slice(&instance.serialize_response(&response));
    Ok(narg_string)
}

/// Verifies a compact proof: recomputes the commitment from the challenge
/// and the response, then the challenge from the commitment. A recomputed
/// commitment with no encoding (draft-03, VerifyCompact step 7) fails.
pub fn verify_compact_with<H, P>(
    session_id: &SessionId,
    instance: &P,
    narg_string: &[u8],
) -> Result<(), VerificationError>
where
    H: DuplexSpongeInit<U = u8>,
    P: NargProtocol,
{
    let mut reader = NargReader::new(narg_string);
    let challenge = read_scalar::<P::Group>(&mut reader)?;
    let response = instance.read_response(&mut reader)?;
    if !reader.is_empty() {
        return Err(VerificationError);
    }
    let commitment = instance.simulate_commitment(&challenge, &response)?;
    let commitment_bytes = instance
        .serialize_commitment(&commitment)
        .ok_or(VerificationError)?;
    let expected = compact_challenge::<H, P>(session_id, instance, &commitment_bytes);
    compact_accept::<P::Group>(&challenge, &expected)
}
