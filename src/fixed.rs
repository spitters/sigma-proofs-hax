//! Fixed-shape Σ-protocol functions for two relations, written in the domain
//! of a compiler front that accepts fixed-size arrays of 64-bit words.
//!
//! The relations are Schnorr's (one scalar `x`, one equation `X = x * G`) and
//! DLEQ (one scalar `x`, two equations `X = x * G` and `Y = x * H`), where `G`
//! is the generator. Each entry function computes the value of a function of
//! the generic core ([`crate::protocol`], [`crate::codec`]) on the instance of
//! its relation that [`Instance::new`](crate::Instance::new) builds with unit
//! coefficients: element vector `[G, X]` and the equation
//! `image [(1, 1)], terms [(0, 0, 1)]` for Schnorr; element vector
//! `[G, H, X, Y]` and the equations `image [(2, 1)], terms [(0, 0, 1)]` and
//! `image [(3, 1)], terms [(0, 1, 1)]` for DLEQ. `tests/fixed.rs` checks each
//! against the generic core on random inputs.
//!
//! The interface:
//!
//! - Parameters and results are 64-bit words and arrays of 64-bit words of
//!   constant length. A 32-byte scalar or element encoding is a `[u64; 4]`:
//!   byte `8k + j` of the encoding is bits `8j` to `8j + 7` of limb `k`, the
//!   memory image of the encoding on a little-endian machine
//!   ([`fixed_bytes_to_limbs`], [`fixed_limbs_to_bytes`]). A pair of elements
//!   (the DLEQ image `(X, Y)` and the DLEQ commitment) is a `[u64; 8]` with the
//!   first element in limbs 0 to 3 ([`fixed_pair`]).
//! - A verdict is a status word: 0 accepts, 1 rejects.
//! - The group and field operations are the associated functions of
//!   [`SigmaGroup`] on the 32-byte encodings, and every call of one returns an
//!   encoding. Two encodings are compared limb by limb ([`fixed_eq`]): the
//!   encodings are canonical, so two of them are equal exactly when the group
//!   elements (or scalars) are, and [`SigmaGroup::group_eq`] and
//!   [`SigmaGroup::scalar_eq`], whose results are Booleans, are not called.
//!
//! The source keeps to the front's domain: counted loops from 0 with constant
//! bounds, array indices that are a loop counter plus a constant, arrays built
//! from `[0; n]` by element updates, and no struct, slice, `Vec`, enum,
//! `Result`, closure, iterator or `&mut`. The extraction drops module paths,
//! so every name carries the prefix `fixed_`, `schnorr_` or `dleq_`
//! ([`crate::protocol::compact_accept`] is another function).

// The extracted subset copies arrays element by element.
#![allow(clippy::manual_memcpy)]

use crate::group::SigmaGroup;

// ---------------------------------------------------------------------------
// Encodings as limbs
// ---------------------------------------------------------------------------

/// The four little-endian 64-bit limbs of a 32-byte encoding: limb `k` holds
/// bytes `8k` to `8k + 7`, byte `8k + j` at bits `8j` to `8j + 7`.
pub fn fixed_bytes_to_limbs(bytes: [u8; 32]) -> [u64; 4] {
    let mut out = [0u64; 4];
    for j in 0..8 {
        let shift = (8 * j) as u64;
        out[0] = out[0] | ((bytes[j] as u64) << shift);
        out[1] = out[1] | ((bytes[j + 8] as u64) << shift);
        out[2] = out[2] | ((bytes[j + 16] as u64) << shift);
        out[3] = out[3] | ((bytes[j + 24] as u64) << shift);
    }
    out
}

/// The 32-byte encoding of four little-endian limbs, the inverse of
/// [`fixed_bytes_to_limbs`].
pub fn fixed_limbs_to_bytes(limbs: [u64; 4]) -> [u8; 32] {
    let mut out = [0u8; 32];
    for j in 0..8 {
        let shift = (8 * j) as u64;
        out[j] = (limbs[0] >> shift) as u8;
        out[j + 8] = (limbs[1] >> shift) as u8;
        out[j + 16] = (limbs[2] >> shift) as u8;
        out[j + 24] = (limbs[3] >> shift) as u8;
    }
    out
}

/// The pair of two encodings: `first` in limbs 0 to 3, `second` in limbs 4
/// to 7.
pub fn fixed_pair(first: [u64; 4], second: [u64; 4]) -> [u64; 8] {
    let mut out = [0u64; 8];
    for i in 0..4 {
        out[i] = first[i];
        out[i + 4] = second[i];
    }
    out
}

/// The first encoding of a pair (limbs 0 to 3).
pub fn fixed_first(pair: [u64; 8]) -> [u64; 4] {
    let mut out = [0u64; 4];
    for i in 0..4 {
        out[i] = pair[i];
    }
    out
}

/// The second encoding of a pair (limbs 4 to 7).
pub fn fixed_second(pair: [u64; 8]) -> [u64; 4] {
    let mut out = [0u64; 4];
    for i in 0..4 {
        out[i] = pair[i + 4];
    }
    out
}

/// 0 when the encodings `a` and `b` are equal, 1 otherwise, without a
/// branch: the OR of the limb differences is 0 exactly when they are equal,
/// and the top bit of `d | -d` is 1 exactly when `d` is not 0.
pub fn fixed_eq(a: [u64; 4], b: [u64; 4]) -> u64 {
    let mut acc: u64 = 0;
    for i in 0..4 {
        acc = acc | (a[i] ^ b[i]);
    }
    (acc | acc.wrapping_neg()) >> 63
}

// ---------------------------------------------------------------------------
// Shared by both relations
// ---------------------------------------------------------------------------

/// The last check of a compact proof, [`crate::protocol::compact_accept`]: 0
/// when the transmitted challenge equals the recomputed one. Both are
/// canonical scalar encodings (the wire layer reads only canonical scalars and
/// the challenge derivation reduces), so encoding equality is
/// `SigmaGroup::scalar_eq`.
pub fn fixed_compact_accept(challenge: [u64; 4], expected: [u64; 4]) -> u64 {
    fixed_eq(challenge, expected)
}

/// The check of `Group.serialize` on one element
/// ([`crate::codec::serialize_elements`]): 0 when `element` has an encoding,
/// that is, is not the identity; 1 for the identity. A recomputed compact
/// commitment without an encoding fails verification (draft-03,
/// `VerifyCompact` step 7).
pub fn fixed_encodable<C: SigmaGroup>(element: [u64; 4]) -> u64 {
    let identity_limbs = fixed_bytes_to_limbs(C::identity());
    fixed_eq(element, identity_limbs) ^ 1
}

// ---------------------------------------------------------------------------
// Schnorr: X = x * G
// ---------------------------------------------------------------------------

/// `ProverCommitment` ([`Instance::prover_commit`](crate::Instance::prover_commit)):
/// the commitment `nonce * G`, the linear map at the nonce.
pub fn schnorr_commit<C: SigmaGroup>(nonce: [u64; 4]) -> [u64; 4] {
    let k = fixed_limbs_to_bytes(nonce);
    let g = C::generator();
    let a = C::group_mul(&k, &g);
    fixed_bytes_to_limbs(a)
}

/// `ProverResponse` ([`Instance::prover_response`](crate::Instance::prover_response)):
/// `nonce + witness * challenge`.
pub fn schnorr_response<C: SigmaGroup>(
    witness: [u64; 4],
    nonce: [u64; 4],
    challenge: [u64; 4],
) -> [u64; 4] {
    let x = fixed_limbs_to_bytes(witness);
    let k = fixed_limbs_to_bytes(nonce);
    let c = fixed_limbs_to_bytes(challenge);
    let product = C::scalar_mul(&x, &c);
    let z = C::scalar_add(&k, &product);
    fixed_bytes_to_limbs(z)
}

/// `SimulateCommitment`
/// ([`Instance::simulate_commitment`](crate::Instance::simulate_commitment)):
/// the commitment `response * G + (-challenge) * X` for which
/// `(challenge, response)` verifies against the image `X`. With the
/// simulator's randomness as `response` it is the commitment of
/// [`Instance::simulate_transcript`](crate::Instance::simulate_transcript),
/// whose response is that randomness.
pub fn schnorr_simulate_commitment<C: SigmaGroup>(
    image: [u64; 4],
    challenge: [u64; 4],
    response: [u64; 4],
) -> [u64; 4] {
    let x_point = fixed_limbs_to_bytes(image);
    let c = fixed_limbs_to_bytes(challenge);
    let z = fixed_limbs_to_bytes(response);
    let negated = C::scalar_neg(&c);
    let g = C::generator();
    let row = C::group_mul(&z, &g);
    let shift = C::group_mul(&negated, &x_point);
    let a = C::group_add(&row, &shift);
    fixed_bytes_to_limbs(a)
}

/// `Verifier` ([`Instance::verifier`](crate::Instance::verifier)): 0 when
/// `commitment` is the simulated commitment of `(challenge, response)`, that
/// is, `response * G = commitment + challenge * X`. This is also the check of
/// a batchable proof: on an instance of one equation
/// [`Instance::verifier_with_randomness`](crate::Instance::verifier_with_randomness)
/// is the verifier and reads no randomness.
pub fn schnorr_verify<C: SigmaGroup>(
    image: [u64; 4],
    commitment: [u64; 4],
    challenge: [u64; 4],
    response: [u64; 4],
) -> u64 {
    let expected = schnorr_simulate_commitment::<C>(image, challenge, response);
    fixed_eq(expected, commitment)
}

/// The commitment a compact proof `(challenge, response)` stands for
/// ([`Instance::compact_commitment`](crate::Instance::compact_commitment)),
/// the simulated commitment.
pub fn schnorr_compact_commitment<C: SigmaGroup>(
    image: [u64; 4],
    challenge: [u64; 4],
    response: [u64; 4],
) -> [u64; 4] {
    schnorr_simulate_commitment::<C>(image, challenge, response)
}

// ---------------------------------------------------------------------------
// DLEQ: X = x * G, Y = x * H
// ---------------------------------------------------------------------------

/// `ProverCommitment`: the commitment `(nonce * G, nonce * H)`.
pub fn dleq_commit<C: SigmaGroup>(h: [u64; 4], nonce: [u64; 4]) -> [u64; 8] {
    let h_point = fixed_limbs_to_bytes(h);
    let k = fixed_limbs_to_bytes(nonce);
    let g = C::generator();
    let a0 = C::group_mul(&k, &g);
    let a1 = C::group_mul(&k, &h_point);
    fixed_pair(fixed_bytes_to_limbs(a0), fixed_bytes_to_limbs(a1))
}

/// `ProverResponse`: `nonce + witness * challenge`, the response of
/// [`schnorr_response`] (one scalar).
pub fn dleq_response<C: SigmaGroup>(
    witness: [u64; 4],
    nonce: [u64; 4],
    challenge: [u64; 4],
) -> [u64; 4] {
    schnorr_response::<C>(witness, nonce, challenge)
}

/// `SimulateCommitment`: the commitment
/// `(response * G + (-challenge) * X, response * H + (-challenge) * Y)` for the
/// image `(X, Y)`; with the simulator's randomness as `response`, the
/// commitment of the simulated transcript.
pub fn dleq_simulate_commitment<C: SigmaGroup>(
    h: [u64; 4],
    image: [u64; 8],
    challenge: [u64; 4],
    response: [u64; 4],
) -> [u64; 8] {
    let h_point = fixed_limbs_to_bytes(h);
    let x_point = fixed_limbs_to_bytes(fixed_first(image));
    let y_point = fixed_limbs_to_bytes(fixed_second(image));
    let c = fixed_limbs_to_bytes(challenge);
    let z = fixed_limbs_to_bytes(response);
    let negated = C::scalar_neg(&c);
    let g = C::generator();
    let row0 = C::group_mul(&z, &g);
    let shift0 = C::group_mul(&negated, &x_point);
    let a0 = C::group_add(&row0, &shift0);
    let row1 = C::group_mul(&z, &h_point);
    let shift1 = C::group_mul(&negated, &y_point);
    let a1 = C::group_add(&row1, &shift1);
    fixed_pair(fixed_bytes_to_limbs(a0), fixed_bytes_to_limbs(a1))
}

/// The check of a batchable proof
/// ([`Instance::verifier_with_randomness`](crate::Instance::verifier_with_randomness)):
/// the two verification equations combined with the weights `1` and
/// `randomness`. With `(A0, A1)` the commitment, `c` the challenge and `z` the
/// response, 0 when
///
/// `A0 + r * A1 + (-z) * G + (-(r * z)) * H + c * X + (r * c) * Y`
///
/// is the identity: the multi-scalar multiplication of the generic verifier,
/// whose terms are the commitment at the powers `1, r` of the randomness and
/// the elements `G, H, X, Y` at their accumulated weights, summed in that
/// order.
pub fn dleq_verify_batchable<C: SigmaGroup>(
    h: [u64; 4],
    image: [u64; 8],
    commitment: [u64; 8],
    challenge: [u64; 4],
    response: [u64; 4],
    randomness: [u64; 4],
) -> u64 {
    let h_point = fixed_limbs_to_bytes(h);
    let x_point = fixed_limbs_to_bytes(fixed_first(image));
    let y_point = fixed_limbs_to_bytes(fixed_second(image));
    let a0 = fixed_limbs_to_bytes(fixed_first(commitment));
    let a1 = fixed_limbs_to_bytes(fixed_second(commitment));
    let c = fixed_limbs_to_bytes(challenge);
    let z = fixed_limbs_to_bytes(response);
    let r = fixed_limbs_to_bytes(randomness);
    let g = C::generator();
    // The weights: `r * c` on Y, `-z` on G, `-(r * z)` on H; `c` is the
    // weight of X.
    let rc = C::scalar_mul(&r, &c);
    let rz = C::scalar_mul(&r, &z);
    let weight_g = C::scalar_neg(&z);
    let weight_h = C::scalar_neg(&rz);
    let t1 = C::group_mul(&r, &a1);
    let s1 = C::group_add(&a0, &t1);
    let t2 = C::group_mul(&weight_g, &g);
    let s2 = C::group_add(&s1, &t2);
    let t3 = C::group_mul(&weight_h, &h_point);
    let s3 = C::group_add(&s2, &t3);
    let t4 = C::group_mul(&c, &x_point);
    let s4 = C::group_add(&s3, &t4);
    let t5 = C::group_mul(&rc, &y_point);
    let total = C::group_add(&s4, &t5);
    let identity_limbs = fixed_bytes_to_limbs(C::identity());
    fixed_eq(fixed_bytes_to_limbs(total), identity_limbs)
}

/// The commitment a compact proof `(challenge, response)` stands for, the
/// simulated commitment.
pub fn dleq_compact_commitment<C: SigmaGroup>(
    h: [u64; 4],
    image: [u64; 8],
    challenge: [u64; 4],
    response: [u64; 4],
) -> [u64; 8] {
    dleq_simulate_commitment::<C>(h, image, challenge, response)
}

/// The check of `Group.serialize` on a DLEQ commitment: 0 when neither
/// element is the identity.
pub fn dleq_encodable<C: SigmaGroup>(commitment: [u64; 8]) -> u64 {
    let first = fixed_encodable::<C>(fixed_first(commitment));
    let second = fixed_encodable::<C>(fixed_second(commitment));
    first | second
}
