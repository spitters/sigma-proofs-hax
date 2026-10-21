//! The fixed-shape functions of `sigma_proofs_hax::fixed` against the generic
//! core of the same crate, over Ristretto255, on random inputs.
//!
//! The generic side runs on the instances that `Instance::new` builds for
//! Schnorr (`X = x * G`) and DLEQ (`X = x * G`, `Y = x * H`) with unit
//! coefficients. For each relation the test compares the prover commitment
//! and response from the same witness, nonce and challenge; the verifier
//! (for DLEQ the batchable verifier, one random linear combination) on the
//! honest transcript, on transcripts with one component replaced, on a false
//! statement and on random transcripts; the simulated commitment and the
//! acceptance of the simulated transcript; the compact commitment, the
//! compact acceptance and the encodability check of `Group.serialize`. The
//! limb conversions are compared with `u64::from_le_bytes`.

#![allow(clippy::type_complexity)]

use sigma_proofs_hax as fk;

use fk::codec::serialize_elements;
use fk::fixed::*;
use fk::protocol::compact_accept;
use fk::ristretto::{scalar_from_uniform_bytes, Ristretto255 as R};
use fk::{Element, Equation, Instance, Scalar, SigmaGroup};

const ROUNDS: u64 = 32;

/// A deterministic generator (splitmix64).
struct Prng(u64);

impl Prng {
    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    /// A uniform scalar: 64 random bytes reduced modulo the group order.
    fn scalar(&mut self) -> Scalar {
        let mut wide = [0u8; 64];
        for k in 0..8 {
            wide[8 * k..8 * k + 8].copy_from_slice(&self.next_u64().to_le_bytes());
        }
        scalar_from_uniform_bytes(&wide)
    }

    /// A uniform group element.
    fn element(&mut self) -> Element {
        R::group_mul(&self.scalar(), &R::generator())
    }

    fn limbs(&mut self) -> [u64; 4] {
        [self.next_u64(), self.next_u64(), self.next_u64(), self.next_u64()]
    }
}

/// The little-endian limbs of an encoding, computed with `u64::from_le_bytes`.
fn limbs(bytes: &[u8; 32]) -> [u64; 4] {
    let mut out = [0u64; 4];
    for (k, limb) in out.iter_mut().enumerate() {
        let mut chunk = [0u8; 8];
        chunk.copy_from_slice(&bytes[8 * k..8 * k + 8]);
        *limb = u64::from_le_bytes(chunk);
    }
    out
}

/// The limbs of a pair of encodings, the first in limbs 0 to 3.
fn pair(first: &[u8; 32], second: &[u8; 32]) -> [u64; 8] {
    let a = limbs(first);
    let b = limbs(second);
    [a[0], a[1], a[2], a[3], b[0], b[1], b[2], b[3]]
}

/// The status word of a verdict of the generic core.
fn status<E>(verdict: &Result<(), E>) -> u64 {
    if verdict.is_ok() {
        0
    } else {
        1
    }
}

/// `s + 1`.
fn bump(s: &Scalar) -> Scalar {
    R::scalar_add(s, &R::scalar_one())
}

/// The Schnorr instance: elements `[G, X]`, the equation `X = 1 * (x * G)`.
fn schnorr_instance(x: &Element) -> Instance {
    let one = R::scalar_one();
    Instance::new::<R>(
        vec![*x],
        vec![Equation {
            image: vec![(1, one)],
            terms: vec![(0, 0, one)],
        }],
    )
    .expect("a valid Schnorr instance")
}

/// The DLEQ instance: elements `[G, H, X, Y]`, the equations `X = x * G` and
/// `Y = x * H`.
fn dleq_instance(h: &Element, x: &Element, y: &Element) -> Instance {
    let one = R::scalar_one();
    Instance::new::<R>(
        vec![*h, *x, *y],
        vec![
            Equation {
                image: vec![(2, one)],
                terms: vec![(0, 0, one)],
            },
            Equation {
                image: vec![(3, one)],
                terms: vec![(0, 1, one)],
            },
        ],
    )
    .expect("a valid DLEQ instance")
}

#[test]
fn limb_conversions_agree() {
    let mut rng = Prng(1);
    for _ in 0..ROUNDS {
        let a = rng.element();
        let b = rng.element();
        let s = rng.scalar();
        for bytes in [a, b, s] {
            assert_eq!(fixed_bytes_to_limbs(bytes), limbs(&bytes));
            assert_eq!(fixed_limbs_to_bytes(limbs(&bytes)), bytes);
        }
        let l = rng.limbs();
        assert_eq!(fixed_bytes_to_limbs(fixed_limbs_to_bytes(l)), l);
        let p = fixed_pair(limbs(&a), limbs(&b));
        assert_eq!(p, pair(&a, &b));
        assert_eq!(fixed_first(p), limbs(&a));
        assert_eq!(fixed_second(p), limbs(&b));
        assert_eq!(fixed_eq(limbs(&a), limbs(&a)), 0);
        assert_eq!(fixed_eq(limbs(&a), limbs(&b)), u64::from(a != b));
        let mut c = a;
        c[31] ^= 0x80;
        assert_eq!(fixed_eq(limbs(&a), limbs(&c)), 1);
    }
}

#[test]
fn schnorr_agrees() {
    let mut rng = Prng(2);
    for _ in 0..ROUNDS {
        let x = rng.scalar();
        let big_x = R::group_mul(&x, &R::generator());
        let instance = schnorr_instance(&big_x);
        let k = rng.scalar();
        let c = rng.scalar();
        let r = rng.scalar();

        // Prover.
        let (commitment, state) = instance.prover_commit::<R>(&[x], &[k]).unwrap();
        assert_eq!(schnorr_commit::<R>(limbs(&k)), limbs(&commitment[0]));
        let response = instance.prover_response::<R>(&state, &c).unwrap();
        assert_eq!(
            schnorr_response::<R>(limbs(&x), limbs(&k), limbs(&c)),
            limbs(&response[0])
        );

        // Verifier: the honest transcript first, then altered ones.
        let other = rng.element();
        let cases: Vec<(Element, Element, Scalar, Scalar)> = vec![
            (big_x, commitment[0], c, response[0]),
            (big_x, commitment[0], c, bump(&response[0])),
            (big_x, commitment[0], bump(&c), response[0]),
            (big_x, other, c, response[0]),
            (other, commitment[0], c, response[0]),
            (big_x, rng.element(), rng.scalar(), rng.scalar()),
        ];
        for (i, (statement, a, challenge, z)) in cases.iter().enumerate() {
            let generic = schnorr_instance(statement);
            let plain = generic.verifier::<R>(&[*a], challenge, &[*z]);
            let batch = generic.verifier_with_randomness::<R>(&[*a], challenge, &[*z], &r);
            let fixed =
                schnorr_verify::<R>(limbs(statement), limbs(a), limbs(challenge), limbs(z));
            assert_eq!(fixed, status(&plain), "Schnorr verifier, case {i}");
            assert_eq!(fixed, status(&batch), "Schnorr batchable verifier, case {i}");
            if i == 0 {
                assert_eq!(fixed, 0, "the honest Schnorr transcript is accepted");
            }
        }

        // Simulator.
        let randomness = rng.scalar();
        let sim_challenge = rng.scalar();
        let (sim_commitment, sim_c, sim_response) = instance
            .simulate_transcript::<R>(&[randomness], &sim_challenge)
            .unwrap();
        assert_eq!(sim_response, vec![randomness]);
        assert_eq!(
            schnorr_simulate_commitment::<R>(
                limbs(&big_x),
                limbs(&sim_challenge),
                limbs(&randomness)
            ),
            limbs(&sim_commitment[0])
        );
        assert_eq!(
            schnorr_verify::<R>(
                limbs(&big_x),
                limbs(&sim_commitment[0]),
                limbs(&sim_c),
                limbs(&sim_response[0])
            ),
            0
        );

        // Compact proofs.
        let compact = instance.compact_commitment::<R>(&c, &response).unwrap();
        assert_eq!(compact, commitment);
        assert_eq!(
            schnorr_compact_commitment::<R>(limbs(&big_x), limbs(&c), limbs(&response[0])),
            limbs(&compact[0])
        );
        for (challenge, expected) in [(c, c), (c, bump(&c)), (c, rng.scalar())] {
            assert_eq!(
                fixed_compact_accept(limbs(&challenge), limbs(&expected)),
                status(&compact_accept::<R>(&challenge, &expected))
            );
        }
        for element in [commitment[0], R::identity()] {
            assert_eq!(
                fixed_encodable::<R>(limbs(&element)),
                u64::from(serialize_elements::<R>(&[element]).is_none())
            );
        }
    }
}

#[test]
fn dleq_agrees() {
    let mut rng = Prng(3);
    for _ in 0..ROUNDS {
        let x = rng.scalar();
        let h = rng.element();
        let big_x = R::group_mul(&x, &R::generator());
        let big_y = R::group_mul(&x, &h);
        let instance = dleq_instance(&h, &big_x, &big_y);
        let k = rng.scalar();
        let c = rng.scalar();
        let r = rng.scalar();

        // Prover.
        let (commitment, state) = instance.prover_commit::<R>(&[x], &[k]).unwrap();
        assert_eq!(commitment.len(), 2);
        assert_eq!(
            dleq_commit::<R>(limbs(&h), limbs(&k)),
            pair(&commitment[0], &commitment[1])
        );
        let response = instance.prover_response::<R>(&state, &c).unwrap();
        assert_eq!(
            dleq_response::<R>(limbs(&x), limbs(&k), limbs(&c)),
            limbs(&response[0])
        );

        // Batchable verifier: the honest transcript first, then altered ones
        // and a false statement (`Y` not `x * H`).
        let a0 = commitment[0];
        let a1 = commitment[1];
        let z = response[0];
        let other = rng.element();
        let y_false = rng.element();
        let cases: Vec<([Element; 3], [Element; 2], Scalar, Scalar)> = vec![
            ([h, big_x, big_y], [a0, a1], c, z),
            ([h, big_x, big_y], [a0, a1], c, bump(&z)),
            ([h, big_x, big_y], [a0, a1], bump(&c), z),
            ([h, big_x, big_y], [a0, other], c, z),
            ([h, big_x, big_y], [other, a1], c, z),
            ([h, big_x, big_y], [a1, a0], c, z),
            ([h, big_x, y_false], [a0, a1], c, z),
            ([other, big_x, big_y], [a0, a1], c, z),
            (
                [h, big_x, big_y],
                [rng.element(), rng.element()],
                rng.scalar(),
                rng.scalar(),
            ),
        ];
        for (i, ([hh, xx, yy], [b0, b1], challenge, resp)) in cases.iter().enumerate() {
            let generic = dleq_instance(hh, xx, yy);
            let batch =
                generic.verifier_with_randomness::<R>(&[*b0, *b1], challenge, &[*resp], &r);
            let fixed = dleq_verify_batchable::<R>(
                limbs(hh),
                pair(xx, yy),
                pair(b0, b1),
                limbs(challenge),
                limbs(resp),
                limbs(&r),
            );
            assert_eq!(fixed, status(&batch), "DLEQ batchable verifier, case {i}");
            if i == 0 {
                assert_eq!(fixed, 0, "the honest DLEQ transcript is accepted");
            }
        }

        // Simulator.
        let randomness = rng.scalar();
        let sim_challenge = rng.scalar();
        let (sim_commitment, sim_c, sim_response) = instance
            .simulate_transcript::<R>(&[randomness], &sim_challenge)
            .unwrap();
        assert_eq!(sim_response, vec![randomness]);
        let fixed_sim = dleq_simulate_commitment::<R>(
            limbs(&h),
            pair(&big_x, &big_y),
            limbs(&sim_challenge),
            limbs(&randomness),
        );
        assert_eq!(fixed_sim, pair(&sim_commitment[0], &sim_commitment[1]));
        assert_eq!(
            dleq_verify_batchable::<R>(
                limbs(&h),
                pair(&big_x, &big_y),
                fixed_sim,
                limbs(&sim_c),
                limbs(&sim_response[0]),
                limbs(&r),
            ),
            0
        );

        // Compact proofs.
        let compact = instance.compact_commitment::<R>(&c, &response).unwrap();
        assert_eq!(compact, commitment);
        assert_eq!(
            dleq_compact_commitment::<R>(limbs(&h), pair(&big_x, &big_y), limbs(&c), limbs(&z)),
            pair(&compact[0], &compact[1])
        );
        let identity = R::identity();
        for elements in [[a0, a1], [identity, a1], [a0, identity]] {
            assert_eq!(
                dleq_encodable::<R>(pair(&elements[0], &elements[1])),
                u64::from(serialize_elements::<R>(&elements).is_none())
            );
        }
    }
}
