//! The Ristretto255 instance of [`SigmaGroup`] (`curve25519-dalek`), and the
//! conversions between the core's encodings and the `curve25519-dalek` types.
//!
//! Compiled only outside the hax view (`cfg(not(hax))`): the extraction sees
//! the group operations as the trait's associated functions.
//!
//! A [`Scalar`] is the big-endian encoding of a scalar (the wire encoding;
//! `curve25519-dalek` stores little-endian), an [`Element`] the compressed
//! Ristretto encoding. The trait's functions decode their arguments and
//! panic on an encoding that is not canonical: the core only passes values
//! that this module produced or that [`decode_scalar`] / [`decode_element`]
//! accepted.
//!
//! Every element has exactly one Ristretto encoding, and decoding accepts
//! only that one, so `group_eq` compares the encodings, and `identity` and
//! `generator` are the constant encodings; none of the three decodes or
//! encodes a point.
//!
//! The multi-scalar multiplications are those of `curve25519-dalek`:
//! constant-time Straus ([`MultiscalarMul`]) for `msm` and variable-time
//! Straus/Pippenger ([`VartimeMultiscalarMul`]) for `msm_vartime` and for
//! each row of `msm_rows_vartime`, which decodes each distinct base of its
//! rows once. A scalar multiplication of the generator's encoding uses the
//! precomputed basepoint table.

use std::collections::HashMap;

use curve25519_dalek::constants::RISTRETTO_BASEPOINT_COMPRESSED;
use curve25519_dalek::ristretto::{CompressedRistretto, RistrettoPoint};
use curve25519_dalek::scalar::Scalar as DalekScalar;
use curve25519_dalek::traits::{Identity, MultiscalarMul, VartimeMultiscalarMul};

use crate::group::SigmaGroup;
use crate::types::{Element, Scalar};
use crate::wire::GroupWire;

/// The Ristretto255 group.
#[derive(Clone, Copy, Debug)]
pub struct Ristretto255;

/// The encoding of a `curve25519-dalek` scalar.
pub fn encode_scalar(s: &DalekScalar) -> Scalar {
    let mut bytes = s.to_bytes();
    bytes.reverse();
    bytes
}

/// The scalar of a canonical encoding.
pub fn decode_scalar(bytes: &Scalar) -> Option<DalekScalar> {
    let mut le = *bytes;
    le.reverse();
    Option::from(DalekScalar::from_canonical_bytes(le))
}

/// The encoding of a Ristretto point.
pub fn encode_element(p: &RistrettoPoint) -> Element {
    p.compress().to_bytes()
}

/// The point of a canonical encoding.
pub fn decode_element(bytes: &Element) -> Option<RistrettoPoint> {
    CompressedRistretto(*bytes).decompress()
}

/// `LE2IP(bytes) mod ℓ` for at most 64 bytes, the reduction of upstream's
/// `ScalarCodec::from_uniform_bytes`.
pub fn scalar_from_uniform_bytes(bytes: &[u8]) -> Scalar {
    let mut wide = [0u8; 64];
    wide[..bytes.len()].copy_from_slice(bytes);
    encode_scalar(&DalekScalar::from_bytes_mod_order_wide(&wide))
}

fn s(bytes: &Scalar) -> DalekScalar {
    decode_scalar(bytes).expect("canonical scalar encoding")
}

fn p(bytes: &Element) -> RistrettoPoint {
    decode_element(bytes).expect("canonical element encoding")
}

/// `scalar * point`. A point whose encoding is the generator's (a public
/// constant; encodings are canonical, so this is point equality) goes
/// through the precomputed basepoint table, any other through the
/// variable-base multiplication; both are constant time in the scalar.
fn mul_point(scalar: &DalekScalar, point: &Element) -> RistrettoPoint {
    if *point == RISTRETTO_BASEPOINT_COMPRESSED.0 {
        RistrettoPoint::mul_base(scalar)
    } else {
        p(point) * scalar
    }
}

/// The first `scalars.len()` terms decoded, each input once.
fn decode_terms(
    scalars: &[Scalar],
    bases: &[Element],
) -> (Vec<DalekScalar>, Vec<RistrettoPoint>) {
    let n = scalars.len();
    (scalars.iter().map(s).collect(), bases[..n].iter().map(p).collect())
}

impl SigmaGroup for Ristretto255 {
    fn scalar_zero() -> Scalar {
        encode_scalar(&DalekScalar::ZERO)
    }
    fn scalar_one() -> Scalar {
        encode_scalar(&DalekScalar::ONE)
    }
    fn scalar_add(a: &Scalar, b: &Scalar) -> Scalar {
        encode_scalar(&(s(a) + s(b)))
    }
    fn scalar_sub(a: &Scalar, b: &Scalar) -> Scalar {
        encode_scalar(&(s(a) - s(b)))
    }
    fn scalar_mul(a: &Scalar, b: &Scalar) -> Scalar {
        encode_scalar(&(s(a) * s(b)))
    }
    fn scalar_neg(a: &Scalar) -> Scalar {
        encode_scalar(&(-s(a)))
    }
    fn scalar_eq(a: &Scalar, b: &Scalar) -> bool {
        s(a) == s(b)
    }
    // The encodings of the identity (32 zero bytes) and of the basepoint.
    fn identity() -> Element {
        CompressedRistretto::identity().0
    }
    fn generator() -> Element {
        RISTRETTO_BASEPOINT_COMPRESSED.0
    }
    fn group_add(a: &Element, b: &Element) -> Element {
        encode_element(&(p(a) + p(b)))
    }
    fn group_mul(scalar: &Scalar, point: &Element) -> Element {
        encode_element(&mul_point(&s(scalar), point))
    }
    // Encodings are canonical: equal elements have equal encodings.
    fn group_eq(a: &Element, b: &Element) -> bool {
        a == b
    }
    // The dispatch is on the number of terms, which is public: zero terms
    // give the identity, one term is one scalar multiplication (faster than
    // Straus, as upstream measures), more go to dalek's constant-time Straus.
    fn msm(scalars: &[Scalar], bases: &[Element]) -> Element {
        match scalars.len() {
            0 => Self::identity(),
            1 => encode_element(&mul_point(&s(&scalars[0]), &bases[0])),
            _ => {
                let (ss, ps) = decode_terms(scalars, bases);
                encode_element(&RistrettoPoint::multiscalar_mul(&ss, &ps))
            }
        }
    }
    fn msm_vartime(scalars: &[Scalar], bases: &[Element]) -> Element {
        if scalars.len() == 0 {
            return Self::identity();
        }
        let (ss, ps) = decode_terms(scalars, bases);
        encode_element(&RistrettoPoint::vartime_multiscalar_mul(&ss, &ps))
    }
    // Each row is the MSM of `msm_vartime` on the same decoded terms; the
    // bases are decoded once per distinct encoding across all rows.
    fn msm_rows_vartime(rows: &[(Vec<Scalar>, Vec<Element>)]) -> Vec<Element> {
        let mut slot: HashMap<Element, usize> = HashMap::new();
        let mut points: Vec<RistrettoPoint> = Vec::new();
        for (scalars, bases) in rows {
            for base in &bases[..scalars.len()] {
                slot.entry(*base).or_insert_with(|| {
                    points.push(p(base));
                    points.len() - 1
                });
            }
        }
        rows.iter()
            .map(|(scalars, bases)| {
                if scalars.len() == 0 {
                    return Self::identity();
                }
                let ss: Vec<DalekScalar> = scalars.iter().map(s).collect();
                let ps = bases[..scalars.len()].iter().map(|b| &points[slot[b]]);
                encode_element(&RistrettoPoint::vartime_multiscalar_mul(&ss, ps))
            })
            .collect()
    }
}

impl GroupWire for Ristretto255 {
    const ELEMENT_LEN: usize = 32;
    fn element_to_wire(element: &Element) -> Vec<u8> {
        element.to_vec()
    }
    fn element_from_wire(bytes: &[u8]) -> Option<Element> {
        let bytes: Element = bytes.try_into().ok()?;
        decode_element(&bytes).map(|_| bytes)
    }
    fn scalar_is_canonical(scalar: &Scalar) -> bool {
        decode_scalar(scalar).is_some()
    }
    fn scalar_from_uniform_bytes(bytes: &[u8]) -> Scalar {
        scalar_from_uniform_bytes(bytes)
    }
}
