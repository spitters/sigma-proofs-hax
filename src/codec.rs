//! Serialization of instances and protocol messages (the specification's
//! `SerializeLinearRelation` and the message encodings,
//! draft-irtf-cfrg-sigma-protocols-03, Sections 2.3 and 3.6). Scalars and
//! elements are already in their wire encodings, so serializing concatenates
//! them; counts and indices are 4-byte little-endian. `Group.serialize` fails
//! on the identity.

use crate::group::SigmaGroup;
use crate::types::{Element, Instance, Scalar};

/// `out` followed by the 4-byte little-endian encoding of `x`.
pub fn push_u32_le(out: Vec<u8>, x: u32) -> Vec<u8> {
    let mut bytes = out;
    bytes.push((x & 255) as u8);
    bytes.push(((x >> 8) & 255) as u8);
    bytes.push(((x >> 16) & 255) as u8);
    bytes.push(((x >> 24) & 255) as u8);
    bytes
}

/// `out` followed by the 32 bytes of `bytes`.
pub fn push_bytes32(out: Vec<u8>, bytes: &[u8; 32]) -> Vec<u8> {
    let mut extended = out;
    for i in 0..32 {
        extended.push(bytes[i]);
    }
    extended
}

/// `Group.serialize(elements)`: the concatenated encodings of `elements`, or
/// `None` if one of them is the identity, which has no encoding.
pub fn serialize_elements<C: SigmaGroup>(elements: &[Element]) -> Option<Vec<u8>> {
    let mut out = Vec::new();
    let mut encodable = true;
    for i in 0..elements.len() {
        if C::group_eq(&elements[i], &C::identity()) {
            encodable = false;
        }
        out = push_bytes32(out, &elements[i]);
    }
    if encodable {
        Some(out)
    } else {
        None
    }
}

/// The concatenated encodings of `scalars`.
pub fn serialize_scalars(scalars: &[Scalar]) -> Vec<u8> {
    let mut out = Vec::new();
    for i in 0..scalars.len() {
        out = push_bytes32(out, &scalars[i]);
    }
    out
}

impl Instance {
    /// `SerializeLinearRelation`: the equation count, then per equation its
    /// image terms and its right-hand-side terms (each list preceded by its
    /// count), then the statement's elements (from index 1). The elements of
    /// a validated instance are not the identity (check 8), so they are
    /// concatenated as they are.
    pub fn serialize(&self) -> Vec<u8> {
        let mut out = Vec::new();
        out = push_u32_le(out, self.equations.len() as u32);
        for j in 0..self.equations.len() {
            let equation = &self.equations[j];
            out = push_u32_le(out, equation.image.len() as u32);
            for k in 0..equation.image.len() {
                let (element_index, coeff) = equation.image[k];
                out = push_u32_le(out, element_index);
                out = push_bytes32(out, &coeff);
            }
            out = push_u32_le(out, equation.terms.len() as u32);
            for k in 0..equation.terms.len() {
                let (scalar_index, element_index, coeff) = equation.terms[k];
                out = push_u32_le(out, scalar_index);
                out = push_u32_le(out, element_index);
                out = push_bytes32(out, &coeff);
            }
        }
        for i in 1..self.elements.len() {
            out = push_bytes32(out, &self.elements[i]);
        }
        out
    }
}
