//! Wire codecs over the core: the byte encodings of a group's elements and
//! scalars, and the instance encodings of draft-irtf-cfrg-sigma-protocols-03
//! and of `sigma-proofs` 0.4.1.
//!
//! Compiled only outside the hax view (`cfg(not(hax))`).
//!
//! The core holds an element as a 32-byte value that the group
//! implementation interprets ([`Element`]). For Ristretto255 that value is
//! the wire encoding; a group whose encoding is longer (P-256: 33 bytes,
//! BLS12-381 G1: 48 bytes) can hold a handle instead. [`GroupWire`] gives the
//! wire encoding of the core's values. Scalars are 32-byte big-endian
//! encodings in the core and on the wire for every group used here.
//!
//! The element codec follows draft-03 (Section 2.3.1): `Group.serialize` and
//! `Group.deserialize` fail on the identity, in instances and in prover
//! messages alike.
//!
//! The two instance encodings ([`InstanceFormat`]) share the layout of
//! `SerializeLinearRelation` and differ in the element indexing only:
//!
//! - [`InstanceFormat::Draft03`] (draft-03, Sections 3.2 and 3.6, and the
//!   core's [`Instance::serialize`]): the generator is element 0 and the
//!   statement elements follow from index 1. Wire index `i` is core index `i`.
//! - [`InstanceFormat::ImplicitIdentity`] (upstream 0.4.1): the identity and
//!   the generator are implicit at element indices 0 and 1, and the statement
//!   elements follow from index 2. Wire index `i + 1` is core index `i`; wire
//!   index 0, upstream's identity slot, has no core index, and an encoding
//!   that refers to it is rejected (as check 8: the instance would contain
//!   the identity).

use core::marker::PhantomData;

use spongefish::{NargReader, VerificationError as SpongeError};

use crate::codec::push_u32_le;
use crate::group::SigmaGroup;
use crate::types::{Element, Equation, Instance, InvalidInstance, Scalar, VerificationError};

/// `Ns`, the length of a scalar encoding.
pub const SCALAR_LEN: usize = 32;

/// The challenge width: the scalar length plus 16 bytes of wide reduction.
pub const CHALLENGE_LEN: usize = SCALAR_LEN + 16;

/// The wire codec of a [`SigmaGroup`] instance.
pub trait GroupWire: SigmaGroup {
    /// `Ne`, the length of an element encoding.
    const ELEMENT_LEN: usize;
    /// The canonical encoding of the curve point; the identity has one. The
    /// draft-03 codec ([`element_to_wire`]) refuses it.
    fn element_to_wire(element: &Element) -> Vec<u8>;
    /// The element of a canonical encoding of `ELEMENT_LEN` bytes (the
    /// identity's included); `None` for any other byte string. The draft-03
    /// codec ([`read_element`]) rejects the identity.
    fn element_from_wire(bytes: &[u8]) -> Option<Element>;
    /// Whether `scalar` is a canonical encoding: big-endian, below the group
    /// order.
    fn scalar_is_canonical(scalar: &Scalar) -> bool;
    /// `DecodeField(bytes, p, 1)`: `LE2IP(bytes) mod p`.
    fn scalar_from_uniform_bytes(bytes: &[u8]) -> Scalar;
}

/// The instance encoding: the element indexing on the wire.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum InstanceFormat {
    /// Upstream `sigma-proofs` 0.4.1: identity and generator at 0 and 1.
    ImplicitIdentity,
    /// draft-irtf-cfrg-sigma-protocols-03: generator at 0, no identity.
    Draft03,
}

impl InstanceFormat {
    /// The wire index of core index 0.
    fn offset(self) -> u32 {
        match self {
            InstanceFormat::ImplicitIdentity => 1,
            InstanceFormat::Draft03 => 0,
        }
    }
}

/// The core index of a wire index; `None` for upstream's identity slot.
pub fn core_index(format: InstanceFormat, wire_index: u32) -> Option<u32> {
    wire_index.checked_sub(format.offset())
}

/// The wire index of a core index; `None` if it does not fit in `u32`.
pub fn wire_index(format: InstanceFormat, core_index: u32) -> Option<u32> {
    core_index.checked_add(format.offset())
}

/// The equations with their element indices mapped from `format` to the
/// core's; an equation that refers to upstream's identity slot is rejected
/// (as check 8).
pub fn core_equations(
    format: InstanceFormat,
    equations: &[Equation],
) -> Result<Vec<Equation>, InvalidInstance> {
    let identity_slot = InvalidInstance { check: Some(8) };
    let mut out = Vec::with_capacity(equations.len());
    for equation in equations {
        let mut image = Vec::with_capacity(equation.image.len());
        for &(element_index, coeff) in &equation.image {
            let element_index = core_index(format, element_index).ok_or(identity_slot)?;
            image.push((element_index, coeff));
        }
        let mut terms = Vec::with_capacity(equation.terms.len());
        for &(scalar_index, element_index, coeff) in &equation.terms {
            let element_index = core_index(format, element_index).ok_or(identity_slot)?;
            terms.push((scalar_index, element_index, coeff));
        }
        out.push(Equation { image, terms });
    }
    Ok(out)
}

/// `Group.serialize([element])`; `None` for the identity.
pub fn element_to_wire<W: GroupWire>(element: &Element) -> Option<Vec<u8>> {
    if W::group_eq(element, &W::identity()) {
        return None;
    }
    Some(W::element_to_wire(element))
}

/// `Group.serialize(elements)`; `None` if one of them is the identity.
pub fn serialize_elements<W: GroupWire>(elements: &[Element]) -> Option<Vec<u8>> {
    let mut out = Vec::with_capacity(elements.len() * W::ELEMENT_LEN);
    for element in elements {
        out.extend_from_slice(&element_to_wire::<W>(element)?);
    }
    Some(out)
}

/// Reads one element (`Group.deserialize`); an invalid encoding and the
/// identity are rejected.
pub fn read_element<W: GroupWire>(reader: &mut NargReader<'_>) -> Result<Element, VerificationError> {
    let bytes = reader.take(W::ELEMENT_LEN).map_err(|_| VerificationError)?;
    let element = W::element_from_wire(bytes).ok_or(VerificationError)?;
    if W::group_eq(&element, &W::identity()) {
        return Err(VerificationError);
    }
    Ok(element)
}

/// Reads `n` elements.
pub fn read_elements<W: GroupWire>(
    reader: &mut NargReader<'_>,
    n: usize,
) -> Result<Vec<Element>, VerificationError> {
    (0..n).map(|_| read_element::<W>(reader)).collect()
}

/// Reads one canonical scalar.
pub fn read_scalar<W: GroupWire>(reader: &mut NargReader<'_>) -> Result<Scalar, VerificationError> {
    let bytes: [u8; SCALAR_LEN] = reader.take_array().map_err(|_: SpongeError| VerificationError)?;
    if W::scalar_is_canonical(&bytes) {
        Ok(bytes)
    } else {
        Err(VerificationError)
    }
}

/// Reads `n` canonical scalars.
pub fn read_scalars<W: GroupWire>(
    reader: &mut NargReader<'_>,
    n: usize,
) -> Result<Vec<Scalar>, VerificationError> {
    (0..n).map(|_| read_scalar::<W>(reader)).collect()
}

fn push_scalar(out: &mut Vec<u8>, scalar: &Scalar) {
    out.extend_from_slice(scalar);
}

/// `SerializeLinearRelation` in `format`; `None` if the instance has no
/// encoding in it (a statement element is the identity, or, under
/// [`InstanceFormat::ImplicitIdentity`], an element index is `2^32 - 1`).
/// Neither occurs for a validated instance that fits in memory.
///
/// For Ristretto255 under [`InstanceFormat::Draft03`] this is the core's
/// [`Instance::serialize`].
pub fn serialize_instance<W: GroupWire>(instance: &Instance, format: InstanceFormat) -> Option<Vec<u8>> {
    let mut out = push_u32_le(Vec::new(), instance.equations.len() as u32);
    for equation in &instance.equations {
        out = push_u32_le(out, equation.image.len() as u32);
        for (element_index, coeff) in &equation.image {
            out = push_u32_le(out, wire_index(format, *element_index)?);
            push_scalar(&mut out, coeff);
        }
        out = push_u32_le(out, equation.terms.len() as u32);
        for (scalar_index, element_index, coeff) in &equation.terms {
            out = push_u32_le(out, *scalar_index);
            out = push_u32_le(out, wire_index(format, *element_index)?);
            push_scalar(&mut out, coeff);
        }
    }
    out.extend_from_slice(&serialize_elements::<W>(&instance.statement_elements())?);
    Some(out)
}

fn invalid() -> InvalidInstance {
    InvalidInstance { check: None }
}

fn read_u32(reader: &mut NargReader<'_>) -> Result<u32, InvalidInstance> {
    let bytes: [u8; 4] = reader.take_array().map_err(|_| invalid())?;
    Ok(u32::from_le_bytes(bytes))
}

fn read_coefficient<W: GroupWire>(reader: &mut NargReader<'_>) -> Result<Scalar, InvalidInstance> {
    read_scalar::<W>(reader).map_err(|_| invalid())
}

/// The inverse of [`serialize_instance`], then the core's
/// [`Instance::new`] (its `ValidateInstance` and the image).
///
/// As upstream's `Instance::deserialize`: the statement elements are those
/// up to the largest referenced index, and a short element section, an
/// invalid element or scalar encoding (the identity's included), or trailing
/// bytes fail. Under [`InstanceFormat::ImplicitIdentity`] the element indices
/// are mapped to the core's by [`core_equations`].
pub fn deserialize_instance<W: GroupWire>(
    bytes: &[u8],
    format: InstanceFormat,
) -> Result<Instance, InvalidInstance> {
    let mut reader = NargReader::new(bytes);
    let num_equations = read_u32(&mut reader)?;
    let mut equations = Vec::new();
    // The largest wire index referenced, at least the generator's.
    let mut max_index: u32 = format.offset();
    for _ in 0..num_equations {
        let num_image = read_u32(&mut reader)?;
        let mut image = Vec::new();
        for _ in 0..num_image {
            let element_index = read_u32(&mut reader)?;
            let coeff = read_coefficient::<W>(&mut reader)?;
            max_index = max_index.max(element_index);
            image.push((element_index, coeff));
        }
        let num_terms = read_u32(&mut reader)?;
        let mut terms = Vec::new();
        for _ in 0..num_terms {
            let scalar_index = read_u32(&mut reader)?;
            let element_index = read_u32(&mut reader)?;
            let coeff = read_coefficient::<W>(&mut reader)?;
            max_index = max_index.max(element_index);
            terms.push((scalar_index, element_index, coeff));
        }
        equations.push(Equation { image, terms });
    }
    let mut elements = Vec::new();
    for _ in format.offset()..max_index {
        elements.push(read_element::<W>(&mut reader).map_err(|_| invalid())?);
    }
    if !reader.is_empty() {
        return Err(invalid());
    }
    Instance::new::<W>(elements, core_equations(format, &equations)?)
}

/// A validated instance of the group `W` with its encoding in `format`, the
/// statement of the Fiat-Shamir layer over `W`.
#[derive(Clone, Debug)]
pub struct WireInstance<W> {
    instance: Instance,
    format: InstanceFormat,
    encoded: Vec<u8>,
    group: PhantomData<W>,
}

impl<W: GroupWire> WireInstance<W> {
    /// The instance with its encoding; [`InvalidInstance`] if it has none in
    /// `format`.
    pub fn new(instance: Instance, format: InstanceFormat) -> Result<Self, InvalidInstance> {
        let encoded = serialize_instance::<W>(&instance, format).ok_or_else(invalid)?;
        Ok(WireInstance {
            instance,
            format,
            encoded,
            group: PhantomData,
        })
    }

    /// The instance of an encoding ([`deserialize_instance`]).
    pub fn deserialize(bytes: &[u8], format: InstanceFormat) -> Result<Self, InvalidInstance> {
        Self::new(deserialize_instance::<W>(bytes, format)?, format)
    }

    /// The core instance.
    pub fn instance(&self) -> &Instance {
        &self.instance
    }

    /// The instance encoding, absorbed first by the Fiat-Shamir layer.
    pub fn encoded(&self) -> &[u8] {
        &self.encoded
    }

    /// The instance encoding and element codec.
    pub fn format(&self) -> InstanceFormat {
        self.format
    }
}
