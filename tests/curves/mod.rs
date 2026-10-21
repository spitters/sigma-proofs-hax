//! The P-256 and BLS12-381 G1 instances of [`SigmaGroup`] and [`GroupWire`],
//! for the test-vector suite.
//!
//! The core holds an element in 32 bytes ([`Element`]), shorter than the
//! encodings of these groups (33 and 48 bytes). An element here is a handle:
//! the index of the point in a per-group table, in which every point is
//! entered once, keyed by its canonical encoding. Equal points therefore have
//! equal handles. The table lives as long as the test process; handles never
//! reach a transcript, which carries the wire encodings ([`GroupWire`]).
//!
//! Scalars are the core's 32-byte big-endian encodings, the wire encoding of
//! both ciphersuites. The codecs are those of upstream `sigma-proofs` 0.4.1
//! (`codec.rs`): SEC1 compressed points with the tags `00`, `02`, `03` only
//! (the identity is 33 zero bytes), compressed G1 points with the subgroup
//! check, big-endian scalars below the order, and `DecodeField` as
//! `LE2IP(bytes) mod p`.

use std::collections::HashMap;
use std::marker::PhantomData;
use std::sync::{Mutex, OnceLock};

use ff::{Field, PrimeField};
use group::{Group, GroupEncoding};

use sigma_proofs_hax::wire::GroupWire;
use sigma_proofs_hax::{Element, Scalar, SigmaGroup};

/// The points of one group, each once, by canonical encoding.
pub struct Table<P> {
    points: Vec<P>,
    ids: HashMap<Vec<u8>, u64>,
}

impl<P> Table<P> {
    fn new() -> Self {
        Table {
            points: Vec::new(),
            ids: HashMap::new(),
        }
    }
}

/// A prime-order group with its codecs.
pub trait Curve: 'static {
    type Point: Group<Scalar = Self::Field>;
    type Field: PrimeField;
    /// `Ne`.
    const ELEMENT_LEN: usize;
    fn table() -> &'static Mutex<Table<Self::Point>>;
    /// The canonical encoding, the identity's included.
    fn encode(point: &Self::Point) -> Vec<u8>;
    /// The point of a canonical encoding of `ELEMENT_LEN` bytes.
    fn decode(bytes: &[u8]) -> Option<Self::Point>;
}

fn handle(id: u64) -> Element {
    let mut out = [0u8; 32];
    out[..8].copy_from_slice(&id.to_le_bytes());
    out
}

fn intern<C: Curve>(point: C::Point) -> Element {
    let key = C::encode(&point);
    let mut table = C::table().lock().unwrap();
    if let Some(id) = table.ids.get(&key) {
        return handle(*id);
    }
    let id = table.points.len() as u64;
    table.points.push(point);
    table.ids.insert(key, id);
    handle(id)
}

fn point<C: Curve>(element: &Element) -> C::Point {
    let mut id = [0u8; 8];
    id.copy_from_slice(&element[..8]);
    let table = C::table().lock().unwrap();
    table.points[u64::from_le_bytes(id) as usize]
}

/// Whether the field's representation is little-endian (upstream
/// `repr_is_le`).
fn repr_is_le<F: PrimeField>() -> bool {
    F::ONE.to_repr().as_ref()[0] == 1
}

fn scalar_to_be<F: PrimeField>(value: &F) -> Scalar {
    let repr = value.to_repr();
    let mut out = [0u8; 32];
    out.copy_from_slice(repr.as_ref());
    if repr_is_le::<F>() {
        out.reverse();
    }
    out
}

fn scalar_from_be<F: PrimeField>(bytes: &Scalar) -> Option<F> {
    let mut repr = F::Repr::default();
    AsMut::<[u8]>::as_mut(&mut repr).copy_from_slice(bytes);
    if repr_is_le::<F>() {
        AsMut::<[u8]>::as_mut(&mut repr).reverse();
    }
    Option::from(F::from_repr(repr))
}

fn field<F: PrimeField>(bytes: &Scalar) -> F {
    scalar_from_be(bytes).expect("canonical scalar encoding")
}

/// `LE2IP(bytes) mod p` over 8-byte limbs (upstream `wide_reduce`).
fn wide_reduce<F: PrimeField>(bytes: &[u8]) -> F {
    assert_eq!(bytes.len() % 8, 0);
    let shift = F::from(u64::MAX) + F::ONE;
    let mut acc = F::ZERO;
    for chunk in bytes.rchunks(8) {
        let limb = chunk.iter().rev().fold(0u64, |w, &b| (w << 8) | u64::from(b));
        acc = acc * shift + F::from(limb);
    }
    acc
}

/// The group of a [`Curve`], over handles.
pub struct Interned<C>(PhantomData<C>);

impl<C> Clone for Interned<C> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<C> Copy for Interned<C> {}

impl<C: Curve> SigmaGroup for Interned<C> {
    fn scalar_zero() -> Scalar {
        scalar_to_be(&C::Field::ZERO)
    }
    fn scalar_one() -> Scalar {
        scalar_to_be(&C::Field::ONE)
    }
    fn scalar_add(a: &Scalar, b: &Scalar) -> Scalar {
        scalar_to_be(&(field::<C::Field>(a) + field::<C::Field>(b)))
    }
    fn scalar_sub(a: &Scalar, b: &Scalar) -> Scalar {
        scalar_to_be(&(field::<C::Field>(a) - field::<C::Field>(b)))
    }
    fn scalar_mul(a: &Scalar, b: &Scalar) -> Scalar {
        scalar_to_be(&(field::<C::Field>(a) * field::<C::Field>(b)))
    }
    fn scalar_neg(a: &Scalar) -> Scalar {
        scalar_to_be(&(-field::<C::Field>(a)))
    }
    fn scalar_eq(a: &Scalar, b: &Scalar) -> bool {
        field::<C::Field>(a) == field::<C::Field>(b)
    }
    fn identity() -> Element {
        intern::<C>(C::Point::identity())
    }
    fn generator() -> Element {
        intern::<C>(C::Point::generator())
    }
    fn group_add(a: &Element, b: &Element) -> Element {
        intern::<C>(point::<C>(a) + point::<C>(b))
    }
    fn group_mul(s: &Scalar, p: &Element) -> Element {
        intern::<C>(point::<C>(p) * field::<C::Field>(s))
    }
    fn group_eq(a: &Element, b: &Element) -> bool {
        point::<C>(a) == point::<C>(b)
    }
    fn msm(scalars: &[Scalar], bases: &[Element]) -> Element {
        sigma_proofs_hax::msm::msm_reference::<Self>(scalars, bases)
    }
    fn msm_vartime(scalars: &[Scalar], bases: &[Element]) -> Element {
        sigma_proofs_hax::msm::msm_reference::<Self>(scalars, bases)
    }
}

impl<C: Curve> GroupWire for Interned<C> {
    const ELEMENT_LEN: usize = C::ELEMENT_LEN;
    fn element_to_wire(element: &Element) -> Vec<u8> {
        C::encode(&point::<C>(element))
    }
    fn element_from_wire(bytes: &[u8]) -> Option<Element> {
        C::decode(bytes).map(intern::<C>)
    }
    fn scalar_is_canonical(scalar: &Scalar) -> bool {
        scalar_from_be::<C::Field>(scalar).is_some()
    }
    fn scalar_from_uniform_bytes(bytes: &[u8]) -> Scalar {
        scalar_to_be(&wide_reduce::<C::Field>(bytes))
    }
}

/// P-256 (secp256r1).
pub struct P256Curve;

impl Curve for P256Curve {
    type Point = p256::ProjectivePoint;
    type Field = p256::Scalar;
    const ELEMENT_LEN: usize = 33;
    fn table() -> &'static Mutex<Table<Self::Point>> {
        static TABLE: OnceLock<Mutex<Table<p256::ProjectivePoint>>> = OnceLock::new();
        TABLE.get_or_init(|| Mutex::new(Table::new()))
    }
    fn encode(point: &Self::Point) -> Vec<u8> {
        AsRef::<[u8]>::as_ref(&point.to_bytes()).to_vec()
    }
    fn decode(bytes: &[u8]) -> Option<Self::Point> {
        if bytes.len() != Self::ELEMENT_LEN || !matches!(bytes[0], 0x00 | 0x02 | 0x03) {
            return None;
        }
        let mut repr = <Self::Point as GroupEncoding>::Repr::default();
        AsMut::<[u8]>::as_mut(&mut repr).copy_from_slice(bytes);
        Option::from(Self::Point::from_bytes(&repr))
    }
}

/// BLS12-381 G1.
pub struct Bls12381Curve;

impl Curve for Bls12381Curve {
    type Point = bls12_381::G1Projective;
    type Field = bls12_381::Scalar;
    const ELEMENT_LEN: usize = 48;
    fn table() -> &'static Mutex<Table<Self::Point>> {
        static TABLE: OnceLock<Mutex<Table<bls12_381::G1Projective>>> = OnceLock::new();
        TABLE.get_or_init(|| Mutex::new(Table::new()))
    }
    fn encode(point: &Self::Point) -> Vec<u8> {
        AsRef::<[u8]>::as_ref(&point.to_bytes()).to_vec()
    }
    fn decode(bytes: &[u8]) -> Option<Self::Point> {
        if bytes.len() != Self::ELEMENT_LEN {
            return None;
        }
        let mut repr = <Self::Point as GroupEncoding>::Repr::default();
        AsMut::<[u8]>::as_mut(&mut repr).copy_from_slice(bytes);
        Option::from(Self::Point::from_bytes(&repr))
    }
}

/// The P-256 group of the ciphersuite `sigma-proofs_Shake128_P256`.
pub type P256 = Interned<P256Curve>;

/// The BLS12-381 G1 group of the ciphersuite
/// `sigma-proofs_Shake128_BLS12381`.
pub type Bls12381 = Interned<Bls12381Curve>;
