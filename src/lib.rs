//! A hax-extractable fork of the Σ-protocol core of `sigma-proofs` 0.4.1
//! (<https://github.com/sigma-rs/sigma-proofs>, MIT OR Apache-2.0), the
//! implementation of draft-irtf-cfrg-sigma-protocols.
//!
//! The names follow the upstream crate and the representation follows
//! draft-irtf-cfrg-sigma-protocols-03, Section 3: a [`LinearRelation`] is a
//! [`LinearMap`] (linear combinations over allocated scalar and group-element
//! variables) with its image variables, and compiles into a validated
//! [`Instance`], whose equations carry an image `(element index, coefficient)`
//! list and right-hand-side terms `(scalar index, element index,
//! coefficient)`. The generator is element 0 of every instance and there is
//! no identity element; [`instance::validate`] is the draft's
//! `ValidateInstance` with its ten checks, and the element codec
//! ([`codec::serialize_elements`]) fails on the identity. Upstream 0.4.1
//! places the identity and the generator at element indices 0 and 1 and runs
//! three of the checks; its instance encoding is the draft-03 one with every
//! element index shifted by one ([`wire::InstanceFormat`]).
//!
//! The extracted core (every module except [`ristretto`], [`wire`] and
//! [`fiat_shamir`])
//! is written in the subset of Rust that hax and hax-lean translate:
//!
//! - scalars and group elements are 32-byte encodings ([`Scalar`],
//!   [`Element`]), and every group and field operation is an associated
//!   function of the trait [`SigmaGroup`], so the extracted functions are
//!   parametric in an interpretation of the group;
//! - prover nonces and simulator randomness are function inputs;
//! - no `&mut`: a function that upstream mutates its receiver through returns
//!   the updated value instead;
//! - index loops, no iterator chains or closures.
//!
//! The Fiat-Shamir layer (the duplex sponge of `spongefish`) and the wire
//! codecs are outside the extracted core. [`fiat_shamir`] produces the
//! batchable and compact NARG strings over the Ristretto255 instance
//! [`ristretto`] in upstream's instance encoding, and over any group with a
//! wire codec ([`wire::GroupWire`]) in the instance encoding of
//! draft-irtf-cfrg-sigma-protocols-03 or of upstream 0.4.1
//! ([`wire::InstanceFormat`]); the three modules are compiled only outside
//! the hax view (`cfg(not(hax))`).

// The extracted subset: index loops, `x = x op y`, vectors built by `push`,
// `len() == 0`, nested conditionals.
#![allow(
    clippy::needless_range_loop,
    clippy::assign_op_pattern,
    clippy::vec_init_then_push,
    clippy::len_zero,
    clippy::collapsible_else_if
)]

pub mod codec;
pub mod composition;
pub mod fixed;
pub mod group;
pub mod instance;
pub mod msm;
pub mod protocol;
pub mod relation;
pub mod types;

#[cfg(not(hax))]
pub mod fiat_shamir;
#[cfg(not(hax))]
pub mod ristretto;
#[cfg(not(hax))]
pub mod wire;

pub use group::SigmaGroup;
pub use types::*;
