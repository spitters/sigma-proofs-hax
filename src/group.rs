//! The group and field operations the core calls and does not define.
//!
//! An implementor fixes a prime-order group with its scalar field and the
//! canonical encodings [`Scalar`] and [`Element`]. The functions are total:
//! their arguments are encodings the implementor produced, or that the
//! decoding layer checked.
//!
//! Every linear combination of the core is one call of
//! [`SigmaGroup::msm`] (secret scalars) or [`SigmaGroup::msm_vartime`]
//! (public scalars), both with the value of
//! [`crate::msm::msm_reference`], the sum term by term, except the rows of
//! the simulated commitment (the verifier of one equation, the compact
//! verifier and the simulator): those are one call of
//! [`SigmaGroup::msm_rows_vartime`] together, with the value of
//! [`crate::msm::msm_rows_reference`], one [`SigmaGroup::msm_vartime`] per
//! row.

use crate::types::{Element, Scalar};

/// A prime-order group and its scalar field, over canonical encodings.
pub trait SigmaGroup: Copy {
    /// The scalar `0`.
    fn scalar_zero() -> Scalar;
    /// The scalar `1`.
    fn scalar_one() -> Scalar;
    /// Field addition `a + b`.
    fn scalar_add(a: &Scalar, b: &Scalar) -> Scalar;
    /// Field subtraction `a - b`.
    fn scalar_sub(a: &Scalar, b: &Scalar) -> Scalar;
    /// Field multiplication `a * b`.
    fn scalar_mul(a: &Scalar, b: &Scalar) -> Scalar;
    /// Field negation `-a`.
    fn scalar_neg(a: &Scalar) -> Scalar;
    /// Field equality.
    fn scalar_eq(a: &Scalar, b: &Scalar) -> bool;
    /// The group identity.
    fn identity() -> Element;
    /// The group generator.
    fn generator() -> Element;
    /// The group law `a + b`.
    fn group_add(a: &Element, b: &Element) -> Element;
    /// The scalar action `s * p`.
    fn group_mul(s: &Scalar, p: &Element) -> Element;
    /// Group equality.
    fn group_eq(a: &Element, b: &Element) -> bool;
    /// Multi-scalar multiplication `Σ scalars[i] * bases[i]` over
    /// `i < scalars.len()`; `bases` has at least `scalars.len()` entries and
    /// the entries beyond are not read. The empty sum is the identity.
    ///
    /// Constant time in the scalars: running time and memory access pattern
    /// depend only on `scalars.len()` and on the bases. For secret scalars:
    /// the prover nonces and the witness.
    fn msm(scalars: &[Scalar], bases: &[Element]) -> Element;
    /// The value of [`SigmaGroup::msm`], in variable time: running time and
    /// memory access pattern may depend on the scalars. For public scalars
    /// only: the verifier of a batchable proof of several equations, and the
    /// evaluation of public
    /// coefficients in instance construction.
    fn msm_vartime(scalars: &[Scalar], bases: &[Element]) -> Element;
    /// [`SigmaGroup::msm_vartime`] of each row: the result has one entry per
    /// row, `msm_vartime(&rows[j].0, &rows[j].1)` at index `j`, and each row
    /// satisfies the length condition of [`SigmaGroup::msm`]. One call
    /// evaluates all rows of a linear map, so that an implementation decodes
    /// a base that several rows share once. Variable time, for public
    /// scalars only, as [`SigmaGroup::msm_vartime`]: the simulated
    /// commitment, whose scalars are the challenge and the response.
    fn msm_rows_vartime(rows: &[(Vec<Scalar>, Vec<Element>)]) -> Vec<Element>;
}
