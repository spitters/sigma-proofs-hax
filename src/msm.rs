//! The value of the multi-scalar multiplications of [`SigmaGroup`].
//!
//! The core evaluates every linear combination by one call of
//! [`SigmaGroup::msm`] or [`SigmaGroup::msm_vartime`], as upstream does by
//! Straus' method in a constant-time and a variable-time form. This module
//! keeps their value, the sum `Σ scalars[i] * bases[i]` term by term in
//! [`SigmaGroup::group_mul`] and [`SigmaGroup::group_add`]: an implementor
//! without an MSM of its own may return [`msm_reference`] from both, and it
//! is the specification against which an implementation is checked.

use crate::group::SigmaGroup;
use crate::types::{Element, Scalar};

/// `Σ scalars[i] * bases[i]` over the first `scalars.len()` terms, term by
/// term; `bases` has at least as many entries. Its running time depends on
/// the scalars through [`SigmaGroup::group_mul`] only.
pub fn msm_reference<C: SigmaGroup>(scalars: &[Scalar], bases: &[Element]) -> Element {
    let mut acc = C::identity();
    for i in 0..scalars.len() {
        let term = C::group_mul(&scalars[i], &bases[i]);
        acc = C::group_add(&acc, &term);
    }
    acc
}
