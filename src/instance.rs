//! The validated instance: construction through the specification's
//! `ValidateInstance` (draft-irtf-cfrg-sigma-protocols-03, Section 3.5), the
//! image, and the linear map.

use crate::group::SigmaGroup;
use crate::types::{Element, Equation, Instance, InvalidInstance, Scalar, U32_MAX};

/// The left-hand side of `equation`: `Σ coeff * elements[e]` over its image
/// terms, one variable-time MSM ([`SigmaGroup::msm_vartime`]; the
/// coefficients are public). Every element index of the image terms is below
/// `elements.len()`.
pub fn image_entry<C: SigmaGroup>(elements: &[Element], equation: &Equation) -> Element {
    let mut scalars = Vec::new();
    let mut bases = Vec::new();
    for k in 0..equation.image.len() {
        let (element_index, coeff) = equation.image[k];
        scalars.push(coeff);
        bases.push(elements[element_index as usize]);
    }
    C::msm_vartime(&scalars, &bases)
}

/// The entry of the linear map's matrix in the row of `equation` and the
/// column `scalar_index`: `Σ coeff * elements[e]` over the terms
/// `(scalar_index, e, coeff)` of `equation`, one variable-time MSM
/// ([`SigmaGroup::msm_vartime`]; the coefficients are public). Every element
/// index of the terms is below `elements.len()`.
pub fn column_entry<C: SigmaGroup>(
    elements: &[Element],
    equation: &Equation,
    scalar_index: u32,
) -> Element {
    let mut scalars = Vec::new();
    let mut bases = Vec::new();
    for k in 0..equation.terms.len() {
        let (term_scalar, element_index, coeff) = equation.terms[k];
        if term_scalar == scalar_index {
            scalars.push(coeff);
            bases.push(elements[element_index as usize]);
        }
    }
    C::msm_vartime(&scalars, &bases)
}

/// The specification's `ValidateInstance` over the element vector
/// `elements` (the generator at index 0) and `equations`. Returns the
/// witness length `num_scalars = 1 + max(scalar_index)`.
///
/// The ten checks run in their order in the specification, each only when
/// the previous ones pass, and the first failure is reported
/// ([`InvalidInstance`]). Check 3 is on the counts: the indices are `u32`.
/// Check 6 fails without allocating when `num_scalars` exceeds the number of
/// terms, which bounds the number of distinct scalar indices.
pub fn validate<C: SigmaGroup>(
    elements: &[Element],
    equations: &[Equation],
) -> Result<usize, InvalidInstance> {
    let num_elements = elements.len();
    let mut failed: u8 = 0;
    // Check 1: at least one equation.
    if equations.len() == 0 {
        failed = 1;
    }
    // Check 2: non-empty image and terms.
    if failed == 0 {
        for j in 0..equations.len() {
            if equations[j].image.len() == 0 || equations[j].terms.len() == 0 {
                failed = 2;
            }
        }
    }
    // Check 3: the counts are below 2^32.
    if failed == 0 {
        if equations.len() as u64 > U32_MAX {
            failed = 3;
        }
        for j in 0..equations.len() {
            if equations[j].image.len() as u64 > U32_MAX
                || equations[j].terms.len() as u64 > U32_MAX
            {
                failed = 3;
            }
        }
    }
    // Check 4: the element indices are in range; the used elements, the
    // largest scalar index and the number of terms are collected.
    let mut element_used = vec![false; num_elements];
    let mut max_scalar: u32 = 0;
    let mut num_terms: usize = 0;
    if failed == 0 {
        for j in 0..equations.len() {
            let equation = &equations[j];
            for k in 0..equation.image.len() {
                let (element_index, _coeff) = equation.image[k];
                if element_index as usize >= num_elements {
                    failed = 4;
                } else {
                    element_used[element_index as usize] = true;
                }
            }
            for k in 0..equation.terms.len() {
                let (scalar_index, element_index, _coeff) = equation.terms[k];
                if element_index as usize >= num_elements {
                    failed = 4;
                } else {
                    element_used[element_index as usize] = true;
                }
                if scalar_index > max_scalar {
                    max_scalar = scalar_index;
                }
                num_terms = num_terms + 1;
            }
        }
    }
    // Check 5: every element other than the generator is used.
    if failed == 0 {
        for i in 1..num_elements {
            if !element_used[i] {
                failed = 5;
            }
        }
    }
    // Check 6: every scalar index below num_scalars is used.
    if failed == 0 {
        if max_scalar as usize >= num_terms {
            failed = 6;
        } else {
            let mut scalar_used = vec![false; max_scalar as usize + 1];
            for j in 0..equations.len() {
                let equation = &equations[j];
                for k in 0..equation.terms.len() {
                    let (scalar_index, _element_index, _coeff) = equation.terms[k];
                    scalar_used[scalar_index as usize] = true;
                }
            }
            for s in 0..max_scalar as usize + 1 {
                if !scalar_used[s] {
                    failed = 6;
                }
            }
        }
    }
    // Check 7: element 0 is the generator.
    if failed == 0 {
        if num_elements == 0 {
            failed = 7;
        } else {
            if !C::group_eq(&elements[0], &C::generator()) {
                failed = 7;
            }
        }
    }
    // Check 8: no element is the identity.
    if failed == 0 {
        for i in 0..num_elements {
            if C::group_eq(&elements[i], &C::identity()) {
                failed = 8;
            }
        }
    }
    // Check 9: no image entry is the identity.
    if failed == 0 {
        for j in 0..equations.len() {
            let value = image_entry::<C>(elements, &equations[j]);
            if C::group_eq(&value, &C::identity()) {
                failed = 9;
            }
        }
    }
    // Check 10: no column of the linear map is the identity.
    if failed == 0 {
        for s in 0..max_scalar as usize + 1 {
            let mut nonzero = false;
            for j in 0..equations.len() {
                let entry = column_entry::<C>(elements, &equations[j], s as u32);
                if !C::group_eq(&entry, &C::identity()) {
                    nonzero = true;
                }
            }
            if !nonzero {
                failed = 10;
            }
        }
    }
    if failed != 0 {
        Err(InvalidInstance {
            check: Some(failed),
        })
    } else {
        Ok(max_scalar as usize + 1)
    }
}

/// `image(instance)`: the left-hand side of each equation
/// ([`image_entry`]).
pub fn compute_image<C: SigmaGroup>(elements: &[Element], equations: &[Equation]) -> Vec<Element> {
    let mut image = Vec::new();
    for j in 0..equations.len() {
        image.push(image_entry::<C>(elements, &equations[j]));
    }
    image
}

impl Instance {
    /// Builds an instance from the statement's elements (indices from 1; the
    /// generator is element 0) and its equations, running `ValidateInstance`,
    /// then computing the image.
    pub fn new<C: SigmaGroup>(
        elements: Vec<Element>,
        equations: Vec<Equation>,
    ) -> Result<Instance, InvalidInstance> {
        let mut all_elements = Vec::new();
        all_elements.push(C::generator());
        for i in 0..elements.len() {
            all_elements.push(elements[i]);
        }
        let num_scalars = validate::<C>(&all_elements, &equations)?;
        let image = compute_image::<C>(&all_elements, &equations);
        Ok(Instance {
            elements: all_elements,
            equations,
            image,
            num_scalars,
        })
    }

    /// The statement's elements, without the generator.
    pub fn statement_elements(&self) -> Vec<Element> {
        let mut out = Vec::new();
        for i in 1..self.elements.len() {
            out.push(self.elements[i]);
        }
        out
    }

    /// `num_elements(instance)`, the generator included.
    pub fn num_elements(&self) -> usize {
        self.elements.len()
    }

    /// `num_equations(instance)`.
    pub fn num_equations(&self) -> usize {
        self.equations.len()
    }

    /// `num_scalars(instance)`: `1 + max(scalar_index)` over the terms.
    pub fn num_scalars(&self) -> usize {
        self.num_scalars
    }

    /// The MSM terms of row `j` of the linear map at `scalars`: the scalars
    /// `coeff * scalars[s]` and the bases `elements[e]`, one pair per term
    /// `(s, e, coeff)` of equation `j`, in the order of the terms. `scalars`
    /// has at least `num_scalars()` entries.
    pub fn evaluation_pairs<C: SigmaGroup>(
        &self,
        j: usize,
        scalars: &[Scalar],
    ) -> (Vec<Scalar>, Vec<Element>) {
        let equation = &self.equations[j];
        let mut values = Vec::new();
        let mut bases = Vec::new();
        for k in 0..equation.terms.len() {
            let (scalar_index, element_index, coeff) = equation.terms[k];
            values.push(C::scalar_mul(&coeff, &scalars[scalar_index as usize]));
            bases.push(self.elements[element_index as usize]);
        }
        (values, bases)
    }

    /// Row `j` of the linear map at `scalars`:
    /// `Σ coeff * scalars[s] * elements[e]` over the terms of equation `j`,
    /// one constant-time MSM ([`SigmaGroup::msm`]) over
    /// [`Instance::evaluation_pairs`]: the scalars may be secret. `scalars`
    /// has at least `num_scalars()` entries.
    pub fn map_row<C: SigmaGroup>(&self, j: usize, scalars: &[Scalar]) -> Element {
        let (values, bases) = self.evaluation_pairs::<C>(j, scalars);
        C::msm(&values, &bases)
    }

    /// `map(instance, scalars)`: the linear map at `scalars`, one element per
    /// equation, each in constant time ([`Instance::map_row`]). `scalars` has
    /// at least `num_scalars()` entries.
    pub fn map<C: SigmaGroup>(&self, scalars: &[Scalar]) -> Vec<Element> {
        let mut out = Vec::new();
        for j in 0..self.equations.len() {
            out.push(self.map_row::<C>(j, scalars));
        }
        out
    }

    /// Whether `witness` satisfies every equation: `map(witness) = image`.
    /// `witness` has at least `num_scalars()` entries.
    pub fn is_witness_valid<C: SigmaGroup>(&self, witness: &[Scalar]) -> bool {
        let mapped = self.map::<C>(witness);
        let mut valid = true;
        for j in 0..self.image.len() {
            if !C::group_eq(&self.image[j], &mapped[j]) {
                valid = false;
            }
        }
        valid
    }
}
