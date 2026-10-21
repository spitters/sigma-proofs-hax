//! Linear maps and relations: allocation of variables, equations, the image
//! from a witness, and compilation into a validated [`Instance`].
//!
//! Upstream mutates the relation through `&mut self`; here every builder
//! takes the relation by value and returns the updated relation (with the
//! allocated variable, or the result of a fallible step).

use crate::group::SigmaGroup;
use crate::types::{
    Element, Equation, GroupMap, GroupVar, Instance, InvalidInstance, LinearCombination, LinearMap,
    LinearRelation, Scalar, ScalarTerm, ScalarVar, U32_MAX,
};

/// The value of a term's scalar at `scalars`: the variable's entry, or one.
pub fn scalar_value<C: SigmaGroup>(scalar: ScalarTerm, scalars: &[Scalar]) -> Scalar {
    match scalar {
        ScalarTerm::Var(var) => scalars[var.index],
        ScalarTerm::Unit => C::scalar_one(),
    }
}

impl GroupMap {
    /// The empty assignment.
    pub fn empty() -> GroupMap {
        GroupMap(Vec::new())
    }

    /// The element assigned to `var`, if any.
    pub fn lookup(&self, var: GroupVar) -> Option<Element> {
        if var.index < self.0.len() {
            self.0[var.index]
        } else {
            None
        }
    }

    /// The element assigned to `var`, or [`InvalidInstance`] if it has none.
    pub fn get(&self, var: GroupVar) -> Result<Element, InvalidInstance> {
        match self.lookup(var) {
            Some(element) => Ok(element),
            None => Err(InvalidInstance { check: None }),
        }
    }

    /// Assigns `element` to `var`, growing the map, replacing any previous
    /// assignment.
    pub fn assign_element_unchecked(self, var: GroupVar, element: Element) -> GroupMap {
        let mut slots = self.0;
        while slots.len() <= var.index {
            slots.push(None);
        }
        slots[var.index] = Some(element);
        GroupMap(slots)
    }

    /// Assigns `element` to `var`. An assignment that conflicts with an
    /// existing one is [`InvalidInstance`] (upstream panics).
    pub fn assign_element<C: SigmaGroup>(
        self,
        var: GroupVar,
        element: Element,
    ) -> Result<GroupMap, InvalidInstance> {
        let conflict = match self.lookup(var) {
            Some(assigned) => !C::group_eq(&assigned, &element),
            None => false,
        };
        if conflict {
            Err(InvalidInstance { check: None })
        } else {
            Ok(self.assign_element_unchecked(var, element))
        }
    }
}

impl LinearMap {
    /// The empty linear map.
    pub fn new() -> LinearMap {
        LinearMap {
            linear_combinations: Vec::new(),
            group_elements: GroupMap::empty(),
            num_scalars: 0,
            num_elements: 0,
        }
    }

    /// The number of equations.
    pub fn num_constraints(&self) -> usize {
        self.linear_combinations.len()
    }

    /// Evaluates every linear combination at `scalars`, one value per
    /// allocated scalar variable; a different length, or a term over an
    /// unassigned element, is [`InvalidInstance`]. Each combination is one
    /// constant-time MSM ([`SigmaGroup::msm`]) over its terms with an
    /// assigned element: `scalars` may be the witness.
    pub fn evaluate<C: SigmaGroup>(
        &self,
        scalars: &[Scalar],
    ) -> Result<Vec<Element>, InvalidInstance> {
        if scalars.len() != self.num_scalars {
            return Err(InvalidInstance { check: None });
        }
        let mut complete = true;
        let mut out = Vec::new();
        for j in 0..self.linear_combinations.len() {
            let combination = &self.linear_combinations[j];
            let mut coefficients = Vec::new();
            let mut bases = Vec::new();
            for k in 0..combination.terms.len() {
                let weighted = combination.terms[k];
                let value = scalar_value::<C>(weighted.term.scalar, scalars);
                let coefficient = C::scalar_mul(&value, &weighted.weight);
                match self.group_elements.lookup(weighted.term.elem) {
                    Some(element) => {
                        coefficients.push(coefficient);
                        bases.push(element);
                    }
                    None => {
                        complete = false;
                    }
                }
            }
            out.push(C::msm(&coefficients, &bases));
        }
        if complete {
            Ok(out)
        } else {
            Err(InvalidInstance { check: None })
        }
    }
}

impl Default for LinearMap {
    fn default() -> Self {
        Self::new()
    }
}

impl LinearRelation {
    /// The empty relation, with the generator assigned to the element
    /// variable 0 (draft-irtf-cfrg-sigma-protocols-03, Section 3.2: the
    /// generator is element 0 of every instance, and there is no identity
    /// element).
    pub fn new<C: SigmaGroup>() -> LinearRelation {
        let mut slots = Vec::new();
        slots.push(Some(C::generator()));
        LinearRelation {
            linear_map: LinearMap {
                linear_combinations: Vec::new(),
                group_elements: GroupMap(slots),
                num_scalars: 0,
                num_elements: 1,
            },
            image: Vec::new(),
        }
    }

    /// The variable of the generator, element index 0.
    pub fn generator(&self) -> GroupVar {
        GroupVar { index: 0 }
    }

    /// Allocates a scalar variable.
    pub fn allocate_scalar(self) -> (LinearRelation, ScalarVar) {
        let index = self.linear_map.num_scalars;
        let linear_map = LinearMap {
            linear_combinations: self.linear_map.linear_combinations,
            group_elements: self.linear_map.group_elements,
            num_scalars: index + 1,
            num_elements: self.linear_map.num_elements,
        };
        (
            LinearRelation {
                linear_map,
                image: self.image,
            },
            ScalarVar { index },
        )
    }

    /// Allocates `n` scalar variables.
    pub fn allocate_scalars_vec(self, n: usize) -> (LinearRelation, Vec<ScalarVar>) {
        let mut relation = self;
        let mut vars = Vec::new();
        for _i in 0..n {
            let (next, var) = relation.allocate_scalar();
            relation = next;
            vars.push(var);
        }
        (relation, vars)
    }

    /// Allocates a group-element variable, unassigned.
    pub fn allocate_element(self) -> (LinearRelation, GroupVar) {
        let index = self.linear_map.num_elements;
        let linear_map = LinearMap {
            linear_combinations: self.linear_map.linear_combinations,
            group_elements: self.linear_map.group_elements,
            num_scalars: self.linear_map.num_scalars,
            num_elements: index + 1,
        };
        (
            LinearRelation {
                linear_map,
                image: self.image,
            },
            GroupVar { index },
        )
    }

    /// Allocates `n` group-element variables, unassigned.
    pub fn allocate_elements_vec(self, n: usize) -> (LinearRelation, Vec<GroupVar>) {
        let mut relation = self;
        let mut vars = Vec::new();
        for _i in 0..n {
            let (next, var) = relation.allocate_element();
            relation = next;
            vars.push(var);
        }
        (relation, vars)
    }

    /// Allocates a group-element variable assigned to `element`.
    pub fn allocate_element_with(self, element: Element) -> (LinearRelation, GroupVar) {
        let (relation, var) = self.allocate_element();
        let linear_map = LinearMap {
            linear_combinations: relation.linear_map.linear_combinations,
            group_elements: relation
                .linear_map
                .group_elements
                .assign_element_unchecked(var, element),
            num_scalars: relation.linear_map.num_scalars,
            num_elements: relation.linear_map.num_elements,
        };
        (
            LinearRelation {
                linear_map,
                image: relation.image,
            },
            var,
        )
    }

    /// Assigns `element` to `var`; a conflicting assignment is
    /// [`InvalidInstance`] (upstream panics).
    pub fn set_element<C: SigmaGroup>(
        self,
        var: GroupVar,
        element: Element,
    ) -> Result<LinearRelation, InvalidInstance> {
        let group_elements = self
            .linear_map
            .group_elements
            .assign_element::<C>(var, element)?;
        let linear_map = LinearMap {
            linear_combinations: self.linear_map.linear_combinations,
            group_elements,
            num_scalars: self.linear_map.num_scalars,
            num_elements: self.linear_map.num_elements,
        };
        Ok(LinearRelation {
            linear_map,
            image: self.image,
        })
    }

    /// Adds the equation `lhs = rhs`.
    pub fn append_equation(self, lhs: GroupVar, rhs: LinearCombination) -> LinearRelation {
        let mut linear_combinations = self.linear_map.linear_combinations;
        linear_combinations.push(rhs);
        let mut image = self.image;
        image.push(lhs);
        LinearRelation {
            linear_map: LinearMap {
                linear_combinations,
                group_elements: self.linear_map.group_elements,
                num_scalars: self.linear_map.num_scalars,
                num_elements: self.linear_map.num_elements,
            },
            image,
        }
    }

    /// Allocates an unassigned image variable `lhs` and adds `lhs = rhs`.
    pub fn allocate_eq(self, rhs: LinearCombination) -> (LinearRelation, GroupVar) {
        let (relation, var) = self.allocate_element();
        (relation.append_equation(var, rhs), var)
    }

    /// Allocates an image variable assigned to `lhs` and adds `lhs = rhs`.
    pub fn allocate_eq_with(
        self,
        lhs: Element,
        rhs: LinearCombination,
    ) -> (LinearRelation, GroupVar) {
        let (relation, var) = self.allocate_element_with(lhs);
        (relation.append_equation(var, rhs), var)
    }

    /// Evaluates the linear map at `scalars` and assigns every unassigned
    /// image variable; an image variable already assigned is checked against
    /// the computed value. On any error the relation is returned unchanged.
    pub fn compute_image<C: SigmaGroup>(
        self,
        scalars: &[Scalar],
    ) -> (LinearRelation, Result<(), InvalidInstance>) {
        if self.linear_map.num_constraints() != self.image.len() {
            return (self, Err(InvalidInstance { check: None }));
        }
        match self.linear_map.evaluate::<C>(scalars) {
            Err(error) => (self, Err(error)),
            Ok(mapped) => {
                let mut staged = self.linear_map.group_elements.clone();
                let mut consistent = true;
                for j in 0..mapped.len() {
                    let lhs = self.image[j];
                    match staged.lookup(lhs) {
                        Some(assigned) => {
                            if !C::group_eq(&assigned, &mapped[j]) {
                                consistent = false;
                            }
                        }
                        None => {
                            staged = staged.assign_element_unchecked(lhs, mapped[j]);
                        }
                    }
                }
                if consistent {
                    let linear_map = LinearMap {
                        linear_combinations: self.linear_map.linear_combinations,
                        group_elements: staged,
                        num_scalars: self.linear_map.num_scalars,
                        num_elements: self.linear_map.num_elements,
                    };
                    (
                        LinearRelation {
                            linear_map,
                            image: self.image,
                        },
                        Ok(()),
                    )
                } else {
                    (self, Err(InvalidInstance { check: None }))
                }
            }
        }
    }

    /// Computes the image from `witness` ([`LinearRelation::compute_image`])
    /// and compiles the relation; the instance must take a witness of the
    /// length given.
    pub fn compile_with_witness<C: SigmaGroup>(
        self,
        witness: &[Scalar],
    ) -> (LinearRelation, Result<Instance, InvalidInstance>) {
        let (relation, computed) = self.compute_image::<C>(witness);
        match computed {
            Err(error) => (relation, Err(error)),
            Ok(()) => match relation.compile::<C>() {
                Err(error) => (relation, Err(error)),
                Ok(instance) => {
                    if instance.num_scalars != witness.len() {
                        (relation, Err(InvalidInstance { check: None }))
                    } else {
                        (relation, Ok(instance))
                    }
                }
            },
        }
    }

    /// Compiles the relation into a validated [`Instance`].
    ///
    /// Each equation `lhs = Σ weight * (scalar * elem)` becomes the image
    /// `[(lhs, 1)]` followed by `(elem, -weight)` for each constant term, and
    /// the terms `(scalar, elem, weight)` of the variable terms, in order.
    /// Elements no equation uses are dropped and the remaining indices
    /// renumbered in allocation order (the generator keeps 0). The result
    /// passes through [`Instance::new`].
    pub fn compile<C: SigmaGroup>(&self) -> Result<Instance, InvalidInstance> {
        if self.image.len() != self.linear_map.linear_combinations.len() {
            return Err(InvalidInstance { check: None });
        }
        let mut in_range = true;
        let mut max_index: usize = 0;
        let mut equations = Vec::new();
        for j in 0..self.image.len() {
            let lhs = self.image[j];
            if lhs.index as u64 > U32_MAX {
                in_range = false;
            }
            if lhs.index > max_index {
                max_index = lhs.index;
            }
            let mut image = Vec::new();
            image.push((lhs.index as u32, C::scalar_one()));
            let mut terms = Vec::new();
            let combination = &self.linear_map.linear_combinations[j];
            for k in 0..combination.terms.len() {
                let weighted = combination.terms[k];
                let element_index = weighted.term.elem.index;
                if element_index as u64 > U32_MAX {
                    in_range = false;
                }
                if element_index > max_index {
                    max_index = element_index;
                }
                match weighted.term.scalar {
                    ScalarTerm::Var(scalar_var) => {
                        if scalar_var.index as u64 > U32_MAX {
                            in_range = false;
                        }
                        terms.push((
                            scalar_var.index as u32,
                            element_index as u32,
                            weighted.weight,
                        ));
                    }
                    ScalarTerm::Unit => {
                        image.push((element_index as u32, C::scalar_neg(&weighted.weight)));
                    }
                }
            }
            equations.push(Equation { image, terms });
        }
        if !in_range {
            return Err(InvalidInstance { check: None });
        }

        // The used element indices, with the generator.
        let mut used = vec![false; max_index + 1];
        used[0] = true;
        for j in 0..equations.len() {
            let equation = &equations[j];
            for k in 0..equation.image.len() {
                let (element_index, _coeff) = equation.image[k];
                used[element_index as usize] = true;
            }
            for k in 0..equation.terms.len() {
                let (_scalar_index, element_index, _coeff) = equation.terms[k];
                used[element_index as usize] = true;
            }
        }
        // The new index of each used index, in allocation order.
        let mut remap = vec![0u32; max_index + 1];
        let mut count: u32 = 0;
        for i in 0..max_index + 1 {
            if used[i] {
                remap[i] = count;
                count = count + 1;
            }
        }
        let mut renumbered = Vec::new();
        for j in 0..equations.len() {
            let equation = &equations[j];
            let mut image = Vec::new();
            for k in 0..equation.image.len() {
                let (element_index, coeff) = equation.image[k];
                image.push((remap[element_index as usize], coeff));
            }
            let mut terms = Vec::new();
            for k in 0..equation.terms.len() {
                let (scalar_index, element_index, coeff) = equation.terms[k];
                terms.push((scalar_index, remap[element_index as usize], coeff));
            }
            renumbered.push(Equation { image, terms });
        }

        let mut assigned = true;
        let mut elements = Vec::new();
        for i in 1..max_index + 1 {
            if used[i] {
                match self.linear_map.group_elements.lookup(GroupVar { index: i }) {
                    Some(element) => elements.push(element),
                    None => {
                        assigned = false;
                    }
                }
            }
        }
        if !assigned {
            return Err(InvalidInstance { check: None });
        }
        Instance::new::<C>(elements, renumbered)
    }
}
