//! The types of the Σ-protocol core: encodings, errors, linear-combination
//! expressions, linear maps and relations, validated instances, prover
//! state, and the AND-composition trees.

/// A scalar: the canonical big-endian encoding of a field element, the wire
/// encoding of the specification.
pub type Scalar = [u8; 32];

/// A group element: its canonical 32-byte encoding.
pub type Element = [u8; 32];

/// The bound of the specification's check 3: counts and indices are below
/// `2^32`.
pub const U32_MAX: u64 = 4294967295;

/// A statement that fails construction or validation. `check` is the number
/// of the first check of the specification's `ValidateInstance`
/// (draft-irtf-cfrg-sigma-protocols-03, Section 3.5) that failed, or `None`
/// for a failure outside those checks:
///
/// 1. at least one equation;
/// 2. every equation has a non-empty image and non-empty terms;
/// 3. counts and indices are below `2^32`;
/// 4. every element index is below `num_elements`;
/// 5. every element index other than 0 is used;
/// 6. every scalar index below `num_scalars` is used;
/// 7. element 0 is the generator;
/// 8. no element is the identity;
/// 9. no image entry is the identity;
/// 10. no column of the linear map is the identity.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct InvalidInstance {
    pub check: Option<u8>,
}

/// The witness does not have the shape the statement requires.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct InvalidWitness;

/// A transcript or proof that does not verify.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct VerificationError;

/// A reference to a scalar variable of a linear relation: its allocation
/// index.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ScalarVar {
    pub index: usize,
}

/// A reference to a group-element variable of a linear relation: its
/// allocation index.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct GroupVar {
    pub index: usize,
}

/// The scalar of a term: a variable, or the constant one.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ScalarTerm {
    Var(ScalarVar),
    Unit,
}

/// A term `scalar * elem`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Term {
    pub scalar: ScalarTerm,
    pub elem: GroupVar,
}

/// A term with its constant weight.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Weighted {
    pub term: Term,
    pub weight: Scalar,
}

/// A sparse linear combination `Σ weight_i * (scalar_i * elem_i)`, the
/// upstream `Sum<Weighted<Term<G>, G::Scalar>>`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LinearCombination {
    pub terms: Vec<Weighted>,
}

/// The assignment of group-element variables, by index.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GroupMap(pub Vec<Option<Element>>);

/// A list of linear combinations over allocated variables.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LinearMap {
    /// The linear combinations, one per equation.
    pub linear_combinations: Vec<LinearCombination>,
    /// The assigned group elements.
    pub group_elements: GroupMap,
    /// The number of allocated scalar variables.
    pub num_scalars: usize,
    /// The number of allocated group-element variables.
    pub num_elements: usize,
}

/// A linear map with the image variable of each equation: the statement
/// `image[i] = linear_combinations[i]` for every `i`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LinearRelation {
    pub linear_map: LinearMap,
    pub image: Vec<GroupVar>,
}

/// One equation of an instance (Section "Representation"): `image = terms`,
/// where `image` lists `(element_index, coeff)` and `terms` lists
/// `(scalar_index, element_index, coeff)`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Equation {
    pub image: Vec<(u32, Scalar)>,
    pub terms: Vec<(u32, u32, Scalar)>,
}

/// A validated instance (the specification's `LinearRelation`, Section 3.2).
/// `elements` is the element vector: the generator at index 0, then the
/// statement's elements. `image` is the evaluation of each equation's
/// left-hand side and `num_scalars` the witness length, both computed at
/// construction.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Instance {
    pub elements: Vec<Element>,
    pub equations: Vec<Equation>,
    pub image: Vec<Element>,
    pub num_scalars: usize,
}

/// The prover's secrets between its two moves.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProverState {
    pub nonces: Vec<Scalar>,
    pub witness: Vec<Scalar>,
}

/// The AND of instances: the statement that every branch holds.
///
/// Upstream composes instances into a tree (`ComposedInstance`) whose AND
/// nodes carry one commitment and one response per branch. For a tree of AND
/// nodes the protocol messages are those of its leaves, in depth-first order,
/// under one shared challenge; this is the AND of those leaves. The tree
/// itself enters only the instance label of the Fiat-Shamir layer.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AndInstance {
    pub branches: Vec<Instance>,
}

/// One scalar vector per branch of an [`AndInstance`]: the witness, or the
/// prover nonces, which have the witness's shape.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AndWitness {
    pub branches: Vec<Vec<Scalar>>,
}

/// One commitment per branch of an [`AndInstance`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AndCommitment {
    pub branches: Vec<Vec<Element>>,
}

/// One prover state per branch of an [`AndInstance`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AndProverState {
    pub branches: Vec<ProverState>,
}

/// One response per branch of an [`AndInstance`]: the response, or the
/// simulator randomness, which has the response's shape.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AndResponse {
    pub branches: Vec<Vec<Scalar>>,
}
