//! The test vectors of draft-irtf-cfrg-sigma-protocols-03, Appendix A, run
//! against the fork: the extracted Σ core with the non-extracted Fiat-Shamir
//! layer over SHAKE128, for the ciphersuites `sigma-proofs_Shake128_P256` and
//! `sigma-proofs_Shake128_BLS12381` and both flavours (batchable `DSFS`,
//! compact `CMPT`).
//!
//! Two vector sets, under `tests/vectors/`:
//!
//! - `draft03*.json`: Appendix A of draft-03 (17 August 2026), extracted from
//!   its text rendering; the fields are the draft's, with the section and the
//!   prose preceding each vector (`Section`, `Comment`).
//! - `upstream-0.4.1*.json`: the vectors that upstream `sigma-proofs` 0.4.1
//!   vendors (`tests/spec/testdata`), unchanged.
//!
//! Both sets have the same relations, witnesses, tags, session identifiers
//! and prover randomness (Appendix A.1). Their instance encodings differ:
//! draft-03, whose representation the core implements, places the generator
//! at element index 0 and has no identity slot
//! ([`InstanceFormat::Draft03`]: no index shift); upstream 0.4.1 places the
//! identity and the generator at element indices 0 and 1, so every element
//! index is one more ([`InstanceFormat::ImplicitIdentity`]). Both run through
//! the core's `ValidateInstance` with the ten checks of draft-03, Section 3.5,
//! and through draft-03's element codec, which rejects the identity.
//!
//! For each valid vector: the session identifier is `DeriveSessionID(Tag)`;
//! the relation rebuilt from the seeded PRNG by the core's `LinearRelation`
//! encodes to `Instance` and its witness to `Witness`; `Instance` decodes and
//! re-encodes to itself, and the element indices of the decoded core instance
//! are those of `Instance` (draft-03) or one less (upstream); `NargString`
//! verifies; and the prover, given the flavour's nonce stream, reproduces
//! `NargString` byte for byte. For each adversarial vector: an
//! `Expected = reject` vector is rejected while its `BaseId` baseline is
//! accepted, and an `Expected = accept` vector is accepted, except the
//! upstream vectors that only upstream 0.4.1 accepts
//! ([`UPSTREAM_ONLY_ACCEPTS`]), which the core rejects as draft-03 does and
//! the test reports. Batch verification is not run: the fork has no batch
//! verifier.

mod curves;

use spongefish::{derive_session_id, instantiations::Shake128, PrivateRng};

use curves::{Bls12381, P256};
use sigma_proofs_hax as fk;
use fk::fiat_shamir as ffs;
use fk::ristretto::Ristretto255;
use fk::wire::{serialize_instance, wire_index, GroupWire, InstanceFormat, WireInstance};
use fk::{
    Element, Equation, GroupVar, Instance, LinearCombination, LinearRelation, Scalar, ScalarTerm,
    ScalarVar, SigmaGroup, Term, Weighted,
};

type Drng = PrivateRng<Shake128>;

const DRAFT03_P256: &str = include_str!("vectors/draft03_Shake128_P256.json");
const DRAFT03_P256_INVALID: &str = include_str!("vectors/draft03-invalid_Shake128_P256.json");
const DRAFT03_BLS: &str = include_str!("vectors/draft03_Shake128_BLS12381.json");
const DRAFT03_BLS_INVALID: &str = include_str!("vectors/draft03-invalid_Shake128_BLS12381.json");
const UPSTREAM_P256: &str = include_str!("vectors/upstream-0.4.1_Shake128_P256.json");
const UPSTREAM_P256_INVALID: &str =
    include_str!("vectors/upstream-0.4.1-invalid_Shake128_P256.json");
const UPSTREAM_BLS: &str = include_str!("vectors/upstream-0.4.1_Shake128_BLS12381.json");
const UPSTREAM_BLS_INVALID: &str =
    include_str!("vectors/upstream-0.4.1-invalid_Shake128_BLS12381.json");

// ---------------------------------------------------------------------------
// Vector files
// ---------------------------------------------------------------------------

struct Vector {
    id: String,
    base_id: Option<String>,
    ciphersuite: String,
    relation: Option<String>,
    flavor: String,
    tag: String,
    session_id: Option<Vec<u8>>,
    instance: Vec<u8>,
    witness: Option<Vec<u8>>,
    narg_string: Vec<u8>,
    accept: bool,
}

impl Vector {
    /// The class of an adversarial vector: the letter of its last `Id`
    /// component (`A` encodings, `B` scalars, `C` lengths, `D` the zero
    /// proof, `E` instance validation, `F` binding, `H` tampering).
    fn class(&self) -> char {
        self.name().chars().next().unwrap()
    }

    /// The last `Id` component of an adversarial vector (`E1`, `F2b`, ...).
    fn name(&self) -> &str {
        self.id.rsplit('/').next().unwrap()
    }
}

fn unhex(s: &str) -> Vec<u8> {
    assert!(s.len().is_multiple_of(2), "odd hex length");
    (0..s.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&s[i..i + 2], 16).expect("hex digit"))
        .collect()
}

fn load(json: &str) -> Vec<Vector> {
    let records: serde_json::Value = serde_json::from_str(json).expect("vector file");
    records
        .as_array()
        .expect("a list of vectors")
        .iter()
        .map(|r| {
            let field = |k: &str| r.get(k).and_then(|v| v.as_str()).map(str::to_owned);
            let required = |k: &str| field(k).unwrap_or_else(|| panic!("field {k} missing"));
            let expected = required("Expected");
            assert!(expected == "accept" || expected == "reject");
            Vector {
                id: required("Id"),
                base_id: field("BaseId"),
                ciphersuite: required("Ciphersuite"),
                relation: field("Relation"),
                flavor: required("Flavor"),
                tag: required("Tag"),
                session_id: field("SessionId").map(|s| unhex(&s)),
                instance: unhex(&required("Instance")),
                witness: field("Witness").map(|s| unhex(&s)),
                narg_string: unhex(&required("NargString")),
                accept: expected == "accept",
            }
        })
        .collect()
}

// ---------------------------------------------------------------------------
// The seeded PRNG of Appendix A.1 and the relations
// ---------------------------------------------------------------------------

fn drng(tag: &str) -> Drng {
    PrivateRng::from_seed(*derive_session_id::<Shake128>(tag.as_bytes()).as_bytes())
}

fn sample<W: GroupWire>(rng: &mut Drng) -> Scalar {
    ffs::sample_scalar_of::<W, Shake128>(rng)
}

fn samples<W: GroupWire, const N: usize>(rng: &mut Drng) -> [Scalar; N] {
    core::array::from_fn(|_| sample::<W>(rng))
}

fn times_g<W: SigmaGroup>(s: &Scalar) -> Element {
    W::group_mul(s, &W::generator())
}

fn term<W: SigmaGroup>(scalar: ScalarVar, elem: GroupVar) -> Weighted {
    Weighted {
        term: Term {
            scalar: ScalarTerm::Var(scalar),
            elem,
        },
        weight: W::scalar_one(),
    }
}

fn constant(elem: GroupVar, weight: Scalar) -> Weighted {
    Weighted {
        term: Term {
            scalar: ScalarTerm::Unit,
            elem,
        },
        weight,
    }
}

fn lc(terms: Vec<Weighted>) -> LinearCombination {
    LinearCombination { terms }
}

fn assign<W: SigmaGroup>(r: LinearRelation, vars: &[GroupVar], dlogs: &[Scalar]) -> LinearRelation {
    let mut r = r;
    for (var, dlog) in vars.iter().zip(dlogs) {
        r = r.set_element::<W>(*var, times_g::<W>(dlog)).expect("fresh variable");
    }
    r
}

fn compiled<W: SigmaGroup>(r: LinearRelation, witness: Vec<Scalar>) -> (Instance, Vec<Scalar>) {
    let (_, instance) = r.compile_with_witness::<W>(&witness);
    (instance.expect("the relation compiles"), witness)
}

/// The relation `name` built with the core's `LinearRelation`, drawing the
/// auxiliary generators and the witness from `rng` in the order of the
/// specification's generator (that of upstream's `tests/spec_vectors.rs`).
fn build<W: GroupWire>(name: &str, rng: &mut Drng) -> (Instance, Vec<Scalar>) {
    let r = LinearRelation::new::<W>();
    let g = r.generator();
    match name {
        // X = x * G
        "discrete_logarithm" => {
            let (r, x) = r.allocate_scalar();
            let (r, _) = r.allocate_eq(lc(vec![term::<W>(x, g)]));
            let [x_val] = samples::<W, 1>(rng);
            compiled::<W>(r, vec![x_val])
        }
        // X = x * G, Y = x * H
        "dleq" | "dleq_derived_element" => {
            let [h, x_val] = samples::<W, 2>(rng);
            let (r, x) = r.allocate_scalar();
            let (r, _) = r.allocate_eq(lc(vec![term::<W>(x, g)]));
            let (r, var_h) = r.allocate_element();
            let (r, _) = r.allocate_eq(lc(vec![term::<W>(x, var_h)]));
            let r = assign::<W>(r, &[var_h], &[h]);
            compiled::<W>(r, vec![x_val])
        }
        // C = x * G + r * H
        "pedersen_commitment" => {
            let [h, x_val, r_val] = samples::<W, 3>(rng);
            let (r, s) = r.allocate_scalars_vec(2);
            let (r, var_h) = r.allocate_element();
            let (r, _) = r.allocate_eq(lc(vec![term::<W>(s[0], g), term::<W>(s[1], var_h)]));
            let r = assign::<W>(r, &[var_h], &[h]);
            compiled::<W>(r, vec![x_val, r_val])
        }
        // X = x0 * G0 + x1 * G1, Y = x0 * G2 + x1 * G3
        "pedersen_commitment_dleq" => {
            let gens = samples::<W, 4>(rng);
            let [x0, x1] = samples::<W, 2>(rng);
            let (r, s) = r.allocate_scalars_vec(2);
            let (r, b01) = r.allocate_elements_vec(2);
            let (r, _) = r.allocate_eq(lc(vec![term::<W>(s[0], b01[0]), term::<W>(s[1], b01[1])]));
            let (r, b23) = r.allocate_elements_vec(2);
            let (r, _) = r.allocate_eq(lc(vec![term::<W>(s[0], b23[0]), term::<W>(s[1], b23[1])]));
            let r = assign::<W>(r, &[b01[0], b01[1], b23[0], b23[1]], &gens);
            compiled::<W>(r, vec![x0, x1])
        }
        // C = blind * Q2 + msg_1 * J1 + msg_2 * J2 + msg_3 * J3
        "bbs_blind_commitment_computation" => {
            let gens = samples::<W, 4>(rng);
            let [m1, m2, m3] = samples::<W, 3>(rng);
            let [blind] = samples::<W, 1>(rng);
            let (r, s) = r.allocate_scalars_vec(4);
            let (r, b) = r.allocate_elements_vec(4);
            let (r, _) = r.allocate_eq(lc((0..4).map(|i| term::<W>(s[i], b[i])).collect()));
            let r = assign::<W>(r, &b, &gens);
            compiled::<W>(r, vec![blind, m1, m2, m3])
        }
        // X = x * G, M = x * E0 - E1
        "elgamal_decryption" => {
            let [x_val, r_val, m_val] = samples::<W, 3>(rng);
            let (r, x) = r.allocate_scalar();
            let (r, var_x) = r.allocate_eq(lc(vec![term::<W>(x, g)]));
            let (r, e) = r.allocate_elements_vec(3);
            let minus_one = W::scalar_neg(&W::scalar_one());
            let r = r.append_equation(e[2], lc(vec![term::<W>(x, e[0]), constant(e[1], minus_one)]));
            let big_x = times_g::<W>(&x_val);
            let m = times_g::<W>(&m_val);
            let e1 = W::group_add(&W::group_mul(&r_val, &big_x), &W::group_mul(&minus_one, &m));
            let mut r = r;
            for (var, value) in [(var_x, big_x), (e[0], times_g::<W>(&r_val)), (e[1], e1), (e[2], m)] {
                r = r.set_element::<W>(var, value).expect("fresh variable");
            }
            (r.compile::<W>().expect("the relation compiles"), vec![x_val])
        }
        other => panic!("unknown relation {other}"),
    }
}

// ---------------------------------------------------------------------------
// Verification and proving through the Fiat-Shamir layer
// ---------------------------------------------------------------------------

fn session(tag: &str) -> spongefish::SessionId {
    derive_session_id::<Shake128>(tag.as_bytes())
}

fn verify<W: GroupWire>(instance: &WireInstance<W>, v: &Vector) -> bool {
    let sid = session(&v.tag);
    match v.flavor.as_str() {
        "batchable" => ffs::verify_batchable_with::<Shake128, _>(&sid, instance, &v.narg_string).is_ok(),
        "compact" => ffs::verify_compact_with::<Shake128, _>(&sid, instance, &v.narg_string).is_ok(),
        other => panic!("unknown flavor {other}"),
    }
}

/// The verifier's decision on a vector: decode the instance, then verify;
/// a rejection carries its reason.
fn decide<W: GroupWire>(v: &Vector, format: InstanceFormat) -> Result<(), String> {
    match WireInstance::<W>::deserialize(&v.instance, format) {
        Ok(instance) => {
            if verify(&instance, v) {
                Ok(())
            } else {
                Err("the NARG string does not verify".to_owned())
            }
        }
        Err(e) => Err(match e.check {
            Some(check) => format!("ValidateInstance check {check}"),
            None => "the instance does not decode".to_owned(),
        }),
    }
}

fn verifies<W: GroupWire>(v: &Vector, format: InstanceFormat) -> bool {
    decide::<W>(v, format).is_ok()
}

fn take_u32(bytes: &[u8], pos: &mut usize) -> u32 {
    let x = u32::from_le_bytes(bytes[*pos..*pos + 4].try_into().expect("4 bytes"));
    *pos += 4;
    x
}

fn take_scalar(bytes: &[u8], pos: &mut usize) -> Scalar {
    let s: Scalar = bytes[*pos..*pos + 32].try_into().expect("32 bytes");
    *pos += 32;
    s
}

/// The equations of an instance encoding as they are on the wire, without
/// the core: element indices are wire indices.
fn wire_equations(bytes: &[u8]) -> Vec<Equation> {
    let mut pos = 0;
    let mut equations = Vec::new();
    for _ in 0..take_u32(bytes, &mut pos) {
        let mut image = Vec::new();
        for _ in 0..take_u32(bytes, &mut pos) {
            let element_index = take_u32(bytes, &mut pos);
            image.push((element_index, take_scalar(bytes, &mut pos)));
        }
        let mut terms = Vec::new();
        for _ in 0..take_u32(bytes, &mut pos) {
            let scalar_index = take_u32(bytes, &mut pos);
            let element_index = take_u32(bytes, &mut pos);
            terms.push((scalar_index, element_index, take_scalar(bytes, &mut pos)));
        }
        equations.push(Equation { image, terms });
    }
    equations
}

/// The core's equations with their element indices in `format`.
fn in_format(format: InstanceFormat, equations: &[Equation]) -> Vec<Equation> {
    let index = |e: u32| wire_index(format, e).expect("a wire index");
    equations
        .iter()
        .map(|eq| Equation {
            image: eq.image.iter().map(|&(e, c)| (index(e), c)).collect(),
            terms: eq.terms.iter().map(|&(s, e, c)| (s, index(e), c)).collect(),
        })
        .collect()
}

fn scalars_bytes(scalars: &[Scalar]) -> Vec<u8> {
    scalars.iter().flatten().copied().collect()
}

/// Runs the valid vectors; returns the failures.
fn run_valid<W: GroupWire>(vectors: &[Vector], format: InstanceFormat) -> Vec<String> {
    let mut failures = Vec::new();
    for v in vectors {
        let mut fail = |what: &str| failures.push(format!("{}: {what}", v.id));
        if !v.accept {
            fail("a valid vector expects reject");
            continue;
        }
        let relation = v.relation.as_deref().expect("Relation");
        let sid = session(&v.tag);
        if Some(sid.as_bytes().as_slice()) != v.session_id.as_deref() {
            fail("SessionId is not DeriveSessionID(Tag)");
        }

        // The relation rebuilt from the seeded PRNG.
        let mut rng = drng(&format!("TestDRNG-SIGMA-PROOFS-{}-{relation}", v.ciphersuite));
        let (built, witness) = build::<W>(relation, &mut rng);
        if serialize_instance::<W>(&built, format).as_deref() != Some(v.instance.as_slice()) {
            fail("the rebuilt relation does not encode to Instance");
        }
        if Some(scalars_bytes(&witness)) != v.witness {
            fail("the rebuilt witness is not Witness");
        }

        let instance = match WireInstance::<W>::deserialize(&v.instance, format) {
            Ok(instance) => instance,
            Err(e) => {
                fail(&format!("Instance does not decode ({e:?})"));
                continue;
            }
        };
        if instance.encoded() != v.instance.as_slice() {
            fail("Instance does not re-encode to itself");
        }
        // The core's element indices: those of the vector under draft-03,
        // one less under upstream 0.4.1.
        let core = &instance.instance().equations;
        let wire = wire_equations(&v.instance);
        if in_format(format, core) != wire {
            fail("the core's equations are not those of Instance");
        }
        if format == InstanceFormat::Draft03 && *core != wire {
            fail("the core shifts the element indices of a draft-03 Instance");
        }
        if !verify(&instance, v) {
            fail("NargString does not verify");
        }

        let marker = match v.flavor.as_str() {
            "batchable" => "DSFS",
            "compact" => "CMPT",
            other => panic!("unknown flavor {other}"),
        };
        let mut nonces = drng(&format!(
            "TestDRNG-SIGMA-PROOFS-{marker}-{}-{relation}",
            v.ciphersuite
        ));
        let proof = match marker {
            "DSFS" => ffs::prove_batchable_with::<Shake128, Shake128, _>(&sid, &instance, &witness, &mut nonces),
            _ => ffs::prove_compact_with::<Shake128, Shake128, _>(&sid, &instance, &witness, &mut nonces),
        };
        match proof {
            Ok(bytes) if bytes == v.narg_string => {}
            Ok(_) => fail("the regenerated NARG string differs from NargString"),
            Err(e) => fail(&format!("the prover fails ({e:?})")),
        }
    }
    failures
}

/// The outcome of a run of adversarial vectors.
struct Outcome {
    failures: Vec<String>,
    run: usize,
    /// The `Expected = accept` vectors of `only_upstream` that the core
    /// rejects, with the reason.
    draft03_rejections: Vec<String>,
}

/// Runs the adversarial vectors of the classes `classes`. A vector named in
/// `only_upstream` (by its last `Id` component) is an `Expected = accept`
/// vector of upstream 0.4.1 that draft-03 rejects: the core must reject it.
fn run_adversarial<W: GroupWire>(
    valid: &[Vector],
    invalid: &[Vector],
    format: InstanceFormat,
    classes: &str,
    only_upstream: &[&str],
) -> Outcome {
    let mut failures = Vec::new();
    let mut draft03_rejections = Vec::new();
    let mut run = 0;
    for v in invalid.iter().filter(|v| classes.contains(v.class())) {
        run += 1;
        let verdict = decide::<W>(v, format);
        if only_upstream.iter().any(|name| *name == v.name()) {
            match verdict {
                Ok(()) if v.accept => {
                    failures.push(format!("{}: draft-03 rejects it, accepted", v.id))
                }
                Err(reason) if v.accept => draft03_rejections.push(format!("{} ({reason})", v.id)),
                _ => failures.push(format!("{}: listed as upstream-only, expects reject", v.id)),
            }
            continue;
        }
        if v.accept {
            if let Err(reason) = verdict {
                failures.push(format!("{}: must accept, rejected ({reason})", v.id));
            }
            continue;
        }
        if verdict.is_ok() {
            failures.push(format!("{}: must reject, accepted", v.id));
        }
        let base_id = v.base_id.as_deref().expect("BaseId");
        match valid.iter().find(|b| b.id == base_id) {
            Some(base) if verifies::<W>(base, format) => {}
            Some(_) => failures.push(format!("{}: baseline {base_id} rejected", v.id)),
            None => failures.push(format!("{}: baseline {base_id} not found", v.id)),
        }
    }
    if draft03_rejections.len() != only_upstream.len() {
        failures.push(format!(
            "{} upstream-only vectors listed, {} rejected",
            only_upstream.len(),
            draft03_rejections.len()
        ));
    }
    Outcome {
        failures,
        run,
        draft03_rejections,
    }
}

fn report(name: &str, run: usize, failures: &[String]) {
    eprintln!("{name}: {} of {run} vectors pass", run - failures.len().min(run));
    for f in failures {
        eprintln!("  FAIL {f}");
    }
    assert!(failures.is_empty(), "{name}: {} failures", failures.len());
}

fn valid_suite<W: GroupWire>(name: &str, json: &str, format: InstanceFormat) {
    let valid = load(json);
    assert!(!valid.is_empty());
    report(name, valid.len(), &run_valid::<W>(&valid, format));
}

fn adversarial_suite<W: GroupWire>(
    name: &str,
    valid_json: &str,
    invalid_json: &str,
    format: InstanceFormat,
    classes: &str,
    only_upstream: &[&str],
) {
    let outcome = run_adversarial::<W>(
        &load(valid_json),
        &load(invalid_json),
        format,
        classes,
        only_upstream,
    );
    assert!(outcome.run > 0);
    if !outcome.draft03_rejections.is_empty() {
        eprintln!(
            "{name}: {} vectors accepted by upstream 0.4.1 are draft-03 rejections",
            outcome.draft03_rejections.len()
        );
        for r in &outcome.draft03_rejections {
            eprintln!("  DRAFT-03 REJECTS {r}");
        }
    }
    report(name, outcome.run, &outcome.failures);
}

/// Every adversarial class of the vector files.
const ALL_CLASSES: &str = "ABCDEFH";

/// The `Expected = accept` vectors of upstream 0.4.1 that draft-03 rejects:
/// the empty relation (check 1), an unused scalar index (check 6, twice), an
/// image that is the identity (check 9), and an identity element in the
/// instance (check 8; the element codec rejects its encoding).
const UPSTREAM_ONLY_ACCEPTS: &[&str] = &["E0", "E1", "E1b", "E2", "E3"];

/// The classes whose decision the codec, the Fiat-Shamir layer and the core's
/// verifier make: encodings, scalars, lengths, the zero proof, binding and
/// tampering.
const TRANSCRIPT_CLASSES: &str = "ABCDFH";

// ---------------------------------------------------------------------------
// draft-irtf-cfrg-sigma-protocols-03, Appendix A
// ---------------------------------------------------------------------------

#[test]
fn draft03_valid_p256() {
    valid_suite::<P256>("draft-03 A.2.1 P-256", DRAFT03_P256, InstanceFormat::Draft03);
}

#[test]
fn draft03_valid_bls12381() {
    valid_suite::<Bls12381>("draft-03 A.3.1 BLS12-381", DRAFT03_BLS, InstanceFormat::Draft03);
}

#[test]
fn draft03_adversarial_p256() {
    adversarial_suite::<P256>(
        "draft-03 A.2.2 P-256 (classes A-D, F, H)",
        DRAFT03_P256,
        DRAFT03_P256_INVALID,
        InstanceFormat::Draft03,
        TRANSCRIPT_CLASSES,
        &[],
    );
}

#[test]
fn draft03_adversarial_bls12381() {
    adversarial_suite::<Bls12381>(
        "draft-03 A.3.2 BLS12-381 (classes A-D, F, H)",
        DRAFT03_BLS,
        DRAFT03_BLS_INVALID,
        InstanceFormat::Draft03,
        TRANSCRIPT_CLASSES,
        &[],
    );
}

/// Class E of draft-03 tests its `ValidateInstance` (Section 3.5): an unused
/// scalar index (check 6: E1, E1b), an image that is the identity (check 9:
/// E2), an identity element (check 8, rejected by the element codec: E3), and
/// an element index out of range (check 4, or a short element section: E4).
#[test]
fn draft03_instance_validation_p256() {
    adversarial_suite::<P256>(
        "draft-03 A.2.2 P-256 (class E)",
        DRAFT03_P256,
        DRAFT03_P256_INVALID,
        InstanceFormat::Draft03,
        "E",
        &[],
    );
}

#[test]
fn draft03_instance_validation_bls12381() {
    adversarial_suite::<Bls12381>(
        "draft-03 A.3.2 BLS12-381 (class E)",
        DRAFT03_BLS,
        DRAFT03_BLS_INVALID,
        InstanceFormat::Draft03,
        "E",
        &[],
    );
}

// ---------------------------------------------------------------------------
// The vectors of upstream sigma-proofs 0.4.1
// ---------------------------------------------------------------------------

#[test]
fn upstream_041_valid_p256() {
    valid_suite::<P256>("upstream 0.4.1 P-256", UPSTREAM_P256, InstanceFormat::ImplicitIdentity);
}

#[test]
fn upstream_041_valid_bls12381() {
    valid_suite::<Bls12381>(
        "upstream 0.4.1 BLS12-381",
        UPSTREAM_BLS,
        InstanceFormat::ImplicitIdentity,
    );
}

#[test]
fn upstream_041_adversarial_p256() {
    adversarial_suite::<P256>(
        "upstream 0.4.1 invalid P-256",
        UPSTREAM_P256,
        UPSTREAM_P256_INVALID,
        InstanceFormat::ImplicitIdentity,
        ALL_CLASSES,
        UPSTREAM_ONLY_ACCEPTS,
    );
}

#[test]
fn upstream_041_adversarial_bls12381() {
    adversarial_suite::<Bls12381>(
        "upstream 0.4.1 invalid BLS12-381",
        UPSTREAM_BLS,
        UPSTREAM_BLS_INVALID,
        InstanceFormat::ImplicitIdentity,
        ALL_CLASSES,
        UPSTREAM_ONLY_ACCEPTS,
    );
}

// ---------------------------------------------------------------------------
// The wire layer against the core's own encoding
// ---------------------------------------------------------------------------

/// Over Ristretto255, the draft-03 instance encoding of the wire layer is the
/// core's `Instance::serialize`, and the upstream encoding carries the core's
/// equations with every element index one more, for every relation of the
/// suite.
#[test]
fn ristretto_wire_encoding_is_the_core_encoding() {
    for name in [
        "discrete_logarithm",
        "dleq",
        "pedersen_commitment",
        "pedersen_commitment_dleq",
        "bbs_blind_commitment_computation",
        "elgamal_decryption",
    ] {
        let mut rng = drng(&format!("sigma-proofs-hax wire {name}"));
        let (instance, _) = build::<Ristretto255>(name, &mut rng);
        assert_eq!(
            serialize_instance::<Ristretto255>(&instance, InstanceFormat::Draft03),
            Some(instance.serialize()),
            "{name}"
        );
        let upstream =
            serialize_instance::<Ristretto255>(&instance, InstanceFormat::ImplicitIdentity)
                .expect("an upstream encoding");
        assert_eq!(
            wire_equations(&upstream),
            in_format(InstanceFormat::ImplicitIdentity, &instance.equations),
            "{name}"
        );
    }
}
