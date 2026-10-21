//! Differential test of the fork against the unmodified upstream
//! `sigma-proofs` 0.4.1 (dev-dependency `sigma-proofs = "=0.4.1"`), over
//! Ristretto255.
//!
//! The fork follows draft-irtf-cfrg-sigma-protocols-03: the generator is
//! element 0 and there is no identity slot, and `ValidateInstance` runs ten
//! checks. Upstream 0.4.1 places the identity and the generator at element
//! indices 0 and 1 and runs three checks (draft-03's checks 3 to 5). The two
//! are compared through the index shift of the wire layer
//! (`InstanceFormat::ImplicitIdentity`: upstream index `i + 1` is the fork's
//! index `i`, and upstream's identity slot has no fork index). On the inputs
//! both accept the results must agree; an input only upstream accepts must be
//! rejected by a check of draft-03 that upstream does not run, and is
//! reported (tallied by check) as a draft-03 rejection; an input only the
//! fork accepts is a failure.
//!
//! Both sides build the same relations (discrete logarithm, DLEQ, Pedersen,
//! a three-equation relation with weights and constant terms, and random
//! relations), and the test compares:
//!
//! - compilation: the result, the failed check, the instance encoding (the
//!   fork's through the index shift), the image and the witness length;
//! - `ValidateInstance` on random raw instances (`Instance::new`, the fork's
//!   after the index shift);
//! - the Σ-protocol: commitment and response from the same nonces (the fork
//!   takes upstream's nonces, drawn from the same seeded `PrivateRng`), the
//!   verifier, the batchable verifier (one random linear combination), the
//!   simulator, and tampered and ill-shaped transcripts;
//! - the NARG strings of batchable and compact proofs, byte for byte, and
//!   cross-verification of each side's proofs, of tampered and truncated ones;
//! - AND compositions (nested upstream trees against the AND of their
//!   leaves).

#![allow(clippy::type_complexity)]

use std::cell::RefCell;
use std::collections::BTreeMap;

use curve25519_dalek::constants::RISTRETTO_BASEPOINT_POINT;
use curve25519_dalek::{RistrettoPoint as G, Scalar as S};

use sigma_proofs as up;
use up::codec::ScalarCodec;
use up::composition::{ComposedCommitment, ComposedInstance, ComposedResponse, ComposedWitness};
use up::linear_relation::{
    Equation as UEquation, GroupVar as UGroupVar, Instance as UInstance,
    LinearCombination as ULinearCombination, Term as UTerm, Weighted as UWeighted,
};
use up::traits::{SigmaProtocol, SigmaProtocolSimulator};
use up::{DefaultHash, PrivateRng};

use fk::fiat_shamir::{self as ffs, AndTree};
use fk::ristretto::{decode_scalar, encode_element, encode_scalar, Ristretto255 as R};
use fk::wire::{core_equations, serialize_instance, InstanceFormat};
use fk::SigmaGroup;
use sigma_proofs_hax as fk;

type Rng = PrivateRng<DefaultHash>;

fn rng(seed: u64, stream: u8) -> Rng {
    let mut bytes = [0u8; 32];
    bytes[..8].copy_from_slice(&seed.to_le_bytes());
    bytes[8] = stream;
    Rng::from_seed(bytes)
}

fn sample(rng: &mut Rng) -> S {
    <S as ScalarCodec>::sample(rng)
}

fn sample_vec(rng: &mut Rng, n: usize) -> Vec<S> {
    (0..n).map(|_| sample(rng)).collect()
}

fn point(rng: &mut Rng) -> G {
    RISTRETTO_BASEPOINT_POINT * sample(rng)
}

fn es(xs: &[S]) -> Vec<fk::Scalar> {
    xs.iter().map(encode_scalar).collect()
}

fn ee(xs: &[G]) -> Vec<fk::Element> {
    xs.iter().map(encode_element).collect()
}

fn small(rng: &mut Rng, bound: u64) -> u64 {
    let mut b = [0u8; 8];
    rng.fill_bytes(&mut b);
    u64::from_le_bytes(b) % bound
}

// ---------------------------------------------------------------------------
// Relation specifications, built on both sides
// ---------------------------------------------------------------------------

#[derive(Clone, Copy, Debug)]
enum Sc {
    Var(usize),
    Unit,
}

#[derive(Clone, Debug)]
struct EqSpec {
    /// A preassigned image, or `None` for an image computed from the witness.
    lhs: Option<G>,
    /// `(scalar, element variable index, weight)`.
    terms: Vec<(Sc, usize, S)>,
}

#[derive(Clone, Debug)]
struct RelSpec {
    num_scalars: usize,
    /// The assigned elements, at variable indices `2..2 + bases.len()`
    /// (upstream's: 0 is the identity, 1 the generator).
    bases: Vec<G>,
    /// Further element variables, allocated and never assigned.
    extra: usize,
    equations: Vec<EqSpec>,
}

fn build_upstream(spec: &RelSpec) -> up::LinearRelation<G> {
    let mut r = up::LinearRelation::<G>::new();
    let svars = r.allocate_scalars_vec(spec.num_scalars);
    let mut gvars: Vec<UGroupVar<G>> = vec![r.identity(), r.generator()];
    for b in &spec.bases {
        gvars.push(r.allocate_element_with(*b));
    }
    for _ in 0..spec.extra {
        gvars.push(r.allocate_element());
    }
    for eq in &spec.equations {
        let lc: ULinearCombination<G> = eq
            .terms
            .iter()
            .map(|t| {
                let term: UTerm<G> = match t.0 {
                    Sc::Var(i) => UTerm::from((svars[i], gvars[t.1])),
                    Sc::Unit => UTerm::from(gvars[t.1]),
                };
                UWeighted { term, weight: t.2 }
            })
            .sum();
        match eq.lhs {
            Some(value) => {
                r.allocate_eq_with(value, lc);
            }
            None => {
                r.allocate_eq(lc);
            }
        }
    }
    r
}

/// The specification built on the fork. The fork has no identity variable:
/// the specification's index 0 is a variable assigned the identity,
/// allocated after the generator, so that compilation drops it unless an
/// equation uses it (which validation then rejects, check 8). Every other
/// index keeps its position: the generator is the fork's variable 0 and
/// compilation renumbers the elements from 1, in upstream's order.
fn build_fork(spec: &RelSpec) -> fk::LinearRelation {
    let r = fk::LinearRelation::new::<R>();
    let (r, svars) = r.allocate_scalars_vec(spec.num_scalars);
    let generator = r.generator();
    let (mut r, identity) = r.allocate_element_with(R::identity());
    let mut gvars = vec![identity, generator];
    for b in &spec.bases {
        let (next, var) = r.allocate_element_with(encode_element(b));
        r = next;
        gvars.push(var);
    }
    let (mut r, extra) = r.allocate_elements_vec(spec.extra);
    gvars.extend(extra);
    for eq in &spec.equations {
        let terms = eq
            .terms
            .iter()
            .map(|t| fk::Weighted {
                term: fk::Term {
                    scalar: match t.0 {
                        Sc::Var(i) => fk::ScalarTerm::Var(svars[i]),
                        Sc::Unit => fk::ScalarTerm::Unit,
                    },
                    elem: gvars[t.1],
                },
                weight: encode_scalar(&t.2),
            })
            .collect();
        let lc = fk::LinearCombination { terms };
        r = match eq.lhs {
            Some(value) => r.allocate_eq_with(encode_element(&value), lc).0,
            None => r.allocate_eq(lc).0,
        };
    }
    r
}

// ---------------------------------------------------------------------------
// Draft-03 rejections
// ---------------------------------------------------------------------------

/// The checks of draft-03 that upstream 0.4.1 does not run; upstream's
/// checks 1 (counts), 2 (index range) and 3 (every element used) are
/// draft-03's 3, 4 and 5.
const DRAFT03_ONLY_CHECKS: [u8; 7] = [1, 2, 6, 7, 8, 9, 10];

thread_local! {
    /// The inputs of the running test that upstream accepts and the fork
    /// rejects, by the draft-03 check that rejects them.
    static DRAFT03_REJECTIONS: RefCell<BTreeMap<u8, usize>> = const { RefCell::new(BTreeMap::new()) };
}

/// Records an input that only upstream accepts; the fork's failure must be
/// a check that upstream does not run.
fn draft03_rejection(context: &str, check: Option<u8>) {
    let check = check.unwrap_or_else(|| {
        panic!("{context}: only upstream accepts, and the fork fails outside ValidateInstance")
    });
    assert!(
        DRAFT03_ONLY_CHECKS.contains(&check),
        "{context}: only upstream accepts, and the fork fails check {check}, which upstream runs"
    );
    DRAFT03_REJECTIONS.with(|t| *t.borrow_mut().entry(check).or_insert(0) += 1);
}

/// Prints and returns the draft-03 rejections of the running test.
fn report_draft03_rejections(test: &str) -> BTreeMap<u8, usize> {
    let tally = DRAFT03_REJECTIONS.with(|t| std::mem::take(&mut *t.borrow_mut()));
    let total: usize = tally.values().sum();
    eprintln!("{test}: {total} inputs accepted by upstream 0.4.1 are draft-03 rejections");
    for (check, n) in &tally {
        eprintln!("  draft-03 check {check}: {n}");
    }
    tally
}

/// Both sides reject: a check that upstream also runs fails as upstream's
/// does (under draft-03's number); the fork may fail a draft-03 check first.
fn both_reject(context: &str, upstream: Option<u8>, fork: Option<u8>) {
    match fork {
        Some(check) if DRAFT03_ONLY_CHECKS.contains(&check) => {}
        _ => assert_eq!(
            fork,
            upstream.map(|check| check + 2),
            "{context}: failed checks differ"
        ),
    }
}

/// The upstream encoding of a fork instance: its draft-03 encoding with
/// every element index one more.
fn upstream_encoding(fi: &fk::Instance) -> Vec<u8> {
    serialize_instance::<R>(fi, InstanceFormat::ImplicitIdentity).expect("an upstream encoding")
}

/// The two sides hold the same instance: the encodings (the fork's through
/// the index shift), the images, the witness lengths, and the elements (the
/// fork has no identity slot).
fn assert_same_instance(ui: &UInstance<G>, fi: &fk::Instance) {
    assert_eq!(ui.serialize(), upstream_encoding(fi), "instance encodings differ");
    assert_eq!(ee(ui.image()), fi.image, "images differ");
    assert_eq!(ui.num_scalars(), fi.num_scalars(), "witness lengths differ");
    assert_eq!(ui.num_equations(), fi.num_equations());
    assert_eq!(ui.num_elements(), fi.num_elements() + 1);
    assert_eq!(ee(ui.elements()), fi.statement_elements());
}

/// The result of compiling a specification on both sides.
#[allow(clippy::large_enum_variant)]
enum Compiled {
    /// Both sides compile, to the same instance.
    Both(UInstance<G>, fk::Instance),
    /// Upstream compiles; the fork rejects the instance by a check of
    /// draft-03 that upstream does not run (the check).
    OnlyUpstream(u8),
    /// Neither side compiles.
    Neither,
}

/// Compiles the specification on both sides with `witness` and checks that
/// the two agree.
fn compile_both(spec: &RelSpec, witness: &[S]) -> Compiled {
    let mut ur = build_upstream(spec);
    let fr = build_fork(spec);
    let up_result = ur.compile_with_witness(witness);
    let (_, fk_result) = fr.compile_with_witness::<R>(&es(witness));
    match (up_result, fk_result) {
        (Ok(ui), Ok(fi)) => {
            assert_same_instance(&ui, &fi);
            Compiled::Both(ui, fi)
        }
        (Ok(_), Err(fe)) => {
            draft03_rejection("compilation", fe.check);
            Compiled::OnlyUpstream(fe.check.expect("a check"))
        }
        (Err(ue), Err(fe)) => {
            both_reject("compilation", ue.check, fe.check);
            Compiled::Neither
        }
        (Err(_), Ok(_)) => panic!("compilation: the fork accepts what upstream rejects"),
    }
}

/// Both sides compile the specification.
fn compile_both_ok(spec: &RelSpec, witness: &[S]) -> (UInstance<G>, fk::Instance) {
    match compile_both(spec, witness) {
        Compiled::Both(ui, fi) => (ui, fi),
        Compiled::OnlyUpstream(check) => panic!("draft-03 rejects the relation (check {check})"),
        Compiled::Neither => panic!("the relation does not compile"),
    }
}

// ---------------------------------------------------------------------------
// The named relations
// ---------------------------------------------------------------------------

fn dlog(rng: &mut Rng) -> RelSpec {
    let one = S::ONE;
    let _ = rng;
    RelSpec {
        num_scalars: 1,
        bases: vec![],
        extra: 0,
        equations: vec![EqSpec {
            lhs: None,
            terms: vec![(Sc::Var(0), 1, one)],
        }],
    }
}

fn dleq(rng: &mut Rng) -> RelSpec {
    let h = point(rng);
    RelSpec {
        num_scalars: 1,
        bases: vec![h],
        extra: 0,
        equations: vec![
            EqSpec {
                lhs: None,
                terms: vec![(Sc::Var(0), 1, S::ONE)],
            },
            EqSpec {
                lhs: None,
                terms: vec![(Sc::Var(0), 2, S::ONE)],
            },
        ],
    }
}

fn pedersen(rng: &mut Rng) -> RelSpec {
    let h = point(rng);
    RelSpec {
        num_scalars: 2,
        bases: vec![h],
        extra: 0,
        equations: vec![EqSpec {
            lhs: None,
            terms: vec![(Sc::Var(0), 1, S::ONE), (Sc::Var(1), 2, S::ONE)],
        }],
    }
}

/// Three equations over three scalars, with weights other than one,
/// constant terms, a shared scalar across equations, two terms on one
/// element, and an allocated element that no equation uses (dropped and the
/// indices renumbered by compilation).
fn three_equations(rng: &mut Rng) -> RelSpec {
    let h = point(rng);
    let unused = point(rng);
    let k = point(rng);
    let two = S::from(2u64);
    let three = S::from(3u64);
    let five = S::from(5u64);
    RelSpec {
        num_scalars: 3,
        // h at 2, unused at 3, k at 4
        bases: vec![h, unused, k],
        extra: 0,
        equations: vec![
            EqSpec {
                lhs: None,
                terms: vec![(Sc::Var(0), 1, S::ONE), (Sc::Var(1), 2, S::ONE)],
            },
            EqSpec {
                lhs: None,
                terms: vec![
                    (Sc::Var(1), 4, three),
                    (Sc::Var(2), 1, -S::ONE),
                    (Sc::Unit, 2, two),
                    (Sc::Var(1), 2, two),
                ],
            },
            EqSpec {
                lhs: None,
                terms: vec![
                    (Sc::Var(2), 2, S::ONE),
                    (Sc::Var(0), 4, S::ONE),
                    (Sc::Var(1), 1, S::ONE),
                    (Sc::Unit, 4, -five),
                ],
            },
        ],
    }
}

/// A random relation: element indices among the generator and the assigned
/// elements (rarely the identity or an unassigned element), random weights,
/// some constant terms, some preassigned images (true or false for the
/// witness given). The first term of equation `j` carries the scalar
/// `j mod num_scalars` on a non-identity element, so that most relations
/// meet draft-03's checks 2 and 6; those with fewer equations than scalars,
/// with no scalars, or with a term on the identity meet upstream's checks
/// only.
fn random_relation(rng: &mut Rng, witness: &[S]) -> RelSpec {
    let num_scalars = witness.len();
    let nb = small(rng, 4) as usize;
    let bases: Vec<G> = (0..nb).map(|_| point(rng)).collect();
    let extra = small(rng, 2) as usize;
    let ne = 1 + small(rng, 3) as usize;
    let mut equations = Vec::new();
    for j in 0..ne {
        let mut terms = Vec::new();
        if num_scalars > 0 {
            let e = 1 + small(rng, (nb + 1) as u64) as usize;
            terms.push((Sc::Var(j % num_scalars), e, S::ONE));
        }
        let nt = small(rng, 3) as usize;
        for _ in 0..nt {
            let sc = if num_scalars > 0 && small(rng, 5) != 0 {
                Sc::Var(small(rng, num_scalars as u64) as usize)
            } else {
                Sc::Unit
            };
            let e = match small(rng, 20) {
                0 => 0,
                1 if extra > 0 => 2 + nb + small(rng, extra as u64) as usize,
                _ => 1 + small(rng, (nb + 1) as u64) as usize,
            };
            let w = if small(rng, 2) == 0 {
                S::ONE
            } else {
                sample(rng)
            };
            terms.push((sc, e, w));
        }
        equations.push(EqSpec { lhs: None, terms });
    }
    // Preassign some images: to their true value, or to a random element.
    for equation in equations.iter_mut() {
        match small(rng, 4) {
            0 => {
                let value: G = equation
                    .terms
                    .iter()
                    .map(|&(sc, e, w)| {
                        let s = match sc {
                            Sc::Var(i) => witness[i],
                            Sc::Unit => S::ONE,
                        };
                        let base = match e {
                            0 => G::default(),
                            1 => RISTRETTO_BASEPOINT_POINT,
                            k if k < 2 + nb => bases[k - 2],
                            _ => G::default(),
                        };
                        base * (s * w)
                    })
                    .sum();
                equation.lhs = Some(value);
            }
            1 => equation.lhs = Some(point(rng)),
            _ => {}
        }
    }
    RelSpec {
        num_scalars,
        bases,
        extra,
        equations,
    }
}

// ---------------------------------------------------------------------------
// The Σ-protocol, compared
// ---------------------------------------------------------------------------

fn same_verdict<A, B>(context: &str, u: &Result<(), A>, f: &Result<(), B>) {
    assert_eq!(u.is_ok(), f.is_ok(), "{context}: verdicts differ");
}

/// Runs the protocol on both sides for one compiled instance and witness.
/// Returns whether the honest transcript verified.
fn protocol_both(ui: &UInstance<G>, fi: &fk::Instance, witness: &[S], seed: u64) -> bool {
    let n = ui.num_scalars();
    let fw = es(witness);

    // Witness validity.
    if witness.len() == n {
        assert_eq!(
            bool::from(ui.is_witness_valid(witness)),
            fi.is_witness_valid::<R>(&fw),
            "witness validity differs"
        );
    }

    // Commitment from the same nonces.
    let mut ur = rng(seed, 1);
    let mut fr = rng(seed, 1);
    let up_commit = ui.prover_commit(witness, &mut ur);
    let nonces = sample_vec(&mut fr, if witness.len() == n { n } else { 0 });
    let fk_commit = fi.prover_commit::<R>(&fw, &es(&nonces));
    let ((uc, ust), (fc, fst)) = match (up_commit, fk_commit) {
        (Ok(u), Ok(f)) => (u, f),
        (Err(_), Err(_)) => return false,
        (u, f) => panic!("prover_commit disagrees: {} vs {}", u.is_ok(), f.is_ok()),
    };
    assert_eq!(ee(&uc), fc, "commitments differ");

    // Response to the same challenge.
    let mut cr = rng(seed, 2);
    let challenge = sample(&mut cr);
    let fch = encode_scalar(&challenge);
    let ures = ui
        .prover_response(ust, &challenge)
        .expect("upstream response");
    let fres = fi.prover_response::<R>(&fst, &fch).expect("fork response");
    assert_eq!(es(&ures), fres, "responses differ");

    // Verifier and batchable verifier.
    let randomness = sample(&mut cr);
    let frand = encode_scalar(&randomness);
    let uv = ui.verifier(&uc, &challenge, &ures);
    let fv = fi.verifier::<R>(&fc, &fch, &fres);
    same_verdict("verifier", &uv, &fv);
    let uvr = ui.verifier_with_randomness(&uc, &challenge, &ures, &randomness);
    let fvr = fi.verifier_with_randomness::<R>(&fc, &fch, &fres, &frand);
    same_verdict("verifier_with_randomness", &uvr, &fvr);
    assert_eq!(uv.is_ok(), uvr.is_ok(), "the two upstream verifiers differ");
    let honest = uv.is_ok();

    // Tampered transcripts.
    for i in 0..ures.len() {
        let mut ut = ures.clone();
        ut[i] += S::ONE;
        let ft = es(&ut);
        same_verdict(
            "tampered response",
            &ui.verifier(&uc, &challenge, &ut),
            &fi.verifier::<R>(&fc, &fch, &ft),
        );
        same_verdict(
            "tampered response (batch)",
            &ui.verifier_with_randomness(&uc, &challenge, &ut, &randomness),
            &fi.verifier_with_randomness::<R>(&fc, &fch, &ft, &frand),
        );
    }
    for j in 0..uc.len() {
        let mut ct = uc.clone();
        ct[j] += RISTRETTO_BASEPOINT_POINT;
        let fct = ee(&ct);
        same_verdict(
            "tampered commitment",
            &ui.verifier(&ct, &challenge, &ures),
            &fi.verifier::<R>(&fct, &fch, &fres),
        );
        same_verdict(
            "tampered commitment (batch)",
            &ui.verifier_with_randomness(&ct, &challenge, &ures, &randomness),
            &fi.verifier_with_randomness::<R>(&fct, &fch, &fres, &frand),
        );
    }
    let ch2 = challenge + S::ONE;
    let fch2 = encode_scalar(&ch2);
    same_verdict(
        "tampered challenge",
        &ui.verifier(&uc, &ch2, &ures),
        &fi.verifier::<R>(&fc, &fch2, &fres),
    );
    same_verdict(
        "tampered challenge (batch)",
        &ui.verifier_with_randomness(&uc, &ch2, &ures, &randomness),
        &fi.verifier_with_randomness::<R>(&fc, &fch2, &fres, &frand),
    );
    // Ill-shaped transcripts.
    if !ures.is_empty() {
        let short = &ures[..ures.len() - 1];
        same_verdict(
            "short response",
            &ui.verifier(&uc, &challenge, &short.to_vec()),
            &fi.verifier::<R>(&fc, &fch, &es(short)),
        );
    }
    let mut long = ures.clone();
    long.push(S::ONE);
    same_verdict(
        "long response",
        &ui.verifier(&uc, &challenge, &long),
        &fi.verifier::<R>(&fc, &fch, &es(&long)),
    );
    let mut longc = uc.clone();
    longc.push(RISTRETTO_BASEPOINT_POINT);
    same_verdict(
        "long commitment",
        &ui.verifier(&longc, &challenge, &ures),
        &fi.verifier::<R>(&ee(&longc), &fch, &fres),
    );

    // Simulator: the same randomness gives the same transcript.
    let mut us = rng(seed, 3);
    let mut fs = rng(seed, 3);
    let (sc, sch, sres) = ui
        .simulate_transcript(&mut us)
        .expect("upstream simulation");
    let fsres_rand = sample_vec(&mut fs, n);
    let fsch = sample(&mut fs);
    let (fsc, fsch_out, fsres) = fi
        .simulate_transcript::<R>(&es(&fsres_rand), &encode_scalar(&fsch))
        .expect("fork simulation");
    assert_eq!(ee(&sc), fsc, "simulated commitments differ");
    assert_eq!(encode_scalar(&sch), fsch_out, "simulated challenges differ");
    assert_eq!(es(&sres), fsres, "simulated responses differ");
    assert!(ui.verifier(&sc, &sch, &sres).is_ok());
    assert!(fi.verifier::<R>(&fsc, &fsch_out, &fsres).is_ok());
    assert!(fi
        .verifier_with_randomness::<R>(&fsc, &fsch_out, &fsres, &frand)
        .is_ok());

    // Simulated commitment of an arbitrary transcript.
    let zr = sample_vec(&mut cr, n);
    let uz = ui.simulate_commitment(&challenge, &zr).expect("upstream");
    let fz = fi.simulate_commitment::<R>(&fch, &es(&zr)).expect("fork");
    assert_eq!(ee(&uz), fz, "simulate_commitment differs");
    let zbad = sample_vec(&mut cr, n + 1);
    assert_eq!(
        ui.simulate_commitment(&challenge, &zbad).is_ok(),
        fi.simulate_commitment::<R>(&fch, &es(&zbad)).is_ok()
    );

    honest
}

/// The NARG strings of batchable and compact proofs, compared byte for byte,
/// and cross-verified with tampering.
fn narg_both(ui: &UInstance<G>, fi: &fk::Instance, witness: &[S], seed: u64) {
    let sid = up::derive_session_id::<DefaultHash>(b"sigma-proofs-hax differential");
    let fw = es(witness);

    let up_b =
        up::prove_batchable_with::<DefaultHash, UInstance<G>>(&sid, ui, witness, &mut rng(seed, 4));
    let fk_b = ffs::prove_batchable_with::<DefaultHash, DefaultHash, fk::Instance>(
        &sid,
        fi,
        &fw,
        &mut rng(seed, 4),
    );
    let up_c =
        up::prove_compact_with::<DefaultHash, UInstance<G>>(&sid, ui, witness, &mut rng(seed, 5));
    let fk_c = ffs::prove_compact_with::<DefaultHash, DefaultHash, fk::Instance>(
        &sid,
        fi,
        &fw,
        &mut rng(seed, 5),
    );
    assert_eq!(up_b.is_ok(), fk_b.is_ok());
    assert_eq!(up_c.is_ok(), fk_c.is_ok());
    let (Ok(ub), Ok(fb), Ok(uc), Ok(fc)) = (up_b, fk_b, up_c, fk_c) else {
        return;
    };
    assert_eq!(ub, fb, "batchable proofs differ");
    assert_eq!(uc, fc, "compact proofs differ");

    let verify_b = |bytes: &[u8]| {
        let u = up::verify_batchable_with::<DefaultHash, UInstance<G>>(&sid, ui, bytes);
        let f = ffs::verify_batchable_with::<DefaultHash, fk::Instance>(&sid, fi, bytes);
        same_verdict("verify_batchable", &u, &f);
        u.is_ok()
    };
    let verify_c = |bytes: &[u8]| {
        let u = up::verify_compact_with::<DefaultHash, UInstance<G>>(&sid, ui, bytes);
        let f = ffs::verify_compact_with::<DefaultHash, fk::Instance>(&sid, fi, bytes);
        same_verdict("verify_compact", &u, &f);
        u.is_ok()
    };
    let valid = bool::from(ui.is_witness_valid(witness));
    assert_eq!(verify_b(&ub), valid);
    assert_eq!(verify_c(&uc), valid);
    let verifiers: [(&Vec<u8>, &dyn Fn(&[u8]) -> bool); 2] = [(&ub, &verify_b), (&uc, &verify_c)];
    for (proof, verify) in verifiers {
        for pos in (0..proof.len()).step_by(11) {
            let mut t = proof.clone();
            t[pos] ^= 1 << (pos % 8);
            verify(&t);
        }
        if !proof.is_empty() {
            verify(&proof[..proof.len() - 1]);
        }
        let mut long = proof.clone();
        long.push(0);
        verify(&long);
    }
    // Another session.
    let other = up::derive_session_id::<DefaultHash>(b"another session");
    assert_eq!(
        up::verify_batchable_with::<DefaultHash, UInstance<G>>(&other, ui, &ub).is_ok(),
        ffs::verify_batchable_with::<DefaultHash, fk::Instance>(&other, fi, &ub).is_ok()
    );
}

fn run_named(name: &str, build: fn(&mut Rng) -> RelSpec, rounds: u64) {
    for seed in 0..rounds {
        let mut r = rng(seed, 0);
        let spec = build(&mut r);
        let witness = sample_vec(&mut r, spec.num_scalars);
        let (ui, fi) = compile_both_ok(&spec, &witness);
        assert!(
            protocol_both(&ui, &fi, &witness, seed),
            "{name}: honest proof rejected"
        );
        narg_both(&ui, &fi, &witness, seed);

        // A wrong witness: the same image, another witness.
        let wrong = sample_vec(&mut r, spec.num_scalars);
        assert!(
            !protocol_both(&ui, &fi, &wrong, seed + 1000),
            "{name}: wrong witness accepted"
        );
        narg_both(&ui, &fi, &wrong, seed + 1000);

        // Witnesses of the wrong length.
        protocol_both(&ui, &fi, &witness[..witness.len() - 1], seed);
        let mut long = witness.clone();
        long.push(S::ONE);
        protocol_both(&ui, &fi, &long, seed);
        assert!(matches!(compile_both(&spec, &long), Compiled::Neither));
    }
}

#[test]
fn dlog_agrees() {
    run_named("dlog", dlog, 6);
}

#[test]
fn dleq_agrees() {
    run_named("DLEQ", dleq, 6);
}

#[test]
fn pedersen_agrees() {
    run_named("Pedersen", pedersen, 6);
}

#[test]
fn three_equations_agree() {
    run_named("three equations", three_equations, 6);
}

#[test]
fn random_relations_agree() {
    let mut compiled = 0;
    let mut only_upstream = 0;
    for seed in 0..200u64 {
        let mut r = rng(seed, 7);
        let n = small(&mut r, 4) as usize;
        let witness = sample_vec(&mut r, n);
        let spec = random_relation(&mut r, &witness);
        match compile_both(&spec, &witness) {
            Compiled::Both(ui, fi) => {
                compiled += 1;
                let honest = protocol_both(&ui, &fi, &witness, seed);
                assert_eq!(honest, bool::from(ui.is_witness_valid(&witness)));
                if seed % 4 == 0 {
                    narg_both(&ui, &fi, &witness, seed);
                }
            }
            Compiled::OnlyUpstream(..) => only_upstream += 1,
            Compiled::Neither => {}
        }
    }
    report_draft03_rejections("random relations");
    eprintln!("random relations: {compiled} compiled on both sides, {only_upstream} on upstream only");
    assert!(
        compiled > 20,
        "too few random relations compiled: {compiled}"
    );
    assert!(only_upstream > 5, "too few draft-03 rejections: {only_upstream}");
}

/// The draft-03 check the fork fails on `spec`, which upstream compiles.
fn only_upstream_check(spec: &RelSpec, witness: &[S]) -> u8 {
    match compile_both(spec, witness) {
        Compiled::OnlyUpstream(check) => check,
        Compiled::Both(..) => panic!("both sides compile"),
        Compiled::Neither => panic!("neither side compiles"),
    }
}

#[test]
fn relation_errors_agree() {
    let mut r = rng(99, 0);
    // A term over an unassigned element.
    let spec = RelSpec {
        num_scalars: 1,
        bases: vec![point(&mut r)],
        extra: 1,
        equations: vec![EqSpec {
            lhs: None,
            terms: vec![(Sc::Var(0), 3, S::ONE)],
        }],
    };
    assert!(matches!(compile_both(&spec, &[sample(&mut r)]), Compiled::Neither));
    // A preassigned image the witness does not meet.
    let spec = RelSpec {
        num_scalars: 1,
        bases: vec![],
        extra: 0,
        equations: vec![EqSpec {
            lhs: Some(point(&mut r)),
            terms: vec![(Sc::Var(0), 1, S::ONE)],
        }],
    };
    assert!(matches!(compile_both(&spec, &[sample(&mut r)]), Compiled::Neither));
    // The empty relation: draft-03 check 1.
    let spec = RelSpec {
        num_scalars: 0,
        bases: vec![],
        extra: 0,
        equations: vec![],
    };
    assert_eq!(only_upstream_check(&spec, &[]), 1);
    // An equation with no witness terms: draft-03 check 2 when the equation
    // holds; neither side compiles when it does not.
    let g = point(&mut r);
    let h = point(&mut r);
    for (lhs, holds) in [(g, true), (h, false)] {
        let spec = RelSpec {
            num_scalars: 1,
            bases: vec![g],
            extra: 0,
            equations: vec![
                EqSpec {
                    lhs: None,
                    terms: vec![(Sc::Var(0), 1, S::ONE)],
                },
                EqSpec {
                    lhs: Some(lhs),
                    terms: vec![(Sc::Unit, 2, S::ONE)],
                },
            ],
        };
        let w = [sample(&mut r)];
        if holds {
            assert_eq!(only_upstream_check(&spec, &w), 2);
        } else {
            assert!(matches!(compile_both(&spec, &w), Compiled::Neither));
        }
    }
    // A scalar that no term carries, below the largest one: draft-03 check 6.
    let spec = RelSpec {
        num_scalars: 2,
        bases: vec![],
        extra: 0,
        equations: vec![EqSpec {
            lhs: None,
            terms: vec![(Sc::Var(1), 1, S::ONE)],
        }],
    };
    assert_eq!(only_upstream_check(&spec, &sample_vec(&mut r, 2)), 6);
    // A term over the identity: draft-03 check 8.
    let spec = RelSpec {
        num_scalars: 1,
        bases: vec![],
        extra: 0,
        equations: vec![EqSpec {
            lhs: None,
            terms: vec![(Sc::Var(0), 1, S::ONE), (Sc::Var(0), 0, S::ONE)],
        }],
    };
    assert_eq!(only_upstream_check(&spec, &[sample(&mut r)]), 8);
    // An image that is the identity: X = x * G + H with x = 0 compiles to the
    // image X - H, and X = H; no element is the identity. Draft-03 check 9.
    let spec = RelSpec {
        num_scalars: 1,
        bases: vec![point(&mut r)],
        extra: 0,
        equations: vec![EqSpec {
            lhs: None,
            terms: vec![(Sc::Var(0), 1, S::ONE), (Sc::Unit, 2, S::ONE)],
        }],
    };
    assert_eq!(only_upstream_check(&spec, &[S::ZERO]), 9);
    // A column of the linear map that is the identity (x * G - x * G):
    // draft-03 check 10.
    let spec = RelSpec {
        num_scalars: 2,
        bases: vec![point(&mut r)],
        extra: 0,
        equations: vec![EqSpec {
            lhs: None,
            terms: vec![
                (Sc::Var(0), 1, S::ONE),
                (Sc::Var(0), 1, -S::ONE),
                (Sc::Var(1), 2, S::ONE),
            ],
        }],
    };
    assert_eq!(only_upstream_check(&spec, &sample_vec(&mut r, 2)), 10);
    let tally = report_draft03_rejections("relation errors");
    assert_eq!(tally.keys().copied().collect::<Vec<u8>>(), vec![1, 2, 6, 8, 9, 10]);
}

// ---------------------------------------------------------------------------
// ValidateInstance on raw instances
// ---------------------------------------------------------------------------

/// Random raw instances in upstream's indexing (0 the identity, 1 the
/// generator, the statement elements from 2), given to upstream's
/// `Instance::new` and, through the index shift, to the fork's. Most indices
/// are those of the generator and the statement elements; one in sixteen is
/// the identity slot and one in sixteen is out of range, and one list in ten
/// is empty.
#[test]
fn validate_instance_agrees() {
    let mut both = 0;
    let mut only_upstream = 0;
    let mut upstream_checks = [0usize; 4];
    for seed in 0..400u64 {
        let mut r = rng(seed, 8);
        let ne = small(&mut r, 4) as usize;
        let elements: Vec<G> = (0..ne).map(|_| point(&mut r)).collect();
        let neq = if small(&mut r, 16) == 0 {
            0
        } else {
            1 + small(&mut r, 3) as usize
        };
        let index = |r: &mut Rng| -> u32 {
            match small(r, 16) {
                0 => 0,
                1 => (ne + 2) as u32,
                _ => 1 + small(r, (ne + 1) as u64) as u32,
            }
        };
        let mut equations = Vec::new();
        for _ in 0..neq {
            let ni = if small(&mut r, 10) == 0 {
                0
            } else {
                1 + small(&mut r, 2) as usize
            };
            let nt = if small(&mut r, 10) == 0 {
                0
            } else {
                1 + small(&mut r, 3) as usize
            };
            let mut image: Vec<(u32, S)> = Vec::new();
            for _ in 0..ni {
                let e = index(&mut r);
                image.push((e, sample(&mut r)));
            }
            let mut terms: Vec<(u32, u32, S)> = Vec::new();
            for _ in 0..nt {
                let s = small(&mut r, 3) as u32;
                let e = index(&mut r);
                terms.push((s, e, sample(&mut r)));
            }
            equations.push((image, terms));
        }
        let ueqs: Vec<UEquation<G>> = equations
            .iter()
            .map(|(i, t)| UEquation {
                image: i.clone(),
                terms: t.clone(),
            })
            .collect();
        let feqs: Vec<fk::Equation> = equations
            .iter()
            .map(|(i, t)| fk::Equation {
                image: i.iter().map(|&(e, c)| (e, encode_scalar(&c))).collect(),
                terms: t
                    .iter()
                    .map(|&(s, e, c)| (s, e, encode_scalar(&c)))
                    .collect(),
            })
            .collect();
        let u = UInstance::new(elements.clone(), ueqs);
        let f = core_equations(InstanceFormat::ImplicitIdentity, &feqs)
            .and_then(|core| fk::Instance::new::<R>(ee(&elements), core));
        let context = format!("seed {seed}");
        match (u, f) {
            (Ok(ui), Ok(fi)) => {
                both += 1;
                assert_same_instance(&ui, &fi);
                let w = sample_vec(&mut r, ui.num_scalars());
                protocol_both(&ui, &fi, &w, seed);
            }
            (Ok(_), Err(fe)) => {
                only_upstream += 1;
                draft03_rejection(&context, fe.check);
            }
            (Err(ue), Err(fe)) => {
                upstream_checks[ue.check.unwrap_or(0) as usize] += 1;
                both_reject(&context, ue.check, fe.check);
            }
            (Err(_), Ok(_)) => panic!("{context}: the fork accepts what upstream rejects"),
        }
    }
    let tally = report_draft03_rejections("raw instances");
    eprintln!(
        "raw instances: {both} valid on both sides, {only_upstream} on upstream only, \
         upstream failures by check {upstream_checks:?}"
    );
    // Every outcome occurs: valid on both sides, upstream's checks 2 and 3,
    // and draft-03 rejections by checks 1, 2, 6 and 8.
    assert!(both > 15, "too few valid instances: {both}");
    assert!(upstream_checks[2] > 0 && upstream_checks[3] > 0, "{upstream_checks:?}");
    for check in [1, 2, 6, 8] {
        assert!(tally.contains_key(&check), "no draft-03 rejection by check {check}");
    }
    // Check 7, which no instance built by `Instance::new` fails: element 0
    // is not the generator.
    let x = encode_element(&point(&mut rng(400, 8)));
    let equation = fk::Equation {
        image: vec![(1, encode_scalar(&S::ONE))],
        terms: vec![(0, 0, encode_scalar(&S::ONE))],
    };
    assert_eq!(
        fk::instance::validate::<R>(&[x, x], &[equation]),
        Err(fk::InvalidInstance { check: Some(7) })
    );
}

// ---------------------------------------------------------------------------
// AND composition
// ---------------------------------------------------------------------------

/// An upstream AND tree, its fork tree, and the witness of each.
struct AndCase {
    upstream: ComposedInstance<G>,
    witness: ComposedWitness<G>,
    tree: AndTree,
    leaves: Vec<Vec<S>>,
}

fn leaf(spec: &RelSpec, witness: Vec<S>) -> AndCase {
    let (ui, fi) = compile_both_ok(spec, &witness);
    AndCase {
        upstream: ComposedInstance::from(ui),
        witness: ComposedWitness::Simple(witness.clone()),
        tree: AndTree::Simple(fi),
        leaves: vec![witness],
    }
}

fn and(cases: Vec<AndCase>) -> AndCase {
    let mut upstream = Vec::new();
    let mut witness = Vec::new();
    let mut tree = Vec::new();
    let mut leaves = Vec::new();
    for c in cases {
        upstream.push(c.upstream);
        witness.push(c.witness);
        tree.push(c.tree);
        leaves.extend(c.leaves);
    }
    AndCase {
        upstream: ComposedInstance::and(upstream).expect("AND"),
        witness: ComposedWitness::and(witness),
        tree: AndTree::And(tree),
        leaves,
    }
}

fn flatten_commitment(c: &ComposedCommitment<G>, out: &mut Vec<Vec<fk::Element>>) {
    match c {
        ComposedCommitment::Simple(v) => out.push(ee(v)),
        ComposedCommitment::Branches(bs) => bs.iter().for_each(|b| flatten_commitment(b, out)),
        ComposedCommitment::Claim(_) => panic!("no claims here"),
    }
}

fn flatten_response(r: &ComposedResponse<G>, out: &mut Vec<Vec<fk::Scalar>>) {
    match r {
        ComposedResponse::Simple(v) => out.push(es(v)),
        ComposedResponse::And(bs) => bs.iter().for_each(|b| flatten_response(b, out)),
        _ => panic!("AND trees only"),
    }
}

fn and_both(case: &AndCase, seed: u64, expect_valid: bool) {
    let flat = case.tree.flatten();
    let fw = fk::AndWitness {
        branches: case.leaves.iter().map(|w| es(w)).collect(),
    };
    assert_eq!(flat.is_witness_valid::<R>(&fw), expect_valid);

    // Commitment and response from the same nonces.
    let (uc, ust) = case
        .upstream
        .prover_commit(&case.witness, &mut rng(seed, 1))
        .expect("upstream commit");
    let mut fr = rng(seed, 1);
    let nonces = fk::AndWitness {
        branches: ffs::sample_per_leaf(&flat, &mut fr),
    };
    let (fc, fst) = flat.prover_commit::<R>(&fw, &nonces).expect("fork commit");
    let mut ucf = Vec::new();
    flatten_commitment(&uc, &mut ucf);
    assert_eq!(ucf, fc.branches, "AND commitments differ");
    let challenge = sample(&mut rng(seed, 2));
    let fch = encode_scalar(&challenge);
    let ur = case
        .upstream
        .prover_response(ust, &challenge)
        .expect("upstream response");
    let fres = flat
        .prover_response::<R>(&fst, &fch)
        .expect("fork response");
    let mut urf = Vec::new();
    flatten_response(&ur, &mut urf);
    assert_eq!(urf, fres.branches, "AND responses differ");
    let uv = case.upstream.verifier(&uc, &challenge, &ur);
    let fv = flat.verifier::<R>(&fc, &fch, &fres);
    same_verdict("AND verifier", &uv, &fv);
    assert_eq!(fv.is_ok(), expect_valid);
    let randomness = encode_scalar(&sample(&mut rng(seed, 9)));
    same_verdict(
        "AND batchable verifier",
        &uv,
        &flat.verifier_with_randomness::<R>(&fc, &fch, &fres, &randomness),
    );
    // Tamper with each response branch.
    for b in 0..fres.branches.len() {
        if fres.branches[b].is_empty() {
            continue;
        }
        let mut ft = fres.clone();
        ft.branches[b][0] = encode_scalar(&(decode_scalar(&ft.branches[b][0]).unwrap() + S::ONE));
        assert!(flat.verifier::<R>(&fc, &fch, &ft).is_err());
    }
    // Wrong shapes.
    if !fw.branches.is_empty() {
        let mut short = fw.clone();
        short.branches.pop();
        assert!(flat.prover_commit::<R>(&short, &nonces).is_err());
    }

    // Simulator.
    let (sc, sch, sr) = case
        .upstream
        .simulate_transcript(&mut rng(seed, 3))
        .expect("upstream simulation");
    let mut fs = rng(seed, 3);
    let srand = fk::AndResponse {
        branches: ffs::sample_per_leaf(&flat, &mut fs),
    };
    let sch_f = encode_scalar(&sample(&mut fs));
    let (fsc, fsch, fsr) = flat
        .simulate_transcript::<R>(&srand, &sch_f)
        .expect("fork simulation");
    let mut scf = Vec::new();
    flatten_commitment(&sc, &mut scf);
    let mut srf = Vec::new();
    flatten_response(&sr, &mut srf);
    assert_eq!(scf, fsc.branches, "AND simulated commitments differ");
    assert_eq!(encode_scalar(&sch), fsch);
    assert_eq!(srf, fsr.branches, "AND simulated responses differ");
    assert!(flat.verifier::<R>(&fsc, &fsch, &fsr).is_ok());

    // NARG strings, with the tree in the instance label.
    let sid = up::derive_session_id::<DefaultHash>(b"sigma-proofs-hax AND");
    let ub = up::prove_batchable_with::<DefaultHash, ComposedInstance<G>>(
        &sid,
        &case.upstream,
        &case.witness,
        &mut rng(seed, 4),
    )
    .expect("upstream batchable");
    let fb = ffs::prove_batchable_with::<DefaultHash, DefaultHash, AndTree>(
        &sid,
        &case.tree,
        &fw,
        &mut rng(seed, 4),
    )
    .expect("fork batchable");
    assert_eq!(ub, fb, "AND batchable proofs differ");
    let uc = up::prove_compact_with::<DefaultHash, ComposedInstance<G>>(
        &sid,
        &case.upstream,
        &case.witness,
        &mut rng(seed, 5),
    )
    .expect("upstream compact");
    let fcp = ffs::prove_compact_with::<DefaultHash, DefaultHash, AndTree>(
        &sid,
        &case.tree,
        &fw,
        &mut rng(seed, 5),
    )
    .expect("fork compact");
    assert_eq!(uc, fcp, "AND compact proofs differ");
    for (proof, compact) in [(&ub, false), (&uc, true)] {
        let mut variants = vec![proof.clone()];
        for pos in (0..proof.len()).step_by(13) {
            let mut t = proof.clone();
            t[pos] ^= 1;
            variants.push(t);
        }
        for t in variants {
            let (u, f) = if compact {
                (
                    up::verify_compact_with::<DefaultHash, ComposedInstance<G>>(
                        &sid,
                        &case.upstream,
                        &t,
                    )
                    .is_ok(),
                    ffs::verify_compact_with::<DefaultHash, AndTree>(&sid, &case.tree, &t).is_ok(),
                )
            } else {
                (
                    up::verify_batchable_with::<DefaultHash, ComposedInstance<G>>(
                        &sid,
                        &case.upstream,
                        &t,
                    )
                    .is_ok(),
                    ffs::verify_batchable_with::<DefaultHash, AndTree>(&sid, &case.tree, &t)
                        .is_ok(),
                )
            };
            assert_eq!(u, f, "AND NARG verdicts differ");
        }
    }
}

#[test]
fn and_composition_agrees() {
    for seed in 0..3u64 {
        let mut r = rng(seed, 10);
        let specs = [
            dlog(&mut r),
            dleq(&mut r),
            pedersen(&mut r),
            three_equations(&mut r),
        ];
        let ws: Vec<Vec<S>> = specs
            .iter()
            .map(|s| sample_vec(&mut r, s.num_scalars))
            .collect();
        let l = |i: usize| leaf(&specs[i], ws[i].clone());

        and_both(&and(vec![l(0), l(1)]), seed, true);
        and_both(
            &and(vec![l(2), and(vec![l(3), l(0)]), l(1)]),
            seed + 10,
            true,
        );
        and_both(&and(vec![]), seed + 20, true);
        and_both(&l(3), seed + 30, true);

        // A branch whose witness does not satisfy it: compiled with the
        // right witness, proved with another.
        let mut bad = l(1);
        let wrong = sample_vec(&mut r, 1);
        bad.witness = ComposedWitness::Simple(wrong.clone());
        bad.leaves = vec![wrong];
        and_both(&and(vec![l(0), bad]), seed + 40, false);
    }
}
