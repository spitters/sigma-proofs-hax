//! The group kernels against their reference definitions, on random inputs.
//!
//! - `msm_rows_vartime` of the Ristretto255 instance and of the P-256 and
//!   BLS12-381 G1 test groups (`tests/curves`): one entry per row, equal to
//!   `msm_vartime` of the row, to `msm_reference` (term by term) and to
//!   `msm_rows_reference`. The rows share bases, repeat bases, include the
//!   generator and empty rows, and some carry a base beyond their scalars
//!   that is not a valid element, which the kernel must not read.
//! - The Ristretto255 `identity`, `generator` and `group_eq`, which work on
//!   encodings: the encodings of the `curve25519-dalek` identity and
//!   basepoint, and equality of the decoded points, on elements computed
//!   along different paths.

mod curves;

use curve25519_dalek::constants::RISTRETTO_BASEPOINT_POINT;
use curve25519_dalek::ristretto::RistrettoPoint;
use curve25519_dalek::traits::Identity;
use spongefish::{derive_session_id, instantiations::Shake128, PrivateRng};

use curves::{Bls12381, P256};
use sigma_proofs_hax as fk;
use fk::fiat_shamir as ffs;
use fk::msm::{msm_reference, msm_rows_reference};
use fk::ristretto::{decode_element, encode_element, Ristretto255 as R};
use fk::wire::GroupWire;
use fk::{Element, Scalar, SigmaGroup};

type Drng = PrivateRng<Shake128>;

/// A base that no kernel may read: not a Ristretto encoding, and a handle
/// past the end of the tables of the test groups.
const UNREAD: Element = [0xff; 32];

fn rng(tag: &str) -> Drng {
    PrivateRng::from_seed(*derive_session_id::<Shake128>(tag.as_bytes()).as_bytes())
}

fn scalar<W: GroupWire>(rng: &mut Drng) -> Scalar {
    ffs::sample_scalar_of::<W, Shake128>(rng)
}

/// An index below `bound`.
fn index(rng: &mut Drng, bound: usize) -> usize {
    let mut bytes = [0u8; 8];
    rng.fill_bytes(&mut bytes);
    (u64::from_le_bytes(bytes) % bound as u64) as usize
}

/// A random multiple of the generator.
fn element<W: GroupWire>(rng: &mut Drng) -> Element {
    W::group_mul(&scalar::<W>(rng), &W::generator())
}

/// `num_rows` rows of 0 to 5 terms whose bases are drawn from a pool of
/// `pool` elements, the generator first; a third of the rows end with the
/// base [`UNREAD`] beyond their scalars.
fn random_rows<W: GroupWire>(
    rng: &mut Drng,
    num_rows: usize,
    pool: usize,
) -> Vec<(Vec<Scalar>, Vec<Element>)> {
    let mut elements = vec![W::generator()];
    for _ in 1..pool {
        elements.push(element::<W>(rng));
    }
    let mut rows = Vec::new();
    for _ in 0..num_rows {
        let terms = index(rng, 6);
        let mut scalars = Vec::new();
        let mut bases = Vec::new();
        for _ in 0..terms {
            scalars.push(scalar::<W>(rng));
            bases.push(elements[index(rng, pool)]);
        }
        if index(rng, 3) == 0 {
            bases.push(UNREAD);
        }
        rows.push((scalars, bases));
    }
    rows
}

fn check_msm_rows<W: GroupWire>(name: &str) {
    assert!(W::msm_rows_vartime(&[]).is_empty(), "{name}: no rows");
    let mut r = rng(&format!("sigma-proofs-hax kernels msm_rows_vartime {name}"));
    for trial in 0..20 {
        let num_rows = 1 + index(&mut r, 8);
        let pool = 1 + index(&mut r, 6);
        let rows = random_rows::<W>(&mut r, num_rows, pool);
        let values = W::msm_rows_vartime(&rows);
        assert_eq!(values.len(), rows.len(), "{name}, trial {trial}: one entry per row");
        for (j, (scalars, bases)) in rows.iter().enumerate() {
            assert_eq!(
                values[j],
                W::msm_vartime(scalars, bases),
                "{name}, trial {trial}, row {j}: msm_vartime of the row"
            );
            assert_eq!(
                values[j],
                msm_reference::<W>(scalars, bases),
                "{name}, trial {trial}, row {j}: the row term by term"
            );
        }
        assert_eq!(
            values,
            msm_rows_reference::<W>(&rows),
            "{name}, trial {trial}: msm_rows_reference"
        );
    }
}

#[test]
fn msm_rows_vartime_ristretto255() {
    check_msm_rows::<R>("ristretto255");
}

#[test]
fn msm_rows_vartime_p256() {
    check_msm_rows::<P256>("P-256");
}

#[test]
fn msm_rows_vartime_bls12381() {
    check_msm_rows::<Bls12381>("BLS12-381 G1");
}

#[test]
fn ristretto255_encoding_operations() {
    assert_eq!(R::identity(), encode_element(&RistrettoPoint::identity()));
    assert_eq!(R::generator(), encode_element(&RISTRETTO_BASEPOINT_POINT));
    let g = R::generator();
    let mut r = rng("sigma-proofs-hax kernels group_eq");
    for trial in 0..20 {
        let x = scalar::<R>(&mut r);
        let y = scalar::<R>(&mut r);
        // x G + y G and (x + y) G: one element along two paths.
        let a = R::group_add(&R::group_mul(&x, &g), &R::group_mul(&y, &g));
        let b = R::group_mul(&R::scalar_add(&x, &y), &g);
        let c = R::group_mul(&x, &g);
        // x G + (-x) G: the identity.
        let zero = R::group_add(&c, &R::group_mul(&R::scalar_neg(&x), &g));
        assert!(R::group_eq(&a, &b), "trial {trial}: x G + y G = (x + y) G");
        assert!(R::group_eq(&zero, &R::identity()), "trial {trial}: x G - x G = 0");
        for (u, v) in [(a, b), (a, c), (b, c), (c, c), (c, g), (zero, R::identity()), (a, zero)] {
            let points_equal = decode_element(&u).unwrap() == decode_element(&v).unwrap();
            assert_eq!(R::group_eq(&u, &v), points_equal, "trial {trial}");
        }
    }
}
