# sigma-proofs-hax

A fork of [`sigma-proofs`](https://github.com/sigma-rs/sigma-proofs) 0.4.1, the Rust
implementation of the IRTF CFRG drafts
[draft-irtf-cfrg-sigma-protocols-03](https://datatracker.ietf.org/doc/draft-irtf-cfrg-sigma-protocols/)
and [draft-irtf-cfrg-fiat-shamir-03](https://datatracker.ietf.org/doc/draft-irtf-cfrg-fiat-shamir/),
rewritten so that [hax](https://github.com/cryspen/hax) extracts its Σ-protocol core to Lean 4.
[CatCrypt-core](https://github.com/spitters/CatCrypt-core) proves that the extracted core is the
Σ-protocol for linear relations that the draft specifies, and proves that protocol and its
Fiat–Shamir transforms secure with concrete bounds.

## Changes from upstream 0.4.1

- The instance representation and validation of draft-03, Section 3: the generator is element 0
  of every instance and there is no identity slot, `instance::validate` runs the ten checks of
  `ValidateInstance`, and the element codec rejects the identity. Upstream 0.4.1 places the
  identity and the generator at element indices 0 and 1 and runs three of the checks;
  `wire::InstanceFormat` converts between the two instance encodings.
- The extracted core is written in the subset of Rust that hax translates. Scalars and group
  elements are 32-byte encodings; every group and field operation is an associated function of
  the trait `SigmaGroup`, including the multi-scalar multiplications `msm` (constant time in the
  scalars, used by the prover) and `msm_vartime` (public scalars: verifier, simulator, statement
  image); prover nonces and simulator randomness are inputs; a function returns the updated value
  where upstream mutates through `&mut`; loops are index loops.
- The module `fixed` holds Schnorr and DLEQ provers, simulators and verifiers of fixed shape:
  64-bit limb arrays for scalars and elements, and status words (0 accepts) for verdicts, for
  compilation by a compiler whose front accepts fixed-size arrays of machine words.
- The Fiat–Shamir layer (`fiat_shamir`, on the duplex sponge of
  [`spongefish`](https://crates.io/crates/spongefish)), the wire codecs (`wire`) and the
  ristretto255 instance of `SigmaGroup` (`ristretto`, on
  [curve25519-dalek](https://crates.io/crates/curve25519-dalek), with Straus multi-scalar
  multiplication and the basepoint table) are compiled outside the hax view (`cfg(not(hax))`).

## Tests

`cargo test` runs three suites.

- `tests/draft_vectors.rs`: the test vectors of draft-03, Appendix A (SHAKE128 over P-256 and
  BLS12-381 G1, batchable and compact proofs, valid and adversarial instances), and the vectors
  that upstream 0.4.1 vendors. For each valid vector the prover reproduces the proof byte for
  byte and the verifier accepts it; each adversarial vector is rejected or accepted as the vector
  states, except the upstream vectors that only upstream's three checks accept, which the fork
  rejects as draft-03 does.
- `tests/differential.rs`: the fork against the unmodified upstream 0.4.1 over ristretto255, on
  the same relations and nonces. Encodings, commitments, responses, simulated transcripts and
  proof strings agree, and so do the verdicts on correct, tampered and truncated proofs; an input
  that only upstream accepts must fail a draft-03 check that upstream does not run.
- `tests/fixed.rs`: the fixed-shape functions against the generic core on random inputs.

## What is proved

The [SigmaProtocol README of CatCrypt-core](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Crypto/SigmaProtocol/README.md)
states the theorems. The extraction of this crate is
[`SigmaProofs_haxpipe`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Crypto/SigmaProtocol/Extraction/SigmaProofs_haxpipe.lean),
translated to Lean by [hax-lean](https://github.com/spitters/hax-lean).

- With the group operations interpreted at ristretto255, the extracted prover, verifier,
  simulator and compact check are the components of the Σ-protocol `linearSigma`
  ([`extSigma_eq`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Crypto/SigmaProtocol/SurfaceDeps.lean)).
  Completeness, special soundness, perfect honest-verifier zero knowledge and the Fiat–Shamir
  knowledge-soundness and zero-knowledge bounds therefore hold for the extracted code.
- The extracted validation accepts exactly the instances that satisfy the ten checks of draft-03,
  Section 3.5, for equations with one image term and unit coefficients
  ([`Instance_new_ok_iff`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Crypto/SigmaProtocol/SurfaceDeps.lean)).
- The extracted batched verifier accepts a proof that the per-equation verifier rejects with
  probability at most (m−1)/|scalars| for m equations
  ([`batch_accept_prob_le`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Crypto/SigmaProtocol/SigmaProofsBatchAnd.lean)).
- The fixed-shape Schnorr and DLEQ functions are `linearSigma` on the discrete-logarithm and DLEQ
  relations
  ([`fixedSchnorrSigma_eq`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Crypto/SigmaProtocol/FixedShape.lean),
  [`fixedDleqSigma_eq`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Crypto/SigmaProtocol/FixedShape.lean)).

## Licence

MIT OR Apache-2.0, as upstream ([LICENSE-MIT](LICENSE-MIT), [LICENSE-APACHE](LICENSE-APACHE)).
Upstream `sigma-proofs` is by Nugzari Uzoevi, Michele Orrù, Ian Goldberg, Victor Snyder-Graf and
Lénaïck Gouriou. The vectors under `tests/vectors/` are taken from draft-03, Appendix A, and from
upstream 0.4.1.
