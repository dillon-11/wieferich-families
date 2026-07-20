# Wieferich phenomena of algebraic units

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.21456694.svg)](https://doi.org/10.5281/zenodo.21456694)

To every algebraic unit α is attached a Wieferich locus: the set of primes
p at which the Frobenius trace congruence Tr(α^p) ≡ Tr(α) holds mod p²
rather than merely mod p (for rational units: the classical condition that
the multiplicative order does not grow from p to p²). The
classical Wieferich condition (`p² | 2^(p−1) − 1`), the Wall–Sun–Sun
condition, the Perrin-square condition, and Gold's criterion for the
Iwasawa invariant λ_p(K) > 1 of an imaginary quadratic field are
specializations of one theorem, the order-lift dichotomy. This repository
contains the paper, the census data, the search kernels, and the Lean 4
formalization.

Results reported in the paper:

- Censuses of thirteen unit loci to 10⁹ — extended to 10¹⁰ for Lehmer's
  unit — including the first computation for any Salem number: the locus
  of Lehmer's unit contains p = 720847 and nothing else below 10¹⁰; two
  further Salem loci contain 144479 and 4674101.
- A 47-field census of Gold's condition to 10⁹ — four orders of magnitude
  past the tabulated range of Dummit–Ford–Kisilevsky–Sands (1991) — with
  the records 330017383 (ℚ(√−67)) and 346527893 (ℚ(√−52)), each an
  unconditional witness of λ_p(K) > 1, detected by a closed form costing
  two modular multiplications.
- A λ ≥ 3 determination through the Massey-product criterion rather than
  a p-adic L-function: λ₅(ℚ(√−11)) = 2 exactly, by one norm equation in
  the first tower layer (`scripts/massey_rung_lambda3.gp`).
- An exact determination of the depth-≥3 stratum of the family
  x² − kx − 1, k ≤ 1000: 66 members, local law, unique Hensel lifting —
  and the exact Iwasawa linearity of the depth grading along the tower
  (λ = 1, μ = 0, ν = the Wieferich depth), with deterministic members
  of every depth d ≥ 3.
- A localization theorem — squared primes in cyclotomic values Φ_n(α) are
  order-lift failures at index n — and the graded prime towers it yields.
- Closed-form Aurifeuillian factorizations of the towers' composite
  levels, the associated half-prime families with N−1 certificates
  assembled from the construction (192 and 258 digits), and fifteen new
  primes of the Pell and x² − 3x − 1 towers, 175–1173 digits, each with
  an APR-CL certificate.
- Trace returns force torsion: a non-torsion unit has finitely many
  integer trace returns, and across 1,436 Salem polynomials the observed
  window follows an exact two-parameter law (Mahler measure and circle
  load). Lehmer's polynomial is the unique long-window member with zero
  returns in the census.
- An exact discriminant identity for reciprocal polynomials,
  d_P = (−1)^d·P(1)·P(−1)·d_T², and a fully native class-number
  certificate for Lehmer's polynomial: h = 1 for both the degree-10
  field and its trace field, unit index 4.
- The Wilson integral of the family: the section-carry total of the root
  pairing a ↔ ∓a⁻¹ of x² − kx ∓ 1 reads the Wilson quotient through the
  norm character of the family — Lerch's congruence in involuted form,
  exact at every odd prime tested (`scripts/lerch_wilson_carry.py`).

## Repository layout

| Path | Contents |
| --- | --- |
| [`source.md`](source.md) | the paper |
| [`PROVENANCE.md`](PROVENANCE.md) | verification layers, preregistration protocol, kernel-defect disclosures, re-verification commands |
| [`WieferichFamilies/`](WieferichFamilies/) | the Lean 4 formalization (Mathlib-only; see below) |
| [`scripts/`](scripts/) | census kernels (C, 128-bit modular arithmetic) and regeneration scripts |
| [`data/`](data/) | member tables: unit loci, Gold atlas, depth-≥3 members |
| [`data/half_primes.tsv`](data/half_primes.tsv) | the Aurifeuillian half-prime family, odd m ≤ 1000 |
| [`data/tower_primes/`](data/tower_primes/) | the fifteen new primes of §3.4 with APR-CL status and factordb identifiers |
| [`data/certified_zone/`](data/certified_zone/) | N−1 certificates, including the 192- and 258-digit half-primes |

## The Lean formalization

Twenty-eight modules under the `Wieferich` namespace, importing only
Mathlib. The layers:

- **Mechanism** — `LiftDichotomy` (the order-lift dichotomy and its
  instantiation for the reduction of any order), `HigherOrder` (the
  depth-≥3 algebra and the nine depth-4 certificates), `Exclusions`
  (the classification of empty census classes, the exact local counts,
  the collapse factorization, and the torsion grade — one module),
  `DepthTransfer`, `TraceReturns` (trace returns force torsion),
  `Dobrowolski` + `DobrowolskiBaseline` (the resultant valuation reads
  Wieferich depth; the baseline `q^{deg P} ∣ Res(P, P∘X^q)` proved in
  general via the Frobenius factorization), `PierceValues` (the
  two-sided bound `1 ≤ ∏‖αᵐ−1‖ ≤ 2^d·Mᵐ` on the Pierce–Lehmer
  sequence), `MetallicRegulator` (`M(x² − kx − 1)` equals the
  fundamental unit; the golden floor at degree 2), `ZsygmondyLTE` (the
  Birkhoff–Vandiver bound and the Zsygmondy reduction),
  `LocusDisjointness`.
- **Certificates** — `PowerLadder` (O(log p) certificates; 489061 in 19
  steps, 6811741 in 23), `RecordCertificates` (330017383, 346527893),
  `AtlasCertificates` (the members above 10⁷), `LehmerCertificate`
  (720847 at the degree-10 companion matrix).
- **Gold / Iwasawa** — `GoldCriterion` (the closed form of the unit-root
  condition), `GoldScope` (the census flag equals Gold's flag at every
  h ≤ 5), `LambdaLadder`, `IwasawaGrid`, `BernoulliAnchors`
  (Glaisher, Wolstenholme, `1093² | 2¹⁰⁹² − 1`), `PierpontSmoothness`,
  `ClassNumberOne`, `ClassGroupStructure`, `PisotClassFields`,
  `PlasticAnchor` (Hilbert class fields of the h = 3 fields are
  generated by Pisot units).
- **Construct-and-certify** — `CertifiedZone` (factor floor + size bound
  ⟹ prime; the Aurifeuillian seam), `SearchCost` (the cost model of the
  sieve-and-certify pipeline, with correctness of the output as a
  conjunct).

Companion repositories:
[`lehmer-e10`](https://github.com/dillon-11/lehmer-E10) (irreducibility
of Lehmer's polynomial and the E₁₀ Coxeter identity);
[`salem-tower`](https://github.com/dillon-11/salem-tower) (the prime
towers); [`cyclotomic-orders`](https://github.com/dillon-11/cyclotomic-orders)
(parity tower, Glaisher bands, cyclotomic values at integer bases).

## Lemmas of independent use

Candidates for use outside this repository (all `sorry`-free, axioms
`propext`/`Classical.choice`/`Quot.sound`):

- `orderOf_dichotomy_of_ker_exponent` (`LiftDichotomy`) — for a group
  homomorphism whose kernel has exponent p, element orders lift by 1 or
  exactly p. Plain group theory; not in Mathlib.
- `qpow_dvd_dobResultant` + `frobenius_factor` (`DobrowolskiBaseline`)
  — the base of Dobrowolski's lower bound,
  `q^{deg P} ∣ Res(P, P∘X^q)`, against Mathlib's resultant API.
- `pierce_sandwich` (`PierceValues`) —
  `1 ≤ ∏‖αᵢ^m − 1‖ ≤ 2^d·M(P)^m`, companion bounds to the Landau and
  Mignotte inequalities in `Mathlib.Analysis.Polynomial.MahlerMeasure`.
- `emultiplicity_cyclotomic_le_one` and the LTE tower law
  `emultiplicity_prime_pow_pow_sub_one` (`ZsygmondyLTE`) — the
  Birkhoff–Vandiver first-power bound and the linear valuation growth
  up the q-power tower; groundwork for Zsygmondy's theorem.
- `certified_zone` (`CertifiedZone`) — factor floor b plus N < b²
  imply primality, with the congruence form; and the Lucas
  rung-doubling law `V_{2n} = V_n² − 2(−1)ⁿ`.
- `mahler_metallic` / `golden_floor_deg2` (`MetallicRegulator`) — the
  Mahler measure of x² − kx − 1 is the fundamental unit; the degree-2
  floor is the golden ratio.

## Verify

```bash
# the Lean formalization (Mathlib cache, then full build)
lake exe cache get && lake build

# any census member p: depth-2 test with the built-in Frobenius guard
cc -O2 -o kernel scripts/lehmer_wieferich_kernel.c && ./kernel <lo> <hi> 2
# (use lehmer_wieferich_kernel128.c for hi > 2^32)

# the census of ANY unit, from its polynomial alone (here x² − x − 1):
cc -O2 -std=c11 -o ukernel scripts/unit_wieferich_kernel.c -lm && \
  ./ukernel 5 1000000000 2  1 -1 -1

# the Wilson integral of the family (§2.6), thirty seconds, pure python
python3 scripts/lerch_wilson_carry.py

# the fifteen new primes: APR-CL re-proof of any value in data/tower_primes/
gp -q  # isprime(N), PARI/GP >= 2.17
```

## Status

Draft. All census ranges have been re-run under the fixed kernels (see
the defect disclosures in `PROVENANCE.md`): the battery re-runs reproduce
every published member exactly, and the Lehmer decade (10⁹, 10¹⁰] —
404,204,977 primes — is empty, as preregistered at P(0) = 0.90.

## License

Apache-2.0 (code); the text of `source.md` and `PROVENANCE.md` is
additionally available under CC BY 4.0.
