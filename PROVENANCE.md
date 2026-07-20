# Provenance and verification discipline

## Verification layers (why no false member is possible)

1. **The Frobenius guard** is unconditional: `tr(α^p) ≡ tr(α) (mod p)` holds for
   every prime p. Every census kernel checks it at every candidate; a violation
   means the candidate is composite or the arithmetic is corrupted, and the run
   flags loudly instead of failing silently.
2. **Every claimed member is verified independently of the search code**: a
   big-integer Hensel/companion-matrix re-computation, and a kernel-checked
   Lean certificate (O(log p) square-and-multiply ladder; axiom footprint of
   the ladder core is `propext` alone). 720847 is additionally verified by the
   degree-5 Dickson trace ladder.
3. **Preregistration**: every census records its expected count (Σ 1/p over
   eligible primes) and a mutation control before running; controls
   must die.

## Method discipline

Every experimental run in this program goes through a fixed loop, enforced by
tooling rather than habit:

- **Predictions are recorded before the computation runs** (expected counts,
  expected mechanisms, expected control behavior) and scored afterwards as
  hit / split / miss. The ledger keeps the misses: several results here exist
  because a scored miss redirected the search — e.g. the apparent cross-family
  repeat primes were resolved as a birthday fluke by a decisive test, and the
  level-set criterion extracted en route is the keeper.
- **Controls run first.** Each census carries a mutation control (a corrupted
  principal form, a rotated modulus, a wrong-discriminant unit) that must
  fail; a run whose control survives is discarded, not filed.
- **Vacuous outcomes are routed separately.** A run whose guard fires (as in
  the sieve defect below) is neither a confirmation nor a refutation and is
  never filed as either; it triggers diagnosis of the instrument.
- **Nothing is claimed from a single code path.** Member sets must agree
  between independent implementations before any locus statement is made.

Three contributors: the human author (direction, judgment, review);
Claude (Anthropic) — reasoning, implementation, Lean formalization; and a
research harness enforcing preregistration, control-first experiments, and
independent re-computation. Trust none of them: every claim is
kernel-checked or re-computable in one command.

## Known kernel defects found and fixed (2026-07-18)

Both defects were caught by the guard/verification discipline; neither can
produce a false member. Both affect *completeness* (tallies) of specific
ranges only; the re-runs under the fixed kernels are complete and
reproduce every published member (battery to 10⁹ bit-identical;
Lehmer decade (10⁹, 10¹⁰] swept: 404,204,977 primes, zero members,
Frobenius guard fired zero times).

- **Segmented-sieve base-prime under-allocation** (`base_lim/10 + 100` slots
  vs π(base_lim) needed): heap overflow letting composites through the sieve
  when √hi ∈ [~1.7e3, ~5.5e4] (ranges reaching ~10⁸–3×10⁹). Symptom: guard
  violations at composites (e.g. 109474369 = 10463²). Fix: `base_lim/2 + 100`.
- **u64 modular-addition overflow at m = p² > 2⁶³** (p > 3.03×10⁹), and
  p² wrapping u64 at p > 2³²: fixed by 128-bit addition, and a dedicated
  128-bit-modulus kernel (`lehmer_wieferich_kernel128.c`, 34-bit-split mulmod)
  for p > 2³².

All searches above 10⁸ are re-run under the fixed kernels before any
completeness claim ("the locus is exactly {…}") is published; member sets are
diffed against the original runs and any tally correction is logged here.

## One-command re-verification

- Certificates: `lake exe cache get && lake build` in this repo
  (`WieferichFamilies/`, the paper's own Lean companion — mechanism +
  construct-and-certify layers, moved from bsd-complex 2026-07-19), and
  `lake build` in the cross-repo companions (salem-tower, cyclotomic-orders,
  bsd-complex for the Iwasawa-side ladders).
- Censuses: `cc -O2 -o kernel scripts/lehmer_wieferich_kernel.c && ./kernel <lo> <hi> 2`
  (use `lehmer_wieferich_kernel128.c` for hi > 2³²); shard ranges are recorded
  per census in the paper's §4 tables.
- Tower primes (§5.y, `data/tower_primes/`): each of the 15 values
  re-proves with PARI/GP APR-CL (`isprime(N)` at default flags, version
  2.17.4); the four staked values carry the factordb identifiers in the
  table.
- Massey rung (§2.2): `gp -q scripts/massey_rung_lambda3.gp` recomputes
  λ₅(ℚ(√−11)) = 2 with the generator and Hilbert-90 controls inline.
- Wilson integral (§2.6): `python3 scripts/lerch_wilson_carry.py`
  re-verifies the carry-total identity at every odd prime below 3000
  (set `PAIR = 1` for the norm-plus family; `PAIR = 3` is the control
  and must fail).
