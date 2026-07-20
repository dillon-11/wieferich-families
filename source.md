# Wieferich phenomena of algebraic units

*Draft. Formal certificates: the Lean 4 companion in this repository
(`WieferichFamilies/`) and the companion repositories `salem-tower`,
`cyclotomic-orders`, `lehmer-e10`. Census kernels: `scripts/`. Data:
`data/`.*

## Abstract

A Wieferich prime is a prime p with p² | 2^{p−1} − 1 [Wieferich 1909]. We
study the condition in the generality it naturally lives in: to every
algebraic unit α is attached a Wieferich locus

    W(α) = { p : ord(α mod p²) = ord(α mod p) },

the set of primes at which the multiplicative order of α fails to grow from
p to p². One elementary theorem governs every instance: for a group
homomorphism whose kernel has exponent p, element orders lift by a factor of
1 or exactly p, and the reduction (ℤ[α]/p²)ˣ → (ℤ[α]/p)ˣ is such a
homomorphism. The classical Wieferich condition, the Wall–Sun–Sun condition
[Wall 1960; Sun–Sun 1992], the Perrin-square condition, and Gold's criterion
for the Iwasawa invariant λ_p(K) > 1 of an imaginary quadratic field
[Gold 1974] are specializations.

We report: (i) censuses of thirteen unit loci to 10⁹, including the first
computation for any Salem number — the locus of Lehmer's unit [Lehmer 1933]
contains p = 720847 and, by the extension of its census to 10¹⁰, nothing
else below 10¹⁰; the loci of two further Salem numbers contain
144479 and 4674101; (ii) a 47-field census of Gold's condition to 10⁹ —
extending the tabulated range p ≤ 20000 of [Dummit–Ford–Kisilevsky–Sands
1991] by four orders of magnitude, with the records 330017383 (ℚ(√−67))
and 346527893 (ℚ(√−52)), each an unconditional witness of λ_p(K) > 1, and
a closed-form two-multiplication detector of the condition; (iii) an
exact (non-statistical) determination of the depth-≥3 stratum of the
metallic family x² − kx − 1, k ≤ 1000, and the exact linearity of the
depth grading along the p-power tower — in Iwasawa's notation λ = 1,
μ = 0, with ν the Wieferich depth — by lifting the exponent, with
deterministic members of every depth d ≥ 3; (iv) a localization theorem
identifying squared primes in cyclotomic values Φ_n(α) with order-lift
failures at index n, and the resulting graded prime towers; (v) closed-form
Aurifeuillian factorizations of the towers' composite levels, yielding
several new prime families — among them fifteen previously unrecorded
primes of the Pell and x² − 3x − 1 towers, 175–1173 digits, each with an
APR-CL certificate — and a certification method in which the N−1
factorization needed by classical primality proving [Brillhart–Lehmer–
Selfridge 1975] is supplied by the construction itself. Every reported
member above 10⁷ carries a Lean 4 kernel certificate of size O(log p);
mechanism theorems are machine-checked against Mathlib.

## 1. The framework

**Definition 1.1.** Let α be an algebraic unit with minimal polynomial P of
degree d, R = ℤ[α], and let p ∤ disc(P) be prime. The *Wieferich locus* of α
is

    W(α) = { p prime : ord_{(R/p²R)ˣ}(α) = ord_{(R/pR)ˣ}(α) }.

**Theorem 1.2 (order-lift dichotomy).** Let φ : G → H be a group
homomorphism whose kernel has exponent p, and let g ∈ G with φ(g) of finite
order. Then ord(g) = ord(φg) or ord(g) = p · ord(φg).

*Proof.* d := ord(φg) divides ord(g); g^d lies in the kernel, so g^{dp} = 1
and ord(g) | dp; primality of p leaves the two options. ∎
(Lean: `orderOf_dichotomy_of_ker_exponent`.)

**Lemma 1.3.** In a commutative ring, x² = 0 implies (1+x)^n = 1 + nx.
Hence in R/p²R every element of 1 + pR has p-th power 1, so the reduction
(R/p²R)ˣ → (R/pR)ˣ satisfies the hypothesis of Theorem 1.2 for every order
R. (Lean: `one_add_pow_of_sq_zero`, `ker_pow_prime`.)

Membership in W(α) is thus the non-generic branch of the dichotomy.
Under the standard heuristic that the Fermat
quotient of α equidistributes mod p (open even for α = 2), each prime lies
in W(α) with probability 1/p; the locus is expected infinite of logarithmic
density, and finite censuses admit Poisson tests (§5). Unconditionally,
nothing is known in either direction even for α = 2; under the
abc-conjecture the complement of W(2) is infinite [Silverman 1988].

**The p-adic logarithm.** For p ∤ disc(P) the Fermat quotient
q_p(α) = (α^{ord_p(α)} − 1)/p mod p is the depth-one coefficient of the
p-adic logarithm of α, and p ∈ W(α) is precisely its vanishing: log_p(α) ≡ 0
to second order. The locus is the depth-2 zero set of log_p as p varies —
the finite-place counterpart of the archimedean grading of §2.1 by the
Mahler measure log M(α). Gold's criterion is the same statement for the
p-adic unit root of the Frobenius quadratic of an imaginary quadratic field,
which is why both families obey the one dichotomy. Depth-k strata (§2.3)
refine the condition to vanishing of order k.

**The trace test.** Membership is decidable in O(d² log p) ring operations:
compute x^p mod (P(x), p²) and compare traces. The mod-p congruence
tr(α^p) ≡ tr(α) is the Frobenius identity and holds for every p — it serves
as an integrity guard on all searches below; the locus is the mod-p²
refinement. For d = 1 this is the classical Fermat-quotient test. For
reciprocal P the computation descends to the trace polynomial (degree d/2)
through the Dickson identity α^n + α^{−n} = D_n(α + α^{−1}), with
D_{2n} = D_n² − 2 as the square-and-multiply step. Over F_p the p-th
Dickson polynomial is the Frobenius, D_p(y) = y^p (Lean:
`dickson_frobenius_guard`).

## 2. The Wieferich families

### 2.1 One locus per unit

| unit α | degree / type | classical name | locus (known) | search bound |
|---|---|---|---|---|
| 2 | 1, rational | Wieferich (A001220) | {1093, 3511} | 2⁶⁴ [Dorais–Klyve 2011; PrimeGrid] |
| 10 | 1, rational | base-10 (A045616) | {3, 487, 56598313} | ~10¹⁴ (lit.; re-verified here) |
| (1+√5)/2 | 2, Pisot | Wall–Sun–Sun | ∅ | 2.8·10¹⁵ [PrimeGrid] |
| 1+√2 | 2, Pisot | (Pell) | {13, 31, 1546463} | 10⁹ (this work) |
| (3+√13)/2 | 2, Pisot | — | {241} | 10⁹ (this work) |
| plastic ρ | 3, Pisot (minimal) | Perrin-square (A173656) | {521, 190699} | ~10¹¹ (lit.) |
| supergolden ψ | 3, Pisot | — | ∅ | 10⁹ (this work) |
| tribonacci | 3, Pisot | — | {233} | 10⁹ (this work) |
| root of x⁴−x³−1 | 4, Pisot | — | {2819, 3178913} | 10⁹ (this work) |
| Lehmer's α | 10, Salem (min. known) | — | {720847} | 10¹⁰ (this work) |
| salem14 | 14, Salem, M = 1.200027 | — | {144479} | 10⁹ (this work) |
| salem18 | 18, Salem, M = 1.188368 | — | {4674101} | 10⁹ (this work) |

(salem14 is the root of x¹⁴ − x¹¹ − x¹⁰ + x⁷ − x⁴ − x³ + 1; salem18 the
root of x¹⁸ − x¹⁷ + x¹⁶ − x¹⁵ − x¹² + x¹¹ − x¹⁰ + x⁹ − x⁸ + x⁷ − x⁶ − x³ +
x² − x + 1, the second-smallest known Salem number. The minimality of the
degree-12 and degree-14 entries is verified exhaustively here: an
enumeration of all totally-real integer trace polynomials by the Robinson
derivative chain [Robinson 1964] — each successive coefficient enters the
derivative only as an additive constant, so total reality over an
interval propagates in closed form, with no per-candidate root-finding —
shows that no Salem number of degree 12 or 14 has measure below Lehmer's,
and recovers the published minima 1.240726 and 1.200027 [Mossinghoff
1998] to 10⁻⁶.)

The loci are pairwise disjoint as computed: 521 and 190699 are neither
base-2 Wieferich nor Wall–Sun–Sun; 720847 belongs to no smaller unit's
locus. Members with p ≤ deg P ({5, 7} for salem14; {5, 7, 11} for salem18)
arise from integer divisibilities rather than the generic mechanism and are
reported separately (§2.5).

The Lehmer census is the first at any serious height for a Salem unit. The
polynomial's irreducibility and its identity with the characteristic
polynomial of the E₁₀ Coxeter element are machine-checked in the companion
repository `lehmer-e10` [McMullen 2002], so the degree-10 order the census
works in is not an assumption. The member p = 720847 satisfies
tr(α^p) ≡ −1 (mod p²) and not (mod p³) — depth exactly 2 — and is verified
four independent ways: the C census kernel, a big-integer companion-matrix
recomputation, a 20-step kernel-checked Lean matrix ladder at degree 10,
and the degree-5 Dickson trace ladder. The census swept the 50,847,530
primes of [5, 10⁹) with the Frobenius guard holding at every prime; the
Poisson expectation for the range is λ = 2.46, consistent with the observed
count of 1. The extension through 10¹⁰ is complete: the 404,204,977 primes
of the decade (10⁹, 10¹⁰] contain no further member (λ ≈ 0.105 for the
decade; the zero was preregistered at P(0) = 0.90), so 720847 is the only
member of the Lehmer locus below 10¹⁰.

**The metallic family: the deep stratum is algebraic.** The family
x² − kx − 1 is the fundamental-unit ladder of the real quadratic orders
of norm −1: its Mahler measure is exactly the unit,
M(x² − kx − 1) = (k + √(k²+4))/2, so log M is the regulator, monotone in
k with floor the golden ratio at k = 1 (Lean: `mahler_metallic`,
`golden_floor_deg2`). Over this ladder with k ≤ 1000, p ∈ [5, 10⁶), the
stratum of depth ≥ 3 (p³ divides the defining congruence) consists of
exactly 66 members, 9 of depth 4 and none deeper.
These counts are not statistics. For fixed p the depth-3 members are the
roots of one congruence mod p³; the count obeys the local law
N₂(p) = p − 2·[p ≡ 1 (mod 4)] (the deficit is the two values k ↔ ±2i
excluded by the discriminant condition), and Hensel's lemma gives
N_d(p) = N₂(p) for every d ≥ 2 — each root lifts uniquely to every depth.
Deterministic counting for p ≤ 97 gives 62 members; the four members with
p > 97 were verified by independent big-integer computation. The depth-4
count of 9 equals the local-law prediction. (Lean: `unique_lift_of_unit_slope`,
`n2_at_7`; certificates mod p⁴ for the nine depth-4 members,
`hyper_moduli`.)

Two further phenomena in this family are theorems rather than observations.
The diagonal k = jp (0 < j < p) is empty at depth 3: there the roots of P
are 1-units times ±1, and (1+pc)^p + (−1+pd)^p ≡ p²(c+d) (mod p³) cannot
equal jp (Lean: `torsion_diagonal_rigid`, `metallic_diagonal_null`; the
census sees 0 members against a naive expectation of 41.1). Cubic units of
trace ≡ 0 built on perturbed cube roots of unity are members at depth
exactly 3 (Lean: `cube_root_char_sum`; 223 of 231 tested cases, the
remainder explained by the same computation). Both are instances of a
trichotomy graded by proximity to torsion: exact-torsion units are members
at every depth (`exact_torsion_all_depth`), perturbed-torsion units at
depth exactly 3 (`graded_collapse`), kernel-only cases never
(`grade_depth_matrix`). Where a census class is empty, the emptiness is a
theorem of this trichotomy or a finite window of a (conjecturally)
equidistributed sequence; the paper claims nothing stronger.

### 2.2 One locus per imaginary quadratic field

For K imaginary quadratic and p split with principal prime above it, write
4p = a² + |D|b². The unit-root condition

    a·(a^p − a)/p ≡ −1 (mod p)

is equivalent to u^{p−1} ≡ 1 (mod p²) for the p-adic unit root u of the
Frobenius quadratic (Lean: `unit_root_linearization`), and by Gold's
criterion [Gold 1974] it detects λ_p(K) > 1. The criterion needs no
principality: for p ∤ hD and 𝔭^h = (α), λ_p(K) > 1 ⟺ α^{p−1} ≡ 1 (mod 𝔭̄²);
since p ∤ h, h-th powering is an automorphism of the depth-2 kernel stratum,
so on the principal stratum the census flag and Gold's flag agree (Lean:
`census_flag_iff_gold_flag`). Every member below, at every class number
h ≤ 5, is therefore an unconditional witness of λ_p(K) > 1.

The low range of this condition is classical. Dummit, Ford, Kisilevsky
and Sands [1991] tabulated λ_p(K) for |D| ≤ 1000 and p ≤ 20000, so every
member below 20000 here is a recomputation; for ℚ(√−3) the full member
list is OEIS A239902 — the "exceptional primes" of Cosgrave and Dilcher
[2011], identified with λ_p > 1 by Stokes [2022] — whose sixth term
6811741 this census re-derives by a disjoint route (the closed form above
with a Cornacchia trace; no Gauss factorials, no p-adic L-function). The
contributions of this section are the range, the detector, and the
typing: the census is complete to 10⁸ and through the decade (10⁸, 10⁹]
— four orders of magnitude past the tabulated range — with 30 members to
10⁸ (Poisson expectation 20.2) and 2 in the decade (expectation 1.27);
the two-multiplication closed form needs none of the machinery of the
existing routes; and the members are typed as order-lift failures of the
unit root, uniformly with every other locus in this paper.

Members above the classical range include four for ℚ(√−163) — among them
32040013 and 85611527 — the records 330017383 (ℚ(√−67), h = 1) and
346527893 (ℚ(√−52), h = 2), and 17525953 for ℚ(√−56) (h = 4).

Three structural observations from the census data:

*Eligibility and the class group.* Only principal split primes are
eligible; the principal-split density is 1/h. At h = 2 principality is a
genus-theory congruence mod |D|. At h = 3 and h = 5 it is a Chebotarev
condition of density 1/3, 1/5 (verified: 235,061 split primes across six
h = 3 fields, density 0.3326; 196,015 across five h = 5 fields, 0.1992).
At h = 4 the behavior tracks the isomorphism type: for the ℤ/2 × ℤ/2 fields
principality is constant on residue classes mod |D| (multiquadratic Hilbert
class field), for the ℤ/4 fields it is not (D₄ closure). The mechanism is
complex conjugation, which acts on Gal(H/K) ≅ Cl(K) by inversion; the
action is trivial exactly on 2-torsion, so H/ℚ is abelian — and
principality a pure congruence condition — precisely when the class group
is elementary 2-torsion (Lean: `two_torsion_abelian`,
`z4_not_two_torsion`). The eligibility structure therefore reads the
isomorphism type of the class group, not just its order: at equal h it
separates ℤ/4 from ℤ/2 × ℤ/2.

*The Hilbert class field and the unit ladder.* For each h = 3 field the
principality condition is complete splitting in its cubic Hilbert class
field, generated by a Pisot unit of the same discriminant: disc −23 gives
x³ − x − 1 (the plastic number, the unit of the Perrin locus above), disc
−31 gives x³ − x² − 1, and so on — verified without mismatch over five
fields to 10⁵. The two halves of the paper meet here; orthogonality of the
two conditions is checked at p = 521 (a Perrin-square member, inert in
ℚ(√−23)).

*Depth of the members.* All 32 members have unit-root depth exactly 2:
a mod-p³ recomputation of every member (preregistered; the Poisson
expectation for depth ≥ 3 among them is 0.47, and the mutated-trace
control collapses to background) finds none deeper. This is a statement
about the unit root only, not about λ. By Gold's criterion depth ≥ 2 is
λ > 1, but the ladder does not continue diagonally: λ ≥ 3 is *not* the
depth-3 condition α^{p−1} ≡ 1 (mod 𝔭̄³). The correct rung
(McCallum–Sharifi for cyclotomic fields; Qi [2024] uniformly, via
n-fold Massey products) tests an auxiliary element — solve
Nm_{K₁/K}(β) = α in the first layer, form α₁ from the twisted product
∏σⁱ(βⁱ), and λ ≥ 3 ⟺ log_p α₁ ≡ 0 (mod p²) — a fresh depth-2
condition on a new unit, not a deeper condition on α. The depth-≥3
locus of the unit root is a doubly-non-generic stratum in its own
right, and the census confirms it empty here at the 1/p rate.

*The first Massey rung, computed.* For the smallest member (D = −11,
p = 5) the auxiliary element is within direct reach: solving
Nm(β) = α in the degree-10 field K·ℚ₁, with ℚ₁ the quintic subfield
of ℚ(ζ₂₅), and testing the twisted product ∏σⁱ(β)ⁱ gives
λ₅(ℚ(√−11)) = 2 exactly — the rung is nonzero, invariant under the
choice of generator and under the Hilbert-90 ambiguity of β
(`scripts/massey_rung_lambda3.gp`). This is, to our knowledge, the
first λ ≥ 3 test carried out through the Massey-product criterion
rather than a p-adic L-function; the same method reaches the next
members (D = −19, p = 11 and D = −3, p = 13) at relative degrees 22
and 26.

*Bernoulli indices.* The λ-condition fires on interior Bernoulli indices
(Herbrand–Ribet: 37 | num B₃₂, 67 | num B₅₈), the classical Wieferich
condition on the edge of the same spectrum, through Glaisher's congruence
q_p(2) ≡ −½·H_{(p−1)/2} (mod p) and the Wolstenholme window. Anchors
machine-checked: Glaisher at p = 7, 13; Wolstenholme at 5, 7; and
1093² | 2¹⁰⁹² − 1 carried through a 329-digit computation with empty axiom
footprint. The unit generalizations of Glaisher's congruence — the
Fibonacci and Pell quotients as harmonic band sums, so that the
Wall–Sun–Sun condition of §2.1 is the vanishing of a harmonic band —
are developed, with their Lean layer, in the companion repository
`cyclotomic-orders` (v0.1.2). Among {37, 43, 67, 79}, the invariants (h(−p) = 1;
p irregular) realize all four combinations, one prime each; the record
330017383 lies in the field of the doubly-positive cell, ℚ(√−67). Exactly
{37, 163} of the associated set are Pierpont primes (p − 1 3-smooth), the
others carrying single non-smooth factors 7, 11, 13; see Question 2 (§6).

### 2.3 Localization: cyclotomic values and prime towers

The Wieferich condition localizes index by index. For q | Φ_n(a), q ∤ na:

    q² | Φ_n(a)   ⟺   ord_{q²}(a) = ord_q(a) = n

(Lean: `cyclotomic_sq_dvd_iff_orderOf_eq`; the proof combines the standard
order characterization of primitive prime divisors with Theorem 1.2 and a
valuation-transfer lemma placing the q-adic valuation of aⁿ − 1 in its
primitive part). Squared primes in cyclotomic values are order-lift
failures at that index.

To a Salem polynomial P attach L_k = |Res(P, x^{2^k} + 1)| =
|N(Φ_{2^{k+1}}(α))|. Each L_k is a perfect square, exactly:
√L_k = |Res(P_tr, D_{2^{k−1}})| at the trace level. The sequence √L_k
carries a graded family of primes: q divides √L_k exactly when P has a root
of multiplicative order 2^{k+1} over F̄_q, and the index of the mod-q
factor carrying that root obeys the Dedekind grading r = ord_{2^{k+1}}(q)
(split case r = 1 forces q ≡ 1 mod 2^{k+1}; extension case r > 1 by
Lagrange in F_{q^m}; both machine-checked). For Lehmer's polynomial the
tower contains the Mersenne primes 3, 31, 127 (extension case), the Fermat
primes 257 and 65537 (split case — for a Fermat prime the multiplicative
group is a 2-group, so any splitting polynomial contributes), and larger
primes: √L₉ = 1302851980779781121, a 19-digit prime. A prime with several
roots of distinct 2-power orders occurs at several indices (65537 at
k = 10, 14, 15).

The localization theorem splits repeated prime factors of √L_k into a
horizontal case (several root pairs at one index: 8191², 257², 577² across
a 367-polynomial census, degrees 6–10, k ≤ 8) and a vertical case — a
genuine order-lift failure. The census finds the vertical case realized:
two degree-10 Salem polynomials have √L₂ = 49, the mod-7 factor
self-reciprocal with roots of order 8 mod 49. Lehmer's own tower is
squarefree through k = 10, and 720847 has no root of 2-power order: the
two loci are disjoint as far as computed.

**Mersenne primality as a tower statement.** The doubling step
D_{2n} = D_n² − 2 evaluated at 4 = tr(2 + √3) is the Lucas–Lehmer
sequence, term for term (Lean: `tower_eq_lucasLehmer`), and chaining
through Mathlib's certified Lucas–Lehmer test gives: 2^p − 1 is prime iff
the tower vanishes mod 2^p − 1 (`mersenne_prime_iff_tower_vanishes`).
When 2^p − 1 is prime, the extension AdjoinRoot(x² − 4x + 1) over
ZMod(2^p − 1) contains a unit of order exactly 2^p
(`mersenne_prime_seed_order`); the underlying calculus is generic: over
any commutative ring, D_n(u + u⁻¹) = 0 iff u^{2n} = −1, and such an
antiperiod pins v₂(ord u) = v₂(n) + 1 (`UnitAntiperiod`).

Two corollaries. A squared prime factor of a Mersenne number 2^p − 1
(p prime) is a base-2 Wieferich prime; in general q² | 2ⁿ − 1 forces q
Wieferich or q·ord_q(2) | n (Lean: `sq_dvd_mersenne_wieferich`,
`sq_dvd_two_pow_forced`). No squarefree failure is known. Replacing 2-power
by 3-power indices yields a second tower, N_k = |Res(P, Φ_{3^{k+1}})|, a
perfect square by the identity (v² + v + 1)(v⁻² + v⁻¹ + 1) = (D_s(y) + 1)²
with v = α^s, s = 3^k; for Lehmer's polynomial it contains 163 (k = 3,
split, ≡ 1 mod 81) and 19100773 (k = 4, ≡ 1 mod 243).

**Dobrowolski's resultant.** The baseline is a general theorem: for monic
P and prime p, the Frobenius factorization P(X^p) = P^p + p·h over ℤ gives
the exact integer identity

    Res(P, P(x^p)) = p^{deg P} · Res(P, h),

so p^{deg P} divides the resultant unconditionally (Lean:
`DobrowolskiBaseline`: `frobenius_factor`, `dobResultant_eq_qpow_mul`,
`qpow_dvd_dobResultant`). The refinement measured by these censuses is
that the valuation reads the Wieferich depth linearly: each depth-e
failure at an eligible factor adds (factor degree)·(e − 1) above the
baseline. On the metallic family at p = 7: the golden non-member gives
v = 2 (the baseline, sharp), the depth-3 member 6, the depth-4 member 8;
for the two tower examples above, v₇ = 12 = 10 + 2·1 against the Lehmer
control at 10 (Lean anchors: `Dobrowolski`, `dobro_hyper_7`, axiom
footprint `propext`). The fluctuation term in Dobrowolski's lower bound
[Dobrowolski 1979] is therefore the Wieferich depth of the unit. The
formalized baseline gives the ≥ direction in general; the exact increment
law is supported here by the census and the kernel anchors. One remark on
scope: the Mahler-measure inequality M(P) ≥ |P(0)| places every unit of
this paper exactly on the |P(0)| = 1 wall — the locus where the
constant-term lever in Mahler lower bounds degenerates, which is why the
depth refinement, not the constant term, carries the information here.

**Pierce values.** The same resultant engine bounds the Pierce–Lehmer
sequence Δ_m = ±Res(P, X^m − 1) = ±∏ᵢ(αᵢ^m − 1) [Pierce 1916;
Lehmer 1933] two-sidedly: when no root of P is an m-th root of unity,

    1 ≤ ∏ᵢ ‖αᵢ^m − 1‖ ≤ 2^d · M(P)^m

(Lean: `PierceValues`: `one_le_abs_pierce`, `pierce_upper`,
`pierce_sandwich`). The lower bound is the integrality input of the
Blanksby–Montgomery lower bound for the Mahler measure
[Blanksby–Montgomery 1971]; the pair is the constraint window in which
the depth grading of Question 4 lives, since Δ_m is exactly the
cyclotomic-value product whose squared primes the localization theorem
classifies.

**The trace field.** A reciprocal P of degree 2d and its trace polynomial
T — P(x) = x^d T(x + 1/x) — satisfy the exact discriminant identity

    d_P = (−1)^d · P(1) · P(−1) · d_T²,

because the relative different of the extension is generated by x − x⁻¹
and N_{T/ℚ}(y² − 4) = T(2)·T(−2) = (−1)^d P(1)P(−1). The relative
conductor is thus m² = |P(1)P(−1)| — up to sign the second Pierce value
Δ₂, the cyclotomic value data above evaluated at the two fixed points
x = ±1 of x ↦ 1/x — and P(1)P(−1) < 0 without exception, since a Salem
root pushes T(2) below zero while sign T(−2) = (−1)^d. Both statements
are verified exactly on all 112 Salem trace fields of the census (and
the ±1-evaluation identity on all 4,913 degree-6 lattice points).

For Lehmer's polynomial the identity opens a complete class-number
certificate with no computer-algebra system in the loop: disc T = 36497
is prime, so ℤ[y]/(T) is the maximal order, and the Dedekind criterion
at 36497 gives d_P = 36497². The Minkowski bounds are then rigorous
(M_T = 7.3, M_P = 34.8), and explicit generators for every prime ideal
below them — y itself has norm T(0) = 3; x² + 1 has norm 9;
x³ + x − 1 and x³ − x² − 1 generate the two norm-23 primes; two explicit
degree-5 lifts of the mod-2 factors of P generate the norm-32 primes —
prove h_T = h_P = 1. The unit index [E_P : E_T⟨λ⟩] — the index, inside
the unit group of ℚ(α), of the subgroup generated by the trace-field
units together with the Salem unit λ — is a positive integer, and the
analytic class number formula for the pair, evaluated to 7 ppm, pins it
to exactly 4: the computed ratio is 0.2500007, and the integrality of
the index leaves 4 as the only admissible value — a pinch, not a
floating-point identity. The second-smallest degree-10 Salem polynomial
(x¹⁰ − x⁶ − x⁵ − x⁴ + 1, M ≈ 1.21639) repeats the pattern exactly:
disc T = 38569 prime, h_P = 1 by the same Minkowski certificates, unit
index 4.

**The depth grading is Iwasawa-linear.** The dichotomy is not confined
to the first lift. The kernel of (R/p^{k+1}R)ˣ → (R/p^kR)ˣ consists of
the classes 1 + p^k R, and (p^k c)² = 0 in R/p^{k+1}R for every k ≥ 1,
so Lemma 1.3 and Theorem 1.2 apply verbatim at every level of the
p-power tower: at each step the order is preserved or multiplied by
exactly p. Lifting the exponent then rigidifies the entire profile: for
an odd prime q with q | x − 1,

    v_q(x^{q^k} − 1) = v_q(x − 1) + k

exactly (Lean: `emultiplicity_prime_pow_pow_sub_one`). For a member q of
W(α) of depth e this reads: the tower valuations
e_k = v_q(α^{n q^k} − 1), with n the order of α at q, climb linearly
from e with slope one. In the notation of Iwasawa's growth formula
e_k = λk + μq^k + ν, the unit tower has λ = 1 and μ = 0 unconditionally,
and ν is the Wieferich depth of the base level: the depth *is* the
ν-invariant of the tower. This answers Question 4 in the form it was
asked: the multiplicity of q in the Pierce–Lehmer sequence is

    v_q(Δ_m) = e + v_q(m/n)   for n | m   (and 0 otherwise)

— the depth carries the constant term and the index carries the growth,
which is exactly the coincidence of the depth grading with the
multiplicity grading, made quantitative. The linearity was verified with
zero exceptions across 429 base-2 and 428 golden-unit instances
(preregistered).

In the metallic family the deep diagonal is, moreover, constructive.
For p³ | k the pair (k, p) is a member of depth exactly v_p(k): the
residue classes of k mod p³ admitting depth-3 members are the zero class
together with sign-symmetric pairs, and on the zero class the Hensel
lift stalls at precisely the valuation of k. Every depth d ≥ 3 therefore
has deterministic members k ∈ p^d · {1, …, p − 1} — no search — and the
lone instance with k ≤ 1000, k = 625 = 5⁴ at p = 5, is one of the nine
depth-4 members certified in §2.1 (`hyper_625_5`). The two ends of the
diagonal behave oppositely: the valuation-1 diagonal k = jp is empty at
depth 3 (§2.1), the valuation-≥3 diagonal is full with exact depth.

### 2.4 Primitive divisors

Every prime factor of Φ_n(a) is primitive (order exactly n, hence ≡ 1
mod n) or intrinsic (divides n) — machine-checked, with the disjointness
and existence reductions. The Birkhoff–Vandiver first-power bound
[Birkhoff–Vandiver 1904] is formalized (`emultiplicity_cyclotomic_le_one`):
an intrinsic prime divides Φ_n(2) at most once, by one application of
lifting-the-exponent whose hypothesis is automatic (ord_q(2) | n/q). The
existence statement of Zsygmondy's theorem [Zsygmondy 1892] at base 2
reduces to the single inequality |Φ_n(2)| > rad(n) for n > 6 (typed as
`SizeLeaf`); on prime-power indices the inequality is proved, so existence
of a primitive divisor of Φ_{p^k}(2) is unconditional here
(`prime_pow_rung_size`, `exists_extrinsic_prime_pow`). The norm-form
analogue for unit towers reduces the same way, with one change forced by
data: a 367-polynomial census (indices ≤ 30, preregistered) exhibited
intrinsic multiplicity up to 20 at degree 8 — the naive first-power
statement is false for norms, because the norm accumulates the unit's own
Wieferich depth at the order index — and the formalized reduction
(`NormFormLift`, `dvd_radical_pow_of_bounded`) therefore carries an
explicit multiplicity budget. The reduction is formalized a second time,
independently and self-contained, in `salem-tower`
(`ZsygmondyReduction`), with the LTE step done by an elementary
geometric-sum congruence.

### 2.5 The integer place

Call n > 1 a *trace return* of a unit if tr(αⁿ) = tr(α) in ℤ. An exact
return is membership at every modulus simultaneously — the depth-∞ stratum.
For a non-torsion unit, returns are confined to an initial window
n ≲ log(2d + 2)/log M(α).

**Theorem.** A degree-d unit whose trace sequence is bounded and returns to
one value infinitely often has eventually periodic traces, and eventual
periodicity forces every root to be a root of unity. Hence a non-torsion
unit has finitely many trace returns. (Lean:
`eventually_periodic_of_bounded`, `coeff_zero_of_forall_sum_pow`,
`roots_torsion_of_eventually_periodic`, `no_persistent_resonance`.)

(The traces of Salem numbers themselves are a studied subject — the
small tables go back to [Boyd 1977], and McKee–Smyth showed Salem
numbers exist of every trace [McKee–Smyth 2005]; the return statistic
here concerns the trace sequence of the powers of one fixed unit.)
Across 1,436 Salem polynomials of degrees 6–30 the window obeys an exact
two-parameter law. Write L for the circle load — the trace mass carried
by the d − 2 conjugates on |z| = 1, after subtracting the escaped pair.
Then the observed small-trace window W = max{n : |t_n| ≤ 6} equals
max{n : αⁿ − L ≤ 6} within ±3 for 99.9% of the census: Mahler measure
and circle load determine the window. The load itself is a construction
invariant, not a degree law (Spearman −0.15 against degree):
exhaustively enumerated small-height Salem polynomials run near the
alignment bound (0.7–0.95 per conjugate pair), while polynomials padded
up from low-degree Pisot seeds collapse below 0.1 of it by degree 24.
(For Lehmer's polynomial the
theoretical bound above permits ≈ 19 indices; the observed |t| ≤ 6
window is W = 12.) Within the window, silence is graded, and sharply:
the fraction of polynomials with no return collapses monotonically with
window length — about 0.98 at W ≤ 2, but only 2 of 13 at W = 5 — and
exactly three census members reach W ≥ 10. Two of them return (salem18
at every odd n ≤ 11, kernel-verified at the companion matrix,
`salem18_integer_collisions`); Lehmer's polynomial, at W = 12 with zero
returns, is the unique long-window silent member of the entire census.
The load, in turn, is a continuous function of torsion proximity: the
mean distance of the circle phases to the nearest roots-of-unity grid
tracks the load at Spearman 0.70, and constructions padded toward roots
of unity interpolate continuously into the loud, structured-cancellation
regime. So Lehmer's polynomial is extremal in measure (the longest
window), typical in load (0.79 of the alignment bound, inside its
degree-10 cohort), and unique in silence — and the extremality question
for Salem numbers is correspondingly sharp: whether a window this long
can stay returnless has exactly one known witness, and the census cannot
decide whether the pairing of minimal measure with silence is forced or
accidental. Pisot trace sequences, by contrast, are strictly monotone
from n = 1: no cancellation is available and the question does not
arise.

### 2.6 The Wilson integral of the family

The loci of this section are pointwise statements about the Fermat
quotient q_p(α) = (α^(p−1) − 1)/p. Their total is also a classical
object. Lerch's congruence [Lerch 1905] identifies the sum of the
rational spectrum with the Wilson quotient:

Σ_{a=1}^{p−1} q_p(a) ≡ w_p (mod p),  w_p = ((p−1)! + 1)/p

(sign in these conventions; verified here for every odd p < 3000). The
family x² − kx − 1 meets this sum intrinsically. Every a ∈ F_p^× is a
root of the member k = a − a⁻¹, and the family double-covers F_p^× by
the pairing a ↔ −a⁻¹; the Fermat quotient is odd under the pairing up
to an exact carry term, and summing the carries over the window
[1, p−1] gives the involuted form

Σ_{a=1}^{p−1} (a·b_a + 1)/p ≡ 2·w_p (mod p),  a·b_a ≡ −1 (mod p).

The companion family x² − kx + 1, whose pairing is a ↔ a⁻¹, satisfies
the same identity with the opposite sign: writing the pairing as
a·b_a ≡ ε (mod p) with ε = ∓1 the norm of the family,

Σ_{a=1}^{p−1} (a·b_a − ε)/p ≡ −2ε·w_p (mod p),

verified exactly at every odd prime p < 3000 for both signs, with the
non-unit pairing a·b_a ≡ 3 as control (`scripts/lerch_wilson_carry.py`).
The carry-total of a quadratic unit family thus reads the Wilson
quotient through the norm character of the family. In this reading a
Wieferich event at (k, p) is a pointwise zero of the Fermat-quotient
spectrum, while a Wilson prime — 5, 13, 563, none other below 2·10¹³
[Costa–Gerbicz–Harvey 2014] — is a zero of its total: one congruence
on the whole spectrum rather than one per member, which is the right
order of magnitude for its rarity. These identities are census-verified
computations, not part of the Lean development.

## 3. New prime families from Aurifeuillian structure

The composite levels of the unit towers are not opaque: they factor in
closed form, and the factors are prime families of independent interest.
This section reports the factorization laws, the resulting families, and
fifteen new proven primes.

### 3.1 The factorization law

For the golden unit and odd m, the primitive part of the Fibonacci–Lucas
tower at index 5m factors as

    Λ_{5m} = (H₊ / s₊) · (H₋ / s₋),      H± = 5F_m² ± 5F_m + 1,

with H₊H₋ = 25F_m⁴ − 15F_m² + 1 and the stray factors s± supported on
rank-of-apparition primes (verified exactly at the seven indices
n = 85, …, 265 in `data/`; the prime 11 alternates between the halves).
This is the Aurifeuillian phenomenon [Brent 1993] in unit coordinates. Two
consequences matter for primality:

- *Sieve inheritance.* The prime factors of H± satisfy the full index-5m
  congruence q ≡ ±1 (mod 5m).
- *The certificate seam.* H± − 1 = 5F_m(F_m ± 1). The N−1 side of every
  half-value factors by construction into Fibonacci numbers and their
  neighbors, so Brillhart–Lehmer–Selfridge certificates assemble from
  standard factor tables.

(Lean: `aurifHalf_product`, `aurifHalfP_seam`, `goldHalfP_seam`.)

**The 4 | n square law.** A second closed-form structure governs the
doubly-even indices: for a norm-(−1) metallic unit the primitive part
Λ_n is a perfect square at every index 4 | n, n > 4 — 444 of 444
instances to index 600 across the golden, Pell, and x² − 3x − 1 towers,
against 0 of 149 for base 2, whose unit has norm +1. The mechanism is
the identity Φ_{4m}(x) = Φ_{2m}(x²): the index-4m value of the unit is
the index-2m value of its square, which has norm +1 and is reciprocal,
so its cyclotomic values factor through the trace field as squares —
the same mechanism as the 2-power tower of §2.3, now on the whole
4 | n lane. Taking square roots on the lane recovers 65 (golden), 32
(Pell), and 33 (x² − 3x − 1) additional prime indices, and turns an
apparent within-size depletion of primes at v₂(n) = 2 (observed 5
against 31 expected) into an algebraically transparent removal and
redirection of lanes rather than a statistical deficit.

### 3.2 Half-primes and their certificates

The half-values that are prime form a family graded by m — 23 members for
odd m ≤ 1000, the largest of 258 digits (`data/half_primes.tsv`). Via the
seam and the factorizations of F₄₅₇, F₂₂₉, L₂₂₈, F₆₁₇, F₃₀₉, L₃₀₈
(factordb, re-verified), the members at m = 457 and m = 617 carry complete
Lucas N−1 certificates at 192 and 258 digits
(`data/certified_zone/cert_half_prime_457_617.json`, witnesses 2 and 11).
These indices appear in the tables of Lucas Aurifeuillian primitive parts
(OEIS A061443, entries k = 2285, 3085); the certificates, which replace
probable-prime status by N−1 proofs assembled from the construction, are
new.

### 3.3 Halves are norms

The two halves are norms from the quadratic extension adjoining the
discriminant. Solving Schinzel's identity Φ_D(x) = A(x)² − Dx·B(x)²
[Schinzel 1962] for D = 13 gives A = x⁶ + 7x⁵ + 15x⁴ + 19x³ + 15x² + 7x + 1,
B = x⁵ + 3x⁴ + 5x³ + 5x² + 3x + 1, and the norm halves evaluated at the
unit reproduce the x² − 3x − 1 census factors at m = 3, 5, 7; for D = 17
the degree-8 solution exists likewise. At the base-2 place the same
statement reads: at every index n ≡ 4 (mod 8) of the census one half equals
gcd(N((1+i)^{n/4} − 1), Λ_n) — the Gaussian–Mersenne norms — with the
middle sign given by the quadratic character of 2, i.e. the exponent class
mod 8. One mechanism, three instances (ℤ[i], ℤ[φ], ℤ[(3+√13)/2]): the
Aurifeuillian halves of a unit tower are norms from the disc-adjoined
extension.

### 3.4 The Pell and x² − 3x − 1 towers: fifteen new primes

The public record is uneven across discriminants. For the golden unit the
primitive-part prime tables reach index ~3·10⁵ (OEIS A061442/3/5 and the
associated factor projects); for the Pell unit no such table exists (OEIS
A008555 lists the primitive parts but no primality census); for
x² − 3x − 1 nothing is recorded at all.

A preregistered sweep of indices 1100 ≤ n ≤ 2600 (garbage-controlled: an
additive perturbation of the primitive part must and does kill all hits)
found 17 distinct prime primitive parts after identifying the re-indexing
duplicates Λ_{2n} = Λ_n (odd n). A factordb probe of the largest values
shows the expected gradient: both tested x² − 2x − 1 values of index
< 2100 were already present with primality proofs, while n = 2317 (758
digits) was absent, and all three tested x² − 3x − 1 values were absent.
The fifteen values retained as new are listed in
`data/tower_primes/tower_primes.tsv` with the four factordb
identifiers; each of the fifteen — ten of x² − 3x − 1 (175–1173 digits,
largest at n = 2497) and five of Pell (322–758 digits) — carries an APR-CL
primality proof [Adleman–Pomerance–Rumely 1983; Cohen–Lenstra 1984]
produced with PARI/GP 2.17 and re-runnable from the stored values in one
command.

Every value inherits the index-n congruence sieve on its prime factors, so
the certification method of §4.2 applies as the family grows.

## 4. Certificates and method

### 4.1 Member certificates

Every reported Wieferich-type member above 10⁷ carries a Lean 4 kernel
certificate: ⌈log₂ p⌉ square-and-multiply congruence steps mod p², each a
kernel decision on integers < p⁶, glued by two ModEq lemmas (axiom
footprint of the core: `propext`). Certification height is unbounded in
practice — demonstrated from 489061 (19 steps; previously certified only
through a ~1.25-million-digit computation) to 346527893 (29 steps). For
reciprocal P the ladder runs at the trace level (degree d/2); the 720847
certificate re-verifies at degree 5, with a control prime failing mod q²
while passing the Frobenius guard. The nine depth-4 metallic members carry
matrix certificates mod p⁴ (`hyper_moduli`), and `modulus_is_p_squared`
pins the certified modulus. All searches ran in two independent
implementations (C kernel with 128-bit arithmetic; big-integer reference)
with bit-identical member sets on validation ranges.

### 4.2 Primality from construction

For the towers the primality proving is not external to the mathematics:

- *The certified zone.* If every prime factor of N is ≥ b and N < b², then
  N is prime (trial-division floor + size; Lean: `certified_zone`,
  `certified_zone_modeq`). The congruence sieve of §2.3/§3.1 supplies the
  floor: all factors of a primitive part at index n are ≡ ±1 (mod n), so
  values below (n+1)² are prime by construction, with no primality test in
  the pipeline.
- *The seam.* Beyond the quadratic zone, the N−1 factorization required by
  [Brillhart–Lehmer–Selfridge 1975] is definitional for the Aurifeuillian
  halves (§3.1) and partially definitional for tower values (a unit of
  order n in (ℤ/N)ˣ forces n | N − 1; Lean: `dvd_sub_one_of_orderOf`).
- *Closure in practice.* The shifted values Λ_n ∓ 1 of tower primes
  factor preferentially into the tower's own earlier levels: in log-mass,
  the fraction carried by primes q with ord_q(α) ≤ n is 0.45–0.58 across
  the towers against 0.14–0.19 on size-matched controls — a threefold
  bias, which routes N−1 mass into factors the construction can see. Three
  end-to-end Lucas certificates assemble from tower data alone — the Pell
  tower at n = 291 (74 digits, witness 31), x² − 3x − 1 at n = 297
  (94 digits, witness 14), the golden tower at n = 513 (68 digits,
  witness 59) — each instantiating Mathlib's `lucas_primality`
  (`data/certified_zone/`). Under a strict closure rule (only completely
  factored pieces count toward the N−1 fraction; large probable-prime
  cofactors count as reductions, not certificates), 90–100% of prime
  indices reach the Pocklington threshold β > 1/3 at moderate size,
  57–80% above 100 digits, with the largest closed certificate at 359
  digits (Pell, n = 937). The doubling pairs propagate certificates
  along n ↦ 2n via V_{2n} = V_n² − 2(−1)ⁿ (Lean: the rung-doubling law
  in `CertifiedZone`).
- *Cost.* The search-cost accounting is itself formalized: with R indices
  read, S sieve survivors, oracle cost o and certificate cost c, the
  pipeline cost is r·R + √S·o + c, never exceeding — and, for S > 1,
  strictly below — the linear scan; any sieve that shrinks S shrinks the
  bound monotonically (Lean: `SearchCost` module: `engine_le_scan`,
  `engine_lt_scan`, `lane_compression_mono`, `engine_end_to_end`; the
  final conjunct of `engine_end_to_end` is the primality of the output
  via `certified_zone`).

### 4.3 Search discipline

Every census was preregistered: expected count, control behavior, and pass
criteria recorded before the run. Controls are of two kinds — a depth-1
mutation that must explode (it does, in every census), and the Frobenius
guard, which fired zero times across all completed censuses (7 ×
50,847,530 primes in the unit battery alone). The preregistration ledger
ships with the data (§5.4).

## 5. Statistics

Under the equidistribution heuristic of §1, a depth-2 census over a prime
range expects λ = Σ 1/p members, Poisson-distributed over eligible primes.

### 5.1 Per-census table

| census | range | eligible primes | λ | observed | note |
| --- | --- | --- | --- | --- | --- |
| Lehmer unit | [5, 10⁹) | 50,847,530 | 2.46 | 1 (720847) | P(N ≤ 1) ≈ 0.30 |
| Lehmer unit, decade | (10⁹, 10¹⁰] | 404,204,977 | 0.105 | 0 | predicted 0 at P(0) = 0.90; guard 0 |
| 7-unit battery | [5, 10⁹) each | 7 × 50,847,530 | 2.4–2.5 each | 9 across 7 loci | supergolden ∅: P(0) = 8.5% |
| Gold, 47 fields | [5, 10⁸) | principal-split per field | 20.2 | 30 | +2.2σ; reproduced 30/30 on re-run |
| Gold, decade | (10⁸, 10⁹] | — | 1.27 | 2 (the records) | both re-found on re-run |
| metallic depth ≥ 3 | k ≤ 1000, p ≤ 10⁶ | 78,494,018 pairs | 91 | 66 (−2.6σ) | exact count, §5.2 |
| torsion diagonal | 20 classes, p ≤ 10⁶ | — | 41.1 | 0 (z = −6.4) | a theorem, §2.1 |
| off-diagonal control | 20 classes, p ≤ 10⁶ | — | 41.1 | 39 (z = −0.3) | |
| trace-0 cubic diagonal | p ≤ 10⁶ | 231 classes | — | 223/231 members | a theorem, §2.1 |
| Wall–Sun–Sun | p < 10⁶ | — | — | 0 | classical null reproduced |
| tower squared primes | 367 polynomials, k ≤ 8 | — | — | 2 vertical; all 30 instances classified | §2.3 |

The three entries beyond 1σ are the three §2 explains exactly: the
diagonal zero and the cubic near-fill are theorems, and the metallic
deficit is the ramified-class exclusion in the local law (§5.2).

### 5.2 The metallic count, reconciled

For fixed p the depth-3 members are roots of one congruence mod p³ with
local count N₂(p) = p − 2·[p ≡ 1 (mod 4)] (verified p = 5, …, 37) and
Hensel rigidity N_d = N₂ for d ≥ 2. Deterministic counting for p ≤ 97
gives 62; independent verification of the four members with p > 97 gives
66 = the observed total, and the depth-4 count of 9 is the local-law
value. The −2.6σ in the table is the ramified exclusion, not a
fluctuation.

### 5.3 Per-field diagnostics of the Gold census

Two diagnostics on the member positions, one positive and hedged, one a
preregistered null.

*A possible excess at ℚ(√−3).* The field D = −3 carries six members
below 10⁸ (13, 181, 2521, 76543, 489061, 6811741 — the list of OEIS
A239902) against a sieve-computed expectation λ = 1.10: P(≥ 6) ≈ 0.001,
surviving the 47-field look-elsewhere correction at p = 0.046. The flag
is representation-invariant (all three Cornacchia representations of 4p
agree on every member and control), the excess concentrates at the
single trace value t = −1 rather than distorting the quotient
distribution, and ℚ(√−4) — the only other field with extra torsion —
shows no excess (1 observed, 1.17 expected). Whether this is a small-p
fluctuation (three of the six members cost almost nothing) or a genuine
torsion-linked mechanism is open; the next decade of the census decides,
and the prediction is preregistered.

*No shell structure (null).* A preregistered Fisher rank statistic
testing whether member positions p carry multiplicative structure in
p − 1 beyond the depth condition is null exactly as predicted
(X = 53.9 against the 1% line 68.7 on 22 members), and an in-sample
pattern among the smallest members did not extend: 0 of 8 members above
5·10⁵ repeat it. Member positions look Poisson in every coordinate
tested, consistent with the equidistribution heuristic of §1.

### 5.4 Preregistration ledger

| id | census | prediction (condensed) | score |
| --- | --- | --- | --- |
| P-1784344562-8340 | Lehmer unit 10⁹ | kernel = reference below 2·10⁴; guard 0; Poisson λ ≈ 2.46 | hit |
| P-1784347567-5436 | 7-unit battery | bit-identical validation; guard 0; per-unit Poisson | hit |
| P-1784341672-3940 | Gold 47-field 10⁸ | classical members reproduced; Hensel at every flag; ≥ 8 new members h ≥ 2; ≥ 1 record; control explodes | hit |
| P-1784347925-4600 | metallic depth ≥ 3 | validated k ≤ 29; guard 0; Poisson λ ≈ 91; ~9 depth-4 | hit |
| P-1784316776-0479 | Wall–Sun–Sun / disjointness | no WSS < 10⁶; 16 CM members non-WSS | hit |
| P-1784351179-6409 | tower squared primes | zero vertical, < 5 horizontal | split: 2 vertical found; classifier held 30/30 |
| P-1784351543-8469 | Lehmer decade 10¹⁰ | zero members (P(0) = 0.90); Dickson cross-check on any member | hit: 0 members in 404,204,977 primes, guard 0 |

The split is reported as scored: the count sub-prediction failed — the
squared-prime population was richer than predicted, and the excess became
the classification theorem of §2.3 — while the classifier sub-prediction
held on every instance.

## 6. Questions

Each question is an open edge on a result proved or computed in the
body; the anchor section is given in parentheses, and nothing is
answered here.

1. (§2.1) The Lehmer locus is nonempty but lonely: the census to 10¹⁰
   finds only 720847 (the decade (10⁹, 10¹⁰] is empty, as the rate
   λ ≈ 0.105 predicts). Is a second member within computational reach?
2. (§2.2) Is the minimal non-smooth factor of p − 1 — the Pierpont
   deviation observed across {37, 43, 67, 79, 163} — an invariant of
   the cell in the (class number, irregularity) classification?
3. (§5.3) Do the per-field statistics of the Gold census match
   Iwasawa-theoretic predictions for the distribution of λ_p(K) over p?
   Everything tested so far is Poisson except a possible atom at
   ℚ(√−3); the next decade is the preregistered discriminator.
4. (§2.3) The depth grading is closed along the tower; over p it is
   open. The expected count Σ_p p^{1−e} converges for e ≥ 3, so a fixed
   unit should have only finitely many deep members. Exhibit a unit
   with two members of depth ≥ 3, or prove an effective finiteness
   statement.
5. (§2.3) Are there infinitely many Salem polynomials whose tower
   carries an order-lift failure? The heuristic rate is 1/q per
   eligible factor; the census realizes two instances at q = 7.
6. (§5) Equidistribution of the Fermat quotient of a unit, as p varies,
   is open even for α = 2, and every Poisson statement in §5 is
   conditional on it. Which parts of the structure survive its failure?
7. (§2.2) Extend the Massey-rung computation of λ₅(ℚ(√−11)) = 2 to the
   rest of the Gold atlas — one norm equation in the first layer per
   member. Do the closed-form techniques of §2.2 (Cornacchia trace, no
   p-adic L-function) extend to the rung, giving an O(log p)-witnessed
   λ ≥ 3 detector?
8. (§2.3) Both computed trace-field certificates give unit index
   [E_P : E_T⟨λ⟩] = 4. Is the index 4 for every Salem polynomial with
   h_P = 1, or an accident of small discriminant? The certificate
   machinery makes any candidate checkable.
9. (§2.5) Can a window of length ≥ 10 stay silent for any Salem
   polynomial other than Lehmer's? Equivalently: is minimal Mahler
   measure forced to pair with silence? A census at higher degree
   decides this falsifiably, one polynomial at a time.
10. (§3) Which index lanes of a unit tower carry algebraically forced
   factorizations, and is there a complete classification of such
   primality-transparent lanes in terms of the splitting of the unit
   in cyclotomic extensions, each with a certificate seam like §3.1's?
11. (§2.6) Does the Wilson quotient decompose along the strata of the
   family — split versus inert members, or the depth grading — with
   structured subsums? And do Wilson primes admit an order-lift
   reading: which group's order fails to lift at (p−1)! ≡ −1 (mod p²)?

## References

- L. Adleman, C. Pomerance, R. Rumely, *On distinguishing prime numbers
  from composite numbers*, Ann. of Math. 117 (1983), 173–206.
- G. D. Birkhoff, H. S. Vandiver, *On the integral divisors of aⁿ − bⁿ*,
  Ann. of Math. 5 (1904), 173–180.
- P. E. Blanksby, H. L. Montgomery, *Algebraic integers near the unit
  circle*, Acta Arith. 18 (1971), 355–369.
- D. W. Boyd, *Small Salem numbers*, Duke Math. J. 44 (1977), 315–328.
- R. P. Brent, *On computing factors of cyclotomic polynomials*,
  Math. Comp. 61 (1993), 131–149.
- J. Brillhart, D. H. Lehmer, J. L. Selfridge, *New primality criteria and
  factorizations of 2^m ± 1*, Math. Comp. 29 (1975), 620–647.
- H. Cohen, H. W. Lenstra, Jr., *Primality testing and Jacobi sums*,
  Math. Comp. 42 (1984), 297–330.
- J. B. Cosgrave, K. Dilcher, *An introduction to Gauss factorials*,
  Amer. Math. Monthly 118 (2011), 812–829.
- E. Costa, R. Gerbicz, D. Harvey, *A search for Wilson primes*,
  Math. Comp. 83 (2014), 3071–3091.
- R. Crandall, K. Dilcher, C. Pomerance, *A search for Wieferich and Wilson
  primes*, Math. Comp. 66 (1997), 433–449.
- D. S. Dummit, D. Ford, H. Kisilevsky, J. W. Sands, *Computation of
  Iwasawa lambda invariants for imaginary quadratic fields*,
  J. Number Theory 37 (1991), 100–121.
- E. Dobrowolski, *On a question of Lehmer and the number of irreducible
  factors of a polynomial*, Acta Arith. 34 (1979), 391–401.
- F. G. Dorais, D. Klyve, *A Wieferich prime search up to 6.7 × 10¹⁵*,
  J. Integer Seq. 14 (2011), Article 11.9.2.
- R. Gold, *The nontriviality of certain ℤ_l-extensions*,
  J. Number Theory 6 (1974), 369–373.
- D. H. Lehmer, *Factorization of certain cyclotomic functions*,
  Ann. of Math. 34 (1933), 461–479.
- M. Lerch, *Zur Theorie des Fermatschen Quotienten (a^(p−1) − 1)/p = q(a)*,
  Math. Ann. 60 (1905), 471–490.
- J. McKee, C. Smyth, *There are Salem numbers of every trace*,
  Bull. London Math. Soc. 37 (2005), 25–36.
- C. T. McMullen, *Coxeter groups, Salem numbers and the Hilbert metric*,
  Publ. Math. IHÉS 95 (2002), 151–183.
- W. G. McCallum, R. T. Sharifi, *A cup product in the Galois
  cohomology of number fields*, Duke Math. J. 120 (2003), 269–310.
- M. J. Mossinghoff, *Polynomials with small Mahler measure*,
  Math. Comp. 67 (1998), 1697–1705.
- T. A. Pierce, *The numerical factors of the arithmetic forms
  ∏(1 ± αᵢᵐ)*, Ann. of Math. 18 (1916), 53–64.
- P. Qi, *Iwasawa λ invariant and Massey product*, arXiv:2402.06028
  (2024).
- R. M. Robinson, *Algebraic equations with span less than 4*,
  Math. Comp. 18 (1964), 547–559.
- A. Schinzel, *On primitive prime factors of aⁿ − bⁿ*,
  Proc. Cambridge Philos. Soc. 58 (1962), 555–562.
- J. H. Silverman, *Wieferich's criterion and the abc-conjecture*,
  J. Number Theory 30 (1988), 226–237.
- C. M. Stokes, *A characterisation of Iwasawa invariants of imaginary
  quadratic fields*, arXiv:2207.07804 (2022).
- Z.-H. Sun, Z.-W. Sun, *Fibonacci numbers and Fermat's last theorem*,
  Acta Arith. 60 (1992), 371–388.
- D. D. Wall, *Fibonacci series modulo m*, Amer. Math. Monthly 67 (1960),
  525–532.
- A. Wieferich, *Zum letzten Fermatschen Theorem*, J. Reine Angew. Math.
  136 (1909), 293–302.
- K. Zsygmondy, *Zur Theorie der Potenzreste*, Monatsh. Math. Phys. 3
  (1892), 265–284.
- Data sources: OEIS A001220, A045616, A173656, A239902, A061442, A061443,
  A061445, A008555; factordb.com; the PrimeGrid Wieferich and Wall–Sun–Sun
  searches.

## Provenance and reproduction

One command re-runs each census (C kernels; seeds and shard ranges
recorded); one `lake build` re-checks every certificate. The Lean
companion lives in this repository (`WieferichFamilies/`, Mathlib-only).
Cross-repository companions: `salem-tower` (the tower program),
`cyclotomic-orders` (cyclotomic values at integer bases; the
parity-tower law and the Glaisher band-sum layer),
`lehmer-e10` (irreducibility and the E₁₀ identity), and `bsd-complex`
(the Iwasawa-side ladders). The fifteen primes of §3.4 re-prove with
PARI/GP (`isprime`, APR-CL) from `data/tower_primes/`. Method details and
kernel-defect disclosures: `PROVENANCE.md`.
