import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Expand
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.ZMod.Basic

/-!
# The certified zone

If every prime factor of `N` is at least `b` and `N < b²`, then `N` is
prime: a composite `N` would have a prime factor below `√N`. When the
factor floor is supplied by a congruence sieve — as it is for primitive
parts of cyclotomic values, whose prime factors are `≡ 1 (mod n)` — values
below `(n+1)²` are prime by construction, with no primality test involved.
This is the elementary half of the classical `N − 1` method of Brillhart,
Lehmer, and Selfridge (Math. Comp. 29, 1975).

## Main results

* `certified_zone`: factor floor `b` and `N < b²` imply `N.Prime`.
* `certified_zone_modeq`: the congruence form, floor `n + 1` from
  `q ≡ 1 (mod n)`.
* `dvd_sub_one_of_orderOf`: for prime `N`, a unit of order `n` in
  `ZMod N` forces `n ∣ N − 1` — the entry point for `N − 1`
  factorization beyond the quadratic zone.
* `vZ`, `dZ`, the Aurifeuillian seam (`aurifHalf_product`,
  `aurifHalfP_seam`, `goldHalfP_seam`): the closed factorizations of §3 of
  the paper, including `H± − 1 = 5·F_m·(F_m ± 1)`.
-/

namespace Wieferich.CertifiedZone

/-- **The certified zone.** If every prime factor of `N` is at least `b`
and `N < b ^ 2`, then `N` is prime: a composite `N` would have its least
prime factor below `√N < b`, against the sieve. Zero primality testing —
the sieve and the size bound are the whole certificate. -/
theorem certified_zone {N b : ℕ} (h1 : 1 < N)
    (hb : ∀ q : ℕ, q.Prime → q ∣ N → b ≤ q) (hN : N < b ^ 2) :
    N.Prime := by
  by_contra hnp
  have hsq : N.minFac ^ 2 ≤ N :=
    Nat.minFac_sq_le_self (Nat.lt_of_lt_of_le Nat.zero_lt_one h1.le) hnp
  have hble : b ≤ N.minFac :=
    hb N.minFac (Nat.minFac_prime (Nat.ne_of_gt h1)) (Nat.minFac_dvd N)
  have : b ^ 2 ≤ N := le_trans (Nat.pow_le_pow_left hble 2) hsq
  omega

/-- Floor extraction from the Zsygmondy congruence: a prime `q ≡ 1 (mod n)`
with `n ≥ 1` is either `1` (impossible) or at least `n + 1`. -/
theorem le_of_modeq_one {q n : ℕ} (hq : q.Prime)
    (h : q ≡ 1 [MOD n]) : n + 1 ≤ q := by
  have h2 : 2 ≤ q := hq.two_le
  have hdvd : n ∣ q - 1 := (Nat.modEq_iff_dvd' hq.one_lt.le).mp h.symm
  rcases Nat.eq_zero_or_pos (q - 1) with h0 | hpos
  · omega
  · have := Nat.le_of_dvd hpos hdvd
    omega

/-- **Certified zone, congruence form.** If every prime factor of `N` is
`≡ 1 (mod n)` — exactly what the extrinsic layer of the Zsygmondy sieve
proves for primitive parts — then `1 < N < (n+1)²` forces `N` prime. -/
theorem certified_zone_modeq {N n : ℕ} (h1 : 1 < N)
    (hq : ∀ q : ℕ, q.Prime → q ∣ N → q ≡ 1 [MOD n])
    (hN : N < (n + 1) ^ 2) : N.Prime :=
  certified_zone h1 (fun q hqp hqd => le_of_modeq_one hqp (hq q hqp hqd)) hN

/-- **The closure driver.** For prime `N`, any unit of `ZMod N` of order `n`
forces `n ∣ N − 1`. This is why a tower rung that IS prime hands its own
index to the `N − 1` side: the factored-structure program (Pocklington past
the quadratic zone) starts from this divisibility. -/
theorem dvd_sub_one_of_orderOf {N : ℕ} (hN : N.Prime)
    (u : (ZMod N)ˣ) : orderOf u ∣ N - 1 := by
  haveI : Fact N.Prime := ⟨hN⟩
  have hcard : Fintype.card (ZMod N)ˣ = N - 1 := by
    rw [ZMod.card_units_eq_totient, Nat.totient_prime hN]
  exact hcard ▸ orderOf_dvd_card

end Wieferich.CertifiedZone

/-! ## The rung-doubling closure (the Aurifeuillian-style identity)

The census found rung-doubling pairs — (261, 522), (291, 582),
(109, 218) — where certification propagates from rung n to rung 2n. The
algebraic engine is the Lucas V-sequence doubling law `V_{2n} = V_n² − 2(−1)ⁿ`
(Q = −1, the metallic family): the shifted value at a doubled rung is a
square shifted by 2, hence factors through the half rung. Proven here from
the recurrence alone, via the Catalan invariant. -/

/-- Integer Lucas V-sequence of `x² − kx − 1`: `V 0 = 2`, `V 1 = k`,
`V (n+2) = k·V (n+1) + V n`. -/
def vZ (k : ℤ) : ℕ → ℤ
  | 0 => 2
  | 1 => k
  | (n+2) => k * vZ k (n+1) + vZ k n

@[simp] lemma vZ_zero (k : ℤ) : vZ k 0 = 2 := rfl
@[simp] lemma vZ_one (k : ℤ) : vZ k 1 = k := rfl
lemma vZ_add_two (k : ℤ) (n : ℕ) : vZ k (n+2) = k * vZ k (n+1) + vZ k n := rfl

/-- Catalan invariant of the metallic V-sequence:
`V_n·V_{n+2} − V_{n+1}² = (−1)ⁿ·(k² + 4)`. -/
lemma vZ_catalan (k : ℤ) : ∀ n : ℕ,
    vZ k n * vZ k (n+2) - vZ k (n+1) ^ 2 = (-1) ^ n * (k ^ 2 + 4)
  | 0 => by simp [vZ_add_two]; ring
  | (n+1) => by
    have ih := vZ_catalan k n
    rw [vZ_add_two k (n+1), vZ_add_two k n, pow_succ]
    rw [vZ_add_two k n] at ih
    ring_nf
    ring_nf at ih
    linarith [ih]

/-- **Rung-doubling law** (even and odd companions, simultaneous induction):
`V_{2n} = V_n² − 2(−1)ⁿ` and `V_{2n+1} = V_n·V_{n+1} − k(−1)ⁿ`. -/
theorem vZ_double_pair (k : ℤ) : ∀ n : ℕ,
    vZ k (2*n) = vZ k n ^ 2 - 2 * (-1) ^ n ∧
    vZ k (2*n+1) = vZ k n * vZ k (n+1) - k * (-1) ^ n
  | 0 => by constructor <;> simp <;> ring
  | (n+1) => by
    obtain ⟨h1, h2⟩ := vZ_double_pair k n
    have hcat := vZ_catalan k n
    rw [vZ_add_two k n] at hcat
    have e2 : 2*(n+1) = (2*n) + 2 := by ring
    have heven : vZ k (2*(n+1)) = vZ k (n+1) ^ 2 - 2 * (-1) ^ (n+1) := by
      rw [e2, vZ_add_two, h1, h2, pow_succ]
      linear_combination hcat
    refine ⟨heven, ?_⟩
    have e3 : 2*(n+1)+1 = (2*n+1) + 2 := by ring
    have : vZ k (2*(n+1)+1) = k * vZ k (2*n+2) + vZ k (2*n+1) := by
      rw [e3, vZ_add_two]
    rw [this, show (2*n+2 : ℕ) = 2*(n+1) by ring, heven, h2, vZ_add_two, pow_succ]
    ring

/-- The even form in subtraction-free shape: at even doubling steps the
half-rung square exceeds the doubled rung by exactly 2 — the shifted value
`V_{2n} + 2` IS the square `V_n²`, so every factor of the doubled shifted
value lives at the half rung. -/
theorem vZ_double_even (k : ℤ) (n : ℕ) (hn : Even n) :
    vZ k (2*n) + 2 = vZ k n ^ 2 := by
  have := (vZ_double_pair k n).1
  rw [hn.neg_one_pow] at this
  omega

/-! ## The square-lane identity

`Φ_{4m}(x) = Φ_{2m}(x²)` — the cyclotomic engine of the metallic 4∣n square
law: evaluating at a norm(−1) unit α, the argument α² is a norm(+1)
(reciprocal) unit, so the primitive part is a norm of a reciprocal value and
the reciprocal square law reactivates lane-wise. 444/444 metallic
rungs verified; here is the polynomial identity feeding it. -/

theorem cyclotomic_four_mul_eval (m : ℕ) (hm : 0 < m) (x : ℤ) :
    (Polynomial.cyclotomic (4*m) ℤ).eval x
      = (Polynomial.cyclotomic (2*m) ℤ).eval (x^2) := by
  have h2 : (2:ℕ).Prime := Nat.prime_two
  have hdvd : 2 ∣ 2*m := ⟨m, rfl⟩
  have hexp := Polynomial.cyclotomic_expand_eq_cyclotomic (R := ℤ) h2 hdvd
  have h4 : 2*m*2 = 4*m := by ring
  calc (Polynomial.cyclotomic (4*m) ℤ).eval x
      = (Polynomial.cyclotomic (2*m*2) ℤ).eval x := by rw [h4]
    _ = (Polynomial.expand ℤ 2 (Polynomial.cyclotomic (2*m) ℤ)).eval x := by rw [hexp]
    _ = (Polynomial.cyclotomic (2*m) ℤ).eval (x^2) := by
        rw [Polynomial.expand_eval]

/-! ## The re-indexing identity

For the metallic family (αβ = −1), `Δ_n = (α^n−1)(β^n−1) = (−1)^n + 1 − V_n`.
At odd n this is `−V_n`, so `Δ_{2n} = −Δ_n²` — the doubled rung carries the
SAME primitive content re-indexed (silver Λ₂₉₁ = Λ₅₈₂, one 74-digit prime).
Formalized on the V-sequence: no phenomenon, an identity. -/

/-- `dZ k n = (−1)^n + 1 − V_n` — the norm form `(α^n−1)(β^n−1)` of the
metallic unit, expressed through the V-sequence. -/
def dZ (k : ℤ) (n : ℕ) : ℤ := (-1)^n + 1 - vZ k n

/-- At odd rungs the norm form is exactly `−V_n`. -/
theorem dZ_odd (k : ℤ) {n : ℕ} (hn : Odd n) : dZ k n = -(vZ k n) := by
  unfold dZ
  rw [hn.neg_one_pow]
  ring

/-- **Re-indexing identity**: for odd n, `Δ_{2n} = −Δ_n²` — doubling squares
the norm form, so the primitive part at rung 2n repeats the rung-n prime. -/
theorem dZ_double_odd (k : ℤ) {n : ℕ} (hn : Odd n) :
    dZ k (2*n) = -(dZ k n)^2 := by
  have hv := (vZ_double_pair k n).1
  rw [hn.neg_one_pow] at hv
  have he : Even (2*n) := even_two_mul n
  unfold dZ
  rw [he.neg_one_pow, hv, hn.neg_one_pow]
  ring

/-! ## Aurifeuillian half-primes

The gold fission law: `Λ_{5m} = (H₊/s₊)(H₋/s₋)` with `H± = 5F_m² ± 5F_m + 1`
(strays = rank-of-apparition primes). The three ring identities below are the
algebraic skeleton: the product law, and the two SEAMS — the shifted half-value
factors by construction into Fibonacci neighbours, `H₊ − 1 = 5F(F+1)`,
handing every half-prime its own N−1 certificate vocabulary. -/

/-- The Aurifeuillian half-forms of the golden tower. -/
def aurifHalfP (x : ℤ) : ℤ := 5*x^2 + 5*x + 1
def aurifHalfM (x : ℤ) : ℤ := 5*x^2 - 5*x + 1

/-- Product law: `H₊·H₋ = 25x⁴ − 15x² + 1` (the quartic under `Λ_{5m}`). -/
theorem aurifHalf_product (x : ℤ) :
    aurifHalfP x * aurifHalfM x = 25*x^4 - 15*x^2 + 1 := by
  unfold aurifHalfP aurifHalfM; ring

/-- Seam (+): the shifted half factors into neighbours, `H₊ − 1 = 5x(x+1)`. -/
theorem aurifHalfP_seam (x : ℤ) : aurifHalfP x - 1 = 5*x*(x+1) := by
  unfold aurifHalfP; ring

/-- Seam (−): `H₋ − 1 = 5x(x−1)`. -/
theorem aurifHalfM_seam (x : ℤ) : aurifHalfM x - 1 = 5*x*(x-1) := by
  unfold aurifHalfM; ring

/-- Nat form on Fibonacci: the half-prime candidate at index m. -/
def goldHalfP (m : ℕ) : ℕ := 5*(Nat.fib m)^2 + 5*Nat.fib m + 1

/-- The N−1 side of a gold half-prime is `5·F_m·(F_m+1)` BY CONSTRUCTION —
the certificate seam is definitional. -/
theorem goldHalfP_seam (m : ℕ) :
    goldHalfP m - 1 = 5 * Nat.fib m * (Nat.fib m + 1) := by
  unfold goldHalfP
  have h : 5*(Nat.fib m)^2 + 5*Nat.fib m = 5 * Nat.fib m * (Nat.fib m + 1) := by ring
  omega

/-! ## The freeze lemma

Iterating a p-adically contracting map never deepens a congruence: if
`f a − f b` gains a factor `p` over `a − b` (whenever `p ∣ a − b`), then the
exact valuation of `f k − k` is preserved by iteration — the census measured
`e_j = D` for all j at 0/40 exceptions; here is the mechanism. The Dickson
diagonal satisfies the hypothesis (its divided differences are ≡ 0 mod p on
p-adically close pairs), so the metallic filtration tower is FROZEN. -/

/-- One-step freeze: exact valuation `D` of `f k − k` survives one iterate. -/
theorem freeze_step {f : ℤ → ℤ} {p k : ℤ} {D : ℕ}
    (hcontr : ∀ a b : ℤ, p ∣ (a - b) → (a - b) * p ∣ f a - f b)
    (hD1 : 1 ≤ D)
    (hD : p ^ D ∣ f k - k) (hDe : ¬ p ^ (D + 1) ∣ f k - k) :
    p ^ D ∣ f (f k) - k ∧ ¬ p ^ (D + 1) ∣ f (f k) - k := by
  have hp1 : p ∣ f k - k := by
    have : (p : ℤ) ^ 1 ∣ p ^ D := pow_dvd_pow p hD1
    exact dvd_trans (by simpa using this) hD
  have hstep : (f k - k) * p ∣ f (f k) - f k := hcontr (f k) k hp1
  have hdeep : p ^ (D + 1) ∣ f (f k) - f k :=
    dvd_trans (by rw [pow_succ]; exact mul_dvd_mul hD dvd_rfl) hstep
  constructor
  · have h1 : p ^ D ∣ f (f k) - f k := dvd_trans (pow_dvd_pow p (Nat.le_succ D)) hdeep
    have := dvd_add h1 hD
    simpa [sub_add_sub_cancel] using this
  · intro hbad
    have : p ^ (D + 1) ∣ f k - k := by
      have hsub := dvd_sub hbad hdeep
      simpa [sub_sub_sub_cancel_left] using hsub
    exact hDe this

/-- The D = 5 Gauss-sum identity behind the golden fission law:
`Φ₅(x) = (x²+3x+1)² − 5x(x+1)²`. -/
theorem phi5_gauss (x : ℤ) :
    (x^2+3*x+1)^2 - 5*x*(x+1)^2 = x^4+x^3+x^2+x+1 := by ring
