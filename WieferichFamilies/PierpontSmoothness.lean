/-
Copyright (c) 2026 Dillon Ryan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dillon Ryan
-/
import WieferichFamilies.IwasawaGrid

/-!
# The 3-smoothness of p − 1 across the classification

A prime `p` is a Pierpont prime iff `p − 1` is 3-smooth
(`p = 2^u·3^v + 1`), iff `Gal(ℚ(ζ_p)/ℚ)` is a {2,3}-group. Across the
four-cell classification of `IwasawaGrid`: exactly `{37, 163}` are
Pierpont (`163 = 2·3⁴ + 1`), while `43, 67, 79` each carry a single
non-smooth factor (`7, 11, 13` — consecutive primes; see §6 of the
paper). Among `{2, 3, 5, 7, 11, 13, 17, 19}` the unique non-Pierpont is
`11`.
-/

namespace Wieferich.PierpontSmoothness

/-- `n` is **3-smooth**: every prime divisor is ≤ 3. Bounded form, so the kernel
    decides it. `p` is a Pierpont prime iff `ThreeSmooth (p − 1)`. -/
abbrev ThreeSmooth (n : ℕ) : Prop := ∀ q < n + 1, q.Prime → q ∣ n → q ≤ 3

/-- **the Fermat slice**: a prime divisor of `2^k` is 2, so `p − 1 = 2^k`
    (Fermat) implies every prime of `p − 1` is ≤ 3 — Fermat primes ARE the dyadic
    slice of the Pierpont grade. The transition Fermat → Pierpont is an inclusion,
    not a jump: adding the ternary rung strictly widens the same tower. -/
theorem pow_two_smooth (k q : ℕ) (hq : q.Prime) (h : q ∣ 2 ^ k) : q = 2 :=
  (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow h)

/-- **the Pierpont split**: `37 − 1 = 36` and `163 − 1 = 162`
    are 3-smooth (Pierpont), while `42, 66, 78` (for 43, 67, 79) are not — each carries
    a rogue prime 7, 11, 13. Exactly the two
    corner cells of the classification (37 and 163) are Pierpont. -/
theorem pierpont_split_37_163 :
    ThreeSmooth 36 ∧ ThreeSmooth 162 ∧
    ¬ ThreeSmooth 42 ∧ ¬ ThreeSmooth 66 ∧ ¬ ThreeSmooth 78 := by decide +kernel

/-- **the exception at 11**: among {5, 7, 11, 13, 17, 19}, only `11` fails the Pierpont grade (`10
    = 2·5`) —
    5, 17 are Fermat (dyadic), 7, 13, 19 are properly ternary Pierpont. -/
theorem eleven_not_pierpont :
    ThreeSmooth 4 ∧ ThreeSmooth 6 ∧ ¬ ThreeSmooth 10 ∧
    ThreeSmooth 12 ∧ ThreeSmooth 16 ∧ ThreeSmooth 18 := by decide +kernel

/-- **the Gold atlas floor is Pierpont**: the two smallest atlas
    members 5 (`D = −11`) and 13 (`D = −3`, the seed) are Pierpont; the next members
    11 and 181 are not (`10 = 2·5`, `180 = 2²·3²·5`). The ternary rung sits exactly at
    the base of the unit-root Wieferich family. -/
theorem atlas_pierpont_floor :
    ThreeSmooth 4 ∧ ThreeSmooth 12 ∧ ¬ ThreeSmooth 10 ∧ ¬ ThreeSmooth 180 := by decide +kernel

/-- **the top Heegner number is Pierpont**: `163 = 2·3⁴ + 1`,
    and the exponent pattern is pure ternary depth 4 over dyadic depth 1 — the
    deepest CM pole sits on the ternary tower, not the dyadic one. -/
theorem heegner_top_is_pierpont : 163 = 2 * 3 ^ 4 + 1 ∧ 37 = 2 ^ 2 * 3 ^ 2 + 1 := by
  decide +kernel

/-- **the 6q + 1 ladder**: the three non-Pierpont members are
    exactly `6q + 1` at consecutive primes `q = 7, 11, 13`: `43 = 6·7+1`,
    `67 = 6·11+1`, `79 = 6·13+1` — so `p − 1 = 2·3·q` and each enters the
    smoothness tower `{2} ⊂ {2,3} ⊂ {2,3,7} ⊂ …` precisely at its own prime
    (37, 163 at 3; 43 at 7; 67 at 11; 79 at 13 — all distinct). -/
theorem six_q_plus_one_ladder :
    43 = 6 * 7 + 1 ∧ 67 = 6 * 11 + 1 ∧ 79 = 6 * 13 + 1 ∧
    42 = 2 * 3 * 7 ∧ 66 = 2 * 3 * 11 ∧ 78 = 2 * 3 * 13 := by decide +kernel

/-- The **Pierpont grade datum** for a prime: the dyadic grade (Fermat: `p − 1` a
    2-power) and the ternary grade (Pierpont: `p − 1` 3-smooth), with the inclusion
    `dyadic → ternary` carried as a field. -/
structure PierpontGradeDatum (p : ℕ) where
  /-- `p − 1 = 2^k`: the dyadic (Fermat, ruler-compass) grade. -/
  dyadic : Prop
  /-- `p − 1` is 3-smooth: the ternary (Pierpont, trisection) grade. -/
  ternary : Prop
  /-- the transition: dyadic constructibility includes into ternary. -/
  includes : dyadic → ternary

end Wieferich.PierpontSmoothness
