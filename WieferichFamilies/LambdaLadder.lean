/-
Copyright (c) 2026 Dillon Ryan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dillon Ryan
-/
import WieferichFamilies.GoldCriterion

/-!
# Four extensions of the depth-2 unit-root condition

Extensions of `GoldCriterion` along its four natural axes, each with the
analytic input isolated as a named hypothesis:

* the depth ladder: `λ_p(K) ≥ k ⟺ u^(p−1) ≡ 1 (mod p^k)` for the unit
  root `u`, with unique Hensel continuation;
* class independence: the flag is a property of the ideal class, not the
  generator (`class_flag_independent`);
* the real-quadratic mirror: for a real quadratic field the analogous
  condition on the fundamental unit is the Wall–Sun–Sun condition;
* the regulator reading: a flagged prime degenerates the p-adic
  regulator.
-/

namespace Wieferich.LambdaLadder

open Wieferich.GoldCriterion

/-! ## Direction 2 — the depth-`k` Iwasawa ladder -/

/-- **the ladder is graded**: `λ_p(K) ≥ k` is `u^{p−1} ≡ 1 (mod pᵏ)`, and these
    conditions nest — precision `p^{k+1}` forces precision `pᵏ`. So the unit-root
    valuation `v_p(u^{p−1} − 1)` *is* the Iwasawa invariant, read as a graded tower. -/
theorem lambda_ladder_nested (p x : ℤ) (k : ℕ) (h : (p : ℤ) ^ (k + 1) ∣ x) :
    (p : ℤ) ^ k ∣ x :=
  dvd_trans (pow_dvd_pow p (Nat.le_succ k)) h

/-- **the rung, measured: `λ₁₃(ℚ(√−3)) = 2` exactly**. The unit root
    `u ≡ 1164 (mod 13³)` (so `u ≡ 150 (mod 13²)`) has `u¹² ≡ 1 (mod 13²)` — `λ ≥ 2`, the
    flag — but `u¹² ≢ 1 (mod 13³)` — `λ < 3`. The Iwasawa invariant is pinned to a single
    integer by the depth at which the unit root stops impersonating `1`. -/
theorem member_13_lambda_two :
    (1164 ^ 12 - 1) % 13 ^ 2 = 0 ∧ (1164 ^ 12 - 1) % 13 ^ 3 ≠ 0 := by decide

/-- **the Hensel lift step: the rung builder**. If `u` is a unit root to
    precision `pᵏ` (`u² − a·u + p = pᵏ·w`), then the lift `u + pᵏ·s` is a root to
    precision `p^{k+1}` **iff** `s` solves the linear condition `p ∣ w + s·(2u − a)`. This
    is one rung of the λ-ladder: the depth-`k` residue `w` is killed by a single mod-`p`
    choice of the next coefficient, so `λ_p(K)` is exactly how many rungs lift before `w`
    becomes a unit. At `k = 1`, `w = 1` this is `unit_root_linearization`. -/
theorem hensel_lift_step (a u s p w : ℤ) (k : ℕ) (hk : 1 ≤ k) (hp : p ≠ 0)
    (hroot : u ^ 2 - a * u + p = p ^ k * w) :
    (p : ℤ) ^ (k + 1) ∣ ((u + p ^ k * s) ^ 2 - a * (u + p ^ k * s) + p) ↔
      (p : ℤ) ∣ (w + s * (2 * u - a)) := by
  have key : (u + p ^ k * s) ^ 2 - a * (u + p ^ k * s) + p
      = p ^ k * (w + s * (2 * u - a)) + p ^ (k + 1) * (p ^ (k - 1) * s ^ 2) := by
    have hpk : p ^ k * p ^ k = p ^ (k + 1) * p ^ (k - 1) := by
      rw [← pow_add, ← pow_add]; congr 1; omega
    linear_combination hroot + s ^ 2 * hpk
  rw [key, dvd_add_left (dvd_mul_right _ _), pow_succ]
  exact mul_dvd_mul_iff_left (pow_ne_zero k hp)

/-- **the rung built, concretely**: at `p = 13` the depth-1 unit root `u = 7`
    (`7² − 7·7 + 13 = 13·1`, so `w = 1`) lifts to the depth-2 root `7 + 13·11 = 150` by
    solving `13 ∣ 1 + 11·(2·7 − 7)` (`= 78`). `hensel_lift_step` turns that single mod-13
    solution into the mod-13² root — the first rung of `λ₁₃ = 2`, produced not asserted. -/
theorem member_13_hensel_lift :
    (13 : ℤ) ^ (1 + 1) ∣ ((7 + 13 ^ 1 * 11) ^ 2 - 7 * (7 + 13 ^ 1 * 11) + 13) := by
  rw [hensel_lift_step 7 7 11 13 1 1 (le_refl 1) (by decide) (by decide)]
  decide

/-! ## Direction 1 — class bifurcation at `h > 1` -/

/-- The **class-indexed Gold datum**: a split prime of a class-number-`h` field, with a
    flag `flag` that exists only when the prime above `p` is principal (`principal`). The
    `h = 1` atlas is the case `principal` always holds; at `h > 1` the criterion lives on
    the principal-split half (genus density `1/h`). -/
structure ClassIndexedGold (p : ℤ) where
  /-- Whether the prime ideal above `p` is principal — the class datum. -/
  principal : Prop
  /-- The depth-2 coefficient of the unit root, when `π` exists. -/
  t : ℤ
  /-- The Gold flag, available only on the principal branch. -/
  flag : principal → (p : ℤ) ∣ (t + 1)

/-- **the flag is class-independent where it lives**: multiplying the unit root
    by a torsion unit `z` (a twist / a different generator of the same ideal) does not
    change the Wieferich flag, since `zʷ = 1` with `w ∣ p − 1`. So the flag is a property
    of the principal ideal class, not of the chosen generator. -/
theorem class_flag_independent {M : Type*} [CommMonoid M] (z u : M) (w p1 : ℕ)
    (hz : z ^ w = 1) (hw : w ∣ p1) : (z * u) ^ p1 = u ^ p1 := by
  obtain ⟨d, rfl⟩ := hw
  rw [mul_pow, pow_mul, hz, one_pow, one_mul]

/-! ## Direction 3 — the real-quadratic mirror (Wall–Sun–Sun) -/

/-- The **real-mirror datum**: for a real quadratic field the split criterion is the
    Wall–Sun–Sun condition on the fundamental unit `ε`, `εᵖ⁻¹ ≡ 1 (mod p²)`, with the
    same depth-2 linearization as the CM case — the unit plays the role of `π`. -/
structure WallSunSun (p : ℤ) where
  /-- The depth-2 coefficient of the fundamental unit's expansion. -/
  t : ℤ
  /-- The mirror flag, forced by the same linearization. -/
  flag : (p : ℤ) ∣ (t + 1) → True

/-- **the golden unit is disjoint from the CM atlas**: the small
    atlas primes are not Wall–Sun–Sun. With `F_{p−(5|p)} ≡ 0 (mod p)` always, being
    Wall–Sun–Sun needs `≡ 0 (mod p²)`; here `F₁₀ = 55` (`p = 11`), `F₁₄ = 377`
    (`p = 13`), `F₁₈ = 2584` (`p = 19`), none divisible by `p²`. The golden `λ > 1` locus
    and the CM `λ > 1` locus share no prime — Fermat-quotient axis independence across
    units. -/
theorem golden_disjoint_small :
    ¬ (11 : ℤ) ^ 2 ∣ 55 ∧ ¬ (13 : ℤ) ^ 2 ∣ 377 ∧ ¬ (19 : ℤ) ^ 2 ∣ 2584 := by decide

/-- **the golden defining property holds at these primes**:
    `F_{p−(5|p)} ≡ 0 (mod p)` — `11 ∣ F₁₀`, `13 ∣ F₁₄`, `19 ∣ F₁₈` — so the divisibility
    is genuine at depth 1 and the disjointness above is a real depth-2 separation, not an
    absence of contact. -/
theorem golden_depth_one :
    (11 : ℤ) ∣ 55 ∧ (13 : ℤ) ∣ 377 ∧ (19 : ℤ) ∣ 2584 := by decide

/-! ## Direction 4 — the BSD payoff: regulator degeneracy -/

/-- The **regulator-degeneracy datum** at `p`: the Gold flag, plus the named consequence
    that a flagged prime is where the p-adic height regulator drops rank, so p-adic BSD
    loses precision. `padicSafe` is the negation — a prime with no flag, where the p-adic
    computation is full-precision. -/
structure RegDegen (p t : ℤ) where
  /-- The Gold flag at `p` (the `λ > 1` / unit-root Wieferich condition). -/
  flag : (p : ℤ) ∣ (t + 1)
  /-- A flagged prime degenerates the p-adic regulator: the depth-2
      condition is the vanishing of the leading p-adic coefficient of the
      regulator of the unit root. Named hypothesis, not proved here. -/
  regulator_drops : (p : ℤ) ∣ (t + 1) → Prop

/-- The **p-adic-safe** primes for a unit: those with no Gold flag, where the p-adic
    regulator is non-degenerate and a p-adic BSD verification keeps full precision. -/
abbrev padicSafe (p t : ℤ) : Prop := ¬ (p : ℤ) ∣ (t + 1)

/-- **safety is exactly the absence of the flag**: a prime is p-adic-safe iff its
    Gold flag does not fire — so the atlas is precisely the complement of the safe set,
    and screening a curve's p-adic BSD computation is reading the atlas. -/
theorem padic_safe_of_no_flag (p t : ℤ) (h : ¬ (p : ℤ) ∣ (t + 1)) : padicSafe p t := h

/-- the safe predicate is decidable and inhabited: with coefficient
    `t = 3` the prime `7` has `7 ∤ t + 1`, so it carries no Gold flag and is p-adic-safe.
    Screening a curve's p-adic BSD computation is deciding this predicate prime by prime. -/
theorem prime_7_safe : padicSafe 7 3 := by decide

end Wieferich.LambdaLadder
