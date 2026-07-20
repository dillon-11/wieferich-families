/-
Copyright (c) 2026 Dillon Ryan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dillon Ryan
-/
import WieferichFamilies.LiftDichotomy
import WieferichFamilies.Exclusions
import WieferichFamilies.ZsygmondyLTE
import Mathlib.Algebra.Polynomial.Roots

/-!
# Depth transfer lemmas

Four lemmas connecting the depth grading across its guises.

## Main results

* `metallic_no_collision`: the Lucas V-sequence of x² − kx − 1 is
  strictly increasing past `n = 1` for every `k ≥ 1`, so a Pisot unit of
  this family has no integer trace return (the Salem case is a finite
  check, `salem18_integer_collisions`).
* `orderOf_tower_of_ker_exponent_pow`: through a kernel of exponent
  `p^n`, orders lift by `p^j` with `j ≤ n` — the `n`-step form of the
  order-lift dichotomy.
* `emultiplicity_pow_prime_pow_sub_one`: the LTE ladder
  `v_q(x^(q^j) − 1) = v_q(x − 1) + j`.
* `unit_slope_root_multiplicity_one`: a unit-slope lift equation has a simple
  root; multiplicity above 1 forces degeneration off the generic stratum.
* `meterReading`, `meter_monotone_proximity`: the depth reading of the
  torsion grade of `TorsionGrading`, monotone in torsion proximity.
-/

namespace Wieferich.DepthTransfer

open Polynomial

/-! ## 1. No trace returns in the family x² − kx − 1 -/

/-- The metallic Lucas V-sequence: `V 0 = 2, V 1 = k, V (n+2) = k·V(n+1) + V n` —
    the integer trace sequence of the metallic unit x² − kx − 1. -/
def metallicV (k : ℕ) : ℕ → ℕ
  | 0 => 2
  | 1 => k
  | n + 2 => k * metallicV k (n + 1) + metallicV k n

lemma metallicV_pos {k : ℕ} (hk : 1 ≤ k) : ∀ n, 1 ≤ metallicV k n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => simp [metallicV]
    | 1 => simpa [metallicV] using hk
    | m + 2 =>
      have h1 := ih (m + 1) (by omega)
      simp only [metallicV]
      nlinarith

/-- Strict growth past the first step: `V n < V (n+1)` for `n ≥ 1, k ≥ 1`. -/
theorem metallicV_lt_succ {k : ℕ} (hk : 1 ≤ k) : ∀ n, 1 ≤ n →
    metallicV k n < metallicV k (n + 1) := by
  intro n hn
  match n, hn with
  | 1, _ =>
    change metallicV k 1 < metallicV k 2
    simp only [metallicV]
    nlinarith
  | m + 2, _ =>
    change metallicV k (m + 2) < metallicV k (m + 3)
    have h1 := metallicV_pos hk (m + 1)
    simp only [metallicV]
    have hA : k * metallicV k (m + 1) + metallicV k m
        ≤ k * (k * metallicV k (m + 1) + metallicV k m) :=
      Nat.le_mul_of_pos_left _ hk
    omega

lemma metallicV_one_lt {k : ℕ} (hk : 1 ≤ k) : ∀ n, 2 ≤ n →
    metallicV k 1 < metallicV k n := by
  intro n hn
  induction n with
  | zero => omega
  | succ m ih =>
    rcases Nat.lt_or_ge m 2 with hm | hm
    · interval_cases m
      · omega
      · exact metallicV_lt_succ hk 1 le_rfl
    · exact (ih (by omega)).trans (metallicV_lt_succ hk m (by omega))

/-- **Metallic silence, as a theorem** (the Pisot half of the closure grading):
    no metallic unit ever resonates — `V n ≠ V 1` for every `n ≥ 2, k ≥ 1`.
    Golden (k = 1) holds the longest window and, like every metallic, total
    silence; the emptiness is theorem-typed, not census-typed. -/
theorem metallic_no_collision {k : ℕ} (hk : 1 ≤ k) {n : ℕ} (hn : 2 ≤ n) :
    metallicV k n ≠ metallicV k 1 :=
  (metallicV_one_lt hk n hn).ne'

/-! ## 2. Order lifting through a kernel of exponent p^n -/

/-- **The n-rung climb theorem**: through a kernel of exponent `p^n`, orders lift
    by `p^j` for some `j ≤ n`. Generalizes `orderOf_dichotomy_of_ker_exponent`
    (n = 1). Each rung of the tower is a 1-or-p lift; a non-strict jump
    (j < rung count) is the Wieferich branch of the climb. -/
theorem orderOf_tower_of_ker_exponent_pow {G H : Type*} [Group G] [Group H]
    {p n : ℕ} (hp : p.Prime) (φ : G →* H)
    (hker : ∀ g : G, φ g = 1 → g ^ p ^ n = 1) (g : G)
    (hd : orderOf (φ g) ≠ 0) :
    ∃ j ≤ n, orderOf g = p ^ j * orderOf (φ g) := by
  set d := orderOf (φ g) with hdef
  have hdvd : d ∣ orderOf g := orderOf_map_dvd φ g
  have h1 : φ (g ^ d) = 1 := by rw [map_pow, hdef, pow_orderOf_eq_one]
  have h2 : (g ^ d) ^ p ^ n = 1 := hker _ h1
  have h3 : orderOf g ∣ d * p ^ n := orderOf_dvd_of_pow_eq_one (by rwa [← pow_mul] at h2)
  obtain ⟨k, hk⟩ := hdvd
  have hkp : k ∣ p ^ n := by
    have h4 : d * k ∣ d * p ^ n := hk ▸ h3
    exact (mul_dvd_mul_iff_left hd).mp h4
  obtain ⟨j, hj, rfl⟩ := (Nat.dvd_prime_pow hp).mp hkp
  exact ⟨j, hj, by rw [hk, mul_comm]⟩

/-! ## 3. The LTE ladder (riemann-roch budget / Dobrowolski core) -/

/-- **The LTE ladder**: `v_q(x^{q^j} − 1) = v_q(x − 1) + j` for odd prime q with
    q ∣ x − 1. The increment of the multiplicity budget up the q-power tower is
    exactly linear — baseline plus j, nothing else. This is the Lean core of the
    Dobrowolski depth law and the arithmetic part of the budget decomposition. -/
theorem emultiplicity_pow_prime_pow_sub_one {q : ℕ} (hq : q.Prime) (hodd : Odd q)
    {x : ℤ} (hx1 : (q : ℤ) ∣ x - 1) (j : ℕ) :
    emultiplicity (q : ℤ) (x ^ q ^ j - 1) = emultiplicity (q : ℤ) (x - 1) + j := by
  induction j with
  | zero => simp
  | succ m ih =>
    have hstep : (q : ℤ) ∣ x ^ q ^ m - 1 := by
      have h1 : x - 1 ∣ x ^ q ^ m - 1 := by
        simpa using sub_dvd_pow_sub_pow x 1 (q ^ m)
      exact hx1.trans h1
    have h2 : (x ^ q ^ m) ^ q = x ^ q ^ (m + 1) := by
      rw [← pow_mul, pow_succ]
    calc emultiplicity (q : ℤ) (x ^ q ^ (m + 1) - 1)
        = emultiplicity (q : ℤ) ((x ^ q ^ m) ^ q - 1) := by rw [h2]
      _ = emultiplicity (q : ℤ) (x ^ q ^ m - 1) + 1 :=
          Wieferich.ZsygmondyLTE.emultiplicity_prime_pow_sub_one hq hodd hstep
      _ = emultiplicity (q : ℤ) (x - 1) + m + 1 := by rw [ih]
      _ = emultiplicity (q : ℤ) (x - 1) + (m + 1) := by
          rw [add_assoc]

/-! ## 4. Equidistribution strata -/

/-- **Unit slope forces simple roots**: the lift equation `a·t = b` with
    unit slope, as a polynomial, has root multiplicity exactly 1. Multiplicity
    ≥ 2 requires vanishing slope. A multiple-zero claim is
    structurally a zero-slope claim. -/
theorem unit_slope_root_multiplicity_one {K : Type*} [Field K] {a b : K} (ha : a ≠ 0) :
    (C a * X - C b).rootMultiplicity (a⁻¹ * b) = 1 := by
  have hP0 : (C a * X - C b : Polynomial K) ≠ 0 := by
    intro h
    have hc : (C a * X - C b : Polynomial K).coeff 1 = 0 := by rw [h]; simp
    rw [coeff_sub, coeff_C_mul, coeff_X_one, mul_one, coeff_C, if_neg one_ne_zero,
      sub_zero] at hc
    exact ha hc
  have hdeg : (C a * X - C b : Polynomial K).natDegree = 1 := by
    compute_degree!
  have hroot : (C a * X - C b : Polynomial K).IsRoot (a⁻¹ * b) := by
    simp only [IsRoot.def, eval_sub, eval_mul, eval_C, eval_X]
    rw [mul_inv_cancel_left₀ ha, sub_self]
  have hge : 1 ≤ (C a * X - C b : Polynomial K).rootMultiplicity (a⁻¹ * b) :=
    (rootMultiplicity_pos hP0).mpr hroot
  have hle : (C a * X - C b : Polynomial K).rootMultiplicity (a⁻¹ * b) ≤ 1 := by
    have hdvd := pow_rootMultiplicity_dvd (C a * X - C b : Polynomial K) (a⁻¹ * b)
    have hle' := natDegree_le_of_dvd hdvd hP0
    rw [natDegree_pow, natDegree_X_sub_C, hdeg] at hle'
    omega
  omega

/-! ## 5. The depth reading of the torsion grade -/

/-- The depth reading of each torsion grade: exact torsion has infinite
    depth, perturbed torsion depth 3, kernel-only depth 0. -/
def meterReading : Wieferich.Exclusions.CollapseGrade → ℕ∞
  | .exactTorsion => ⊤
  | .perturbedTorsion => 3
  | .kernelOnly => 0

/-- The meter agrees with the depth signature: `∞` where `gradeDepth` is `none`,
    the exact depth elsewhere. -/
theorem meter_matches_grade :
    ∀ g : Wieferich.Exclusions.CollapseGrade,
      meterReading g = (Wieferich.Exclusions.gradeDepth g).elim ⊤ (↑·) := by
  intro g
  cases g <;> rfl

/-- Torsion proximity (2 = exact, 1 = perturbed, 0 = kernel-only). -/
def proximity : Wieferich.Exclusions.CollapseGrade → ℕ
  | .exactTorsion => 2
  | .perturbedTorsion => 1
  | .kernelOnly => 0

/-- Depth is monotone in torsion proximity. -/
theorem meter_monotone_proximity :
    ∀ g h : Wieferich.Exclusions.CollapseGrade,
      proximity g ≤ proximity h → meterReading g ≤ meterReading h := by
  intro g h
  cases g <;> cases h <;> decide

end Wieferich.DepthTransfer
