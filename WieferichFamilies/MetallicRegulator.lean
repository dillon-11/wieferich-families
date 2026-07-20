import Mathlib.Analysis.Polynomial.MahlerMeasure
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The metallic family: Mahler measure = fundamental unit

For `k ≥ 1` the polynomial `x² − kx − 1` defines a real quadratic order
whose fundamental unit of norm −1 is the metallic mean
`(k + √(k²+4))/2` (golden mean at `k = 1`, silver at `k = 2`, and so
on). Its Mahler measure is exactly that unit — one root escapes the unit
disc, the other (`−1/ε`) stays inside — so

    `log M(x² − kx − 1) = the regulator of the order`.

The family is therefore the degree-2 stratum of Lehmer's problem in
closed form: the measure is monotone in `k` and its floor over `k ≥ 1`
is the golden ratio, attained at `k = 1`. This is the exact sense in
which the depth censuses over `x² − kx − 1` (the metallic family of the
paper) walk the fundamental-unit ladder of real quadratic fields.

## Main results

* `mahler_metallic`: `M(x² − kx − 1) = (k + √(k²+4))/2` for `k ≥ 0`.
* `mahler_golden`: `M(x² − x − 1) = (1 + √5)/2`.
* `golden_floor_deg2`: `(1 + √5)/2 ≤ M(x² − kx − 1)` for every `k ≥ 1`.
-/

namespace Wieferich.MetallicRegulator

open Polynomial

noncomputable section

/-- The metallic mean of parameter `t`: the escaped root of `x² − tx − 1`. -/
def metallic (t : ℝ) : ℝ := (t + Real.sqrt (t ^ 2 + 4)) / 2

/-- The conjugate root `−1/metallic`, inside the unit disc for `t ≥ 0`. -/
def metallicConj (t : ℝ) : ℝ := (t - Real.sqrt (t ^ 2 + 4)) / 2

lemma sqrt_sq_add_four (t : ℝ) : Real.sqrt (t ^ 2 + 4) ^ 2 = t ^ 2 + 4 :=
  Real.sq_sqrt (by positivity)

lemma metallic_add_conj (t : ℝ) : metallic t + metallicConj t = t := by
  unfold metallic metallicConj; ring

lemma metallic_mul_conj (t : ℝ) : metallic t * metallicConj t = -1 := by
  unfold metallic metallicConj
  have h := sqrt_sq_add_four t
  nlinarith [h]

/-- The escaped root dominates 1. -/
lemma one_le_metallic {t : ℝ} (ht : 0 ≤ t) : 1 ≤ metallic t := by
  have h2 : (2 : ℝ) ≤ Real.sqrt (t ^ 2 + 4) := by
    have h4 : Real.sqrt ((2 : ℝ) ^ 2) ≤ Real.sqrt (t ^ 2 + 4) :=
      Real.sqrt_le_sqrt (by nlinarith)
    rwa [Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)] at h4
  unfold metallic
  linarith

/-- The conjugate root stays inside the closed unit disc for `t ≥ 0`. -/
lemma abs_metallicConj_le_one {t : ℝ} (ht : 0 ≤ t) : |metallicConj t| ≤ 1 := by
  have hs0 : 0 ≤ Real.sqrt (t ^ 2 + 4) := Real.sqrt_nonneg _
  have hlt : t ≤ Real.sqrt (t ^ 2 + 4) := by
    have h4 : Real.sqrt (t ^ 2) ≤ Real.sqrt (t ^ 2 + 4) :=
      Real.sqrt_le_sqrt (by nlinarith)
    rwa [Real.sqrt_sq ht] at h4
  have hup : Real.sqrt (t ^ 2 + 4) ≤ t + 2 := by
    have h4 : Real.sqrt (t ^ 2 + 4) ≤ Real.sqrt ((t + 2) ^ 2) :=
      Real.sqrt_le_sqrt (by nlinarith)
    rwa [Real.sqrt_sq (by linarith : (0:ℝ) ≤ t + 2)] at h4
  have hneg : metallicConj t ≤ 0 := by unfold metallicConj; linarith
  rw [abs_of_nonpos hneg]
  unfold metallicConj
  linarith

/-- Monotonicity of the fundamental-unit ladder. -/
lemma metallic_mono {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) : metallic s ≤ metallic t := by
  have h : Real.sqrt (s ^ 2 + 4) ≤ Real.sqrt (t ^ 2 + 4) :=
    Real.sqrt_le_sqrt (by nlinarith)
  unfold metallic
  linarith

/-- The metallic polynomial `x² − kx − 1` over ℤ. -/
def metallicPoly (k : ℤ) : Polynomial ℤ := X ^ 2 - C k * X - 1

/-- Factorization of the metallic polynomial over ℂ through its two real
roots. -/
lemma metallicPoly_map_factor (k : ℤ) :
    (metallicPoly k).map (Int.castRingHom ℂ) =
      (X - C ((metallic (k : ℝ) : ℝ) : ℂ)) * (X - C ((metallicConj (k : ℝ) : ℝ) : ℂ)) := by
  set a : ℂ := ((metallic (k : ℝ) : ℝ) : ℂ) with ha
  set b : ℂ := ((metallicConj (k : ℝ) : ℝ) : ℂ) with hb
  have hab_add : a + b = ((k : ℝ) : ℂ) := by
    rw [ha, hb, ← Complex.ofReal_add, metallic_add_conj]
  have hab_mul : a * b = -1 := by
    rw [ha, hb, ← Complex.ofReal_mul, metallic_mul_conj]
    norm_num
  have hmap : (metallicPoly k).map (Int.castRingHom ℂ) =
      X ^ 2 - C ((k : ℝ) : ℂ) * X - 1 := by
    unfold metallicPoly
    have hc : (Int.castRingHom ℂ) k = ((k : ℝ) : ℂ) := by push_cast; norm_num
    rw [Polynomial.map_sub, Polynomial.map_sub, Polynomial.map_pow,
      Polynomial.map_mul, Polynomial.map_X, Polynomial.map_C, Polynomial.map_one, hc]
  rw [hmap]
  have hfac : (X - C a) * (X - C b) =
      (X : Polynomial ℂ) ^ 2 - C ((k : ℝ) : ℂ) * X - 1 := by
    calc (X - C a) * (X - C b)
        = X ^ 2 - (C a + C b) * X + C a * C b := by ring
      _ = X ^ 2 - C ((k : ℝ) : ℂ) * X - 1 := by
          rw [← Polynomial.C_add, hab_add, ← Polynomial.C_mul, hab_mul,
            Polynomial.C_neg, Polynomial.C_1]
          ring
  exact hfac.symm

/-- **The measure is the fundamental unit**:
`M(x² − kx − 1) = (k + √(k²+4))/2` for `k ≥ 0`, so `log M` is the
regulator of the norm-(−1) real quadratic order. -/
theorem mahler_metallic (k : ℤ) (hk : 0 ≤ k) :
    ((metallicPoly k).map (Int.castRingHom ℂ)).mahlerMeasure = metallic (k : ℝ) := by
  have hk' : (0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  rw [metallicPoly_map_factor k, mahlerMeasure_mul, mahlerMeasure_X_sub_C,
    mahlerMeasure_X_sub_C]
  have h1 : ‖((metallic (k : ℝ) : ℝ) : ℂ)‖ = metallic (k : ℝ) := by
    rw [Complex.norm_real]
    exact abs_of_nonneg (le_trans one_pos.le (one_le_metallic hk'))
  have h2 : ‖((metallicConj (k : ℝ) : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real]
    exact abs_metallicConj_le_one hk'
  rw [h1, max_eq_right (one_le_metallic hk'), max_eq_left h2, mul_one]

/-- **The golden instance**: `M(x² − x − 1) = (1 + √5)/2`. -/
theorem mahler_golden :
    ((metallicPoly 1).map (Int.castRingHom ℂ)).mahlerMeasure = (1 + Real.sqrt 5) / 2 := by
  rw [mahler_metallic 1 (by norm_num)]
  unfold metallic
  norm_num

/-- **The degree-2 floor**: on the fundamental-unit ladder the measure is
bounded below by the golden ratio — `(1+√5)/2 ≤ M(x² − kx − 1)` for every
`k ≥ 1`, with equality at `k = 1`. -/
theorem golden_floor_deg2 (k : ℤ) (hk : 1 ≤ k) :
    (1 + Real.sqrt 5) / 2 ≤ ((metallicPoly k).map (Int.castRingHom ℂ)).mahlerMeasure := by
  have hk0 : (0 : ℤ) ≤ k := by linarith
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  rw [mahler_metallic k hk0]
  have h := metallic_mono (by norm_num : (0:ℝ) ≤ 1) hk1
  have hg : metallic 1 = (1 + Real.sqrt 5) / 2 := by
    unfold metallic
    norm_num
  linarith [hg ▸ h]

end

end Wieferich.MetallicRegulator
