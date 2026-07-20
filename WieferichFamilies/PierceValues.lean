/-
Copyright (c) 2026 Dillon Ryan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dillon Ryan
-/
import WieferichFamilies.DobrowolskiBaseline
import Mathlib.Analysis.Polynomial.MahlerMeasure

/-!
# Pierce values: the two-sided bound

For a monic integer polynomial `p` with roots `αᵢ` over ℂ, the Pierce
values (Pierce, Ann. of Math. 18 (1916); Lehmer, Ann. of Math. 34 (1933))
are the integers

    `Δ_m = ± Res(p, X^m − 1) = ± ∏ᵢ (αᵢ^m − 1)`.

When no root of `p` is an `m`-th root of unity, `Δ_m` is a nonzero
integer, hence `1 ≤ |Δ_m|`; and each factor satisfies
`‖α^m − 1‖ ≤ 2·max(1,‖α‖)^m`, so `|Δ_m| ≤ 2^d · M(p)^m` with `M` the
Mahler measure. The two-sided constraint

    `1 ≤ ∏ᵢ ‖αᵢ^m − 1‖ ≤ 2^d · M(p)^m`

is the arithmetic input of the Blanksby–Montgomery lower bound for the
Mahler measure (Acta Arith. 18 (1971)) and Lehmer's own growth test for
the sequence `Δ_m`. The lower bound is proved by the same evaluation
identity used for the Dobrowolski baseline (`resultant_cast`): the
resultant is an integer whose complex value is the product `∏ (αᵢ^m − 1)`.

## Main results

* `one_le_abs_pierce`: `1 ≤ |Res(p, X^m − 1)|` when no root of `p` is an
  `m`-th root of unity.
* `abs_pierce_eq_prod`: `|Res(p, X^m − 1)| = ∏ᵢ ‖αᵢ^m − 1‖`.
* `pierce_upper`: `∏ᵢ ‖αᵢ^m − 1‖ ≤ 2^{deg p} · M(p)^m`.
* `pierce_sandwich`: the two bounds together.
-/

namespace Wieferich.PierceValues

open Polynomial Wieferich.DobrowolskiBaseline

/-- The Pierce value `Res(p, X^m − 1)`, an integer equal to
`± ∏ᵢ (αᵢ^m − 1)` over the roots of `p`. -/
noncomputable def pierceNum (p : Polynomial ℤ) (m : ℕ) : ℤ :=
  resultant p (X ^ m - 1) p.natDegree m

lemma natDegree_X_pow_sub_one_le (m : ℕ) :
    ((X : Polynomial ℤ) ^ m - 1).natDegree ≤ m :=
  (natDegree_sub_le _ _).trans (by simp)

lemma eval_X_pow_sub_one (m : ℕ) (α : ℂ) :
    (((X ^ m - 1 : Polynomial ℤ)).map (Int.castRingHom ℂ)).eval α = α ^ m - 1 := by
  simp

/-- The complex value of the Pierce value is the product `∏ (α^m − 1)`
over the roots of `p`. -/
lemma pierce_cast {p : Polynomial ℤ} (hm : p.Monic) (m : ℕ) :
    ((pierceNum p m : ℤ) : ℂ)
      = ((p.map (Int.castRingHom ℂ)).roots.map fun α => α ^ m - 1).prod := by
  rw [pierceNum, resultant_cast hm (natDegree_X_pow_sub_one_le m)]
  exact congrArg Multiset.prod (Multiset.map_congr rfl fun α _ => eval_X_pow_sub_one m α)

/-- **The Pierce floor**: when no root of `p` is an `m`-th root of unity,
the Pierce value is a nonzero integer — `1 ≤ |Res(p, X^m − 1)|`. -/
theorem one_le_abs_pierce {p : Polynomial ℤ} (hm : p.Monic) {m : ℕ}
    (hnru : ∀ α ∈ (p.map (Int.castRingHom ℂ)).roots, α ^ m ≠ 1) :
    1 ≤ |pierceNum p m| := by
  refine Int.one_le_abs ?_
  intro h0
  have hc : ((pierceNum p m : ℤ) : ℂ) = 0 := by rw [h0]; simp
  rw [pierce_cast hm, Multiset.prod_eq_zero_iff, Multiset.mem_map] at hc
  obtain ⟨α, hα, hz⟩ := hc
  exact hnru α hα (sub_eq_zero.mp hz)

/-- **The capacity identity**: `|Res(p, X^m − 1)| = ∏ᵢ ‖αᵢ^m − 1‖`. -/
theorem abs_pierce_eq_prod {p : Polynomial ℤ} (hm : p.Monic) (m : ℕ) :
    ((|pierceNum p m| : ℤ) : ℝ)
      = ((p.map (Int.castRingHom ℂ)).roots.map fun α => ‖α ^ m - 1‖).prod := by
  have h : ((|pierceNum p m| : ℤ) : ℝ) = ‖((pierceNum p m : ℤ) : ℂ)‖ := by
    rw [Complex.norm_intCast, Int.cast_abs]
  have hnp : ∀ s : Multiset ℂ, ‖s.prod‖ = (s.map fun z => ‖z‖).prod := by
    intro s
    induction s using Multiset.induction with
    | empty => simp
    | cons a t ih =>
      rw [Multiset.prod_cons, Multiset.map_cons, Multiset.prod_cons, norm_mul, ih]
  rw [h, pierce_cast hm, hnp, Multiset.map_map]
  rfl

private lemma prod_map_le_prod_map {s : Multiset ℂ} {f g : ℂ → ℝ}
    (h0 : ∀ x ∈ s, 0 ≤ f x) (h : ∀ x ∈ s, f x ≤ g x) :
    (s.map f).prod ≤ (s.map g).prod := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a t ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons]
    have hfa := h0 a (Multiset.mem_cons_self a t)
    have hga := h a (Multiset.mem_cons_self a t)
    have hft : (t.map f).prod ≤ (t.map g).prod :=
      ih (fun x hx => h0 x (Multiset.mem_cons_of_mem hx))
        (fun x hx => h x (Multiset.mem_cons_of_mem hx))
    have hf0 : 0 ≤ (t.map f).prod :=
      Multiset.prod_nonneg fun x hx => by
        obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp hx
        exact h0 y (Multiset.mem_cons_of_mem hy)
    exact mul_le_mul hga hft hf0 (le_trans hfa hga)

/-- Per-root growth cap: `‖α^m − 1‖ ≤ 2 · max(1,‖α‖)^m`. -/
lemma pierce_factor_le (α : ℂ) (m : ℕ) :
    ‖α ^ m - 1‖ ≤ 2 * max 1 ‖α‖ ^ m := by
  have h1 : ‖α ^ m - 1‖ ≤ ‖α‖ ^ m + 1 := by
    calc ‖α ^ m - 1‖ ≤ ‖α ^ m‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = ‖α‖ ^ m + 1 := by rw [norm_pow, norm_one]
  have h2 : ‖α‖ ^ m ≤ max 1 ‖α‖ ^ m :=
    pow_le_pow_left₀ (norm_nonneg _) (le_max_right _ _) m
  have h3 : (1 : ℝ) ≤ max 1 ‖α‖ ^ m := one_le_pow₀ (le_max_left _ _)
  linarith

/-- **The growth cap**: `∏ᵢ ‖αᵢ^m − 1‖ ≤ 2^{deg p} · M(p)^m`, with `M`
the Mahler measure of `p` over ℂ. -/
theorem pierce_upper {p : Polynomial ℤ} (hm : p.Monic) (m : ℕ) :
    ((p.map (Int.castRingHom ℂ)).roots.map fun α => ‖α ^ m - 1‖).prod
      ≤ 2 ^ p.natDegree * (p.map (Int.castRingHom ℂ)).mahlerMeasure ^ m := by
  set pc := p.map (Int.castRingHom ℂ) with hpc
  have hmc : pc.Monic := hm.map _
  have hM : pc.mahlerMeasure = (pc.roots.map fun α => max 1 ‖α‖).prod := by
    rw [mahlerMeasure_eq_leadingCoeff_mul_prod_roots, hmc.leadingCoeff, norm_one, one_mul]
  have hcard : Multiset.card pc.roots = p.natDegree := by
    have hsplit : pc.Splits := IsAlgClosed.splits pc
    rw [← hsplit.natDegree_eq_card_roots, hm.natDegree_map]
  have hle : (pc.roots.map fun α => ‖α ^ m - 1‖).prod
      ≤ (pc.roots.map fun α => 2 * max 1 ‖α‖ ^ m).prod :=
    prod_map_le_prod_map (fun x _ => norm_nonneg _) (fun x _ => pierce_factor_le x m)
  refine hle.trans (le_of_eq ?_)
  have hsplit2 : (pc.roots.map fun α => 2 * max 1 ‖α‖ ^ m).prod
      = (pc.roots.map fun _ => (2 : ℝ)).prod * (pc.roots.map fun α => max 1 ‖α‖ ^ m).prod := by
    induction pc.roots using Multiset.induction with
    | empty => simp
    | cons a s ih =>
      simp only [Multiset.map_cons, Multiset.prod_cons]
      rw [ih]; ring
  have hpow : (pc.roots.map fun α => max 1 ‖α‖ ^ m).prod
      = ((pc.roots.map fun α => max 1 ‖α‖).prod) ^ m := by
    rw [show (pc.roots.map fun α => max 1 ‖α‖ ^ m)
        = ((pc.roots.map fun α => max 1 ‖α‖).map fun x => x ^ m) by
      rw [Multiset.map_map]; rfl]
    induction (pc.roots.map fun α => max 1 ‖α‖) using Multiset.induction with
    | empty => simp
    | cons a s ih =>
      rw [Multiset.map_cons, Multiset.prod_cons, Multiset.prod_cons, ih, mul_pow]
  rw [hsplit2, Multiset.map_const', Multiset.prod_replicate, hcard, hpow, hM]

/-- **The Pierce sandwich**: for a monic `p` none of whose roots is an
`m`-th root of unity,

    `1 ≤ ∏ᵢ ‖αᵢ^m − 1‖ ≤ 2^{deg p} · M(p)^m`.

The lower bound is integrality (Pierce), the upper the Mahler growth cap
(Lehmer); the Blanksby–Montgomery argument lives between them. -/
theorem pierce_sandwich {p : Polynomial ℤ} (hm : p.Monic) {m : ℕ}
    (hnru : ∀ α ∈ (p.map (Int.castRingHom ℂ)).roots, α ^ m ≠ 1) :
    (1 : ℝ) ≤ ((p.map (Int.castRingHom ℂ)).roots.map fun α => ‖α ^ m - 1‖).prod
      ∧ ((p.map (Int.castRingHom ℂ)).roots.map fun α => ‖α ^ m - 1‖).prod
        ≤ 2 ^ p.natDegree * (p.map (Int.castRingHom ℂ)).mahlerMeasure ^ m := by
  refine ⟨?_, pierce_upper hm m⟩
  rw [← abs_pierce_eq_prod hm]
  exact_mod_cast one_le_abs_pierce hm hnru

end Wieferich.PierceValues
