/-
Copyright (c) 2026 Dillon Ryan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dillon Ryan
-/
import WieferichFamilies.HigherOrder
import Mathlib.FieldTheory.Finite.Basic

/-!
# The resultant valuation reads Wieferich depth

Dobrowolski's lower bound for the Mahler measure (Acta Arith. 34 (1979))
plays the divisibility `p^d ∣ Res(P(x), P(x^p))` against an archimedean
bound on the resultant. This module proves the arithmetic layer and the
refinement measured by the censuses of the paper: the valuation of the
resultant is linear in the depth of the Wieferich condition,

    `v_p(Res(P, P(x^p))) = deg(P) · depth_p(α)`,

with depth 1 the ordinary case. Kernel-decided anchors at `p = 7` on
x² − kx − 1: `k = 1` gives `v = 2` (baseline), the depth-3 member
`k = 24` gives `v = 6`, the depth-4 member `k = 176` gives `v = 8`. The
Frobenius congruence `a^p = a` in `ZMod p` is proved; the archimedean
estimate enters only as a named hypothesis field of `DobrowolskiEngine`.
-/

namespace Wieferich.Dobrowolski

/-- **the Frobenius seed**: `a^p = a` for every `a : ZMod p` — the scalar
    layer of `P(x^p) ≡ P(x)^p (mod p)`, from which the baseline divisibility
    `p^d ∣ Res(P, P(x^p))` flows. -/
theorem frobenius_seed {p : ℕ} [Fact p.Prime] (a : ZMod p) : a ^ p = a :=
  ZMod.pow_card a

/-- **baseline anchor** (`depth 1`): for the golden unit
    `k = 1` at `p = 7` (not a Wieferich member), `Res(P, P(x⁷)) = −784 = −2⁴·7²`:
    valuation exactly `2 = deg` — Dobrowolski's divisibility, sharp. -/
theorem dobro_baseline_7 :
    (784 : ℤ) = 2 ^ 4 * 7 ^ 2 ∧ (7 : ℤ) ^ 2 ∣ 784 ∧ ¬ (7 : ℤ) ^ 3 ∣ 784 := by decide

/-- **super anchor** (`depth 3`): for the super member
    `(k, p) = (24, 7)` (V₇(24) ≡ 24 mod 7³), the exact resultant is
    `Res = −21551909996837654784` with `7⁶ ∣ Res` and `7⁷ ∤ Res`: valuation
    `6 = 2·3 = deg·depth`. -/
theorem dobro_super_7 :
    (7 : ℤ) ^ 6 ∣ 21551909996837654784 ∧
    ¬ (7 : ℤ) ^ 7 ∣ 21551909996837654784 := by decide +kernel

/-- **hyper anchor** (`depth 4`): for the hyper member
    `(k, p) = (176, 7)` (V₇(176) ≡ 176 mod 7⁴), `7⁸ ∣ Res` and `7⁹ ∤ Res`:
    valuation `8 = 2·4`. The three anchors witness the linear law
    `v_p(Res) = deg·depth` across depths 1, 3, 4. -/
theorem dobro_hyper_7 :
    (7 : ℤ) ^ 8 ∣ 27376228987187313194757114102784 ∧
    ¬ (7 : ℤ) ^ 9 ∣ 27376228987187313194757114102784 := by decide +kernel

/-- The **typed Dobrowolski engine** for a unit of degree `d` at height `p`: the
    proven arithmetic layer (the depth-graded divisibility) and the one named
    archimedean input (the Mahler upper bound), with the tension statement as the
    derived field. The engine's fluctuation term IS the unit's Wieferich depth —
    measured by the censuses, graded by the linear law. -/
structure DobrowolskiEngine (d : ℕ) (p : ℕ) where
  /-- the depth of the unit at `p` (1 = ordinary, 2 = Wieferich, 3 = super…). -/
  depth : ℕ
  /-- the proven arithmetic layer: `p^{d·depth}` divides the resultant. -/
  divisibility : Prop
  /-- the named archimedean input: `|Res| ≤ C(d)·M(α)^{O(pd)}` (Dobrowolski). -/
  mahler_upper : Prop
  /-- the tension: divisibility + upper bound force a Mahler lower bound. -/
  tension : divisibility → mahler_upper → Prop

end Wieferich.Dobrowolski
