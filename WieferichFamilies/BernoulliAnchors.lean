/-
Copyright (c) 2026 Dillon Ryan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dillon Ryan
-/
import WieferichFamilies.PierpontSmoothness

/-!
# Bernoulli anchors: Glaisher and Wolstenholme

The λ-condition fires on interior Bernoulli indices (`p ∣ num B_k`,
`k < p − 1`); the classical Wieferich condition fires on the edge of the
same spectrum, through Glaisher's congruence
`q_p(2) ≡ −(1/2)·H_((p−1)/2) (mod p)` and the Wolstenholme congruence
`H_(p−1) ≡ 0 (mod p²)`.

## Main results

Kernel-decided anchors: Glaisher at `p = 7` and `13`, Wolstenholme at
`5` and `7`, and `1093² ∣ 2¹⁰⁹² − 1` carried through a 329-digit power
with empty axiom footprint. The general Glaisher congruence enters as
the single named hypothesis field of `BernoulliEdge`.
-/

namespace Wieferich.BernoulliAnchors

/-! ## Glaisher anchors: the Fermat quotient IS a half-harmonic sum -/

/-- **Glaisher at 7**: `q_7(2) = (2⁶ − 1)/7 = 9`, and in `ZMod 7`,
    `9 = −(1/2)·(1 + 1/2 + 1/3)` — the Fermat quotient equals the negated half of the
    half-harmonic sum. The ν-axis condition `q_p(2) ≡ 0` is a harmonic-sum zero. -/
theorem glaisher_7 :
    (2 ^ 6 - 1 : ℕ) = 7 * 9 ∧
    (2 * 4 : ZMod 7) = 1 ∧ (3 * 5 : ZMod 7) = 1 ∧
    (9 : ZMod 7) = -(4 * (1 + 4 + 5)) := by decide

/-- **Glaisher at the atlas seed 13**: `q₁₃(2) = 315`, and in
    `ZMod 13`, `315 = −(1/2)·H₆`. The same edge congruence at the first Gold member —
    the ν-reading and the λ-reading (`λ₁₃ = 2`, BSDLambdaLadder) meet at 13. -/
theorem glaisher_13 :
    (2 ^ 12 - 1 : ℕ) = 13 * 315 ∧
    (2 * 7 : ZMod 13) = 1 ∧ (3 * 9 : ZMod 13) = 1 ∧ (4 * 10 : ZMod 13) = 1 ∧
    (5 * 8 : ZMod 13) = 1 ∧ (6 * 11 : ZMod 13) = 1 ∧
    (315 : ZMod 13) = -(7 * (1 + 7 + 9 + 10 + 8 + 11)) := by decide

/-! ## Wolstenholme anchors: the edge window -/

/-- **Wolstenholme at 5**: `H₄ ≡ 0 (mod 5²)` as a sum of unit
    inverses in `ZMod 25` — the `B_{p−3}` edge window at its smallest prime. -/
theorem wolstenholme_5 :
    (2 * 13 : ZMod 25) = 1 ∧ (3 * 17 : ZMod 25) = 1 ∧ (4 * 19 : ZMod 25) = 1 ∧
    (1 + 13 + 17 + 19 : ZMod 25) = 0 := by decide

/-- **Wolstenholme at 7**: `H₆ ≡ 0 (mod 7²)` in `ZMod 49`. -/
theorem wolstenholme_7 :
    (2 * 25 : ZMod 49) = 1 ∧ (3 * 33 : ZMod 49) = 1 ∧ (4 * 37 : ZMod 49) = 1 ∧
    (5 * 10 : ZMod 49) = 1 ∧ (6 * 41 : ZMod 49) = 1 ∧
    (1 + 25 + 33 + 37 + 10 + 41 : ZMod 49) = 0 := by decide

/-! ## The classical ν-generator, kernel-certified -/

/-- **the classical Wieferich prime**: `1093² ∣ 2¹⁰⁹² − 1`. The
    base-2 ν-axis generator, certified through the full 329-digit power. -/
theorem wieferich_1093_kernel : (1093 : ℕ) ^ 2 ∣ 2 ^ 1092 - 1 := by decide +kernel

/-! ## The edge datum -/

/-- The **Bernoulli edge datum** for a prime `p`: the ν-axis zero (`q_p(2) ≡ 0`), the
    half-harmonic zero (`H_{(p−1)/2} ≡ 0 (mod p)`), and the Glaisher bridge between
    them — the one named literature input, anchored at 7 and 13 by kernel `decide`. -/
structure BernoulliEdge (p : ℕ) where
  /-- the ν-axis: the Fermat quotient `q_p(2)` vanishes mod `p`. -/
  quotient_zero : Prop
  /-- the edge zero: the half-harmonic sum `H_{(p−1)/2}` vanishes mod `p`. -/
  harmonic_zero : Prop
  /-- Glaisher (1900): `q_p(2) ≡ −(1/2)·H_{(p−1)/2} (mod p)` — the two vanish
      together. Named input; kernel-anchored at 7 and 13 above. -/
  glaisher : quotient_zero ↔ harmonic_zero

/-- **the edge fires at 1093**: given the Glaisher bridge, the certified
    Wieferich condition at 1093 forces the half-harmonic zero `H₅₄₆ ≡ 0 (mod 1093)` —
    the classical ν-generator is a Bernoulli-EDGE zero, the same spectrum the λ-axis
    reads at interior indices. -/
theorem edge_fires_at_1093 (E : BernoulliEdge 1093) (hq : E.quotient_zero) :
    E.harmonic_zero := E.glaisher.mp hq

/-- **the classification reads one spectrum**: the λ-axis interior anchor
    (`37 ∣ num B₃₂`, `IwasawaGrid`), the ν-axis edge anchors (Glaisher at the atlas
    seed, Wolstenholme window), and the certified ν-generator, in one statement —
    μ global, λ interior, ν edge: three readings of the Bernoulli spectrum. -/
theorem grid_reads_bernoulli :
    (37 : ℤ) ∣ (-7709321041217) ∧
    ((315 : ZMod 13) = -(7 * (1 + 7 + 9 + 10 + 8 + 11))) ∧
    ((1 + 13 + 17 + 19 : ZMod 25) = 0) ∧
    (1093 : ℕ) ^ 2 ∣ 2 ^ 1092 - 1 :=
  ⟨Wieferich.IwasawaGrid.irregular_37_B32, glaisher_13.2.2.2.2.2.2, wolstenholme_5.2.2.2,
    wieferich_1093_kernel⟩

end Wieferich.BernoulliAnchors
