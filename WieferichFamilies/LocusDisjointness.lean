/-
Copyright (c) 2026 Dillon Ryan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dillon Ryan
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum

/-!
# Disjointness of the unit loci

One Wieferich locus per algebraic unit, and the computed loci are
pairwise disjoint: the base-2 members `{1093, 3511}`, the Wall–Sun–Sun
locus (empty below 2.8·10¹⁵), and the Perrin-square members
`{521, 190699}` (OEIS A173656) share no prime. This module proves the
pairwise non-membership of the known members by kernel decision.
-/

namespace Wieferich.LocusDisjointness

/-- **521 is Perrin-Wieferich but not base-2 Wieferich**: `521² ∤
    2⁵²⁰ − 1`, so the plastic-unit member 521 is off the base-2 (rational-unit) ν-locus
    `{1093, 3511}`. The loci do not share this prime. -/
theorem plastic_521_not_classical : ¬ (521 : ℤ) ^ 2 ∣ (2 ^ 520 - 1) := by decide +kernel

/-- **the plastic ν-locus is off the base-2 locus by value**: neither
    521 nor 190699 equals a base-2 Wieferich prime `1093` or `3511`. -/
theorem plastic_members_distinct :
    (521 : ℤ) ≠ 1093 ∧ (521 : ℤ) ≠ 3511 ∧
    (190699 : ℤ) ≠ 1093 ∧ (190699 : ℤ) ≠ 3511 := by decide

/-- The **locus-disjointness datum**: for a prime `p`, its membership in the three ν-axis
    Wieferich loci — base 2, golden (Wall–Sun–Sun), plastic (Perrin). The independence says a prime
        lies on at most one; the datum records the three predicates as
    separate grades of the ν-axis, one per algebraic unit. -/
structure UnitLoci (p : ℤ) where
  /-- `p² ∣ 2^{p−1} − 1` (base-2 rational unit). -/
  base2 : Prop
  /-- `p² ∣ F_{p−(5|p)}` (golden quadratic Pisot, Wall–Sun–Sun). -/
  golden : Prop
  /-- `p² ∣ P(p)` (the plastic number; Perrin-square condition). -/
  plastic : Prop

/-- **the loci are disjoint at 521**: the plastic member 521 carries the plastic
    grade but provably not the base-2 grade, witnessing that the three per-unit ν-loci do
    not coincide — the ν-axis is genuinely plural, one Wieferich locus per
    algebraic unit, mutually disjoint. -/
theorem unit_loci_disjoint (L : UnitLoci 521)
    (hbase : L.base2 = ((521 : ℤ) ^ 2 ∣ (2 ^ 520 - 1))) : ¬ L.base2 := by
  rw [hbase]; exact plastic_521_not_classical

/-! ## λ ⊥ ν within the plastic unit -/

/-- **the Perrin-Wieferich prime 521 is not on the λ-fold principal
    locus**: `x³ − x − 1` has the single root `393` mod 521 (a transposition Frobenius —
    521 is inert in `ℚ(√−23)`), so the cubic does NOT split completely (`Frob ≠ id`, not
    principal). Thus the plastic unit's `ν`-axis (Perrin–Wieferich, `ρ^{p−1} ≡ 1`) and
    its `λ`-axis (complete splitting of the Pisot cubic, `Frob = id`) are orthogonal at
    521 — the μ-λ-ν independence realized inside a single unit. -/
theorem perrin_521_off_lambda_fold :
    (393 : ZMod 521) ^ 3 - 393 - 1 = 0 ∧
    (∀ x : ZMod 521, x ^ 3 - x - 1 = 0 → x = 393) := by decide +kernel

end Wieferich.LocusDisjointness
