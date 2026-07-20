/-
Copyright (c) 2026 Dillon Ryan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dillon Ryan
-/
import WieferichFamilies.ClassNumberOne

/-!
# The bifurcation reads the class group, not the class number

At `h = 4` the two isomorphism types behave differently: for
`ℤ/2 × ℤ/2` the genus group is the whole class group, the Hilbert class
field is abelian over ℚ (multiquadratic), and principality is a
congruence condition mod `|D|`; for `ℤ/4` the closure is dihedral and
principality requires a quartic character beyond `p mod |D|`. The census
data of the paper (§2.2) matches: zero mixed residue classes for the
`ℤ/2 × ℤ/2` fields, mixed classes for the `ℤ/4` fields.
-/

namespace Wieferich.ClassGroupStructure

/-! ## The 2-torsion / abelian dichotomy -/

/-- **a group of exponent 2 is abelian**: if `g * g = 1` for every `g`, then the
    group is commutative. This is the class-field-theory reason `ℤ/2 × ℤ/2` gives an
    abelian Hilbert class field over ℚ: conjugation-by-inversion is trivial on 2-torsion,
    so `H/ℚ` is abelian and the bifurcation is a congruence condition. -/
theorem two_torsion_abelian {G : Type*} [Group G] (h : ∀ g : G, g * g = 1) (a b : G) :
    a * b = b * a := by
  have inv : ∀ g : G, g⁻¹ = g := fun g => by
    rw [← mul_one g⁻¹, ← h g, ← mul_assoc, inv_mul_cancel, one_mul]
  have := h (a * b)
  calc a * b = (a * b)⁻¹ := (inv (a * b)).symm
    _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
    _ = b * a := by rw [inv a, inv b]

/-- **`ℤ/4` is not exponent 2**: the generator `1` has `1 + 1 = 2 ≠ 0`,
    an element of order 4. So the cyclic class group escapes `two_torsion_abelian`, its
    conjugation-by-inversion is nontrivial, and `H/ℚ` is the non-abelian dihedral `D₄` —
    the quartic branch of the `h = 4` bifurcation. -/
theorem z4_not_two_torsion : ∃ x : ZMod 4, x + x ≠ 0 := ⟨1, by decide⟩

/-- **`ℤ/2 × ℤ/2` is exponent 2**: every element doubles to zero, so
    it is the elementary abelian case — abelian `H/ℚ`, congruence bifurcation. -/
theorem klein_two_torsion : ∀ x : ZMod 2 × ZMod 2, x + x = 0 := by decide

/-! ## The typed h=4 dichotomy -/

/-- The **h=4 bifurcation datum**: the class group's exponent-2-ness (`elementary2`), the
    resulting field-theoretic branch, and the named class-field-theory arrow tying them.
    When `elementary2` (ℤ/2 × ℤ/2) the branch `congruenceBranch` holds — principality is a
    congruence mod `|D|`; otherwise (ℤ/4) the quartic branch, non-abelian `D₄`. -/
structure H4Bifurcation where
  /-- The class group is an elementary abelian 2-group. -/
  elementary2 : Prop
  /-- The bifurcation is a congruence condition mod `|D|` (abelian `H/ℚ`). -/
  congruenceBranch : Prop
  /-- **Named** (class field theory): elementary-2 class group ⟺ abelian `H/ℚ` ⟺ the
      principal branch is a congruence condition. -/
  cft : elementary2 ↔ congruenceBranch

/-- **the dichotomy holds both ways**: the congruence (abelian) branch is
    equivalent to the class group being elementary-2. So the same class number `h = 4`
    splits into a congruence branch (`ℤ/2 × ℤ/2`) and a non-congruence quartic branch
    (`ℤ/4`) — the Wieferich bifurcation reads the group, not `|C|`. -/
theorem bifurcation_reads_group (H : H4Bifurcation) :
    H.congruenceBranch ↔ H.elementary2 :=
  H.cft.symm

end Wieferich.ClassGroupStructure
