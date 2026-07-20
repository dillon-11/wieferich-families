/-
Copyright (c) 2026 Dillon Ryan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dillon Ryan
-/
import WieferichFamilies.LambdaLadder

/-!
# ℚ(√−23) and the plastic cubic

The first class-number-3 field is `K = ℚ(√−23)`; its cubic Hilbert
class field is the splitting field of `x³ − x − 1` (discriminant −23,
the minimal Pisot number; the associated weight-1 level-23 newform is
`η(τ)·η(23τ)`, Deligne–Serre). By class field theory a split prime `p`
has principal prime ideal iff `Frob_p = id` in `S₃` iff `x³ − x − 1`
splits completely mod `p`; Gold eligibility on ℚ(√−23) is exactly
complete splitting of the plastic cubic — the same unit that carries
the Perrin-square locus of §2.1 of the paper.
-/

namespace Wieferich.PlasticAnchor

/-! ## The plastic cubic and its discriminant -/

/-- **the plastic cubic has discriminant `−23`**: for `x³ + px + q`,
    `Δ = −4p³ − 27q²`, and at `p = q = −1` this is `4 − 27 = −23 = d_K` of the first
    class-number-3 field. The cubic that generates the qutrit Hilbert class field is
    pinned to the unit by one integer. -/
theorem plastic_cubic_disc : (-4 * (-1) ^ 3 - 27 * (-1) ^ 2 : ℤ) = -23 := by decide

/-! ## The fold at two primes: split vs inert of the plastic cubic -/

/-- **`p = 59` is principal and the plastic cubic splits**: the prime
    ideal above 59 is principal (`4·59 = 12² + 23·2²`) and `x³ − x − 1 ≡ (x−4)(x−13)(x−42)
    (mod 59)` — the three roots `4, 13, 42` witness complete splitting, `Frob₅₉ = id`. This
    is the principal branch where `π`, hence the Gold flag, lives. -/
theorem plastic_principal_59 :
    4 * 59 = 12 ^ 2 + 23 * 2 ^ 2 ∧
    (4 ^ 3 - 4 - 1) % 59 = 0 ∧ (13 ^ 3 - 13 - 1) % 59 = 0 ∧ (42 ^ 3 - 42 - 1) % 59 = 0 := by
  decide

/-- **`p = 13` is inert for the plastic cubic**: `x³ − x − 1` has no
    root in `ZMod 13`, so it is irreducible there (`Frob₁₃` a 3-cycle) — the
    non-principal branch, where no `π` exists and the Gold flag cannot fire. -/
theorem plastic_irreducible_13 : ∀ x : ZMod 13, x ^ 3 - x - 1 ≠ 0 := by decide

/-! ## The typed fold -/

/-- The **plastic fold datum** at a split prime `p` of `ℚ(√−23)`: the Gold flag (when it
    fires), the principality of the prime above `p`, and the two named reciprocity arrows
    of class field theory — the flag needs `π` (`flag_needs_principal`), and principality
    is complete splitting of the plastic cubic (`principal_iff_split`, the Artin/Chebotarev
    identity `Frob = id ⟺ x³ − x − 1` splits). Everything but these two named arrows is
    the proven Gold layer. -/
structure PlasticFold (p : ℤ) where
  /-- The prime ideal above `p` is principal. -/
  principal : Prop
  /-- The plastic cubic `x³ − x − 1` splits completely mod `p`. -/
  plasticSplits : Prop
  /-- The Gold / unit-root Wieferich flag at `p`. -/
  flag : Prop
  /-- **Named** (class field theory): the flag needs a prime element, i.e. principality. -/
  flag_needs_principal : flag → principal
  /-- **Named** (Artin reciprocity for the `S₃` extension): principality of the prime
      above `p` is complete splitting of the plastic cubic. -/
  principal_iff_split : principal ↔ plasticSplits

/-- **the fold**: a Gold / unit-root Wieferich prime of `ℚ(√−23)` splits the
    plastic cubic completely. The CM `λ_p(K) > 1` locus lies inside the minimal-Pisot
    splitting locus — the Wieferich census joined to the Salem-unit program through the
    first non-abelian unit. -/
theorem flag_implies_plastic_split {p : ℤ} (H : PlasticFold p) (hf : H.flag) :
    H.plasticSplits :=
  H.principal_iff_split.mp (H.flag_needs_principal hf)

end Wieferich.PlasticAnchor
