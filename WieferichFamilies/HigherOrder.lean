import WieferichFamilies.LiftDichotomy
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Wieferich conditions of higher order in the family x² − kx − 1

Over the family x² − kx − 1 (k ≤ 1000, p ≤ 10⁶) the census of the paper
finds 66 members of depth 3 (`p³` divides the defining congruence) and 9 of
depth 4. For fixed `p` the depth-3 members are the roots of one congruence
mod `p³`, with local count `N₂(p) = p − 2·[p ≡ 1 (mod 4)]` and unique
Hensel lifting to every depth, which reconciles the counts exactly.

## Main results

* `torsion_diagonal_rigid`: in a ring with `p² = 0`, the two roots
  `1 + p·c` and `−1 + p·d` of a quadratic on the diagonal `k = jp` have
  `α^p + ᾱ^p = 0` for odd `p` — the trace collapses, so the depth-2
  condition `V_p ≡ jp (mod p²)` with `jp ≢ 0` cannot hold. This explains
  the census observation of 0 members on 20 diagonal classes against an
  expectation of 41 (control classes: 39 observed).
* `hyper_103_11` … `hyper_807_5`: kernel-decided certificates (Lucas
  matrix power mod `p⁴`) for the nine depth-4 members.
-/

namespace Wieferich.HigherOrder

open Wieferich.LiftDichotomy

/-- **Torsion-diagonal rigidity.** In a commutative ring with `p² = 0`, if
    `α = 1 + p·c` and `ᾱ = −1 + p·d` (the roots of a quadratic on the
    diagonal `k = jp`, both 1-units up to sign), then for odd `p`
    `α^p + ᾱ^p = 0`. The trace collapses, so the depth-2 condition
    `V_p ≡ jp (mod p²)` with `jp ≢ 0` never holds. -/
theorem torsion_diagonal_rigid {S : Type*} [CommRing S] {p : ℕ} {c d : S}
    (hp2 : (p : S) ^ 2 = 0) (hodd : Odd p) :
    (1 + (p : S) * c) ^ p + (-1 + (p : S) * d) ^ p = 0 := by
  have h1 : (1 + (p : S) * c) ^ p = 1 := ker_pow_prime_eq_one hp2
  have h2 : (-1 + (p : S) * d) ^ p = -(1 + (p : S) * (-d)) ^ p := by
    have : (-1 + (p : S) * d) = -(1 + (p : S) * (-d)) := by ring
    rw [this, hodd.neg_pow]
  rw [h1, h2, ker_pow_prime_eq_one hp2]
  ring

/-! ## The nine depth-4 certificates (Lucas matrix power mod p⁴) -/

set_option maxRecDepth 8000 in
/-- depth-4 member `(k, p) = (103, 11)` of the family x² − kx − 1: `V_11(103) ≡ 103 (mod 11⁴ = 14641)`. -/
theorem hyper_103_11 :
    (Matrix.of ![![(103 : ZMod 14641), 1], ![1, 0]] ^ 11).trace = 103 := by decide

set_option maxRecDepth 8000 in
/-- depth-4 member `(k, p) = (176, 7)` of the family x² − kx − 1: `V_7(176) ≡ 176 (mod 7⁴ = 2401)`. -/
theorem hyper_176_7 :
    (Matrix.of ![![(176 : ZMod 2401), 1], ![1, 0]] ^ 7).trace = 176 := by decide

set_option maxRecDepth 8000 in
/-- depth-4 member `(k, p) = (182, 5)` of the family x² − kx − 1: `V_5(182) ≡ 182 (mod 5⁴ = 625)`. -/
theorem hyper_182_5 :
    (Matrix.of ![![(182 : ZMod 625), 1], ![1, 0]] ^ 5).trace = 182 := by decide

set_option maxRecDepth 8000 in
/-- depth-4 member `(k, p) = (239, 13)` of the family x² − kx − 1: `V_13(239) ≡ 239 (mod 13⁴ = 28561)`. -/
theorem hyper_239_13 :
    (Matrix.of ![![(239 : ZMod 28561), 1], ![1, 0]] ^ 13).trace = 239 := by decide

set_option maxRecDepth 8000 in
/-- depth-4 member `(k, p) = (306, 7)` of the family x² − kx − 1: `V_7(306) ≡ 306 (mod 7⁴ = 2401)`. -/
theorem hyper_306_7 :
    (Matrix.of ![![(306 : ZMod 2401), 1], ![1, 0]] ^ 7).trace = 306 := by decide

set_option maxRecDepth 8000 in
/-- depth-4 member `(k, p) = (367, 7)` of the family x² − kx − 1: `V_7(367) ≡ 367 (mod 7⁴ = 2401)`. -/
theorem hyper_367_7 :
    (Matrix.of ![![(367 : ZMod 2401), 1], ![1, 0]] ^ 7).trace = 367 := by decide

set_option maxRecDepth 8000 in
/-- depth-4 member `(k, p) = (443, 5)` of the family x² − kx − 1: `V_5(443) ≡ 443 (mod 5⁴ = 625)`. -/
theorem hyper_443_5 :
    (Matrix.of ![![(443 : ZMod 625), 1], ![1, 0]] ^ 5).trace = 443 := by decide

set_option maxRecDepth 8000 in
/-- depth-4 member `(k, p) = (625, 5)` of the family x² − kx − 1: `V_5(625) ≡ 625 (mod 5⁴ = 625)`. -/
theorem hyper_625_5 :
    (Matrix.of ![![(625 : ZMod 625), 1], ![1, 0]] ^ 5).trace = 625 := by decide

set_option maxRecDepth 8000 in
/-- depth-4 member `(k, p) = (807, 5)` of the family x² − kx − 1: `V_5(807) ≡ 807 (mod 5⁴ = 625)`. -/
theorem hyper_807_5 :
    (Matrix.of ![![(807 : ZMod 625), 1], ![1, 0]] ^ 5).trace = 807 := by decide
/-- the hyper moduli are fourth powers: `14641 = 11⁴`,
    `2401 = 7⁴`, `625 = 5⁴`, `28561 = 13⁴`. -/
theorem hyper_moduli :
    (14641 : ℕ) = 11 ^ 4 ∧ (2401 : ℕ) = 7 ^ 4 ∧ (625 : ℕ) = 5 ^ 4 ∧
    (28561 : ℕ) = 13 ^ 4 := by decide

end Wieferich.HigherOrder
