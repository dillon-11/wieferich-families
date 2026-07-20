/-
Copyright (c) 2026 Dillon Ryan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dillon Ryan
-/
import WieferichFamilies.GoldCriterion

/-!
# O(log p) certificates for the unit-root condition

A binary-exponentiation ladder decides the depth-2 unit-root condition in
`⌈log₂ p⌉` square-and-multiply steps, each a kernel decision on integers
below `p⁶`, glued by two `Nat.ModEq` lemmas. Certificate size is
`O(log p)`, so certifiable height is unbounded in practice.

## Main results

* `ladder_sq`, `ladder_sq_mul`: the generic ladder steps.
* `ladder_489061` (19 steps): re-proves, at about `10⁻⁵` of the kernel
  work, a fact previously certified only through a ~1.25-million-digit
  power computation.
* `ladder_6811741`, `record_6811741_dvd` (23 steps, `D = −3`): the first
  certificate of the full depth-2 condition `u^(p−1) ≡ 1 (mod p²)` at
  this height.
* `ladder_matches_megadigit`: agreement with the direct computation.
-/

namespace Wieferich.PowerLadder

/-! ## The two generic rungs -/

/-- **the squaring rung**: from `a^e ≡ r`, conclude `a^{2e} ≡ r·r` (mod `n`).
    With `r` a reduced residue this is the entire content of one binary-exponentiation
    step; the kernel never sees a number above `n²`. -/
theorem ladder_sq {a e r n : ℕ} (h : a ^ e ≡ r [MOD n]) :
    a ^ (2 * e) ≡ r * r [MOD n] := by
  have hx : a ^ (2 * e) = a ^ e * a ^ e := by rw [two_mul, pow_add]
  rw [hx]; exact h.mul h

/-- **the square-and-multiply rung**: from `a^e ≡ r`, conclude
    `a^{2e+1} ≡ r·r·a` (mod `n`) — the odd-bit step of the ladder. -/
theorem ladder_sq_mul {a e r n : ℕ} (h : a ^ e ≡ r [MOD n]) :
    a ^ (2 * e + 1) ≡ r * r * a [MOD n] := by
  have hx : a ^ (2 * e + 1) = a ^ e * a ^ e * a := by rw [pow_succ, two_mul, pow_add]
  rw [hx]; exact (h.mul h).mul (Nat.ModEq.refl a)

/-! ## The 489061 certificate, re-proved at O(log p) -/

/-- Proved (ladder) — the depth-2 unit-root condition at `p = 489061`:
    `239003622990^{p-1} ≡ 1 (mod p²)` via 19 square-and-multiply rungs,
    each a kernel `decide` below `p⁶` — certificate size `O(log p)`. -/
theorem ladder_489061 : (239003622990 : ℕ) ^ 489060 ≡ 1 [MOD 239180661721] := by
  have h0 : (239003622990 : ℕ) ^ 1 ≡ 239003622990 [MOD 239180661721] := by decide
  have h1 : (239003622990 : ℕ) ^ 3 ≡ 483682318 [MOD 239180661721] := by
    have h := ladder_sq_mul h0
    have e : 2 * 1 + 1 = 3 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h2 : (239003622990 : ℕ) ^ 7 ≡ 177038731 [MOD 239180661721] := by
    have h := ladder_sq_mul h1
    have e : 2 * 3 + 1 = 7 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h3 : (239003622990 : ℕ) ^ 14 ≡ 847079 [MOD 239180661721] := by
    have h := ladder_sq h2
    have e : 2 * 7 = 14 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h4 : (239003622990 : ℕ) ^ 29 ≡ 660721049 [MOD 239180661721] := by
    have h := ladder_sq_mul h3
    have e : 2 * 14 + 1 = 29 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h5 : (239003622990 : ℕ) ^ 59 ≡ 238519940672 [MOD 239180661721] := by
    have h := ladder_sq_mul h4
    have e : 2 * 29 + 1 = 59 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h6 : (239003622990 : ℕ) ^ 119 ≡ 238519940672 [MOD 239180661721] := by
    have h := ladder_sq_mul h5
    have e : 2 * 59 + 1 = 119 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h7 : (239003622990 : ℕ) ^ 238 ≡ 239179814643 [MOD 239180661721] := by
    have h := ladder_sq h6
    have e : 2 * 119 = 238 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h8 : (239003622990 : ℕ) ^ 477 ≡ 238696979403 [MOD 239180661721] := by
    have h := ladder_sq_mul h7
    have e : 2 * 238 + 1 = 477 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h9 : (239003622990 : ℕ) ^ 955 ≡ 177038731 [MOD 239180661721] := by
    have h := ladder_sq_mul h8
    have e : 2 * 477 + 1 = 955 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h10 : (239003622990 : ℕ) ^ 1910 ≡ 847079 [MOD 239180661721] := by
    have h := ladder_sq h9
    have e : 2 * 955 = 1910 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h11 : (239003622990 : ℕ) ^ 3820 ≡ 847078 [MOD 239180661721] := by
    have h := ladder_sq h10
    have e : 2 * 1910 = 3820 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h12 : (239003622990 : ℕ) ^ 7641 ≡ 238696979403 [MOD 239180661721] := by
    have h := ladder_sq_mul h11
    have e : 2 * 3820 + 1 = 7641 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h13 : (239003622990 : ℕ) ^ 15283 ≡ 177038731 [MOD 239180661721] := by
    have h := ladder_sq_mul h12
    have e : 2 * 7641 + 1 = 15283 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h14 : (239003622990 : ℕ) ^ 30566 ≡ 847079 [MOD 239180661721] := by
    have h := ladder_sq h13
    have e : 2 * 15283 = 30566 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h15 : (239003622990 : ℕ) ^ 61132 ≡ 847078 [MOD 239180661721] := by
    have h := ladder_sq h14
    have e : 2 * 30566 = 61132 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h16 : (239003622990 : ℕ) ^ 122265 ≡ 238696979403 [MOD 239180661721] := by
    have h := ladder_sq_mul h15
    have e : 2 * 61132 + 1 = 122265 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h17 : (239003622990 : ℕ) ^ 244530 ≡ 239180661720 [MOD 239180661721] := by
    have h := ladder_sq h16
    have e : 2 * 122265 = 244530 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h18 : (239003622990 : ℕ) ^ 489060 ≡ 1 [MOD 239180661721] := by
    have h := ladder_sq h17
    have e : 2 * 244530 = 489060 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  exact h18

/-! ## The atlas record 6811741, certified in full for the first time -/

/-- Proved (ladder) — the depth-2 unit-root condition at `p = 6811741`:
    `46390612794032^{p-1} ≡ 1 (mod p²)` via 23 square-and-multiply rungs,
    each a kernel `decide` below `p⁶` — certificate size `O(log p)`. -/
theorem ladder_6811741 : (46390612794032 : ℕ) ^ 6811740 ≡ 1 [MOD 46399815451081] := by
  have h0 : (46390612794032 : ℕ) ^ 1 ≡ 46390612794032 [MOD 46399815451081] := by decide
  have h1 : (46390612794032 : ℕ) ^ 3 ≡ 25142139722 [MOD 46399815451081] := by
    have h := ladder_sq_mul h0
    have e : 2 * 1 + 1 = 3 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h2 : (46390612794032 : ℕ) ^ 6 ≡ 46399815451080 [MOD 46399815451081] := by
    have h := ladder_sq h1
    have e : 2 * 3 = 6 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h3 : (46390612794032 : ℕ) ^ 12 ≡ 1 [MOD 46399815451081] := by
    have h := ladder_sq h2
    have e : 2 * 6 = 12 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h4 : (46390612794032 : ℕ) ^ 25 ≡ 46390612794032 [MOD 46399815451081] := by
    have h := ladder_sq_mul h3
    have e : 2 * 12 + 1 = 25 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h5 : (46390612794032 : ℕ) ^ 51 ≡ 25142139722 [MOD 46399815451081] := by
    have h := ladder_sq_mul h4
    have e : 2 * 25 + 1 = 51 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h6 : (46390612794032 : ℕ) ^ 103 ≡ 9202657049 [MOD 46399815451081] := by
    have h := ladder_sq_mul h5
    have e : 2 * 51 + 1 = 103 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h7 : (46390612794032 : ℕ) ^ 207 ≡ 25142139722 [MOD 46399815451081] := by
    have h := ladder_sq_mul h6
    have e : 2 * 103 + 1 = 207 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h8 : (46390612794032 : ℕ) ^ 415 ≡ 9202657049 [MOD 46399815451081] := by
    have h := ladder_sq_mul h7
    have e : 2 * 207 + 1 = 415 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h9 : (46390612794032 : ℕ) ^ 831 ≡ 25142139722 [MOD 46399815451081] := by
    have h := ladder_sq_mul h8
    have e : 2 * 415 + 1 = 831 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h10 : (46390612794032 : ℕ) ^ 1663 ≡ 9202657049 [MOD 46399815451081] := by
    have h := ladder_sq_mul h9
    have e : 2 * 831 + 1 = 1663 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h11 : (46390612794032 : ℕ) ^ 3326 ≡ 11798282 [MOD 46399815451081] := by
    have h := ladder_sq h10
    have e : 2 * 1663 = 3326 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h12 : (46390612794032 : ℕ) ^ 6652 ≡ 11798281 [MOD 46399815451081] := by
    have h := ladder_sq h11
    have e : 2 * 3326 = 6652 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h13 : (46390612794032 : ℕ) ^ 13304 ≡ 46399803652799 [MOD 46399815451081] := by
    have h := ladder_sq h12
    have e : 2 * 6652 = 13304 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h14 : (46390612794032 : ℕ) ^ 26608 ≡ 11798281 [MOD 46399815451081] := by
    have h := ladder_sq h13
    have e : 2 * 13304 = 26608 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h15 : (46390612794032 : ℕ) ^ 53216 ≡ 46399803652799 [MOD 46399815451081] := by
    have h := ladder_sq h14
    have e : 2 * 26608 = 53216 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h16 : (46390612794032 : ℕ) ^ 106433 ≡ 34344796771 [MOD 46399815451081] := by
    have h := ladder_sq_mul h15
    have e : 2 * 53216 + 1 = 106433 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h17 : (46390612794032 : ℕ) ^ 212866 ≡ 46399803652800 [MOD 46399815451081] := by
    have h := ladder_sq h16
    have e : 2 * 106433 = 212866 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h18 : (46390612794032 : ℕ) ^ 425733 ≡ 46374673311359 [MOD 46399815451081] := by
    have h := ladder_sq_mul h17
    have e : 2 * 212866 + 1 = 425733 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h19 : (46390612794032 : ℕ) ^ 851467 ≡ 9202657049 [MOD 46399815451081] := by
    have h := ladder_sq_mul h18
    have e : 2 * 425733 + 1 = 851467 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h20 : (46390612794032 : ℕ) ^ 1702935 ≡ 25142139722 [MOD 46399815451081] := by
    have h := ladder_sq_mul h19
    have e : 2 * 851467 + 1 = 1702935 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h21 : (46390612794032 : ℕ) ^ 3405870 ≡ 46399815451080 [MOD 46399815451081] := by
    have h := ladder_sq h20
    have e : 2 * 1702935 = 3405870 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h22 : (46390612794032 : ℕ) ^ 6811740 ≡ 1 [MOD 46399815451081] := by
    have h := ladder_sq h21
    have e : 2 * 3405870 = 6811740 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  exact h22

/-- the ladder in divisibility form: `p² ∣ u^{p−1} − 1` at the atlas record
    `p = 6811741`, `u = 46390612794032` the depth-2 Hensel unit root of trace `5042`
    (`D = −3`). The full unit-root Wieferich condition at the record height, from 23
    rungs — nothing in the proof grows with `p` except the rung count. -/
theorem record_6811741_dvd :
    (6811741 : ℕ) ^ 2 ∣ 46390612794032 ^ 6811740 - 1 := by
  have hsq : (6811741 : ℕ) ^ 2 = 46399815451081 := by norm_num
  rw [hsq]
  refine (Nat.modEq_iff_dvd' ?_).mp ladder_6811741.symm
  exact Nat.one_le_pow _ _ (by norm_num)

/-- **the ladder and the megadigit certificate agree**: `489061² = 239180661721`
    is the modulus of `ladder_489061`, so the ladder proves the same depth-2 condition
    the ≈1.25M-digit kernel object proved — at nineteen `decide`s below `p⁶`. -/
theorem ladder_matches_megadigit :
    (489061 : ℕ) ^ 2 = 239180661721 ∧
    (239003622990 : ℕ) ^ 489060 ≡ 1 [MOD 239180661721] :=
  ⟨by norm_num, ladder_489061⟩

end Wieferich.PowerLadder
