/-
Copyright (c) 2026 Dillon Ryan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dillon Ryan
-/
import WieferichFamilies.PowerLadder

/-!
# The two record members, certified

The 47-field census of the paper, extended through the decade
(10⁸, 10⁹], produced the two largest known members of Gold's condition:

* `p = 330017383`, `D = −67` (trace 33525) — the field with `h(−67) = 1`
  and `67 ∣ num B₅₈`; its first known member.
* `p = 346527893`, `D = −52` (trace 16990) — class number 2.

Each certificate is 29 ladder steps (`PowerLadder`), every step a kernel
decision below `p⁶`. By Gold's criterion each certifies `λ_p(K) > 1` for
its field.

## Main results

`ladder_330017383`, `ladder_346527893`, `record_330017383_dvd`,
`record_genus_dvd`, `records_above_atlas`.
-/

namespace Wieferich.RecordCertificates

open Wieferich.PowerLadder

/-! ## The ℚ(√−67) record: p = 330017383 -/

/-- Proved (ladder) — the depth-2 unit-root condition at `p = 330017383`:
    `106546445419140355^{p-1} ≡ 1 (mod p²)` via 29 square-and-multiply rungs,
    each a kernel `decide` below `p⁶` — certificate size `O(log p)`. -/
theorem ladder_330017383 : (106546445419140355 : ℕ) ^ 330017382 ≡ 1 [MOD 108911473082168689] := by
  have h0 : (106546445419140355 : ℕ) ^ 1 ≡ 106546445419140355 [MOD 108911473082168689] := by decide
  have h1 : (106546445419140355 : ℕ) ^ 2 ≡ 463890859 [MOD 108911473082168689] := by
    have h := ladder_sq h0
    have e : 2 * 1 = 2 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h2 : (106546445419140355 : ℕ) ^ 4 ≡ 106283255981589192 [MOD 108911473082168689] := by
    have h := ladder_sq h1
    have e : 2 * 2 = 4 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h3 : (106546445419140355 : ℕ) ^ 9 ≡ 89644117240887832 [MOD 108911473082168689] := by
    have h := ladder_sq_mul h2
    have e : 2 * 4 + 1 = 9 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h4 : (106546445419140355 : ℕ) ^ 19 ≡ 50279624494079597 [MOD 108911473082168689] := by
    have h := ladder_sq_mul h3
    have e : 2 * 9 + 1 = 19 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h5 : (106546445419140355 : ℕ) ^ 39 ≡ 6517162709957986 [MOD 108911473082168689] := by
    have h := ladder_sq_mul h4
    have e : 2 * 19 + 1 = 39 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h6 : (106546445419140355 : ℕ) ^ 78 ≡ 772141674838890 [MOD 108911473082168689] := by
    have h := ladder_sq h5
    have e : 2 * 39 = 78 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h7 : (106546445419140355 : ℕ) ^ 157 ≡ 45258552494121689 [MOD 108911473082168689] := by
    have h := ladder_sq_mul h6
    have e : 2 * 78 + 1 = 157 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h8 : (106546445419140355 : ℕ) ^ 314 ≡ 52032610988012774 [MOD 108911473082168689] := by
    have h := ladder_sq h7
    have e : 2 * 157 = 314 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h9 : (106546445419140355 : ℕ) ^ 629 ≡ 19336105581135840 [MOD 108911473082168689] := by
    have h := ladder_sq_mul h8
    have e : 2 * 314 + 1 = 629 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h10 : (106546445419140355 : ℕ) ^ 1258 ≡ 83809799706357431 [MOD 108911473082168689] := by
    have h := ladder_sq h9
    have e : 2 * 629 = 1258 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h11 : (106546445419140355 : ℕ) ^ 2517 ≡ 43204849077624064 [MOD 108911473082168689] := by
    have h := ladder_sq_mul h10
    have e : 2 * 1258 + 1 = 2517 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h12 : (106546445419140355 : ℕ) ^ 5035 ≡ 85812960699341391 [MOD 108911473082168689] := by
    have h := ladder_sq_mul h11
    have e : 2 * 2517 + 1 = 5035 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h13 : (106546445419140355 : ℕ) ^ 10071 ≡ 38090963003527476 [MOD 108911473082168689] := by
    have h := ladder_sq_mul h12
    have e : 2 * 5035 + 1 = 10071 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h14 : (106546445419140355 : ℕ) ^ 20142 ≡ 89444865535584485 [MOD 108911473082168689] := by
    have h := ladder_sq h13
    have e : 2 * 10071 = 20142 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h15 : (106546445419140355 : ℕ) ^ 40285 ≡ 98098535236365714 [MOD 108911473082168689] := by
    have h := ladder_sq_mul h14
    have e : 2 * 20142 + 1 = 40285 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h16 : (106546445419140355 : ℕ) ^ 80570 ≡ 26904075222569736 [MOD 108911473082168689] := by
    have h := ladder_sq h15
    have e : 2 * 40285 = 80570 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h17 : (106546445419140355 : ℕ) ^ 161141 ≡ 56790393675704107 [MOD 108911473082168689] := by
    have h := ladder_sq_mul h16
    have e : 2 * 80570 + 1 = 161141 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h18 : (106546445419140355 : ℕ) ^ 322282 ≡ 105463731186791476 [MOD 108911473082168689] := by
    have h := ladder_sq h17
    have e : 2 * 161141 = 322282 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h19 : (106546445419140355 : ℕ) ^ 644565 ≡ 44605743962694549 [MOD 108911473082168689] := by
    have h := ladder_sq_mul h18
    have e : 2 * 322282 + 1 = 644565 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h20 : (106546445419140355 : ℕ) ^ 1289130 ≡ 89994007599968202 [MOD 108911473082168689] := by
    have h := ladder_sq h19
    have e : 2 * 644565 = 1289130 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h21 : (106546445419140355 : ℕ) ^ 2578260 ≡ 92022069259211835 [MOD 108911473082168689] := by
    have h := ladder_sq h20
    have e : 2 * 1289130 = 2578260 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h22 : (106546445419140355 : ℕ) ^ 5156521 ≡ 64963443406727194 [MOD 108911473082168689] := by
    have h := ladder_sq_mul h21
    have e : 2 * 2578260 + 1 = 5156521 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h23 : (106546445419140355 : ℕ) ^ 10313043 ≡ 23737300630088950 [MOD 108911473082168689] := by
    have h := ladder_sq_mul h22
    have e : 2 * 5156521 + 1 = 10313043 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h24 : (106546445419140355 : ℕ) ^ 20626086 ≡ 64085214193577639 [MOD 108911473082168689] := by
    have h := ladder_sq h23
    have e : 2 * 10313043 = 20626086 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h25 : (106546445419140355 : ℕ) ^ 41252172 ≡ 12632630811998982 [MOD 108911473082168689] := by
    have h := ladder_sq h24
    have e : 2 * 20626086 = 41252172 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h26 : (106546445419140355 : ℕ) ^ 82504345 ≡ 33545127686331626 [MOD 108911473082168689] := by
    have h := ladder_sq_mul h25
    have e : 2 * 41252172 + 1 = 82504345 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h27 : (106546445419140355 : ℕ) ^ 165008691 ≡ 1 [MOD 108911473082168689] := by
    have h := ladder_sq_mul h26
    have e : 2 * 82504345 + 1 = 165008691 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h28 : (106546445419140355 : ℕ) ^ 330017382 ≡ 1 [MOD 108911473082168689] := by
    have h := ladder_sq h27
    have e : 2 * 165008691 = 330017382 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  exact h28

/-! ## The genus-grade record: p = 346527893, D = −52 (h = 2) -/

/-- Proved (ladder) — the depth-2 unit-root condition at `p = 346527893`:
    `52280367975162154^{p-1} ≡ 1 (mod p²)` via 29 square-and-multiply rungs,
    each a kernel `decide` below `p⁶` — certificate size `O(log p)`. -/
theorem ladder_346527893 : (52280367975162154 : ℕ) ^ 346527892 ≡ 1 [MOD 120081580627019449] := by
  have h0 : (52280367975162154 : ℕ) ^ 1 ≡ 52280367975162154 [MOD 120081580627019449] := by decide
  have h1 : (52280367975162154 : ℕ) ^ 2 ≡ 120081580222623763 [MOD 120081580627019449] := by
    have h := ladder_sq h0
    have e : 2 * 1 = 2 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h2 : (52280367975162154 : ℕ) ^ 5 ≡ 52535477239869775 [MOD 120081580627019449] := by
    have h := ladder_sq_mul h1
    have e : 2 * 2 + 1 = 5 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h3 : (52280367975162154 : ℕ) ^ 10 ≡ 36345811799828625 [MOD 120081580627019449] := by
    have h := ladder_sq h2
    have e : 2 * 5 = 10 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h4 : (52280367975162154 : ℕ) ^ 20 ≡ 104488151824867881 [MOD 120081580627019449] := by
    have h := ladder_sq h3
    have e : 2 * 10 = 20 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h5 : (52280367975162154 : ℕ) ^ 41 ≡ 47129840229321569 [MOD 120081580627019449] := by
    have h := ladder_sq_mul h4
    have e : 2 * 20 + 1 = 41 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h6 : (52280367975162154 : ℕ) ^ 82 ≡ 41349600270507911 [MOD 120081580627019449] := by
    have h := ladder_sq h5
    have e : 2 * 41 = 82 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h7 : (52280367975162154 : ℕ) ^ 165 ≡ 24555232993294791 [MOD 120081580627019449] := by
    have h := ladder_sq_mul h6
    have e : 2 * 82 + 1 = 165 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h8 : (52280367975162154 : ℕ) ^ 330 ≡ 15730671331606736 [MOD 120081580627019449] := by
    have h := ladder_sq h7
    have e : 2 * 165 = 330 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h9 : (52280367975162154 : ℕ) ^ 660 ≡ 89737295959945640 [MOD 120081580627019449] := by
    have h := ladder_sq h8
    have e : 2 * 330 = 660 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h10 : (52280367975162154 : ℕ) ^ 1321 ≡ 69596975747214527 [MOD 120081580627019449] := by
    have h := ladder_sq_mul h9
    have e : 2 * 660 + 1 = 1321 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h11 : (52280367975162154 : ℕ) ^ 2643 ≡ 104301894967616692 [MOD 120081580627019449] := by
    have h := ladder_sq_mul h10
    have e : 2 * 1321 + 1 = 2643 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h12 : (52280367975162154 : ℕ) ^ 5287 ≡ 56648113728991520 [MOD 120081580627019449] := by
    have h := ladder_sq_mul h11
    have e : 2 * 2643 + 1 = 5287 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h13 : (52280367975162154 : ℕ) ^ 10575 ≡ 12418009243091893 [MOD 120081580627019449] := by
    have h := ladder_sq_mul h12
    have e : 2 * 5287 + 1 = 10575 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h14 : (52280367975162154 : ℕ) ^ 21150 ≡ 102394087620076014 [MOD 120081580627019449] := by
    have h := ladder_sq h13
    have e : 2 * 10575 = 21150 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h15 : (52280367975162154 : ℕ) ^ 42300 ≡ 24815631751130741 [MOD 120081580627019449] := by
    have h := ladder_sq h14
    have e : 2 * 21150 = 42300 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h16 : (52280367975162154 : ℕ) ^ 84601 ≡ 77333314320481577 [MOD 120081580627019449] := by
    have h := ladder_sq_mul h15
    have e : 2 * 42300 + 1 = 84601 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h17 : (52280367975162154 : ℕ) ^ 169203 ≡ 69016193805098031 [MOD 120081580627019449] := by
    have h := ladder_sq_mul h16
    have e : 2 * 84601 + 1 = 169203 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h18 : (52280367975162154 : ℕ) ^ 338406 ≡ 56801836691584963 [MOD 120081580627019449] := by
    have h := ladder_sq h17
    have e : 2 * 169203 = 338406 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h19 : (52280367975162154 : ℕ) ^ 676812 ≡ 83291705299934148 [MOD 120081580627019449] := by
    have h := ladder_sq h18
    have e : 2 * 338406 = 676812 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h20 : (52280367975162154 : ℕ) ^ 1353624 ≡ 93410290893545753 [MOD 120081580627019449] := by
    have h := ladder_sq h19
    have e : 2 * 676812 = 1353624 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h21 : (52280367975162154 : ℕ) ^ 2707249 ≡ 64458767751064845 [MOD 120081580627019449] := by
    have h := ladder_sq_mul h20
    have e : 2 * 1353624 + 1 = 2707249 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h22 : (52280367975162154 : ℕ) ^ 5414498 ≡ 10057119945315773 [MOD 120081580627019449] := by
    have h := ladder_sq h21
    have e : 2 * 2707249 = 5414498 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h23 : (52280367975162154 : ℕ) ^ 10828996 ≡ 24878626698350726 [MOD 120081580627019449] := by
    have h := ladder_sq h22
    have e : 2 * 5414498 = 10828996 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h24 : (52280367975162154 : ℕ) ^ 21657993 ≡ 94036549682440686 [MOD 120081580627019449] := by
    have h := ladder_sq_mul h23
    have e : 2 * 10828996 + 1 = 21657993 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h25 : (52280367975162154 : ℕ) ^ 43315986 ≡ 68699089834943732 [MOD 120081580627019449] := by
    have h := ladder_sq h24
    have e : 2 * 21657993 = 43315986 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h26 : (52280367975162154 : ℕ) ^ 86631973 ≡ 1 [MOD 120081580627019449] := by
    have h := ladder_sq_mul h25
    have e : 2 * 43315986 + 1 = 86631973 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h27 : (52280367975162154 : ℕ) ^ 173263946 ≡ 1 [MOD 120081580627019449] := by
    have h := ladder_sq h26
    have e : 2 * 86631973 = 173263946 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h28 : (52280367975162154 : ℕ) ^ 346527892 ≡ 1 [MOD 120081580627019449] := by
    have h := ladder_sq h27
    have e : 2 * 173263946 = 346527892 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  exact h28

/-- divisibility form of the ℚ(√−67) record: `330017383² ∣ u^{p−1} − 1`
    with `u` the depth-2 Hensel unit root of trace `33525` in `ℚ(√−67)` — the doubly-marked field
        (class number one and irregular) acquires a certified Gold member. -/
theorem record_330017383_dvd :
    (330017383 : ℕ) ^ 2 ∣ 106546445419140355 ^ 330017382 - 1 := by
  have hsq : (330017383 : ℕ) ^ 2 = 108911473082168689 := by norm_num
  rw [hsq]
  exact dvd_sub_one_of_modEq (by norm_num) ladder_330017383

/-- divisibility form of the genus-grade record: `346527893² ∣ u^{p−1} − 1`
    with `u` the depth-2 Hensel unit root of trace `16990` in `ℚ(√−52)` (h = 2) — the
    first certified Gold member of a class-number-2 field at record height. -/
theorem record_genus_dvd :
    (346527893 : ℕ) ^ 2 ∣ 52280367975162154 ^ 346527892 - 1 := by
  have hsq : (346527893 : ℕ) ^ 2 = 120081580627019449 := by norm_num
  rw [hsq]
  exact dvd_sub_one_of_modEq (by norm_num) ladder_346527893

/-- **both records sit above the whole prior atlas**: each exceeds
    the previous record member `6811741`, and the larger record lies in the (10⁸, 10⁹]
    decade the C sweep opened. -/
theorem records_above_atlas :
    (6811741 : ℕ) < 330017383 ∧ (6811741 : ℕ) < 346527893 ∧
    (10 : ℕ) ^ 8 < 330017383 ∧ 330017383 < 10 ^ 9 := by decide

end Wieferich.RecordCertificates
