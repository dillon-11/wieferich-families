import WieferichFamilies.PowerLadder

/-!
# Census members above 10⁷, certified

The three members of the 10⁸ census above 10⁷ beyond the two decade
records: `p = 32040013` and `p = 85611527` in ℚ(√−163) (traces 8005,
13135), and `p = 17525953` in ℚ(√−56), the first class-number-4 member at
this height. Each is certified by the O(log p) ladder (25–27 steps). With
`PowerLadder` and `RecordCertificates`, every census member above 10⁷
carries a kernel certificate.
-/

namespace Wieferich.AtlasCertificates

open Wieferich.PowerLadder

/-- Proved (ladder) — the depth-2 unit-root condition at `p = 32040013`:
    `256480312070^{p-1} ≡ 1 (mod p²)` via 25 square-and-multiply rungs,
    each a kernel `decide` below `p⁶` — certificate size `O(log p)`. -/
theorem ladder_32040013 : (256480312070 : ℕ) ^ 32040012 ≡ 1 [MOD 1026562433040169] := by
  have h0 : (256480312070 : ℕ) ^ 1 ≡ 256480312070 [MOD 1026562433040169] := by decide
  have h1 : (256480312070 : ℕ) ^ 3 ≡ 1026305952728099 [MOD 1026562433040169] := by
    have h := ladder_sq_mul h0
    have e : 2 * 1 + 1 = 3 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h2 : (256480312070 : ℕ) ^ 7 ≡ 1026305952728099 [MOD 1026562433040169] := by
    have h := ladder_sq_mul h1
    have e : 2 * 3 + 1 = 7 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h3 : (256480312070 : ℕ) ^ 15 ≡ 1026305952728099 [MOD 1026562433040169] := by
    have h := ladder_sq_mul h2
    have e : 2 * 7 + 1 = 15 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h4 : (256480312070 : ℕ) ^ 30 ≡ 1026562433040168 [MOD 1026562433040169] := by
    have h := ladder_sq h3
    have e : 2 * 15 = 30 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h5 : (256480312070 : ℕ) ^ 61 ≡ 256480312070 [MOD 1026562433040169] := by
    have h := ladder_sq_mul h4
    have e : 2 * 30 + 1 = 61 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h6 : (256480312070 : ℕ) ^ 122 ≡ 1026562433040168 [MOD 1026562433040169] := by
    have h := ladder_sq h5
    have e : 2 * 61 = 122 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h7 : (256480312070 : ℕ) ^ 244 ≡ 1 [MOD 1026562433040169] := by
    have h := ladder_sq h6
    have e : 2 * 122 = 244 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h8 : (256480312070 : ℕ) ^ 488 ≡ 1 [MOD 1026562433040169] := by
    have h := ladder_sq h7
    have e : 2 * 244 = 488 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h9 : (256480312070 : ℕ) ^ 977 ≡ 256480312070 [MOD 1026562433040169] := by
    have h := ladder_sq_mul h8
    have e : 2 * 488 + 1 = 977 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h10 : (256480312070 : ℕ) ^ 1955 ≡ 1026305952728099 [MOD 1026562433040169] := by
    have h := ladder_sq_mul h9
    have e : 2 * 977 + 1 = 1955 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h11 : (256480312070 : ℕ) ^ 3911 ≡ 1026305952728099 [MOD 1026562433040169] := by
    have h := ladder_sq_mul h10
    have e : 2 * 1955 + 1 = 3911 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h12 : (256480312070 : ℕ) ^ 7822 ≡ 1026562433040168 [MOD 1026562433040169] := by
    have h := ladder_sq h11
    have e : 2 * 3911 = 7822 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h13 : (256480312070 : ℕ) ^ 15644 ≡ 1 [MOD 1026562433040169] := by
    have h := ladder_sq h12
    have e : 2 * 7822 = 15644 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h14 : (256480312070 : ℕ) ^ 31289 ≡ 256480312070 [MOD 1026562433040169] := by
    have h := ladder_sq_mul h13
    have e : 2 * 15644 + 1 = 31289 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h15 : (256480312070 : ℕ) ^ 62578 ≡ 1026562433040168 [MOD 1026562433040169] := by
    have h := ladder_sq h14
    have e : 2 * 31289 = 62578 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h16 : (256480312070 : ℕ) ^ 125156 ≡ 1 [MOD 1026562433040169] := by
    have h := ladder_sq h15
    have e : 2 * 62578 = 125156 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h17 : (256480312070 : ℕ) ^ 250312 ≡ 1 [MOD 1026562433040169] := by
    have h := ladder_sq h16
    have e : 2 * 125156 = 250312 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h18 : (256480312070 : ℕ) ^ 500625 ≡ 256480312070 [MOD 1026562433040169] := by
    have h := ladder_sq_mul h17
    have e : 2 * 250312 + 1 = 500625 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h19 : (256480312070 : ℕ) ^ 1001250 ≡ 1026562433040168 [MOD 1026562433040169] := by
    have h := ladder_sq h18
    have e : 2 * 500625 = 1001250 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h20 : (256480312070 : ℕ) ^ 2002500 ≡ 1 [MOD 1026562433040169] := by
    have h := ladder_sq h19
    have e : 2 * 1001250 = 2002500 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h21 : (256480312070 : ℕ) ^ 4005001 ≡ 256480312070 [MOD 1026562433040169] := by
    have h := ladder_sq_mul h20
    have e : 2 * 2002500 + 1 = 4005001 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h22 : (256480312070 : ℕ) ^ 8010003 ≡ 1026305952728099 [MOD 1026562433040169] := by
    have h := ladder_sq_mul h21
    have e : 2 * 4005001 + 1 = 8010003 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h23 : (256480312070 : ℕ) ^ 16020006 ≡ 1026562433040168 [MOD 1026562433040169] := by
    have h := ladder_sq h22
    have e : 2 * 8010003 = 16020006 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h24 : (256480312070 : ℕ) ^ 32040012 ≡ 1 [MOD 1026562433040169] := by
    have h := ladder_sq h23
    have e : 2 * 16020006 = 32040012 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  exact h24
/-- Proved (ladder) — the depth-2 unit-root condition at `p = 85611527`:
    `1393884676144324^{p-1} ≡ 1 (mod p²)` via 27 square-and-multiply rungs,
    each a kernel `decide` below `p⁶` — certificate size `O(log p)`. -/
theorem ladder_85611527 : (1393884676144324 : ℕ) ^ 85611526 ≡ 1 [MOD 7329333555271729] := by
  have h0 : (1393884676144324 : ℕ) ^ 1 ≡ 1393884676144324 [MOD 7329333555271729] := by decide
  have h1 : (1393884676144324 : ℕ) ^ 2 ≡ 1305171 [MOD 7329333555271729] := by
    have h := ladder_sq h0
    have e : 2 * 1 = 2 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h2 : (1393884676144324 : ℕ) ^ 5 ≡ 5908682893886082 [MOD 7329333555271729] := by
    have h := ladder_sq_mul h1
    have e : 2 * 2 + 1 = 5 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h3 : (1393884676144324 : ℕ) ^ 10 ≡ 3510352433814639 [MOD 7329333555271729] := by
    have h := ladder_sq h2
    have e : 2 * 5 = 10 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h4 : (1393884676144324 : ℕ) ^ 20 ≡ 6244542246953447 [MOD 7329333555271729] := by
    have h := ladder_sq h3
    have e : 2 * 10 = 20 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h5 : (1393884676144324 : ℕ) ^ 40 ≡ 4780890072117519 [MOD 7329333555271729] := by
    have h := ladder_sq h4
    have e : 2 * 20 = 40 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h6 : (1393884676144324 : ℕ) ^ 81 ≡ 2466714748946434 [MOD 7329333555271729] := by
    have h := ladder_sq_mul h5
    have e : 2 * 40 + 1 = 81 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h7 : (1393884676144324 : ℕ) ^ 163 ≡ 5931165536363829 [MOD 7329333555271729] := by
    have h := ladder_sq_mul h6
    have e : 2 * 81 + 1 = 163 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h8 : (1393884676144324 : ℕ) ^ 326 ≡ 1071366502391855 [MOD 7329333555271729] := by
    have h := ladder_sq h7
    have e : 2 * 163 = 326 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h9 : (1393884676144324 : ℕ) ^ 653 ≡ 2902632489051878 [MOD 7329333555271729] := by
    have h := ladder_sq_mul h8
    have e : 2 * 326 + 1 = 653 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h10 : (1393884676144324 : ℕ) ^ 1306 ≡ 5849457372117120 [MOD 7329333555271729] := by
    have h := ladder_sq h9
    have e : 2 * 653 = 1306 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h11 : (1393884676144324 : ℕ) ^ 2612 ≡ 4458989770477950 [MOD 7329333555271729] := by
    have h := ladder_sq h10
    have e : 2 * 1306 = 2612 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h12 : (1393884676144324 : ℕ) ^ 5225 ≡ 6826002503820173 [MOD 7329333555271729] := by
    have h := ladder_sq_mul h11
    have e : 2 * 2612 + 1 = 5225 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h13 : (1393884676144324 : ℕ) ^ 10450 ≡ 4374871973424156 [MOD 7329333555271729] := by
    have h := ladder_sq h12
    have e : 2 * 5225 = 10450 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h14 : (1393884676144324 : ℕ) ^ 20901 ≡ 517245051291707 [MOD 7329333555271729] := by
    have h := ladder_sq_mul h13
    have e : 2 * 10450 + 1 = 20901 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h15 : (1393884676144324 : ℕ) ^ 41802 ≡ 3884414843170990 [MOD 7329333555271729] := by
    have h := ladder_sq h14
    have e : 2 * 20901 = 41802 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h16 : (1393884676144324 : ℕ) ^ 83605 ≡ 3468735588182051 [MOD 7329333555271729] := by
    have h := ladder_sq_mul h15
    have e : 2 * 41802 + 1 = 83605 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h17 : (1393884676144324 : ℕ) ^ 167210 ≡ 559953378429403 [MOD 7329333555271729] := by
    have h := ladder_sq h16
    have e : 2 * 83605 = 167210 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h18 : (1393884676144324 : ℕ) ^ 334420 ≡ 1721949297231923 [MOD 7329333555271729] := by
    have h := ladder_sq h17
    have e : 2 * 167210 = 334420 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h19 : (1393884676144324 : ℕ) ^ 668840 ≡ 4379765302098957 [MOD 7329333555271729] := by
    have h := ladder_sq h18
    have e : 2 * 334420 = 668840 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h20 : (1393884676144324 : ℕ) ^ 1337680 ≡ 6873986602089940 [MOD 7329333555271729] := by
    have h := ladder_sq h19
    have e : 2 * 668840 = 1337680 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h21 : (1393884676144324 : ℕ) ^ 2675360 ≡ 1136604697580696 [MOD 7329333555271729] := by
    have h := ladder_sq h20
    have e : 2 * 1337680 = 2675360 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h22 : (1393884676144324 : ℕ) ^ 5350720 ≡ 3988762618436725 [MOD 7329333555271729] := by
    have h := ladder_sq h21
    have e : 2 * 2675360 = 5350720 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h23 : (1393884676144324 : ℕ) ^ 10701440 ≡ 4135336697147744 [MOD 7329333555271729] := by
    have h := ladder_sq h22
    have e : 2 * 5350720 = 10701440 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h24 : (1393884676144324 : ℕ) ^ 21402881 ≡ 1918870238554053 [MOD 7329333555271729] := by
    have h := ladder_sq_mul h23
    have e : 2 * 10701440 + 1 = 21402881 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h25 : (1393884676144324 : ℕ) ^ 42805763 ≡ 1 [MOD 7329333555271729] := by
    have h := ladder_sq_mul h24
    have e : 2 * 21402881 + 1 = 42805763 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h26 : (1393884676144324 : ℕ) ^ 85611526 ≡ 1 [MOD 7329333555271729] := by
    have h := ladder_sq h25
    have e : 2 * 42805763 = 85611526 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  exact h26
/-- Proved (ladder) — the depth-2 unit-root condition at `p = 17525953`:
    `218200656119811^{p-1} ≡ 1 (mod p²)` via 25 square-and-multiply rungs,
    each a kernel `decide` below `p⁶` — certificate size `O(log p)`. -/
theorem ladder_17525953 : (218200656119811 : ℕ) ^ 17525952 ≡ 1 [MOD 307159028558209] := by
  have h0 : (218200656119811 : ℕ) ^ 1 ≡ 218200656119811 [MOD 307159028558209] := by decide
  have h1 : (218200656119811 : ℕ) ^ 2 ≡ 8851970 [MOD 307159028558209] := by
    have h := ladder_sq h0
    have e : 2 * 1 = 2 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h2 : (218200656119811 : ℕ) ^ 4 ≡ 78357372880900 [MOD 307159028558209] := by
    have h := ladder_sq h1
    have e : 2 * 2 = 4 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h3 : (218200656119811 : ℕ) ^ 8 ≡ 281770825599533 [MOD 307159028558209] := by
    have h := ladder_sq h2
    have e : 2 * 4 = 8 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h4 : (218200656119811 : ℕ) ^ 16 ≡ 207825482566051 [MOD 307159028558209] := by
    have h := ladder_sq h3
    have e : 2 * 8 = 16 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h5 : (218200656119811 : ℕ) ^ 33 ≡ 253869191083171 [MOD 307159028558209] := by
    have h := ladder_sq_mul h4
    have e : 2 * 16 + 1 = 33 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h6 : (218200656119811 : ℕ) ^ 66 ≡ 272403500494595 [MOD 307159028558209] := by
    have h := ladder_sq h5
    have e : 2 * 33 = 66 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h7 : (218200656119811 : ℕ) ^ 133 ≡ 100967904105702 [MOD 307159028558209] := by
    have h := ladder_sq_mul h6
    have e : 2 * 66 + 1 = 133 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h8 : (218200656119811 : ℕ) ^ 267 ≡ 186374808100650 [MOD 307159028558209] := by
    have h := ladder_sq_mul h7
    have e : 2 * 133 + 1 = 267 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h9 : (218200656119811 : ℕ) ^ 534 ≡ 92481770604389 [MOD 307159028558209] := by
    have h := ladder_sq h8
    have e : 2 * 267 = 534 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h10 : (218200656119811 : ℕ) ^ 1069 ≡ 7913822775296 [MOD 307159028558209] := by
    have h := ladder_sq_mul h9
    have e : 2 * 534 + 1 = 1069 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h11 : (218200656119811 : ℕ) ^ 2139 ≡ 231905037465655 [MOD 307159028558209] := by
    have h := ladder_sq_mul h10
    have e : 2 * 1069 + 1 = 2139 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h12 : (218200656119811 : ℕ) ^ 4278 ≡ 221427424472193 [MOD 307159028558209] := by
    have h := ladder_sq h11
    have e : 2 * 2139 = 4278 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h13 : (218200656119811 : ℕ) ^ 8557 ≡ 97957702573824 [MOD 307159028558209] := by
    have h := ladder_sq_mul h12
    have e : 2 * 4278 + 1 = 8557 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h14 : (218200656119811 : ℕ) ^ 17115 ≡ 269515466502195 [MOD 307159028558209] := by
    have h := ladder_sq_mul h13
    have e : 2 * 8557 + 1 = 17115 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h15 : (218200656119811 : ℕ) ^ 34230 ≡ 123748885429696 [MOD 307159028558209] := by
    have h := ladder_sq h14
    have e : 2 * 17115 = 34230 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h16 : (218200656119811 : ℕ) ^ 68460 ≡ 264216013617150 [MOD 307159028558209] := by
    have h := ladder_sq h15
    have e : 2 * 34230 = 68460 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h17 : (218200656119811 : ℕ) ^ 136921 ≡ 26371676472244 [MOD 307159028558209] := by
    have h := ladder_sq_mul h16
    have e : 2 * 68460 + 1 = 136921 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h18 : (218200656119811 : ℕ) ^ 273843 ≡ 42090178373355 [MOD 307159028558209] := by
    have h := ladder_sq_mul h17
    have e : 2 * 136921 + 1 = 273843 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h19 : (218200656119811 : ℕ) ^ 547686 ≡ 126392747590901 [MOD 307159028558209] := by
    have h := ladder_sq h18
    have e : 2 * 273843 = 547686 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h20 : (218200656119811 : ℕ) ^ 1095372 ≡ 237028502265521 [MOD 307159028558209] := by
    have h := ladder_sq h19
    have e : 2 * 547686 = 1095372 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h21 : (218200656119811 : ℕ) ^ 2190744 ≡ 34356118748007 [MOD 307159028558209] := by
    have h := ladder_sq h20
    have e : 2 * 1095372 = 2190744 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h22 : (218200656119811 : ℕ) ^ 4381488 ≡ 307159028558208 [MOD 307159028558209] := by
    have h := ladder_sq h21
    have e : 2 * 2190744 = 4381488 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h23 : (218200656119811 : ℕ) ^ 8762976 ≡ 1 [MOD 307159028558209] := by
    have h := ladder_sq h22
    have e : 2 * 4381488 = 8762976 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  have h24 : (218200656119811 : ℕ) ^ 17525952 ≡ 1 [MOD 307159028558209] := by
    have h := ladder_sq h23
    have e : 2 * 8762976 = 17525952 := by norm_num
    rw [e] at h; exact h.trans (by decide)
  exact h24

/-- the three high members are distinct from the decade records and
    ordered: `17525953 < 32040013 < 85611527 < 330017383`. -/
theorem atlas_high_members_ordered :
    (17525953 : ℕ) < 32040013 ∧ (32040013 : ℕ) < 85611527 ∧
    (85611527 : ℕ) < 330017383 := by decide

end Wieferich.AtlasCertificates
