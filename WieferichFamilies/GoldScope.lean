/-
Copyright (c) 2026 Dillon Ryan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dillon Ryan
-/
import WieferichFamilies.LiftDichotomy

/-!
# Gold's criterion on the principal stratum

Gold's criterion (J. Number Theory 6 (1974)): for `K` imaginary
quadratic, `p > 3` with `p ∤ h_K`, `pO_K = 𝔭𝔭̄`, and `𝔭^h = (α)`:
`λ_p(K) > 1 ⟺ α^(p−1) ≡ 1 (mod 𝔭̄²)`. The census of the paper restricts
to `𝔭 = (π)` principal and flags `π^(p−1) ≡ 1 (mod 𝔭̄²)`. This module
proves the two flags equivalent: the obstruction `y = π^(p−1) mod 𝔭̄²`
lies in `1 + 𝔭̄/𝔭̄²`, so `y^p = 1`; an element of order dividing both `p`
and `h` with `gcd(h, p) = 1` is trivial. Every census member at `h ≤ 5`
is therefore an unconditional witness of `λ_p(K) > 1`.

## Main results

* `pow_eq_one_iff_of_coprime`
* `depth_two_flag_iff_power_flag`
* `census_flag_iff_gold_flag`
-/

namespace Wieferich.GoldScope

/-- **coprime order collapse**: in any monoid, if `y^p = 1` and
    `gcd(h, p) = 1`, then `y^h = 1 ⟺ y = 1`. The order of `y` divides both, hence
    divides their gcd. -/
theorem pow_eq_one_iff_of_coprime {M : Type*} [Monoid M] {y : M} {h p : ℕ}
    (hyp : y ^ p = 1) (hcop : Nat.Coprime h p) : y ^ h = 1 ↔ y = 1 := by
  constructor
  · intro hh
    have h1 : orderOf y ∣ h := orderOf_dvd_of_pow_eq_one hh
    have h2 : orderOf y ∣ p := orderOf_dvd_of_pow_eq_one hyp
    have hg : orderOf y ∣ Nat.gcd h p := Nat.dvd_gcd h1 h2
    rw [hcop] at hg
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_one hg ▸ rfl)
  · intro hy; rw [hy, one_pow]

/-- **the depth-2 flag is `h`-power-insensitive**: in a commutative ring
    with `x² = 0` and `p·x = 0` (the obstruction module `𝔭̄/𝔭̄²` with `p ∈ 𝔭̄`),
    `(1+x)^h = 1 ⟺ x = 0` whenever `gcd(h, p) = 1`. So testing the generator `π`
    or the class-power generator `α = π^h` flags the same primes. -/
theorem depth_two_flag_iff_power_flag {S : Type*} [CommRing S] {x : S} {h p : ℕ}
    (hx : x ^ 2 = 0) (hpx : (p : S) * x = 0) (hcop : Nat.Coprime h p) :
    (1 + x) ^ h = 1 ↔ x = 0 := by
  have hyp : (1 + x) ^ p = 1 := by
    rw [Wieferich.LiftDichotomy.one_add_pow_of_sq_zero hx p, hpx, add_zero]
  rw [pow_eq_one_iff_of_coprime hyp hcop]
  constructor
  · intro h1
    have := congrArg (· - 1) h1
    simpa using this
  · intro h0; rw [h0, add_zero]

/-- **the census flag is Gold's flag** (named specialization): with
    `y = π^{p−1} mod 𝔭̄²` written `1 + x` (`x ∈ 𝔭̄/𝔭̄²`, square-zero, `p`-torsion)
    and `h = h_K` coprime to `p` (true whenever `h_K < p`, i.e. all 47 census
    fields at every member), Gold's condition `(π^{p−1})^{h} ≡ 1` holds iff the
    census condition `π^{p−1} ≡ 1` does. -/
theorem census_flag_iff_gold_flag {S : Type*} [CommRing S] {x : S} {h p : ℕ}
    (hx : x ^ 2 = 0) (hpx : (p : S) * x = 0) (hp : p.Prime) (hlt : 0 < h)
    (hh : h < p) : (1 + x) ^ h = 1 ↔ 1 + x = 1 := by
  have hcop : Nat.Coprime h p :=
    Nat.Coprime.symm (hp.coprime_iff_not_dvd.mpr
      (fun hdvd => absurd (Nat.le_of_dvd hlt hdvd) (not_le.mpr hh)))
  rw [depth_two_flag_iff_power_flag hx hpx hcop]
  constructor
  · intro h0; rw [h0, add_zero]
  · intro h1
    have := congrArg (· - 1) h1
    simpa using this

end Wieferich.GoldScope
