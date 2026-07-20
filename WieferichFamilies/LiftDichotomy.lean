/-
Copyright (c) 2026 Dillon Ryan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dillon Ryan
-/
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.Group.Units.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
# The order-lift dichotomy

Passing from `p` to `p²`, the multiplicative order of a unit either stays
equal or multiplies by exactly `p`. The Wieferich condition on a unit `α`
(classically `p² ∣ 2^(p−1) − 1`, Wieferich 1909) is the first branch; the
second is generic. This module proves the dichotomy in the generality it
holds at, and instantiates it for the reduction `(R/p²R)ˣ → (R/pR)ˣ` of an
arbitrary order `R = ℤ[α]`.

## Main results

* `orderOf_dichotomy_of_ker_exponent`: for a group homomorphism
  `φ : G →* H` whose kernel has exponent `p`, `orderOf g` equals
  `orderOf (φ g)` or `p * orderOf (φ g)`.
* `one_add_pow_of_sq_zero`: in a commutative ring, `x² = 0` implies
  `(1 + x)^n = 1 + n·x`.
* `ker_pow_prime_eq_one`: if `p² = 0` in `S`, every element `1 + p·c` has
  `p`-th power `1` — so the reduction kernel has exponent `p`.
* `LiftDatum`, `lift_dichotomy`: the packaged instantiation. The
  only structural input is that reduction-trivial units have the form
  `1 + p·c`; the dichotomy follows for every order.

The specializations — base 2, Wall–Sun–Sun (Wall, *Fibonacci series
modulo m*, Amer. Math. Monthly 67 (1960); Sun–Sun, Acta Arith. 60 (1992)),
Perrin-square, and Gold's criterion for imaginary quadratic fields
(Gold, J. Number Theory 6 (1974)) — are rows of `lift_dichotomy`.
-/

namespace Wieferich.LiftDichotomy

/-! ## The general group lemma -/

/-- **The order-lift dichotomy.** If `φ : G →* H` has kernel of exponent `p`
    (every kernel element satisfies `k^p = 1`) and `φ g` has finite positive
    order, then `orderOf g` is `orderOf (φ g)` or `p * orderOf (φ g)`. -/
theorem orderOf_dichotomy_of_ker_exponent {G H : Type*} [Group G] [Group H] {p : ℕ}
    (hp : p.Prime) (φ : G →* H) (hker : ∀ g : G, φ g = 1 → g ^ p = 1) (g : G)
    (hd : orderOf (φ g) ≠ 0) :
    orderOf g = orderOf (φ g) ∨ orderOf g = p * orderOf (φ g) := by
  set d := orderOf (φ g) with hdef
  have hdvd : d ∣ orderOf g := orderOf_map_dvd φ g
  have h1 : φ (g ^ d) = 1 := by rw [map_pow, hdef, pow_orderOf_eq_one]
  have h2 : (g ^ d) ^ p = 1 := hker _ h1
  have h3 : orderOf g ∣ d * p := orderOf_dvd_of_pow_eq_one (by rwa [← pow_mul] at h2)
  obtain ⟨k, hk⟩ := hdvd
  have hdne : d ≠ 0 := hd
  have hkp : k ∣ p := by
    have : d * k ∣ d * p := hk ▸ h3
    exact (mul_dvd_mul_iff_left hdne).mp this
  rcases (Nat.Prime.eq_one_or_self_of_dvd hp k hkp) with h | h
  · left; rw [hk, h, mul_one]
  · right; rw [hk, h, mul_comm]

/-! ## The binomial collapse -/

/-- In a commutative ring, `x² = 0` implies `(1 + x)^n = 1 + n·x`. -/
theorem one_add_pow_of_sq_zero {S : Type*} [CommRing S] {x : S} (hx : x ^ 2 = 0) :
    ∀ n : ℕ, (1 + x) ^ n = 1 + n * x := by
  intro n
  induction n with
  | zero => simp
  | succ m ih =>
    have hxx : x * x = 0 := by rw [← sq]; exact hx
    rw [pow_succ, ih, Nat.cast_succ]
    linear_combination (m : S) * hxx

/-- If `p² = 0` in `S` (e.g. `S = R/p²R`), then
    `(1 + p·c)^p = 1 + p²·c`. -/
theorem ker_pow_prime {S : Type*} [CommRing S] {p : ℕ} {c : S}
    (hp2 : (p : S) ^ 2 = 0) : (1 + (p : S) * c) ^ p = 1 + (p : S) ^ 2 * c := by
  have hx : ((p : S) * c) ^ 2 = 0 := by linear_combination c ^ 2 * hp2
  rw [one_add_pow_of_sq_zero hx p]
  ring

/-- If `p² = 0` in `S`, every element of the form `1 + p·c` has `p`-th
    power `1`: the reduction kernel `1 + pS` has exponent `p`. -/
theorem ker_pow_prime_eq_one {S : Type*} [CommRing S] {p : ℕ} {c : S}
    (hp2 : (p : S) ^ 2 = 0) : (1 + (p : S) * c) ^ p = 1 := by
  rw [ker_pow_prime hp2, hp2, zero_mul, add_zero]

/-! ## The instantiation for orders -/

/-- The data of a depth-2 reduction `φ : Sˣ →* Tˣ` (typically
    `S = R/p²R → T = R/pR` for an order `R = ℤ[α]`): `p²` vanishes in `S`,
    and reduction-trivial units have the form `1 + p·c`. Both hold for the
    reduction of any order at any prime. -/
structure LiftDatum {S T : Type*} [CommRing S] [CommRing T] (p : ℕ)
    (φ : Sˣ →* Tˣ) where
  /-- `p² = 0` in the depth-2 quotient. -/
  p_sq_zero : (p : S) ^ 2 = 0
  /-- reduction-trivial units have the form `1 + p·c` (the kernel is `1 + pS`). -/
  kernel_form : ∀ u : Sˣ, φ u = 1 → ∃ c : S, (u : S) = 1 + (p : S) * c

/-- Given a `LiftDatum`, every unit of the depth-2 quotient has order
    equal to its depth-1 order or exactly `p` times it. The classical
    Wieferich, Wall–Sun–Sun, Perrin-square, and Gold conditions are
    instances (`R = ℤ`, `ℤ[φ]`, `ℤ[ρ]`, `O_K`). -/
theorem lift_dichotomy {S T : Type*} [CommRing S] [CommRing T] {p : ℕ}
    (hp : p.Prime) {φ : Sˣ →* Tˣ} (D : LiftDatum p φ) (u : Sˣ)
    (hd : orderOf (φ u) ≠ 0) :
    orderOf u = orderOf (φ u) ∨ orderOf u = p * orderOf (φ u) := by
  refine orderOf_dichotomy_of_ker_exponent hp φ ?_ u hd
  intro g hg
  obtain ⟨c, hc⟩ := D.kernel_form g hg
  ext
  push_cast
  rw [hc]
  exact ker_pow_prime_eq_one D.p_sq_zero

end Wieferich.LiftDichotomy
