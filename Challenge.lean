/-
  Challenge: Wieferich phenomena of algebraic units — headline statements,
  Mathlib-only.

  1. `orderOf_dichotomy_of_ker_exponent`: the order-lift dichotomy. For any
     group homomorphism whose kernel has exponent `p`, element orders lift
     by a factor of `1` or exactly `p`. The reduction
     `(R/p²R)ˣ → (R/pR)ˣ` of any order `R = ℤ[α]` satisfies the
     hypothesis, so every Wieferich-type condition (base 2, Wall–Sun–Sun,
     Perrin-square, Gold's criterion) is an instance.

  2. `certified_zone`: if every prime factor of `N` is at least `b` and
     `N < b²`, then `N` is prime — the elementary half of the N−1 method,
     with the factor floor supplied by the congruence sieve of the towers.

  3. `torsion_diagonal_rigid`: on the diagonal classes of the family
     x² − kx − 1 the depth-2 condition never holds — the emptiness
     observed in the census is a theorem.

  4. `wieferich_720847_trace`: the Wieferich prime of Lehmer's polynomial.
     The trace of the p-th power of the degree-10 companion matrix of
     `x¹⁰ + x⁹ − x⁷ − x⁶ − x⁵ − x⁴ − x³ + x + 1` over `ZMod p²` equals
     `−1` at `p = 720847` — the depth-2 condition for the smallest known
     Salem number.

  The `sorry`s below are the challenge form; the proofs are in the
  `WieferichFamilies` library of this repository (`lake build`; each
  theorem's axiom footprint is `propext`, `Classical.choice`,
  `Quot.sound` or smaller).
-/
import Mathlib

/-- The order-lift dichotomy: through a kernel of exponent `p`, orders
lift by `1` or exactly `p`. -/
theorem orderOf_dichotomy_of_ker_exponent {G H : Type*} [Group G] [Group H] {p : ℕ}
    (hp : p.Prime) (φ : G →* H) (hker : ∀ g : G, φ g = 1 → g ^ p = 1) (g : G)
    (hd : orderOf (φ g) ≠ 0) :
    orderOf g = orderOf (φ g) ∨ orderOf g = p * orderOf (φ g) := sorry

/-- The certified zone: a factor floor `b` and the size bound `N < b²`
force primality. -/
theorem certified_zone {N b : ℕ} (h1 : 1 < N)
    (hb : ∀ q : ℕ, q.Prime → q ∣ N → b ≤ q) (hN : N < b ^ 2) :
    N.Prime := sorry

/-- Diagonal rigidity: in a commutative ring with `p² = 0`, the two roots
`1 + p·c` and `−1 + p·d` have `α^p + ᾱ^p = 0` for odd `p`, so the
depth-2 condition with nonzero diagonal target never holds. -/
theorem torsion_diagonal_rigid {S : Type*} [CommRing S] {p : ℕ} {c d : S}
    (hp2 : (p : S) ^ 2 = 0) (hodd : Odd p) :
    (1 + (p : S) * c) ^ p + (-1 + (p : S) * d) ^ p = 0 := sorry

/-- The Wieferich prime of Lehmer's polynomial: the depth-2 trace
condition at `p = 720847`, stated at the companion matrix of
`x¹⁰ + x⁹ − x⁷ − x⁶ − x⁵ − x⁴ − x³ + x + 1` over `ZMod p²`. -/
theorem wieferich_720847_trace :
    ((Matrix.of ![![(0 : ZMod (720847 ^ 2)), 0, 0, 0, 0, 0, 0, 0, 0, -1],
                  ![1, 0, 0, 0, 0, 0, 0, 0, 0, -1],
                  ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
                  ![0, 0, 1, 0, 0, 0, 0, 0, 0, 1],
                  ![0, 0, 0, 1, 0, 0, 0, 0, 0, 1],
                  ![0, 0, 0, 0, 1, 0, 0, 0, 0, 1],
                  ![0, 0, 0, 0, 0, 1, 0, 0, 0, 1],
                  ![0, 0, 0, 0, 0, 0, 1, 0, 0, 1],
                  ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
                  ![0, 0, 0, 0, 0, 0, 0, 0, 1, -1]]) ^ 720847).trace = -1 := sorry
