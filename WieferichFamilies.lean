/-
Copyright (c) 2026 Dillon Ryan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dillon Ryan
-/
import Mathlib
-- The broad import is deliberate and load-bearing: the top-level comparison
-- theorems below must elaborate in the same environment as Challenge.lean
-- (which imports all of Mathlib). A narrower import changes instance-resolution
-- paths and the comparator rejects byte-identical statements. Do not narrow.
import WieferichFamilies.Assembly
import WieferichFamilies.AtlasCertificates
import WieferichFamilies.BernoulliAnchors
import WieferichFamilies.CertifiedZone
import WieferichFamilies.ClassGroupStructure
import WieferichFamilies.ClassNumberOne
import WieferichFamilies.DepthTransfer
import WieferichFamilies.Dobrowolski
import WieferichFamilies.DobrowolskiBaseline
import WieferichFamilies.MetallicRegulator
import WieferichFamilies.PierceValues
import WieferichFamilies.Exclusions
import WieferichFamilies.GoldCriterion
import WieferichFamilies.GoldScope
import WieferichFamilies.HigherOrder
import WieferichFamilies.IwasawaGrid
import WieferichFamilies.LambdaLadder
import WieferichFamilies.LehmerCertificate
import WieferichFamilies.LiftDichotomy
import WieferichFamilies.LocusDisjointness
import WieferichFamilies.PierpontSmoothness
import WieferichFamilies.PisotClassFields
import WieferichFamilies.PlasticAnchor
import WieferichFamilies.PowerLadder
import WieferichFamilies.RecordCertificates
import WieferichFamilies.SearchCost
import WieferichFamilies.TraceReturns
import WieferichFamilies.ZsygmondyLTE

/-!
The four challenge statements (`Challenge.lean`), re-declared at top
level exactly as stated there, each proved by the library. This is the
surface the comparator checks.
-/

/-- The order-lift dichotomy: through a kernel of exponent `p`, orders
lift by `1` or exactly `p`. -/
theorem orderOf_dichotomy_of_ker_exponent {G H : Type*} [Group G] [Group H] {p : ℕ}
    (hp : p.Prime) (φ : G →* H) (hker : ∀ g : G, φ g = 1 → g ^ p = 1) (g : G)
    (hd : orderOf (φ g) ≠ 0) :
    orderOf g = orderOf (φ g) ∨ orderOf g = p * orderOf (φ g) :=
  Wieferich.LiftDichotomy.orderOf_dichotomy_of_ker_exponent hp φ hker g hd

/-- The certified zone: a factor floor `b` and the size bound `N < b²`
force primality. -/
theorem certified_zone {N b : ℕ} (h1 : 1 < N)
    (hb : ∀ q : ℕ, q.Prime → q ∣ N → b ≤ q) (hN : N < b ^ 2) :
    N.Prime :=
  Wieferich.CertifiedZone.certified_zone h1 hb hN

/-- Diagonal rigidity: in a commutative ring with `p² = 0`, the two roots
`1 + p·c` and `−1 + p·d` have `α^p + ᾱ^p = 0` for odd `p`. -/
theorem torsion_diagonal_rigid {S : Type*} [CommRing S] {p : ℕ} {c d : S}
    (hp2 : (p : S) ^ 2 = 0) (hodd : Odd p) :
    (1 + (p : S) * c) ^ p + (-1 + (p : S) * d) ^ p = 0 :=
  Wieferich.HigherOrder.torsion_diagonal_rigid hp2 hodd

/-- The Wieferich prime of Lehmer's polynomial: the depth-2 trace
condition at `p = 720847`, at the degree-10 companion matrix over
`ZMod p²`. -/
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
                  ![0, 0, 0, 0, 0, 0, 0, 0, 1, -1]]) ^ 720847).trace = -1 := by
  have hM : (Matrix.of ![![(0 : ZMod (720847 ^ 2)), 0, 0, 0, 0, 0, 0, 0, 0, -1],
                  ![1, 0, 0, 0, 0, 0, 0, 0, 0, -1],
                  ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
                  ![0, 0, 1, 0, 0, 0, 0, 0, 0, 1],
                  ![0, 0, 0, 1, 0, 0, 0, 0, 0, 1],
                  ![0, 0, 0, 0, 1, 0, 0, 0, 0, 1],
                  ![0, 0, 0, 0, 0, 1, 0, 0, 0, 1],
                  ![0, 0, 0, 0, 0, 0, 1, 0, 0, 1],
                  ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
                  ![0, 0, 0, 0, 0, 0, 0, 0, 1, -1]]) =
      Wieferich.LehmerCertificate.Mc := by decide
  rw [hM, Wieferich.LehmerCertificate.lehmer_wieferich_720847]
  decide
