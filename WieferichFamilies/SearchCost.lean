import WieferichFamilies.CertifiedZone

/-!
# Cost accounting for sieve-and-certify prime search

The cost model for a pipeline that reads `R` candidate indices, sieves
them to `S` survivors, searches the survivors with an oracle of unit cost
`o` (quadratically accelerated, e.g. Grover search), and certifies one
output: `engineCost = r·R + √S·o + c`, exact over ℕ.

## Main results

* `grover_face_quadratic`: `(√S)² ≤ S`.
* `engine_le_scan`: the pipeline never costs more than the linear scan.
* `engine_lt_scan`: it costs strictly less once `S > 1` and the oracle is
  not free.
* `lane_compression_mono`: any sieve improvement that shrinks `S` shrinks
  the bound.
* `engine_end_to_end` / `engine_end_to_end_modeq`: cost bound and
  primality of the output in one statement; the correctness conjunct is
  `certified_zone`.
* `engine_cost_stage_r`, `engine_cost_100M`: exact instances
  (`√25 = 5`, `√(4·10⁶) = 2000`).
-/

namespace Wieferich.SearchCost

open Wieferich.CertifiedZone

/-- The pipeline cost model: per-index readout cost times `R` indices,
plus `Nat.sqrt survivors` oracle calls (quadratically accelerated search),
plus one certificate. Exact ℕ arithmetic. -/
def engineCost (readout R survivors oracle cert : ℕ) : ℕ :=
  readout * R + Nat.sqrt survivors * oracle + cert

/-- The search stage stays within its quadratic budget: `(√S)² ≤ S`. -/
theorem grover_face_quadratic (S : ℕ) : Nat.sqrt S ^ 2 ≤ S := by
  simpa [pow_two] using Nat.sqrt_le' S

/-- The pipeline never costs more than the linear scan it replaces. -/
theorem engine_le_scan (r R S o c : ℕ) :
    engineCost r R S o c ≤ r * R + S * o + c := by
  unfold engineCost
  have h : Nat.sqrt S * o ≤ S * o :=
    Nat.mul_le_mul_right o (Nat.sqrt_le_self S)
  omega

/-- With more than one survivor and a non-free oracle the pipeline is
strictly cheaper than the linear scan. -/
theorem engine_lt_scan (r R c : ℕ) {S o : ℕ} (hS : 1 < S) (ho : 0 < o) :
    engineCost r R S o c < r * R + S * o + c := by
  unfold engineCost
  have h : Nat.sqrt S * o < S * o :=
    Nat.mul_lt_mul_of_lt_of_le (Nat.sqrt_lt_self hS) le_rfl ho
  omega

/-- Monotonicity in the survivor count: any sieve improvement that shrinks
the survivor set (`S' ≤ S`) shrinks the cost bound. Successive sieves
compose, each feeding a smaller `S` to the next stage. -/
theorem lane_compression_mono (r R o c : ℕ) {S' S : ℕ} (h : S' ≤ S) :
    engineCost r R S' o c ≤ engineCost r R S o c := by
  unfold engineCost
  have hs : Nat.sqrt S' ≤ Nat.sqrt S := Nat.sqrt_le_sqrt h
  have h2 : Nat.sqrt S' * o ≤ Nat.sqrt S * o := Nat.mul_le_mul_right o hs
  omega

/-- The end-to-end statement: the output candidate `N`, sieved to factor
floor `b` inside the certified zone, is prime, and the run cost is bounded
by readout + √-search + certificate, itself at most the linear scan. -/
theorem engine_end_to_end {N b : ℕ} (r R S o c : ℕ) (h1 : 1 < N)
    (hb : ∀ q : ℕ, q.Prime → q ∣ N → b ≤ q) (hN : N < b ^ 2) :
    N.Prime ∧ engineCost r R S o c ≤ r * R + S * o + c :=
  ⟨certified_zone h1 hb hN, engine_le_scan r R S o c⟩

/-- Congruence form: when the Zsygmondy sieve delivers all factors
`≡ 1 (mod n)` (floor `n+1`), the same end-to-end statement rides
`certified_zone_modeq`. -/
theorem engine_end_to_end_modeq {N n : ℕ} (r R S o c : ℕ) (h1 : 1 < N)
    (hq : ∀ q : ℕ, q.Prime → q ∣ N → q ≡ 1 [MOD n])
    (hN : N < (n + 1) ^ 2) :
    N.Prime ∧ engineCost r R S o c ≤ r * R + S * o + c :=
  ⟨certified_zone_modeq h1 hq hN, engine_le_scan r R S o c⟩

/-- Instance with the census values of the paper: 40 indices read, 25
sieve survivors; the search stage spends `√25 = 5` oracle calls where a
scan spends 25. -/
theorem engine_cost_stage_r (r o c : ℕ) :
    engineCost r 40 25 o c = r * 40 + 5 * o + c := by
  have h : Nat.sqrt 25 = 5 := by simpa using Nat.sqrt_eq 5
  unfold engineCost; rw [h]

/-- Instance at the 100-million-digit scale: with the expected search
multiplicity of ~4·10⁶ candidates per hit at standard trial-factoring
depth, the search stage spends exactly `√(4·10⁶) = 2000` oracle calls. -/
theorem engine_cost_100M (r R o c : ℕ) :
    engineCost r R 4000000 o c = r * R + 2000 * o + c := by
  have h : Nat.sqrt 4000000 = 2000 := by simpa using Nat.sqrt_eq 2000
  unfold engineCost; rw [h]

end Wieferich.SearchCost
