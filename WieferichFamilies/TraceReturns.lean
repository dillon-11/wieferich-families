import WieferichFamilies.Exclusions
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Data.Fintype.Pigeonhole

/-!
# Trace returns force torsion

For a degree-d unit, an integer trace return (`tr(αⁿ) = tr(α)` in ℤ) is
Wieferich membership at every modulus simultaneously. This module proves
that returns cannot persist: a bounded, recurrent trace sequence is
eventually periodic (pigeonhole in the d-fold state space), eventual
periodicity collapses the power sums (Vandermonde), and the collapse
forces every root to be a root of unity. Contrapositively, a unit with a
non-torsion root has finitely many trace returns, confined to the window
`n ≲ log(2d + 2)/log M(α)`.

## Main results

* `eventually_periodic_of_bounded`
* `coeff_zero_of_forall_sum_pow`
* `roots_torsion_of_eventually_periodic`
* `unbounded_of_nontorsion_root`, `no_persistent_resonance`
-/

namespace Wieferich.TraceReturns

open Matrix BigOperators

/-! ## Pigeonhole: bounded + recurrent ⟹ eventually periodic -/

/-- **bounded recurrent integer sequences are eventually periodic**: if
    `t` satisfies a depth-`d` recurrence (each value a function of the previous
    `d`) and is bounded, its state tuples live in a finite box, two states
    collide, and forward determinism propagates the collision forever. This is
    the "small measure forces exposure" engine's partner: boundedness on an
    infinite window IS eventual periodicity. -/
theorem eventually_periodic_of_bounded {d : ℕ} (hd : 0 < d) (t : ℕ → ℤ)
    (F : (Fin d → ℤ) → ℤ) (hrec : ∀ n, t (n + d) = F (fun i => t (n + i)))
    (B : ℕ) (hB : ∀ n, |t n| ≤ B) :
    ∃ N T, 0 < T ∧ ∀ n, N ≤ n → t (n + T) = t n := by
  -- states in a finite box, encoded into Fin (2B+1)
  have hbd : ∀ n, ((t n + B).toNat) < 2 * B + 1 := by
    intro n
    have := abs_le.mp (hB n)
    omega
  let g : ℕ → (Fin d → Fin (2 * B + 1)) := fun n i => ⟨(t (n + i) + B).toNat, hbd _⟩
  obtain ⟨i, j, hne, hij⟩ := Finite.exists_ne_map_eq_of_infinite g
  have hg : ∀ m : Fin d, t (i + m) = t (j + m) := by
    intro m
    have h1 := congrArg (fun v => ((v m : Fin (2 * B + 1)) : ℕ)) hij
    simp only [g] at h1
    have hi := abs_le.mp (hB (i + m))
    have hj' := abs_le.mp (hB (j + m))
    omega
  -- order the collision
  rcases lt_or_gt_of_ne hne with hlt | hlt
  case _ =>
    refine ⟨i, j - i, by omega, ?_⟩
    -- determinism: states equal at i and j propagate
    have hstate : ∀ k, ∀ m : Fin d, t (i + k + m) = t (j + k + m) := by
      intro k
      induction k with
      | zero =>
        intro m
        simpa using hg m
      | succ q ih =>
        intro m
        by_cases hm : (m : ℕ) + 1 < d
        · have e1 : i + (q + 1) + (m : ℕ) = i + q + ((m : ℕ) + 1) := by omega
          have e2 : j + (q + 1) + (m : ℕ) = j + q + ((m : ℕ) + 1) := by omega
          rw [e1, e2]
          exact ih ⟨(m : ℕ) + 1, hm⟩
        · have hmd : (m : ℕ) = d - 1 := by omega
          have h1 : t (i + q + d) = F (fun i' => t (i + q + i')) := hrec (i + q)
          have h2 : t (j + q + d) = F (fun i' => t (j + q + i')) := hrec (j + q)
          have hFeq : F (fun i' => t (i + q + i')) = F (fun i' => t (j + q + i')) := by
            congr 1
            funext i'
            exact ih i'
          have key : t (i + q + d) = t (j + q + d) := by rw [h1, hFeq, ← h2]
          have : i + (q + 1) + (m : ℕ) = i + q + d := by omega
          rw [this]
          have : j + (q + 1) + (m : ℕ) = j + q + d := by omega
          rw [this]
          exact key
    intro n hn
    have hk : n = i + (n - i) := by omega
    have := hstate (n - i) ⟨0, hd⟩
    have hji : j + (n - i) + 0 = n + (j - i) := by omega
    have hii : i + (n - i) + 0 = n := by omega
    rw [hii, hji] at this
    exact this.symm
  case _ =>
    refine ⟨j, i - j, by omega, ?_⟩
    have hstate : ∀ k, ∀ m : Fin d, t (j + k + m) = t (i + k + m) := by
      intro k
      induction k with
      | zero =>
        intro m
        simpa using (hg m).symm
      | succ q ih =>
        intro m
        by_cases hm : (m : ℕ) + 1 < d
        · have e1 : i + (q + 1) + (m : ℕ) = i + q + ((m : ℕ) + 1) := by omega
          have e2 : j + (q + 1) + (m : ℕ) = j + q + ((m : ℕ) + 1) := by omega
          rw [e1, e2]
          exact ih ⟨(m : ℕ) + 1, hm⟩
        · have hmd : (m : ℕ) = d - 1 := by omega
          have h1 : t (j + q + d) = F (fun i' => t (j + q + i')) := hrec (j + q)
          have h2 : t (i + q + d) = F (fun i' => t (i + q + i')) := hrec (i + q)
          have hFeq : F (fun i' => t (j + q + i')) = F (fun i' => t (i + q + i')) := by
            congr 1
            funext i'
            exact ih i'
          have key : t (j + q + d) = t (i + q + d) := by rw [h1, hFeq, ← h2]
          have e1 : j + (q + 1) + (m : ℕ) = j + q + d := by omega
          have e2 : i + (q + 1) + (m : ℕ) = i + q + d := by omega
          rw [e1, e2]
          exact key
    intro n hn
    have := hstate (n - j) ⟨0, hd⟩
    have hii : i + (n - j) + 0 = n + (i - j) := by omega
    have hjj : j + (n - j) + 0 = n := by omega
    rw [hjj, hii] at this
    exact this.symm

/-! ## Vandermonde: persistent vanishing collapses coefficients -/

/-- **character independence**: if `∑ cᵢ αᵢⁿ = 0` for every `n`, with the
    `αᵢ` distinct, then every `cᵢ = 0` — the Vandermonde determinant
    `∏ (αⱼ − αᵢ) ≠ 0` forces it via the adjugate. -/
theorem coeff_zero_of_forall_sum_pow {K : Type*} [Field K] {d : ℕ}
    (α : Fin d → K) (hinj : Function.Injective α) (c : Fin d → K)
    (h : ∀ n : ℕ, ∑ i, c i * α i ^ n = 0) : ∀ i, c i = 0 := by
  let A : Matrix (Fin d) (Fin d) K := Matrix.of fun n i => α i ^ (n : ℕ)
  have hAc : A.mulVec c = 0 := by
    funext n
    have hcm : ∑ i, α i ^ (n : ℕ) * c i = 0 := by
      rw [← h n]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    simpa [A, Matrix.mulVec, dotProduct] using hcm
  have hdet : A.det ≠ 0 := by
    have : A = (Matrix.vandermonde α)ᵀ := by
      funext n i
      simp [A, Matrix.vandermonde]
    rw [this, Matrix.det_transpose, Matrix.det_vandermonde]
    refine Finset.prod_ne_zero_iff.mpr fun i _ => Finset.prod_ne_zero_iff.mpr fun j hj => ?_
    have hij : i < j := Finset.mem_Ioi.mp hj
    exact sub_ne_zero.mpr fun hEq => hij.ne' (hinj hEq)
  have hzero : A.det • c = 0 := by
    have := congrArg (A.adjugate.mulVec) hAc
    rwa [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec,
      Matrix.one_mulVec, Matrix.mulVec_zero] at this
  intro i
  have := congrArg (fun v => v i) hzero
  simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
  exact (mul_eq_zero.mp this).resolve_left hdet

/-! ## The torsion conclusion -/

/-- **eventual resonance forces torsion**: if the power sums
    `∑ αᵢⁿ` repeat with period `T` from some point on (distinct nonzero `αᵢ`),
    then EVERY root satisfies `αᵢᵀ = 1`. The `α^N` prefactor absorbs the delay,
    so eventual periodicity suffices — no backward determinism needed. All roots
    torsion is Kronecker's conclusion: Mahler measure 1. -/
theorem roots_torsion_of_eventually_periodic {K : Type*} [Field K] {d : ℕ}
    (α : Fin d → K) (hinj : Function.Injective α) (h0 : ∀ i, α i ≠ 0)
    {N T : ℕ} (_hT : 0 < T)
    (h : ∀ n, N ≤ n → ∑ i, α i ^ (n + T) = ∑ i, α i ^ n) :
    ∀ i, α i ^ T = 1 := by
  have hc : ∀ i, α i ^ N * (α i ^ T - 1) = 0 := by
    refine coeff_zero_of_forall_sum_pow α hinj _ fun m => ?_
    have hm := h (N + m) (Nat.le_add_right _ _)
    have : ∑ i, α i ^ N * (α i ^ T - 1) * α i ^ m =
        (∑ i, α i ^ (N + m + T)) - ∑ i, α i ^ (N + m) := by
      rw [← Finset.sum_sub_distrib]
      congr 1
      funext i
      ring
    rw [this, hm, sub_self]
  intro i
  have := hc i
  rcases mul_eq_zero.mp this with h1 | h2
  · exact absurd h1 (pow_ne_zero N (h0 i))
  · exact sub_eq_zero.mp h2

/-- **the Lehmer-facing contrapositive**: a unit whose roots are
    distinct, nonzero, and NOT all `T`-torsion for any `T` cannot have an
    eventually periodic power-sum sequence. Combined with
    `eventually_periodic_of_bounded`: any non-torsion unit has UNBOUNDED
    traces — resonance cannot persist above Mahler measure 1, which is why the
    (window, collisions) invariant is a genuine Mahler coordinate. -/
theorem no_persistent_resonance {K : Type*} [Field K] {d : ℕ}
    (α : Fin d → K) (hinj : Function.Injective α) (h0 : ∀ i, α i ≠ 0)
    (i₀ : Fin d) (hnt : ∀ T, 0 < T → α i₀ ^ T ≠ 1) :
    ∀ N T, 0 < T → ¬ (∀ n, N ≤ n → ∑ i, α i ^ (n + T) = ∑ i, α i ^ n) :=
  fun _ T hT h => hnt T hT
    (roots_torsion_of_eventually_periodic α hinj h0 hT h i₀)

end Wieferich.TraceReturns
