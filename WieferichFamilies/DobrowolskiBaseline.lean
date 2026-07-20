import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The Dobrowolski baseline as a general lemma

The divisibility at the base of Dobrowolski's lower bound for the Mahler
measure (Dobrowolski, Acta Arith. 34 (1979)): for a monic integer
polynomial `p` and a prime `q`,

    `q ^ deg p  ∣  Res(p, p ∘ X^q)`.

The mechanism is the Frobenius factorization `p(X^q) = p^q + q·h` over ℤ
(the freshman's dream mod `q`, lifted), which gives the exact integer
identity `Res(p, p∘X^q) = q^{deg p} · Res(p, h)`.

This is the general form of the "baseline `deg P`" of §2.3 of the paper:
the valuation `v_q(Res(P, P(x^q)))` is at least `deg P` unconditionally;
the per-prime anchors of `Dobrowolski.lean` witness the paper's finer
increment law (each depth-`e` order-lift failure adds
`(factor degree)·(e − 1)`), which refines this floor.

## Main results

* `frobenius_factor`: `p.comp (X^q) = p^q + C q · h` for some `h : ℤ[X]`.
* `dobResultant_eq_qpow_mul`: the exact factorization
  `Res(p, p∘X^q) = q^{deg p} · Res(p, h)`.
* `qpow_dvd_dobResultant`: the divisibility `q^{deg p} ∣ Res(p, p∘X^q)`.
-/

namespace Wieferich.DobrowolskiBaseline

open Polynomial

/-- The Dobrowolski resultant `Res(p, p ∘ X^q)`. -/
noncomputable def dobResultant (p : Polynomial ℤ) (q : ℕ) : ℤ :=
  resultant p (p.comp (X ^ q)) p.natDegree (p.comp (X ^ q)).natDegree

/-- The complex value of `Res(p, g)` for monic `p` (at degree bound
`n ≥ deg g`) is `∏_{α root of p} g(α)`. -/
lemma resultant_cast {p g : Polynomial ℤ} (hm : p.Monic) {n : ℕ}
    (hn : g.natDegree ≤ n) :
    ((resultant p g p.natDegree n : ℤ) : ℂ)
      = ((p.map (Int.castRingHom ℂ)).roots.map
          fun α => (g.map (Int.castRingHom ℂ)).eval α).prod := by
  set φ := Int.castRingHom ℂ with hφ
  set pc := p.map φ with hpc
  set gc := g.map φ with hgc
  have hmc : pc.Monic := hm.map _
  have hdeg : pc.natDegree = p.natDegree := hm.natDegree_map φ
  have hmap : ((resultant p g p.natDegree n : ℤ) : ℂ)
      = resultant pc gc p.natDegree n := by
    have hrmm := resultant_map_map (f := p) (g := g) (m := p.natDegree) (n := n) φ
    exact hrmm.symm
  rw [hmap]
  have hsplit : pc.Splits := IsAlgClosed.splits pc
  have hle : gc.natDegree ≤ n := Polynomial.natDegree_map_le.trans hn
  rw [← hdeg, resultant_eq_prod_eval pc gc n hle hsplit, hmc.leadingCoeff,
      one_pow, one_mul]

/-- **The Frobenius factorization**: for `q` prime,
`p.comp (X^q) = p^q + C q · h` for an integer polynomial `h` — every
coefficient of `p(X^q) − p^q` is divisible by `q`. -/
lemma frobenius_factor {p : Polynomial ℤ} {q : ℕ} (hq : q.Prime) :
    ∃ h : Polynomial ℤ, p.comp (X ^ q) = p ^ q + Polynomial.C (q : ℤ) * h := by
  haveI : Fact q.Prime := ⟨hq⟩
  set φ := Int.castRingHom (ZMod q) with hφ
  have hfrob : (frobenius (ZMod q) q) = RingHom.id (ZMod q) := by
    ext a; rw [frobenius_def, RingHom.id_apply, ZMod.pow_card]
  have hexpand : (p.map φ).comp (X ^ q) = (p.map φ) ^ q := by
    have hmfe := map_frobenius_expand (R := ZMod q) (p := q) (f := p.map φ)
    rw [hfrob, Polynomial.map_id] at hmfe
    rw [← Polynomial.expand_eq_comp_X_pow]; exact hmfe
  have hmapeq : (p.comp (X ^ q)).map φ = (p ^ q).map φ := by
    rw [Polynomial.map_comp, Polynomial.map_pow, Polynomial.map_X, hexpand, Polynomial.map_pow]
  have hsub0 : (p.comp (X ^ q) - p ^ q).map φ = 0 := by
    rw [Polynomial.map_sub, hmapeq, sub_self]
  have hdvd : ∀ n, (q : ℤ) ∣ (p.comp (X ^ q) - p ^ q).coeff n := by
    intro n
    have hcz : ((p.comp (X ^ q) - p ^ q).coeff n : ZMod q) = 0 := by
      have h2 : ((p.comp (X ^ q) - p ^ q).map φ).coeff n = 0 := by
        rw [hsub0, Polynomial.coeff_zero]
      rw [Polynomial.coeff_map] at h2
      simpa using h2
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mp hcz
  obtain ⟨h, hh⟩ := (Polynomial.C_dvd_iff_dvd_coeff (q : ℤ) _).mpr hdvd
  exact ⟨h, by linear_combination hh⟩

/-- **The exact factorization**: for `q` prime and monic `p`,
`Res(p, p∘X^q) = q^{deg p} · Res(p, h)` with `h` the Frobenius quotient.
Proved by evaluating at the roots: `p(α^q) = q·h(α)`. -/
theorem dobResultant_eq_qpow_mul {p : Polynomial ℤ} (hm : p.Monic) {q : ℕ}
    (hq : q.Prime) :
    ∃ h : Polynomial ℤ, dobResultant p q
      = (q : ℤ) ^ p.natDegree
        * resultant p h p.natDegree (p.comp (X ^ q)).natDegree := by
  obtain ⟨h, hfac⟩ := frobenius_factor (p := p) hq
  refine ⟨h, ?_⟩
  set N := (p.comp (X ^ q)).natDegree with hN
  set φ := Int.castRingHom ℂ with hφ
  set pc := p.map φ with hpc
  set hc := h.map φ with hhc
  have hmc : pc.Monic := hm.map _
  have hfacC : pc.comp (X ^ q) = pc ^ q + Polynomial.C (q : ℂ) * hc := by
    have h1 := congrArg (Polynomial.map φ) hfac
    simp only [Polynomial.map_comp, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_add,
      Polynomial.map_mul, Polynomial.map_C] at h1
    rw [show φ (q : ℤ) = (q : ℂ) from by simp [hφ]] at h1
    exact h1
  have hroot : ∀ α ∈ pc.roots, (pc.comp (X ^ q)).eval α = (q : ℂ) * hc.eval α := by
    intro α hα
    have h0 : pc.eval α = 0 := by
      have := Polynomial.isRoot_of_mem_roots hα
      rwa [Polynomial.IsRoot.def] at this
    rw [hfacC, Polynomial.eval_add, Polynomial.eval_pow, h0, Polynomial.eval_mul,
      Polynomial.eval_C, zero_pow hq.ne_zero, zero_add]
  have hhle : h.natDegree ≤ N := by
    by_cases hz : h = 0
    · simp [hz]
    · have : Polynomial.C (q : ℤ) * h = p.comp (X ^ q) - p ^ q := by
        linear_combination -hfac
      have hqne : ((q : ℤ)) ≠ 0 := by exact_mod_cast hq.ne_zero
      have hCh : (Polynomial.C (q : ℤ) * h).natDegree = h.natDegree := by
        rw [Polynomial.natDegree_C_mul hqne]
      calc h.natDegree = (Polynomial.C (q : ℤ) * h).natDegree := hCh.symm
        _ = (p.comp (X ^ q) - p ^ q).natDegree := by rw [this]
        _ ≤ max (p.comp (X ^ q)).natDegree (p ^ q).natDegree :=
            Polynomial.natDegree_sub_le _ _
        _ ≤ N := by
            apply max_le le_rfl
            rw [Polynomial.natDegree_pow]
            by_cases hp0 : p.natDegree = 0
            · simp [hp0]
            · rw [Polynomial.natDegree_comp]
              simp [Nat.mul_comm]
  have hcast : ((dobResultant p q : ℤ) : ℂ)
      = ((((q : ℤ) ^ p.natDegree * resultant p h p.natDegree N : ℤ)) : ℂ) := by
    rw [dobResultant, resultant_cast hm le_rfl]
    have hmapcomp : (p.comp (X ^ q)).map φ = pc.comp (X ^ q) := by
      rw [Polynomial.map_comp, Polynomial.map_pow, Polynomial.map_X]
    rw [hmapcomp, Multiset.map_congr rfl hroot, Multiset.prod_map_mul,
      Multiset.map_const', Multiset.prod_replicate]
    have hsplit : pc.Splits := IsAlgClosed.splits pc
    rw [← hsplit.natDegree_eq_card_roots, hm.natDegree_map]
    rw [show ((pc.roots.map fun α => hc.eval α).prod)
        = ((resultant p h p.natDegree N : ℤ) : ℂ) from (resultant_cast hm hhle).symm]
    push_cast; ring
  exact_mod_cast hcast

/-- **The Dobrowolski baseline**: for `q` prime and monic `p`,
`q^{deg p} ∣ Res(p, p∘X^q)`. -/
theorem qpow_dvd_dobResultant {p : Polynomial ℤ} (hm : p.Monic) {q : ℕ}
    (hq : q.Prime) :
    (q : ℤ) ^ p.natDegree ∣ dobResultant p q := by
  obtain ⟨h, hkey⟩ := dobResultant_eq_qpow_mul hm hq
  exact ⟨_, hkey⟩

end Wieferich.DobrowolskiBaseline
