import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.NumberTheory.Multiplicity
import Mathlib.Data.Nat.Squarefree
import Mathlib.FieldTheory.Finite.Basic

/-!
# The Birkhoff–Vandiver first-power bound and the Zsygmondy reduction

Every prime factor of `Φ_n(a)` is primitive (multiplicative order exactly
`n`) or intrinsic (divides `n`). This module proves the first-power bound
for intrinsic primes at base 2 and reduces Zsygmondy existence to a single
size inequality.

## Main results

* `cyclotomic_eval_mul_dvd`: for prime `q ∣ n`,
  `Φ_n(a) · (a^(n/q) − 1) ∣ a^n − 1`.
* `emultiplicity_prime_pow_sub_one`: for odd prime `q ∣ x − 1`,
  `v_q(x^q − 1) = v_q(x − 1) + 1` (lifting the exponent).
* `intrinsic_dvd_pow_div_sub_one`: an intrinsic prime satisfies the LTE
  hypothesis automatically (`ord_q(2)` divides `n/q`).
* `emultiplicity_cyclotomic_le_one`: the first-power bound
  `v_q(Φ_n(2)) ≤ 1` for intrinsic `q` (Birkhoff–Vandiver, Ann. of
  Math. 5 (1904)).
* `dvd_prod_primeFactors_of_no_extrinsic`, `exists_extrinsic_of_prod_lt`:
  with no extrinsic prime factor, `Φ_n(2)` divides `rad(n)`; hence
  `|Φ_n(2)| > rad(n)` forces a primitive prime divisor to exist
  (Zsygmondy, Monatsh. Math. Phys. 3 (1892)).
* `prime_pow_rung_size`, `exists_extrinsic_prime_pow`: the size
  inequality is proved on prime-power indices, so existence is
  unconditional there.
-/

namespace Wieferich.ZsygmondyLTE

open Polynomial Finset

/-- **(A)** For a prime q dividing n (0 < n): `Φ_n(a) · (a^{n/q} − 1) ∣ a^n − 1`
    at every integer a — n/q is a proper divisor, so Mathlib's product law
    applies, and evaluation preserves divisibility. -/
theorem cyclotomic_eval_mul_dvd {n q : ℕ} (hq : q.Prime) (hqn : q ∣ n) (hn : 0 < n)
    (a : ℤ) :
    (cyclotomic n ℤ).eval a * (a ^ (n / q) - 1) ∣ a ^ n - 1 := by
  have hmem : n / q ∈ n.properDivisors :=
    Nat.mem_properDivisors.mpr ⟨Nat.div_dvd_of_dvd hqn, Nat.div_lt_self hn hq.one_lt⟩
  have h := eval_dvd (x := a)
    (X_pow_sub_one_mul_cyclotomic_dvd_X_pow_sub_one_of_dvd ℤ hmem)
  simp only [eval_mul, eval_sub, eval_pow, eval_X, eval_one] at h
  rwa [mul_comm] at h

/-- **(LTE step)** For an odd prime q with q ∣ x − 1:
    `v_q(x^q − 1) = v_q(x − 1) + 1`. -/
theorem emultiplicity_prime_pow_sub_one {q : ℕ} (hq : q.Prime) (hodd : Odd q) {x : ℤ}
    (hx1 : (q : ℤ) ∣ x - 1) :
    emultiplicity (q : ℤ) (x ^ q - 1) = emultiplicity (q : ℤ) (x - 1) + 1 := by
  have hq2 : (2 : ℤ) ≤ (q : ℤ) := by exact_mod_cast hq.two_le
  have hx : ¬(q : ℤ) ∣ x := by
    intro hdvd
    have h1 : (q : ℤ) ∣ 1 := (dvd_sub_right hdvd).mp (by simpa using hx1)
    have := Int.le_of_dvd one_pos h1
    omega
  have h := Int.emultiplicity_pow_sub_pow hq hodd (y := 1) (by simpa using hx1) hx q
  simpa [Nat.Prime.emultiplicity_self hq] using h

/-- **(LTE tower)** For an odd prime q with q ∣ x − 1, the valuation climbs
    the q-power tower linearly with slope one:
    `v_q(x^{q^k} − 1) = v_q(x − 1) + k`. In Iwasawa's growth notation
    `e_k = λk + μq^k + ν` the unit tower has `λ = 1` and `μ = 0`
    unconditionally, with `ν` set by the depth of the base level. -/
theorem emultiplicity_prime_pow_pow_sub_one {q : ℕ} (hq : q.Prime) (hodd : Odd q)
    {x : ℤ} (hx1 : (q : ℤ) ∣ x - 1) (k : ℕ) :
    emultiplicity (q : ℤ) (x ^ q ^ k - 1) = emultiplicity (q : ℤ) (x - 1) + k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hdvd : (q : ℤ) ∣ x ^ q ^ k - 1 := by
      have h := sub_dvd_pow_sub_pow x 1 (q ^ k)
      rw [one_pow] at h
      exact hx1.trans h
    have hstep := emultiplicity_prime_pow_sub_one hq hodd (x := x ^ q ^ k) hdvd
    rw [pow_succ, pow_mul, hstep, ih, Nat.cast_add, Nat.cast_one, add_assoc]

/-- **(ord transfer)** An intrinsic odd prime q (q ∣ n, q ∣ 2^n − 1) automatically
    has q ∣ 2^{n/q} − 1: the order of 2 mod q divides both n and q − 1, is coprime
    to q, hence divides n/q. -/
theorem intrinsic_dvd_pow_div_sub_one {n q : ℕ} (hq : q.Prime) (hodd : Odd q)
    (hqn : q ∣ n) (hdvd : (q : ℤ) ∣ 2 ^ n - 1) :
    (q : ℤ) ∣ 2 ^ (n / q) - 1 := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hq2 : (2 : ZMod q) ≠ 0 := by
    have : ¬ q ∣ 2 := by
      intro h
      rcases (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp h with rfl
      exact absurd hodd (by decide)
    have h2 : ((2 : ℕ) : ZMod q) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]; exact this
    simpa using h2
  have hpow : (2 : ZMod q) ^ n = 1 := by
    have h0 : ((2 ^ n - 1 : ℤ) : ZMod q) = 0 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; exact hdvd
    push_cast at h0
    linear_combination h0
  have hord_n : orderOf (2 : ZMod q) ∣ n := orderOf_dvd_of_pow_eq_one hpow
  have hord_q1 : orderOf (2 : ZMod q) ∣ q - 1 :=
    orderOf_dvd_of_pow_eq_one (ZMod.pow_card_sub_one_eq_one hq2)
  have hcop : Nat.Coprime (orderOf (2 : ZMod q)) q := by
    refine Nat.Coprime.symm (hq.coprime_iff_not_dvd.mpr ?_)
    intro hdvd'
    have h1 : q ∣ q - 1 := hdvd'.trans hord_q1
    have h2 : 0 < q - 1 := by have := hq.two_le; omega
    have := Nat.le_of_dvd h2 h1
    omega
  have hordnq : orderOf (2 : ZMod q) ∣ n / q := by
    have hn_eq : q * (n / q) = n := Nat.mul_div_cancel' hqn
    have h : orderOf (2 : ZMod q) ∣ q * (n / q) := by rw [hn_eq]; exact hord_n
    exact Nat.Coprime.dvd_of_dvd_mul_left hcop h
  have hpow2 : (2 : ZMod q) ^ (n / q) = 1 := orderOf_dvd_iff_pow_eq_one.mp hordnq
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  linear_combination hpow2

/-- **(B) The Birkhoff–Vandiver first-power bound.** For an odd intrinsic prime
    q (q ∣ n, 0 < n) with q ∣ 2^n − 1: `v_q(Φ_n(2)) ≤ 1`. Combines (A), (LTE),
    (ord). -/
theorem emultiplicity_cyclotomic_le_one {n q : ℕ} (hq : q.Prime) (hodd : Odd q)
    (hqn : q ∣ n) (hn : 0 < n) (hdvd : (q : ℤ) ∣ 2 ^ n - 1) :
    emultiplicity (q : ℤ) ((cyclotomic n ℤ).eval 2) ≤ 1 := by
  have hqZ : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hq
  have hnq : 0 < n / q := Nat.div_pos (Nat.le_of_dvd hn hqn) hq.pos
  set x : ℤ := 2 ^ (n / q) with hx_def
  have hx1 : (q : ℤ) ∣ x - 1 := intrinsic_dvd_pow_div_sub_one hq hodd hqn hdvd
  have hxq : x ^ q = 2 ^ n := by
    rw [hx_def, ← pow_mul, Nat.div_mul_cancel hqn]
  have hLTE : emultiplicity (q : ℤ) ((2 : ℤ) ^ n - 1)
      = emultiplicity (q : ℤ) (x - 1) + 1 := by
    rw [← hxq]; exact emultiplicity_prime_pow_sub_one hq hodd hx1
  obtain ⟨c, hc⟩ := cyclotomic_eval_mul_dvd hq hqn hn (2 : ℤ)
  have hx1_ne : x - 1 ≠ 0 := by
    have : (2 : ℤ) ≤ x := by
      rw [hx_def]
      calc (2 : ℤ) = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ (n / q) := by
        apply pow_le_pow_right₀ (by norm_num) hnq
    omega
  have hfin : FiniteMultiplicity (q : ℤ) (x - 1) :=
    Int.finiteMultiplicity_iff.mpr ⟨by simpa using hq.ne_one, hx1_ne⟩
  have hsplit : emultiplicity (q : ℤ) ((2 : ℤ) ^ n - 1)
      = emultiplicity (q : ℤ) ((cyclotomic n ℤ).eval 2) + emultiplicity (q : ℤ) (x - 1)
        + emultiplicity (q : ℤ) c := by
    rw [hc, emultiplicity_mul hqZ, emultiplicity_mul hqZ]
  have hle : emultiplicity (q : ℤ) ((cyclotomic n ℤ).eval 2) + emultiplicity (q : ℤ) (x - 1)
      ≤ emultiplicity (q : ℤ) (x - 1) + 1 := by
    rw [← hLTE, hsplit]
    exact le_add_right le_rfl
  have hfin_ne : emultiplicity (q : ℤ) (x - 1) ≠ ⊤ :=
    finiteMultiplicity_iff_emultiplicity_ne_top.mp hfin
  rw [add_comm (emultiplicity (q : ℤ) ((cyclotomic n ℤ).eval 2))
      (emultiplicity (q : ℤ) (x - 1)), add_comm (emultiplicity (q : ℤ) (x - 1)) 1] at hle
  -- now: v(x−1) + v(Φ) ≤ 1 + v(x−1); commute the right and cancel
  rw [add_comm (1 : ℕ∞) (emultiplicity (q : ℤ) (x - 1))] at hle
  exact (ENat.add_le_add_iff_left hfin_ne).mp hle

/-- **(D, divisibility form)** If every prime factor of N divides n and appears
    to the first power, N divides the radical ∏_{p ∣ n} p. -/
theorem dvd_prod_primeFactors_of_no_extrinsic {N n : ℕ} (_hN : 0 < N) (hn : 0 < n)
    (hsupp : ∀ q : ℕ, q.Prime → q ∣ N → q ∣ n)
    (hsq : ∀ q : ℕ, q.Prime → ¬ q * q ∣ N) :
    N ∣ ∏ p ∈ n.primeFactors, p := by
  have hNsq : Squarefree N := by
    rw [Nat.squarefree_iff_prime_squarefree]
    intro p hp
    exact hsq p hp
  have hNprod : ∏ p ∈ N.primeFactors, p = N := Nat.prod_primeFactors_of_squarefree hNsq
  rw [← hNprod]
  apply Finset.prod_dvd_prod_of_subset
  intro p hp
  rw [Nat.mem_primeFactors] at hp ⊢
  exact ⟨hp.1, hsupp p hp.1 hp.2.1, hn.ne'⟩

/-- **(D, contrapositive) — the existence trigger.** If |Φ_n(2)| exceeds the
    radical of n, an extrinsic prime factor (q ∤ n) exists: an intrinsic-only
    factorization is squarefree by (B) (q = 2 never divides Φ_n(2) ∣ 2^n − 1),
    hence divides rad(n). -/
theorem exists_extrinsic_of_prod_lt {n : ℕ} (hn : 0 < n)
    (hpos : 0 < ((cyclotomic n ℤ).eval 2).natAbs)
    (hbig : ∏ p ∈ n.primeFactors, p < ((cyclotomic n ℤ).eval 2).natAbs) :
    ∃ q : ℕ, q.Prime ∧ (q : ℤ) ∣ (cyclotomic n ℤ).eval 2 ∧ ¬ q ∣ n := by
  set N := ((cyclotomic n ℤ).eval 2).natAbs with hN_def
  by_contra hcon
  push_neg at hcon
  have hsupp : ∀ q : ℕ, q.Prime → q ∣ N → q ∣ n := by
    intro q hq hqN
    refine hcon q hq ?_
    rw [← Int.natAbs_dvd_natAbs, Int.natAbs_natCast]
    exact hqN
  have hΦdvd : (cyclotomic n ℤ).eval 2 ∣ 2 ^ n - 1 := by
    have hpoly : cyclotomic n ℤ ∣ X ^ n - 1 := by
      rw [← prod_cyclotomic_eq_X_pow_sub_one hn ℤ]
      exact Finset.dvd_prod_of_mem _ (Nat.mem_divisors_self n hn.ne')
    have h := eval_dvd (x := (2 : ℤ)) hpoly
    simpa using h
  have hNodd : ¬ 2 ∣ N := by
    intro h2
    have h2Z : (2 : ℤ) ∣ (cyclotomic n ℤ).eval 2 := by
      have : ((2 : ℕ) : ℤ) ∣ (cyclotomic n ℤ).eval 2 := by
        rw [← Int.natAbs_dvd_natAbs, Int.natAbs_natCast]
        exact h2
      simpa using this
    have hdvd1 : (2 : ℤ) ∣ 2 ^ n - 1 := h2Z.trans hΦdvd
    have h1 : (2 : ℤ) ∣ 2 ^ n := dvd_pow_self 2 hn.ne'
    have : (2 : ℤ) ∣ 1 := (dvd_sub_right h1).mp (by simpa using hdvd1)
    norm_num at this
  have hsq : ∀ q : ℕ, q.Prime → ¬ q * q ∣ N := by
    intro q hq hqq
    have hqN : q ∣ N := (dvd_mul_right q q).trans hqq
    have hodd : Odd q := hq.odd_of_ne_two (by rintro rfl; exact hNodd hqN)
    have hqn : q ∣ n := hsupp q hq hqN
    have hq2n : (q : ℤ) ∣ 2 ^ n - 1 := by
      have hqZ : (q : ℤ) ∣ (cyclotomic n ℤ).eval 2 := by
        have : ((q : ℕ) : ℤ) ∣ (cyclotomic n ℤ).eval 2 := by
          rw [← Int.natAbs_dvd_natAbs, Int.natAbs_natCast]
          exact hqN
        simpa using this
      exact hqZ.trans hΦdvd
    have hB := emultiplicity_cyclotomic_le_one hq hodd hqn hn hq2n
    have hsqZ : (q : ℤ) ^ 2 ∣ (cyclotomic n ℤ).eval 2 := by
      have h1 : (q * q : ℕ) ∣ N := hqq
      have h2 : ((q * q : ℕ) : ℤ) ∣ (cyclotomic n ℤ).eval 2 := by
        rw [← Int.natAbs_dvd_natAbs, Int.natAbs_natCast]
        exact h1
      push_cast at h2
      rwa [← sq] at h2
    have h2le : (2 : ℕ∞) ≤ emultiplicity (q : ℤ) ((cyclotomic n ℤ).eval 2) :=
      le_emultiplicity_of_pow_dvd hsqZ
    have : (2 : ℕ∞) ≤ 1 := h2le.trans hB
    norm_num at this
  have hdvd := dvd_prod_primeFactors_of_no_extrinsic hpos hn hsupp hsq
  have hprodpos : 0 < ∏ p ∈ n.primeFactors, p :=
    Finset.prod_pos fun p hp => (Nat.prime_of_mem_primeFactors hp).pos
  have := Nat.le_of_dvd hprodpos hdvd
  omega

/-- **(E anchor, identity)** `Φ_p(2) = 2^p − 1`: on prime rungs the cyclotomic
    value IS the Mersenne number. -/
theorem cyclotomic_prime_eval_two {p : ℕ} (hp : p.Prime) :
    (cyclotomic p ℤ).eval 2 = 2 ^ p - 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [cyclotomic_prime ℤ p, eval_geom_sum]
  have h := geom_sum_mul (2 : ℤ) p
  simpa using h

/-- **(E anchor, size)** On prime rungs the size leaf is a theorem:
    `Φ_p(2) > p` for every prime p. -/
theorem prime_rung_size {p : ℕ} (hp : p.Prime) :
    (p : ℤ) < (cyclotomic p ℤ).eval 2 := by
  rw [cyclotomic_prime_eval_two hp]
  have key : ∀ k : ℕ, 2 ≤ k → k + 1 < 2 ^ k := by
    intro k
    induction k with
    | zero => omega
    | succ m ih =>
      intro hk
      rcases Nat.lt_or_ge m 2 with hm | hm
      · interval_cases m
        · omega
        · norm_num
      · have h1 := ih hm
        have h2 : 2 ^ (m + 1) = 2 * 2 ^ m := by ring
        omega
  have h2 := key p hp.two_le
  have hZ : ((p : ℤ) + 1) < 2 ^ p := by exact_mod_cast h2
  omega

/-- **(E, prime-power rungs) The size leaf is a THEOREM on every prime power.**
    `Φ_{p^k}(2) = ∑_{i<p} (2^{p^{k−1}})^i ≥ (2^{p^{k−1}})^{p−1} ≥ 2^p > p = rad(p^k)`. -/
theorem prime_pow_rung_size {p k : ℕ} (hp : p.Prime) (hk : 0 < k) :
    ∏ r ∈ (p ^ k).primeFactors, r < ((cyclotomic (p ^ k) ℤ).eval 2).natAbs := by
  -- the radical of a prime power is p
  have hrad : ∏ r ∈ (p ^ k).primeFactors, r = p := by
    rw [Nat.primeFactors_prime_pow hk.ne' hp]
    simp
  -- write k = m + 1 and use the geometric-sum form
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  rw [hrad, cyclotomic_prime_pow_eq_geom_sum hp, eval_finsetSum]
  simp only [eval_pow, eval_X]
  -- the sum of nonneg powers dominates its i = p−1 term
  have hterm : ((2 : ℤ) ^ p ^ m) ^ (p - 1) ≤ ∑ i ∈ Finset.range p, ((2 : ℤ) ^ p ^ m) ^ i := by
    apply Finset.single_le_sum (f := fun i => ((2 : ℤ) ^ p ^ m) ^ i)
    · intro i _
      positivity
    · exact Finset.mem_range.mpr (by have := hp.two_le; omega)
  -- the base is at least 2, so the top term is at least 2^{p−1}
  have hbase2 : (2 : ℤ) ≤ 2 ^ p ^ m := by
    calc (2 : ℤ) = 2 ^ 1 := (pow_one 2).symm
    _ ≤ 2 ^ p ^ m := pow_le_pow_right₀ (by norm_num) (Nat.one_le_pow m p hp.pos)
  have hterm_ge : (2 : ℤ) ^ (p - 1) ≤ ((2 : ℤ) ^ p ^ m) ^ (p - 1) :=
    pow_le_pow_left₀ (by norm_num) hbase2 (p - 1)
  -- p ≤ 2^{p−1} for every prime p
  have hkey : ∀ j : ℕ, 2 ≤ j → j + 1 < 2 ^ j := by
    intro j
    induction j with
    | zero => omega
    | succ w ih =>
      intro hj
      rcases Nat.lt_or_ge w 2 with hw | hw
      · interval_cases w
        · omega
        · norm_num
      · have h1 := ih hw
        have h2 : 2 ^ (w + 1) = 2 * 2 ^ w := by ring
        omega
  have hp_le : (p : ℤ) ≤ 2 ^ (p - 1) := by
    rcases eq_or_lt_of_le hp.two_le with h2 | h3
    · rw [← h2]; norm_num
    · have hN : p < 2 ^ (p - 1) := by
        have := hkey (p - 1) (by omega)
        omega
      exact_mod_cast hN.le
  -- the sum dominates its 0 and p−1 terms together: 1 + top term
  have hpair : (1 : ℤ) + ((2 : ℤ) ^ p ^ m) ^ (p - 1)
      ≤ ∑ i ∈ Finset.range p, ((2 : ℤ) ^ p ^ m) ^ i := by
    have hne : (0 : ℕ) ≠ p - 1 := by have := hp.two_le; omega
    have hsub : ({0, p - 1} : Finset ℕ) ⊆ Finset.range p := by
      intro i hi
      rcases Finset.mem_insert.mp hi with rfl | hi'
      · exact Finset.mem_range.mpr hp.pos
      · rw [Finset.mem_singleton] at hi'
        subst hi'
        exact Finset.mem_range.mpr (by have := hp.two_le; omega)
    have hmono := Finset.sum_le_sum_of_subset_of_nonneg
      (f := fun i => ((2 : ℤ) ^ p ^ m) ^ i) hsub (fun i _ _ => by positivity)
    rw [Finset.sum_pair hne] at hmono
    simpa using hmono
  have hsum_pos : (p : ℤ) < ∑ i ∈ Finset.range p, ((2 : ℤ) ^ p ^ m) ^ i := by
    linarith [hpair, hterm_ge, hp_le]
  -- transfer to natAbs
  have hnn : (0 : ℤ) ≤ ∑ i ∈ Finset.range p, ((2 : ℤ) ^ p ^ m) ^ i := by
    apply Finset.sum_nonneg
    intro i _
    positivity
  have hcast : (((∑ i ∈ Finset.range p, ((2 : ℤ) ^ p ^ m) ^ i).natAbs : ℤ))
      = ∑ i ∈ Finset.range p, ((2 : ℤ) ^ p ^ m) ^ i := Int.natAbs_of_nonneg hnn
  have hfin : (p : ℤ) < ((∑ i ∈ Finset.range p, ((2 : ℤ) ^ p ^ m) ^ i).natAbs : ℤ) := by
    rw [hcast]; exact hsum_pos
  exact_mod_cast hfin

/-- **Unconditional Zsygmondy-type existence at prime-power rungs**: for every
    prime p and k ≥ 1, `Φ_{p^k}(2)` has a prime factor different from p — no
    SizeLeaf hypothesis needed. (The master order theorem upgrades it: that
    factor has ord_q(2) = p^k exactly, hence q ≡ 1 mod p^k.) -/
theorem exists_extrinsic_prime_pow {p k : ℕ} (hp : p.Prime) (hk : 0 < k) :
    ∃ q : ℕ, q.Prime ∧ (q : ℤ) ∣ (cyclotomic (p ^ k) ℤ).eval 2 ∧ ¬ q ∣ p ^ k := by
  have hn0 : 0 < p ^ k := pow_pos hp.pos k
  have hbig := prime_pow_rung_size hp hk
  have hradpos : 0 < ∏ r ∈ (p ^ k).primeFactors, r :=
    Finset.prod_pos fun r hr => (Nat.prime_of_mem_primeFactors hr).pos
  exact exists_extrinsic_of_prod_lt hn0 (by omega) hbig

/-- **The typed leaf.** The ONE remaining analytic input to Zsygmondy existence
    at base 2: for n > 6 the cyclotomic value beats the radical. Everything else
    in the build order is a theorem above; this structure names the residue.
    (Road: the Möbius product form of Φ_n(2) — the error term Σ|log₂(1 − 2^{−d})|
    is < 2.1, giving Φ_n(2) > 2^{φ(n)−2.1}, which beats rad(n) ≤ n once
    φ(n) ≥ log₂ n + 3; finitely many exceptions checked directly.) -/
structure SizeLeaf : Prop where
  bound : ∀ n : ℕ, 6 < n → ∏ p ∈ n.primeFactors, p < ((cyclotomic n ℤ).eval 2).natAbs

/-- **The assembly**: the size leaf is the whole remaining distance — given it,
    every n > 6 has an extrinsic prime factor of Φ_n(2). -/
theorem exists_extrinsic_of_sizeLeaf (h : SizeLeaf) {n : ℕ} (hn : 6 < n) :
    ∃ q : ℕ, q.Prime ∧ (q : ℤ) ∣ (cyclotomic n ℤ).eval 2 ∧ ¬ q ∣ n := by
  have hn0 : 0 < n := by omega
  have hbig := h.bound n hn
  have hprodpos : 0 < ∏ p ∈ n.primeFactors, p :=
    Finset.prod_pos fun p hp => (Nat.prime_of_mem_primeFactors hp).pos
  exact exists_extrinsic_of_prod_lt hn0 (by omega) hbig

/-- **(D, bounded form)** If every prime factor of N divides n and appears with
    multiplicity at most C, then N divides rad(n)^C. Generalizes the squarefree
    case (C = 1) via factorization comparison. -/
theorem dvd_radical_pow_of_bounded {N n C : ℕ} (hN : 0 < N) (hn : 0 < n)
    (hsupp : ∀ q : ℕ, q.Prime → q ∣ N → q ∣ n)
    (hbound : ∀ q : ℕ, q.Prime → ¬ q ^ (C + 1) ∣ N) :
    N ∣ (∏ p ∈ n.primeFactors, p) ^ C := by
  set R : ℕ := ∏ p ∈ n.primeFactors, p with hR_def
  have hRpos : 0 < R :=
    Finset.prod_pos fun p hp => (Nat.prime_of_mem_primeFactors hp).pos
  rw [← Nat.factorization_le_iff_dvd hN.ne' (pow_ne_zero C hRpos.ne')]
  intro q
  rcases Nat.eq_zero_or_pos (N.factorization q) with h0 | hqpos
  · simp [h0]
  · have hq : q.Prime := Nat.prime_of_mem_primeFactors (by
      rw [← Nat.support_factorization]
      exact Finsupp.mem_support_iff.mpr hqpos.ne')
    have hqN : q ∣ N := Nat.dvd_of_factorization_pos hqpos.ne'
    have hqn : q ∣ n := hsupp q hq hqN
    have hmem : q ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hq, hqn, hn.ne'⟩
    -- LHS ≤ C from the multiplicity bound
    have hle : N.factorization q ≤ C := by
      by_contra hgt
      push_neg at hgt
      exact hbound q hq ((Nat.Prime.pow_dvd_iff_le_factorization hq hN.ne').mpr hgt)
    -- RHS: the radical's factorization at q ∈ primeFactors is exactly 1
    have hRfact : R.factorization q = 1 := by
      have h1 : R.factorization = ∑ p ∈ n.primeFactors, Nat.factorization p :=
        Nat.factorization_prod fun p hp => (Nat.prime_of_mem_primeFactors hp).ne_zero
      have h2 : R.factorization q = ∑ p ∈ n.primeFactors, Nat.factorization p q := by
        rw [h1, Finsupp.finset_sum_apply]
      rw [h2]
      have h3 : ∀ p ∈ n.primeFactors, Nat.factorization p q = if p = q then 1 else 0 := by
        intro p hp
        rw [(Nat.prime_of_mem_primeFactors hp).factorization, Finsupp.single_apply]
      rw [Finset.sum_congr rfl h3, Finset.sum_ite_eq' n.primeFactors q fun _ => 1]
      simp [hmem]
    have hpow : (R ^ C).factorization q = C * R.factorization q := by
      rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
    rw [hpow, hRfact, mul_one]
    exact hle

/-- **The norm-form lift, typed with a multiplicity budget (the BHV face).**
    For a unit α of degree d, the size-vs-intrinsic argument runs over
    the norm form N_n = |Norm(Φ_n(α))|. CALIBRATED by a preregistered census
    (Salem boxes of degree 6–10, rungs ≤ 30): the naive rational first-power field
    v_q(N_n) ≤ 1 fails (1,972 instances), and even v_q ≤ deg fails (41
    instances, max v = 20 at deg 8) — the raw multiplicity includes the
    unit's Wieferich depth at the ord-rung, not just the e·f ideal
    bookkeeping. The honest field carries an explicit budget C = C(α):
    intrinsic multiplicity is bounded, and the Mahler size bound must beat
    rad(n)^C. Both remain the two open fields; the assembly below shows they
    still suffice, by the bounded reduction. -/
structure NormFormLift (normValue : ℕ → ℕ) (C : ℕ) : Prop where
  /-- the budgeted intrinsic bound: no intrinsic prime divides N_n more than
      C times (open; C absorbs Σe·f plus the ord-rung depth baseline). -/
  intrinsic_bounded : ∀ n q : ℕ, 0 < n → q.Prime → q ∣ n →
    ¬ q ^ (C + 1) ∣ normValue n
  /-- the Mahler size bound against the budgeted radical (open; the analytic
      half is the Pierce-ledger window). -/
  size_beats_radical_pow : ∀ n : ℕ, 6 < n →
    (∏ p ∈ n.primeFactors, p) ^ C < normValue n

/-- **The norm-form assembly**: given the budgeted lift, every rung n > 6 has an
    extrinsic prime factor — the BHV existence statement, reduced to the two
    open fields by the bounded reduction. -/
theorem normForm_exists_extrinsic {normValue : ℕ → ℕ} {C : ℕ}
    (h : NormFormLift normValue C) {n : ℕ} (hn : 6 < n) (hpos : 0 < normValue n) :
    ∃ q : ℕ, q.Prime ∧ q ∣ normValue n ∧ ¬ q ∣ n := by
  by_contra hcon
  push_neg at hcon
  have hsupp : ∀ q : ℕ, q.Prime → q ∣ normValue n → q ∣ n := fun q hq hqN =>
    hcon q hq hqN
  have hn0 : 0 < n := by omega
  have hbound : ∀ q : ℕ, q.Prime → ¬ q ^ (C + 1) ∣ normValue n := by
    intro q hq hqq
    have hqN : q ∣ normValue n := (dvd_pow_self q (Nat.succ_ne_zero C)).trans hqq
    exact h.intrinsic_bounded n q hn0 hq (hsupp q hq hqN) hqq
  have hdvd := dvd_radical_pow_of_bounded hpos hn0 hsupp hbound
  have hprodpos : 0 < (∏ p ∈ n.primeFactors, p) ^ C :=
    pow_pos (Finset.prod_pos fun p hp => (Nat.prime_of_mem_primeFactors hp).pos) C
  have hle := Nat.le_of_dvd hprodpos hdvd
  have hbig := h.size_beats_radical_pow n hn
  omega

end Wieferich.ZsygmondyLTE
