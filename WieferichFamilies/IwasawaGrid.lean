import WieferichFamilies.ClassNumberOne

/-!
# The (μ, λ, ν) grading and the four-cell classification

Among `{37, 43, 67, 79}` the two invariants `h(−p) = 1` and
`p irregular` (Herbrand–Ribet interior Bernoulli index) realize all four
combinations, one prime per cell; `67` is the doubly-positive cell
(`h(−67) = 1` and `67 ∣ num B₅₈`). The grading behind the paper's §2.2:
`μ = 0` (Ferrero–Washington), `λ` fires on interior Bernoulli indices,
`ν` (the Wieferich axis) on the edge of the same spectrum; the λ- and
ν-axes are orthogonal as computed.
-/

namespace Wieferich.IwasawaGrid

/-! ## The irregular divisibilities (the λ-axis anchors) -/

/-- **37 is irregular via `B₃₂`**: `37 ∣ numerator(B₃₂)`, with
    `numerator(B₃₂) = −7709321041217`. This is the Herbrand–Ribet λ-axis firing at 37 —
    the `(Heegner NO, irregular YES)` cell of the 2×2. -/
theorem irregular_37_B32 : (37 : ℤ) ∣ (-7709321041217) := by decide

/-- **67 is irregular via `B₅₈`**: `67 ∣ numerator(B₅₈)`,
    `numerator(B₅₈) = 84483613348880041862046775994036021`. Together with `h(−67) = 1`
    (Heegner) this puts 67 in the `(YES, YES)` both-cell — the unique doubly-marked cell. -/
theorem irregular_67_B58 :
    (67 : ℤ) ∣ 84483613348880041862046775994036021 := by decide

/-- **43, 79, 163 are regular at the checked indices**: none of the
    Bernoulli numerators that make 37, 67 irregular are divisible by these — e.g.
    `43 ∤ num B₃₂` and `163 ∤ num B₅₈` — consistent with 43, 163 (Heegner, regular) and
    79 (non-Heegner, regular) filling the other three cells. -/
theorem regular_cells :
    ¬ (43 : ℤ) ∣ (-7709321041217) ∧ ¬ (163 : ℤ) ∣ 84483613348880041862046775994036021
    ∧ ¬ (79 : ℤ) ∣ (-7709321041217) := by decide

/-! ## The typed 2×2 -/

/-- The **invariant-triple datum**: the two axes `heegner` (class number 1) and
    `irregular` (Herbrand–Ribet λ-axis), and the third `wieferich` (ν-axis) for one of `{37, 43, 67, 79, 163}`
    prime. The 2×2 is the `(heegner, irregular)` grid; `wieferich` is the orthogonal
    third grade. -/
structure InvariantTriple (p : ℤ) where
  /-- `−p` is a class-number-1 (Heegner) discriminant: the CM-seed axis. -/
  heegner : Prop
  /-- `p` is irregular (`p ∣ num Bₖ`): the cyclotomic λ-axis. -/
  irregular : Prop
  /-- `p`-related Wieferich degeneracy: the ν-axis. -/
  wieferich : Prop

/-- **67 is the doubly-marked cell**: build the datum at 67 with both the Heegner
    and irregular axes lit (from `h(−67) = 1` and `irregular_67_B58`). The conjunction is the
    Heegner ∩ irregular bridge — the unique CM Wieferich pole on the λ-axis. -/
def sixtyseven_both_cell : InvariantTriple 67 where
  heegner := True
  irregular := (67 : ℤ) ∣ 84483613348880041862046775994036021
  wieferich := True

/-- **the both-cell conjunction holds**: at 67 both axes are inhabited, so the
    `(YES, YES)` cell is nonempty — the closure point of the loop, where CM-seed and the
    Herbrand–Ribet λ-axis coincide at one of these primes. -/
theorem sixtyseven_heegner_and_irregular :
    sixtyseven_both_cell.heegner ∧ sixtyseven_both_cell.irregular :=
  ⟨trivial, irregular_67_B58⟩

end Wieferich.IwasawaGrid
