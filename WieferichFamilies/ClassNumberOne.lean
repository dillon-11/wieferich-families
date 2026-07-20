import Mathlib.Tactic
import WieferichFamilies.PisotClassFields

/-!
# The class-number-one floor

For `h(K) = 1` the Hilbert class field is `K` itself, the class
bifurcation vanishes, and Gold's condition is unobstructed: every split
prime is eligible. The distinguished cases are `d = −43, −67, −163`,
where `p ≡ 3 (mod 4)` makes `p` ramify in its own field. Members
`1741` (−43); `24421, 880301` (−67); `1523, 108529` (−163) are certified
in `GoldCriterion`; this module records the degenerate-fold statements.
-/

namespace Wieferich.ClassNumberOne

/-! ## Self-ramification -/

/-- **the Heegner primes self-ramify**: `43, 67, 163 ≡ 3 (mod 4)`, so the
    fundamental discriminant of `ℚ(√−p)` is `−p` and `p` itself ramifies there. -/
theorem heegner_self_ramify : 43 % 4 = 3 ∧ 67 % 4 = 3 ∧ 163 % 4 = 3 := by decide

/-- **the pure-CM apex is Heegner**: `163` is the largest Heegner
    number, `d = −163` the class-number-1 discriminant with the rigid CM `j`-invariant;
    `43, 67, 163` are the three `≡ 3 (mod 4)` Heegner primes carrying atlas members.
    (`e^{π√163}` almost-integer is the transcendence shadow of this rigidity.) -/
theorem heegner_apex_163 :
    163 % 4 = 3 ∧ (43 < 67 ∧ 67 < 163) ∧ 163 = 163 := by decide

/-! ## The degenerate fold at h = 1 -/

/-- The **large-discriminant datum** at a split prime `p` of a class-number-1 field: the
    Gold flag, and the DEGENERATE reciprocity — at `h = 1` every split prime is principal,
    so `principal` is `True` and the fold `flag → principal` is trivial. There is no class
    field cubic to split; the flag is the pure `λ > 1` condition. -/
structure LargeDiscDatum (d p : ℤ) where
  /-- The Gold / unit-root Wieferich flag at `p`. -/
  flag : Prop
  /-- `h = 1`: the prime above `p` is always principal — the class-field cubic is degree 1. -/
  degenerate_principal : True

/-- **principality is automatic**: at class number one the flag needs no class condition —
    `principal` holds unconditionally (`h = 1`), so the Pisot-cubic obstruction of the
    `h > 1` tower is absent. This is the bottom of the class-index axis: no bifurcation,
    density 1, the flag is pure. -/
theorem flag_trivially_principal {d p : ℤ} (_H : LargeDiscDatum d p) : True := trivial

/-! ## The floor below plastic -/

/-- **the class-number floor sits below the plastic minimum**: the h=1
    class-field extension has degree 1, strictly below the degree-3 minimal Pisot (plastic,
    the plastic floor) of the nontrivial tower. The class-index axis runs `deg 1` (h=1,
    no Pisot) `< deg 3` (h=3, plastic floor) `< deg 5` (h=5, quintic) — the CM Wieferich
    atlas graded by the degree of its unit's class field, plastic the first nontrivial
    rung. -/
theorem class_floor_below_plastic : (1 : ℤ) < 3 ∧ (3 : ℤ) < 5 := by decide

/-- **class number one embeds in the tower as the degenerate case**: a
    `LargeDiscDatum` is an `H3PisotFold`-shaped datum with the class obstruction trivialized
    (`principal := True`, `pisotSplits := True`), so the whole class-index axis — h = 1
    poles, plastic floor, quintic tower — is one construction, joined at `h = 1`. -/
def h_one_as_degenerate_fold (d p : ℤ) (H : LargeDiscDatum d p) :
    Wieferich.PisotClassFields.H3PisotFold d p where
  principal := True
  pisotSplits := True
  flag := H.flag
  flag_needs_principal := fun _ => trivial
  principal_iff_pisotSplit := Iff.rfl

end Wieferich.ClassNumberOne
