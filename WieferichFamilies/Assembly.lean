import WieferichFamilies.GoldCriterion
import WieferichFamilies.PlasticAnchor
import WieferichFamilies.ClassGroupStructure
import WieferichFamilies.IwasawaGrid
import WieferichFamilies.LocusDisjointness
import WieferichFamilies.PowerLadder
import WieferichFamilies.RecordCertificates
import WieferichFamilies.PierpontSmoothness
import WieferichFamilies.BernoulliAnchors

/-!
# Assembled statements

Connective theorems conjoining one representative result from each layer
of the development, so the soundness of the whole is a single `#check`.
-/

namespace Wieferich.Assembly

/-- The depth-2 unit-root condition is forced by the trace
(`unit_root_linearization`), and by Gold's criterion (J. Number
Theory 6 (1974)) it detects `λ_p(K) > 1`. -/
theorem unit_root_wieferich_typed {p a t : ℤ}
    (G : Wieferich.GoldCriterion.GoldCriterion p a t) :
    G.lambdaGtOne ∧ (p : ℤ) ∣ (a * t + 1) :=
  ⟨Wieferich.GoldCriterion.gold_criterion_holds G,
   Wieferich.GoldCriterion.unit_root_linearization p a t G.p_ne G.unit_root⟩

/-- The class-field layer, assembled: the closed form is forced by the
trace; a Gold flag of ℚ(√−23) splits the plastic cubic; `ℤ/4` escapes
the exponent-2 case; `67` is the doubly-positive cell; and the
Perrin-square member 521 is not a base-2 Wieferich prime. -/
theorem wieferich_gold_layer
    (p a t : ℤ) (hp : p ≠ 0)
    (hlin : (p : ℤ) ^ 2 ∣ ((a + p * t) ^ 2 - (a * (a + p * t) - p)))
    (D : Wieferich.PlasticAnchor.PlasticFold 23) (hf : D.flag) :
    (p : ℤ) ∣ (a * t + 1) ∧ D.plasticSplits ∧
    (∃ x : ZMod 4, x + x ≠ 0) ∧
    (Wieferich.IwasawaGrid.sixtyseven_both_cell.heegner ∧
      Wieferich.IwasawaGrid.sixtyseven_both_cell.irregular) ∧
    ¬ (521 : ℤ) ^ 2 ∣ (2 ^ 520 - 1) :=
  ⟨Wieferich.GoldCriterion.unit_root_linearization p a t hp hlin,
   Wieferich.PlasticAnchor.flag_implies_plastic_split D hf,
   Wieferich.ClassGroupStructure.z4_not_two_torsion,
   Wieferich.IwasawaGrid.sixtyseven_heegner_and_irregular,
   Wieferich.LocusDisjointness.plastic_521_not_classical⟩

/-- The certificate layer, assembled: the O(log p) ladder agrees with the
direct computation at 489061; the record 330017383 is certified; the
3-smoothness classification; and the Bernoulli anchors, including
`1093² ∣ 2¹⁰⁹² − 1`. -/
theorem gold_record_layer :
    ((489061 : ℕ) ^ 2 = 239180661721 ∧
      (239003622990 : ℕ) ^ 489060 ≡ 1 [MOD 239180661721]) ∧
    (330017383 : ℕ) ^ 2 ∣ 106546445419140355 ^ 330017382 - 1 ∧
    (163 = 2 * 3 ^ 4 + 1 ∧ 37 = 2 ^ 2 * 3 ^ 2 + 1) ∧
    ((37 : ℤ) ∣ (-7709321041217) ∧
      ((315 : ZMod 13) = -(7 * (1 + 7 + 9 + 10 + 8 + 11))) ∧
      ((1 + 13 + 17 + 19 : ZMod 25) = 0) ∧
      (1093 : ℕ) ^ 2 ∣ 2 ^ 1092 - 1) :=
  ⟨Wieferich.PowerLadder.ladder_matches_megadigit,
   Wieferich.RecordCertificates.record_330017383_dvd,
   Wieferich.PierpontSmoothness.heegner_top_is_pierpont,
   Wieferich.BernoulliAnchors.grid_reads_bernoulli⟩

end Wieferich.Assembly
