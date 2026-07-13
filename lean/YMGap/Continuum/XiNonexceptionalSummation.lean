/-
# Global summation of the nonexceptional source

The admissible component switch is injective on the nonexceptional source,
lands in the opposite restricted occurrence-pair product, and preserves each
pair weight.  The constructive finite weighted-injection theorem therefore
bounds the entire nonexceptional sum by that opposite product.
-/

import YMGap.Continuum.XiNonexceptionalTargetValidity

namespace YMGap.Continuum.XiNonexceptionalSummation

open YMGap.Constructive
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.AbstractPolymerXi
open YMGap.Continuum.XiExceptionalWeightedInjection
open YMGap.Continuum.XiExceptionalOccurrenceCodes
open YMGap.Continuum.XiExceptionalSourceCodes
open YMGap.Continuum.XiExceptionalSourceWeight
open YMGap.Continuum.XiExceptionalSourcePartition
open YMGap.Continuum.XiAdmissibleSourceSwitch
open YMGap.Continuum.XiNonexceptionalTargetValidity

variable {L : Lattice}
variable [DecidableEq L.Plaquette]

theorem nonexceptionalSourceCodes_nodup
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool) :
    (nonexceptionalSourceCodes Gamma qP b1 b2).Nodup := by
  unfold nonexceptionalSourceCodes
  exact nodup_filter_bool _ _ (maskPairs_nodup Gamma.length)

theorem nonexceptional_source_le_opposite_product
    {w : Q'} (hw : (0 : Q') ≤ w)
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (label : L.Plaquette → Rep) :
    qListSum (occurrencePairWeight w qP b1 b2 Gamma label)
        (nonexceptionalSourceCodes Gamma qP b1 b2) ≤
      XiR w (fun X => qP X && !((fun X => b1 X || b2 X) X)) Gamma label *
        XiR w (fun X => qP X && !((fun _ : Polymer L => false) X))
          Gamma label := by
  have hsum :
      qListSum (occurrencePairWeight w qP b1 b2 Gamma label)
          (nonexceptionalSourceCodes Gamma qP b1 b2) ≤
        qListSum
          (occurrencePairWeight w qP (fun X => b1 X || b2 X)
            (fun _ => false) Gamma label)
          (maskPairs Gamma.length) := by
    apply qListSum_le_of_injective
      (nonexceptionalSourceCodes Gamma qP b1 b2)
      (maskPairs Gamma.length)
      (occurrencePairWeight w qP b1 b2 Gamma label)
      (occurrencePairWeight w qP (fun X => b1 X || b2 X)
        (fun _ => false) Gamma label)
      (switchedBranchCode Gamma b2)
    · exact nonexceptionalSourceCodes_nodup Gamma qP b1 b2
    · intro pair _
      exact maskPairs_complete (switchedBranchCode Gamma b2 pair)
    · intro pair1 hmem1 pair2 hmem2 hcode
      have h1 := nonexceptional_of_mem Gamma qP b1 b2 pair1 hmem1
      have h2 := nonexceptional_of_mem Gamma qP b1 b2 pair2 hmem2
      exact switchedBranchCode_injective_of_admissible Gamma qP b1 b2
        pair1 pair2 h1.1 h2.1 hcode
    · intro pair hmem
      have hp := nonexceptional_of_mem Gamma qP b1 b2 pair hmem
      exact Q'.le_of_eqv (Q'.eqv_symm
        (nonexceptional_switched_weight_eqv_source w Gamma qP b1 b2
          label pair hp.1 hp.2))
    · intro pair _
      exact occurrencePairWeight_nonnegative hw qP
        (fun X => b1 X || b2 X) (fun _ => false) Gamma label pair
  exact Q'.le_trans' _ _ _ hsum
    (Q'.le_of_eqv
      (occurrencePairWeight_sum_eqv_restriction_product w qP
        (fun X => b1 X || b2 X) (fun _ => false) Gamma label))

#print axioms nonexceptionalSourceCodes_nodup
#print axioms nonexceptional_source_le_opposite_product

end YMGap.Continuum.XiNonexceptionalSummation
