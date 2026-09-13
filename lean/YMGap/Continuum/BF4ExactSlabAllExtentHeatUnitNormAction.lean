/-
# The completed heat unit has the ORIGINAL action-integral squared norm

The rational norms of the growing all-label codes converge to their actual
completed inner product. Their explicitly controlled interface-cutoff
discrepancy from the original full action integrals tends to zero. Constructive
limit uniqueness therefore identifies the two CReal representatives and the
actual completed norm, for every odd slab and every rational 0 < w < 1.

This identifies the SAME normalization quantity; it does not prove a strictly
positive lower bound, normalization, physical vacuum stationarity, compatible
slab maps, time transfer, a strict gap or a continuum theory. Both Cauchy
moduli and the comparison modulus are supplied by the imported constructions.
-/

import YMGap.Continuum.BF4ExactSlabAllExtentHeatUnitActionComparison

namespace YMGap.Continuum.BF4ExactSlabAllExtentHeatUnitNormAction

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.BF4ExactSlabAllExtentCutoffLimitForm
open YMGap.Continuum.BF4ExactSlabAllExtentCutoffLimitGNS
open YMGap.Continuum.BF4ExactSlabAllExtentHeatUnit
open YMGap.Continuum.BF4ExactSlabAllExtentHeatUnitCauchy
open YMGap.Continuum.BF4ExactSlabAllExtentActionLimit
open YMGap.Continuum.BF4ExactSlabAllExtentHeatUnitActionComparison

def heatUnitNormRepresentative (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) : CReal :=
  (cutoffLimitGNSData w (Q'.le_of_lt hw0) half).cinnerRep
    (heatUnitCauchy w hw0 hw1 half) (heatUnitCauchy w hw0 hw1 half)

theorem heatUnit_inner_sequence (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half K : Nat) :
    (cutoffLimitGNSData w (Q'.le_of_lt hw0) half).cInnerSeq
      (heatUnitCauchy w hw0 hw1 half) (heatUnitCauchy w hw0 hw1 half) K =
      limitForm w (heatUnitCode K half) (heatUnitCode K half) := by
  unfold GNSData.cInnerSeq
  rw [heatUnitCauchy_seq, cutoffLimitGNSData_form]

theorem heatUnitNorm_converges (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) :
    CReal.ConvergesTo
      (fun K => CReal.ofQ' (limitForm w (heatUnitCode K half) (heatUnitCode K half)))
      (heatUnitNormRepresentative w hw0 hw1 half) := by
  have hseq := funext (heatUnit_inner_sequence w hw0 hw1 half)
  have h := CReal.convergesTo_ofQ'CauchySeq
    ((cutoffLimitGNSData w (Q'.le_of_lt hw0) half).cInnerSeq
      (heatUnitCauchy w hw0 hw1 half) (heatUnitCauchy w hw0 hw1 half))
    ((cutoffLimitGNSData w (Q'.le_of_lt hw0) half).cInnerQCauchy
      (heatUnitCauchy w hw0 hw1 half) (heatUnitCauchy w hw0 hw1 half))
  change CReal.ConvergesTo _ (heatUnitNormRepresentative w hw0 hw1 half) at h
  rw [hseq] at h
  exact h

theorem heatUnitNormRepresentative_eq_action (w : Q') (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (half : Nat) :
    CReal.Equiv (heatUnitNormRepresentative w hw0 hw1 half) (fullActionLimit w hw0 hw1 half) :=
  CReal.Equiv_of_ofQ'_limit_close
    (heatUnitNorm_converges w hw0 hw1 half)
    (heatProductHaar_converges w hw0 hw1 _ _ _)
    (fun ε hε => ⟨unitNormActionModulus w half ε,
      fun K hK => heatUnitNormAction_close hw0 hw1 half ε hε K hK⟩)

/-- This is the inner product on the previously constructed original slab carrier. -/
theorem completedHeatUnit_norm_rep (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) :
    (cutoffLimitCompletion w (Q'.le_of_lt hw0) half).hilbert.cinner
      (completedHeatUnit w hw0 hw1 half) (completedHeatUnit w hw0 hw1 half) =
      Quotient.mk CReal.crealSetoid (heatUnitNormRepresentative w hw0 hw1 half) := rfl

/-- No decoupled partition function or surrogate measure enters this equality. -/
theorem completedHeatUnit_norm_action (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) :
    (cutoffLimitCompletion w (Q'.le_of_lt hw0) half).hilbert.cinner
      (completedHeatUnit w hw0 hw1 half) (completedHeatUnit w hw0 hw1 half) =
      Quotient.mk CReal.crealSetoid (fullActionLimit w hw0 hw1 half) :=
  (completedHeatUnit_norm_rep w hw0 hw1 half).trans
    (Quotient.sound (heatUnitNormRepresentative_eq_action w hw0 hw1 half))

end YMGap.Continuum.BF4ExactSlabAllExtentHeatUnitNormAction

#print axioms YMGap.Continuum.BF4ExactSlabAllExtentHeatUnitNormAction.heatUnitNormRepresentative
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentHeatUnitNormAction.heatUnit_inner_sequence
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentHeatUnitNormAction.heatUnitNorm_converges
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentHeatUnitNormAction.heatUnitNormRepresentative_eq_action
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentHeatUnitNormAction.completedHeatUnit_norm_rep
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentHeatUnitNormAction.completedHeatUnit_norm_action
