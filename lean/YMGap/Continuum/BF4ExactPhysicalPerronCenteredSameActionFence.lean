/-
# Cutoff-one fence for centered exact/physical same action

The uncentered exact-Haar / positive-physical identification is already false.
Centering by the physical stationary mean does not repair it.  At cutoff one
and heat coordinate `w = 8/9`, the unconditional Haar-five evaluation gives a
sharp elementary separation:

* the exact centered vacuum moment is at least `5/8`;
* the positive physical centered vacuum moment is at most `1/8`.

Thus the centered same-action seam is also uninhabited at this concrete
physical point.  Any surviving producer must work directly with the positive
physical law, or compare it with the signed Haar law using an explicit
nonzero error.

## Axiom gate

Finite lists and exact `Q'` arithmetic only.  No `Classical.*`,
`native_decide`, `sorry`, custom axiom, choice, or noncomputable declaration.
-/

import YMGap.Continuum.BF4CentralLowerCubeRowDomination
import YMGap.Continuum.BF4ExactCutoffOneHaarFiveClosure

namespace YMGap.Continuum.BF4ExactPhysicalPerronCenteredSameActionFence

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum.BF4CanonicalFiniteNumeratorPartitionBudget
open YMGap.Continuum.BF4CentralLowerCubeRowDomination
open YMGap.Continuum.BF4CutoffOneBinarySurfaceCertificate
open YMGap.Continuum.BF4ExactCutoffOneHaarFiveClosure
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumMomentExpansion
open YMGap.Continuum.BF4ExactPhysicalPerronCenteredReroute
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4SU2FixedMagneticPositiveKernelConvergence
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

private theorem q_add_le_add {a b c d : Q'}
    (hab : a ≤ b) (hcd : c ≤ d) :
    a + c ≤ b + d :=
  Q'.le_trans' _ _ _
    (Q'.add_le_add_right a b c hab)
    (Q'.add_le_add_left b c d hcd)

private theorem listQSum_nonnegative
    {A : Type} (value : A → Q')
    (hvalue : ∀ item, (0 : Q') ≤ value item) :
    ∀ items : List A, (0 : Q') ≤ listQSum value items
  | [] => Q'.le_refl' 0
  | head :: tail =>
      Q'.zero_le_add _ _ (hvalue head)
        (listQSum_nonnegative value hvalue tail)

private theorem listQSum_member_le_nonnegative
    {A : Type} (value : A → Q')
    (hvalue : ∀ item, (0 : Q') ≤ value item) :
    ∀ (items : List A) {item : A}, item ∈ items →
      value item ≤ listQSum value items
  | [], _, hmem => False.elim (List.not_mem_nil hmem)
  | head :: tail, item, hmem => by
      rcases List.mem_cons.mp hmem with hhead | htail
      · subst item
        exact Q'.add_le_self_of_nonneg _ _
          (listQSum_nonnegative value hvalue tail)
      · have ih :=
          listQSum_member_le_nonnegative value hvalue tail htail
        have htailLe :
            listQSum value tail ≤
              value head + listQSum value tail := by
          exact Q'.le_trans' _
            (listQSum value tail + value head) _
            (Q'.add_le_self_of_nonneg _ _ (hvalue head))
            (Q'.le_of_eqv
              (Q'.add_comm_eqv
                (listQSum value tail) (value head)))
        exact Q'.le_trans' _ _ _ ih htailLe

private theorem neg_mul_neg_eqv_local (a b : Q') :
    (-a) * (-b) ≈ a * b := by
  refine Q'.eqv_trans _ (-(a * (-b))) _
    (Q'.neg_mul_eqv a (-b)) ?_
  refine Q'.eqv_trans _ (-(-(a * b))) _
    (Q'.neg_eqv_congr _ _ (Q'.mul_neg_eqv a b))
    (Q'.neg_neg_eqv (a * b))

/-! ## 1. Exact lower bound -/

/-- At the concrete nome `8/9`, the actual cutoff-one exact-Haar centered
vacuum moment is at least `5/8`. -/
theorem fiveEighths_le_exactCenteredVacuumMomentExpression_eightNinths
    (hw : (0 : Q') ≤ cubeActivitySevenWeightFloor) :
    Q'.mkPos 5 8 (by decide) ≤
      exactCenteredVacuumMomentExpression
        cubeActivitySevenWeightFloor hw 1 := by
  let p := centralPhysicalRowMarginal
    cubeActivitySevenWeightFloor hw 1 0 zeroEdgeLabelling
  let R := exactVacuumRightConstantCrossMoment
    cubeActivitySevenWeightFloor 1
  let C := exactConstantQuadraticMoment
    cubeActivitySevenWeightFloor 1
  have hp0 : (0 : Q') ≤ p :=
    centralPhysicalRowMarginal_nonnegative
      hw 1 0 zeroEdgeLabelling
  have hp8 : p ≤ Q'.mkPos 1 8 (by decide) :=
    centralVacuumRowMarginal_le_oneEighth_of_eightNinths_le
      hw (Q'.le_refl' cubeActivitySevenWeightFloor) (by decide)
  have hRactual :
      R ≈ QPoly.eval expectedVacuumRowHeatPolynomial
        cubeActivitySevenWeightFloor :=
    exactVacuumRightConstantCrossMoment_cutoffOne_actual
      cubeActivitySevenWeightFloor
  have hR0eval :
      (0 : Q') ≤ QPoly.eval expectedVacuumRowHeatPolynomial
        cubeActivitySevenWeightFloor :=
    eval_nonnegative_of_allNonnegativeCoefficientsB hw
      expectedVacuumRowHeatPolynomial (by decide)
  have hR0 : (0 : Q') ≤ R :=
    Q'.le_trans' _ _ _ hR0eval (Q'.ge_of_eqv hRactual)
  have hRle : R ≤ Q'.mkPos 3 2 (by decide) :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv hRactual) (by
      unfold cubeActivitySevenWeightFloor
      decide)
  have hCactual :
      C ≈ QPoly.eval expectedConstantHeatPolynomial
        cubeActivitySevenWeightFloor :=
    exactConstantQuadraticMoment_cutoffOne_actual
      cubeActivitySevenWeightFloor
  have hC0eval :
      (0 : Q') ≤ QPoly.eval expectedConstantHeatPolynomial
        cubeActivitySevenWeightFloor :=
    eval_nonnegative_of_allNonnegativeCoefficientsB hw
      expectedConstantHeatPolynomial (by decide)
  have hC0 : (0 : Q') ≤ C :=
    Q'.le_trans' _ _ _ hC0eval (Q'.ge_of_eqv hCactual)
  have hpR_le : p * R ≤ Q'.mkPos 3 16 (by decide) := by
    exact Q'.le_trans' _
      (Q'.mkPos 1 8 (by decide) * R) _
      (Q'.mul_le_mul_of_nonneg_right _ _ _ hp8 hR0)
      (Q'.le_trans' _
        (Q'.mkPos 1 8 (by decide) * Q'.mkPos 3 2 (by decide)) _
        (Q'.mul_le_mul_of_nonneg_left _ _ _ hRle (by decide))
        (by decide))
  have hnegative :
      -(Q'.mkPos 3 16 (by decide)) ≤ (-p) * R :=
    Q'.le_trans' _ (-(p * R)) _
      (Q'.neg_le_neg hpR_le)
      (Q'.ge_of_eqv (Q'.neg_mul_eqv p R))
  have hpositive : (0 : Q') ≤ ((-p) * (-p)) * C := by
    have hpp0 : (0 : Q') ≤ p * p :=
      Q'.mul_nonneg p p hp0 hp0
    have hnegneg0 : (0 : Q') ≤ (-p) * (-p) :=
      Q'.le_trans' _ _ _ hpp0
        (Q'.ge_of_eqv (neg_mul_neg_eqv_local p p))
    exact Q'.mul_nonneg _ _ hnegneg0 hC0
  unfold exactCenteredVacuumMomentExpression
  change Q'.mkPos 5 8 (by decide) ≤
    1 + ((-p) * R + ((-p) * R + ((-p) * (-p)) * C))
  exact Q'.le_trans' _
    (1 +
      (-(Q'.mkPos 3 16 (by decide)) +
        (-(Q'.mkPos 3 16 (by decide)) + 0))) _
    (by decide)
    (q_add_le_add (Q'.le_refl' 1)
      (q_add_le_add hnegative
        (q_add_le_add hnegative hpositive)))

/-! ## 2. Physical upper bound -/

/-- At the same point, the centered positive-physical vacuum moment is at
most the vacuum row mass and hence at most `1/8`. -/
theorem physicalCenteredVacuumMomentExpression_eightNinths_le_oneEighth
    (hw : (0 : Q') ≤ cubeActivitySevenWeightFloor) :
    physicalCenteredVacuumMomentExpression
        cubeActivitySevenWeightFloor hw 1 ≤
      Q'.mkPos 1 8 (by decide) := by
  let p := centralPhysicalRowMarginal
    cubeActivitySevenWeightFloor hw 1 0 zeroEdgeLabelling
  let diagonal := centralNormalizedPhysicalReflectedKernel
    cubeActivitySevenWeightFloor hw 1 0
      zeroEdgeLabelling zeroEdgeLabelling
  have hp0 : (0 : Q') ≤ p :=
    centralPhysicalRowMarginal_nonnegative
      hw 1 0 zeroEdgeLabelling
  have hp8 : p ≤ Q'.mkPos 1 8 (by decide) :=
    centralVacuumRowMarginal_le_oneEighth_of_eightNinths_le
      hw (Q'.le_refl' cubeActivitySevenWeightFloor) (by decide)
  have hdiagonal : diagonal ≤ p := by
    unfold p centralPhysicalRowMarginal diagonal
    exact listQSum_member_le_nonnegative
      (centralNormalizedPhysicalReflectedKernel
        cubeActivitySevenWeightFloor hw 1 0 zeroEdgeLabelling)
      (fun target =>
        centralNormalizedPhysicalReflectedKernel_nonnegative
          hw 1 0 zeroEdgeLabelling target)
      (centralHalfStates 1 0)
      (zeroEdgeLabelling_mem_centralHalfStates 1 0)
  have hsquare0 : (0 : Q') ≤ p * p :=
    Q'.mul_nonneg p p hp0 hp0
  have hnegative : -(p * p) ≤ (0 : Q') :=
    Q'.nonpos_neg_of_nonneg hsquare0
  unfold physicalCenteredVacuumMomentExpression
  change diagonal + (-(p * p)) ≤ Q'.mkPos 1 8 (by decide)
  exact Q'.le_trans' _ (p + 0) _
    (q_add_le_add hdiagonal hnegative)
    (Q'.le_trans' _ p _
      (Q'.le_of_eqv (Q'.eqv_of_eq (Q'.add_zero' p)))
      hp8)

/-! ## 3. The centered same-action obstruction -/

/-- Centered exact-Haar / positive-physical same action is already false at
cutoff one and nome `8/9`. -/
theorem exactHaarPhysicalPerronCenteredSameActionAt_cutoffOne_eightNinths_uninhabited
    (hw : (0 : Q') ≤ cubeActivitySevenWeightFloor) :
    ExactHaarPhysicalPerronCenteredSameActionAt
        cubeActivitySevenWeightFloor hw 1 → False := by
  intro identification
  have himpossible :
      Q'.mkPos 5 8 (by decide) ≤ Q'.mkPos 1 8 (by decide) :=
    Q'.le_trans' _
      (exactCenteredVacuumMomentExpression
        cubeActivitySevenWeightFloor hw 1) _
      (fiveEighths_le_exactCenteredVacuumMomentExpression_eightNinths hw)
      (Q'.le_trans' _
        (physicalCenteredVacuumMomentExpression
          cubeActivitySevenWeightFloor hw 1) _
        (Q'.le_of_eqv
          (YMGap.Continuum.BF4ExactPhysicalCenteredVacuumMomentExpansion.ExactHaarPhysicalPerronCenteredSameActionAt.vacuumMoment_balance
            identification))
        (physicalCenteredVacuumMomentExpression_eightNinths_le_oneEighth hw))
  exact (by decide : ¬
    Q'.mkPos 5 8 (by decide) ≤ Q'.mkPos 1 8 (by decide)) himpossible

end YMGap.Continuum.BF4ExactPhysicalPerronCenteredSameActionFence

#print axioms YMGap.Continuum.BF4ExactPhysicalPerronCenteredSameActionFence.fiveEighths_le_exactCenteredVacuumMomentExpression_eightNinths
#print axioms YMGap.Continuum.BF4ExactPhysicalPerronCenteredSameActionFence.physicalCenteredVacuumMomentExpression_eightNinths_le_oneEighth
#print axioms YMGap.Continuum.BF4ExactPhysicalPerronCenteredSameActionFence.exactHaarPhysicalPerronCenteredSameActionAt_cutoffOne_eightNinths_uninhabited
