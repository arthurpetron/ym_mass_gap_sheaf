/-
# Separate cyclic coordinate motion from the actual fresh-output heat step

The cyclic step is not asserted positive or self-adjoint. Two explicit
reversals identify its derotation with an actual conjugated head heat map.
The resulting angular estimate pairs the output with the ROTATED input.
It is not the unrotated one-step defect, nor the full product estimate.
-/

import YMGap.Continuum.SU2QuaternionBlockReversal
import YMGap.Continuum.SU2QuaternionProductHeatCyclicFold
import YMGap.Continuum.SU2QuaternionConjugatedHeadHeatBlockEnergy
import YMGap.Continuum.BF4ExactSlabSelectedFaceCanonicalWord

namespace YMGap.Continuum.SU2QuaternionProductHeatCyclicRotation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugePolynomialSemantics
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
open YMGap.Continuum.BF4ExactSlabSelectedFaceCanonicalWord
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionHaarCertificateReindex
open YMGap.Continuum.SU2QuaternionHeadChainComposition
open YMGap.Continuum.SU2QuaternionSpareHeadCopy
open YMGap.Continuum.SU2QuaternionBlockReversal
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry
open YMGap.Continuum.SU2QuaternionRelativeHeatTransmission
open YMGap.Continuum.SU2QuaternionProductHeatCyclicFold
open YMGap.Continuum.SU2QuaternionHeadHeatDiagonal
open YMGap.Continuum.SU2QuaternionConjugatedHeadHeat
open YMGap.Continuum.SU2QuaternionConjugatedHeadHeatBlockEnergy
open YMGap.Continuum.SU2QuaternionAngularReindex
open YMGap.Continuum.SU2HeatCutoffCasimirBound
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarAngularCarrier

local infix:50 " ≈ " => Q'.eqv

private theorem reverseTail_heat_prefix (tail : Nat) (w : Q') (K : Nat) :
    QuaternionPrefixPolynomialEqv (tail+2)
      (reindexQuaternionPolynomial (reverseTailBlocks (tail+2))
        (heatAt 0 (tail+1) w K)) (relativeHeat w K) := by
  let s := reverseTailBlocks (tail+2)
  have hp : QuaternionPrefixPolyQuaternionEqv (tail+2)
      (reindexPolyQuaternion s
        (PolyQuaternion.mul (PolyQuaternion.coordinateVariable 0)
          (PolyQuaternion.conj (PolyQuaternion.coordinateVariable (tail+1)))))
      (PolyQuaternion.mul (PolyQuaternion.coordinateVariable 0)
        (PolyQuaternion.conj (PolyQuaternion.coordinateVariable 1))) := by
    rw [reindexPolyQuaternion_mul, reindexPolyQuaternion_conj]
    exact (reindex_coordinateVariable_prefix s (by omega)
      (reverseTailBlocks_map_zero _)).mul
      (reindex_coordinateVariable_prefix s (by omega)
        (reverseTailBlocks_map_one (tail+1))).conj
  have hc (d : Nat) : QuaternionPrefixPolynomialEqv (tail+2)
      (reindexQuaternionPolynomial s (characterPolynomial (scalarAt 0 (tail+1)) d))
      (characterPolynomial (scalarAt 0 1) d) :=
    (reindexQuaternionPolynomial_character_prefix s _ d).trans (hp.scalar.character d)
  change QuaternionPrefixPolynomialEqv (tail+2)
    (reindexQuaternionPolynomial s (heatAt 0 (tail+1) w K)) (heatAt 0 1 w K)
  unfold heatAt
  induction List.range (K+1) with
  | nil => exact .nil
  | cons d ds ih =>
      simp only [finitePolySum, reindexQuaternionPolynomial_add,
        reindexQuaternionPolynomial_smul]
      exact ((hc d).smul _).append ih

/-- Bilinear identification retains all spectators and both signed insertions. -/
theorem cycleStep_reversed_pairing (tail : Nat) (w : Q') (K : Nat)
    (p q : RatPoly) (hp : SupportedQuaternionBlocks (tail+1) p)
    (hq : SupportedQuaternionBlocks (tail+1) q) :
    quaternionHaar (tail+1) (polyMul q (cycleStep (tail+1) w K p)) ≈
      heatPair tail w K
        (reindexQuaternionPolynomial (reverseTailBlocks (tail+1)) p)
        (reindexQuaternionPolynomial (reverseBlocks (tail+1)) q) := by
  let s := reverseTailBlocks (tail+2)
  have hp' : SupportedQuaternionBlocks (tail+2) p :=
    fun t ht => Nat.le_trans (hp t ht) (by omega)
  have hh := heat_supported (by omega : 0 < tail+2)
    (by omega : tail+1 < tail+2) w K
  have hi := supported_polyMul (supported_polyMul hh hp') (lift_supported hq 1)
  have hs := quaternionHaar_reindex s
    (polyMul (polyMul (heatAt 0 (tail+1) w K) p) (liftHead q)) hi
  have he : QuaternionPrefixPolynomialEqv (tail+2)
      (reindexQuaternionPolynomial s
        (polyMul (polyMul (heatAt 0 (tail+1) w K) p) (liftHead q)))
      (polyMul (polyMul (relativeHeat w K)
        (copy (reindexQuaternionPolynomial (reverseTailBlocks (tail+1)) p)))
        (liftHead (reindexQuaternionPolynomial (reverseBlocks (tail+1)) q))) := by
    simp only [reindexQuaternionPolynomial_mul]
    exact ((reverseTail_heat_prefix tail w K).mul
      (reverseTail_source_copy_prefix (tail+1) (by omega) p hp)).mul
      (reverseTail_lift_prefix (tail+1) q)
  have ht := quaternionHaar_prefixPolynomialEqv (tail+2) he
    (reindex_supported s _)
    (supported_polyMul
      (supported_polyMul
        (heat_supported (by omega : 0 < tail+2) (by omega : 1 < tail+2) w K)
        (copy_supported (by omega) (reindex_supported (reverseTailBlocks (tail+1)) p)))
      (lift_supported (reindex_supported (reverseBlocks (tail+1)) q) 1))
  exact Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _))
    (Q'.eqv_trans _ _ _
      (Q'.eqv_symm (head_pairing (tail+1) 1 (polyMul (heatAt 0 (tail+1) w K) p) q))
      (Q'.eqv_trans _ _ _ (Q'.eqv_symm hs) ht))

/-- The cyclic output is a full reversal of head smoothing on tail-reversed input. -/
theorem cycleStep_rotation_carrier (tail : Nat) (w : Q') (K : Nat)
    (p : RatPoly) (hp : SupportedQuaternionBlocks (tail+1) p) :
    HaarCarrierEqv (tail+1) (cycleStep (tail+1) w K p)
      (reindexQuaternionPolynomial (reverseBlocks (tail+1))
        (headMap w K (reindexQuaternionPolynomial (reverseTailBlocks (tail+1)) p))) := by
  apply carrier_of_supported (cycleStep_supported _ _ _ hp) (reindex_supported _ _)
  intro q hq
  exact Q'.eqv_trans _ _ _ (cycleStep_reversed_pairing tail w K p q hp hq)
    (Q'.eqv_trans _ _ _ (Q'.eqv_symm (headMap_pairing tail w K _ _))
      (Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _))
        (Q'.eqv_symm (reindex_pair (reverseBlocks (tail+1)) q _ hq
          (headMap_supported tail w K (reindex_supported _ _))))))

/-- The coordinate motion left after a fresh-output step, without smoothing. -/
def cycleRotation (n : Nat) (p : RatPoly) : RatPoly :=
  reindexQuaternionPolynomial (reverseBlocks n)
    (reindexQuaternionPolynomial (reverseTailBlocks n) p)

/-- Undo that coordinate motion, in the opposite order of the two involutions. -/
def cycleReturn (n : Nat) (p : RatPoly) : RatPoly :=
  reindexQuaternionPolynomial (reverseTailBlocks n)
    (reindexQuaternionPolynomial (reverseBlocks n) p)

/-- Derotation of the actual cyclic step is an actual conjugated head update. -/
theorem cycleReturn_step_carrier (tail : Nat) (w : Q') (K : Nat)
    (p : RatPoly) (hp : SupportedQuaternionBlocks (tail+1) p) :
    HaarCarrierEqv (tail+1) (cycleReturn (tail+1) (cycleStep (tail+1) w K p))
      (conjugatedHeadMap (reverseTailBlocks (tail+1)) w K p) := by
  have hm := headMap_supported tail w K (reindex_supported (reverseTailBlocks (tail+1)) p)
  have h := reindex_carrier (reverseBlocks (tail+1))
    (cycleStep_supported _ _ _ hp) (reindex_supported _ _)
    (cycleStep_rotation_carrier tail w K p hp)
  have hi := carrierOfPrefix (reindex_supported (reverseBlocks (tail+1)) _) hm
    (reindex_twice_prefix (reverseBlocks (tail+1)) _)
  exact reindex_carrier (reverseTailBlocks (tail+1)) (reindex_supported _ _) hm
    (HaarCarrierEqv.trans h hi)

/-- Move inverse coordinate motion from output to forward motion of the input. -/
theorem cycleReturn_pairing (n : Nat) (p q : RatPoly)
    (hp : SupportedQuaternionBlocks n p) (hq : SupportedQuaternionBlocks n q) :
    quaternionHaar n (polyMul p (cycleReturn n q)) ≈
      quaternionHaar n (polyMul (cycleRotation n p) q) :=
  Q'.eqv_trans _ _ _
    (reindex_pair (reverseTailBlocks n) p _ hp (reindex_supported _ _))
    (reindex_pair (reverseBlocks n) _ q (reindex_supported _ _) hq)

/-- Correct local defect: the comparison input follows the cyclic rotation.
No unrotated intermediate-step bound or full-product inequality is asserted. -/
theorem cycleStep_rotated_defect_le_head_energy (tail : Nat) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q')) (K : Nat)
    (hK : sufficientCutoff w ≤ K) (p : RatPoly)
    (hp : SupportedQuaternionBlocks (tail+1) p) :
    quaternionHaar (tail+1) (polyMul p p) -
        quaternionHaar (tail+1)
          (polyMul (cycleRotation (tail+1) p) (cycleStep (tail+1) w K p)) ≤
      ((1 : Q')-w) * quaternionHaar (tail+1) (blockAngularSquare 0 p) := by
  have he := Q'.eqv_trans _ _ _
    (Q'.eqv_symm (cycleReturn_pairing (tail+1) p (cycleStep (tail+1) w K p)
      hp (cycleStep_supported _ _ _ hp)))
    (cycleReturn_step_carrier tail w K p hp p)
  have hd := conjugatedHeadMap_defect_le_selected_block_energy tail hw0 hw1 K hK
    (reverseTailBlocks (tail+1)) p hp
  rw [reverseTailBlocks_map_zero] at hd
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.add_eqv_congr' (Q'.eqv_refl _) (Q'.neg_eqv_congr _ _ he))) hd

end YMGap.Continuum.SU2QuaternionProductHeatCyclicRotation

#print axioms YMGap.Continuum.SU2QuaternionProductHeatCyclicRotation.cycleStep_reversed_pairing
#print axioms YMGap.Continuum.SU2QuaternionProductHeatCyclicRotation.cycleStep_rotation_carrier
#print axioms YMGap.Continuum.SU2QuaternionProductHeatCyclicRotation.cycleRotation
#print axioms YMGap.Continuum.SU2QuaternionProductHeatCyclicRotation.cycleReturn
#print axioms YMGap.Continuum.SU2QuaternionProductHeatCyclicRotation.cycleReturn_step_carrier
#print axioms YMGap.Continuum.SU2QuaternionProductHeatCyclicRotation.cycleReturn_pairing
#print axioms YMGap.Continuum.SU2QuaternionProductHeatCyclicRotation.cycleStep_rotated_defect_le_head_energy
