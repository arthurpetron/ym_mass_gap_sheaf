/-
# Angular control of the ORIGINAL full-product heat defect

Use the positive-contraction potential along the actual cyclic path, with
the reference following the coordinate rotation. This avoids any assumed
commutation of different updates. The factor is two, independent of volume.
The sharper factor-one target is not asserted. Proper active subsets,
signed endpoint corrections and physical/continuum conclusions are separate.
-/

import YMGap.Continuum.PositiveContractionProductDefect
import YMGap.Continuum.SU2QuaternionProductHeatCyclicContraction
import YMGap.Continuum.SU2QuaternionCyclicRotationPeriod
import YMGap.Continuum.SU2QuaternionCyclicAngularEnergy
import YMGap.Continuum.SchurHadamardTransfer

namespace YMGap.Continuum.SU2QuaternionProductHeatAngularDefect

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionHaarCertificateReindex
open YMGap.Continuum.SU2QuaternionBlockReversal
open YMGap.Continuum.SU2QuaternionHeadHeatDiagonal
open YMGap.Continuum.SU2QuaternionHeadHeatPositiveContraction
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionProductHeatCyclicFold
open YMGap.Continuum.SU2QuaternionProductHeatCyclicRotation
open YMGap.Continuum.SU2QuaternionProductHeatCyclicContraction
open YMGap.Continuum.SU2QuaternionCyclicRotationPeriod
open YMGap.Continuum.SU2QuaternionCyclicAngularEnergy
open YMGap.Continuum.SU2QuaternionAngularReindex
open YMGap.Continuum.SU2QuaternionFiniteHaarGNSCarrier
open YMGap.Continuum.SU2HeatCutoffCasimirBound
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarLinearAngularEnergy
open YMGap.Continuum.PositiveContractionProductDefect

local infix:50 " ≈ " => Q'.eqv

private def haarPotential (n : Nat) (p q : RatPoly) : Q' :=
  quaternionHaar n (polyMul q q) + -(4 * quaternionHaar n (polyMul p q)) +
    3 * quaternionHaar n (polyMul p p)

private theorem rotation_pair (n : Nat) (p q : RatPoly)
    (hp : SupportedQuaternionBlocks n p) (hq : SupportedQuaternionBlocks n q) :
    quaternionHaar n (polyMul (cycleRotation n p) (cycleRotation n q)) ≈
      quaternionHaar n (polyMul p q) := by
  unfold cycleRotation
  rw [← reindexQuaternionPolynomial_mul, ← reindexQuaternionPolynomial_mul]
  exact Q'.eqv_trans _ _ _
    (quaternionHaar_reindex (reverseBlocks n) _ (reindex_supported _ _))
    (quaternionHaar_reindex (reverseTailBlocks n) _ (supported_polyMul hp hq))

private theorem rotation_potential (n : Nat) (p q : RatPoly)
    (hp : SupportedQuaternionBlocks n p) (hq : SupportedQuaternionBlocks n q) :
    haarPotential n (cycleRotation n p) (cycleRotation n q) ≈ haarPotential n p q :=
  Q'.add_eqv_congr'
    (Q'.add_eqv_congr' (rotation_pair n q q hq hq)
      (Q'.neg_eqv_congr _ _ (Q'.mul_eqv_congr_left _ _ _ (rotation_pair n p q hp hq))))
    (Q'.mul_eqv_congr_left _ _ _ (rotation_pair n p p hp hp))

private theorem potential_carrier_right (n : Nat) (p : RatPoly) {q r : RatPoly}
    (h : HaarCarrierEqv n q r) : haarPotential n p q ≈ haarPotential n p r :=
  Q'.add_eqv_congr'
    (Q'.add_eqv_congr' (haar_of_carrier (HaarCarrierEqv.mul h h))
      (Q'.neg_eqv_congr _ _ (Q'.mul_eqv_congr_left _ _ _ (h p))))
    (Q'.eqv_refl _)

private theorem cyclic_potential_step (tail : Nat) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (K : Nat)
    (p q : RatPoly) (hp : SupportedQuaternionBlocks (tail+1) p)
    (hq : SupportedQuaternionBlocks (tail+1) q) :
    haarPotential (tail+1) (cycleRotation (tail+1) p) (cycleStep (tail+1) w K q) ≤
      haarPotential (tail+1) p q + 4 *
        (quaternionHaar (tail+1) (polyMul p p) +
          -(quaternionHaar (tail+1) (polyMul p (headMap w K p)))) := by
  let D := finiteHaarGNSData (tail+1)
  let P : D.V → D.V := fun a => ⟨headMap w K a.val, headMap_supported tail w K a.property⟩
  have hs := potential_step D P
    (fun a b => headMap_symmetric tail w K a.val b.val a.property b.property)
    (fun a => headMap_positive tail hw0 K a.val a.property)
    (fun a => headMap_form_le_norm tail hw0 hw1 K a.val a.property)
    ⟨p, hp⟩ ⟨q, hq⟩
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (potential_carrier_right (tail+1) (cycleRotation (tail+1) p)
      (cycleStep_headMap_carrier tail w K q hq)))
    (Q'.le_trans' _ _ _
      (Q'.le_of_eqv (rotation_potential (tail+1) p (headMap w K q) hp
        (headMap_supported tail w K hq))) hs)

private theorem cycleIterate_succ_left (n : Nat) (w : Q') (K : Nat) :
    ∀ (m : Nat) (p : RatPoly), cycleIterate n w K (m+1) p =
      cycleStep n w K (cycleIterate n w K m p)
  | 0, _ => rfl
  | m+1, p => cycleIterate_succ_left n w K m (cycleStep n w K p)

/-- Every original cyclic prefix obeys a sum of angular costs on the rotating
REFERENCE, not on the changing smoothed input. The coefficient does not grow
with the number of steps. -/
theorem cycleIterate_rotated_defect_le_angular (tail : Nat) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q')) (K : Nat)
    (hK : sufficientCutoff w ≤ K) (p : RatPoly)
    (hp : SupportedQuaternionBlocks (tail+1) p) (m : Nat) :
    quaternionHaar (tail+1)
        (polyMul (rotateIterate (tail+1) m p) (rotateIterate (tail+1) m p)) +
      -(quaternionHaar (tail+1)
        (polyMul (rotateIterate (tail+1) m p) (cycleIterate (tail+1) w K m p))) ≤
      2 * finSum (fun i => ((1 : Q')-w) *
        quaternionHaar (tail+1) (angularSquare (rotateIterate (tail+1) i p))) m := by
  let D := finiteHaarGNSData (tail+1)
  let x : Nat → D.V := fun i =>
    ⟨rotateIterate (tail+1) i p, rotateIterate_supported (tail+1) i hp⟩
  let y : Nat → D.V := fun i =>
    ⟨cycleIterate (tail+1) w K i p, cycleIterate_supported _ _ _ i p hp⟩
  apply path_defect_bound D x y _ (potential_self D ⟨p, hp⟩) _ m
  intro i
  change haarPotential (tail+1) (rotateIterate (tail+1) (i+1) p)
      (cycleIterate (tail+1) w K (i+1) p) ≤ _
  rw [rotateIterate, cycleIterate_succ_left]
  have hr := rotateIterate_supported (tail+1) i hp
  have hy := cycleIterate_supported (tail+1) w K i p hp
  exact Q'.le_trans' _ _ _
    (cyclic_potential_step tail hw0 (Q'.le_of_lt hw1) K _ _ hr hy)
    (Q'.add_le_add_left _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ 4
        (headMap_defect_le_angular tail hw0 hw1 K hK _ hr) (by decide)))

/-- The original fully active endpoint, with its reference returned exactly
to the original input. All heat factors and signed input coefficients remain. -/
theorem productMap_range_defect_le_rotated_angular (tail : Nat) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q')) (K : Nat)
    (hK : sufficientCutoff w ≤ K) (p : RatPoly)
    (hp : SupportedQuaternionBlocks (tail+1) p) :
    quaternionHaar (tail+1) (polyMul p p) +
      -(quaternionHaar (tail+1)
        (polyMul p (productMap (tail+1) w K (List.range (tail+1)) p))) ≤
      2 * finSum (fun i => ((1 : Q')-w) *
        quaternionHaar (tail+1) (angularSquare (rotateIterate (tail+1) i p))) (tail+1) := by
  have hr := rotateIterate_period_carrier (tail+1) p hp
  have hc := HaarCarrierEqv.symm (productMap_range_cycle_carrier (tail+1) w K p)
  have hn := haar_of_carrier (HaarCarrierEqv.mul hr hr)
  have hm := haar_of_carrier (HaarCarrierEqv.mul hr hc)
  exact Q'.le_trans' _ _ _
    (Q'.ge_of_eqv (Q'.add_eqv_congr' hn (Q'.neg_eqv_congr _ _ hm)))
    (cycleIterate_rotated_defect_le_angular tail hw0 hw1 K hK p hp (tail+1))

/-- Dimension-independent angular DEFECT bound on the ORIGINAL fully active
product. The reference is the original signed polynomial, the angular sum is
over its original blocks, and the sole loss is the explicit factor two.
This is not a strict gap or an estimate for arbitrary proper active subsets. -/
theorem productMap_range_defect_le_two_angular (tail : Nat) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q')) (K : Nat)
    (hK : sufficientCutoff w ≤ K) (p : RatPoly)
    (hp : SupportedQuaternionBlocks (tail+1) p) :
    quaternionHaar (tail+1) (polyMul p p) +
      -(quaternionHaar (tail+1)
        (polyMul p (productMap (tail+1) w K (List.range (tail+1)) p))) ≤
      (2 * ((1 : Q')-w)) * finSum (fun i =>
        quaternionHaar (tail+1) (blockAngularSquare i p)) (tail+1) := by
  have he := SchurHadamardTransfer.finSum_congr_lt
    (fun i => ((1 : Q')-w) * quaternionHaar (tail+1)
      (angularSquare (rotateIterate (tail+1) i p)))
    (fun i => ((1 : Q')-w) * quaternionHaar (tail+1) (blockAngularSquare i p))
    (tail+1) (fun i hi => Q'.mul_eqv_congr_left _ _ _
      (rotateIterate_headAngularSquare_haar_of_lt (tail+1) (by omega) i hi p hp))
  have hf := Q'.eqv_symm (const_mul_finSum
    (fun i => quaternionHaar (tail+1) (blockAngularSquare i p)) ((1 : Q')-w) (tail+1))
  exact Q'.le_trans' _ _ _
    (productMap_range_defect_le_rotated_angular tail hw0 hw1 K hK p hp)
    (Q'.le_of_eqv (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left 2 _ _ (Q'.eqv_trans _ _ _ he hf))
      (Q'.eqv_symm (Q'.mul_assoc_eqv 2 ((1 : Q')-w) _))))

end YMGap.Continuum.SU2QuaternionProductHeatAngularDefect

#print axioms YMGap.Continuum.SU2QuaternionProductHeatAngularDefect.cycleIterate_rotated_defect_le_angular
#print axioms YMGap.Continuum.SU2QuaternionProductHeatAngularDefect.productMap_range_defect_le_rotated_angular
#print axioms YMGap.Continuum.SU2QuaternionProductHeatAngularDefect.productMap_range_defect_le_two_angular
