/-
# Partial-product angular defect with the inactive residual retained

For a partition into inactive F and active ids, put q=P_F f and r=f-q.
The ORIGINAL partial-product form defect is exactly H(r*r) plus the full
product defect on q. The checked factor-two angular estimate therefore
applies to q, without pretending inactive coordinates are identity channels.
The residual is an actual computed polynomial, not an assumed error budget.

This does not prove it small in a spatial/scaling family, bound derivatives
of the interacting source, or control the signed endpoint correction.
-/

import YMGap.Continuum.SU2QuaternionProductHeatInactiveProjection
import YMGap.Continuum.SU2QuaternionHaarFamilyPythagoras
import YMGap.Continuum.SU2QuaternionProductHeatAngularDefect

namespace YMGap.Continuum.SU2QuaternionProductHeatInactiveAngularDefect

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionHaarFamilyProjection
open YMGap.Continuum.SU2QuaternionHaarFamilyPythagoras
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionProductHeatInactiveProjection
open YMGap.Continuum.SU2QuaternionProductHeatAngularDefect
open YMGap.Continuum.SU2QuaternionAngularReindex
open YMGap.Continuum.SU2HeatCutoffCasimirBound
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv

/-- Exact FORM-defect decomposition, not just a norm-square comparison of
the two output maps. The entire original input is projected. -/
theorem productMap_defect_eq_residual_add_full (n : Nat) (w : Q') (K : Nat)
    (ids F : List Nat) (hids : ∀ i, i ∈ ids → i < n)
    (hF : ∀ i, i ∈ F → i < n) (hnot : ∀ i, i ∈ F → i ∉ ids)
    (hcover : (F++ids).Perm (List.range n))
    (f : RatPoly) (hf : SupportedQuaternionBlocks n f) :
    quaternionHaar n (polyMul f f) +
      -(quaternionHaar n (polyMul f (productMap n w K ids f))) ≈
      quaternionHaar n (polyMul (familyResidual F f) (familyResidual F f)) +
        (quaternionHaar n (polyMul (familyProject F f) (familyProject F f)) +
          -(quaternionHaar n (polyMul (familyProject F f)
            (productMap n w K (List.range n) (familyProject F f))))) := by
  have hs := family_square_decomposition n F hF f
  have hp := productMap_inactive_to_full_pairing n w K ids F hids hF hnot hcover f hf
  exact Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' hs (Q'.neg_eqv_congr _ _ hp))
    (poly_identity_of_normal_eq
      (.add (.add (.var 0) (.var 1)) (.neg (.var 2)))
      (.add (.var 1) (.add (.var 0) (.neg (.var 2)))) (by decide)
      (fun
        | 0 => quaternionHaar n (polyMul (familyProject F f) (familyProject F f))
        | 1 => quaternionHaar n (polyMul (familyResidual F f) (familyResidual F f))
        | _ => quaternionHaar n (polyMul (familyProject F f)
            (productMap n w K (List.range n) (familyProject F f)))))

/-- Actual partial-product estimate. The prefactor is independent of the
number of blocks; the nonnegative inactive residual is explicitly retained. -/
theorem productMap_defect_le_projected_angular (tail : Nat) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q')) (K : Nat)
    (hK : sufficientCutoff w ≤ K) (ids F : List Nat)
    (hids : ∀ i, i ∈ ids → i < tail+1) (hF : ∀ i, i ∈ F → i < tail+1)
    (hnot : ∀ i, i ∈ F → i ∉ ids) (hcover : (F++ids).Perm (List.range (tail+1)))
    (f : RatPoly) (hf : SupportedQuaternionBlocks (tail+1) f) :
    quaternionHaar (tail+1) (polyMul f f) +
      -(quaternionHaar (tail+1) (polyMul f (productMap (tail+1) w K ids f))) ≤
      quaternionHaar (tail+1) (polyMul (familyResidual F f) (familyResidual F f)) +
        (2 * ((1 : Q')-w)) * finSum (fun i => quaternionHaar (tail+1)
          (blockAngularSquare i (familyProject F f))) (tail+1) :=
  Q'.le_trans' _ _ _ (Q'.le_of_eqv
    (productMap_defect_eq_residual_add_full (tail+1) w K ids F hids hF hnot hcover f hf))
    (Q'.add_le_add_left _ _ _
      (productMap_range_defect_le_two_angular tail hw0 hw1 K hK
        (familyProject F f) (familyProject_supported F hf)))

/-- When independence of the COMPLETE input has actually been proved, its
inactive projection is removable and no residual budget is needed. -/
theorem productMap_defect_le_angular_of_independent (tail : Nat) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q')) (K : Nat)
    (hK : sufficientCutoff w ≤ K) (ids F : List Nat)
    (hids : ∀ i, i ∈ ids → i < tail+1) (hF : ∀ i, i ∈ F → i < tail+1)
    (hnot : ∀ i, i ∈ F → i ∉ ids) (hcover : (F++ids).Perm (List.range (tail+1)))
    (f : RatPoly) (hf : SupportedQuaternionBlocks (tail+1) f)
    (hind : ∀ i, i ∈ F → QuaternionBlockIndependent i f) :
    quaternionHaar (tail+1) (polyMul f f) +
      -(quaternionHaar (tail+1) (polyMul f (productMap (tail+1) w K ids f))) ≤
      (2 * ((1 : Q')-w)) * finSum (fun i =>
        quaternionHaar (tail+1) (blockAngularSquare i f)) (tail+1) := by
  have hfix := familyProject_fixed F f hind
  have hm := productMap_congr (tail+1) w K (List.range (tail+1)) hfix
  have hp := Q'.eqv_trans _ _ _
    (productMap_inactive_to_full_pairing (tail+1) w K ids F hids hF hnot hcover f hf)
    (haar_of_coeff (hfix.mul hm))
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.add_eqv_congr' (Q'.eqv_refl _) (Q'.neg_eqv_congr _ _ hp)))
    (productMap_range_defect_le_two_angular tail hw0 hw1 K hK f hf)

end YMGap.Continuum.SU2QuaternionProductHeatInactiveAngularDefect

#print axioms YMGap.Continuum.SU2QuaternionProductHeatInactiveAngularDefect.productMap_defect_eq_residual_add_full
#print axioms YMGap.Continuum.SU2QuaternionProductHeatInactiveAngularDefect.productMap_defect_le_projected_angular
#print axioms YMGap.Continuum.SU2QuaternionProductHeatInactiveAngularDefect.productMap_defect_le_angular_of_independent
