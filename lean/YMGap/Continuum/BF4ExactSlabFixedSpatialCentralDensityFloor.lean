/-
# A depth- and cutoff-independent floor for the normalized central density

The original central potential and both terminal messages are retained.
The SAME boundary-mass square in the raw lower/upper bounds cancels before
normalization. The explicit positive fraction depends on nome and spatial
width; it is not a spatial- or spacing-uniform estimate.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialCentralDensity
import YMGap.Continuum.QPolyHaarPositiveSubstitution

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialCentralDensityFloor

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferMixingRate
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialCentralDensity
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4ExactSlabAllNomeTailInterval (prefixCap majorant_prefix_bound)
open YMGap.Continuum.SU2AllLabelPointwiseHeatCorridor (pointwiseHeatMajorant)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QPolyHaarPositiveSubstitution (haar_one)

local notation:max "N" width:arg => List.length (baseLinks width)
local infix:50 " ≈ " => Q'.eqv

private theorem haar_neg (blocks : Nat) : ∀ p : RatPoly,
    quaternionHaar blocks (polyNeg p) ≈ -(quaternionHaar blocks p)
  | [] => by change (0 : Q') ≈ -0; decide
  | t::rest => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.neg_mul_eqv t.2 (quaternionHaarMono blocks t.1)) (haar_neg blocks rest))
      (Q'.eqv_symm (Q'.neg_add_eqv_split _ _))

private theorem haar_cap (blocks : Nat) (c : Q') : quaternionHaar blocks (cap c) ≈ c :=
  Q'.eqv_trans _ _ _ (quaternionHaar_polySmul blocks c polyOne)
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (haar_one blocks)) (Q'.mul_one_eqv c))

private theorem haar_upper {blocks : Nat} {p : RatPoly} {c : Q'}
    (P : Certificate blocks (polyAdd (cap c) (polyNeg p))) : quaternionHaar blocks p ≤ c :=
  Q'.le_of_sub_nonneg (Q'.le_trans' _ _ _ P.haar_nonnegative
    (Q'.le_of_eqv (Q'.eqv_trans _ _ _ (quaternionHaar_append blocks _ _)
      (Q'.add_eqv_congr' (haar_cap blocks c) (haar_neg blocks p)))))

private theorem cap_neg (c : Q') : RatPolyCoeffEqv (polyNeg (cap c)) (cap (-c)) := by
  intro weight
  change (-(c*1)) * weight [] + 0 ≈ ((-c)*1) * weight [] + 0
  exact Q'.add_eqv_congr'
    (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm (Q'.neg_mul_eqv c 1))) (Q'.eqv_refl _)

private def lowerWeaken {blocks : Nat} {p : RatPoly} {a b : Q'} (h : b ≤ a)
    (P : Certificate blocks (polyAdd p (polyNeg (cap a)))) :
    Certificate blocks (polyAdd p (polyNeg (cap b))) :=
  .ofCoeff ((coeffEvalExpr_eqv_of_normalize_eq
    (.add (.var 0) (.neg (.var 2)))
    (.add (.add (.var 0) (.neg (.var 1))) (.add (.var 1) (.neg (.var 2))))
    (by decide) (fun | 0 => p | 1 => cap a | _ => cap b)).trans
      ((RatPolyCoeffEqv.refl _).add
        (((RatPolyCoeffEqv.refl _).add (cap_neg b)).trans (cap_add a (-b)))))
    (P.add (Certificate.constant blocks (a + -b) (Q'.sub_nonneg_of_le h)))

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))

include hw0 hw1

theorem spatialCeiling_positive (width : Nat) : (0 : Q') < spatialCeiling w width := by
  have hfirst : (0 : Q') < RationalTail.finSum (pointwiseHeatMajorant w) 1 := by
    change (0 : Q') < 0 + 1*1
    decide
  exact HKPos.pow_pos (HeatKernelRGStep.lt_of_lt_of_le hfirst (majorant_prefix_bound hw0 hw1 1)) _

theorem densityCeiling_positive (width : Nat) : (0 : Q') < densityCeiling w width :=
  Q'.mul_pos (spatialCeiling_positive hw0 hw1 width)
    (Q'.mul_pos (kineticCap_positive hw0 hw1 width) (kineticCap_positive hw0 hw1 width))

/-- An explicit rational lower comparison, independent of late K and depth. -/
def centralFraction (width : Nat) : Q' :=
  densityFloor w width * Q'.recipPos (densityCeiling w width) (densityCeiling_positive hw0 hw1 width)

theorem centralFraction_positive (width : Nat) : (0 : Q') < centralFraction hw0 hw1 width :=
  Q'.mul_pos (densityFloor_positive hw0 hw1 width)
    (Q'.recipPos_pos _ (densityCeiling_positive hw0 hw1 width))

theorem centralFraction_cancel (width : Nat) :
    centralFraction hw0 hw1 width * densityCeiling w width ≈ densityFloor w width :=
  Q'.eqv_trans _ _ _
    (poly_identity_of_normal_eq (.mul (.mul (.var 0) (.var 1)) (.var 2))
      (.mul (.var 0) (.mul (.var 2) (.var 1))) (by decide)
      (fun | 0 => densityFloor w width
           | 1 => Q'.recipPos (densityCeiling w width) (densityCeiling_positive hw0 hw1 width)
           | _ => densityCeiling w width))
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _
      (Q'.mul_recipPos_eqv _ (densityCeiling_positive hw0 hw1 width))) (Q'.mul_one_eqv _))

theorem centralMass_positive (K width : Nat) (hK : headCutoff w ≤ K) (t : Nat) :
    (0 : Q') < quaternionHaar (N width) (centralDensity w K width t) :=
  terminalPair_positive hw0 hw1 K width hK (t+1) (t+1)

theorem centralMass_upper (K width : Nat) (hK : headCutoff w ≤ K) (t : Nat) :
    quaternionHaar (N width) (centralDensity w K width t) ≤
      densityCeiling w width * (boundaryMass w K width t * boundaryMass w K width t) :=
  haar_upper (centralDensity_upper hw0 hw1 K width hK t)

/-- This certificate is about W minus fraction times its OWN original mass.
It is stronger than a comparison of two unrelated normalized integrals. -/
def centralDensity_normalizedFloor (K width : Nat) (hK : headCutoff w ≤ K) (t : Nat) :
    Certificate (N width) (polyAdd (centralDensity w K width t)
      (polyNeg (cap (centralFraction hw0 hw1 width *
        quaternionHaar (N width) (centralDensity w K width t))))) := by
  have h := Q'.mul_le_mul_of_nonneg_left _ _ (centralFraction hw0 hw1 width)
    (centralMass_upper hw0 hw1 K width hK t) (Q'.le_of_lt (centralFraction_positive hw0 hw1 width))
  have he : centralFraction hw0 hw1 width *
      (densityCeiling w width * (boundaryMass w K width t * boundaryMass w K width t)) ≈
      densityFloor w width * (boundaryMass w K width t * boundaryMass w K width t) :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
      (Q'.mul_eqv_congr_right _ _ _ (centralFraction_cancel hw0 hw1 width))
  exact lowerWeaken (Q'.le_trans' _ _ _ h (Q'.le_of_eqv he))
    (centralDensity_lower hw0 hw1 K width hK t)

end YMGap.Continuum.BF4ExactSlabFixedSpatialCentralDensityFloor

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCentralDensityFloor.spatialCeiling_positive
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCentralDensityFloor.densityCeiling_positive
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCentralDensityFloor.centralFraction
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCentralDensityFloor.centralFraction_positive
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCentralDensityFloor.centralFraction_cancel
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCentralDensityFloor.centralMass_positive
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCentralDensityFloor.centralMass_upper
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCentralDensityFloor.centralDensity_normalizedFloor
