/-
# Actual projected-source first order versus the SAME interacting variance

The original terminal recursion supplies source cap and marginal floor with
the SAME predecessor mass squared. Bare Haar mean zero and the literal
Casimir-12 identity then compare the whole signed family's first-order energy
to its original centered interacting variance. No source, predecessor mass,
or variance is inverted. Only the explicit positive floor coefficient is
inverted in the final optional scalar form.

The coefficients depend on nome and the FULL spatial width. They are independent
of late cutoff and positive terminal depth, not physical scaling constants.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalSourceBounds
import YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyBareHaar
import YMGap.Continuum.BF4ExactSlabFixedSpatialSourceVarianceGram
import YMGap.Continuum.BF4ExactSlabFixedSpatialCentralDensityFloor
import YMGap.Continuum.QuaternionHaarIntervalSecondMoment
import YMGap.Continuum.QuaternionHaarPositiveFloorCancellation

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialFamilySourceVarianceBound

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionActiveCasimirProduct
open YMGap.Continuum.SU2QuaternionHaarFamilyProjection (familyProject_supported)
open YMGap.Continuum.SU2QuaternionProductHeatSourceTaylor (sourceFirstOrder)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarIntervalSecondMoment
open YMGap.Continuum.QuaternionHaarPositiveFloorCancellation (floor_insertion)
open YMGap.Continuum.QuaternionHaarDensityVariance
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat
  (spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFlow (fringeBlocks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich
  (kineticFloor kineticFloor_positive kineticCap)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferMixingRate (kineticCap_positive)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCentralDensity
  (spatialFloor spatialCeiling)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCentralDensityFloor
  (spatialCeiling_positive)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
  (terminalMessage terminalMessage_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalDual
  (marginalWeight marginalCertificate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialProjectedSourceEnergy
  (projectedEndpointSource)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyVarianceWard
  (oddVariance marginalMass_positive marginalMass_pin marginalVariance_pin)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSourceVarianceGram
  (oddCentered oddCentered_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow (oddMass)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteFamilySchedule
  (spatialSpan spatialSpan_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
  (headCutoff headFloor_positive)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalSourceBounds
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyBareHaar

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
local notation:max "H" blocks:arg => quaternionHaar blocks
attribute [local irreducible] baseLinks terminalMessage projectedEndpointSource
  predecessorMass

/-- Two spatial floors and three kinetic floors; depends only on nome/width. -/
def sourceFloorScale (w : Q') (width : Nat) : Q' :=
  (spatialFloor w width * spatialFloor w width) *
    ((kineticFloor w width * kineticFloor w width) * kineticFloor w width)

/-- Squared source cap coefficient, with NO cutoff or depth argument. -/
def sourceCapScale (w : Q') (width : Nat) : Q' :=
  (spatialCeiling w width * kineticCap w width) *
    (spatialCeiling w width * kineticCap w width)

theorem sourceFloorScale_positive {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (width : Nat) :
    (0 : Q') < sourceFloorScale w width := by
  have hv : (0 : Q') < spatialFloor w width :=
    HKPos.pow_pos (headFloor_positive hw0 hw1) _
  have hk := kineticFloor_positive hw0 hw1 width
  exact Q'.mul_pos (Q'.mul_pos hv hv) (Q'.mul_pos (Q'.mul_pos hk hk) hk)

theorem sourceCapScale_positive {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (width : Nat) :
    (0 : Q') < sourceCapScale w width := by
  have h := Q'.mul_pos (spatialCeiling_positive hw0 hw1 width)
    (kineticCap_positive hw0 hw1 width)
  exact Q'.mul_pos h h

private theorem cap_square_factor (v k m : Q') :
    (v*(k*m))*(v*(k*m)) ≈ ((v*k)*(v*k))*(m*m) :=
  poly_identity_of_normal_eq
    (.mul (.mul (.var 0) (.mul (.var 1) (.var 2)))
      (.mul (.var 0) (.mul (.var 1) (.var 2))))
    (.mul (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1)))
      (.mul (.var 2) (.var 2)))
    (by decide) (fun | 0 => v | 1 => k | _ => m)

private theorem projectedCap_square_factor (w : Q') (K width n : Nat) :
    projectedCap w K width n * projectedCap w K width n ≈
      sourceCapScale w width *
        (predecessorMass w K width n * predecessorMass w K width n) :=
  cap_square_factor (spatialCeiling w width) (kineticCap w width)
    (predecessorMass w K width n)

private theorem haar_neg (blocks : Nat) : ∀ p : RatPoly,
    H blocks (polyNeg p) ≈ -(H blocks p)
  | [] => by change (0 : Q') ≈ -0; decide
  | t::rest => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.neg_mul_eqv t.2 (quaternionHaarMono blocks t.1))
        (haar_neg blocks rest))
      (Q'.eqv_symm (Q'.neg_add_eqv_split _ _))

private theorem ceiling_insertion {blocks : Nat} {m p : RatPoly} {u : Q'}
    (P : Certificate blocks p)
    (U : Certificate blocks (polyAdd (cap u) (polyNeg m))) :
    H blocks (polyMul m p) ≤ u * H blocks p := by
  have hn := (U.mul P).haar_nonnegative
  have hc : H blocks (polyMul (cap u) p) ≈ u * H blocks p :=
    Q'.eqv_trans _ _ _ (haar_of_coeff (cap_mul_left u p))
      (quaternionHaar_polySmul blocks u p)
  have he : H blocks (polyMul (polyAdd (cap u) (polyNeg m)) p) ≈
      u * H blocks p + -(H blocks (polyMul m p)) :=
    Q'.eqv_trans _ _ _
      (haar_of_coeff (coeffEvalExpr_eqv_of_normalize_eq
        (.mul (.add (.var 0) (.neg (.var 1))) (.var 2))
        (.add (.mul (.var 0) (.var 2)) (.neg (.mul (.var 1) (.var 2))))
        (by decide) (fun | 0 => cap u | 1 => m | _ => p)))
      (Q'.eqv_trans _ _ _ (quaternionHaar_append blocks _ _)
        (Q'.add_eqv_congr' hc (haar_neg blocks _)))
  exact Q'.le_of_sub_nonneg (Q'.le_trans' _ _ _ hn (Q'.le_of_eqv he))

/-- The centered squared insertion of the ORIGINAL W, without a fringe
independence hypothesis: the center is its own original normalized mean. -/
theorem marginal_centered_square {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (K width : Nat) (hK : headCutoff w ≤ K)
    (depth : Nat) {f : RatPoly} (hf : SupportedQuaternionBlocks (N width) f) :
    let psi := oddCentered hw0 hw1 K width hK depth f
    H (N width) (polyMul (marginalWeight w K width depth) (polyMul psi psi)) ≈
      oddMass w K width depth * oddVariance hw0 hw1 K width hK depth f := by
  dsimp only
  let z := H (N width) (marginalWeight w K width depth)
  let hz := marginalMass_positive hw0 hw1 K width hK depth
  let a := Q'.recipPos z hz
  let psi := oddCentered hw0 hw1 K width hK depth f
  let A := H (N width) (polyMul (marginalWeight w K width depth) (polyMul psi psi))
  let v := oddVariance hw0 hw1 K width hK depth f
  have hown : A*a ≈ v := Q'.eqv_trans _ _ _
    (own_mean_pin (marginalCertificate hw0 hw1 K width hK depth) hf hz)
    (marginalVariance_pin hw0 hw1 K width hK depth f)
  have hcancel : (A*a)*z ≈ A :=
    Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv A a z)
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left A _ _ (Q'.mul_comm_eqv a z))
        (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left A _ _ (Q'.mul_recipPos_eqv z hz))
          (Q'.mul_one_eqv A)))
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm hcancel)
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ z hown)
      (Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv v z)
        (Q'.mul_eqv_congr_right _ _ v (marginalMass_pin w K width depth))))

/-- Actual projected first order bounded by its matching bare-Haar square.
The source depth is exactly `n+1`; the previous original mass remains explicit. -/
theorem family_firstOrder_le_bare {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat)
    (c : Z4Plaq → Q') (qs : List Z4Plaq)
    (hqs : ∀ p, p ∈ qs → p ∈ spatialFaces width) :
    let f := spatialSpan width c qs
    let q := projectedEndpointSource w K width (terminalMessage w K width (n+1))
    sourceFirstOrder (N width-1) q f ≤
      (sourceCapScale w width * (predecessorMass w K width n * predecessorMass w K width n)) *
        (12 * H (N width) (polyMul f f)) := by
  dsimp only
  let f := spatialSpan width c qs
  let q := projectedEndpointSource w K width (terminalMessage w K width (n+1))
  let u := projectedCap w K width n
  have hq : SupportedQuaternionBlocks (N width) q := by
    unfold q projectedEndpointSource
    exact familyProject_supported _ (supported_polyMul (spatialWeight_supported w K width)
      (terminalMessage_supported w K width (n+1)))
  have hu : (0 : Q') ≤ u := Q'.le_of_lt
    (Q'.mul_pos (spatialCeiling_positive hw0 hw1 width)
      (Q'.mul_pos (kineticCap_positive hw0 hw1 width)
        (predecessorMass_positive hw0 hw1 K width hK n)))
  let I : Interval (N width) q u :=
    ⟨hq, hu, projectedSource_upperCertificate hw0 hw1 K width hK n,
      (Certificate.constant (N width) u hu).add
        (projectedSource_certificate hw0 hw1 K width hK n)⟩
  have hb := ceiling_insertion
    (activeGamma_squareCertificate (List.range (N width))
      (fun i hi => List.mem_range.mp hi) (spatialSpan_supported width c qs))
    (YMGap.Continuum.QuaternionHaarIntervalSecondMoment.Interval.squareBound I).certificate
  have hp := family_sourceFirstOrder_gamma w K width (n+1) c qs
  have he := Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ (projectedCap_square_factor w K width n))
    (Q'.mul_eqv_congr_left _ _ _ (family_gamma_square width c qs hqs))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hp)
    (Q'.le_trans' _ _ _ hb (Q'.le_of_eqv he))

/-- Lower comparison with the actual mean and unchanged odd partition. -/
theorem family_variance_bare_floor {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat)
    (c : Z4Plaq → Q') (qs : List Z4Plaq)
    (hqs : ∀ p, p ∈ qs → p ∈ spatialFaces width) :
    let f := spatialSpan width c qs
    (sourceFloorScale w width * (predecessorMass w K width n * predecessorMass w K width n)) *
        H (N width) (polyMul f f) ≤
      oddMass w K width (n+1) * oddVariance hw0 hw1 K width hK (n+1) f := by
  dsimp only
  let f := spatialSpan width c qs
  let psi := oddCentered hw0 hw1 K width hK (n+1) f
  let ell := marginalFloor w K width n
  have hfactor : ell ≈ sourceFloorScale w width *
      (predecessorMass w K width n * predecessorMass w K width n) :=
    marginalFloor_factor w K width n
  have hm := predecessorMass_positive hw0 hw1 K width hK n
  have hell : (0 : Q') ≤ ell := Q'.le_trans' _ _ _
    (Q'.le_of_lt (Q'.mul_pos (sourceFloorScale_positive hw0 hw1 width)
      (Q'.mul_pos hm hm))) (Q'.ge_of_eqv hfactor)
  have hshift := Q'.mul_le_mul_of_nonneg_left _ _ ell
    (family_shifted_square_ge width c qs hqs
      (normalizedMoment (N width) (marginalWeight w K width (n+1)) f
        (marginalMass_positive hw0 hw1 K width hK (n+1)))) hell
  have hfloor := floor_insertion
    (Certificate.square psi (oddCentered_supported hw0 hw1 K width hK (n+1)
      (spatialSpan_supported width c qs)))
    (marginalWeight_lowerCertificate hw0 hw1 K width hK n)
  have hpin := Q'.eqv_trans _ _ _
    (haar_of_coeff (RatPolyCoeffEqv.mul_comm (polyMul psi psi) _))
    (marginal_centered_square hw0 hw1 K width hK (n+1)
      (spatialSpan_supported width c qs))
  exact Q'.le_trans' _ _ _
    (Q'.ge_of_eqv (Q'.mul_eqv_congr_right _ _ _ hfactor))
    (Q'.le_trans' _ _ _ hshift (Q'.le_trans' _ _ _ hfloor (Q'.le_of_eqv hpin)))

/-- Cleared actual-source comparison. The common predecessor square disappears
by scaled substitution, NOT by division; every zero-observable case remains. -/
theorem family_firstOrder_variance_cleared {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat)
    (c : Z4Plaq → Q') (qs : List Z4Plaq)
    (hqs : ∀ p, p ∈ qs → p ∈ spatialFaces width) :
    let f := spatialSpan width c qs
    let q := projectedEndpointSource w K width (terminalMessage w K width (n+1))
    sourceFloorScale w width * sourceFirstOrder (N width-1) q f ≤
      (12*sourceCapScale w width) *
        (oddMass w K width (n+1) * oddVariance hw0 hw1 K width hK (n+1) f) := by
  dsimp only
  let L := sourceFloorScale w width
  let U := sourceCapScale w width
  let M := predecessorMass w K width n * predecessorMass w K width n
  let F := H (N width) (polyMul (spatialSpan width c qs) (spatialSpan width c qs))
  have ha := Q'.mul_le_mul_of_nonneg_left _ _ L
    (family_firstOrder_le_bare hw0 hw1 K width hK n c qs hqs)
    (Q'.le_of_lt (sourceFloorScale_positive hw0 hw1 width))
  have hv := Q'.mul_le_mul_of_nonneg_left _ _ (12*U)
    (family_variance_bare_floor hw0 hw1 K width hK n c qs hqs)
    (Q'.le_of_lt (Q'.mul_pos (by decide : (0 : Q') < 12)
      (sourceCapScale_positive hw0 hw1 width)))
  have he : L*((U*M)*(12*F)) ≈ (12*U)*((L*M)*F) :=
    poly_identity_of_normal_eq
      (.mul (.var 0) (.mul (.mul (.var 1) (.var 2)) (.mul (.const 12) (.var 3))))
      (.mul (.mul (.const 12) (.var 1)) (.mul (.mul (.var 0) (.var 2)) (.var 3)))
      (by decide) (fun | 0 => L | 1 => U | 2 => M | _ => F)
  exact Q'.le_trans' _ _ _ ha (Q'.le_trans' _ _ _ (Q'.le_of_eqv he) hv)

/-- Computed variance coefficient depending explicitly only on nome and width. -/
def firstOrderVarianceConstant {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (width : Nat) : Q' :=
  (12*sourceCapScale w width) *
    Q'.recipPos (sourceFloorScale w width) (sourceFloorScale_positive hw0 hw1 width)

theorem firstOrderVarianceConstant_positive {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (width : Nat) :
    (0 : Q') < firstOrderVarianceConstant hw0 hw1 width :=
  Q'.mul_pos (Q'.mul_pos (by decide) (sourceCapScale_positive hw0 hw1 width))
    (Q'.recipPos_pos _ _)

/-- No inverse of the observable variance or terminal source is used. -/
theorem family_firstOrder_variance_bound {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat)
    (c : Z4Plaq → Q') (qs : List Z4Plaq)
    (hqs : ∀ p, p ∈ qs → p ∈ spatialFaces width) :
    let f := spatialSpan width c qs
    let q := projectedEndpointSource w K width (terminalMessage w K width (n+1))
    sourceFirstOrder (N width-1) q f ≤
      firstOrderVarianceConstant hw0 hw1 width *
        (oddMass w K width (n+1) * oddVariance hw0 hw1 K width hK (n+1) f) := by
  dsimp only
  let L := sourceFloorScale w width
  let a := Q'.recipPos L (sourceFloorScale_positive hw0 hw1 width)
  let A := sourceFirstOrder (N width-1)
    (projectedEndpointSource w K width (terminalMessage w K width (n+1)))
    (spatialSpan width c qs)
  let S := oddMass w K width (n+1) *
    oddVariance hw0 hw1 K width hK (n+1) (spatialSpan width c qs)
  have h := Q'.mul_le_mul_of_nonneg_right _ _ a
    (family_firstOrder_variance_cleared hw0 hw1 K width hK n c qs hqs)
    (Q'.le_of_lt (Q'.recipPos_pos _ _))
  have hleft : (L*A)*a ≈ A := Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ a (Q'.mul_comm_eqv L A))
    (Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv A L a)
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left A _ _ (Q'.mul_recipPos_eqv L _))
        (Q'.mul_one_eqv A)))
  have hright : ((12*sourceCapScale w width)*S)*a ≈
      firstOrderVarianceConstant hw0 hw1 width*S :=
    poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.var 1)) (.var 2))
      (.mul (.mul (.var 0) (.var 2)) (.var 1)) (by decide)
      (fun | 0 => 12*sourceCapScale w width | 1 => S | _ => a)
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hleft)
    (Q'.le_trans' _ _ _ h (Q'.le_of_eqv hright))

#print axioms sourceFloorScale
#print axioms sourceCapScale
#print axioms sourceFloorScale_positive
#print axioms sourceCapScale_positive
#print axioms marginal_centered_square
#print axioms family_firstOrder_le_bare
#print axioms family_variance_bare_floor
#print axioms family_firstOrder_variance_cleared
#print axioms firstOrderVarianceConstant
#print axioms firstOrderVarianceConstant_positive
#print axioms family_firstOrder_variance_bound

end YMGap.Continuum.BF4ExactSlabFixedSpatialFamilySourceVarianceBound
