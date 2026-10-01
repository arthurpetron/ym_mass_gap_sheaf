/-
# A quantitative negative square in the whole original signed family ceiling

The angular Gram certificate retains 48 times the square of the ORIGINAL
projected source times the whole observable. The actual Casimir-12 geometry
supplies its eigenpin, even for signed coefficients and repeated faces.
The original odd partition, mean, cubic/cutoff debt and both interacting
corrections remain unchanged. No useful scaling-relative rate is claimed.
-/

import YMGap.Continuum.SU2QuaternionSecondOrderRetainedSquare
import YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyCurvature
import YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyCasimir

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyRetainedSquare

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHaarFamilyProjection (familyProject_supported)
open YMGap.Continuum.SU2QuaternionCyclicSecondOrder (sourceSecondMoment sourceErrorBudget)
open YMGap.Continuum.SU2QuaternionProductHeatSourceTaylor (sourceFirstOrder)
open YMGap.Continuum.SU2QuaternionSecondOrderRetainedSquare
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks baseLinks_mem_iff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFlow (fringeBlocks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
  (terminalMessage terminalMessage_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialProjectedSourceEnergy (projectedEndpointSource)
open YMGap.Continuum.BF4ExactSlabFixedSpatialAngularMarginal (angularWeightDefect)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyVarianceWard (oddVariance wardResidual)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyVarianceTaylor
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilySecondOrder
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyCurvature
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyCasimir (spatialSpan_casimir)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow
  (normalizedEnergy oddMass oddMass_positive)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteFamilySchedule
  (spatialSpan spatialSpan_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBaseInclusion (spatialFaces_mono)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] baseLinks terminalMessage projectedEndpointSource
  angularWeightDefect wardResidual

private theorem baseLinks_positive (width : Nat) : 0 < N width := by
  have h : ((0,0,0,0),Dir4.x0) ∈ baseLinks width :=
    (baseLinks_mem_iff width _).mpr
      ⟨by decide, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, rfl⟩
  exact Nat.lt_of_le_of_lt (Nat.zero_le _) (List.idxOf_lt_length_of_mem h)

private theorem projected_supported (w : Q') (K width n : Nat) :
    SupportedQuaternionBlocks (N width)
      (projectedEndpointSource w K width (terminalMessage w K width n)) := by
  unfold projectedEndpointSource
  exact familyProject_supported (fringeBlocks width)
    (supported_polyMul (spatialWeight_supported w K width)
      (terminalMessage_supported w K width n))

/-- Computed square of the SAME projected terminal source and entire observable. -/
def projectedObservableSquare (w : Q') (K width n : Nat) (f : RatPoly) : Q' :=
  let q := projectedEndpointSource w K width (terminalMessage w K width n)
  quaternionHaar (N width) (polyMul (polyMul q f) (polyMul q f))

theorem projectedObservableSquare_nonnegative (w : Q') (K width n : Nat)
    (f : RatPoly) (hf : SupportedQuaternionBlocks (N width) f) :
    (0 : Q') ≤ projectedObservableSquare w K width n f :=
  (Certificate.square _ (supported_polyMul (projected_supported w K width n) hf)).haar_nonnegative

/-- The literal geometric eigenpin supplies all inputs to the retained square.
All signed and repeated-family terms remain inside the one source square. -/
theorem quadraticCoefficient_family_le_retained (w : Q') (K width n : Nat)
    (qs : List Z4Plaq) (c : Z4Plaq → Q')
    (hqs : ∀ p, p ∈ qs → p ∈ spatialFaces width) :
    let f := spatialSpan width c qs
    let q := projectedEndpointSource w K width (terminalMessage w K width n)
    quadraticCoefficient w K width n f ≤
      -curvatureMoment w K width n f - 48*projectedObservableSquare w K width n f +
        sourceFirstOrder (N width-1) q f := by
  dsimp only
  let f := spatialSpan width c qs
  let q := projectedEndpointSource w K width (terminalMessage w K width n)
  have hN : N width-1+1 = N width := Nat.sub_add_cancel (baseLinks_positive width)
  have hq : SupportedQuaternionBlocks (N width-1+1) q := by
    simpa only [hN] using projected_supported w K width n
  have hf : SupportedQuaternionBlocks (N width-1+1) f := by
    simpa only [hN] using spatialSpan_supported width c qs
  have hCf := spatialSpan_casimir width c qs hqs
  have h : sourceSecondMoment (N width-1) q f ≤
      -curvatureMoment w K width n f - 48*projectedObservableSquare w K width n f := by
    simpa only [hN, curvatureMoment, projectedObservableSquare, q, f] using
      sourceSecondMoment_le_retainedSquare (N width-1) q f hq hf
        (by simpa only [hN, f] using hCf)
  exact Q'.add_le_add_right _ _ (sourceFirstOrder (N width-1) q f) h

/-- Original complete numerator with a PROVED quantitative negative-square gain. -/
def retainedVarianceCeiling {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) (f : RatPoly) : Q' :=
  let q := projectedEndpointSource w K width (terminalMessage w K width n)
  ((HalfPow.half*(((1 : Q')-w)*((1 : Q')-w))) *
      (-curvatureMoment w K width n f - 48*projectedObservableSquare w K width n f +
        sourceFirstOrder (N width-1) q f) +
    sourceErrorBudget (N width-1) w K q f -
    ((1 : Q')-w)*angularWeightDefect w K width n f -
    ((1 : Q')-w)*wardResidual hw0 hw1 K width hK n f) *
    Q'.recipPos (oddMass w K width n) (oddMass_positive hw0 hw1 K width hK n)

/-- Exact improvement, paid under the unchanged original partition. -/
theorem retainedVarianceCeiling_gain {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) (f : RatPoly) :
    retainedVarianceCeiling hw0 hw1 K width hK n f ≈
      curvatureVarianceCeiling hw0 hw1 K width hK n f -
        ((HalfPow.half*(((1 : Q')-w)*((1 : Q')-w)))*
          (48*projectedObservableSquare w K width n f))*
          Q'.recipPos (oddMass w K width n) (oddMass_positive hw0 hw1 K width hK n) :=
  poly_identity_of_normal_eq
    (.mul
      (.add (.add (.add
        (.mul (.var 0) (.add (.add (.neg (.var 1)) (.neg (.mul (.const 48) (.var 2)))) (.var 3)))
        (.var 4)) (.neg (.var 5))) (.neg (.var 6))) (.var 7))
    (.add
      (.mul (.add (.add (.add
        (.mul (.var 0) (.add (.neg (.var 1)) (.var 3))) (.var 4))
        (.neg (.var 5))) (.neg (.var 6))) (.var 7))
      (.neg (.mul (.mul (.var 0) (.mul (.const 48) (.var 2))) (.var 7))))
    (by decide) (fun
      | 0 => HalfPow.half*(((1 : Q')-w)*((1 : Q')-w))
      | 1 => curvatureMoment w K width n f
      | 2 => projectedObservableSquare w K width n f
      | 3 => sourceFirstOrder (N width-1)
          (projectedEndpointSource w K width (terminalMessage w K width n)) f
      | 4 => sourceErrorBudget (N width-1) w K
          (projectedEndpointSource w K width (terminalMessage w K width n)) f
      | 5 => ((1 : Q')-w)*angularWeightDefect w K width n f
      | 6 => ((1 : Q')-w)*wardResidual hw0 hw1 K width hK n f
      | _ => Q'.recipPos (oddMass w K width n) (oddMass_positive hw0 hw1 K width hK n))

/-- The computed gain is nonnegative. It need not be strictly positive. -/
theorem retainedVarianceCeiling_le_curvature {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) (f : RatPoly)
    (hf : SupportedQuaternionBlocks (N width) f) :
    retainedVarianceCeiling hw0 hw1 K width hK n f ≤
      curvatureVarianceCeiling hw0 hw1 K width hK n f := by
  let ceiling := curvatureVarianceCeiling hw0 hw1 K width hK n f
  let payment := ((HalfPow.half*(((1 : Q')-w)*((1 : Q')-w)))*
    (48*projectedObservableSquare w K width n f))*
    Q'.recipPos (oddMass w K width n) (oddMass_positive hw0 hw1 K width hK n)
  have hh := Q'.sub_nonneg_of_le (Q'.le_of_lt hw1)
  have hpayment : (0 : Q') ≤ payment :=
    Q'.mul_nonneg _ _
      (Q'.mul_nonneg _ _
        (Q'.mul_nonneg _ _ HalfPow.half_nonneg (Q'.mul_nonneg _ _ hh hh))
        (Q'.mul_nonneg _ _ (by decide)
          (projectedObservableSquare_nonnegative w K width n f hf)))
      (Q'.le_of_lt (Q'.recipPos_pos _ _))
  have h := Q'.add_le_add_left ceiling _ _ (Q'.neg_le_neg hpayment)
  have hzero : ceiling + -(0 : Q') ≈ ceiling :=
    poly_identity_of_normal_eq (.add (.var 0) (.neg (.const 0)))
      (.var 0) (by decide) (fun _ => ceiling)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv
    (retainedVarianceCeiling_gain hw0 hw1 K width hK n f))
    (Q'.le_trans' _ _ _ h (Q'.le_of_eqv hzero))

theorem secondOrderVarianceCeiling_family_le_retained {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat)
    (qs : List Z4Plaq) (c : Z4Plaq → Q')
    (hqs : ∀ p, p ∈ qs → p ∈ spatialFaces width) :
    secondOrderVarianceCeiling hw0 hw1 K width hK n (spatialSpan width c qs) ≤
      retainedVarianceCeiling hw0 hw1 K width hK n (spatialSpan width c qs) := by
  let f := spatialSpan width c qs
  let q := projectedEndpointSource w K width (terminalMessage w K width n)
  have hh := Q'.sub_nonneg_of_le (Q'.le_of_lt hw1)
  have hc : (0 : Q') ≤ HalfPow.half*(((1 : Q')-w)*((1 : Q')-w)) :=
    Q'.mul_nonneg _ _ HalfPow.half_nonneg (Q'.mul_nonneg _ _ hh hh)
  have hquad := Q'.mul_le_mul_of_nonneg_left _ _ _
    (quadraticCoefficient_family_le_retained w K width n qs c hqs) hc
  have hraw := Q'.add_le_add_right _ _
    (-(((1 : Q')-w)*wardResidual hw0 hw1 K width hK n f))
    (Q'.add_le_add_right _ _ (-(((1 : Q')-w)*angularWeightDefect w K width n f))
      (Q'.add_le_add_right _ _ (sourceErrorBudget (N width-1) w K q f) hquad))
  exact Q'.mul_le_mul_of_nonneg_right _ _ _ hraw
    (Q'.le_of_lt (Q'.recipPos_pos _ _))

/-- Concrete SAME-variance consumer. The negative-square gain is supplied;
its scaling comparison with the other signed terms is still open. -/
theorem padded_family_energy_le_retained {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K : Nat) {base width : Nat}
    (hwidth : base < width) (hK : headCutoff w ≤ K) (n : Nat)
    (qs : List Z4Plaq) (c : Z4Plaq → Q')
    (hqs : ∀ p, p ∈ qs → p ∈ spatialFaces base) :
    normalizedEnergy hw0 hw1 K width hK n (spatialSpan width c qs) ≤
      12*(((1 : Q')-w)*oddVariance hw0 hw1 K width hK n (spatialSpan width c qs)) +
        retainedVarianceCeiling hw0 hw1 K width hK n (spatialSpan width c qs) :=
  Q'.le_trans' _ _ _
    (Q'.le_of_eqv (padded_family_energy_variance hw0 hw1 K hwidth hK n qs c hqs))
    (Q'.add_le_add_left _ _ _
      (Q'.le_trans' _ _ _
        (varianceRemainder_le_secondOrder hw0 hw1 K width hK n (spatialSpan width c qs))
        (secondOrderVarianceCeiling_family_le_retained hw0 hw1 K width hK n qs c
          (fun p hp => spatialFaces_mono (Nat.le_of_lt hwidth) (hqs p hp)))))

#print axioms projectedObservableSquare
#print axioms projectedObservableSquare_nonnegative
#print axioms quadraticCoefficient_family_le_retained
#print axioms retainedVarianceCeiling
#print axioms retainedVarianceCeiling_gain
#print axioms retainedVarianceCeiling_le_curvature
#print axioms secondOrderVarianceCeiling_family_le_retained
#print axioms padded_family_energy_le_retained

end YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyRetainedSquare
