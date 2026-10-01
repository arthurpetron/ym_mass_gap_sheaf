/-
# Signed Taylor identity in the original normalized odd marginal

Rebase the already proved source Taylor formula from q^2 to the actual
odd marginal. The effective remainder is exactly the mixed Taylor remainder
minus the diagonal remainder minus (1-w) times the angular weight defect.
All three signed terms share the original partition. No source derivative,
terminal factor, cross term or change-of-weight correction is discarded.

The concrete padded signed family is included. This is an exact finite
identity, not a bound on the remainder relative to interacting variance,
not a continuum limit, and not a new conditional survival wrapper.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialAngularMarginal
import YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFringeIndependent
import YMGap.Continuum.BF4WilsonPlaquetteFamilyIncrement

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialMarginalTaylor

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionAngularReindex
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionCyclicModeTaylor (pairRemainder)
open YMGap.Continuum.SU2QuaternionProductHeatAngularTaylor (weightedAngularEnergy)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks baseLinks_mem_iff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFlow (fringeBlocks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
  (terminalMessage terminalMessage_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialProjectedSourceEnergy (projectedEndpointSource)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm (energy)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow
  (normalizedEnergy oddMass oddMass_positive)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSourceTaylor (energy_taylor_angular)
open YMGap.Continuum.BF4ExactSlabFixedSpatialAngularMarginal
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBaseInclusion (spatialFaces_mono)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFringeIndependent
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteFamilySchedule
  (spatialSpan spatialSpan_supported)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4WilsonPlaquetteFamilySourcePin (familyExpression)
open YMGap.Continuum.BF4WilsonPlaquetteFamilyIncrement (finite_family_increment_pin)
open YMGap.Continuum.BF4WilsonAllNomeZeroRadiusIncrement (squareAt)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowTimeLimit (originalWindowScalar)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] baseLinks terminalMessage projectedEndpointSource
  marginalAngular angularWeightDefect originalWindowScalar

/-- All signed remainders after moving the leading term to the actual
odd marginal. Its size and sign are NOT assumed or proved. -/
def signedRemainder (w : Q') (K width n : Nat) (f : RatPoly) : Q' :=
  let q := projectedEndpointSource w K width (terminalMessage w K width n)
  (pairRemainder (N width-1) w K q (polyMul q (polyMul f f)) +
    -(pairRemainder (N width-1) w K (polyMul q f) (polyMul q f))) +
    -(((1 : Q')-w)*angularWeightDefect w K width n f)

/-- The leading angular term is now under V*g_n*g_(n+1), not q^2. -/
theorem energy_taylor_marginal (w : Q') (K width n : Nat) (f : RatPoly)
    (hf : SupportedQuaternionBlocks (N width) f) (hb : 0 < N width)
    (hind : ∀ j, j ∈ fringeBlocks width → QuaternionBlockIndependent j f) :
    energy w K width (terminalMessage w K width n) f ≈
      ((1 : Q')-w)*marginalAngular w K width n f + signedRemainder w K width n f := by
  let q := projectedEndpointSource w K width (terminalMessage w K width n)
  let a := weightedAngularEnergy (N width-1) q f
  let d := angularWeightDefect w K width n f
  let r := pairRemainder (N width-1) w K q (polyMul q (polyMul f f)) +
    -(pairRemainder (N width-1) w K (polyMul q f) (polyMul q f))
  have h := energy_taylor_angular w K width (terminalMessage w K width n) f
    (terminalMessage_supported w K width n) hf hb hind
  have halg : ((1 : Q')-w)*a+r ≈
      ((1 : Q')-w)*(a+d)+(r+ -(((1 : Q')-w)*d)) :=
    poly_identity_of_normal_eq
      (.add (.mul (.var 0) (.var 1)) (.var 3))
      (.add (.mul (.var 0) (.add (.var 1) (.var 2)))
        (.add (.var 3) (.neg (.mul (.var 0) (.var 2))))) (by decide)
      (fun | 0 => (1 : Q')-w | 1 => a | 2 => d | _ => r)
  exact Q'.eqv_trans _ _ _ h (Q'.eqv_trans _ _ _ halg
    (Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_left _ _ _ (angular_weight_identity w K width n f hf hb hind))
      (Q'.eqv_refl _)))

/-- Normalize BOTH the marginal angular cost and the complete signed
remainder by the same original odd-chain partition. -/
def normalizedAngular {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) (f : RatPoly) : Q' :=
  marginalAngular w K width n f *
    Q'.recipPos (oddMass w K width n) (oddMass_positive hw0 hw1 K width hK n)

def normalizedRemainder {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) (f : RatPoly) : Q' :=
  signedRemainder w K width n f *
    Q'.recipPos (oddMass w K width n) (oddMass_positive hw0 hw1 K width hK n)

theorem normalizedEnergy_taylor {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) (f : RatPoly)
    (hf : SupportedQuaternionBlocks (N width) f) (hb : 0 < N width)
    (hind : ∀ j, j ∈ fringeBlocks width → QuaternionBlockIndependent j f) :
    normalizedEnergy hw0 hw1 K width hK n f ≈
      ((1 : Q')-w)*normalizedAngular hw0 hw1 K width hK n f +
        normalizedRemainder hw0 hw1 K width hK n f :=
  Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ (energy_taylor_marginal w K width n f hf hb hind))
    (Q'.eqv_trans _ _ _ (Q'.add_mul_eqv _ _ _)
      (Q'.add_eqv_congr' (Q'.mul_assoc_eqv _ _ _) (Q'.eqv_refl _)))

private theorem baseLinks_positive (width : Nat) : 0 < N width := by
  have h : ((0,0,0,0),Dir4.x0) ∈ baseLinks width :=
    (baseLinks_mem_iff width _).mpr
      ⟨by decide, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, rfl⟩
  exact Nat.lt_of_le_of_lt (Nat.zero_le _) (List.idxOf_lt_length_of_mem h)

/-- Strict padding discharges every locality condition for the entire signed
family, with arbitrary coefficients, repetitions and no termwise bounds. -/
theorem padded_family_normalized_taylor {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K : Nat) {base width : Nat}
    (hwidth : base < width) (hK : headCutoff w ≤ K) (n : Nat)
    (qs : List Z4Plaq) (c : Z4Plaq → Q')
    (hqs : ∀ p, p ∈ qs → p ∈ spatialFaces base) :
    normalizedEnergy hw0 hw1 K width hK n (spatialSpan width c qs) ≈
      ((1 : Q')-w)*normalizedAngular hw0 hw1 K width hK n (spatialSpan width c qs) +
        normalizedRemainder hw0 hw1 K width hK n (spatialSpan width c qs) :=
  normalizedEnergy_taylor hw0 hw1 K width hK n (spatialSpan width c qs)
    (spatialSpan_supported width c qs) (baseLinks_positive width)
    (spatialSpan_fringe_independent_after_padding hwidth c qs hqs)

/-- Exact consumer on the EXISTING finite Wilson window and its original
cutoff/depth schedule. Both signs and the shared original partition survive. -/
theorem finite_family_increment_taylor {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {base width : Nat}
    (hwidth : base < width) (qs : List Z4Plaq) (c : Z4Plaq → Q')
    (hqs : ∀ p, p ∈ qs → p ∈ spatialFaces base) (stage depth : Nat) :
    originalWindowScalar hw0 hw1 1
        (squareAt (familyExpression width qs c
          (fun p hp => spatialFaces_mono (Nat.le_of_lt hwidth) (hqs p hp))) 1)
        stage depth depth ≈
      2*(((1 : Q')-w)*normalizedAngular hw0 hw1 (headCutoff w+stage) width
          (Nat.le_add_right _ _) depth (spatialSpan width c qs) +
        normalizedRemainder hw0 hw1 (headCutoff w+stage) width
          (Nat.le_add_right _ _) depth (spatialSpan width c qs)) :=
  Q'.eqv_trans _ _ _
    (finite_family_increment_pin hw0 hw1 width qs c
      (fun p hp => spatialFaces_mono (Nat.le_of_lt hwidth) (hqs p hp)) stage depth)
    (Q'.mul_eqv_congr_left _ _ _
      (padded_family_normalized_taylor hw0 hw1 _ hwidth (Nat.le_add_right _ _)
        depth qs c hqs))

#print axioms signedRemainder
#print axioms energy_taylor_marginal
#print axioms normalizedAngular
#print axioms normalizedRemainder
#print axioms normalizedEnergy_taylor
#print axioms baseLinks_positive
#print axioms padded_family_normalized_taylor
#print axioms finite_family_increment_taylor

end YMGap.Continuum.BF4ExactSlabFixedSpatialMarginalTaylor
