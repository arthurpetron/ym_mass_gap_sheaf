/-
# Literal original-coordinate reciprocal approximants realize the conditional update

The finite polynomial is G_k(project_j A) * project_j(p A), with A the
actual incident action and j the unchanged original physical link index.
Exact Haar-carrier pins identify it with the head-coordinate approximant.
The resulting explicit Cauchy/null data are in the EXISTING full original
action space and identify the limit with its existing conditionalUpdate.

This does not yet pass the two-exterior edge-flow comparison to a limiting
joint pairing, establish coercivity, or give an OS/physical mass gap.
-/

import YMGap.Continuum.BF4ExactSlabStarReciprocalInverse
import YMGap.Continuum.BF4ExactSlabStarReciprocalTransport

namespace YMGap.Continuum.BF4ExactSlabInPlaceReciprocalConditional

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.GNSModulusCompletion
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabLinkStarGeometry
open YMGap.Continuum.BF4ExactSlabStarNormalizer
open YMGap.Continuum.BF4ExactSlabStarBandCertificate
open YMGap.Continuum.BF4ExactSlabCrossExteriorStar
open YMGap.Continuum.BF4ExactSlabStarReciprocalParameters
open YMGap.Continuum.BF4ExactSlabHeadNormalizerBand
open YMGap.Continuum.BF4ExactSlabStarReciprocalTransport
open YMGap.Continuum.BF4ExactSlabStarInverseApproximation
open YMGap.Continuum.BF4ExactSlabStarFullActionProbe
open YMGap.Continuum.BF4ExactSlabStarConditionalProjection
open YMGap.Continuum.BF4ExactSlabStarReciprocalInverse
open YMGap.Continuum.QuaternionHaarPositiveWindowInverse
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz
open YMGap.Continuum.QuaternionHaarAngularCarrier
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionHaarBlockProjection
open YMGap.Continuum.SU2QuaternionHaarBlockCertificate
open YMGap.Continuum.SU2QuaternionHaarHeadProbeTransport
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local notation:max "blocks" extent:arg => List.length (boundaryCompleteSlabLinks extent)
local infix:50 " ≈ " => Q'.eqv

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K extent : Nat) (hK : headCutoff w ≤ K) (link : Z4Link)
  (hl : link ∈ boundaryCompleteSlabLinks extent)

local notation "F" => fullData hw0 hw1 K extent hK
local notation "G" => exteriorData hw0 hw1 K extent hK link hl
local notation "N" => numeratorMap hw0 hw1 K extent hK link hl

def inPlaceNumerator (p : (F).V) : RatPoly :=
  project (slot extent link) (polyMul p.val (incidentHeat w K extent link))

theorem inPlaceNumerator_supported (p : (F).V) :
    SupportedQuaternionBlocks (blocks extent) (inPlaceNumerator hw0 hw1 K extent hK link p) :=
  project_supported _ (supported_polyMul p.property (incidentHeat_supported w K extent link))

/-- The inserted numerator uses the SAME selected original block. -/
theorem numerator_head_pin (p : (F).V) :
    HaarCarrierEqv (blocks extent) (inPlaceNumerator hw0 hw1 K extent hK link p)
      (headProbe (linkHeadSwap extent link hl) (N p).val) :=
  (carrierOfPrefix (headProbe_supported _ _)
    (inPlaceNumerator_supported hw0 hw1 K extent hK link p)
    (restored_prefix _ _ (List.idxOf_lt_length_of_mem hl)
      (polyMul p.val (incidentHeat w K extent link)))).symm

/-- Literal polynomial conditional approximation in the original coordinates. -/
def inPlaceApproximation (p : (F).V) (k : Nat) : (F).V :=
  ⟨polyMul (inPlaceNumerator hw0 hw1 K extent hK link p)
      (reciprocal (inPlaceNormalizer w K extent link) (starUpper w extent link)
        (starUpper_positive hw0 hw1 extent link) k),
    supported_polyMul (inPlaceNumerator_supported hw0 hw1 K extent hK link p)
      (reciprocal_supported (inPlaceNormalizer_supported w K extent link)
        (starUpper w extent link) (starUpper_positive hw0 hw1 extent link) k)⟩

local notation "A" => inPlaceApproximation hw0 hw1 K extent hK link

/-- No replacement of the action or its conditional numerator is involved. -/
theorem approximation_head_pin (p : (F).V) (k : Nat) :
    HaarCarrierEqv (blocks extent) (A p k).val
      (probeMap hw0 hw1 K extent hK link hl
        (reciprocalApproximation hw0 hw1 K extent hK link hl (N p) k)).val := by
  change HaarCarrierEqv _ _
    (headProbe (linkHeadSwap extent link hl)
      (polyMul (N p).val (headReciprocal hw0 hw1 K extent link hl k)))
  rw [headProbe_mul]
  exact HaarCarrierEqv.mul (numerator_head_pin hw0 hw1 K extent hK link hl p)
    (inPlace_headReciprocal_carrier hw0 hw1 K extent link hl k)

private theorem distance_carrier {a b c d : (F).V}
    (ha : HaarCarrierEqv (blocks extent) a.val c.val)
    (hb : HaarCarrierEqv (blocks extent) b.val d.val) :
    (F).distSqQ a b ≈ (F).distSqQ c d := by
  have h : HaarCarrierEqv (blocks extent) ((F).sub a b).val ((F).sub c d).val :=
    HaarCarrierEqv.add ha (HaarCarrierEqv.smul (-1) hb)
  exact haar_of_carrier (HaarCarrierEqv.mul_right
    (polynomialProduct (faceHeatPolynomial w K extent) (slabPhysicalFaceEdges extent))
    (HaarCarrierEqv.mul h h))

local notation "S" p => probeCauchy hw0 hw1 K extent hK link hl
  (reciprocalCauchy hw0 hw1 K extent hK link hl (N p))

/-- Same modulus as the already constructed head/probe sequence; only the
literal polynomial representatives change by proved Haar-carrier equality. -/
def inPlaceCauchy (p : (F).V) : CauchyGNS F where
  seq := A p
  modulus := (S p).modulus
  isCauchy := by
    intro epsilon he i j hi hj
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (distance_carrier hw0 hw1 K extent hK
        (approximation_head_pin hw0 hw1 K extent hK link hl p i)
        (approximation_head_pin hw0 hw1 K extent hK link hl p j)))
      ((S p).isCauchy epsilon he i j hi hj)

/-- Exact equality at every approximant supplies a zero coordinate-change
modulus; no representatives are chosen from a quotient. -/
def headNullModulus (p : (F).V) :
    CauchyNullModulus F (inPlaceCauchy hw0 hw1 K extent hK link hl p) (S p) where
  modulus := fun _ => 0
  close := by
    intro epsilon he k _
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.eqv_trans _ _ _
        (distance_carrier hw0 hw1 K extent hK
          (approximation_head_pin hw0 hw1 K extent hK link hl p k) (.refl _ _))
        ((F).rad_refl ((S p).seq k)))) (Q'.le_of_lt he)

/-- The actual in-place sequence and existing conditionalDenseMap carry a
computed cross-sequence null modulus on the full ORIGINAL action space. -/
def conditionalNull (p : (F).V) :
    CauchyNullModulus F (inPlaceCauchy hw0 hw1 K extent hK link hl p)
      ((conditionalDenseMap hw0 hw1 K extent hK link hl).toRep p) :=
  (headNullModulus hw0 hw1 K extent hK link hl p).trans
    (conditionalNullModulus hw0 hw1 K extent hK link hl p)

theorem inPlace_limit_eq_conditionalUpdate (p : (F).V) :
    Quotient.mk (cauchySetoid F) (inPlaceCauchy hw0 hw1 K extent hK link hl p) =
      conditionalUpdate hw0 hw1 K extent hK link hl p :=
  Quotient.sound (conditionalNull hw0 hw1 K extent hK link hl p).toCauchyNull

#print axioms inPlaceNumerator
#print axioms inPlaceNumerator_supported
#print axioms numerator_head_pin
#print axioms inPlaceApproximation
#print axioms approximation_head_pin
#print axioms inPlaceCauchy
#print axioms headNullModulus
#print axioms conditionalNull
#print axioms inPlace_limit_eq_conditionalUpdate

end YMGap.Continuum.BF4ExactSlabInPlaceReciprocalConditional
