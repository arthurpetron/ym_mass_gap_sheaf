/-
# Concrete local tests and the detached ORIGINAL-action reference

Only the four translated probe crossing faces are selected. All other
crossing faces keep their full Gram trees. The test polynomials are the
actual detached lower heat product Lfar and scalarLoop*Lfar. The full lower
action is still present in both original-law test amplitudes.

Separately, the detached squared background gives an exact four-moment
reference determinant -Zfar^2/128, uniformly as an identity in volume and
cutoff. No equality of this bare local reference with the interacting
whole-forest test minor is asserted. Controlling that difference while
retaining the spectator partition is the open positive-excitation step.
-/

import YMGap.Continuum.BF4ExactSlabBulkProbeHaarReference
import YMGap.Continuum.BF4ExactSlabPartialInterfaceTests
import YMGap.Continuum.BF4ExactSlabPlaquetteHeatDressedMinor
import YMGap.Continuum.BF4ExactSlabThermodynamicBaseCompatibility

namespace YMGap.Continuum.BF4ExactSlabBulkProbeSpectatorTests

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabBulkProbeInterface
open YMGap.Continuum.BF4ExactSlabBulkProbeHaarReference
open YMGap.Continuum.BF4ExactSlabDetachedFaceRegion
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabAllExtentHeatUnit
open YMGap.Continuum.BF4ExactSlabFundamentalRetainedChannels
open YMGap.Continuum.BF4ExactSlabPartialInterfaceRetention
open YMGap.Continuum.BF4ExactSlabPartialInterfaceTests
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabPlaquetteReflectionPositivity
open YMGap.Continuum.BF4ExactSlabPlaquetteFiniteGNS
open YMGap.Continuum.BF4ExactSlabPlaquetteRetainedMinor (recentered)
open YMGap.Continuum.BF4ExactSlabPlaquetteHeatDressedMinor (determinant_congr)
open YMGap.Continuum.ReflectedSquareTreeTwoChannelBound (determinant)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionBlockLocality
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local infix:50 " ≈ " => Q'.eqv
local notation "blocks" half => List.length (boundaryCompleteSlabLinks (centralExtent half))

/-- The probe belongs to the already-used thermodynamic enlargement family,
not merely to an isomorphic finite observable algebra. -/
theorem bulkProbe_enlarge (half : Nat) : bulkProbe (0+half) =
    BF4ExactSlabThermodynamicBaseCompatibility.enlarge half BF4ExactSlabPlaquetteCoordinateChannels.probe := by
  simp only [Nat.zero_add, bulkProbe, BF4ExactSlabThermodynamicBaseCompatibility.enlarge,
    BF4ExactSlabPlaquetteBulkEmbedding.bulkAtTime, BF4ExactSlabPlaquetteCoordinateChannels.probe,
    BF4ExactSlabPlaquetteBulkEmbedding.bulkFaceId, translatedId, Nat.sub_zero]
  rfl

/-- Outer none retains every channel at the untouched original face. -/
def localChoice (half : Nat) (c : CoordinateChoice) (id : Nat) : PartialChoice :=
  if id ∈ crossingIds half then some c else none

theorem localChoice_selected (half : Nat) (c : CoordinateChoice) {id : Nat} (hi : id ∈ crossingIds half) :
    localChoice half c id = some c := if_pos hi

theorem localChoice_spectator (half : Nat) (c : CoordinateChoice) {id : Nat} (hi : id ∉ crossingIds half) :
    localChoice half c id = none := if_neg hi

def spectatorHeat (w : Q') (K half : Nat) : RatPoly :=
  polynomialProduct (faceHeatPolynomial w K (centralExtent half)) (lowerSpectators half)

def collarHeat (w : Q') (K half : Nat) : RatPoly :=
  polynomialProduct (faceHeatPolynomial w K (centralExtent half)) (lowerCollar half)

theorem lowerHeat_split (w : Q') (K half : Nat) :
    RatPolyCoeffEqv (lowerHeatProduct w K half) (polyMul (collarHeat w K half) (spectatorHeat w K half)) :=
  (polynomialProduct_perm _ (lower_partition half).symm).trans (polynomialProduct_append _ _ _)

theorem spectatorHeat_supported (w : Q') (K half : Nat) :
    SupportedQuaternionBlocks (blocks half) (spectatorHeat w K half) := heatProduct_supported w K _ _

theorem spectatorHeat_local (w : Q') (K half : Nat) :
    LinkLocal (centralExtent half) (faceLinks (centralExtent half) (lowerSpectators half)) (spectatorHeat w K half) :=
  heatProduct_local w K _ _

def scalarTest (w : Q') (K half : Nat) : RatPoly := polyMul (bulkScalar half) (spectatorHeat w K half)

variable {w : Q'} (hw : (0 : Q') ≤ w) (K : Nat) (hK : 1 ≤ K) (half : Nat)

def localMinor : Q' := testMinor hw K hK half (localChoice half none) (localChoice half (some (false,false)))
  (spectatorHeat w K half) (scalarTest w K half) (bulkProbe half)

def localReferenceBudget : Q' := referenceBudget hw K hK half
  (localChoice half none) (localChoice half (some (false,false))) (spectatorHeat w K half) (scalarTest w K half)

/-- Concrete tests on the full original lower action, for every centering.
No positive sign or volume-uniform normalized estimate is an input here. -/
theorem localMinor_recentered_bound (c : Q') : localMinor hw K hK half ≤
    rawForm w K (recentered half (bulkProbe half) c) (recentered half (bulkProbe half) c) *
      localReferenceBudget hw K hK half :=
  every_recentered_bound hw K hK half _ _ _ _ _ c

theorem localReferenceBudget_nonnegative : (0 : Q') ≤ localReferenceBudget hw K hK half :=
  referenceBudget_nonnegative hw K hK half _ _ _ _

omit hw hK in
def referenceBackground (w : Q') (K half : Nat) : RatPoly :=
  polyMul (spectatorHeat w K half) (spectatorHeat w K half)

omit hw hK in
theorem referenceBackground_supported (w : Q') (K half : Nat) :
    SupportedQuaternionBlocks (blocks half) (referenceBackground w K half) :=
  supported_polyMul (spectatorHeat_supported w K half) (spectatorHeat_supported w K half)

omit hw hK in
theorem referenceBackground_local (w : Q') (K half : Nat) :
    LinkLocal (centralExtent half) (faceLinks (centralExtent half) (lowerSpectators half)) (referenceBackground w K half) :=
  (spectatorHeat_local w K half).mul (spectatorHeat_local w K half)

omit hw hK in
def referenceMoment (w : Q') (K half : Nat) (p : RatPoly) : Q' :=
  quaternionHaar (blocks half) (polyMul p (referenceBackground w K half))

omit hw hK in
def spectatorMass (w : Q') (K half : Nat) : Q' := quaternionHaar (blocks half) (referenceBackground w K half)

omit hw hK in
theorem reference_probe_zero (w : Q') (K half : Nat) : referenceMoment w K half (lower (bulkProbe half)) ≈ 0 :=
  Q'.eqv_trans _ _ _ (spectator_factor half (lower_supported _) (referenceBackground_supported w K half)
    (bulkProbe_local half) (referenceBackground_local w K half))
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (bulkProbe_haar_zero half)) (RingNormaliser.q_zero_mul _))

omit hw hK in
theorem reference_scalar_zero (w : Q') (K half : Nat) : referenceMoment w K half (bulkScalar half) ≈ 0 :=
  Q'.eqv_trans _ _ _ (spectator_factor half (bulkScalar_supported half) (referenceBackground_supported w K half)
    (bulkScalar_local half) (referenceBackground_local w K half))
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (bulkScalar_haar_zero half)) (RingNormaliser.q_zero_mul _))

omit hw hK in
theorem reference_unit (w : Q') (K half : Nat) : referenceMoment w K half polyOne ≈ spectatorMass w K half :=
  haar_of_coeff_eqv _ (RatPolyCoeffEqv.one_mul _)

omit hw hK in
theorem reference_mixed (w : Q') (K half : Nat) :
    referenceMoment w K half (polyMul (lower (bulkProbe half)) (bulkScalar half)) ≈
      Q'.invSucc 127 * spectatorMass w K half :=
  mixed_spectator_moment half (referenceBackground_supported w K half) (referenceBackground_local w K half)

omit hw hK in
def referenceDeterminant (w : Q') (K half : Nat) : Q' := determinant
  (referenceMoment w K half (lower (bulkProbe half)))
  (referenceMoment w K half (polyMul (lower (bulkProbe half)) (bulkScalar half)))
  (referenceMoment w K half polyOne) (referenceMoment w K half (bulkScalar half))

omit hw hK in
/-- The whole detached squared background survives in the exact reference.
This determinant is deliberately distinct from the interacting localMinor. -/
theorem referenceDeterminant_pin (w : Q') (K half : Nat) :
    referenceDeterminant w K half ≈ -(Q'.invSucc 127 * spectatorMass w K half * spectatorMass w K half) :=
  Q'.eqv_trans _ _ _ (determinant_congr (reference_probe_zero w K half) (reference_mixed w K half)
    (reference_unit w K half) (reference_scalar_zero w K half))
    (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ (by decide : (0 : Q')*0 ≈ 0)) (QPoly.q_zero_add_eqv _))

end YMGap.Continuum.BF4ExactSlabBulkProbeSpectatorTests

#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeSpectatorTests.localChoice_selected
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeSpectatorTests.bulkProbe_enlarge
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeSpectatorTests.localChoice_spectator
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeSpectatorTests.lowerHeat_split
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeSpectatorTests.spectatorHeat_supported
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeSpectatorTests.spectatorHeat_local
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeSpectatorTests.localMinor_recentered_bound
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeSpectatorTests.localReferenceBudget_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeSpectatorTests.referenceBackground_supported
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeSpectatorTests.referenceBackground_local
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeSpectatorTests.reference_probe_zero
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeSpectatorTests.reference_scalar_zero
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeSpectatorTests.reference_unit
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeSpectatorTests.reference_mixed
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeSpectatorTests.referenceDeterminant_pin
