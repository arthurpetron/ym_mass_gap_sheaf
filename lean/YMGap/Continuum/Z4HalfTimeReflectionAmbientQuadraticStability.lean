/-
# Ambient finite-cylinder stability of the half-time reflection quadratic

The support-pushed corrected-slab Gram is positive, while each of its entries
is a literal corrected-slab conditional cylinder probability.  The general
carrier estimate therefore compares it entrywise with the corresponding
unconditioned ambient-box cylinder law.  Finite-cylinder quadratic stability
then gives the explicit error

    (sum |c|)^2 *
      (number of canonical roots) *
        (anchorDecoratedEffectiveRatio ^ floor * 2).

The only geometric datum not proved here is the carrier floor for the chosen
moving chart.  It is packaged below as a finite, pairwise alignment witness.
This is intentionally explicit: the exhaustive list of every slab-supported
root contains roots adjacent to the slab boundary and does not itself provide
a growing floor.
-/

import YMGap.Continuum.Z4HalfTimeReflectionSupportPairConditionalLaw

namespace YMGap.Continuum.Z4HalfTimeReflectionAmbientQuadraticStability

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4CanonicalBipartitePath
open YMGap.Continuum.Z4CanonicalFamilyFaceSupportDecoder
open YMGap.Continuum.Z4CouplingParametricFiniteCylinderLaw
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionSlabBoundarySwitchSummation
open YMGap.Continuum.Z4HalfTimeReflectionSlabConnectedCarrierAnimal
open YMGap.Continuum.Z4HalfTimeReflectionSlabConnectedPathCarrier
open YMGap.Continuum.Z4HalfTimeReflectionSlabFiniteKConditionalLaw
open YMGap.Continuum.Z4HalfTimeReflectionSlabFiniteKConditionalStability
open YMGap.Continuum.Z4HalfTimeReflectionSlabFiniteKConditionalStabilityGeneral
open YMGap.Continuum.Z4HalfTimeReflectionSupportPairConditionalLaw
open YMGap.Continuum.Z4HalfTimeReflectionSupportPushforwardGram
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The ambient joint cylinder law -/

/-- The ambient-box probability of the same exhaustive support-pair event
which represents one normalized corrected-slab Gram entry. -/
def centralAmbientSupportPairLaw
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (cutoff half : Nat) (leftSupport rightSupport : List Nat) : Q' :=
  couplingKFamilyEventProbability coupling hcoupling cutoff
    (centralAmbient half)
    (slabMarkedCylinderEvent
      (centralSlabCanonicalAtoms half)
      (centralSlabSupportPairCylinderPredicate
        half leftSupport rightSupport))

/-- The corresponding ambient finite reflection quadratic. -/
def centralAmbientSupportQuadratic
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (cutoff half : Nat) (coefficient : List Nat → Q') : Q' :=
  finiteJointQuadratic (centralHalfSupportSpace half) coefficient
    (centralAmbientSupportPairLaw coupling hcoupling cutoff half)

/-- The literal conditional-stability modulus for the exhaustive supported
canonical chart. -/
def centralSupportPairBoundaryEpsilon (half floor : Nat) : Q' :=
  couplingSlabConditionalBoundaryEpsilon
    (centralSlabCanonicalAtoms half).length floor

theorem centralSupportPairBoundaryEpsilon_nonnegative
    (half floor : Nat) :
    (0 : Q') ≤ centralSupportPairBoundaryEpsilon half floor := by
  exact couplingSlabConditionalBoundaryEpsilon_nonnegative
    (centralSlabCanonicalAtoms half).length floor

/-! ## 2. The exact chart-alignment obligation -/

/-- Forward pairwise carrier-floor proposition.  Naming this dependent
function keeps the alignment record itself small enough for predictable
kernel elaboration. -/
def CentralSupportPairForwardFloor
    (half floor : Nat)
    (defaultRoot : CanonicalAtom (centralAmbient half)) : Prop :=
  ∀ leftSupport rightSupport,
    leftSupport ∈ centralHalfSupportSpace half →
    rightSupport ∈ centralHalfSupportSpace half →
    ∀ entry : SlabConnectedSourceEntry (centralExtent half)
      (centralSlabCanonicalAtoms half)
      (centralSlabSupportPairCylinderPredicate
        half leftSupport rightSupport),
      floor ≤
        (slabConnectedCarrierSupport defaultRoot entry).length

/-- Complemented pairwise carrier-floor proposition. -/
def CentralSupportPairComplementFloor
    (half floor : Nat)
    (defaultRoot : CanonicalAtom (centralAmbient half)) : Prop :=
  ∀ leftSupport rightSupport,
    leftSupport ∈ centralHalfSupportSpace half →
    rightSupport ∈ centralHalfSupportSpace half →
    ∀ entry : SlabConnectedSourceEntry (centralExtent half)
      (centralSlabCanonicalAtoms half)
      (complementSlabPredicate
        (centralSlabSupportPairCylinderPredicate
          half leftSupport rightSupport)),
      floor ≤
        (slabConnectedCarrierSupport defaultRoot entry).length

/-- Pairwise connected-carrier floors for the exhaustive support chart.

The forward and complemented predicates are separate conjuncts because the
two-sided conditional estimate genuinely consumes both.  No growth assertion
is hidden in this proposition. -/
def CentralSupportPairCarrierFloors (half floor : Nat) : Prop :=
  ∃ defaultRoot : CanonicalAtom (centralAmbient half),
    CentralSupportPairForwardFloor half floor defaultRoot ∧
      CentralSupportPairComplementFloor half floor defaultRoot

private theorem sub_eqv_right_local {a b b' : Q'}
    (h : b ≈ b') : a - b ≈ a - b' :=
  Q'.add_eqv_congr'
    (Q'.eqv_refl a) (Q'.neg_eqv_congr b b' h)

/-- Entrywise comparison of the literal ambient law with the support-pushed
corrected-slab Gram law. -/
theorem centralAmbientSupportPairLaw_abs_sub_normalized_le
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling) (cutoff half floor : Nat)
    (alignment : CentralSupportPairCarrierFloors half floor)
    (leftSupport rightSupport : List Nat)
    (hleft : leftSupport ∈ centralHalfSupportSpace half)
    (hright : rightSupport ∈ centralHalfSupportSpace half) :
    Q'.abs
        (centralAmbientSupportPairLaw coupling hcoupling cutoff half
            leftSupport rightSupport -
          centralNormalizedSupportPairLaw coupling hcoupling cutoff half
            leftSupport rightSupport) ≤
      centralSupportPairBoundaryEpsilon half floor := by
  unfold CentralSupportPairCarrierFloors at alignment
  obtain ⟨defaultRoot, hforward, hcomplement⟩ := alignment
  have hraw :=
    couplingPhysicalAmbient_givenSlabProbability_abs_sub_le_of_floors
      hcoupling hle cutoff
      (centralSlabSupportPairCylinderPredicate
        half leftSupport rightSupport)
      defaultRoot
      (centralSlabCanonicalAtoms_supported half)
      floor
      (hforward leftSupport rightSupport hleft hright)
      (hcomplement leftSupport rightSupport hleft hright)
  have hconditional :=
    centralNormalizedSupportPairLaw_eq_physicalGivenSlab
      coupling hcoupling cutoff half leftSupport rightSupport
  have hdifference :
      centralAmbientSupportPairLaw coupling hcoupling cutoff half
          leftSupport rightSupport -
        centralNormalizedSupportPairLaw coupling hcoupling cutoff half
          leftSupport rightSupport ≈
      couplingKFamilyEventProbability coupling hcoupling cutoff
          (centralAmbient half)
          (slabMarkedCylinderEvent
            (centralSlabCanonicalAtoms half)
            (centralSlabSupportPairCylinderPredicate
              half leftSupport rightSupport)) -
        couplingParametricKPhysicalGivenSlabProbability
          coupling hcoupling cutoff (centralExtent half)
          (slabMarkedCylinderEvent
            (centralSlabCanonicalAtoms half)
            (centralSlabSupportPairCylinderPredicate
              half leftSupport rightSupport)) := by
    unfold centralAmbientSupportPairLaw
    exact sub_eqv_right_local hconditional
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.abs_eqv_congr hdifference)) hraw

/-! ## 3. Explicit quadratic error and approximate positivity -/

/-- The complete ambient quadratic differs from the normalized corrected-slab
Gram by at most the exact square-`l¹` coefficient modulus. -/
theorem centralAmbientSupportQuadratic_abs_sub_corrected_le
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling) (cutoff half floor : Nat)
    (alignment : CentralSupportPairCarrierFloors half floor)
    (coefficient : List Nat → Q') :
    Q'.abs
        (centralAmbientSupportQuadratic coupling hcoupling cutoff half
            coefficient -
          centralNormalizedSupportReflectionQuadratic
            coupling hcoupling cutoff half coefficient) ≤
      (coefficientL1 (centralHalfSupportSpace half) coefficient *
          coefficientL1 (centralHalfSupportSpace half) coefficient) *
        centralSupportPairBoundaryEpsilon half floor := by
  have hfinite := finiteJointQuadratic_abs_sub_le_square
    (centralHalfSupportSpace half) coefficient
    (centralAmbientSupportPairLaw coupling hcoupling cutoff half)
    (centralNormalizedSupportPairLaw coupling hcoupling cutoff half)
    (centralSupportPairBoundaryEpsilon half floor)
    (centralSupportPairBoundaryEpsilon_nonnegative half floor)
    (fun leftSupport rightSupport hleft hright =>
      centralAmbientSupportPairLaw_abs_sub_normalized_le
        hcoupling hle cutoff half floor alignment
        leftSupport rightSupport hleft hright)
  have hreference :=
    centralNormalizedSupportReflectionQuadratic_eq_jointLaw
      coupling hcoupling cutoff half coefficient
  have hdifference :
      centralAmbientSupportQuadratic coupling hcoupling cutoff half
          coefficient -
        centralNormalizedSupportReflectionQuadratic
          coupling hcoupling cutoff half coefficient ≈
      finiteJointQuadratic (centralHalfSupportSpace half) coefficient
          (centralAmbientSupportPairLaw coupling hcoupling cutoff half) -
        finiteJointQuadratic (centralHalfSupportSpace half) coefficient
          (centralNormalizedSupportPairLaw
            coupling hcoupling cutoff half) := by
    unfold centralAmbientSupportQuadratic
    exact sub_eqv_right_local hreference
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.abs_eqv_congr hdifference)) hfinite

/-- Ambient finite reflection positivity up to the same explicit vanishing
boundary modulus. -/
theorem centralAmbientSupportQuadratic_ge_neg_modulus
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling) (cutoff half floor : Nat)
    (alignment : CentralSupportPairCarrierFloors half floor)
    (coefficient : List Nat → Q') :
    -((coefficientL1 (centralHalfSupportSpace half) coefficient *
          coefficientL1 (centralHalfSupportSpace half) coefficient) *
        centralSupportPairBoundaryEpsilon half floor) ≤
      centralAmbientSupportQuadratic coupling hcoupling cutoff half
        coefficient := by
  have hreference :
      (0 : Q') ≤
        finiteJointQuadratic (centralHalfSupportSpace half) coefficient
          (centralNormalizedSupportPairLaw
            coupling hcoupling cutoff half) := by
    exact Q'.le_trans' _ _ _
      (centralNormalizedSupportReflectionQuadratic_nonnegative
        coupling hcoupling cutoff half coefficient)
      (Q'.le_of_eqv
        (centralNormalizedSupportReflectionQuadratic_eq_jointLaw
          coupling hcoupling cutoff half coefficient))
  exact finiteJointQuadratic_ge_neg_square_modulus
    (centralHalfSupportSpace half) coefficient
    (centralAmbientSupportPairLaw coupling hcoupling cutoff half)
    (centralNormalizedSupportPairLaw coupling hcoupling cutoff half)
    (centralSupportPairBoundaryEpsilon half floor)
    (centralSupportPairBoundaryEpsilon_nonnegative half floor)
    hreference
    (fun leftSupport rightSupport hleft hright =>
      centralAmbientSupportPairLaw_abs_sub_normalized_le
        hcoupling hle cutoff half floor alignment
        leftSupport rightSupport hleft hright)

#print axioms centralSupportPairBoundaryEpsilon_nonnegative
#print axioms centralAmbientSupportPairLaw_abs_sub_normalized_le
#print axioms centralAmbientSupportQuadratic_abs_sub_corrected_le
#print axioms centralAmbientSupportQuadratic_ge_neg_modulus

end YMGap.Continuum.Z4HalfTimeReflectionAmbientQuadraticStability
