/-
# Coupling-sensitive payment for the observable residual core

The first arbitrary-coupling accepted-path theorem deliberately replaced the
exact ordinary-peel coefficient by the uniform coarse factor `2`.  The exact
coefficient remains available: an ordinary positive peel is a threshold-zero
high-spin peel and therefore costs

  exteriorFaceCoefficient w 0 = 2 * w^3.

This module retains that coefficient through the component completion, one
accepted step, the deterministic paired recursion, and the literal observable
profile.  Thus the pointwise payment is sharpened from

  anchor^exterior * 2^core

to

  anchor^exterior * (2*w^3)^core.

After inverse-code entropy is counted, this is contractive throughout the
explicit strong-coupling corridor `0 < w <= 1/400`.  The corridor summation is
the next layer; no claim is made here beyond the exact pointwise telescope.

Constructive contract: finite path induction, the existing exact SU(2)
successor inequality, and rational order algebra only; no choice, `Classical`,
`native_decide`, `sorry`, noncomputable declaration, or new axiom.
-/

import YMGap.Continuum.CompactDualSlabObservablePairedSupportHighSpinProfileWeight

namespace YMGap.Continuum.CompactDualSlabObservablePairedSupportHighSpinProfileCouplingWeight

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.BF4SU2FineIntertwinerPhysicalDisintegration
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeeling
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingArbitraryCouplingWeight
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingHighSpinProfile
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalStep
open YMGap.Continuum.CompactDualSlabAcceptedPairedPeel
open YMGap.Continuum.CompactDualSlabAcceptedPeelWeight
open YMGap.Continuum.CompactDualSlabExpandedFacePeelWeight
open YMGap.Continuum.CompactDualSlabExpandedSourceEnumeration
open YMGap.Continuum.CompactDualSlabFaceStrandComponentAssignment
open YMGap.Continuum.CompactDualSlabFaceStrandComponentCoreCompletionWeight
open YMGap.Continuum.CompactDualSlabFaceStrandComponentDrop
open YMGap.Continuum.CompactDualSlabFaceStrandComponentHighSpinCoreSplitWeight
open YMGap.Continuum.CompactDualSlabFaceStrandComponentWeight
open YMGap.Continuum.CompactDualSlabFaceStrandSeedComponent
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabHighSpinFacePeelWeight
open YMGap.Continuum.CompactDualSlabObservablePairedSupportComponent
open YMGap.Continuum.CompactDualSlabObservablePairedSupportConnectedMassFloor
open YMGap.Continuum.CompactDualSlabObservablePairedSupportHighSpinProfileWeight
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Exact threshold-zero residual path payment -/

/-- An ordinary positive face-peel path telescopes at the exact
threshold-zero successor coefficient `2*w^3`. -/
theorem slabFacePeelPath_faceFactor_le_zeroCoefficient
    {w : Q'} (hw0 : (0 : Q') <= w) (hw1 : w <= (1 : Q'))
    {cutoff extent : Nat} {source target : EdgeLabelling}
    {faces : List Nat}
    (path : SlabFacePeelPath cutoff extent source faces target) :
    slabParametricKPhysicalFaceFactor w cutoff extent source <=
      exteriorFaceCoefficient w 0 ^ faces.length *
        slabParametricKPhysicalFaceFactor w cutoff extent target := by
  induction path with
  | nil physical =>
      simp only [List.length_nil, Q'.pow_zero]
      exact Q'.le_of_eqv
        (Q'.eqv_symm
          (Q'.one_mul_eqv
            (slabParametricKPhysicalFaceFactor
              w cutoff extent physical)))
  | @cons physical target faces faceId hface hpositive hbounded tail ih =>
      have hone := slabPhysicalFaceFactor_exterior_lower_one_le_of_rate
        hw0 hw1 cutoff extent 0 physical faceId hface hpositive hbounded
        (Q'.le_refl' (exteriorFaceCoefficient w 0))
      have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ _ ih
        (exteriorFaceCoefficient_nonnegative hw0 0)
      have hchain := Q'.le_trans' _ _ _ hone hscaled
      simp only [List.length_cons, Q'.pow_succ]
      exact Q'.le_trans' _ _ _ hchain
        (Q'.le_of_eqv
          (Q'.eqv_symm
            (Q'.mul_assoc_eqv (exteriorFaceCoefficient w 0)
              (exteriorFaceCoefficient w 0 ^ faces.length)
              (slabParametricKPhysicalFaceFactor
                w cutoff extent target))))

/-- Unit Haar counting lifts the exact threshold-zero residual payment to
arbitrary source and target accepted assignment witnesses. -/
theorem retainedFineIntertwinerPhysicalFiberWeight_peelPath_le_zeroCoefficient
    {w : Q'} (hw0 : (0 : Q') <= w) (hw1 : w <= (1 : Q'))
    (cutoff half : Nat)
    {sourcePhysical targetPhysical : EdgeLabelling} {faces : List Nat}
    (sourceWitness targetWitness : SlabFusionWitnessAssignment)
    (path : SlabFacePeelPath cutoff (centralExtent half)
      sourcePhysical faces targetPhysical) :
    let D : SlabPhysicalData :=
      { coupling := w
        coupling_nonnegative := hw0
        cutoff := cutoff
        half := half }
    retainedFineIntertwinerPhysicalFiberWeight
        D sourcePhysical sourceWitness <=
      exteriorFaceCoefficient w 0 ^ faces.length *
        retainedFineIntertwinerPhysicalFiberWeight
          D targetPhysical targetWitness := by
  dsimp only
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (retainedFineIntertwinerPhysicalFiberWeight_eqv_faceFactor
        { coupling := w
          coupling_nonnegative := hw0
          cutoff := cutoff
          half := half }
        sourcePhysical sourceWitness))
    (Q'.le_trans' _ _ _
      (slabFacePeelPath_faceFactor_le_zeroCoefficient hw0 hw1 path)
      (Q'.le_of_eqv
        (Q'.mul_eqv_congr_left
          (exteriorFaceCoefficient w 0 ^ faces.length) _ _
          (Q'.eqv_symm
            (retainedFineIntertwinerPhysicalFiberWeight_eqv_faceFactor
              { coupling := w
                coupling_nonnegative := hw0
                cutoff := cutoff
                half := half }
              targetPhysical targetWitness)))))

/-! ## 2. One coupling-sensitive accepted component -/

/-- The high-spin exterior keeps the fixed entropy payment while the
remaining low-spin word keeps its exact coupling-sensitive coefficient. -/
theorem expandedFiberWeight_coreCompleted_le_zeroCoefficient
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (cutoff half : Nat) {physical : SlabLabelling}
    {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn cutoff (centralExtent half) physical
        (boundaryCompleteSlabLinks (centralExtent half))}
    (seed : SlabFusionWitnessFaceStrandSeed
      cutoff (centralExtent half) physical
        (boundaryCompleteSlabLinks (centralExtent half))
        assignment hassignment)
    (hbounded : SlabFaceLabellingBounded
      cutoff (centralExtent half) physical) :
    let D : SlabPhysicalData :=
      { coupling := w
        coupling_nonnegative := Q'.le_of_lt hw0
        cutoff := cutoff
        half := half }
    retainedFineIntertwinerPhysicalFiberWeight D physical assignment <=
      (anchorFaceCoefficient ^
          (SlabFusionWitnessFaceStrandSeed.exteriorPeelFaces seed
            (anchorPaidExteriorThreshold w)).length *
        exteriorFaceCoefficient w 0 ^
          (SlabFusionWitnessFaceStrandSeed.coreResidualFaces seed
            (anchorPaidExteriorThreshold w)).length) *
        retainedFineIntertwinerPhysicalFiberWeight D
          (SlabFusionWitnessFaceStrandSeed.lowerPhysical seed)
          (SlabFusionWitnessFaceStrandSeed.lowerAssignment seed) := by
  dsimp only
  have hexterior :=
    SlabFusionWitnessFaceStrandSeed.expandedFiberWeight_coreSplit_le
      hw0 hw1 cutoff half seed
      (SlabFusionWitnessFaceStrandSeed.lowerAssignment seed) hbounded
  dsimp only at hexterior
  have hresidual :=
    retainedFineIntertwinerPhysicalFiberWeight_peelPath_le_zeroCoefficient
      (Q'.le_of_lt hw0) (Q'.le_of_lt hw1) cutoff half
      (SlabFusionWitnessFaceStrandSeed.lowerAssignment seed)
      (SlabFusionWitnessFaceStrandSeed.lowerAssignment seed)
      (SlabFusionWitnessFaceStrandSeed.coreResidualPath
        seed (anchorPaidExteriorThreshold w) hbounded)
  dsimp only at hresidual
  let exteriorRate := anchorFaceCoefficient ^
    (SlabFusionWitnessFaceStrandSeed.exteriorPeelFaces seed
      (anchorPaidExteriorThreshold w)).length
  let residualRate := exteriorFaceCoefficient w 0 ^
    (SlabFusionWitnessFaceStrandSeed.coreResidualFaces seed
      (anchorPaidExteriorThreshold w)).length
  have hexteriorRate : (0 : Q') <= exteriorRate :=
    Q'.pow_nonneg anchorFaceCoefficient (by decide) _
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ _
    hresidual hexteriorRate
  exact Q'.le_trans' _ _ _ hexterior
    (Q'.le_trans' _ _ _ hscaled
      (Q'.le_of_eqv
        (Q'.eqv_symm
          (Q'.mul_assoc_eqv exteriorRate residualRate
            (retainedFineIntertwinerPhysicalFiberWeight
              { coupling := w
                coupling_nonnegative := Q'.le_of_lt hw0
                cutoff := cutoff
                half := half }
              (SlabFusionWitnessFaceStrandSeed.lowerPhysical seed)
              (SlabFusionWitnessFaceStrandSeed.lowerAssignment seed))))))

/-- One accepted expanded source inherits the exact local-core coefficient. -/
theorem slabExpandedFineEntryWeight_lowerAt_le_zeroCoefficient
    (D : SlabPhysicalData)
    (hw0 : (0 : Q') < D.coupling) (hw1 : D.coupling < (1 : Q'))
    (faceId : Nat) (hface : faceId ∈ slabPhysicalFaceEdges D.extent)
    (entry : SlabExpandedFineSourceEntry D)
    (hpositive : 0 < entry.1.1 faceId) :
    slabExpandedFineEntryWeight D entry <=
      (anchorFaceCoefficient ^
          acceptedExpandedSourceExteriorPeelSizeAt D
            (anchorPaidExteriorThreshold D.coupling)
            faceId hface entry hpositive *
        exteriorFaceCoefficient D.coupling 0 ^
          acceptedExpandedSourceCoreResidualSizeAt D
            (anchorPaidExteriorThreshold D.coupling)
            faceId hface entry hpositive) *
        slabExpandedFineEntryWeight D
          (acceptedExpandedSourceLowerAt
            D faceId hface entry hpositive) := by
  have hphysical := acceptedExpandedSourcePhysical_mem entry
  have hbounded : SlabFaceLabellingBounded
      D.cutoff D.extent entry.1.1 := by
    intro selectedFaceId hselected
    exact Nat.le_of_lt_succ
      ((boundedEdgeLabellings_sound D.cutoff D.faceEdges
        entry.1.1 hphysical).1 selectedFaceId
          (by simpa only [SlabPhysicalData.faceEdges] using hselected))
  have hstep := expandedFiberWeight_coreCompleted_le_zeroCoefficient
    hw0 hw1 D.cutoff D.half
      (acceptedExpandedSourceRootSeed D faceId hface entry hpositive)
      hbounded
  simpa only [slabExpandedFineEntryWeight, slabExpandedFineSourceWeight,
    acceptedExpandedSourceExteriorPeelSizeAt,
    acceptedExpandedSourceCoreResidualSizeAt,
    acceptedExpandedSourceLowerAt] using hstep

/-! ## 3. Telescope the exact coefficient through paired peeling -/

/-- Coupling-sensitive multiplier paid by one selected paired component. -/
def slabAcceptedPairedPeelChoiceCouplingPaymentRate
    {D : SlabPhysicalData} {state : SlabAcceptedTwoReplicaState D}
    (threshold : Nat) (choice : SlabAcceptedPairedPeelChoice D state) : Q' :=
  anchorFaceCoefficient ^
      slabAcceptedPairedPeelChoiceExteriorPeelSizeAt threshold choice *
    exteriorFaceCoefficient D.coupling 0 ^
      slabAcceptedPairedPeelChoiceCoreResidualSizeAt threshold choice

theorem slabAcceptedPairedPeelChoiceCouplingPaymentRate_nonnegative
    {D : SlabPhysicalData} {state : SlabAcceptedTwoReplicaState D}
    (threshold : Nat) (choice : SlabAcceptedPairedPeelChoice D state) :
    (0 : Q') <=
      slabAcceptedPairedPeelChoiceCouplingPaymentRate threshold choice := by
  exact Q'.mul_nonneg _ _
    (Q'.pow_nonneg anchorFaceCoefficient (by decide) _)
    (Q'.pow_nonneg (exteriorFaceCoefficient D.coupling 0)
      (exteriorFaceCoefficient_nonnegative D.coupling_nonnegative 0) _)

/-- One selected paired peel pays the sharpened multiplier; the unchanged
replica is transported by nonnegativity. -/
theorem SlabAcceptedPairedPeelChoice.sourceWeight_le_zeroCoefficient
    (D : SlabPhysicalData)
    (hw0 : (0 : Q') < D.coupling) (hw1 : D.coupling < (1 : Q'))
    {state : SlabAcceptedTwoReplicaState D}
    (choice : SlabAcceptedPairedPeelChoice D state) :
    slabAcceptedTwoReplicaStateWeight D state <=
      slabAcceptedPairedPeelChoiceCouplingPaymentRate
          (anchorPaidExteriorThreshold D.coupling) choice *
        slabAcceptedTwoReplicaStateWeight D choice.lowerState := by
  cases choice with
  | left faceId hface hpositive =>
      have hsource := slabExpandedFineEntryWeight_lowerAt_le_zeroCoefficient
        D hw0 hw1 faceId hface state.1 hpositive
      have hright := slabExpandedFineEntryWeight_nonnegative D state.2
      have hscaled := Q'.mul_le_mul_of_nonneg_right _ _ _ hsource hright
      exact Q'.le_trans' _ _ _ hscaled
        (Q'.le_of_eqv (Q'.mul_assoc_eqv _ _ _))
  | right faceId hface hleftZero hpositive =>
      have hsource := slabExpandedFineEntryWeight_lowerAt_le_zeroCoefficient
        D hw0 hw1 faceId hface state.2 hpositive
      have hleft := slabExpandedFineEntryWeight_nonnegative D state.1
      have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ _ hsource hleft
      refine Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv ?_)
      refine Q'.eqv_trans _
        ((slabExpandedFineEntryWeight D state.1 *
            (anchorFaceCoefficient ^
                acceptedExpandedSourceExteriorPeelSizeAt D
                  (anchorPaidExteriorThreshold D.coupling)
                  faceId hface state.2 hpositive *
              exteriorFaceCoefficient D.coupling 0 ^
                acceptedExpandedSourceCoreResidualSizeAt D
                  (anchorPaidExteriorThreshold D.coupling)
                  faceId hface state.2 hpositive)) *
          slabExpandedFineEntryWeight D
            (acceptedExpandedSourceLowerAt
              D faceId hface state.2 hpositive)) _
        (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
      refine Q'.eqv_trans _
        (((anchorFaceCoefficient ^
                acceptedExpandedSourceExteriorPeelSizeAt D
                  (anchorPaidExteriorThreshold D.coupling)
                  faceId hface state.2 hpositive *
              exteriorFaceCoefficient D.coupling 0 ^
                acceptedExpandedSourceCoreResidualSizeAt D
                  (anchorPaidExteriorThreshold D.coupling)
                  faceId hface state.2 hpositive) *
            slabExpandedFineEntryWeight D state.1) *
          slabExpandedFineEntryWeight D
            (acceptedExpandedSourceLowerAt
              D faceId hface state.2 hpositive)) _
        (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv _ _))
        (Q'.mul_assoc_eqv _ _ _)

private theorem mul_four_regroup_local (A B C E : Q') :
    (A * B) * (C * E) ≈ (A * C) * (B * E) := by
  refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv A B (C * E)) ?_
  refine Q'.eqv_trans _ _ _ ?_
    (Q'.eqv_symm (Q'.mul_assoc_eqv A C (B * E)))
  refine Q'.mul_eqv_congr_left A _ _ ?_
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.mul_assoc_eqv B C E)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ E (Q'.mul_comm_eqv B C)) ?_
  exact Q'.mul_assoc_eqv C B E

private theorem twoRatePower_mul_local
    (exteriorBase coreBase : Q')
    (headExterior headCore tailExterior tailCore : Nat)
    (target : Q') :
    (exteriorBase ^ headExterior * coreBase ^ headCore) *
        ((exteriorBase ^ tailExterior * coreBase ^ tailCore) * target) ≈
      (exteriorBase ^ (headExterior + tailExterior) *
          coreBase ^ (headCore + tailCore)) * target := by
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv
    (exteriorBase ^ headExterior * coreBase ^ headCore)
    (exteriorBase ^ tailExterior * coreBase ^ tailCore) target)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ target
      (mul_four_regroup_local
        (exteriorBase ^ headExterior) (coreBase ^ headCore)
        (exteriorBase ^ tailExterior) (coreBase ^ tailCore))) ?_
  apply Q'.mul_eqv_congr_right
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _
      (Q'.eqv_symm
        (Q'.pow_add_eqv exteriorBase headExterior tailExterior))) ?_
  exact Q'.mul_eqv_congr_left _ _ _
    (Q'.eqv_symm (Q'.pow_add_eqv coreBase headCore tailCore))

/-- Exact coupling-sensitive profiled telescope to the accepted terminal. -/
theorem slabAcceptedPairCanonicalHighSpinProfile_sourceWeight_le_zeroCoefficient
    (D : SlabPhysicalData)
    (hw0 : (0 : Q') < D.coupling) (hw1 : D.coupling < (1 : Q'))
    (faces : List Nat)
    (hphysical : forall faceId, faceId ∈ faces ->
      faceId ∈ slabPhysicalFaceEdges D.extent)
    (state : SlabAcceptedTwoReplicaState D) :
    let result := slabAcceptedPairCanonicalHighSpinProfile
      D (anchorPaidExteriorThreshold D.coupling) faces hphysical state
    slabAcceptedTwoReplicaStateWeight D state <=
      (anchorFaceCoefficient ^ result.2.2.1 *
          exteriorFaceCoefficient D.coupling 0 ^ result.2.2.2) *
        slabAcceptedTwoReplicaStateWeight D result.1 := by
  change slabAcceptedTwoReplicaStateWeight D state <=
    (anchorFaceCoefficient ^
          (slabAcceptedPairCanonicalHighSpinProfile D
            (anchorPaidExteriorThreshold D.coupling)
              faces hphysical state).2.2.1 *
        exteriorFaceCoefficient D.coupling 0 ^
          (slabAcceptedPairCanonicalHighSpinProfile D
            (anchorPaidExteriorThreshold D.coupling)
              faces hphysical state).2.2.2) *
      slabAcceptedTwoReplicaStateWeight D
        (slabAcceptedPairCanonicalHighSpinProfile D
          (anchorPaidExteriorThreshold D.coupling)
            faces hphysical state).1
  rw [slabAcceptedPairCanonicalHighSpinProfile]
  split
  · exact Q'.le_of_eqv (Q'.eqv_symm (Q'.one_mul_eqv _))
  · rename_i choice hchoice
    have hstep := SlabAcceptedPairedPeelChoice.sourceWeight_le_zeroCoefficient
      D hw0 hw1 choice
    have htail :=
      slabAcceptedPairCanonicalHighSpinProfile_sourceWeight_le_zeroCoefficient
        D hw0 hw1 faces hphysical choice.lowerState
    have hrateNonnegative :=
      slabAcceptedPairedPeelChoiceCouplingPaymentRate_nonnegative
        (anchorPaidExteriorThreshold D.coupling) choice
    have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ _
      htail hrateNonnegative
    refine Q'.le_trans' _ _ _ hstep
      (Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv ?_))
    unfold slabAcceptedPairedPeelChoiceCouplingPaymentRate
    exact twoRatePower_mul_local
      anchorFaceCoefficient (exteriorFaceCoefficient D.coupling 0)
      (slabAcceptedPairedPeelChoiceExteriorPeelSizeAt
        (anchorPaidExteriorThreshold D.coupling) choice)
      (slabAcceptedPairedPeelChoiceCoreResidualSizeAt
        (anchorPaidExteriorThreshold D.coupling) choice)
      (slabAcceptedPairCanonicalHighSpinProfile D
        (anchorPaidExteriorThreshold D.coupling)
          faces hphysical choice.lowerState).2.2.1
      (slabAcceptedPairCanonicalHighSpinProfile D
        (anchorPaidExteriorThreshold D.coupling)
          faces hphysical choice.lowerState).2.2.2
      (slabAcceptedTwoReplicaStateWeight D
        (slabAcceptedPairCanonicalHighSpinProfile D
          (anchorPaidExteriorThreshold D.coupling)
            faces hphysical choice.lowerState).1)
termination_by slabAcceptedTwoReplicaStateMass state
decreasing_by
  apply SlabAcceptedPairedPeelChoice.lowerState_mass_lt

/-! ## 4. Literal observable specialization -/

/-- The observable target-support profile inherits the exact `2*w^3`
residual-core payment. -/
theorem slabObservablePairTargetSupportCanonicalHighSpinProfile_sourceWeight_le_zeroCoefficient
    (D : SlabPhysicalData)
    (hw0 : (0 : Q') < D.coupling) (hw1 : D.coupling < (1 : Q'))
    (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (hpair : pair ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId) :
    let result := slabObservablePairTargetSupportCanonicalHighSpinProfile
      D rootFaceId targetFaceId htarget pair hpair
    slabObservableTwoReplicaPairWeight D pair <=
      (anchorFaceCoefficient ^ result.2.2.1 *
          exteriorFaceCoefficient D.coupling 0 ^ result.2.2.2) *
        slabAcceptedTwoReplicaStateWeight D result.1 := by
  rw [slabObservableTwoReplicaPairWeight_eq_acceptedStateWeight_general]
  unfold slabObservablePairTargetSupportCanonicalHighSpinProfile
  exact slabAcceptedPairCanonicalHighSpinProfile_sourceWeight_le_zeroCoefficient
    D hw0 hw1
      (slabTwoReplicaTargetSupportComponent D.extent
        pair.1.1.1 pair.2.1.1 targetFaceId)
      (fun faceId hface =>
        slabObservableTwoReplicaPairTargetSupportComponent_face_mem_physical
          D rootFaceId targetFaceId htarget pair hpair faceId hface)
      (slabObservableTwoReplicaPairToAcceptedState pair)

#print axioms slabFacePeelPath_faceFactor_le_zeroCoefficient
#print axioms retainedFineIntertwinerPhysicalFiberWeight_peelPath_le_zeroCoefficient
#print axioms expandedFiberWeight_coreCompleted_le_zeroCoefficient
#print axioms slabExpandedFineEntryWeight_lowerAt_le_zeroCoefficient
#print axioms slabAcceptedPairedPeelChoiceCouplingPaymentRate
#print axioms SlabAcceptedPairedPeelChoice.sourceWeight_le_zeroCoefficient
#print axioms slabAcceptedPairCanonicalHighSpinProfile_sourceWeight_le_zeroCoefficient
#print axioms slabObservablePairTargetSupportCanonicalHighSpinProfile_sourceWeight_le_zeroCoefficient

end YMGap.Continuum.CompactDualSlabObservablePairedSupportHighSpinProfileCouplingWeight
