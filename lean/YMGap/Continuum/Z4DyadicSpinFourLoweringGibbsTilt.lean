/-
# The spin-four lowering row as an integer tilt of the coarse Gibbs weight

The exact lowering downset still presents each surviving summand as a product
of local recoupling weights.  This file separates that product into its two
mathematically distinct factors:

  * an integer product counting the supported local fusion paths; and
  * the ordinary complete coarse Gibbs physical summand.

Thus the canonical spin-four row partition is exactly an integer-tilted Gibbs
mass on its finite pointwise-lowering downset.  All target link multiplicities
belong to the Gibbs factor and are retained without approximation.

This is a factorization theorem, not yet a bound on the tilted downset mass or
on the centered production-versus-refresh cross.

Constructive contract: structural finite products and exact rational algebra
only; no `Classical`, choice, `native_decide`, proof hole, noncomputable
declaration, trusted external computation, or new axiom.
-/

import YMGap.Continuum.Z4DyadicSpinFourLoweringDownset

namespace YMGap.Continuum.Z4DyadicSpinFourLoweringGibbsTilt

set_option autoImplicit false
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.BF4SU2OuterJointCarrierRawRowMass
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.CompactDualCutoffOnePositivePhysicalClosure
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualSlabExpandedSourceEnumeration
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.CompactDualWholeSlabRecouplingRawKernel
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4DyadicSpinFourLoweringDownset
open YMGap.Continuum.Z4DyadicSpinFourLoweringKernel
open YMGap.Continuum.Z4DyadicSpinFourWholeSlabTargetExact
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Separate the path-count product from the heat product -/

/-- Product of the exact local fusion-path multiplicities over every physical
coarse face. -/
def spinFourLoweringMultiplicityProduct
    (S : SlabScalePair) (sourceState targetState : EdgeLabelling) : Nat :=
  natListProduct
    (fun faceId => spinFourLoweringMultiplicity
      (sourceState faceId) (targetState faceId))
    S.coarse.faceEdges

private theorem wholeSlabFiniteQProduct_congr_on_local {A : Type}
    (left right : A → Q') : ∀ items : List A,
    (∀ item, item ∈ items → left item ≈ right item) →
      wholeSlabFiniteQProduct left items ≈
        wholeSlabFiniteQProduct right items
  | [], _ => Q'.eqv_refl 1
  | head :: tail, hagree => by
      change
        left head * wholeSlabFiniteQProduct left tail ≈
          right head * wholeSlabFiniteQProduct right tail
      exact Q'.eqv_trans _
        (right head * wholeSlabFiniteQProduct left tail) _
        (Q'.mul_eqv_congr_right _ _ _
          (hagree head List.mem_cons_self))
        (Q'.mul_eqv_congr_left _ _ _
          (wholeSlabFiniteQProduct_congr_on_local left right tail
            (fun item hmem =>
              hagree item (List.mem_cons_of_mem head hmem))))

private theorem wholeSlabFiniteQProduct_pointwise_mul_local {A : Type}
    (left right : A → Q') : ∀ items : List A,
    wholeSlabFiniteQProduct (fun item => left item * right item) items ≈
      wholeSlabFiniteQProduct left items *
        wholeSlabFiniteQProduct right items
  | [] => Q'.eqv_symm (Q'.mul_one_eqv 1)
  | head :: tail => by
      simp only [wholeSlabFiniteQProduct]
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left (left head * right head) _ _
          (wholeSlabFiniteQProduct_pointwise_mul_local left right tail)) ?_
      exact YMGap.Continuum.RingNormaliser.q_mul4_swap
        (left head) (right head)
        (wholeSlabFiniteQProduct left tail)
        (wholeSlabFiniteQProduct right tail)

private theorem ofNat_natListProduct_eqv_wholeSlabFiniteQProduct_local
    {A : Type} (value : A → Nat) : ∀ items : List A,
    Q'.ofNat (natListProduct value items) ≈
      wholeSlabFiniteQProduct (fun item => Q'.ofNat (value item)) items
  | [] => Q'.eqv_refl 1
  | head :: tail => by
      simp only [natListProduct, wholeSlabFiniteQProduct]
      exact Q'.eqv_trans _ _ _
        (YMGap.Continuum.HeatKernelRGStep.ofNat_mul_eqv
          (value head) (natListProduct value tail))
        (Q'.mul_eqv_congr_left _ _ _
          (ofNat_natListProduct_eqv_wholeSlabFiniteQProduct_local
            value tail))

private theorem wholeSlabFiniteQProduct_eq_eliminateLinks_local
    (value : Nat → Q') : ∀ items : List Nat,
    wholeSlabFiniteQProduct value items = eliminateLinks value items
  | [] => rfl
  | _ :: tail => by
      simp only [wholeSlabFiniteQProduct, eliminateLinks]
      rw [wholeSlabFiniteQProduct_eq_eliminateLinks_local value tail]

/-- On a physical target, the product of the visible target heat
coefficients is exactly the face factor of its coarse Gibbs weight. -/
theorem spinFourTargetCoefficientProduct_eqv_coarseFaceFactor
    (S : SlabScalePair) (targetState : EdgeLabelling)
    (htargetMem : targetState ∈ S.coarse.physicalLabellings) :
    wholeSlabFiniteQProduct
        (fun faceId => coeffW S.coarse.coupling (targetState faceId))
        S.coarse.faceEdges ≈
      slabParametricKPhysicalFaceFactor S.coarse.coupling
        S.coarse.cutoff S.coarse.extent targetState := by
  let coarseCoefficient : Nat → Q' := fun faceId =>
    coeffAt (heatKernelPacket S.coarse.cutoff S.coarse.coupling)
      (targetState faceId)
  have htargetSound := boundedEdgeLabellings_sound
    S.coarse.cutoff S.coarse.faceEdges targetState htargetMem
  refine Q'.eqv_trans _
    (wholeSlabFiniteQProduct coarseCoefficient S.coarse.faceEdges) _ ?_ ?_
  · apply wholeSlabFiniteQProduct_congr_on_local
    intro faceId hface
    exact Q'.eqv_symm
      (Q'.eqv_of_eq
        (coeffAt_heatKernelPacket (htargetSound.1 faceId hface)))
  · unfold slabParametricKPhysicalFaceFactor SlabPhysicalData.faceEdges
    exact Q'.eqv_of_eq
      (wholeSlabFiniteQProduct_eq_eliminateLinks_local
        coarseCoefficient (slabPhysicalFaceEdges S.coarse.extent))

/-! ## 2. Exact integer-tilted Gibbs row -/

/-- Every surviving lower-triangular raw entry is the exact product of its
integer fusion-path count and the complete coarse Gibbs physical weight. -/
theorem spinFourLoweringWholeSlabRawWeight_eqv_multiplicity_mul_physicalTerm
    (S : SlabScalePair) (sourceState targetState : EdgeLabelling)
    (htargetMem : targetState ∈ S.coarse.physicalLabellings) :
    spinFourLoweringWholeSlabRawWeight S sourceState targetState ≈
      Q'.ofNat
          (spinFourLoweringMultiplicityProduct S sourceState targetState) *
        S.coarse.physicalTerm targetState := by
  let localMultiplicity : Nat → Nat := fun faceId =>
    spinFourLoweringMultiplicity
      (sourceState faceId) (targetState faceId)
  let localCoefficient : Nat → Q' := fun faceId =>
    coeffW S.coarse.coupling (targetState faceId)
  let linkFactor : Q' := Q'.ofNat
    (slabExplicitLinkMultiplicityProduct
      S.coarse.cutoff S.coarse.extent targetState)
  have hseparate :
      wholeSlabFiniteQProduct
          (fun faceId => Q'.ofNat (localMultiplicity faceId) *
            localCoefficient faceId)
          S.coarse.faceEdges ≈
        wholeSlabFiniteQProduct
            (fun faceId => Q'.ofNat (localMultiplicity faceId))
            S.coarse.faceEdges *
          wholeSlabFiniteQProduct localCoefficient S.coarse.faceEdges :=
    wholeSlabFiniteQProduct_pointwise_mul_local _ _ _
  have hmultiplicity :
      wholeSlabFiniteQProduct
          (fun faceId => Q'.ofNat (localMultiplicity faceId))
          S.coarse.faceEdges ≈
        Q'.ofNat
          (spinFourLoweringMultiplicityProduct
            S sourceState targetState) := by
    exact Q'.eqv_symm
      (ofNat_natListProduct_eqv_wholeSlabFiniteQProduct_local
        localMultiplicity S.coarse.faceEdges)
  have hcoefficient :
      wholeSlabFiniteQProduct localCoefficient S.coarse.faceEdges ≈
        slabParametricKPhysicalFaceFactor S.coarse.coupling
          S.coarse.cutoff S.coarse.extent targetState := by
    exact spinFourTargetCoefficientProduct_eqv_coarseFaceFactor
      S targetState htargetMem
  unfold spinFourLoweringWholeSlabRawWeight spinFourLoweringFaceWeight
    SlabPhysicalData.physicalTerm slabParametricKPhysicalTerm
    spinFourLoweringMultiplicityProduct
  change
    wholeSlabFiniteQProduct
        (fun faceId => Q'.ofNat (localMultiplicity faceId) *
          localCoefficient faceId)
        S.coarse.faceEdges * linkFactor ≈
      Q'.ofNat (natListProduct localMultiplicity S.coarse.faceEdges) *
        (slabParametricKPhysicalFaceFactor S.coarse.coupling
          S.coarse.cutoff S.coarse.extent targetState * linkFactor)
  refine Q'.eqv_trans _
    ((wholeSlabFiniteQProduct
        (fun faceId => Q'.ofNat (localMultiplicity faceId))
        S.coarse.faceEdges *
      wholeSlabFiniteQProduct localCoefficient S.coarse.faceEdges) *
        linkFactor) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ _ hseparate
  refine Q'.eqv_trans _
    ((Q'.ofNat (natListProduct localMultiplicity S.coarse.faceEdges) *
      slabParametricKPhysicalFaceFactor S.coarse.coupling
        S.coarse.cutoff S.coarse.extent targetState) * linkFactor) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ linkFactor
      (Q'.eqv_trans _
        (Q'.ofNat (natListProduct localMultiplicity S.coarse.faceEdges) *
          wholeSlabFiniteQProduct localCoefficient S.coarse.faceEdges) _
        (Q'.mul_eqv_congr_right _ _ _ hmultiplicity)
        (Q'.mul_eqv_congr_left _ _ _ hcoefficient))
  · exact Q'.mul_assoc_eqv _ _ _

/-- Generic canonical-profile row mass as an integer-tilted coarse Gibbs mass
on the exact lowering downset. -/
theorem wholeSlabRawRowMass_spinFourProfile_eqv_multiplicityTiltedGibbs
    (S : SlabScalePair) (fineState sourceState : EdgeLabelling)
    (hfineCutoff : S.fine.cutoff = 1)
    (profile : SpinFourWholeSlabPacketProfile S fineState sourceState) :
    listQSum (wholeSlabRecouplingRawWeight S fineState)
        S.coarse.physicalLabellings ≈
      listQSum
        (fun targetState =>
          Q'.ofNat
              (spinFourLoweringMultiplicityProduct
                S sourceState targetState) *
            S.coarse.physicalTerm targetState)
        (spinFourLoweringTargets S sourceState) := by
  refine Q'.eqv_trans _
    (listQSum (spinFourLoweringWholeSlabRawWeight S sourceState)
      (spinFourLoweringTargets S sourceState)) _
    (wholeSlabRawRowMass_spinFourProfile_eqv_loweringDownset
      S fineState sourceState hfineCutoff profile) ?_
  apply listQSum_congr_on
  intro targetState htarget
  exact spinFourLoweringWholeSlabRawWeight_eqv_multiplicity_mul_physicalTerm
    S sourceState targetState
      ((mem_spinFourLoweringTargets_iff
        S sourceState targetState).mp htarget).1

/-- Accepted-endpoint form of the exact integer-tilted Gibbs normalization. -/
theorem wholeSlabJointRawRowMass_attachedEndpointSpinFour_eqv_multiplicityTiltedGibbs
    (S : SlabScalePair)
    (endpoint : SlabExpandedFineSourceEntry S.coarse)
    (hfineCutoff : S.fine.cutoff = 1) :
    wholeSlabJointRawRowMass S
        (attachedEndpointSpinFourFineState S endpoint) ≈
      listQSum
        (fun targetState =>
          Q'.ofNat
              (spinFourLoweringMultiplicityProduct
                S endpoint.1.1 targetState) *
            S.coarse.physicalTerm targetState)
        (spinFourLoweringTargets S endpoint.1.1) := by
  unfold wholeSlabJointRawRowMass
  exact wholeSlabRawRowMass_spinFourProfile_eqv_multiplicityTiltedGibbs
    S (attachedEndpointSpinFourFineState S endpoint) endpoint.1.1
      hfineCutoff
      (attachedEndpointSpinFourWholeSlabPacketProfile
        S endpoint hfineCutoff)

#print axioms spinFourTargetCoefficientProduct_eqv_coarseFaceFactor
#print axioms spinFourLoweringWholeSlabRawWeight_eqv_multiplicity_mul_physicalTerm
#print axioms wholeSlabRawRowMass_spinFourProfile_eqv_multiplicityTiltedGibbs
#print axioms wholeSlabJointRawRowMass_attachedEndpointSpinFour_eqv_multiplicityTiltedGibbs

end YMGap.Continuum.Z4DyadicSpinFourLoweringGibbsTilt
