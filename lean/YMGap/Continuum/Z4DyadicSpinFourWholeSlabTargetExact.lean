/-
# Exact whole-slab weight at the canonical spin-four target

The canonical dyadic spin-zero-through-four support is evaluated here at its
intended complete coarse endpoint.  On every coarse face, maximal retained
spin selects the unique stretched internal channel, so the exact fine-face
sum is the corresponding coarse heat-kernel coefficient.  Multiplying these
identities over every face and retaining the same globally glued coarse-link
multiplicity proves equality with the complete coarse physical summand.

This is a simultaneous multi-face statement: all interacting pair bubbles
are retained at once and evaluated at one globally accepted closed target.
It does not claim that individual bubbles can be deleted from an arbitrary
background, nor that the complete normalized row is already the coarse Gibbs
measure.

Constructive contract: finite list products, exact rational equivalence, and
the explicit SU(2) fusion rules only; no `Classical`, choice, `native_decide`,
proof hole, noncomputable declaration, trusted external computation, or new
axiom.
-/

import YMGap.Continuum.Z4DyadicSpinFourFixedFinalExact
import YMGap.Continuum.Z4DyadicSpinFourEndpointLift
import YMGap.Continuum.Z4DyadicLiteralPairBubbleWholeSlabRawContraction

namespace YMGap.Continuum.Z4DyadicSpinFourWholeSlabTargetExact

set_option autoImplicit false
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverAssignmentSaturatedEndpointLiftCoverage
open YMGap.Continuum.CompactDualSlabBinarySupportLinkCoherence
open YMGap.Continuum.CompactDualSlabObservablePairedFaceSwitchAssignment
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.CompactDualWholeSlabRecouplingRawKernel
open YMGap.Continuum.CompactDualCutoffOnePositivePhysicalClosure
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4DyadicLiteralPairBubbleWholeSlabRawContraction
open YMGap.Continuum.Z4DyadicPairBubbleWholeSlabRawContraction
open YMGap.Continuum.Z4DyadicSpinFourEndpointLift
open YMGap.Continuum.Z4DyadicSpinFourFixedFinalExact
open YMGap.Continuum.Z4DyadicSpinFourXorAssembly
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. A reusable exact packet profile -/

/-- Every physical coarse face sees the canonical ordered binary packet for
its retained spin, and every such spin lies in the spin-four range. -/
structure SpinFourWholeSlabPacketProfile
    (S : SlabScalePair) (fineState coarseState : EdgeLabelling) : Prop where
  packet_eq : ∀ faceId, faceId ∈ S.coarse.faceEdges →
    wholeSlabFinePacket S fineState faceId =
      spinFourPacket (coarseState faceId)
  spin_le_four : ∀ faceId, faceId ∈ S.coarse.faceEdges →
    coarseState faceId ≤ 4

/-- Exact heat-kernel coefficient on one face of a spin-four packet profile. -/
theorem wholeSlabFaceRawWeight_spinFourProfile_eqv_heatCoefficient
    (S : SlabScalePair) (fineState coarseState : EdgeLabelling)
    (hfineCutoff : S.fine.cutoff = 1)
    (profile : SpinFourWholeSlabPacketProfile S fineState coarseState)
    (faceId : Nat) (hface : faceId ∈ S.coarse.faceEdges) :
    wholeSlabFaceRawWeight S fineState coarseState faceId ≈
      coeffAt (heatKernelPacket S.coarse.cutoff S.coarse.coupling)
        (coarseState faceId) := by
  have hspin := profile.spin_le_four faceId hface
  have hlocal :
      wholeSlabFaceRawWeight S fineState coarseState faceId ≈
        coeffW S.coarse.coupling (coarseState faceId) :=
    Q'.eqv_trans _ _ _
      (wholeSlabFaceRawWeight_eqv_fixedFinal_of_packet_eq
        S fineState coarseState faceId
        (spinFourPacket (coarseState faceId)) hfineCutoff
        (profile.packet_eq faceId hface))
      (spinFourPacket_fixedFinalFaceRawWeight_eqv_coeffW
        S.coarse.coupling hspin)
  have hwithin : coarseState faceId < S.coarse.cutoff + 1 := by
    rw [S.coarse_cutoff, hfineCutoff]
    omega
  exact Q'.eqv_trans _ _ _ hlocal
    (Q'.eqv_symm
      (Q'.eqv_of_eq (coeffAt_heatKernelPacket hwithin)))

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

private theorem wholeSlabFiniteQProduct_eq_eliminateLinks_local
    (value : Nat → Q') : ∀ items : List Nat,
    wholeSlabFiniteQProduct value items = eliminateLinks value items
  | [] => rfl
  | _ :: tail => by
      simp only [wholeSlabFiniteQProduct, eliminateLinks]
      rw [wholeSlabFiniteQProduct_eq_eliminateLinks_local value tail]

/-- The complete fine-face product at the intended target is exactly the
coarse heat-kernel face product. -/
theorem wholeSlabFaceRawProduct_spinFourProfile_eqv_coarseFaceFactor
    (S : SlabScalePair) (fineState coarseState : EdgeLabelling)
    (hfineCutoff : S.fine.cutoff = 1)
    (profile : SpinFourWholeSlabPacketProfile S fineState coarseState) :
    wholeSlabFaceRawProduct S fineState coarseState ≈
      slabParametricKPhysicalFaceFactor S.coarse.coupling
        S.coarse.cutoff S.coarse.extent coarseState := by
  let coarseCoefficient : Nat → Q' := fun faceId =>
    coeffAt (heatKernelPacket S.coarse.cutoff S.coarse.coupling)
      (coarseState faceId)
  refine Q'.eqv_trans _
    (wholeSlabFiniteQProduct coarseCoefficient S.coarse.faceEdges) _
    (Q'.eqv_trans _ _ _
      (wholeSlabFaceRawProduct_eqv_finiteQProduct
        S fineState coarseState)
      (wholeSlabFiniteQProduct_congr_on_local _ _
        S.coarse.faceEdges (fun faceId hface =>
          wholeSlabFaceRawWeight_spinFourProfile_eqv_heatCoefficient
            S fineState coarseState hfineCutoff profile faceId hface))) ?_
  unfold slabParametricKPhysicalFaceFactor SlabPhysicalData.faceEdges
  exact Q'.eqv_of_eq
    (wholeSlabFiniteQProduct_eq_eliminateLinks_local
      coarseCoefficient (slabPhysicalFaceEdges S.coarse.extent))

/-- The complete globally link-glued raw kernel value at a spin-four profile
is the literal coarse physical summand. -/
theorem wholeSlabRecouplingRawWeight_spinFourProfile_eqv_physicalTerm
    (S : SlabScalePair) (fineState coarseState : EdgeLabelling)
    (hfineCutoff : S.fine.cutoff = 1)
    (profile : SpinFourWholeSlabPacketProfile S fineState coarseState) :
    wholeSlabRecouplingRawWeight S fineState coarseState ≈
      S.coarse.physicalTerm coarseState := by
  unfold wholeSlabRecouplingRawWeight SlabPhysicalData.physicalTerm
    slabParametricKPhysicalTerm
  exact Q'.mul_eqv_congr_right _ _ _
    (wholeSlabFaceRawProduct_spinFourProfile_eqv_coarseFaceFactor
      S fineState coarseState hfineCutoff profile)

/-! ## 2. Instantiate the profile for every accepted coarse endpoint -/

/-- The explicit finite support underlying the canonical spin-four endpoint
lift. -/
def attachedEndpointSpinFourFineSupport
    (S : SlabScalePair)
    (endpoint : SlabExpandedFineSourceEntry S.coarse) : List Z4Plaq :=
  dyadicSpinFourSupport (attachedEndpointCarrier S)
    (attachedEndpointSpin S endpoint)

/-- The literal cutoff-one fine physical labelling encoded by the canonical
spin-four support. -/
def attachedEndpointSpinFourFineState
    (S : SlabScalePair)
    (endpoint : SlabExpandedFineSourceEntry S.coarse) : EdgeLabelling :=
  slabBinarySupportLabelling S.fine.extent
    (attachedEndpointSpinFourFineSupport S endpoint)

theorem attachedEndpointSpinFourFineSupport_subset
    (S : SlabScalePair)
    (endpoint : SlabExpandedFineSourceEntry S.coarse) :
    ∀ fine, fine ∈ attachedEndpointSpinFourFineSupport S endpoint →
      fine ∈ boundaryCompleteSlabPlaquettes S.fine.extent := by
  have hbubbles := pairBubbleSlabAdmissible_of_selectedMargin
    (attachedEndpointCarrier_self_subset S)
    (attachedEndpointSelectedPairBubbleCoarseMargin endpoint)
  intro fine hfine
  rw [S.fine_extent]
  exact dyadicSpinFourSupport_subset_boundaryCompleteFineSlab
    (attachedEndpointCarrier_self_subset S) hbubbles fine
    (by
      simpa only [attachedEndpointSpinFourFineSupport] using hfine)

/-- The explicit canonical fine support is an actual member of the fine
cutoff-one physical state list. -/
theorem attachedEndpointSpinFourFineState_mem
    (S : SlabScalePair)
    (endpoint : SlabExpandedFineSourceEntry S.coarse)
    (hfineCutoff : S.fine.cutoff = 1) :
    attachedEndpointSpinFourFineState S endpoint ∈
      S.fine.physicalLabellings := by
  unfold attachedEndpointSpinFourFineState
  exact slabBinarySupportLabelling_mem (by omega) _

/-- Every coarse face of the explicit endpoint support has exactly its
canonical ordered spin-four packet. -/
theorem attachedEndpointSpinFourFineState_packet_eq
    (S : SlabScalePair)
    (endpoint : SlabExpandedFineSourceEntry S.coarse)
    (hfineCutoff : S.fine.cutoff = 1)
    (faceId : Nat) (hface : faceId ∈ S.coarse.faceEdges) :
    wholeSlabFinePacket S
        (attachedEndpointSpinFourFineState S endpoint) faceId =
      spinFourPacket (endpoint.1.1 faceId) := by
  have hphysical :
      faceId ∈ slabPhysicalFaceEdges S.coarse.extent := by
    simpa only [SlabPhysicalData.faceEdges] using hface
  have hquery :
      slabPlaquetteAt S.coarse.extent faceId ∈
        attachedEndpointCarrier S :=
    slabPlaquetteAt_mem hphysical
  have hspinBound :
      attachedEndpointSpin S endpoint
          (slabPlaquetteAt S.coarse.extent faceId) ≤ 4 := by
    have hbound :=
      SlabExpandedFineSourceEntry.physical_bounded endpoint faceId hface
    rw [S.coarse_cutoff, hfineCutoff] at hbound
    unfold attachedEndpointSpin
    rw [slabSpinAtPlaquette_slabPlaquetteAt
      S.coarse.extent endpoint.1.1 hphysical]
    omega
  have hread := slabSpinAtPlaquette_binarySupport_eq_supportCoefficient
    (attachedEndpointSpinFourFineSupport_subset S endpoint)
  unfold wholeSlabFinePacket attachedEndpointSpinFourFineState
  rw [hread]
  unfold attachedEndpointSpinFourFineSupport
  rw [supportCoefficient_dyadicSpinFourSupport]
  have hpacket := dyadicFaceSpinPacket_dyadicSpinFourCoefficient
    (attachedEndpointCarrier_nodup S)
    (attachedEndpointSpin S endpoint) hquery hspinBound
  have hspinEq :
      attachedEndpointSpin S endpoint
          (slabPlaquetteAt S.coarse.extent faceId) =
        endpoint.1.1 faceId := by
    unfold attachedEndpointSpin
    exact slabSpinAtPlaquette_slabPlaquetteAt
      S.coarse.extent endpoint.1.1 hphysical
  exact hpacket.trans (congrArg spinFourPacket hspinEq)

/-- Every accepted coarse endpoint supplies a concrete canonical packet
profile with no additional geometric hypothesis. -/
def attachedEndpointSpinFourWholeSlabPacketProfile
    (S : SlabScalePair)
    (endpoint : SlabExpandedFineSourceEntry S.coarse)
    (hfineCutoff : S.fine.cutoff = 1) :
    SpinFourWholeSlabPacketProfile S
      (attachedEndpointSpinFourFineState S endpoint) endpoint.1.1 where
  packet_eq := attachedEndpointSpinFourFineState_packet_eq
    S endpoint hfineCutoff
  spin_le_four := by
    intro faceId hface
    have hbound :=
      SlabExpandedFineSourceEntry.physical_bounded endpoint faceId hface
    rw [S.coarse_cutoff, hfineCutoff] at hbound
    omega

/-- Exact simultaneous multi-face preservation at every accepted endpoint:
the constructed cutoff-one fine source contributes precisely the complete
coarse physical weight at that endpoint. -/
theorem wholeSlabRecouplingRawWeight_attachedEndpointSpinFour_eqv_physicalTerm
    (S : SlabScalePair)
    (endpoint : SlabExpandedFineSourceEntry S.coarse)
    (hfineCutoff : S.fine.cutoff = 1) :
    wholeSlabRecouplingRawWeight S
        (attachedEndpointSpinFourFineState S endpoint) endpoint.1.1 ≈
      S.coarse.physicalTerm endpoint.1.1 :=
  wholeSlabRecouplingRawWeight_spinFourProfile_eqv_physicalTerm
    S (attachedEndpointSpinFourFineState S endpoint) endpoint.1.1
      hfineCutoff
      (attachedEndpointSpinFourWholeSlabPacketProfile
        S endpoint hfineCutoff)

#print axioms SpinFourWholeSlabPacketProfile
#print axioms wholeSlabFaceRawWeight_spinFourProfile_eqv_heatCoefficient
#print axioms wholeSlabFaceRawProduct_spinFourProfile_eqv_coarseFaceFactor
#print axioms wholeSlabRecouplingRawWeight_spinFourProfile_eqv_physicalTerm
#print axioms attachedEndpointSpinFourFineSupport_subset
#print axioms attachedEndpointSpinFourFineState_mem
#print axioms attachedEndpointSpinFourFineState_packet_eq
#print axioms attachedEndpointSpinFourWholeSlabPacketProfile
#print axioms wholeSlabRecouplingRawWeight_attachedEndpointSpinFour_eqv_physicalTerm

end YMGap.Continuum.Z4DyadicSpinFourWholeSlabTargetExact
