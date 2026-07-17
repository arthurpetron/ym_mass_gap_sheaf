/-
# Joint-face Fubini and Gram for face-dependent link channels

Along a multi-fixed word, the channel on a shared link changes from one fixed
face to the next.  A global channel field must therefore depend on both the
fixed face ID and the link.  This file generalizes the duplicate-free joint-face
Fubini and Gram construction to that literal state type and specializes it to
the predecessor/post-channel fields of an incidence trajectory.
-/

import YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenTerminalDeltaCollapse

namespace YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenJointFaceDependentChannels

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.SchurHadamardTransfer
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenFixedIncidencePointwiseRegroup
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenFixedIncidenceTrajectoryAssembly
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenJointFaceBlock
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenJointFaceSlabFubini
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

abbrev FixedFaceChannelField := Nat → Z4Link → Nat

private theorem eliminateLinks_eqv_congr_on_local
    (left right : Nat → Q') : ∀ ids : List Nat,
    (∀ id, id ∈ ids → left id ≈ right id) →
      eliminateLinks left ids ≈ eliminateLinks right ids
  | [], _ => Q'.eqv_refl 1
  | head :: tail, hagree => by
      simp only [eliminateLinks]
      exact Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ _
          (hagree head List.mem_cons_self))
        (Q'.mul_eqv_congr_left _ _ _
          (eliminateLinks_eqv_congr_on_local left right tail
            (fun id hid => hagree id
              (List.mem_cons_of_mem head hid))))

/-! ## 1. Literal face-dependent fixed-label sum -/

def dependentFixedFaceLabelFactor
    (cutoff radius : Nat)
    (incoming outgoing : FixedFaceChannelField)
    (id spin : Nat) : Q' :=
  coeffAt (heatKernelPacket cutoff anchorCoupling) spin *
    fourFusionIndicator
      (fixedFaceFourChannels radius id (incoming id)) spin
      (fixedFaceFourChannels radius id (outgoing id))

def adjacentEvenGlobalDependentFixedFaceChannelKernel
    (cutoff radius : Nat)
    (incoming outgoing : FixedFaceChannelField) : Q' :=
  listQSum (fun boundary =>
    eliminateLinks (fun id =>
      dependentFixedFaceLabelFactor cutoff radius
        incoming outgoing id (boundary id))
      (adjacentEvenFixedFaceIds radius))
    (boundedEdgeLabellings cutoff
      (adjacentEvenFixedFaceIds radius))

def adjacentEvenDependentFixedFaceBlockProduct
    (cutoff radius : Nat)
    (incoming outgoing : FixedFaceChannelField) : Q' :=
  eliminateLinks (fun id =>
    anchorJointFourResummedFaceKernel cutoff
      (fixedFaceFourChannels radius id (incoming id))
      (fixedFaceFourChannels radius id (outgoing id)))
    (adjacentEvenFixedFaceIds radius)

/-- Exact global Fubini with channels allowed to vary at every fixed face. -/
theorem adjacentEvenGlobalDependentFixedFaceChannelKernel_eqv_blockProduct
    (cutoff radius : Nat)
    (incoming outgoing : FixedFaceChannelField) :
    adjacentEvenGlobalDependentFixedFaceChannelKernel
        cutoff radius incoming outgoing ≈
      adjacentEvenDependentFixedFaceBlockProduct
        cutoff radius incoming outgoing := by
  unfold adjacentEvenGlobalDependentFixedFaceChannelKernel
    adjacentEvenDependentFixedFaceBlockProduct
  refine Q'.eqv_trans _ _ _
    (boundedLabelling_product_fubini cutoff
      (dependentFixedFaceLabelFactor cutoff radius incoming outgoing)
      (adjacentEvenFixedFaceIds radius)
      (adjacentEvenFixedFaceIds_nodup radius)) ?_
  apply eliminateLinks_eqv_congr_on_local
  intro id _
  unfold dependentFixedFaceLabelFactor
    anchorJointFourResummedFaceKernel
  exact Q'.eqv_symm
    (listQSum_range_eq_fsum
      (fun spin =>
        coeffAt (heatKernelPacket cutoff anchorCoupling) spin *
          fourFusionIndicator
            (fixedFaceFourChannels radius id (incoming id)) spin
            (fixedFaceFourChannels radius id (outgoing id)))
      (cutoff + 1))

/-! ## 2. Explicit face-dependent Gram carrier -/

def dependentFixedFaceListMatrix
    (faceCutoff radius : Nat) (ids : List Nat)
    (channelState : Nat → FixedFaceChannelField)
    (left right : Nat) : Q' :=
  eliminateLinks (fun id =>
    anchorJointFourResummedFaceKernel faceCutoff
      (fixedFaceFourChannels radius id (channelState left id))
      (fixedFaceFourChannels radius id (channelState right id))) ids

def dependentFixedFaceListGramRep
    (faceCutoff channelCutoff radius : Nat)
    (channelState : Nat → FixedFaceChannelField)
    (hchannel : ∀ configuration id link,
      channelState configuration id link ≤ channelCutoff) :
    ∀ ids : List Nat,
      GramRep (dependentFixedFaceListMatrix
        faceCutoff radius ids channelState)
  | [] => onesGramRep
  | head :: tail =>
      schur_product
        (anchorJointFourProductionGramRep
          faceCutoff channelCutoff
          (fun configuration =>
            fixedFaceFourChannels radius head
              (channelState configuration head))
          (fun configuration =>
            fixedFaceFourChannels_mem_fourChannelSpace
              (hchannel configuration head)))
        (dependentFixedFaceListGramRep
          faceCutoff channelCutoff radius channelState hchannel tail)

def adjacentEvenGlobalDependentFixedFaceChannelMatrix
    (faceCutoff radius : Nat)
    (channelState : Nat → FixedFaceChannelField)
    (left right : Nat) : Q' :=
  adjacentEvenGlobalDependentFixedFaceChannelKernel
    faceCutoff radius (channelState left) (channelState right)

/-- Explicit Gram representation of the literal global fixed-face label sum
on face-dependent channel fields. -/
def adjacentEvenGlobalDependentFixedFaceChannelGramRep
    (faceCutoff channelCutoff radius : Nat)
    (channelState : Nat → FixedFaceChannelField)
    (hchannel : ∀ configuration id link,
      channelState configuration id link ≤ channelCutoff) :
    GramRep (adjacentEvenGlobalDependentFixedFaceChannelMatrix
      faceCutoff radius channelState) := by
  let rep := dependentFixedFaceListGramRep
    faceCutoff channelCutoff radius channelState hchannel
    (adjacentEvenFixedFaceIds radius)
  exact {
    r := rep.r
    d := rep.d
    hd := rep.hd
    v := rep.v
    hM := fun left right =>
      Q'.eqv_trans _ _ _
        (adjacentEvenGlobalDependentFixedFaceChannelKernel_eqv_blockProduct
          faceCutoff radius (channelState left) (channelState right))
        (rep.hM left right)
  }

def adjacentEvenProductionDependentFixedFaceChannelGramRep
    (K radius : Nat)
    (channelState : Nat → FixedFaceChannelField)
    (hchannel : ∀ configuration id link,
      channelState configuration id link ≤ linkAuxiliaryCutoff K) :
    GramRep (adjacentEvenGlobalDependentFixedFaceChannelMatrix
      K radius channelState) :=
  adjacentEvenGlobalDependentFixedFaceChannelGramRep
    K (linkAuxiliaryCutoff K) radius channelState hchannel

/-! ## 3. The actual predecessor/post-channel specialization -/

def adjacentEvenTrajectoryIncomingField
    (radius : Nat) (source : Z4Link → Nat)
    (trajectory : FixedIncidenceTrajectoryState) :
    FixedFaceChannelField :=
  fun id link => adjacentEvenIncidenceIncomingChannel
    radius source trajectory (id, link)

def adjacentEvenTrajectoryOutgoingField
    (trajectory : FixedIncidenceTrajectoryState) :
    FixedFaceChannelField :=
  fun id link => trajectory link id

def adjacentEvenTrajectoryFixedFaceResummedKernel
    (K radius : Nat) (source : Z4Link → Nat)
    (trajectory : FixedIncidenceTrajectoryState) : Q' :=
  adjacentEvenGlobalDependentFixedFaceChannelKernel K radius
    (adjacentEvenTrajectoryIncomingField radius source trajectory)
    (adjacentEvenTrajectoryOutgoingField trajectory)

theorem adjacentEvenTrajectoryFixedFaceResummedKernel_eqv_blockProduct
    (K radius : Nat) (source : Z4Link → Nat)
    (trajectory : FixedIncidenceTrajectoryState) :
    adjacentEvenTrajectoryFixedFaceResummedKernel
        K radius source trajectory ≈
      adjacentEvenDependentFixedFaceBlockProduct K radius
        (adjacentEvenTrajectoryIncomingField radius source trajectory)
        (adjacentEvenTrajectoryOutgoingField trajectory) :=
  adjacentEvenGlobalDependentFixedFaceChannelKernel_eqv_blockProduct
    K radius _ _

/-- Concrete non-vacuity of the generalized production Gram hypothesis. -/
def adjacentEvenZeroDependentChannelState :
    Nat → FixedFaceChannelField := fun _ _ _ => 0

def adjacentEvenZeroProductionDependentFixedFaceChannelGramRep
    (K radius : Nat) :
    GramRep (adjacentEvenGlobalDependentFixedFaceChannelMatrix
      K radius adjacentEvenZeroDependentChannelState) :=
  adjacentEvenProductionDependentFixedFaceChannelGramRep
    K radius adjacentEvenZeroDependentChannelState
    (fun _ _ _ => Nat.zero_le _)

#print axioms adjacentEvenGlobalDependentFixedFaceChannelKernel_eqv_blockProduct
#print axioms dependentFixedFaceListGramRep
#print axioms adjacentEvenGlobalDependentFixedFaceChannelGramRep
#print axioms adjacentEvenProductionDependentFixedFaceChannelGramRep
#print axioms adjacentEvenTrajectoryFixedFaceResummedKernel_eqv_blockProduct
#print axioms adjacentEvenZeroProductionDependentFixedFaceChannelGramRep

end YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenJointFaceDependentChannels
