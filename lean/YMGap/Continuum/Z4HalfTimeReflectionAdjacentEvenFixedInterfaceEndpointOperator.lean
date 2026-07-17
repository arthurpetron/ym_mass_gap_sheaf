/-
# The finite adjacent-even fixed-interface endpoint operator

After the reflected endpoints have been identified with one common lower
half-amplitude map, the sole positivity residual is the operator between the
common fixed-link endpoint channels.  This file defines that operator
literally: fixed spatial face labels are summed once with their heat-kernel
coefficients, and for each such labelling all compatible incidence
trajectories are summed.

The second half audits sequential face composition at the first production
cutoff where distinct fusion matrices occur.  Two actual four-link face
blocks sharing one channel already fail to commute at the hard auxiliary
boundary for `K = 2`, `6*K = 12`.  The exact rational corner is nonsymmetric,
so this naive full-window sequential composition is not a Gram.  The fence
does not refute positivity after compression by the physically reachable
endpoint amplitudes; it shows that such a compression (or an untruncated
common-middle construction) is essential.
-/

import YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenReflectedEndpointAmplitude

namespace YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenFixedInterfaceEndpointOperator

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SchurHadamardTransfer
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenFixedFaceCoefficientAttachment
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenCrossPlaneGeometry
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenFixedIncidenceTrajectoryAssembly
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenFixedLinkEndpointFubini
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenJointFaceBlock
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenJointFaceSlabFubini
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenSlabIncidenceBridge
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4SpinDecoratedCrossVolumeWeights

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Literal production endpoint operator -/

/-- The fixed-interface operator on two concrete global fixed-link endpoint
channel assignments.  Every physical fixed-face label and every compatible
internal trajectory is summed exactly once. -/
def adjacentEvenFixedInterfaceEndpointKernel
    (K radius : Nat) (source target : Z4Link → Nat) : Q' :=
  listQSum (fun physical =>
    adjacentEvenFixedFaceCoefficientProduct K radius physical *
      listQSum (fun trajectory =>
        listQProduct (fun link =>
          adjacentEvenFixedIncidenceTrajectoryFactor
            radius physical source target link (trajectory link))
          (adjacentEvenFixedLinks radius))
        (adjacentEvenFixedIncidenceTrajectoryStates K radius))
    (boundedEdgeLabellings K (adjacentEvenFixedFaceIds radius))

/-- The literal finite list of common fixed-link endpoint coordinates. -/
def adjacentEvenFixedBoundaryChannelAssignments
    (K radius : Nat) : List (Z4Link → Nat) :=
  boundedLabellingsOn (linkAuxiliaryCutoff K)
    (adjacentEvenFixedLinks radius)

def adjacentEvenFixedBoundaryChannelAt
    (K radius index : Nat) : Z4Link → Nat :=
  (adjacentEvenFixedBoundaryChannelAssignments K radius).getD index
    (zeroLabellingOn : Z4Link → Nat)

/-- The production matrix indexed only by the common endpoint/source
coordinate. -/
def adjacentEvenFixedInterfaceEndpointMatrix
    (K radius left right : Nat) : Q' :=
  adjacentEvenFixedInterfaceEndpointKernel K radius
    (adjacentEvenFixedBoundaryChannelAt K radius left)
    (adjacentEvenFixedBoundaryChannelAt K radius right)

/-! ## 2. A literal two-face production patch at `K = 2` -/

/-- Seven open channels for two four-link faces sharing exactly the `shared`
channel and otherwise carrying three separate channels apiece. -/
structure TwoFacePatchChannels where
  shared : Nat
  firstA : Nat
  secondA : Nat
  thirdA : Nat
  firstB : Nat
  secondB : Nat
  thirdB : Nat
deriving DecidableEq

def twoFacePatchAChannels (state : TwoFacePatchChannels) : FourChannels :=
  ⟨state.shared, state.firstA, state.secondA, state.thirdA⟩

def twoFacePatchBChannels (state : TwoFacePatchChannels) : FourChannels :=
  ⟨state.shared, state.firstB, state.secondB, state.thirdB⟩

/-- Sequential composition of the two literal cutoff-two resummed face
blocks, with the common shared channel summed through the production window
`0,...,12`.  The other six channels are untouched by the opposite face. -/
def adjacentEvenTwoFaceProductionPatchKernel
    (left right : TwoFacePatchChannels) : Q' :=
  finSum (fun middle =>
    anchorJointFourResummedFaceKernel 2
        (twoFacePatchAChannels left)
        ⟨middle, right.firstA, right.secondA, right.thirdA⟩ *
      anchorJointFourResummedFaceKernel 2
        ⟨middle, left.firstB, left.secondB, left.thirdB⟩
        (twoFacePatchBChannels right)) 13

/-- The hard-boundary source: the shared channel is one below `6*K`, and the
three private channels force face A to carry spin one and face B spin two. -/
def twoFacePatchSource : TwoFacePatchChannels :=
  ⟨11, 0, 0, 0, 0, 0, 0⟩

def twoFacePatchTarget : TwoFacePatchChannels :=
  ⟨12, 1, 1, 1, 2, 2, 2⟩

def adjacentEvenTwoFaceProductionPatchTestState : Nat → TwoFacePatchChannels
  | 0 => twoFacePatchSource
  | _ => twoFacePatchTarget

def adjacentEvenTwoFaceProductionPatchMatrix
    (left right : Nat) : Q' :=
  adjacentEvenTwoFaceProductionPatchKernel
    (adjacentEvenTwoFaceProductionPatchTestState left)
    (adjacentEvenTwoFaceProductionPatchTestState right)

/-- Exact noncommuting production corner.  Forward order has two shared-link
paths while reverse order has one; all coefficients are the literal derived
anchor coefficients. -/
theorem adjacentEvenTwoFaceProductionPatch_not_symmetric :
    ¬ (adjacentEvenTwoFaceProductionPatchMatrix 0 1 ≈
      adjacentEvenTwoFaceProductionPatchMatrix 1 0) := by
  decide

private theorem gramRep_entry_symmetric
    {matrix : Nat → Nat → Q'} (rep : GramRep matrix)
    (left right : Nat) : matrix left right ≈ matrix right left := by
  refine Q'.eqv_trans _ _ _ (rep.hM left right) ?_
  refine Q'.eqv_trans _ _ _
    (finSum_eqv_congr _ _ (fun rank =>
      Q'.mul_eqv_congr_left (rep.d rank) _ _
        (Q'.mul_comm_eqv
          (rep.v rank left) (rep.v rank right))) rep.r) ?_
  exact Q'.eqv_symm (rep.hM right left)

/-- Therefore the literal two-face full-window sequential patch is not a
`GramRep`.  A proof for the whole slab cannot obtain `T` by blindly composing
the local face Grams on all `0,...,6*K` endpoint channels. -/
theorem adjacentEvenTwoFaceProductionPatch_not_gramRep :
    GramRep adjacentEvenTwoFaceProductionPatchMatrix → False :=
  fun rep => adjacentEvenTwoFaceProductionPatch_not_symmetric
    (gramRep_entry_symmetric rep 0 1)

/-! ## 3. The patch occurs in the literal smallest adjacent-even geometry -/

def adjacentEvenRadiusZeroPatchSharedLink : Z4Link :=
  (((0, 0, 0, 1), Dir4.x0) : Z4Link)

def adjacentEvenRadiusZeroPatchFaceA : Z4Plaq :=
  (((0, 0, 0, 1), Z4Plane.p01) : Z4Plaq)

def adjacentEvenRadiusZeroPatchFaceB : Z4Plaq :=
  (((0, 0, 0, 1), Z4Plane.p02) : Z4Plaq)

def adjacentEvenRadiusZeroPatchFaceAId : Nat := 6

def adjacentEvenRadiusZeroPatchFaceBId : Nat := 7

theorem adjacentEvenRadiusZeroPatchFaceA_fixed :
    adjacentEvenRadiusZeroPatchFaceAId ∈
      adjacentEvenFixedFaceIds 0 := by
  decide

theorem adjacentEvenRadiusZeroPatchFaceB_fixed :
    adjacentEvenRadiusZeroPatchFaceBId ∈
      adjacentEvenFixedFaceIds 0 := by
  decide

theorem adjacentEvenRadiusZeroPatchSharedLink_in_both_faces :
    adjacentEvenRadiusZeroPatchSharedLink ∈
        adjacentEvenFixedFaceLinks 0 adjacentEvenRadiusZeroPatchFaceAId ∧
      adjacentEvenRadiusZeroPatchSharedLink ∈
        adjacentEvenFixedFaceLinks 0 adjacentEvenRadiusZeroPatchFaceBId := by
  decide

theorem adjacentEvenRadiusZeroPatch_face_order :
    adjacentEvenRadiusZeroPatchFaceAId <
      adjacentEvenRadiusZeroPatchFaceBId := by
  decide

#print axioms adjacentEvenTwoFaceProductionPatch_not_symmetric
#print axioms adjacentEvenTwoFaceProductionPatch_not_gramRep
#print axioms adjacentEvenRadiusZeroPatchFaceA_fixed
#print axioms adjacentEvenRadiusZeroPatchFaceB_fixed
#print axioms adjacentEvenRadiusZeroPatchSharedLink_in_both_faces
#print axioms adjacentEvenRadiusZeroPatch_face_order

end YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenFixedInterfaceEndpointOperator
