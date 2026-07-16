/-
# Global fine-support projector for the six-face slot fibre

At cutoff one with one fundamental fine face above each coarse cube face,
the missing recoupling coordinate is the choice of one of four corrected-slab
preimages on every face.  This file enumerates all `4^6 = 4096` choices with
no duplicates and tests global fine closure on the literal selected support:
every touched fine link must have even incidence.

The Boolean test is geometric; its classification is then computed in the
kernel.  Exactly two assignments survive: the odd fine unit cube at fine time
zero and its corrected-slab reflected copy at fine time one.  The all-zero
slot source is rejected by the previously audited incidence-one fence.

Finally the positive compatible cube raw weights are normalized only over
this projected carrier.  This repairs the source-support defect of the coarse
six-face law in the one-fundamental slot sector.  It does not yet classify or
normalize arbitrary multi-spin packets.
-/

import YMGap.Continuum.Z4DyadicSlabCubePhysicalSummandBridge

namespace YMGap.Continuum.Z4DyadicSlabCubeFineSupportProjectedKernel

set_option maxRecDepth 100000
set_option maxHeartbeats 12000000

open YMGap.Constructive
open YMGap.Continuum.BddLatticeAnimal
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4CutoffOneLocalMultiplicityCount
open YMGap.Continuum.Z4DyadicModTwoCellularKernel
open YMGap.Continuum.Z4DyadicSlabCharacterFusionConditionalKernel
open YMGap.Continuum.Z4DyadicSlabCubeCoupledConditionalKernel
open YMGap.Continuum.Z4DyadicSlabCubePhysicalSummandBridge
open YMGap.Continuum.Z4DyadicSlabMultiCharacterPacketKernel
open YMGap.Continuum.Z4DyadicSlabTwoFaceCoupledConditionalKernel
open YMGap.Continuum.Z4DyadicUnitCubeBlockGeometry
open YMGap.Continuum.Z4DyadicSU2ParityMinimalLiftFence
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local infix:50 " ≈ " => Q'.eqv

private theorem listQSum_member_le_local {A : Type}
    (value : A → Q') (hvalue : ∀ x, (0 : Q') ≤ value x) :
    ∀ (xs : List A) {x : A}, x ∈ xs →
      value x ≤ listQSum value xs
  | [], _, hmem => absurd hmem List.not_mem_nil
  | head :: tail, x, hmem => by
      rcases List.mem_cons.mp hmem with hhead | htail
      · subst x
        exact Q'.add_le_self_of_nonneg (value head)
          (listQSum value tail)
          (listQSum_nonnegative_on value tail
            (fun y _ => hvalue y))
      · have ih := listQSum_member_le_local value hvalue tail htail
        have hmono : listQSum value tail ≤
            value head + listQSum value tail := by
          have hle := Q'.add_le_add_right
            (0 : Q') (value head) (listQSum value tail) (hvalue head)
          rwa [Q'.zero_add'] at hle
        exact Q'.le_trans' _ _ _ ih hmono

/-! ## 1. Four slots on each of six faces -/

inductive FineFaceSlot
  | slot0
  | slot1
  | slot2
  | slot3
  deriving DecidableEq

def fineFaceSlots : List FineFaceSlot :=
  [.slot0, .slot1, .slot2, .slot3]

theorem fineFaceSlots_nodup : fineFaceSlots.Nodup := by
  simp [fineFaceSlots]

def fineFaceSlotIndex : FineFaceSlot → Nat
  | .slot0 => 0
  | .slot1 => 1
  | .slot2 => 2
  | .slot3 => 3

/-- Six slots in cube-face order: bottom, top, front, back, left, right. -/
abbrev CubeFineSlotAssignment :=
  FineFaceSlot ×
    (FineFaceSlot ×
      (FineFaceSlot ×
        (FineFaceSlot × (FineFaceSlot × FineFaceSlot))))

def cubeFineSlotAt
    (assignment : CubeFineSlotAssignment) : CubeFaceIndex → FineFaceSlot
  | .bottomXY => assignment.1
  | .topXY => assignment.2.1
  | .frontXZ => assignment.2.2.1
  | .backXZ => assignment.2.2.2.1
  | .leftYZ => assignment.2.2.2.2.1
  | .rightYZ => assignment.2.2.2.2.2

def cubeFineSlotAssignmentStateSpace : List CubeFineSlotAssignment :=
  cartesian fineFaceSlots
    (cartesian fineFaceSlots
      (cartesian fineFaceSlots
        (cartesian fineFaceSlots (cartesian fineFaceSlots fineFaceSlots))))

theorem cubeFineSlotAssignmentStateSpace_nodup :
    cubeFineSlotAssignmentStateSpace.Nodup := by
  exact cartesian_nodup _ _ fineFaceSlots_nodup
    (cartesian_nodup _ _ fineFaceSlots_nodup
      (cartesian_nodup _ _ fineFaceSlots_nodup
        (cartesian_nodup _ _ fineFaceSlots_nodup
          (cartesian_nodup _ _ fineFaceSlots_nodup
            fineFaceSlots_nodup))))

theorem cubeFineSlotAssignmentStateSpace_length :
    cubeFineSlotAssignmentStateSpace.length = 4096 := by
  rfl

/-! ## 2. Literal fine support and global closure test -/

def cubeFineSlotPlaquette
    (assignment : CubeFineSlotAssignment)
    (face : CubeFaceIndex) : Z4Plaq :=
  (dyadicFacePreimages (cubeFace face)).getD
    (fineFaceSlotIndex (cubeFineSlotAt assignment face))
    fallbackPlaquette

def cubeFineSlotSupport
    (assignment : CubeFineSlotAssignment) : List Z4Plaq :=
  cubeFaceIndices.map (cubeFineSlotPlaquette assignment)

/-- Literal incidence checker used to audit the geometric projector below. -/
def cubeFineSlotIncidenceClosedB
    (assignment : CubeFineSlotAssignment) : Bool :=
  (geometricTouchedLinks (cubeFineSlotSupport assignment)).all
    (fun link => decide
      ((geometricIncidentPlaquettes
        (cubeFineSlotSupport assignment) link).length % 2 = 0))

def oddFineCubeSlotAssignment : CubeFineSlotAssignment :=
  (.slot1, (.slot0, (.slot1, (.slot0, (.slot1, .slot0)))))

def reflectedOddFineCubeSlotAssignment : CubeFineSlotAssignment :=
  (.slot3, (.slot2, (.slot3, (.slot2, (.slot3, .slot2)))))

def zeroSlotCubeAssignment : CubeFineSlotAssignment :=
  (.slot0, (.slot0, (.slot0, (.slot0, (.slot0, .slot0)))))

/-- The bit transverse to the selected coarse face within its corrected-slab
four-fibre. -/
def fineFaceSlotTransverseB : FineFaceSlot → Bool
  | .slot0 => false
  | .slot1 => true
  | .slot2 => false
  | .slot3 => true

/-- The fine-time bit within a corrected-slab four-fibre. -/
def fineFaceSlotTimeB : FineFaceSlot → Bool
  | .slot0 => false
  | .slot1 => false
  | .slot2 => true
  | .slot3 => true

def sameFineFaceSlotTimeB
    (left right : FineFaceSlot) : Bool :=
  decide (fineFaceSlotTimeB left = fineFaceSlotTimeB right)

/-- Global geometric closure predicate.  The lower face in each spatial
direction must use transverse bit one, the upper face transverse bit zero,
and all six selected plaquettes must lie at the same fine time.  These are
the literal boundary-matching equations for a fine unit cube. -/
def cubeFineSlotClosedB (assignment : CubeFineSlotAssignment) : Bool :=
  fineFaceSlotTransverseB (cubeFineSlotAt assignment .bottomXY) &&
  !fineFaceSlotTransverseB (cubeFineSlotAt assignment .topXY) &&
  fineFaceSlotTransverseB (cubeFineSlotAt assignment .frontXZ) &&
  !fineFaceSlotTransverseB (cubeFineSlotAt assignment .backXZ) &&
  fineFaceSlotTransverseB (cubeFineSlotAt assignment .leftYZ) &&
  !fineFaceSlotTransverseB (cubeFineSlotAt assignment .rightYZ) &&
  sameFineFaceSlotTimeB
    (cubeFineSlotAt assignment .bottomXY)
    (cubeFineSlotAt assignment .topXY) &&
  sameFineFaceSlotTimeB
    (cubeFineSlotAt assignment .bottomXY)
    (cubeFineSlotAt assignment .frontXZ) &&
  sameFineFaceSlotTimeB
    (cubeFineSlotAt assignment .bottomXY)
    (cubeFineSlotAt assignment .backXZ) &&
  sameFineFaceSlotTimeB
    (cubeFineSlotAt assignment .bottomXY)
    (cubeFineSlotAt assignment .leftYZ) &&
  sameFineFaceSlotTimeB
    (cubeFineSlotAt assignment .bottomXY)
    (cubeFineSlotAt assignment .rightYZ)

theorem oddFineCubeSlotAssignment_mem :
    oddFineCubeSlotAssignment ∈ cubeFineSlotAssignmentStateSpace := by
  simp [oddFineCubeSlotAssignment, cubeFineSlotAssignmentStateSpace,
    fineFaceSlots, mem_cartesian_iff]

theorem reflectedOddFineCubeSlotAssignment_mem :
    reflectedOddFineCubeSlotAssignment ∈
      cubeFineSlotAssignmentStateSpace := by
  simp [reflectedOddFineCubeSlotAssignment,
    cubeFineSlotAssignmentStateSpace, fineFaceSlots, mem_cartesian_iff]

theorem zeroSlotCubeAssignment_mem :
    zeroSlotCubeAssignment ∈ cubeFineSlotAssignmentStateSpace := by
  simp [zeroSlotCubeAssignment, cubeFineSlotAssignmentStateSpace,
    fineFaceSlots, mem_cartesian_iff]

def cubeOrderedOddFineSurface : List Z4Plaq :=
  [((1, 1, 1, 0), .p01),
    ((1, 1, 2, 0), .p01),
    ((1, 1, 1, 0), .p02),
    ((1, 2, 1, 0), .p02),
    ((1, 1, 1, 0), .p12),
    ((2, 1, 1, 0), .p12)]

theorem oddFineCubeSlotSupport_eq :
    cubeFineSlotSupport oddFineCubeSlotAssignment =
      cubeOrderedOddFineSurface := by
  simp [cubeFineSlotSupport, cubeFineSlotPlaquette,
    oddFineCubeSlotAssignment, cubeFineSlotAt, fineFaceSlotIndex,
    cubeFaceIndices, cubeFace, dyadicFacePreimages,
    cubeOrderedOddFineSurface]

theorem cubeOrderedOddFineSurface_sameSupport :
    sameSupport (L := z4Chain.toLattice)
      cubeOrderedOddFineSurface oddFineUnitCubeSurface := by
  constructor
  · intro plaquette hplaquette
    unfold cubeOrderedOddFineSurface at hplaquette
    rcases List.mem_cons.mp hplaquette with rfl | hplaquette
    · unfold oddFineUnitCubeSurface
      exact List.mem_cons_self
    rcases List.mem_cons.mp hplaquette with rfl | hplaquette
    · unfold oddFineUnitCubeSurface
      exact List.mem_cons_of_mem _
        (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ List.mem_cons_self))
    rcases List.mem_cons.mp hplaquette with rfl | hplaquette
    · unfold oddFineUnitCubeSurface
      exact List.mem_cons_of_mem _ List.mem_cons_self
    rcases List.mem_cons.mp hplaquette with rfl | hplaquette
    · unfold oddFineUnitCubeSurface
      exact List.mem_cons_of_mem _
        (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _
            (List.mem_cons_of_mem _ List.mem_cons_self)))
    rcases List.mem_cons.mp hplaquette with rfl | hplaquette
    · unfold oddFineUnitCubeSurface
      exact List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ List.mem_cons_self)
    have hlast := List.mem_singleton.mp hplaquette
    subst plaquette
    unfold oddFineUnitCubeSurface
    exact List.mem_cons_of_mem _
      (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _
            (List.mem_cons_of_mem _ List.mem_cons_self))))
  · intro plaquette hplaquette
    unfold oddFineUnitCubeSurface at hplaquette
    rcases List.mem_cons.mp hplaquette with rfl | hplaquette
    · unfold cubeOrderedOddFineSurface
      exact List.mem_cons_self
    rcases List.mem_cons.mp hplaquette with rfl | hplaquette
    · unfold cubeOrderedOddFineSurface
      exact List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ List.mem_cons_self)
    rcases List.mem_cons.mp hplaquette with rfl | hplaquette
    · unfold cubeOrderedOddFineSurface
      exact List.mem_cons_of_mem _
        (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _
            (List.mem_cons_of_mem _ List.mem_cons_self)))
    rcases List.mem_cons.mp hplaquette with rfl | hplaquette
    · unfold cubeOrderedOddFineSurface
      exact List.mem_cons_of_mem _ List.mem_cons_self
    rcases List.mem_cons.mp hplaquette with rfl | hplaquette
    · unfold cubeOrderedOddFineSurface
      exact List.mem_cons_of_mem _
        (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ List.mem_cons_self))
    have hlast := List.mem_singleton.mp hplaquette
    subst plaquette
    unfold cubeOrderedOddFineSurface
    exact List.mem_cons_of_mem _
      (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _
            (List.mem_cons_of_mem _ List.mem_cons_self))))

theorem zeroSlotCubeSupport_eq :
    cubeFineSlotSupport zeroSlotCubeAssignment =
      zeroPreimageCubeFineSupport := by
  rfl

def reflectedOddFineCubeSurface : List Z4Plaq :=
  [((1, 1, 1, 1), .p01),
    ((1, 1, 2, 1), .p01),
    ((1, 1, 1, 1), .p02),
    ((1, 2, 1, 1), .p02),
    ((1, 1, 1, 1), .p12),
    ((2, 1, 1, 1), .p12)]

theorem reflectedOddFineCubeSlotSupport_eq :
    cubeFineSlotSupport reflectedOddFineCubeSlotAssignment =
      reflectedOddFineCubeSurface := by
  simp [cubeFineSlotSupport, cubeFineSlotPlaquette,
    reflectedOddFineCubeSlotAssignment, cubeFineSlotAt,
    fineFaceSlotIndex, cubeFaceIndices, cubeFace, dyadicFacePreimages,
    reflectedOddFineCubeSurface]

theorem reflectedOddFineCubeSurface_eq_timeShift :
    reflectedOddFineCubeSurface =
      cubeOrderedOddFineSurface.map (timeShiftPlaquette 1) := by
  rfl

theorem oddFineCubeSlotClosed :
    cubeFineSlotClosedB oddFineCubeSlotAssignment = true := by
  rfl

theorem oddFineCubeSlotIncidenceClosed :
    cubeFineSlotIncidenceClosedB oddFineCubeSlotAssignment = true := by
  rfl

theorem reflectedOddFineCubeSlotClosed :
    cubeFineSlotClosedB reflectedOddFineCubeSlotAssignment = true := by
  rfl

theorem reflectedOddFineCubeSlotIncidenceClosed :
    cubeFineSlotIncidenceClosedB
      reflectedOddFineCubeSlotAssignment = true := by
  rfl

private theorem zeroPreimageCubeFenceLink_touched :
    zeroPreimageCubeFenceLink ∈
      geometricTouchedLinks zeroPreimageCubeFineSupport := by
  apply mem_geometricTouchedLinks.mpr
  refine ⟨((1, 1, 0, 0), .p01), ?_, ?_⟩
  · simp [zeroPreimageCubeFineSupport]
  · simp [zeroPreimageCubeFenceLink, edgesOf, dirsOf, addE]

theorem zeroSlotCubeRejected :
    cubeFineSlotClosedB zeroSlotCubeAssignment = false := by
  rfl

theorem zeroSlotCubeIncidenceRejected :
    cubeFineSlotIncidenceClosedB zeroSlotCubeAssignment = false := by
  unfold cubeFineSlotIncidenceClosedB
  rw [zeroSlotCubeSupport_eq]
  cases hclosed :
      (geometricTouchedLinks zeroPreimageCubeFineSupport).all
        (fun link => decide
          ((geometricIncidentPlaquettes
            zeroPreimageCubeFineSupport link).length % 2 = 0)) with
  | false => rfl
  | true =>
      have hfence := List.all_eq_true.mp hclosed
        zeroPreimageCubeFenceLink
        zeroPreimageCubeFenceLink_touched
      simp only [decide_eq_true_eq] at hfence
      rw [zeroPreimageCubeFineSupport_fence_incidence_one] at hfence
      omega

/-! ## 3. Exact 4096-state classification -/

def closedCubeFineSlotStateSpace : List CubeFineSlotAssignment :=
  cubeFineSlotAssignmentStateSpace.filter cubeFineSlotClosedB

theorem closedCubeFineSlotStateSpace_eq :
    closedCubeFineSlotStateSpace =
      [oddFineCubeSlotAssignment,
        reflectedOddFineCubeSlotAssignment] := by
  rfl

theorem closedCubeFineSlotStateSpace_length :
    closedCubeFineSlotStateSpace.length = 2 := by
  rw [closedCubeFineSlotStateSpace_eq]
  rfl

theorem closedCubeFineSlotStateSpace_nodup :
    closedCubeFineSlotStateSpace.Nodup :=
  List.filter_sublist.nodup cubeFineSlotAssignmentStateSpace_nodup

theorem oddFineCubeSlotAssignment_mem_closed :
    oddFineCubeSlotAssignment ∈ closedCubeFineSlotStateSpace := by
  rw [closedCubeFineSlotStateSpace_eq]
  exact List.mem_cons_self

theorem reflectedOddFineCubeSlotAssignment_mem_closed :
    reflectedOddFineCubeSlotAssignment ∈
      closedCubeFineSlotStateSpace := by
  rw [closedCubeFineSlotStateSpace_eq]
  exact List.mem_cons_of_mem _ List.mem_cons_self

theorem zeroSlotCubeAssignment_not_mem_closed :
    zeroSlotCubeAssignment ∉ closedCubeFineSlotStateSpace := by
  unfold closedCubeFineSlotStateSpace
  intro hmem
  have hparts := List.mem_filter.mp hmem
  rw [zeroSlotCubeRejected] at hparts
  exact Bool.false_eq_true.mp hparts.2

/-- Every source retained by the geometric slot projector passes the literal
fine-link incidence checker. -/
theorem mem_closedCubeFineSlotStateSpace_incidenceClosed
    {assignment : CubeFineSlotAssignment}
    (hassignment : assignment ∈ closedCubeFineSlotStateSpace) :
    cubeFineSlotIncidenceClosedB assignment = true := by
  rw [closedCubeFineSlotStateSpace_eq] at hassignment
  rcases List.mem_cons.mp hassignment with hodd | hreflected
  · subst assignment
    exact oddFineCubeSlotIncidenceClosed
  · have heq := List.mem_singleton.mp hreflected
    subst assignment
    exact reflectedOddFineCubeSlotIncidenceClosed

theorem mem_closedCubeFineSlotStateSpace_even_incidence
    {assignment : CubeFineSlotAssignment}
    (hassignment : assignment ∈ closedCubeFineSlotStateSpace)
    {link : Z4Link}
    (hlink : link ∈
      geometricTouchedLinks (cubeFineSlotSupport assignment)) :
    (geometricIncidentPlaquettes
      (cubeFineSlotSupport assignment) link).length % 2 = 0 := by
  have hclosed :=
    mem_closedCubeFineSlotStateSpace_incidenceClosed hassignment
  unfold cubeFineSlotIncidenceClosedB at hclosed
  have hlinkClosed := List.all_eq_true.mp hclosed link hlink
  simpa only [decide_eq_true_eq] using hlinkClosed

/-! ## 4. The slot assignment as a common-total cube source -/

def slotFundamentalPacket : FineFaceSlot → FaceSpinPacket
  | .slot0 => ⟨1, 0, 0, 0⟩
  | .slot1 => ⟨0, 1, 0, 0⟩
  | .slot2 => ⟨0, 0, 1, 0⟩
  | .slot3 => ⟨0, 0, 0, 1⟩

theorem slotFundamentalPacket_mem (slot : FineFaceSlot) :
    slotFundamentalPacket slot ∈ faceSpinPacketStateSpace 1 := by
  apply (mem_faceSpinPacketStateSpace_iff 1 _).mpr
  cases slot with
  | slot0 =>
      change (1 : Nat) ≤ 1 ∧ 0 ≤ 1 ∧ 0 ≤ 1 ∧ 0 ≤ 1
      exact ⟨Nat.le_refl 1, Nat.zero_le 1,
        Nat.zero_le 1, Nat.zero_le 1⟩
  | slot1 =>
      change (0 : Nat) ≤ 1 ∧ 1 ≤ 1 ∧ 0 ≤ 1 ∧ 0 ≤ 1
      exact ⟨Nat.zero_le 1, Nat.le_refl 1,
        Nat.zero_le 1, Nat.zero_le 1⟩
  | slot2 =>
      change (0 : Nat) ≤ 1 ∧ 0 ≤ 1 ∧ 1 ≤ 1 ∧ 0 ≤ 1
      exact ⟨Nat.zero_le 1, Nat.zero_le 1,
        Nat.le_refl 1, Nat.zero_le 1⟩
  | slot3 =>
      change (0 : Nat) ≤ 1 ∧ 0 ≤ 1 ∧ 0 ≤ 1 ∧ 1 ≤ 1
      exact ⟨Nat.zero_le 1, Nat.zero_le 1,
        Nat.zero_le 1, Nat.le_refl 1⟩

def slotFundamentalBoundedPacket
    (slot : FineFaceSlot) : BoundedFaceSpinPacket 1 :=
  ⟨slotFundamentalPacket slot, slotFundamentalPacket_mem slot⟩

theorem slotFundamentalPacket_total (slot : FineFaceSlot) :
    faceSpinTotal (slotFundamentalPacket slot) = 1 := by
  cases slot <;> rfl

def cubeFineSlotSource
    (assignment : CubeFineSlotAssignment) :
    CubeStretchedCompatibleSource 1 where
  packet := fun face =>
    slotFundamentalBoundedPacket (cubeFineSlotAt assignment face)
  commonTotal := 1
  total_eq := by
    intro face
    exact slotFundamentalPacket_total (cubeFineSlotAt assignment face)

theorem oddFineCubeSlotSource_packet_is_geometric
    (face : CubeFaceIndex) :
    dyadicFaceSpinPacket oddFineCubeGeometricSpin (cubeFace face) =
      (cubeFineSlotSource oddFineCubeSlotAssignment).packet face := by
  cases face <;> rfl

def reflectedOddFineCubeGeometricFaceB : Z4Plaq → Bool
  | ((1, 1, 1, 1), .p01) => true
  | ((1, 1, 1, 1), .p02) => true
  | ((1, 1, 1, 1), .p12) => true
  | ((1, 1, 2, 1), .p01) => true
  | ((1, 2, 1, 1), .p02) => true
  | ((2, 1, 1, 1), .p12) => true
  | _ => false

def reflectedOddFineCubeGeometricSpin (plaquette : Z4Plaq) : Nat :=
  match reflectedOddFineCubeGeometricFaceB plaquette with
  | true => 1
  | false => 0

theorem reflectedOddFineCubeGeometricSpin_bounded (plaquette : Z4Plaq) :
    reflectedOddFineCubeGeometricSpin plaquette ≤ 1 := by
  unfold reflectedOddFineCubeGeometricSpin
  cases hface : reflectedOddFineCubeGeometricFaceB plaquette <;> simp

theorem reflectedOddFineCubeSlotSource_packet_is_geometric
    (face : CubeFaceIndex) :
    dyadicFaceSpinPacket reflectedOddFineCubeGeometricSpin
        (cubeFace face) =
      (cubeFineSlotSource
        reflectedOddFineCubeSlotAssignment).packet face := by
  cases face <;> rfl

/-! ## 5. Positive projected normalization -/

def closedCubeFineSlotRawWeight
    (w : Q') (assignment : CubeFineSlotAssignment) : Q' :=
  cubeCoupledRawWeight w 1 (cubeFineSlotSource assignment)
    (compatibleCubeTarget (cubeFineSlotSource assignment))

theorem closedCubeFineSlotRawWeight_nonnegative
    {w : Q'} (hw : (0 : Q') ≤ w)
    (assignment : CubeFineSlotAssignment) :
    (0 : Q') ≤ closedCubeFineSlotRawWeight w assignment := by
  unfold closedCubeFineSlotRawWeight
  exact cubeCoupledRawWeight_nonnegative hw 1
    (cubeFineSlotSource assignment)
    (compatibleCubeTarget (cubeFineSlotSource assignment))

def closedCubeFineSlotPartition (w : Q') : Q' :=
  listQSum (closedCubeFineSlotRawWeight w)
    closedCubeFineSlotStateSpace

theorem closedCubeFineSlotPartition_pos
    {w : Q'} (hw : (0 : Q') < w) :
    (0 : Q') < closedCubeFineSlotPartition w := by
  have hmember := listQSum_member_le_local
    (closedCubeFineSlotRawWeight w)
    (closedCubeFineSlotRawWeight_nonnegative (Q'.le_of_lt hw))
    closedCubeFineSlotStateSpace
    oddFineCubeSlotAssignment_mem_closed
  exact Q'.pos_of_lt_of_le
    (compatibleCubeRawWeight_pos hw 1
      (cubeFineSlotSource oddFineCubeSlotAssignment))
    hmember

def closedCubeFineSlotKernel
    (w : Q') (hw : (0 : Q') < w)
    (assignment : CubeFineSlotAssignment) : Q' :=
  Q'.divPos (closedCubeFineSlotRawWeight w assignment)
    (closedCubeFineSlotPartition w)
    (closedCubeFineSlotPartition_pos hw)

theorem closedCubeFineSlotKernel_nonnegative
    (w : Q') (hw : (0 : Q') < w)
    (assignment : CubeFineSlotAssignment) :
    (0 : Q') ≤ closedCubeFineSlotKernel w hw assignment := by
  unfold closedCubeFineSlotKernel Q'.divPos
  exact Q'.mul_nonneg _ _
    (closedCubeFineSlotRawWeight_nonnegative
      (Q'.le_of_lt hw) assignment)
    (Q'.le_of_lt (Q'.recipPos_pos _ _))

theorem closedCubeFineSlotKernel_row_normalized
    (w : Q') (hw : (0 : Q') < w) :
    listQSum (closedCubeFineSlotKernel w hw)
      closedCubeFineSlotStateSpace ≈ 1 := by
  unfold closedCubeFineSlotKernel Q'.divPos
  exact Q'.eqv_trans _
    (closedCubeFineSlotPartition w *
      Q'.recipPos (closedCubeFineSlotPartition w)
        (closedCubeFineSlotPartition_pos hw)) _
    (listQSum_mul_right
      (closedCubeFineSlotRawWeight w)
      (Q'.recipPos (closedCubeFineSlotPartition w)
        (closedCubeFineSlotPartition_pos hw))
      closedCubeFineSlotStateSpace)
    (Q'.mul_recipPos_eqv _
      (closedCubeFineSlotPartition_pos hw))

/-! ## Dependency gates -/

#print axioms cubeFineSlotAssignmentStateSpace_nodup
#print axioms cubeFineSlotAssignmentStateSpace_length
#print axioms oddFineCubeSlotSupport_eq
#print axioms oddFineCubeSlotClosed
#print axioms reflectedOddFineCubeSlotClosed
#print axioms zeroSlotCubeRejected
#print axioms closedCubeFineSlotStateSpace_eq
#print axioms closedCubeFineSlotStateSpace_nodup
#print axioms zeroSlotCubeAssignment_not_mem_closed
#print axioms mem_closedCubeFineSlotStateSpace_incidenceClosed
#print axioms mem_closedCubeFineSlotStateSpace_even_incidence
#print axioms oddFineCubeSlotSource_packet_is_geometric
#print axioms reflectedOddFineCubeSlotSource_packet_is_geometric
#print axioms closedCubeFineSlotPartition_pos
#print axioms closedCubeFineSlotKernel_nonnegative
#print axioms closedCubeFineSlotKernel_row_normalized

end YMGap.Continuum.Z4DyadicSlabCubeFineSupportProjectedKernel
