/-
# One-denominator joint kernel for two adjacent all-cutoff cubes

The independent cube product is valid only when the two cube carriers are
link separated.  Adjacent cubes share one face and its four boundary links.
This module assembles the correct finite target before normalization:

* all six character/fusion face factors from each cube;
* the eight production links of each cube not incident on the shared face;
* one fusion channel for the two shared-face coarse characters; and
* four link constraints coupling that same channel to the corresponding
  outer faces.

Thus the eight independently counted shared-face boundary-link factors are
removed and replaced by the five-factor shared recoupling fiber.  The full
raw state is summed over both six-face cube target spaces and the fused
shared-face channel, then divided by one derived denominator.

The compatible stretched target is present at every cutoff and has positive
mass, so the resulting joint kernel is nonnegative and exactly
row-normalized.  Reflection covariance and the global fine-support projector
are deliberately left to the next module.
-/

import YMGap.Continuum.Z4AdjacentCubeSharedFaceRecouplingKernel

namespace YMGap.Continuum.Z4AdjacentCubeJointConditionalKernel

set_option maxRecDepth 30000
set_option maxHeartbeats 7000000

open YMGap.Constructive
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4AdjacentCubeSharedFaceRecouplingKernel
open YMGap.Continuum.Z4DyadicSlabCubeCoupledConditionalKernel
open YMGap.Continuum.Z4DyadicSlabTwoFaceCoupledConditionalKernel
open YMGap.Continuum.Z4DyadicSlabTwoFaceSharedLinkKernel
open YMGap.Continuum.Z4DyadicUnitCubeBlockGeometry

local infix:50 " ≈ " => Q'.eqv

private theorem qmul_congr {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

private theorem pos_of_eqv_local {a b : Q'}
    (ha : (0 : Q') < a) (hab : a ≈ b) : (0 : Q') < b :=
  Q'.pos_of_lt_of_le ha (Q'.le_of_eqv hab)

/-! ## 1. Remove the independently counted interface links -/

def incidenceAvoidsFace
    (face : CubeFaceIndex) (incidence : CubeProductionIncidence) : Bool :=
  decide (incidence.left ≠ face ∧ incidence.right ≠ face)

def leftCubeOuterIncidences : List CubeProductionIncidence :=
  cubeProductionIncidences.filter (incidenceAvoidsFace .rightYZ)

def rightCubeOuterIncidences : List CubeProductionIncidence :=
  cubeProductionIncidences.filter (incidenceAvoidsFace .leftYZ)

theorem leftCubeOuterIncidences_length :
    leftCubeOuterIncidences.length = 8 := by
  decide

theorem rightCubeOuterIncidences_length :
    rightCubeOuterIncidences.length = 8 := by
  decide

private def adjacentQProduct {A : Type}
    (value : A → Q') : List A → Q'
  | [] => 1
  | head :: tail => value head * adjacentQProduct value tail

private theorem adjacentQProduct_nonnegative {A : Type}
    (value : A → Q') (hvalue : ∀ x, (0 : Q') ≤ value x) :
    ∀ xs, (0 : Q') ≤ adjacentQProduct value xs
  | [] => Q'.zero_le_one
  | head :: tail =>
      Q'.mul_nonneg _ _ (hvalue head)
        (adjacentQProduct_nonnegative value hvalue tail)

private theorem adjacentQProduct_congr {A : Type}
    (left right : A → Q') (hagrees : ∀ x, left x ≈ right x) :
    ∀ xs, adjacentQProduct left xs ≈ adjacentQProduct right xs
  | [] => Q'.eqv_refl 1
  | head :: tail =>
      qmul_congr (hagrees head)
        (adjacentQProduct_congr left right hagrees tail)

private theorem adjacentQProduct_one {A : Type} :
    ∀ xs : List A, adjacentQProduct (fun _ => (1 : Q')) xs ≈ 1
  | [] => Q'.eqv_refl 1
  | _ :: tail =>
      Q'.eqv_trans _ (1 * 1) _
        (Q'.mul_eqv_congr_left 1 _ _
          (adjacentQProduct_one tail))
        (Q'.one_mul_eqv 1)

def cubeOuterProductionLinkProduct
    (cutoff : Nat) (target : CubePairChannelState)
    (incidences : List CubeProductionIncidence) : Q' :=
  adjacentQProduct
    (cubeProductionIncidenceFactor cutoff target) incidences

theorem cubeOuterProductionLinkProduct_nonnegative
    (cutoff : Nat) (target : CubePairChannelState)
    (incidences : List CubeProductionIncidence) :
    (0 : Q') ≤
      cubeOuterProductionLinkProduct cutoff target incidences := by
  unfold cubeOuterProductionLinkProduct
  apply adjacentQProduct_nonnegative
  intro incidence
  unfold cubeProductionIncidenceFactor
  exact Q'.le_trans' _ _ _
    (fusionInd_nonneg
      (cubeTargetAt target incidence.left).2
      (cubeTargetAt target incidence.right).2 0)
    (Q'.le_of_eqv
      (Q'.eqv_symm
        (twoFaceProductionLinkFactor_eq_fusionInd cutoff
          (cubeTargetAt target incidence.left)
          (cubeTargetAt target incidence.right))))

theorem compatibleCubeOuterProductionLinkProduct_eqv_one
    {cutoff : Nat} (source : CubeStretchedCompatibleSource cutoff)
    (incidences : List CubeProductionIncidence) :
    cubeOuterProductionLinkProduct cutoff
        (compatibleCubeTarget source) incidences ≈ 1 := by
  unfold cubeOuterProductionLinkProduct
  exact Q'.eqv_trans _
    (adjacentQProduct (fun _ : CubeProductionIncidence => (1 : Q'))
      incidences) _
    (adjacentQProduct_congr _ _
      (compatibleCube_incidenceFactor_eqv_one source) incidences)
    (adjacentQProduct_one incidences)

/-! ## 2. Complete finite adjacent target and raw mass -/

abbrev AdjacentCubeJointTarget :=
  (CubePairChannelState × CubePairChannelState) × Nat

def adjacentCubeJointStateSpace (cutoff : Nat) :
    List AdjacentCubeJointTarget :=
  cartesian
    (cartesian (cubePairChannelStateSpace cutoff)
      (cubePairChannelStateSpace cutoff))
    (adjacentCubeSharedFaceStateSpace cutoff)

theorem adjacentCubeJointStateSpace_nodup (cutoff : Nat) :
    (adjacentCubeJointStateSpace cutoff).Nodup := by
  unfold adjacentCubeJointStateSpace
  exact cartesian_nodup _ _
    (cartesian_nodup _ _
      (cubePairChannelStateSpace_nodup cutoff)
      (cubePairChannelStateSpace_nodup cutoff))
    (adjacentCubeSharedFaceStateSpace_nodup cutoff)

def compatibleAdjacentCubeJointTarget
    {cutoff : Nat} (source : AdjacentCubeStretchedSource cutoff) :
    AdjacentCubeJointTarget :=
  ((compatibleCubeTarget source.left,
      compatibleCubeTarget source.right),
    adjacentCubeStretchedFusedChannel source)

theorem compatibleAdjacentCubeJointTarget_mem
    {cutoff : Nat} (source : AdjacentCubeStretchedSource cutoff) :
    compatibleAdjacentCubeJointTarget source ∈
      adjacentCubeJointStateSpace cutoff := by
  unfold adjacentCubeJointStateSpace
  apply (mem_cartesian_iff _ _ _).mpr
  exact ⟨(mem_cartesian_iff _ _ _).mpr
      ⟨compatibleCubeTarget_mem source.left,
        compatibleCubeTarget_mem source.right⟩,
    adjacentCubeStretchedFusedChannel_mem source⟩

def adjacentCubeJointRawWeight
    (w : Q') (cutoff : Nat)
    (source : AdjacentCubeStretchedSource cutoff)
    (target : AdjacentCubeJointTarget) : Q' :=
  (cubeFaceRawProduct w cutoff source.left target.1.1 *
      cubeFaceRawProduct w cutoff source.right target.1.2) *
    ((cubeOuterProductionLinkProduct cutoff target.1.1
          leftCubeOuterIncidences *
        cubeOuterProductionLinkProduct cutoff target.1.2
          rightCubeOuterIncidences) *
      adjacentCubeSharedFaceTargetRawWeight
        target.1.1 target.1.2 target.2)

theorem adjacentCubeJointRawWeight_nonnegative
    {w : Q'} (hw : (0 : Q') ≤ w) (cutoff : Nat)
    (source : AdjacentCubeStretchedSource cutoff)
    (target : AdjacentCubeJointTarget) :
    (0 : Q') ≤ adjacentCubeJointRawWeight w cutoff source target := by
  unfold adjacentCubeJointRawWeight
  exact Q'.mul_nonneg _ _
    (Q'.mul_nonneg _ _
      (cubeFaceRawProduct_nonnegative hw cutoff
        source.left target.1.1)
      (cubeFaceRawProduct_nonnegative hw cutoff
        source.right target.1.2))
    (Q'.mul_nonneg _ _
      (Q'.mul_nonneg _ _
        (cubeOuterProductionLinkProduct_nonnegative
          cutoff target.1.1 leftCubeOuterIncidences)
        (cubeOuterProductionLinkProduct_nonnegative
          cutoff target.1.2 rightCubeOuterIncidences))
      (adjacentCubeSharedFaceTargetRawWeight_nonnegative
        target.1.1 target.1.2 target.2))

theorem compatibleAdjacentCubeJointRawWeight_pos
    {w : Q'} (hw : (0 : Q') < w) (cutoff : Nat)
    (source : AdjacentCubeStretchedSource cutoff) :
    (0 : Q') < adjacentCubeJointRawWeight w cutoff source
      (compatibleAdjacentCubeJointTarget source) := by
  have hleftFaces :=
    compatibleCubeFaceRawProduct_pos hw cutoff source.left
  have hrightFaces :=
    compatibleCubeFaceRawProduct_pos hw cutoff source.right
  have hleftOuter : (0 : Q') <
      cubeOuterProductionLinkProduct cutoff
        (compatibleCubeTarget source.left)
        leftCubeOuterIncidences :=
    pos_of_eqv_local (by decide)
      (Q'.eqv_symm
        (compatibleCubeOuterProductionLinkProduct_eqv_one
          source.left leftCubeOuterIncidences))
  have hrightOuter : (0 : Q') <
      cubeOuterProductionLinkProduct cutoff
        (compatibleCubeTarget source.right)
        rightCubeOuterIncidences :=
    pos_of_eqv_local (by decide)
      (Q'.eqv_symm
        (compatibleCubeOuterProductionLinkProduct_eqv_one
          source.right rightCubeOuterIncidences))
  have hinterface : (0 : Q') <
      adjacentCubeSharedFaceTargetRawWeight
        (compatibleCubeTarget source.left)
        (compatibleCubeTarget source.right)
        (adjacentCubeStretchedFusedChannel source) := by
    change (0 : Q') <
      adjacentCubeSharedFaceRawWeight source
        (adjacentCubeStretchedFusedChannel source)
    exact pos_of_eqv_local (by decide)
      (Q'.eqv_symm
        (adjacentCubeStretchedRawWeight_eqv_one source))
  exact Q'.mul_pos
    (Q'.mul_pos hleftFaces hrightFaces)
    (Q'.mul_pos
      (Q'.mul_pos hleftOuter hrightOuter)
      hinterface)

/-! ## 3. One normalization over the complete adjacent target -/

def adjacentCubeJointPartition
    (w : Q') (cutoff : Nat)
    (source : AdjacentCubeStretchedSource cutoff) : Q' :=
  listQSum (adjacentCubeJointRawWeight w cutoff source)
    (adjacentCubeJointStateSpace cutoff)

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

theorem adjacentCubeJointPartition_pos
    {w : Q'} (hw : (0 : Q') < w) (cutoff : Nat)
    (source : AdjacentCubeStretchedSource cutoff) :
    (0 : Q') < adjacentCubeJointPartition w cutoff source := by
  have hle := listQSum_member_le_local
    (adjacentCubeJointRawWeight w cutoff source)
    (adjacentCubeJointRawWeight_nonnegative
      (Q'.le_of_lt hw) cutoff source)
    (adjacentCubeJointStateSpace cutoff)
    (compatibleAdjacentCubeJointTarget_mem source)
  exact Q'.pos_of_lt_of_le
    (compatibleAdjacentCubeJointRawWeight_pos hw cutoff source) hle

def adjacentCubeJointConditionalKernel
    (w : Q') (hw : (0 : Q') < w) (cutoff : Nat)
    (source : AdjacentCubeStretchedSource cutoff)
    (target : AdjacentCubeJointTarget) : Q' :=
  Q'.divPos
    (adjacentCubeJointRawWeight w cutoff source target)
    (adjacentCubeJointPartition w cutoff source)
    (adjacentCubeJointPartition_pos hw cutoff source)

theorem adjacentCubeJointConditionalKernel_nonnegative
    (w : Q') (hw : (0 : Q') < w) (cutoff : Nat)
    (source : AdjacentCubeStretchedSource cutoff)
    (target : AdjacentCubeJointTarget) :
    (0 : Q') ≤
      adjacentCubeJointConditionalKernel
        w hw cutoff source target := by
  unfold adjacentCubeJointConditionalKernel Q'.divPos
  exact Q'.mul_nonneg _ _
    (adjacentCubeJointRawWeight_nonnegative
      (Q'.le_of_lt hw) cutoff source target)
    (Q'.le_of_lt (Q'.recipPos_pos _ _))

theorem adjacentCubeJointConditionalKernel_row_normalized
    (w : Q') (hw : (0 : Q') < w) (cutoff : Nat)
    (source : AdjacentCubeStretchedSource cutoff) :
    listQSum
        (adjacentCubeJointConditionalKernel w hw cutoff source)
        (adjacentCubeJointStateSpace cutoff) ≈ 1 := by
  unfold adjacentCubeJointConditionalKernel Q'.divPos
  exact Q'.eqv_trans _
    (adjacentCubeJointPartition w cutoff source *
      Q'.recipPos (adjacentCubeJointPartition w cutoff source)
        (adjacentCubeJointPartition_pos hw cutoff source)) _
    (listQSum_mul_right
      (adjacentCubeJointRawWeight w cutoff source)
      (Q'.recipPos (adjacentCubeJointPartition w cutoff source)
        (adjacentCubeJointPartition_pos hw cutoff source))
      (adjacentCubeJointStateSpace cutoff))
    (Q'.mul_recipPos_eqv _
      (adjacentCubeJointPartition_pos hw cutoff source))

#print axioms leftCubeOuterIncidences_length
#print axioms rightCubeOuterIncidences_length
#print axioms adjacentCubeJointStateSpace_nodup
#print axioms compatibleAdjacentCubeJointTarget_mem
#print axioms adjacentCubeJointRawWeight_nonnegative
#print axioms compatibleAdjacentCubeJointRawWeight_pos
#print axioms adjacentCubeJointPartition_pos
#print axioms adjacentCubeJointConditionalKernel_nonnegative
#print axioms adjacentCubeJointConditionalKernel_row_normalized

end YMGap.Continuum.Z4AdjacentCubeJointConditionalKernel
