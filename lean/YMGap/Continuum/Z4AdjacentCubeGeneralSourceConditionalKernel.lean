/-
# General-source adjacent-cube conditional kernel

The stretched-source adjacent-cube kernel requires all six face packets of
each cube to have one common total.  A translated fine unit-cube surface
violates that condition, so the restriction cannot be used as the source
space of a physical slab pushforward.

This module removes the equal-total restriction.  Positivity of the row
denominator is instead carried by one retained fine-intertwiner witness:
an admissible joint target whose exact raw mass is positive.  This is the
right local datum supplied by a positive physical fine spin-foam summand.
The resulting kernel has the same complete adjacent-cube target, is
nonnegative, and is normalized by one exact denominator.

The old stretched source embeds as a special case, with its stretched target
providing the retained witness.  The remaining physical coverage theorem is
therefore sharply stated: construct this witness from every positive physical
fine summand.  No equal-face-total hypothesis remains.
-/

import YMGap.Continuum.Z4AdjacentCubeJointConditionalKernel

namespace YMGap.Continuum.Z4AdjacentCubeGeneralSourceConditionalKernel

set_option maxRecDepth 30000
set_option maxHeartbeats 7000000

open YMGap.Constructive
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4AdjacentCubeJointConditionalKernel
open YMGap.Continuum.Z4AdjacentCubeSharedFaceRecouplingKernel
open YMGap.Continuum.Z4DyadicSlabCharacterFusionConditionalKernel
open YMGap.Continuum.Z4DyadicSlabCubeCoupledConditionalKernel
open YMGap.Continuum.Z4DyadicUnitCubeBlockGeometry

local infix:50 " ≈ " => Q'.eqv

private theorem pos_of_eqv_local {a b : Q'}
    (ha : (0 : Q') < a) (hab : a ≈ b) : (0 : Q') < b :=
  Q'.pos_of_lt_of_le ha (Q'.le_of_eqv hab)

/-! ## 1. Arbitrary bounded physical face packets -/

structure GeneralCubePacketSource (cutoff : Nat) where
  packet : CubeFaceIndex → BoundedFaceSpinPacket cutoff

structure GeneralAdjacentCubePacketSource (cutoff : Nat) where
  left : GeneralCubePacketSource cutoff
  right : GeneralCubePacketSource cutoff

private def generalQProduct {A : Type}
    (value : A → Q') : List A → Q'
  | [] => 1
  | head :: tail => value head * generalQProduct value tail

private theorem generalQProduct_nonnegative {A : Type}
    (value : A → Q') (hvalue : ∀ x, (0 : Q') ≤ value x) :
    ∀ xs, (0 : Q') ≤ generalQProduct value xs
  | [] => Q'.zero_le_one
  | head :: tail =>
      Q'.mul_nonneg _ _ (hvalue head)
        (generalQProduct_nonnegative value hvalue tail)

def generalCubeFaceRawProduct
    (w : Q') (source : GeneralCubePacketSource cutoff)
    (target : CubePairChannelState) : Q' :=
  generalQProduct (fun face =>
    packetPairChannelRawWeight w (source.packet face).val
      (cubeTargetAt target face)) cubeFaceIndices

theorem generalCubeFaceRawProduct_nonnegative
    {w : Q'} (hw : (0 : Q') ≤ w)
    (source : GeneralCubePacketSource cutoff)
    (target : CubePairChannelState) :
    (0 : Q') ≤ generalCubeFaceRawProduct w source target := by
  unfold generalCubeFaceRawProduct
  apply generalQProduct_nonnegative
  intro face
  exact packetPairChannelRawWeight_nonnegative hw
    (source.packet face).val (cubeTargetAt target face)

/-! ## 2. Complete general-source raw mass -/

def generalAdjacentCubeRawWeight
    (w : Q') (cutoff : Nat)
    (source : GeneralAdjacentCubePacketSource cutoff)
    (target : AdjacentCubeJointTarget) : Q' :=
  (generalCubeFaceRawProduct w source.left target.1.1 *
      generalCubeFaceRawProduct w source.right target.1.2) *
    ((cubeOuterProductionLinkProduct cutoff target.1.1
          leftCubeOuterIncidences *
        cubeOuterProductionLinkProduct cutoff target.1.2
          rightCubeOuterIncidences) *
      adjacentCubeSharedFaceTargetRawWeight
        target.1.1 target.1.2 target.2)

theorem generalAdjacentCubeRawWeight_nonnegative
    {w : Q'} (hw : (0 : Q') ≤ w) (cutoff : Nat)
    (source : GeneralAdjacentCubePacketSource cutoff)
    (target : AdjacentCubeJointTarget) :
    (0 : Q') ≤ generalAdjacentCubeRawWeight w cutoff source target := by
  unfold generalAdjacentCubeRawWeight
  exact Q'.mul_nonneg _ _
    (Q'.mul_nonneg _ _
      (generalCubeFaceRawProduct_nonnegative hw source.left target.1.1)
      (generalCubeFaceRawProduct_nonnegative hw source.right target.1.2))
    (Q'.mul_nonneg _ _
      (Q'.mul_nonneg _ _
        (cubeOuterProductionLinkProduct_nonnegative
          cutoff target.1.1 leftCubeOuterIncidences)
        (cubeOuterProductionLinkProduct_nonnegative
          cutoff target.1.2 rightCubeOuterIncidences))
      (adjacentCubeSharedFaceTargetRawWeight_nonnegative
        target.1.1 target.1.2 target.2))

/-! ## 3. Retained positive fine-intertwiner witness -/

structure PositiveAdjacentCubeSource
    (w : Q') (cutoff : Nat) where
  packets : GeneralAdjacentCubePacketSource cutoff
  witness : AdjacentCubeJointTarget
  witness_mem : witness ∈ adjacentCubeJointStateSpace cutoff
  witness_positive :
    (0 : Q') < generalAdjacentCubeRawWeight w cutoff packets witness

def generalAdjacentCubePartition
    (w : Q') (cutoff : Nat)
    (source : PositiveAdjacentCubeSource w cutoff) : Q' :=
  listQSum
    (generalAdjacentCubeRawWeight w cutoff source.packets)
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

theorem generalAdjacentCubePartition_pos
    {w : Q'} (hw : (0 : Q') < w) (cutoff : Nat)
    (source : PositiveAdjacentCubeSource w cutoff) :
    (0 : Q') < generalAdjacentCubePartition w cutoff source := by
  have hle := listQSum_member_le_local
    (generalAdjacentCubeRawWeight w cutoff source.packets)
    (generalAdjacentCubeRawWeight_nonnegative
      (Q'.le_of_lt hw) cutoff source.packets)
    (adjacentCubeJointStateSpace cutoff)
    source.witness_mem
  exact Q'.pos_of_lt_of_le source.witness_positive hle

def generalAdjacentCubeConditionalKernel
    (w : Q') (hw : (0 : Q') < w) (cutoff : Nat)
    (source : PositiveAdjacentCubeSource w cutoff)
    (target : AdjacentCubeJointTarget) : Q' :=
  Q'.divPos
    (generalAdjacentCubeRawWeight w cutoff source.packets target)
    (generalAdjacentCubePartition w cutoff source)
    (generalAdjacentCubePartition_pos hw cutoff source)

theorem generalAdjacentCubeConditionalKernel_nonnegative
    (w : Q') (hw : (0 : Q') < w) (cutoff : Nat)
    (source : PositiveAdjacentCubeSource w cutoff)
    (target : AdjacentCubeJointTarget) :
    (0 : Q') ≤
      generalAdjacentCubeConditionalKernel
        w hw cutoff source target := by
  unfold generalAdjacentCubeConditionalKernel Q'.divPos
  exact Q'.mul_nonneg _ _
    (generalAdjacentCubeRawWeight_nonnegative
      (Q'.le_of_lt hw) cutoff source.packets target)
    (Q'.le_of_lt (Q'.recipPos_pos _ _))

theorem generalAdjacentCubeConditionalKernel_row_normalized
    (w : Q') (hw : (0 : Q') < w) (cutoff : Nat)
    (source : PositiveAdjacentCubeSource w cutoff) :
    listQSum
        (generalAdjacentCubeConditionalKernel w hw cutoff source)
        (adjacentCubeJointStateSpace cutoff) ≈ 1 := by
  unfold generalAdjacentCubeConditionalKernel Q'.divPos
  exact Q'.eqv_trans _
    (generalAdjacentCubePartition w cutoff source *
      Q'.recipPos (generalAdjacentCubePartition w cutoff source)
        (generalAdjacentCubePartition_pos hw cutoff source)) _
    (listQSum_mul_right
      (generalAdjacentCubeRawWeight w cutoff source.packets)
      (Q'.recipPos (generalAdjacentCubePartition w cutoff source)
        (generalAdjacentCubePartition_pos hw cutoff source))
      (adjacentCubeJointStateSpace cutoff))
    (Q'.mul_recipPos_eqv _
      (generalAdjacentCubePartition_pos hw cutoff source))

/-! ## 4. The stretched kernel embeds without changing its raw mass -/

def generalCubeSourceOfStretched
    {cutoff : Nat} (source : CubeStretchedCompatibleSource cutoff) :
    GeneralCubePacketSource cutoff where
  packet := source.packet

def generalAdjacentCubeSourceOfStretched
    {cutoff : Nat} (source : AdjacentCubeStretchedSource cutoff) :
    GeneralAdjacentCubePacketSource cutoff where
  left := generalCubeSourceOfStretched source.left
  right := generalCubeSourceOfStretched source.right

theorem generalCubeFaceRawProduct_of_stretched
    (w : Q') (cutoff : Nat)
    (source : CubeStretchedCompatibleSource cutoff)
    (target : CubePairChannelState) :
    generalCubeFaceRawProduct w
        (generalCubeSourceOfStretched source) target =
      cubeFaceRawProduct w cutoff source target := by
  rfl

theorem generalAdjacentCubeRawWeight_of_stretched
    (w : Q') (cutoff : Nat)
    (source : AdjacentCubeStretchedSource cutoff)
    (target : AdjacentCubeJointTarget) :
    generalAdjacentCubeRawWeight w cutoff
        (generalAdjacentCubeSourceOfStretched source) target =
      adjacentCubeJointRawWeight w cutoff source target := by
  unfold generalAdjacentCubeRawWeight adjacentCubeJointRawWeight
  change
    (generalCubeFaceRawProduct w
        (generalCubeSourceOfStretched source.left) target.1.1 *
      generalCubeFaceRawProduct w
        (generalCubeSourceOfStretched source.right) target.1.2) * _ =
    (cubeFaceRawProduct w cutoff source.left target.1.1 *
      cubeFaceRawProduct w cutoff source.right target.1.2) * _
  rw [generalCubeFaceRawProduct_of_stretched,
    generalCubeFaceRawProduct_of_stretched]

def positiveAdjacentCubeSourceOfStretched
    {w : Q'} (hw : (0 : Q') < w) (cutoff : Nat)
    (source : AdjacentCubeStretchedSource cutoff) :
    PositiveAdjacentCubeSource w cutoff where
  packets := generalAdjacentCubeSourceOfStretched source
  witness := compatibleAdjacentCubeJointTarget source
  witness_mem := compatibleAdjacentCubeJointTarget_mem source
  witness_positive := by
    rw [generalAdjacentCubeRawWeight_of_stretched]
    exact compatibleAdjacentCubeJointRawWeight_pos hw cutoff source

private theorem qeqv_of_le_of_ge_local {a b : Q'}
    (hab : a ≤ b) (hba : b ≤ a) : a ≈ b := by
  show a.num * (b.den : Int) = b.num * (a.den : Int)
  exact Int.le_antisymm hab hba

private theorem divPos_eqv_congr_local {a a' b b' : Q'}
    (hb : (0 : Q') < b) (hb' : (0 : Q') < b')
    (haEq : a ≈ a') (hbEq : b ≈ b') :
    Q'.divPos a b hb ≈ Q'.divPos a' b' hb' := by
  apply qeqv_of_le_of_ge_local
  · apply Q'.le_divPos_of_mul_le a' b' hb'
    exact Q'.le_of_eqv
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left (Q'.divPos a b hb) b' b
          (Q'.eqv_symm hbEq))
        (Q'.eqv_trans _ _ _ (Q'.divPos_mul_eqv a b hb) haEq))
  · apply Q'.le_divPos_of_mul_le a b hb
    exact Q'.le_of_eqv
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left (Q'.divPos a' b' hb') b b' hbEq)
        (Q'.eqv_trans _ _ _ (Q'.divPos_mul_eqv a' b' hb')
          (Q'.eqv_symm haEq)))

theorem generalKernel_of_stretched
    (w : Q') (hw : (0 : Q') < w) (cutoff : Nat)
    (source : AdjacentCubeStretchedSource cutoff)
    (target : AdjacentCubeJointTarget) :
    generalAdjacentCubeConditionalKernel w hw cutoff
        (positiveAdjacentCubeSourceOfStretched hw cutoff source) target ≈
      adjacentCubeJointConditionalKernel w hw cutoff source target := by
  unfold generalAdjacentCubeConditionalKernel
    adjacentCubeJointConditionalKernel
    generalAdjacentCubePartition adjacentCubeJointPartition
  simp only [positiveAdjacentCubeSourceOfStretched]
  rw [generalAdjacentCubeRawWeight_of_stretched]
  have hpartition :
      listQSum
          (generalAdjacentCubeRawWeight w cutoff
            (generalAdjacentCubeSourceOfStretched source))
          (adjacentCubeJointStateSpace cutoff) ≈
        listQSum
          (adjacentCubeJointRawWeight w cutoff source)
          (adjacentCubeJointStateSpace cutoff) := by
    apply listQSum_congr_on
    intro state _
    exact Q'.eqv_of_eq
      (generalAdjacentCubeRawWeight_of_stretched
        w cutoff source state)
  exact divPos_eqv_congr_local
    (generalAdjacentCubePartition_pos hw cutoff
      (positiveAdjacentCubeSourceOfStretched hw cutoff source))
    (adjacentCubeJointPartition_pos hw cutoff source)
    (Q'.eqv_refl _)
    hpartition

#print axioms generalCubeFaceRawProduct_nonnegative
#print axioms generalAdjacentCubeRawWeight_nonnegative
#print axioms generalAdjacentCubePartition_pos
#print axioms generalAdjacentCubeConditionalKernel_nonnegative
#print axioms generalAdjacentCubeConditionalKernel_row_normalized
#print axioms generalCubeFaceRawProduct_of_stretched
#print axioms generalAdjacentCubeRawWeight_of_stretched
#print axioms generalKernel_of_stretched

end YMGap.Continuum.Z4AdjacentCubeGeneralSourceConditionalKernel
