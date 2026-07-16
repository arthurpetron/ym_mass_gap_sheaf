/-
# Normalize a complete two-face shared-link component

The preceding normalization fence shows that separately normalized face rows
can have zero mass after the exact shared-link projection.  The viable order
of operations is therefore forced: multiply both literal face-channel
weights by the production link multiplicity, sum that complete component,
and divide only once.

This file carries out that repair on the smallest non-vacuous source class.
Two bounded face packets are `stretchedCompatible` when the sums of their
four fine twice-spin labels agree.  Their two stretched pair channels then
have the same coarse spin.  Both face weights are strictly positive there,
and the literal degree-two production link multiplicity is one.  This gives
an explicit member of positive weight in a duplicate-free joint target list,
so the coupled denominator is derived rather than assumed.

The resulting joint row is nonnegative, exactly normalized, and intertwines
corrected-slab reflection even when the two incident faces have different
planes.  Arbitrary source pairs are deliberately not admitted: the checked
vacuum/fundamental fence proves that their coupled denominator can be zero.
-/

import YMGap.Continuum.Z4DyadicSlabTwoFaceSharedLinkKernel
import YMGap.Continuum.Z4CanonicalPolymerRange

namespace YMGap.Continuum.Z4DyadicSlabTwoFaceCoupledConditionalKernel

set_option maxRecDepth 12000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4CanonicalPolymerRange
open YMGap.Continuum.Z4DyadicSlabCharacterFusionConditionalKernel
open YMGap.Continuum.Z4DyadicSlabMultiCharacterPacketKernel
open YMGap.Continuum.Z4DyadicSlabReflectionParityKernel
open YMGap.Continuum.Z4DyadicSlabTwoFaceSharedLinkKernel
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4UnitCubeEnumerationParity

local infix:50 " ≈ " => Q'.eqv

private theorem qmul_congr {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

private theorem pos_of_eqv_local {a b : Q'}
    (ha : (0 : Q') < a) (hab : a ≈ b) : (0 : Q') < b :=
  Q'.pos_of_lt_of_le ha (Q'.le_of_eqv hab)

private theorem ofNat_nonnegative_local (n : Nat) :
    (0 : Q') ≤ Q'.ofNat n := by
  rw [Q'.zero_le_iff_num_nonneg]
  exact Int.natCast_nonneg n

private theorem nodup_map_of_injective_local {A B : Type}
    (f : A → B) (hf : ∀ {x y}, f x = f y → x = y) :
    ∀ {xs : List A}, xs.Nodup → (xs.map f).Nodup
  | [], _ => List.nodup_nil
  | x :: xs, h => by
      have hparts := List.nodup_cons.mp h
      apply List.nodup_cons.mpr
      refine ⟨?_, nodup_map_of_injective_local f hf hparts.2⟩
      intro hmem
      obtain ⟨y, hy, heq⟩ := List.mem_map.mp hmem
      exact hparts.1 ((hf heq) ▸ hy)

private theorem listQSum_member_le_local {A : Type}
    (value : A → Q') (hvalue : ∀ x, (0 : Q') ≤ value x) :
    ∀ (xs : List A) {x : A}, x ∈ xs →
      value x ≤ listQSum value xs
  | [], _, h => absurd h List.not_mem_nil
  | head :: tail, x, h => by
      rcases List.mem_cons.mp h with hhead | htail
      · subst x
        exact Q'.add_le_self_of_nonneg (value head)
          (listQSum value tail)
          (listQSum_nonnegative_on value tail
            (fun y _ => hvalue y))
      · have ih := listQSum_member_le_local value hvalue tail htail
        have hmono : listQSum value tail ≤
            value head + listQSum value tail := by
          have h := Q'.add_le_add_right
            (0 : Q') (value head) (listQSum value tail) (hvalue head)
          rwa [Q'.zero_add'] at h
        exact Q'.le_trans' _ _ _ ih hmono

/-! ## 1. Duplicate-free joint targets and compatible sources -/

abbrev JointPairChannelState := PairChannelState × PairChannelState

def jointPairChannelStateSpace (cutoff : Nat) :
    List JointPairChannelState :=
  cartesian (pairChannelStateSpace cutoff) (pairChannelStateSpace cutoff)

theorem jointPairChannelStateSpace_nodup (cutoff : Nat) :
    (jointPairChannelStateSpace cutoff).Nodup := by
  unfold jointPairChannelStateSpace
  exact cartesian_nodup _ _
    (pairChannelStateSpace_nodup cutoff)
    (pairChannelStateSpace_nodup cutoff)

def faceSpinTotal (packet : FaceSpinPacket) : Nat :=
  packet.spin0 + packet.spin1 + packet.spin2 + packet.spin3

def stretchedPairChannelState
    (packet : FaceSpinPacket) : PairChannelState :=
  ((packet.spin0 + packet.spin1, packet.spin2 + packet.spin3),
    faceSpinTotal packet)

structure StretchedCompatibleFacePair (cutoff : Nat) where
  left : BoundedFaceSpinPacket cutoff
  right : BoundedFaceSpinPacket cutoff
  total_eq : faceSpinTotal left.val = faceSpinTotal right.val

def compatibleStretchedTarget {cutoff : Nat}
    (source : StretchedCompatibleFacePair cutoff) :
    JointPairChannelState :=
  (stretchedPairChannelState source.left.val,
    stretchedPairChannelState source.right.val)

theorem compatibleStretchedTarget_mem {cutoff : Nat}
    (source : StretchedCompatibleFacePair cutoff) :
    compatibleStretchedTarget source ∈
      jointPairChannelStateSpace cutoff := by
  unfold compatibleStretchedTarget jointPairChannelStateSpace
  apply (mem_cartesian_iff _ _ _).mpr
  exact ⟨stretchedPairChannel_mem cutoff source.left.val
      source.left.property,
    stretchedPairChannel_mem cutoff source.right.val
      source.right.property⟩

/-! ## 2. One complete raw shared-link component -/

def twoFaceCoupledRawWeight
    (w : Q') (cutoff : Nat)
    (source : StretchedCompatibleFacePair cutoff)
    (target : JointPairChannelState) : Q' :=
  (packetPairChannelRawWeight w source.left.val target.1 *
    packetPairChannelRawWeight w source.right.val target.2) *
    twoFaceProductionLinkFactor cutoff target.1 target.2

theorem twoFaceCoupledRawWeight_nonnegative
    {w : Q'} (hw : (0 : Q') ≤ w) (cutoff : Nat)
    (source : StretchedCompatibleFacePair cutoff)
    (target : JointPairChannelState) :
    (0 : Q') ≤ twoFaceCoupledRawWeight w cutoff source target := by
  unfold twoFaceCoupledRawWeight
  exact Q'.mul_nonneg _ _
    (Q'.mul_nonneg _ _
      (packetPairChannelRawWeight_nonnegative
        hw source.left.val target.1)
      (packetPairChannelRawWeight_nonnegative
        hw source.right.val target.2))
    (ofNat_nonnegative_local _)

theorem compatibleStretched_linkFactor_eqv_one {cutoff : Nat}
    (source : StretchedCompatibleFacePair cutoff) :
    twoFaceProductionLinkFactor cutoff
        (stretchedPairChannelState source.left.val)
        (stretchedPairChannelState source.right.val) ≈ 1 := by
  refine Q'.eqv_trans _
    (YMGap.Continuum.BondMovingStep.fusionInd
      (faceSpinTotal source.left.val)
      (faceSpinTotal source.right.val) 0) _
    (twoFaceProductionLinkFactor_eq_fusionInd cutoff _ _) ?_
  rw [source.total_eq]
  exact Q'.eqv_of_eq
    (YMGap.Continuum.FusionQuotientCollapse.fusionInd_zero_diag_self _)

theorem compatibleStretched_rawWeight_pos
    {w : Q'} (hw : (0 : Q') < w) (cutoff : Nat)
    (source : StretchedCompatibleFacePair cutoff) :
    (0 : Q') < twoFaceCoupledRawWeight w cutoff source
      (compatibleStretchedTarget source) := by
  have hleft := stretchedPairChannelRawWeight_pos hw source.left.val
  have hright := stretchedPairChannelRawWeight_pos hw source.right.val
  have hprod : (0 : Q') <
      packetPairChannelRawWeight w source.left.val
          (stretchedPairChannelState source.left.val) *
        packetPairChannelRawWeight w source.right.val
          (stretchedPairChannelState source.right.val) :=
    Q'.mul_pos hleft hright
  have hprodOne : (0 : Q') <
      (packetPairChannelRawWeight w source.left.val
          (stretchedPairChannelState source.left.val) *
        packetPairChannelRawWeight w source.right.val
          (stretchedPairChannelState source.right.val)) * 1 :=
    Q'.mul_pos hprod (by decide)
  apply pos_of_eqv_local hprodOne
  exact Q'.eqv_symm
    (Q'.mul_eqv_congr_left _ _ _
      (compatibleStretched_linkFactor_eqv_one source))

def twoFaceCoupledPartition
    (w : Q') (cutoff : Nat)
    (source : StretchedCompatibleFacePair cutoff) : Q' :=
  listQSum (twoFaceCoupledRawWeight w cutoff source)
    (jointPairChannelStateSpace cutoff)

theorem twoFaceCoupledPartition_pos
    {w : Q'} (hw : (0 : Q') < w) (cutoff : Nat)
    (source : StretchedCompatibleFacePair cutoff) :
    (0 : Q') < twoFaceCoupledPartition w cutoff source := by
  have hterm := compatibleStretched_rawWeight_pos hw cutoff source
  have hle : twoFaceCoupledRawWeight w cutoff source
        (compatibleStretchedTarget source) ≤
      twoFaceCoupledPartition w cutoff source := by
    unfold twoFaceCoupledPartition
    exact listQSum_member_le_local
      (twoFaceCoupledRawWeight w cutoff source)
      (twoFaceCoupledRawWeight_nonnegative
        (Q'.le_of_lt hw) cutoff source)
      _ (compatibleStretchedTarget_mem source)
  exact Q'.pos_of_lt_of_le hterm hle

/-! ## 3. Normalize once, after production gluing -/

def twoFaceCoupledConditionalKernel
    (w : Q') (hw : (0 : Q') < w) (cutoff : Nat)
    (source : StretchedCompatibleFacePair cutoff)
    (target : JointPairChannelState) : Q' :=
  Q'.divPos
    (twoFaceCoupledRawWeight w cutoff source target)
    (twoFaceCoupledPartition w cutoff source)
    (twoFaceCoupledPartition_pos hw cutoff source)

theorem twoFaceCoupledConditionalKernel_nonnegative
    (w : Q') (hw : (0 : Q') < w) (cutoff : Nat)
    (source : StretchedCompatibleFacePair cutoff)
    (target : JointPairChannelState) :
    (0 : Q') ≤ twoFaceCoupledConditionalKernel
      w hw cutoff source target := by
  unfold twoFaceCoupledConditionalKernel Q'.divPos
  exact Q'.mul_nonneg _ _
    (twoFaceCoupledRawWeight_nonnegative
      (Q'.le_of_lt hw) cutoff source target)
    (Q'.le_of_lt (Q'.recipPos_pos _ _))

theorem twoFaceCoupledConditionalKernel_row_normalized
    (w : Q') (hw : (0 : Q') < w) (cutoff : Nat)
    (source : StretchedCompatibleFacePair cutoff) :
    listQSum
        (twoFaceCoupledConditionalKernel w hw cutoff source)
        (jointPairChannelStateSpace cutoff) ≈ 1 := by
  unfold twoFaceCoupledConditionalKernel Q'.divPos
  exact Q'.eqv_trans _
    (twoFaceCoupledPartition w cutoff source *
      Q'.recipPos (twoFaceCoupledPartition w cutoff source)
        (twoFaceCoupledPartition_pos hw cutoff source)) _
    (listQSum_mul_right
      (twoFaceCoupledRawWeight w cutoff source)
      (Q'.recipPos (twoFaceCoupledPartition w cutoff source)
        (twoFaceCoupledPartition_pos hw cutoff source))
      (jointPairChannelStateSpace cutoff))
    (Q'.mul_recipPos_eqv _
      (twoFaceCoupledPartition_pos hw cutoff source))

/-! ## 4. Reflection of the complete coupled component -/

theorem faceSpinTotal_reflection
    (leftPlane : YMGap.Continuum.ClusterCount4DProgress.Z4Plane)
    (packet : FaceSpinPacket) :
    faceSpinTotal (reflectFaceSpinPacket leftPlane packet) =
      faceSpinTotal packet := by
  cases leftPlane <;> rcases packet with ⟨a, b, c, d⟩ <;>
    simp only [faceSpinTotal, reflectFaceSpinPacket] <;> omega

def reflectStretchedCompatibleFacePair
    (cutoff : Nat)
    (leftPlane rightPlane :
      YMGap.Continuum.ClusterCount4DProgress.Z4Plane)
    (source : StretchedCompatibleFacePair cutoff) :
    StretchedCompatibleFacePair cutoff where
  left := reflectBoundedFaceSpinPacket cutoff leftPlane source.left
  right := reflectBoundedFaceSpinPacket cutoff rightPlane source.right
  total_eq := by
    change faceSpinTotal (reflectFaceSpinPacket leftPlane source.left.val) =
      faceSpinTotal (reflectFaceSpinPacket rightPlane source.right.val)
    rw [faceSpinTotal_reflection, faceSpinTotal_reflection]
    exact source.total_eq

def reflectJointPairChannelState
    (leftPlane rightPlane :
      YMGap.Continuum.ClusterCount4DProgress.Z4Plane)
    (target : JointPairChannelState) : JointPairChannelState :=
  (reflectPairChannelState leftPlane target.1,
    reflectPairChannelState rightPlane target.2)

theorem reflectJointPairChannelState_involutive
    (leftPlane rightPlane :
      YMGap.Continuum.ClusterCount4DProgress.Z4Plane)
    (target : JointPairChannelState) :
    reflectJointPairChannelState leftPlane rightPlane
      (reflectJointPairChannelState leftPlane rightPlane target) =
        target := by
  rcases target with ⟨left, right⟩
  simp only [reflectJointPairChannelState]
  rw [reflectPairChannelState_involutive,
    reflectPairChannelState_involutive]

private theorem reflectPairChannelState_mem_clean
    {cutoff : Nat} {state : PairChannelState}
    (hstate : state ∈ pairChannelStateSpace cutoff)
    (plane : YMGap.Continuum.ClusterCount4DProgress.Z4Plane) :
    reflectPairChannelState plane state ∈
      pairChannelStateSpace cutoff := by
  have hbounds := (mem_pairChannelStateSpace_iff cutoff state).mp hstate
  apply (mem_pairChannelStateSpace_iff cutoff _).mpr
  cases plane with
  | p01 => exact ⟨hbounds.2.1, hbounds.1, hbounds.2.2⟩
  | p02 => exact ⟨hbounds.2.1, hbounds.1, hbounds.2.2⟩
  | p03 => exact hbounds
  | p12 => exact ⟨hbounds.2.1, hbounds.1, hbounds.2.2⟩
  | p13 => exact hbounds
  | p23 => exact hbounds

theorem reflectJointPairChannelState_mem
    {cutoff : Nat} {target : JointPairChannelState}
    (htarget : target ∈ jointPairChannelStateSpace cutoff)
    (leftPlane rightPlane :
      YMGap.Continuum.ClusterCount4DProgress.Z4Plane) :
    reflectJointPairChannelState leftPlane rightPlane target ∈
      jointPairChannelStateSpace cutoff := by
  have hparts := (mem_cartesian_iff _ _ target).mp htarget
  apply (mem_cartesian_iff _ _ _).mpr
  exact ⟨reflectPairChannelState_mem_clean hparts.1 leftPlane,
    reflectPairChannelState_mem_clean hparts.2 rightPlane⟩

private theorem reflectJointPairChannelState_injective
    (leftPlane rightPlane :
      YMGap.Continuum.ClusterCount4DProgress.Z4Plane) :
    Function.Injective
      (reflectJointPairChannelState leftPlane rightPlane) := by
  intro left right heq
  exact (reflectJointPairChannelState_involutive
      leftPlane rightPlane left).symm.trans
    ((congrArg (reflectJointPairChannelState leftPlane rightPlane) heq).trans
      (reflectJointPairChannelState_involutive
        leftPlane rightPlane right))

theorem reflectJointPairChannelStateSpace_perm
    (cutoff : Nat)
    (leftPlane rightPlane :
      YMGap.Continuum.ClusterCount4DProgress.Z4Plane) :
    ((jointPairChannelStateSpace cutoff).map
      (reflectJointPairChannelState leftPlane rightPlane)).Perm
        (jointPairChannelStateSpace cutoff) := by
  apply YMGap.Continuum.Z4CanonicalPolymerUniverse.perm_of_nodup_mem_iff
  · exact nodup_map_of_injective_local
      (reflectJointPairChannelState leftPlane rightPlane)
      (fun {_ _} heq =>
        reflectJointPairChannelState_injective
          leftPlane rightPlane heq)
      (jointPairChannelStateSpace_nodup cutoff)
  · exact jointPairChannelStateSpace_nodup cutoff
  · intro target
    constructor
    · intro htarget
      obtain ⟨source, hsource, hsourceEq⟩ := List.mem_map.mp htarget
      rw [← hsourceEq]
      exact reflectJointPairChannelState_mem hsource leftPlane rightPlane
    · intro htarget
      apply List.mem_map.mpr
      refine ⟨reflectJointPairChannelState leftPlane rightPlane target,
        reflectJointPairChannelState_mem htarget leftPlane rightPlane, ?_⟩
      exact reflectJointPairChannelState_involutive
        leftPlane rightPlane target

private theorem twoFaceProductionLinkFactor_twoPlane_reflection
    (cutoff : Nat)
    (leftPlane rightPlane :
      YMGap.Continuum.ClusterCount4DProgress.Z4Plane)
    (left right : PairChannelState) :
    twoFaceProductionLinkFactor cutoff
        (reflectPairChannelState leftPlane left)
        (reflectPairChannelState rightPlane right) =
      twoFaceProductionLinkFactor cutoff left right := by
  cases leftPlane <;> cases rightPlane <;> rfl

theorem twoFaceCoupledRawWeight_reflection
    (w : Q') (cutoff : Nat)
    (leftPlane rightPlane :
      YMGap.Continuum.ClusterCount4DProgress.Z4Plane)
    (source : StretchedCompatibleFacePair cutoff)
    (target : JointPairChannelState) :
    twoFaceCoupledRawWeight w cutoff
        (reflectStretchedCompatibleFacePair cutoff
          leftPlane rightPlane source)
        (reflectJointPairChannelState leftPlane rightPlane target) ≈
      twoFaceCoupledRawWeight w cutoff source target := by
  unfold twoFaceCoupledRawWeight
    reflectStretchedCompatibleFacePair reflectJointPairChannelState
  exact qmul_congr
    (qmul_congr
      (packetPairChannelRawWeight_reflection
        w leftPlane source.left.val target.1)
      (packetPairChannelRawWeight_reflection
        w rightPlane source.right.val target.2))
    (Q'.eqv_of_eq
      (twoFaceProductionLinkFactor_twoPlane_reflection
        cutoff leftPlane rightPlane target.1 target.2))

theorem twoFaceCoupledPartition_reflection
    (w : Q') (cutoff : Nat)
    (leftPlane rightPlane :
      YMGap.Continuum.ClusterCount4DProgress.Z4Plane)
    (source : StretchedCompatibleFacePair cutoff) :
    twoFaceCoupledPartition w cutoff
        (reflectStretchedCompatibleFacePair cutoff
          leftPlane rightPlane source) ≈
      twoFaceCoupledPartition w cutoff source := by
  let reflectedSource := reflectStretchedCompatibleFacePair cutoff
    leftPlane rightPlane source
  let reflectTarget := reflectJointPairChannelState leftPlane rightPlane
  let targets := jointPairChannelStateSpace cutoff
  refine Q'.eqv_trans _
    (listQSum (twoFaceCoupledRawWeight w cutoff reflectedSource)
      (targets.map reflectTarget)) _ ?_ ?_
  · exact YMGap.Continuum.Z4CanonicalPolymerRange.listQSum_perm _
      (reflectJointPairChannelStateSpace_perm
        cutoff leftPlane rightPlane).symm
  · rw [listQSum_map]
    apply listQSum_congr_on
    intro target _
    exact twoFaceCoupledRawWeight_reflection
      w cutoff leftPlane rightPlane source target

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

theorem twoFaceCoupledConditionalKernel_reflection_equivariant
    (w : Q') (hw : (0 : Q') < w) (cutoff : Nat)
    (leftPlane rightPlane :
      YMGap.Continuum.ClusterCount4DProgress.Z4Plane)
    (source : StretchedCompatibleFacePair cutoff)
    (target : JointPairChannelState) :
    twoFaceCoupledConditionalKernel w hw cutoff
        (reflectStretchedCompatibleFacePair cutoff
          leftPlane rightPlane source)
        (reflectJointPairChannelState leftPlane rightPlane target) ≈
      twoFaceCoupledConditionalKernel w hw cutoff source target := by
  unfold twoFaceCoupledConditionalKernel
  exact divPos_eqv_congr_local
    (twoFaceCoupledPartition_pos hw cutoff
      (reflectStretchedCompatibleFacePair cutoff
        leftPlane rightPlane source))
    (twoFaceCoupledPartition_pos hw cutoff source)
    (twoFaceCoupledRawWeight_reflection
      w cutoff leftPlane rightPlane source target)
    (twoFaceCoupledPartition_reflection
      w cutoff leftPlane rightPlane source)

/-! ## 5. Non-vacuity of the compatible carrier -/

def vacuumCompatibleFacePair : StretchedCompatibleFacePair 1 where
  left := vacuumBoundedFaceSpinPacket
  right := vacuumBoundedFaceSpinPacket
  total_eq := rfl

def oneFundamentalCompatibleFacePair : StretchedCompatibleFacePair 1 where
  left := oneFaceFundamentalBoundedPacket
  right := oneFaceFundamentalBoundedPacket
  total_eq := rfl

theorem compatible_carrier_has_distinct_sources :
    vacuumCompatibleFacePair.left.val ≠
      oneFundamentalCompatibleFacePair.left.val := by
  intro heq
  have hspin := congrArg FaceSpinPacket.spin0 heq
  change (0 : Nat) = 1 at hspin
  omega

/-! ## Dependency gates -/

#print axioms jointPairChannelStateSpace_nodup
#print axioms compatibleStretchedTarget_mem
#print axioms twoFaceCoupledRawWeight_nonnegative
#print axioms compatibleStretched_rawWeight_pos
#print axioms twoFaceCoupledPartition_pos
#print axioms twoFaceCoupledConditionalKernel_row_normalized
#print axioms reflectJointPairChannelStateSpace_perm
#print axioms twoFaceCoupledRawWeight_reflection
#print axioms twoFaceCoupledPartition_reflection
#print axioms twoFaceCoupledConditionalKernel_reflection_equivariant
#print axioms compatible_carrier_has_distinct_sources

end YMGap.Continuum.Z4DyadicSlabTwoFaceCoupledConditionalKernel
