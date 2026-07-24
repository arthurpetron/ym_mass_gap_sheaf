/-
# All-cutoff recoupling kernel on an adjacent-cube shared face

Two cube-channel targets cannot be multiplied independently when their cubes
share a plaquette.  The coarse character on the right face of the left cube
and the coarse character on the left face of the right cube must first fuse
to one shared-face channel `u`.  At each of the four boundary links of that
plaquette, the two outer-face characters must fuse with the same `u`.

For compatible stretched cube sources this gives the exact local factor

    N(sL,sR;u)
      * N(bL,bR;u) * N(tL,tR;u)
      * N(fL,fR;u) * N(kL,kR;u).

The stretched channel `u = commonTotalL + commonTotalR` makes all five
Clebsch--Gordan indicators one, so the derived denominator is strictly
positive at every cutoff.  Normalizing after this complete shared-face
recoupling yields a nonnegative row-stochastic kernel.  Vacuum and
fundamental sources give distinct rows, and arbitrary per-face corrected-slab
reflection leaves the kernel invariant because it preserves every final
coarse character.

This closes the local all-cutoff shared-face fiber.  It does not yet multiply
the remaining sixteen outer-link factors, sum over both six-face cube target
spaces, or identify a whole-slab Gibbs pushforward.
-/

import YMGap.Continuum.Z4DyadicSlabCubeCoupledConditionalKernel

namespace YMGap.Continuum.Z4AdjacentCubeSharedFaceRecouplingKernel

set_option maxRecDepth 20000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4DyadicSlabCharacterFusionConditionalKernel
open YMGap.Continuum.Z4DyadicSlabCubeCoupledConditionalKernel
open YMGap.Continuum.Z4DyadicSlabMultiCharacterPacketKernel
open YMGap.Continuum.Z4DyadicSlabTwoFaceCoupledConditionalKernel
open YMGap.Continuum.Z4DyadicUnitCubeBlockGeometry

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The shared-face fiber -/

structure AdjacentCubeStretchedSource (cutoff : Nat) where
  left : CubeStretchedCompatibleSource cutoff
  right : CubeStretchedCompatibleSource cutoff

def cubeTargetSpin
    (target : CubePairChannelState) (face : CubeFaceIndex) : Nat :=
  (cubeTargetAt target face).2

def adjacentCubeSharedFaceTargetRawWeight
    (left right : CubePairChannelState) (fused : Nat) : Q' :=
  fusionInd
      (cubeTargetSpin left .rightYZ)
      (cubeTargetSpin right .leftYZ) fused *
    (fusionInd
        (cubeTargetSpin left .bottomXY)
        (cubeTargetSpin right .bottomXY) fused *
      (fusionInd
          (cubeTargetSpin left .topXY)
          (cubeTargetSpin right .topXY) fused *
        (fusionInd
            (cubeTargetSpin left .frontXZ)
            (cubeTargetSpin right .frontXZ) fused *
          fusionInd
            (cubeTargetSpin left .backXZ)
            (cubeTargetSpin right .backXZ) fused)))

def adjacentCubeSharedFaceRawWeight
    {cutoff : Nat} (source : AdjacentCubeStretchedSource cutoff)
    (fused : Nat) : Q' :=
  adjacentCubeSharedFaceTargetRawWeight
    (compatibleCubeTarget source.left)
    (compatibleCubeTarget source.right) fused

theorem adjacentCubeSharedFaceTargetRawWeight_nonnegative
    (left right : CubePairChannelState) (fused : Nat) :
    (0 : Q') ≤
      adjacentCubeSharedFaceTargetRawWeight left right fused := by
  unfold adjacentCubeSharedFaceTargetRawWeight
  exact Q'.mul_nonneg _ _
    (fusionInd_nonneg _ _ _)
    (Q'.mul_nonneg _ _
      (fusionInd_nonneg _ _ _)
      (Q'.mul_nonneg _ _
        (fusionInd_nonneg _ _ _)
        (Q'.mul_nonneg _ _
          (fusionInd_nonneg _ _ _)
          (fusionInd_nonneg _ _ _))))

theorem adjacentCubeSharedFaceRawWeight_nonnegative
    {cutoff : Nat} (source : AdjacentCubeStretchedSource cutoff)
    (fused : Nat) :
    (0 : Q') ≤ adjacentCubeSharedFaceRawWeight source fused := by
  unfold adjacentCubeSharedFaceRawWeight
  exact adjacentCubeSharedFaceTargetRawWeight_nonnegative _ _ _

theorem compatibleCubeTarget_spin_eq_commonTotal
    {cutoff : Nat} (source : CubeStretchedCompatibleSource cutoff)
    (face : CubeFaceIndex) :
    cubeTargetSpin (compatibleCubeTarget source) face =
      source.commonTotal := by
  unfold cubeTargetSpin
  rw [compatibleCubeTarget_at]
  unfold stretchedPairChannelState
  exact source.total_eq face

theorem adjacentCubeSharedFaceRawWeight_eq_commonTotals
    {cutoff : Nat} (source : AdjacentCubeStretchedSource cutoff)
    (fused : Nat) :
    adjacentCubeSharedFaceRawWeight source fused =
      fusionInd source.left.commonTotal source.right.commonTotal fused *
        (fusionInd source.left.commonTotal source.right.commonTotal fused *
          (fusionInd source.left.commonTotal source.right.commonTotal fused *
            (fusionInd source.left.commonTotal source.right.commonTotal fused *
      fusionInd source.left.commonTotal
                source.right.commonTotal fused))) := by
  simp only [adjacentCubeSharedFaceRawWeight,
    adjacentCubeSharedFaceTargetRawWeight]
  rw [compatibleCubeTarget_spin_eq_commonTotal,
    compatibleCubeTarget_spin_eq_commonTotal,
    compatibleCubeTarget_spin_eq_commonTotal,
    compatibleCubeTarget_spin_eq_commonTotal,
    compatibleCubeTarget_spin_eq_commonTotal,
    compatibleCubeTarget_spin_eq_commonTotal,
    compatibleCubeTarget_spin_eq_commonTotal,
    compatibleCubeTarget_spin_eq_commonTotal,
    compatibleCubeTarget_spin_eq_commonTotal,
    compatibleCubeTarget_spin_eq_commonTotal]

def adjacentCubeSharedFaceStateSpace (cutoff : Nat) : List Nat :=
  List.range (8 * cutoff + 1)

private theorem range_nodup_local : ∀ n : Nat, (List.range n).Nodup
  | 0 => List.nodup_nil
  | n + 1 => by
      rw [List.range_succ]
      apply List.nodup_append.mpr
      exact ⟨range_nodup_local n,
        List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩,
        fun x hx y hy hxy => by
          have hyN : y = n := List.mem_singleton.mp hy
          rw [hxy, hyN] at hx
          exact absurd (List.mem_range.mp hx) (Nat.lt_irrefl n)⟩

theorem adjacentCubeSharedFaceStateSpace_nodup (cutoff : Nat) :
    (adjacentCubeSharedFaceStateSpace cutoff).Nodup :=
  range_nodup_local _

/-! ## 2. A uniformly available stretched witness -/

theorem cubeSource_commonTotal_le_four_cutoff
    {cutoff : Nat} (source : CubeStretchedCompatibleSource cutoff) :
    source.commonTotal ≤ 4 * cutoff := by
  have hpacket :=
    (source.packet .bottomXY).property
  have hbounds :=
    (mem_faceSpinPacketStateSpace_iff cutoff
      (source.packet .bottomXY).val).mp hpacket
  rw [← source.total_eq .bottomXY]
  unfold faceSpinTotal
  exact Nat.le_trans
    (Nat.add_le_add
      (Nat.add_le_add
        (Nat.add_le_add hbounds.1 hbounds.2.1)
        hbounds.2.2.1)
      hbounds.2.2.2)
    (by omega)

def adjacentCubeStretchedFusedChannel
    {cutoff : Nat} (source : AdjacentCubeStretchedSource cutoff) : Nat :=
  source.left.commonTotal + source.right.commonTotal

theorem adjacentCubeStretchedFusedChannel_mem
    {cutoff : Nat} (source : AdjacentCubeStretchedSource cutoff) :
    adjacentCubeStretchedFusedChannel source ∈
      adjacentCubeSharedFaceStateSpace cutoff := by
  apply List.mem_range.mpr
  have hleft := cubeSource_commonTotal_le_four_cutoff source.left
  have hright := cubeSource_commonTotal_le_four_cutoff source.right
  change source.left.commonTotal + source.right.commonTotal <
    8 * cutoff + 1
  omega

theorem adjacentCubeStretchedRawWeight_eqv_one
    {cutoff : Nat} (source : AdjacentCubeStretchedSource cutoff) :
    adjacentCubeSharedFaceRawWeight source
        (adjacentCubeStretchedFusedChannel source) ≈ 1 := by
  rw [adjacentCubeSharedFaceRawWeight_eq_commonTotals]
  unfold adjacentCubeStretchedFusedChannel
  rw [fusionInd_add_eq_one]
  decide

/-! ## 3. Normalize once after all five interface constraints -/

def adjacentCubeSharedFacePartition
    {cutoff : Nat} (source : AdjacentCubeStretchedSource cutoff) : Q' :=
  listQSum (adjacentCubeSharedFaceRawWeight source)
    (adjacentCubeSharedFaceStateSpace cutoff)

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

theorem adjacentCubeSharedFacePartition_pos
    {cutoff : Nat} (source : AdjacentCubeStretchedSource cutoff) :
    (0 : Q') < adjacentCubeSharedFacePartition source := by
  have hwitness :
      (0 : Q') <
        adjacentCubeSharedFaceRawWeight source
          (adjacentCubeStretchedFusedChannel source) :=
    Q'.pos_of_lt_of_le (by decide)
      (Q'.le_of_eqv
        (Q'.eqv_symm (adjacentCubeStretchedRawWeight_eqv_one source)))
  have hle := listQSum_member_le_local
    (adjacentCubeSharedFaceRawWeight source)
    (adjacentCubeSharedFaceRawWeight_nonnegative source)
    (adjacentCubeSharedFaceStateSpace cutoff)
    (adjacentCubeStretchedFusedChannel_mem source)
  exact Q'.pos_of_lt_of_le hwitness hle

def adjacentCubeSharedFaceConditionalKernel
    {cutoff : Nat} (source : AdjacentCubeStretchedSource cutoff)
    (fused : Nat) : Q' :=
  Q'.divPos
    (adjacentCubeSharedFaceRawWeight source fused)
    (adjacentCubeSharedFacePartition source)
    (adjacentCubeSharedFacePartition_pos source)

theorem adjacentCubeSharedFaceConditionalKernel_nonnegative
    {cutoff : Nat} (source : AdjacentCubeStretchedSource cutoff)
    (fused : Nat) :
    (0 : Q') ≤ adjacentCubeSharedFaceConditionalKernel source fused := by
  unfold adjacentCubeSharedFaceConditionalKernel Q'.divPos
  exact Q'.mul_nonneg _ _
    (adjacentCubeSharedFaceRawWeight_nonnegative source fused)
    (Q'.le_of_lt (Q'.recipPos_pos _ _))

theorem adjacentCubeSharedFaceConditionalKernel_row_normalized
    {cutoff : Nat} (source : AdjacentCubeStretchedSource cutoff) :
    listQSum (adjacentCubeSharedFaceConditionalKernel source)
        (adjacentCubeSharedFaceStateSpace cutoff) ≈ 1 := by
  unfold adjacentCubeSharedFaceConditionalKernel Q'.divPos
  exact Q'.eqv_trans _
    (adjacentCubeSharedFacePartition source *
      Q'.recipPos (adjacentCubeSharedFacePartition source)
        (adjacentCubeSharedFacePartition_pos source)) _
    (listQSum_mul_right
      (adjacentCubeSharedFaceRawWeight source)
      (Q'.recipPos (adjacentCubeSharedFacePartition source)
        (adjacentCubeSharedFacePartition_pos source))
      (adjacentCubeSharedFaceStateSpace cutoff))
    (Q'.mul_recipPos_eqv _
      (adjacentCubeSharedFacePartition_pos source))

/-! ## 4. Corrected-slab reflection invariance -/

def reflectAdjacentCubeStretchedSource
    {cutoff : Nat}
    (leftPlanes rightPlanes : CubeReflectionPlanes)
    (source : AdjacentCubeStretchedSource cutoff) :
    AdjacentCubeStretchedSource cutoff where
  left := reflectCubeCompatibleSource cutoff leftPlanes source.left
  right := reflectCubeCompatibleSource cutoff rightPlanes source.right

theorem reflectedAdjacent_commonTotals
    {cutoff : Nat}
    (leftPlanes rightPlanes : CubeReflectionPlanes)
    (source : AdjacentCubeStretchedSource cutoff) :
    (reflectAdjacentCubeStretchedSource
        leftPlanes rightPlanes source).left.commonTotal =
        source.left.commonTotal ∧
      (reflectAdjacentCubeStretchedSource
        leftPlanes rightPlanes source).right.commonTotal =
        source.right.commonTotal := by
  exact ⟨rfl, rfl⟩

theorem adjacentCubeSharedFaceRawWeight_reflection
    {cutoff : Nat}
    (leftPlanes rightPlanes : CubeReflectionPlanes)
    (source : AdjacentCubeStretchedSource cutoff)
    (fused : Nat) :
    adjacentCubeSharedFaceRawWeight
        (reflectAdjacentCubeStretchedSource
          leftPlanes rightPlanes source) fused =
      adjacentCubeSharedFaceRawWeight source fused := by
  rw [adjacentCubeSharedFaceRawWeight_eq_commonTotals,
    adjacentCubeSharedFaceRawWeight_eq_commonTotals]
  rfl

theorem adjacentCubeSharedFacePartition_reflection
    {cutoff : Nat}
    (leftPlanes rightPlanes : CubeReflectionPlanes)
    (source : AdjacentCubeStretchedSource cutoff) :
    adjacentCubeSharedFacePartition
        (reflectAdjacentCubeStretchedSource
          leftPlanes rightPlanes source) =
      adjacentCubeSharedFacePartition source := by
  unfold adjacentCubeSharedFacePartition
  apply congrArg
    (fun weight =>
      listQSum weight (adjacentCubeSharedFaceStateSpace cutoff))
  funext fused
  exact adjacentCubeSharedFaceRawWeight_reflection
    leftPlanes rightPlanes source fused

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

theorem adjacentCubeSharedFaceConditionalKernel_reflection
    {cutoff : Nat}
    (leftPlanes rightPlanes : CubeReflectionPlanes)
    (source : AdjacentCubeStretchedSource cutoff)
    (fused : Nat) :
    adjacentCubeSharedFaceConditionalKernel
        (reflectAdjacentCubeStretchedSource
          leftPlanes rightPlanes source) fused ≈
      adjacentCubeSharedFaceConditionalKernel source fused := by
  unfold adjacentCubeSharedFaceConditionalKernel
  exact divPos_eqv_congr_local
    (adjacentCubeSharedFacePartition_pos
      (reflectAdjacentCubeStretchedSource
        leftPlanes rightPlanes source))
    (adjacentCubeSharedFacePartition_pos source)
    (Q'.eqv_of_eq
      (adjacentCubeSharedFaceRawWeight_reflection
        leftPlanes rightPlanes source fused))
    (Q'.eqv_of_eq
      (adjacentCubeSharedFacePartition_reflection
        leftPlanes rightPlanes source))

/-! ## 5. Exact source dependence -/

def vacuumAdjacentCubeStretchedSource :
    AdjacentCubeStretchedSource 1 where
  left := vacuumCubeCompatibleSource
  right := vacuumCubeCompatibleSource

def fundamentalAdjacentCubeStretchedSource :
    AdjacentCubeStretchedSource 1 where
  left := oneFundamentalCubeCompatibleSource
  right := oneFundamentalCubeCompatibleSource

theorem vacuumAdjacentCubeKernel_zero_eqv_one :
    adjacentCubeSharedFaceConditionalKernel
        vacuumAdjacentCubeStretchedSource 0 ≈ 1 := by
  decide

def oneHalf : Q' := Q'.mkPos 1 2 (by decide)

theorem fundamentalAdjacentCubeKernel_zero_eqv_oneHalf :
    adjacentCubeSharedFaceConditionalKernel
        fundamentalAdjacentCubeStretchedSource 0 ≈ oneHalf := by
  decide

theorem adjacentCubeSharedFaceConditionalKernel_source_dependent :
    ¬ adjacentCubeSharedFaceConditionalKernel
          vacuumAdjacentCubeStretchedSource 0 ≈
        adjacentCubeSharedFaceConditionalKernel
          fundamentalAdjacentCubeStretchedSource 0 := by
  intro hequal
  have hfalse : (1 : Q') ≈ oneHalf :=
    Q'.eqv_trans _ _ _
      (Q'.eqv_symm vacuumAdjacentCubeKernel_zero_eqv_one)
      (Q'.eqv_trans _ _ _ hequal
        fundamentalAdjacentCubeKernel_zero_eqv_oneHalf)
  exact (by decide : ¬ (1 : Q') ≈ oneHalf) hfalse

#print axioms adjacentCubeSharedFaceRawWeight_nonnegative
#print axioms cubeSource_commonTotal_le_four_cutoff
#print axioms adjacentCubeStretchedFusedChannel_mem
#print axioms adjacentCubeStretchedRawWeight_eqv_one
#print axioms adjacentCubeSharedFacePartition_pos
#print axioms adjacentCubeSharedFaceConditionalKernel_nonnegative
#print axioms adjacentCubeSharedFaceConditionalKernel_row_normalized
#print axioms adjacentCubeSharedFaceConditionalKernel_reflection
#print axioms vacuumAdjacentCubeKernel_zero_eqv_one
#print axioms fundamentalAdjacentCubeKernel_zero_eqv_oneHalf
#print axioms adjacentCubeSharedFaceConditionalKernel_source_dependent

end YMGap.Continuum.Z4AdjacentCubeSharedFaceRecouplingKernel
