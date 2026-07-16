/-
# Two corrected-slab face rows at one production shared link

The character/fusion row of a corrected dyadic face is normalized before it
is coupled to its neighbours.  This file performs the smallest literal
production gluing test: two such rows meet at a degree-two coarse link.  The
link factor is not invented here; it is the existing
`explicitValenceMultiplicity` at degree two and coarse cutoff `4*K`.

That production factor is exactly the vacuum Clebsch--Gordan guard on the two
coarse output spins.  Hence the pointwise glued weight is the product of the
two conditional rows followed by the exact shared-link Haar projection.
Reflection intertwining survives this projection.

The same calculation banks a constructive normalization fence.  At cutoff
one the vacuum fine packet has support only at coarse spin zero, whereas the
packet with one fundamental fine face has support only at coarse spin one.
Both rows are individually normalized, but their product is killed at every
target pair by the production degree-two link factor.  Thus independently
normalizing face rows cannot by itself define the joint physical Gibbs
kernel; a link-coupled partition must be derived before iteration.
-/

import YMGap.Continuum.Z4DyadicSlabCharacterFusionConditionalKernel
import YMGap.Continuum.Z4FusionPathZeroInsertion

namespace YMGap.Continuum.Z4DyadicSlabTwoFaceSharedLinkKernel

set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FusionQuotientCollapse
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4DyadicSlabCharacterFusionConditionalKernel
open YMGap.Continuum.Z4DyadicSlabReflectionParityKernel
open YMGap.Continuum.Z4ExplicitValenceFusionMultiplicity
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FusionPathZeroInsertion
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local infix:50 " ≈ " => Q'.eqv

private theorem qmul_congr {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

private theorem mul_eqv_zero_of_left {a b : Q'} (ha : a ≈ 0) :
    a * b ≈ 0 :=
  Q'.eqv_trans _ (0 * b) _
    (Q'.mul_eqv_congr_right _ _ b ha) (Q'.zero_mul_eqv b)

private theorem mul_eqv_zero_of_right {a b : Q'} (hb : b ≈ 0) :
    a * b ≈ 0 :=
  Q'.eqv_trans _ (a * 0) _
    (Q'.mul_eqv_congr_left a _ _ hb) (Q'.mul_zero_eqv a)

private theorem ofNat_nonnegative_local (n : Nat) :
    (0 : Q') ≤ Q'.ofNat n := by
  rw [Q'.zero_le_iff_num_nonneg]
  exact Int.natCast_nonneg n

/-! ## 1. The literal degree-two production link factor -/

/-- The two coarse output spins placed in the first two external slots of
the production link resolver. -/
def twoFaceCoarseExternal
    (left right : PairChannelState) :
    YMGap.Continuum.SU2FundamentalPentagonFiniteGraph.EdgeLabelling :=
  fun (position : Nat) =>
  if position = 0 then left.2
  else if position = 1 then right.2
  else 0

/-- Exact local spin-foam link factor for two coarse faces.  A fine cutoff
`K` produces coarse spins through `4*K`, so the production auxiliary window
is the standard `6*(4*K)` window. -/
def twoFaceProductionLinkFactor
    (fineCutoff : Nat) (left right : PairChannelState) : Q' :=
  Q'.ofNat
    (explicitValenceMultiplicity (linkAuxiliaryCutoff (4 * fineCutoff)) 2
      (twoFaceCoarseExternal left right))

/-- The literal degree-two production resolver is precisely the vacuum
Clebsch--Gordan projection on the two coarse characters. -/
theorem twoFaceProductionLinkFactor_eq_fusionInd
    (fineCutoff : Nat) (left right : PairChannelState) :
    twoFaceProductionLinkFactor fineCutoff left right ≈
      fusionInd left.2 right.2 0 := by
  unfold twoFaceProductionLinkFactor explicitValenceMultiplicity
    twoFaceCoarseExternal
  rw [twoValentMultiplicity_eq_bool_zero_output]
  unfold boolMultiplicity fusionInd
  cases h : fusionOK left.2 right.2 0 <;> simp [h] <;> decide

theorem twoFaceProductionLinkFactor_reflection
    (fineCutoff : Nat)
    (plane : YMGap.Continuum.ClusterCount4DProgress.Z4Plane)
    (left right : PairChannelState) :
    twoFaceProductionLinkFactor fineCutoff
        (reflectPairChannelState plane left)
        (reflectPairChannelState plane right) =
      twoFaceProductionLinkFactor fineCutoff left right := by
  cases plane <;> rfl

/-! ## 2. Product of two face rows against the production factor -/

def twoFaceSharedLinkConditionalWeight
    (w : Q') (hw : (0 : Q') < w) (fineCutoff : Nat)
    (leftSource rightSource : BoundedFaceSpinPacket fineCutoff)
    (leftTarget rightTarget : PairChannelState) : Q' :=
  (packetPairChannelConditionalKernel w hw fineCutoff
      leftSource leftTarget *
    packetPairChannelConditionalKernel w hw fineCutoff
      rightSource rightTarget) *
    twoFaceProductionLinkFactor fineCutoff leftTarget rightTarget

/-- Pointwise, shared-link gluing is exactly the product of the two face
conditionals followed by the vacuum fusion guard. -/
theorem twoFaceSharedLinkConditionalWeight_eq_fusion_guard
    (w : Q') (hw : (0 : Q') < w) (fineCutoff : Nat)
    (leftSource rightSource : BoundedFaceSpinPacket fineCutoff)
    (leftTarget rightTarget : PairChannelState) :
    twoFaceSharedLinkConditionalWeight w hw fineCutoff
        leftSource rightSource leftTarget rightTarget ≈
      (packetPairChannelConditionalKernel w hw fineCutoff
          leftSource leftTarget *
        packetPairChannelConditionalKernel w hw fineCutoff
          rightSource rightTarget) *
        fusionInd leftTarget.2 rightTarget.2 0 := by
  unfold twoFaceSharedLinkConditionalWeight
  exact Q'.mul_eqv_congr_left _ _ _
    (twoFaceProductionLinkFactor_eq_fusionInd
      fineCutoff leftTarget rightTarget)

theorem twoFaceSharedLinkConditionalWeight_nonnegative
    (w : Q') (hw : (0 : Q') < w) (fineCutoff : Nat)
    (leftSource rightSource : BoundedFaceSpinPacket fineCutoff)
    (leftTarget rightTarget : PairChannelState) :
    (0 : Q') ≤ twoFaceSharedLinkConditionalWeight w hw fineCutoff
      leftSource rightSource leftTarget rightTarget := by
  unfold twoFaceSharedLinkConditionalWeight twoFaceProductionLinkFactor
  exact Q'.mul_nonneg _ _
    (Q'.mul_nonneg _ _
      (packetPairChannelConditionalKernel_nonnegative
        w hw fineCutoff leftSource leftTarget)
      (packetPairChannelConditionalKernel_nonnegative
        w hw fineCutoff rightSource rightTarget))
    (ofNat_nonnegative_local _)

/-- The exact two-face gluing still intertwines corrected-slab reflection;
the production link projection only reads the reflection-fixed coarse spin. -/
theorem twoFaceSharedLinkConditionalWeight_reflection_equivariant
    (w : Q') (hw : (0 : Q') < w) (fineCutoff : Nat)
    (plane : YMGap.Continuum.ClusterCount4DProgress.Z4Plane)
    (leftSource rightSource : BoundedFaceSpinPacket fineCutoff)
    (leftTarget rightTarget : PairChannelState) :
    twoFaceSharedLinkConditionalWeight w hw fineCutoff
        (reflectBoundedFaceSpinPacket fineCutoff plane leftSource)
        (reflectBoundedFaceSpinPacket fineCutoff plane rightSource)
        (reflectPairChannelState plane leftTarget)
        (reflectPairChannelState plane rightTarget) ≈
      twoFaceSharedLinkConditionalWeight w hw fineCutoff
        leftSource rightSource leftTarget rightTarget := by
  unfold twoFaceSharedLinkConditionalWeight
  exact qmul_congr
    (qmul_congr
      (packetPairChannelConditionalKernel_reflection_equivariant
        w hw fineCutoff plane leftSource leftTarget)
      (packetPairChannelConditionalKernel_reflection_equivariant
        w hw fineCutoff plane rightSource rightTarget))
    (Q'.eqv_of_eq
      (twoFaceProductionLinkFactor_reflection
        fineCutoff plane leftTarget rightTarget))

def twoFaceSharedLinkConditionalMass
    (w : Q') (hw : (0 : Q') < w) (fineCutoff : Nat)
    (leftSource rightSource : BoundedFaceSpinPacket fineCutoff) : Q' :=
  listQSum (fun leftTarget =>
    listQSum (fun rightTarget =>
      twoFaceSharedLinkConditionalWeight w hw fineCutoff
        leftSource rightSource leftTarget rightTarget)
      (pairChannelStateSpace fineCutoff))
    (pairChannelStateSpace fineCutoff)

/-! ## 3. A machine-checked normalization obstruction -/

theorem vacuum_raw_zero_of_coarse_ne_zero
    (w : Q') (state : PairChannelState) (hcoarse : state.2 ≠ 0) :
    packetPairChannelRawWeight w vacuumFaceSpinPacket state ≈ 0 := by
  rcases state with ⟨⟨left, right⟩, coarse⟩
  simp only at hcoarse
  unfold packetPairChannelRawWeight vacuumFaceSpinPacket
  change coeffW w coarse *
    (fusionInd 0 0 left *
      (fusionInd 0 0 right * fusionInd left right coarse)) ≈ 0
  by_cases hleft : left = 0
  · subst left
    by_cases hright : right = 0
    · subst right
      have hzero : fusionInd 0 0 coarse = 0 := by
        rw [YMGap.Continuum.FusedFreeSplit.fusionInd_zero_left,
          if_neg (fun h => hcoarse h.symm)]
      rw [hzero]
      exact mul_eqv_zero_of_right
        (mul_eqv_zero_of_right (Q'.mul_zero_eqv _))
    · have hzero : fusionInd 0 0 right = 0 := by
        rw [YMGap.Continuum.FusedFreeSplit.fusionInd_zero_left,
          if_neg (fun h => hright h.symm)]
      rw [hzero]
      exact mul_eqv_zero_of_right
        (mul_eqv_zero_of_right (Q'.zero_mul_eqv _))
  · have hzero : fusionInd 0 0 left = 0 := by
      rw [YMGap.Continuum.FusedFreeSplit.fusionInd_zero_left,
        if_neg (fun h => hleft h.symm)]
    rw [hzero]
    exact mul_eqv_zero_of_right (Q'.zero_mul_eqv _)

theorem oneFundamental_raw_zero_of_coarse_ne_one
    (w : Q') (state : PairChannelState) (hcoarse : state.2 ≠ 1) :
    packetPairChannelRawWeight w oneFaceFundamentalPacket state ≈ 0 := by
  rcases state with ⟨⟨left, right⟩, coarse⟩
  simp only at hcoarse
  unfold packetPairChannelRawWeight oneFaceFundamentalPacket
  change coeffW w coarse *
    (fusionInd 1 0 left *
      (fusionInd 0 0 right * fusionInd left right coarse)) ≈ 0
  by_cases hleft : left = 1
  · subst left
    by_cases hright : right = 0
    · subst right
      have hzero : fusionInd 1 0 coarse = 0 := by
        rw [YMGap.Continuum.FusedFreeSplit.fusionInd_zero_right,
          if_neg (fun h => hcoarse h.symm)]
      rw [hzero]
      exact mul_eqv_zero_of_right
        (mul_eqv_zero_of_right (Q'.mul_zero_eqv _))
    · have hzero : fusionInd 0 0 right = 0 := by
        rw [YMGap.Continuum.FusedFreeSplit.fusionInd_zero_left,
          if_neg (fun h => hright h.symm)]
      rw [hzero]
      exact mul_eqv_zero_of_right
        (mul_eqv_zero_of_right (Q'.zero_mul_eqv _))
  · have hzero : fusionInd 1 0 left = 0 := by
      rw [YMGap.Continuum.FusedFreeSplit.fusionInd_zero_right,
        if_neg (fun h => hleft h.symm)]
    rw [hzero]
    exact mul_eqv_zero_of_right (Q'.zero_mul_eqv _)

private theorem conditionalKernel_eqv_zero_of_raw
    (w : Q') (hw : (0 : Q') < w) (fineCutoff : Nat)
    (source : BoundedFaceSpinPacket fineCutoff)
    (target : PairChannelState)
    (hraw : packetPairChannelRawWeight w source.val target ≈ 0) :
    packetPairChannelConditionalKernel w hw fineCutoff source target ≈
      0 := by
  unfold packetPairChannelConditionalKernel Q'.divPos
  exact mul_eqv_zero_of_left hraw

theorem vacuum_kernel_zero_of_coarse_ne_zero
    (w : Q') (hw : (0 : Q') < w) (state : PairChannelState)
    (hcoarse : state.2 ≠ 0) :
    packetPairChannelConditionalKernel w hw 1
        vacuumBoundedFaceSpinPacket state ≈ 0 := by
  apply conditionalKernel_eqv_zero_of_raw
  exact vacuum_raw_zero_of_coarse_ne_zero w state hcoarse

theorem oneFundamental_kernel_zero_of_coarse_ne_one
    (w : Q') (hw : (0 : Q') < w) (state : PairChannelState)
    (hcoarse : state.2 ≠ 1) :
    packetPairChannelConditionalKernel w hw 1
        oneFaceFundamentalBoundedPacket state ≈ 0 := by
  apply conditionalKernel_eqv_zero_of_raw
  exact oneFundamental_raw_zero_of_coarse_ne_one w state hcoarse

/-- Every target pair is annihilated: either the vacuum row is off coarse
spin zero, the fundamental row is off coarse spin one, or the exact
degree-two production link rejects the unequal outputs zero and one. -/
theorem vacuum_fundamental_sharedLinkWeight_eqv_zero
    (w : Q') (hw : (0 : Q') < w)
    (leftTarget rightTarget : PairChannelState) :
    twoFaceSharedLinkConditionalWeight w hw 1
        vacuumBoundedFaceSpinPacket oneFaceFundamentalBoundedPacket
        leftTarget rightTarget ≈ 0 := by
  by_cases hleft : leftTarget.2 = 0
  · by_cases hright : rightTarget.2 = 1
    · unfold twoFaceSharedLinkConditionalWeight
      apply mul_eqv_zero_of_right
      refine Q'.eqv_trans _ (fusionInd leftTarget.2 rightTarget.2 0) _
        (twoFaceProductionLinkFactor_eq_fusionInd 1 leftTarget rightTarget) ?_
      rw [hleft, hright]
      decide
    · unfold twoFaceSharedLinkConditionalWeight
      apply mul_eqv_zero_of_left
      apply mul_eqv_zero_of_right
      exact oneFundamental_kernel_zero_of_coarse_ne_one
        w hw rightTarget hright
  · unfold twoFaceSharedLinkConditionalWeight
    apply mul_eqv_zero_of_left
    apply mul_eqv_zero_of_left
    exact vacuum_kernel_zero_of_coarse_ne_zero
      w hw leftTarget hleft

theorem vacuum_fundamental_sharedLinkMass_eqv_zero
    (w : Q') (hw : (0 : Q') < w) :
    twoFaceSharedLinkConditionalMass w hw 1
        vacuumBoundedFaceSpinPacket oneFaceFundamentalBoundedPacket ≈
      0 := by
  unfold twoFaceSharedLinkConditionalMass
  refine Q'.eqv_trans _
    (listQSum (fun _ : PairChannelState => (0 : Q'))
      (pairChannelStateSpace 1)) _ ?_ (listQSum_zero _)
  apply listQSum_congr_on
  intro leftTarget _
  refine Q'.eqv_trans _
    (listQSum (fun _ : PairChannelState => (0 : Q'))
      (pairChannelStateSpace 1)) _ ?_ (listQSum_zero _)
  apply listQSum_congr_on
  intro rightTarget _
  exact vacuum_fundamental_sharedLinkWeight_eqv_zero
    w hw leftTarget rightTarget

theorem vacuum_fundamental_sharedLinkMass_not_normalized
    (w : Q') (hw : (0 : Q') < w) :
    ¬ (twoFaceSharedLinkConditionalMass w hw 1
        vacuumBoundedFaceSpinPacket oneFaceFundamentalBoundedPacket ≈ 1) := by
  intro hnormalized
  have hzeroOne : (0 : Q') ≈ 1 :=
    Q'.eqv_trans _ _ _
      (Q'.eqv_symm
        (vacuum_fundamental_sharedLinkMass_eqv_zero w hw))
      hnormalized
  have hnot : ¬ ((0 : Q') ≈ 1) := by decide
  exact hnot hzeroOne

/-- Both face rows pass their individual normalization theorem, while their
literal production shared-link gluing has zero rather than unit mass. -/
theorem independent_rows_normalized_but_shared_link_not
    (w : Q') (hw : (0 : Q') < w) :
    listQSum
        (packetPairChannelConditionalKernel w hw 1
          vacuumBoundedFaceSpinPacket)
        (pairChannelStateSpace 1) ≈ 1 ∧
      listQSum
        (packetPairChannelConditionalKernel w hw 1
          oneFaceFundamentalBoundedPacket)
        (pairChannelStateSpace 1) ≈ 1 ∧
      twoFaceSharedLinkConditionalMass w hw 1
          vacuumBoundedFaceSpinPacket oneFaceFundamentalBoundedPacket ≈ 0 ∧
      ¬ (twoFaceSharedLinkConditionalMass w hw 1
          vacuumBoundedFaceSpinPacket oneFaceFundamentalBoundedPacket ≈ 1) := by
  exact ⟨packetPairChannelConditionalKernel_row_normalized
      w hw 1 vacuumBoundedFaceSpinPacket,
    packetPairChannelConditionalKernel_row_normalized
      w hw 1 oneFaceFundamentalBoundedPacket,
    vacuum_fundamental_sharedLinkMass_eqv_zero w hw,
    vacuum_fundamental_sharedLinkMass_not_normalized w hw⟩

/-! ## Dependency gates -/

#print axioms twoFaceProductionLinkFactor_eq_fusionInd
#print axioms twoFaceSharedLinkConditionalWeight_eq_fusion_guard
#print axioms twoFaceSharedLinkConditionalWeight_reflection_equivariant
#print axioms vacuum_raw_zero_of_coarse_ne_zero
#print axioms oneFundamental_raw_zero_of_coarse_ne_one
#print axioms vacuum_fundamental_sharedLinkWeight_eqv_zero
#print axioms vacuum_fundamental_sharedLinkMass_eqv_zero
#print axioms independent_rows_normalized_but_shared_link_not

end YMGap.Continuum.Z4DyadicSlabTwoFaceSharedLinkKernel
