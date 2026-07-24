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
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4AdjacentCubeSharedFaceRecouplingKernel
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4DyadicSlabCharacterFusionConditionalKernel
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

/-! ## 4. Reflection of the complete adjacent target -/

def reflectAdjacentCubeJointTarget
    (leftPlanes rightPlanes : CubeReflectionPlanes)
    (target : AdjacentCubeJointTarget) : AdjacentCubeJointTarget :=
  ((reflectCubeTarget leftPlanes target.1.1,
      reflectCubeTarget rightPlanes target.1.2),
    target.2)

theorem reflectAdjacentCubeJointTarget_involutive
    (leftPlanes rightPlanes : CubeReflectionPlanes)
    (target : AdjacentCubeJointTarget) :
    reflectAdjacentCubeJointTarget leftPlanes rightPlanes
        (reflectAdjacentCubeJointTarget
          leftPlanes rightPlanes target) = target := by
  rcases target with ⟨⟨left, right⟩, fused⟩
  simp only [reflectAdjacentCubeJointTarget]
  rw [reflectCubeTarget_involutive,
    reflectCubeTarget_involutive]

theorem reflectAdjacentCubeJointTarget_mem
    {cutoff : Nat}
    (leftPlanes rightPlanes : CubeReflectionPlanes)
    {target : AdjacentCubeJointTarget}
    (htarget : target ∈ adjacentCubeJointStateSpace cutoff) :
    reflectAdjacentCubeJointTarget leftPlanes rightPlanes target ∈
      adjacentCubeJointStateSpace cutoff := by
  unfold adjacentCubeJointStateSpace at htarget ⊢
  have hparts := (mem_cartesian_iff _ _ target).mp htarget
  have hcubes := (mem_cartesian_iff _ _ target.1).mp hparts.1
  apply (mem_cartesian_iff _ _ _).mpr
  exact ⟨(mem_cartesian_iff _ _ _).mpr
      ⟨reflectCubeTarget_mem hcubes.1 leftPlanes,
        reflectCubeTarget_mem hcubes.2 rightPlanes⟩,
    hparts.2⟩

private theorem nodup_map_of_injective_local {A B : Type}
    (f : A → B) (hf : Function.Injective f) :
    ∀ {xs : List A}, xs.Nodup → (xs.map f).Nodup
  | [], _ => List.nodup_nil
  | head :: tail, hnodup => by
      have hparts := List.nodup_cons.mp hnodup
      apply List.nodup_cons.mpr
      constructor
      · intro hmem
        obtain ⟨source, hsource, heq⟩ := List.mem_map.mp hmem
        exact hparts.1 ((hf heq) ▸ hsource)
      · exact nodup_map_of_injective_local f hf hparts.2

private theorem reflectAdjacentCubeJointTarget_injective
    (leftPlanes rightPlanes : CubeReflectionPlanes) :
    Function.Injective
      (reflectAdjacentCubeJointTarget leftPlanes rightPlanes) := by
  intro left right heq
  exact (reflectAdjacentCubeJointTarget_involutive
      leftPlanes rightPlanes left).symm.trans
    ((congrArg
      (reflectAdjacentCubeJointTarget leftPlanes rightPlanes)
      heq).trans
      (reflectAdjacentCubeJointTarget_involutive
        leftPlanes rightPlanes right))

private def cubePairChannelStateDecidableEqLocal :
    DecidableEq CubePairChannelState :=
  @instDecidableEqProd PairChannelState
    (PairChannelState ×
      (PairChannelState ×
        (PairChannelState ×
          (PairChannelState × PairChannelState))))
    (inferInstance)
    (@instDecidableEqProd PairChannelState
      (PairChannelState ×
        (PairChannelState ×
          (PairChannelState × PairChannelState)))
      (inferInstance)
      (@instDecidableEqProd PairChannelState
        (PairChannelState × (PairChannelState × PairChannelState))
        (inferInstance)
        (@instDecidableEqProd PairChannelState
          (PairChannelState × PairChannelState)
          (inferInstance)
          (@instDecidableEqProd PairChannelState PairChannelState
            (inferInstance) (inferInstance)))))

theorem reflectAdjacentCubeJointStateSpace_perm
    (cutoff : Nat)
    (leftPlanes rightPlanes : CubeReflectionPlanes) :
    ((adjacentCubeJointStateSpace cutoff).map
      (reflectAdjacentCubeJointTarget
        leftPlanes rightPlanes)).Perm
      (adjacentCubeJointStateSpace cutoff) := by
  letI : DecidableEq CubePairChannelState :=
    cubePairChannelStateDecidableEqLocal
  letI : DecidableEq AdjacentCubeJointTarget := inferInstance
  apply perm_of_nodup_mem_iff
  · exact nodup_map_of_injective_local _
      (reflectAdjacentCubeJointTarget_injective
        leftPlanes rightPlanes)
      (adjacentCubeJointStateSpace_nodup cutoff)
  · exact adjacentCubeJointStateSpace_nodup cutoff
  · intro target
    constructor
    · intro htarget
      obtain ⟨source, hsource, heq⟩ := List.mem_map.mp htarget
      rw [← heq]
      exact reflectAdjacentCubeJointTarget_mem
        leftPlanes rightPlanes hsource
    · intro htarget
      apply List.mem_map.mpr
      refine ⟨reflectAdjacentCubeJointTarget
          leftPlanes rightPlanes target,
        reflectAdjacentCubeJointTarget_mem
          leftPlanes rightPlanes htarget, ?_⟩
      exact reflectAdjacentCubeJointTarget_involutive
        leftPlanes rightPlanes target

private theorem cubeProductionIncidenceFactor_reflection_local
    (cutoff : Nat) (planes : CubeReflectionPlanes)
    (target : CubePairChannelState)
    (incidence : CubeProductionIncidence) :
    cubeProductionIncidenceFactor cutoff
        (reflectCubeTarget planes target) incidence =
      cubeProductionIncidenceFactor cutoff target incidence := by
  unfold cubeProductionIncidenceFactor
  rw [cubeTargetAt_reflectCubeTarget,
    cubeTargetAt_reflectCubeTarget]
  unfold twoFaceProductionLinkFactor twoFaceCoarseExternal
  cases hleft : planes incidence.left <;>
    cases hright : planes incidence.right <;> rfl

theorem cubeOuterProductionLinkProduct_reflection
    (cutoff : Nat) (planes : CubeReflectionPlanes)
    (target : CubePairChannelState)
    (incidences : List CubeProductionIncidence) :
    cubeOuterProductionLinkProduct cutoff
        (reflectCubeTarget planes target) incidences =
      cubeOuterProductionLinkProduct cutoff target incidences := by
  unfold cubeOuterProductionLinkProduct
  apply congrArg id
  induction incidences with
  | nil => rfl
  | cons incidence rest ih =>
      simp only [adjacentQProduct]
      rw [cubeProductionIncidenceFactor_reflection_local, ih]

theorem cubeTargetSpin_reflection
    (planes : CubeReflectionPlanes)
    (target : CubePairChannelState) (face : CubeFaceIndex) :
    cubeTargetSpin (reflectCubeTarget planes target) face =
      cubeTargetSpin target face := by
  unfold cubeTargetSpin
  rw [cubeTargetAt_reflectCubeTarget]
  cases hplane : planes face <;> rfl

theorem adjacentCubeSharedFaceTargetRawWeight_reflection
    (leftPlanes rightPlanes : CubeReflectionPlanes)
    (left right : CubePairChannelState) (fused : Nat) :
    adjacentCubeSharedFaceTargetRawWeight
        (reflectCubeTarget leftPlanes left)
        (reflectCubeTarget rightPlanes right) fused =
      adjacentCubeSharedFaceTargetRawWeight left right fused := by
  unfold adjacentCubeSharedFaceTargetRawWeight
  rw [cubeTargetSpin_reflection, cubeTargetSpin_reflection,
    cubeTargetSpin_reflection, cubeTargetSpin_reflection,
    cubeTargetSpin_reflection, cubeTargetSpin_reflection,
    cubeTargetSpin_reflection, cubeTargetSpin_reflection,
    cubeTargetSpin_reflection, cubeTargetSpin_reflection]

theorem adjacentCubeJointRawWeight_reflection
    (w : Q') (cutoff : Nat)
    (leftPlanes rightPlanes : CubeReflectionPlanes)
    (source : AdjacentCubeStretchedSource cutoff)
    (target : AdjacentCubeJointTarget) :
    adjacentCubeJointRawWeight w cutoff
        (reflectAdjacentCubeStretchedSource
          leftPlanes rightPlanes source)
        (reflectAdjacentCubeJointTarget
          leftPlanes rightPlanes target) ≈
      adjacentCubeJointRawWeight w cutoff source target := by
  unfold adjacentCubeJointRawWeight
    reflectAdjacentCubeStretchedSource
    reflectAdjacentCubeJointTarget
  exact qmul_congr
    (qmul_congr
      (cubeFaceRawProduct_reflection
        w cutoff leftPlanes source.left target.1.1)
      (cubeFaceRawProduct_reflection
        w cutoff rightPlanes source.right target.1.2))
    (qmul_congr
      (qmul_congr
        (Q'.eqv_of_eq
          (cubeOuterProductionLinkProduct_reflection
            cutoff leftPlanes target.1.1
            leftCubeOuterIncidences))
        (Q'.eqv_of_eq
          (cubeOuterProductionLinkProduct_reflection
            cutoff rightPlanes target.1.2
            rightCubeOuterIncidences)))
      (Q'.eqv_of_eq
        (adjacentCubeSharedFaceTargetRawWeight_reflection
          leftPlanes rightPlanes
          target.1.1 target.1.2 target.2)))

theorem adjacentCubeJointPartition_reflection
    (w : Q') (cutoff : Nat)
    (leftPlanes rightPlanes : CubeReflectionPlanes)
    (source : AdjacentCubeStretchedSource cutoff) :
    adjacentCubeJointPartition w cutoff
        (reflectAdjacentCubeStretchedSource
          leftPlanes rightPlanes source) ≈
      adjacentCubeJointPartition w cutoff source := by
  let reflectedSource :=
    reflectAdjacentCubeStretchedSource
      leftPlanes rightPlanes source
  let reflectTarget :=
    reflectAdjacentCubeJointTarget leftPlanes rightPlanes
  let targets := adjacentCubeJointStateSpace cutoff
  refine Q'.eqv_trans _
    (listQSum
      (adjacentCubeJointRawWeight w cutoff reflectedSource)
      (targets.map reflectTarget)) _ ?_ ?_
  · exact YMGap.Continuum.Z4CanonicalPolymerRange.listQSum_perm _
      (reflectAdjacentCubeJointStateSpace_perm
        cutoff leftPlanes rightPlanes).symm
  · rw [listQSum_map]
    apply listQSum_congr_on
    intro target _
    exact adjacentCubeJointRawWeight_reflection
      w cutoff leftPlanes rightPlanes source target

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

theorem adjacentCubeJointConditionalKernel_reflection
    (w : Q') (hw : (0 : Q') < w) (cutoff : Nat)
    (leftPlanes rightPlanes : CubeReflectionPlanes)
    (source : AdjacentCubeStretchedSource cutoff)
    (target : AdjacentCubeJointTarget) :
    adjacentCubeJointConditionalKernel w hw cutoff
        (reflectAdjacentCubeStretchedSource
          leftPlanes rightPlanes source)
        (reflectAdjacentCubeJointTarget
          leftPlanes rightPlanes target) ≈
      adjacentCubeJointConditionalKernel
        w hw cutoff source target := by
  unfold adjacentCubeJointConditionalKernel
  exact divPos_eqv_congr_local
    (adjacentCubeJointPartition_pos hw cutoff
      (reflectAdjacentCubeStretchedSource
        leftPlanes rightPlanes source))
    (adjacentCubeJointPartition_pos hw cutoff source)
    (adjacentCubeJointRawWeight_reflection
      w cutoff leftPlanes rightPlanes source target)
    (adjacentCubeJointPartition_reflection
      w cutoff leftPlanes rightPlanes source)

#print axioms leftCubeOuterIncidences_length
#print axioms rightCubeOuterIncidences_length
#print axioms adjacentCubeJointStateSpace_nodup
#print axioms compatibleAdjacentCubeJointTarget_mem
#print axioms adjacentCubeJointRawWeight_nonnegative
#print axioms compatibleAdjacentCubeJointRawWeight_pos
#print axioms adjacentCubeJointPartition_pos
#print axioms adjacentCubeJointConditionalKernel_nonnegative
#print axioms adjacentCubeJointConditionalKernel_row_normalized
#print axioms reflectAdjacentCubeJointStateSpace_perm
#print axioms adjacentCubeJointRawWeight_reflection
#print axioms adjacentCubeJointPartition_reflection
#print axioms adjacentCubeJointConditionalKernel_reflection

end YMGap.Continuum.Z4AdjacentCubeJointConditionalKernel
