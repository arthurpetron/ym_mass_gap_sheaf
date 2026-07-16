/-
# A closed six-face corrected-slab conditional component

The adjacent two-face component has a derived normalized law, but its outer
edges are unpaired.  The local closure theorem forces the complete six-face
boundary of the elementary cube.  Here we normalize that closed component in
the physically required order:

* enumerate the six face-channel targets without duplicates;
* multiply the six exact character/fusion face weights;
* multiply the literal degree-two production multiplicity at each of the
  twelve distinct cube links;
* sum this complete raw component and divide only once.

The source carrier records one common stretched coarse channel for all six
faces.  Its compatible stretched target has positive face weights, while all
twelve vacuum fusion guards equal one.  Thus the denominator is derived and
strictly positive.  Corrected-slab reflection may use a different plane on
each face; it permutes the target carrier and intertwines the normalized row.
-/

import YMGap.Continuum.Z4DyadicSlabTwoFaceClosureObstruction

namespace YMGap.Continuum.Z4DyadicSlabCubeCoupledConditionalKernel

set_option maxRecDepth 16000
set_option maxHeartbeats 7000000

open YMGap.Constructive
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4CanonicalPolymerRange
open YMGap.Continuum.Z4CoarseUnitCubeBlockGeometry
open YMGap.Continuum.Z4DyadicSlabCharacterFusionConditionalKernel
open YMGap.Continuum.Z4DyadicSlabMultiCharacterPacketKernel
open YMGap.Continuum.Z4DyadicSlabReflectionParityKernel
open YMGap.Continuum.Z4DyadicSlabTwoFaceCoupledConditionalKernel
open YMGap.Continuum.Z4DyadicSlabTwoFaceSharedLinkKernel
open YMGap.Continuum.Z4DyadicUnitCubeBlockGeometry
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

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
          have hle := Q'.add_le_add_right
            (0 : Q') (value head) (listQSum value tail) (hvalue head)
          rwa [Q'.zero_add'] at hle
        exact Q'.le_trans' _ _ _ ih hmono

/-! ## 1. The sixfold target carrier -/

/-- Target order: bottom, top, front, back, left, right. -/
abbrev CubePairChannelState :=
  PairChannelState ×
    (PairChannelState ×
      (PairChannelState ×
        (PairChannelState ×
          (PairChannelState × PairChannelState))))

def cubeTargetAt
    (target : CubePairChannelState) : CubeFaceIndex → PairChannelState
  | .bottomXY => target.1
  | .topXY => target.2.1
  | .frontXZ => target.2.2.1
  | .backXZ => target.2.2.2.1
  | .leftYZ => target.2.2.2.2.1
  | .rightYZ => target.2.2.2.2.2

def cubeTargetOf
    (state : CubeFaceIndex → PairChannelState) : CubePairChannelState :=
  (state .bottomXY,
    (state .topXY,
      (state .frontXZ,
        (state .backXZ, (state .leftYZ, state .rightYZ)))))

theorem cubeTargetAt_cubeTargetOf
    (state : CubeFaceIndex → PairChannelState) (face : CubeFaceIndex) :
    cubeTargetAt (cubeTargetOf state) face = state face := by
  cases face <;> rfl

theorem cubeTargetOf_cubeTargetAt (target : CubePairChannelState) :
    cubeTargetOf (cubeTargetAt target) = target := by
  rcases target with
    ⟨bottom, ⟨top, ⟨front, ⟨back, ⟨left, right⟩⟩⟩⟩⟩
  rfl

def cubePairChannelStateSpace (cutoff : Nat) :
    List CubePairChannelState :=
  let states := pairChannelStateSpace cutoff
  cartesian states
    (cartesian states
      (cartesian states
        (cartesian states (cartesian states states))))

theorem cubePairChannelStateSpace_nodup (cutoff : Nat) :
    (cubePairChannelStateSpace cutoff).Nodup := by
  let states := pairChannelStateSpace cutoff
  have hstates : states.Nodup := pairChannelStateSpace_nodup cutoff
  exact cartesian_nodup _ _ hstates
    (cartesian_nodup _ _ hstates
      (cartesian_nodup _ _ hstates
        (cartesian_nodup _ _ hstates
          (cartesian_nodup _ _ hstates hstates))))

theorem mem_cubePairChannelStateSpace_iff
    (cutoff : Nat) (target : CubePairChannelState) :
    target ∈ cubePairChannelStateSpace cutoff ↔
      ∀ face, cubeTargetAt target face ∈
        pairChannelStateSpace cutoff := by
  rcases target with
    ⟨bottom, ⟨top, ⟨front, ⟨back, ⟨left, right⟩⟩⟩⟩⟩
  simp only [cubePairChannelStateSpace, mem_cartesian_iff]
  constructor
  · intro h face
    cases face
    · exact h.1
    · exact h.2.1
    · exact h.2.2.1
    · exact h.2.2.2.1
    · exact h.2.2.2.2.1
    · exact h.2.2.2.2.2
  · intro h
    exact ⟨h .bottomXY, h .topXY, h .frontXZ,
      h .backXZ, h .leftYZ, h .rightYZ⟩

/-! ## 2. The twelve literal production links -/

structure CubeProductionIncidence where
  link : YMGap.Continuum.ClusterCount4DProgress.Z4Link
  left : CubeFaceIndex
  right : CubeFaceIndex
  deriving DecidableEq

/-- The twelve distinct boundary links, in the same order as
`coarseCubeBoundaryLinks`, together with their two incident faces. -/
def cubeProductionIncidences : List CubeProductionIncidence :=
  [⟨((0, 0, 0, 0), .x0), .bottomXY, .frontXZ⟩,
   ⟨((0, 1, 0, 0), .x0), .bottomXY, .backXZ⟩,
   ⟨((0, 0, 1, 0), .x0), .topXY, .frontXZ⟩,
   ⟨((0, 1, 1, 0), .x0), .topXY, .backXZ⟩,
   ⟨((0, 0, 0, 0), .x1), .bottomXY, .leftYZ⟩,
   ⟨((1, 0, 0, 0), .x1), .bottomXY, .rightYZ⟩,
   ⟨((0, 0, 1, 0), .x1), .topXY, .leftYZ⟩,
   ⟨((1, 0, 1, 0), .x1), .topXY, .rightYZ⟩,
   ⟨((0, 0, 0, 0), .x2), .frontXZ, .leftYZ⟩,
   ⟨((1, 0, 0, 0), .x2), .frontXZ, .rightYZ⟩,
   ⟨((0, 1, 0, 0), .x2), .backXZ, .leftYZ⟩,
   ⟨((1, 1, 0, 0), .x2), .backXZ, .rightYZ⟩]

theorem cubeProductionIncidences_length :
    cubeProductionIncidences.length = 12 := by
  rfl

theorem cubeProductionIncidences_nodup :
    cubeProductionIncidences.Nodup := by
  simp [cubeProductionIncidences]

theorem cubeProductionIncidences_map_link :
    cubeProductionIncidences.map CubeProductionIncidence.link =
      coarseCubeBoundaryLinks := by
  rfl

/-- Every recorded production entry is incident on exactly the two faces
whose coarse spins feed its degree-two Haar resolver. -/
theorem cubeProductionIncidence_on_recorded_faces
    {incidence : CubeProductionIncidence}
    (hincidence : incidence ∈ cubeProductionIncidences) :
    incidence.link ∈ edgesOf (cubeFace incidence.left) ∧
      incidence.link ∈ edgesOf (cubeFace incidence.right) := by
  simp only [cubeProductionIncidences, List.mem_cons,
    List.not_mem_nil, or_false] at hincidence
  rcases hincidence with rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [cubeFace, edgesOf, dirsOf, addE]

/-! ## 3. Common-stretched sources and a positive raw witness -/

structure CubeStretchedCompatibleSource (cutoff : Nat) where
  packet : CubeFaceIndex → BoundedFaceSpinPacket cutoff
  commonTotal : Nat
  total_eq : ∀ face,
    faceSpinTotal (packet face).val = commonTotal

def compatibleCubeTarget {cutoff : Nat}
    (source : CubeStretchedCompatibleSource cutoff) :
    CubePairChannelState :=
  cubeTargetOf (fun face =>
    stretchedPairChannelState (source.packet face).val)

theorem compatibleCubeTarget_at {cutoff : Nat}
    (source : CubeStretchedCompatibleSource cutoff)
    (face : CubeFaceIndex) :
    cubeTargetAt (compatibleCubeTarget source) face =
      stretchedPairChannelState (source.packet face).val := by
  exact cubeTargetAt_cubeTargetOf _ face

theorem compatibleCubeTarget_mem {cutoff : Nat}
    (source : CubeStretchedCompatibleSource cutoff) :
    compatibleCubeTarget source ∈ cubePairChannelStateSpace cutoff := by
  apply (mem_cubePairChannelStateSpace_iff cutoff _).mpr
  intro face
  rw [compatibleCubeTarget_at]
  exact stretchedPairChannel_mem cutoff (source.packet face).val
    (source.packet face).property

private def cubeQProduct {A : Type}
    (value : A → Q') : List A → Q'
  | [] => 1
  | head :: tail => value head * cubeQProduct value tail

private theorem cubeQProduct_nonnegative {A : Type}
    (value : A → Q') (hvalue : ∀ x, (0 : Q') ≤ value x) :
    ∀ xs, (0 : Q') ≤ cubeQProduct value xs
  | [] => by
      change (0 : Q') ≤ 1
      exact Q'.le_of_lt (by decide)
  | head :: tail =>
      Q'.mul_nonneg _ _ (hvalue head)
        (cubeQProduct_nonnegative value hvalue tail)

private theorem cubeQProduct_pos {A : Type}
    (value : A → Q') (hvalue : ∀ x, (0 : Q') < value x) :
    ∀ xs, (0 : Q') < cubeQProduct value xs
  | [] => by
      change (0 : Q') < 1
      decide
  | head :: tail =>
      Q'.mul_pos (hvalue head)
        (cubeQProduct_pos value hvalue tail)

private theorem cubeQProduct_congr_eqv {A : Type}
    (left right : A → Q') (hagrees : ∀ x, left x ≈ right x) :
    ∀ xs, cubeQProduct left xs ≈ cubeQProduct right xs
  | [] => Q'.eqv_refl 1
  | head :: tail =>
      qmul_congr (hagrees head)
        (cubeQProduct_congr_eqv left right hagrees tail)

private theorem cubeQProduct_one {A : Type} :
    ∀ xs : List A, cubeQProduct (fun _ => (1 : Q')) xs ≈ 1
  | [] => Q'.eqv_refl 1
  | _ :: tail =>
      Q'.eqv_trans _ (1 * 1) _
        (Q'.mul_eqv_congr_left 1 _ _ (cubeQProduct_one tail))
        (Q'.one_mul_eqv 1)

def cubeFaceRawProduct
    (w : Q') (cutoff : Nat)
    (source : CubeStretchedCompatibleSource cutoff)
    (target : CubePairChannelState) : Q' :=
  cubeQProduct (fun face =>
    packetPairChannelRawWeight w (source.packet face).val
      (cubeTargetAt target face)) cubeFaceIndices

def cubeProductionIncidenceFactor
    (cutoff : Nat) (target : CubePairChannelState)
    (incidence : CubeProductionIncidence) : Q' :=
  twoFaceProductionLinkFactor cutoff
    (cubeTargetAt target incidence.left)
    (cubeTargetAt target incidence.right)

def cubeProductionLinkProduct
    (cutoff : Nat) (target : CubePairChannelState) : Q' :=
  cubeQProduct (cubeProductionIncidenceFactor cutoff target)
    cubeProductionIncidences

theorem cubeFaceRawProduct_nonnegative
    {w : Q'} (hw : (0 : Q') ≤ w) (cutoff : Nat)
    (source : CubeStretchedCompatibleSource cutoff)
    (target : CubePairChannelState) :
    (0 : Q') ≤ cubeFaceRawProduct w cutoff source target := by
  unfold cubeFaceRawProduct
  apply cubeQProduct_nonnegative
  intro face
  exact packetPairChannelRawWeight_nonnegative hw
    (source.packet face).val (cubeTargetAt target face)

theorem cubeProductionLinkProduct_nonnegative
    (cutoff : Nat) (target : CubePairChannelState) :
    (0 : Q') ≤ cubeProductionLinkProduct cutoff target := by
  unfold cubeProductionLinkProduct cubeProductionIncidenceFactor
  apply cubeQProduct_nonnegative
  intro incidence
  unfold twoFaceProductionLinkFactor
  exact ofNat_nonnegative_local _

theorem compatibleCubeFaceRawProduct_pos
    {w : Q'} (hw : (0 : Q') < w) (cutoff : Nat)
    (source : CubeStretchedCompatibleSource cutoff) :
    (0 : Q') < cubeFaceRawProduct w cutoff source
      (compatibleCubeTarget source) := by
  unfold cubeFaceRawProduct
  apply cubeQProduct_pos
  intro face
  rw [compatibleCubeTarget_at]
  exact stretchedPairChannelRawWeight_pos hw
    (source.packet face).val

theorem compatibleCube_incidenceFactor_eqv_one
    {cutoff : Nat} (source : CubeStretchedCompatibleSource cutoff)
    (incidence : CubeProductionIncidence) :
    cubeProductionIncidenceFactor cutoff
        (compatibleCubeTarget source) incidence ≈ 1 := by
  refine Q'.eqv_trans _
    (YMGap.Continuum.BondMovingStep.fusionInd
      (faceSpinTotal (source.packet incidence.left).val)
      (faceSpinTotal (source.packet incidence.right).val) 0) _ ?_ ?_
  · unfold cubeProductionIncidenceFactor
    rw [compatibleCubeTarget_at, compatibleCubeTarget_at]
    exact twoFaceProductionLinkFactor_eq_fusionInd cutoff _ _
  · rw [source.total_eq incidence.left,
      source.total_eq incidence.right]
    exact Q'.eqv_of_eq
      (YMGap.Continuum.FusionQuotientCollapse.fusionInd_zero_diag_self
        source.commonTotal)

theorem compatibleCubeProductionLinkProduct_eqv_one
    {cutoff : Nat} (source : CubeStretchedCompatibleSource cutoff) :
    cubeProductionLinkProduct cutoff (compatibleCubeTarget source) ≈ 1 := by
  unfold cubeProductionLinkProduct
  exact Q'.eqv_trans _
    (cubeQProduct (fun _ : CubeProductionIncidence => (1 : Q'))
      cubeProductionIncidences) _
    (cubeQProduct_congr_eqv _ _
      (compatibleCube_incidenceFactor_eqv_one source)
      cubeProductionIncidences)
    (cubeQProduct_one cubeProductionIncidences)

def cubeCoupledRawWeight
    (w : Q') (cutoff : Nat)
    (source : CubeStretchedCompatibleSource cutoff)
    (target : CubePairChannelState) : Q' :=
  cubeFaceRawProduct w cutoff source target *
    cubeProductionLinkProduct cutoff target

theorem cubeCoupledRawWeight_nonnegative
    {w : Q'} (hw : (0 : Q') ≤ w) (cutoff : Nat)
    (source : CubeStretchedCompatibleSource cutoff)
    (target : CubePairChannelState) :
    (0 : Q') ≤ cubeCoupledRawWeight w cutoff source target := by
  unfold cubeCoupledRawWeight
  exact Q'.mul_nonneg _ _
    (cubeFaceRawProduct_nonnegative hw cutoff source target)
    (cubeProductionLinkProduct_nonnegative cutoff target)

theorem compatibleCubeRawWeight_pos
    {w : Q'} (hw : (0 : Q') < w) (cutoff : Nat)
    (source : CubeStretchedCompatibleSource cutoff) :
    (0 : Q') < cubeCoupledRawWeight w cutoff source
      (compatibleCubeTarget source) := by
  have hfaces := compatibleCubeFaceRawProduct_pos hw cutoff source
  have hfacesOne : (0 : Q') <
      cubeFaceRawProduct w cutoff source (compatibleCubeTarget source) * 1 :=
    Q'.mul_pos hfaces (by decide)
  apply pos_of_eqv_local hfacesOne
  exact Q'.eqv_symm
    (Q'.mul_eqv_congr_left _ _ _
      (compatibleCubeProductionLinkProduct_eqv_one source))

/-! ## 4. Normalize once after all twelve production gluings -/

def cubeCoupledPartition
    (w : Q') (cutoff : Nat)
    (source : CubeStretchedCompatibleSource cutoff) : Q' :=
  listQSum (cubeCoupledRawWeight w cutoff source)
    (cubePairChannelStateSpace cutoff)

theorem cubeCoupledPartition_pos
    {w : Q'} (hw : (0 : Q') < w) (cutoff : Nat)
    (source : CubeStretchedCompatibleSource cutoff) :
    (0 : Q') < cubeCoupledPartition w cutoff source := by
  have hterm := compatibleCubeRawWeight_pos hw cutoff source
  have hle : cubeCoupledRawWeight w cutoff source
        (compatibleCubeTarget source) ≤
      cubeCoupledPartition w cutoff source := by
    unfold cubeCoupledPartition
    exact listQSum_member_le_local
      (cubeCoupledRawWeight w cutoff source)
      (cubeCoupledRawWeight_nonnegative (Q'.le_of_lt hw) cutoff source)
      _ (compatibleCubeTarget_mem source)
  exact Q'.pos_of_lt_of_le hterm hle

def cubeCoupledConditionalKernel
    (w : Q') (hw : (0 : Q') < w) (cutoff : Nat)
    (source : CubeStretchedCompatibleSource cutoff)
    (target : CubePairChannelState) : Q' :=
  Q'.divPos
    (cubeCoupledRawWeight w cutoff source target)
    (cubeCoupledPartition w cutoff source)
    (cubeCoupledPartition_pos hw cutoff source)

theorem cubeCoupledConditionalKernel_nonnegative
    (w : Q') (hw : (0 : Q') < w) (cutoff : Nat)
    (source : CubeStretchedCompatibleSource cutoff)
    (target : CubePairChannelState) :
    (0 : Q') ≤ cubeCoupledConditionalKernel
      w hw cutoff source target := by
  unfold cubeCoupledConditionalKernel Q'.divPos
  exact Q'.mul_nonneg _ _
    (cubeCoupledRawWeight_nonnegative
      (Q'.le_of_lt hw) cutoff source target)
    (Q'.le_of_lt (Q'.recipPos_pos _ _))

theorem cubeCoupledConditionalKernel_row_normalized
    (w : Q') (hw : (0 : Q') < w) (cutoff : Nat)
    (source : CubeStretchedCompatibleSource cutoff) :
    listQSum
        (cubeCoupledConditionalKernel w hw cutoff source)
        (cubePairChannelStateSpace cutoff) ≈ 1 := by
  unfold cubeCoupledConditionalKernel Q'.divPos
  exact Q'.eqv_trans _
    (cubeCoupledPartition w cutoff source *
      Q'.recipPos (cubeCoupledPartition w cutoff source)
        (cubeCoupledPartition_pos hw cutoff source)) _
    (listQSum_mul_right
      (cubeCoupledRawWeight w cutoff source)
      (Q'.recipPos (cubeCoupledPartition w cutoff source)
        (cubeCoupledPartition_pos hw cutoff source))
      (cubePairChannelStateSpace cutoff))
    (Q'.mul_recipPos_eqv _
      (cubeCoupledPartition_pos hw cutoff source))

/-! ## 5. Corrected-slab reflection of the complete component -/

abbrev CubeReflectionPlanes :=
  CubeFaceIndex → YMGap.Continuum.ClusterCount4DProgress.Z4Plane

def reflectCubeCompatibleSource
    (cutoff : Nat) (planes : CubeReflectionPlanes)
    (source : CubeStretchedCompatibleSource cutoff) :
    CubeStretchedCompatibleSource cutoff where
  packet := fun face =>
    reflectBoundedFaceSpinPacket cutoff (planes face)
      (source.packet face)
  commonTotal := source.commonTotal
  total_eq := by
    intro face
    change faceSpinTotal
      (reflectFaceSpinPacket (planes face) (source.packet face).val) =
        source.commonTotal
    rw [faceSpinTotal_reflection]
    exact source.total_eq face

def reflectCubeTarget
    (planes : CubeReflectionPlanes)
    (target : CubePairChannelState) : CubePairChannelState :=
  cubeTargetOf (fun face =>
    reflectPairChannelState (planes face) (cubeTargetAt target face))

theorem cubeTargetAt_reflectCubeTarget
    (planes : CubeReflectionPlanes)
    (target : CubePairChannelState) (face : CubeFaceIndex) :
    cubeTargetAt (reflectCubeTarget planes target) face =
      reflectPairChannelState (planes face) (cubeTargetAt target face) := by
  exact cubeTargetAt_cubeTargetOf _ face

theorem reflectCubeTarget_involutive
    (planes : CubeReflectionPlanes)
    (target : CubePairChannelState) :
    reflectCubeTarget planes (reflectCubeTarget planes target) =
      target := by
  rw [← cubeTargetOf_cubeTargetAt target]
  apply congrArg cubeTargetOf
  funext face
  rw [cubeTargetAt_reflectCubeTarget,
    reflectPairChannelState_involutive,
    cubeTargetAt_cubeTargetOf]

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

theorem reflectCubeTarget_mem
    {cutoff : Nat} {target : CubePairChannelState}
    (htarget : target ∈ cubePairChannelStateSpace cutoff)
    (planes : CubeReflectionPlanes) :
    reflectCubeTarget planes target ∈
      cubePairChannelStateSpace cutoff := by
  have hparts :=
    (mem_cubePairChannelStateSpace_iff cutoff target).mp htarget
  apply (mem_cubePairChannelStateSpace_iff cutoff _).mpr
  intro face
  rw [cubeTargetAt_reflectCubeTarget]
  exact reflectPairChannelState_mem_clean (hparts face) (planes face)

private theorem reflectCubeTarget_injective
    (planes : CubeReflectionPlanes) :
    Function.Injective (reflectCubeTarget planes) := by
  intro left right heq
  exact (reflectCubeTarget_involutive planes left).symm.trans
    ((congrArg (reflectCubeTarget planes) heq).trans
      (reflectCubeTarget_involutive planes right))

private def cubePairChannelStateDecidableEq :
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

theorem reflectCubePairChannelStateSpace_perm
    (cutoff : Nat) (planes : CubeReflectionPlanes) :
    ((cubePairChannelStateSpace cutoff).map
      (reflectCubeTarget planes)).Perm
        (cubePairChannelStateSpace cutoff) := by
  letI : DecidableEq CubePairChannelState :=
    cubePairChannelStateDecidableEq
  apply YMGap.Continuum.Z4CanonicalPolymerUniverse.perm_of_nodup_mem_iff
  · exact nodup_map_of_injective_local
      (reflectCubeTarget planes)
      (fun {_ _} heq => reflectCubeTarget_injective planes heq)
      (cubePairChannelStateSpace_nodup cutoff)
  · exact cubePairChannelStateSpace_nodup cutoff
  · intro target
    constructor
    · intro htarget
      obtain ⟨source, hsource, hsourceEq⟩ := List.mem_map.mp htarget
      rw [← hsourceEq]
      exact reflectCubeTarget_mem hsource planes
    · intro htarget
      apply List.mem_map.mpr
      refine ⟨reflectCubeTarget planes target,
        reflectCubeTarget_mem htarget planes, ?_⟩
      exact reflectCubeTarget_involutive planes target

theorem cubeFaceRawProduct_reflection
    (w : Q') (cutoff : Nat) (planes : CubeReflectionPlanes)
    (source : CubeStretchedCompatibleSource cutoff)
    (target : CubePairChannelState) :
    cubeFaceRawProduct w cutoff
        (reflectCubeCompatibleSource cutoff planes source)
        (reflectCubeTarget planes target) ≈
      cubeFaceRawProduct w cutoff source target := by
  unfold cubeFaceRawProduct
  apply cubeQProduct_congr_eqv
  intro face
  rw [cubeTargetAt_reflectCubeTarget]
  exact packetPairChannelRawWeight_reflection
    w (planes face) (source.packet face).val
      (cubeTargetAt target face)

private theorem twoFaceProductionLinkFactor_arbitrary_reflection
    (cutoff : Nat)
    (leftPlane rightPlane :
      YMGap.Continuum.ClusterCount4DProgress.Z4Plane)
    (left right : PairChannelState) :
    twoFaceProductionLinkFactor cutoff
        (reflectPairChannelState leftPlane left)
        (reflectPairChannelState rightPlane right) =
      twoFaceProductionLinkFactor cutoff left right := by
  cases leftPlane <;> cases rightPlane <;> rfl

theorem cubeProductionLinkProduct_reflection
    (cutoff : Nat) (planes : CubeReflectionPlanes)
    (target : CubePairChannelState) :
    cubeProductionLinkProduct cutoff
        (reflectCubeTarget planes target) ≈
      cubeProductionLinkProduct cutoff target := by
  unfold cubeProductionLinkProduct
  apply cubeQProduct_congr_eqv
  intro incidence
  unfold cubeProductionIncidenceFactor
  rw [cubeTargetAt_reflectCubeTarget,
    cubeTargetAt_reflectCubeTarget]
  exact Q'.eqv_of_eq
    (twoFaceProductionLinkFactor_arbitrary_reflection
      cutoff (planes incidence.left) (planes incidence.right)
      (cubeTargetAt target incidence.left)
      (cubeTargetAt target incidence.right))

theorem cubeCoupledRawWeight_reflection
    (w : Q') (cutoff : Nat) (planes : CubeReflectionPlanes)
    (source : CubeStretchedCompatibleSource cutoff)
    (target : CubePairChannelState) :
    cubeCoupledRawWeight w cutoff
        (reflectCubeCompatibleSource cutoff planes source)
        (reflectCubeTarget planes target) ≈
      cubeCoupledRawWeight w cutoff source target := by
  unfold cubeCoupledRawWeight
  exact qmul_congr
    (cubeFaceRawProduct_reflection w cutoff planes source target)
    (cubeProductionLinkProduct_reflection cutoff planes target)

theorem cubeCoupledPartition_reflection
    (w : Q') (cutoff : Nat) (planes : CubeReflectionPlanes)
    (source : CubeStretchedCompatibleSource cutoff) :
    cubeCoupledPartition w cutoff
        (reflectCubeCompatibleSource cutoff planes source) ≈
      cubeCoupledPartition w cutoff source := by
  let reflectedSource :=
    reflectCubeCompatibleSource cutoff planes source
  let reflectTarget := reflectCubeTarget planes
  let targets := cubePairChannelStateSpace cutoff
  refine Q'.eqv_trans _
    (listQSum (cubeCoupledRawWeight w cutoff reflectedSource)
      (targets.map reflectTarget)) _ ?_ ?_
  · exact YMGap.Continuum.Z4CanonicalPolymerRange.listQSum_perm _
      (reflectCubePairChannelStateSpace_perm cutoff planes).symm
  · rw [listQSum_map]
    apply listQSum_congr_on
    intro target _
    exact cubeCoupledRawWeight_reflection
      w cutoff planes source target

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

theorem cubeCoupledConditionalKernel_reflection_equivariant
    (w : Q') (hw : (0 : Q') < w) (cutoff : Nat)
    (planes : CubeReflectionPlanes)
    (source : CubeStretchedCompatibleSource cutoff)
    (target : CubePairChannelState) :
    cubeCoupledConditionalKernel w hw cutoff
        (reflectCubeCompatibleSource cutoff planes source)
        (reflectCubeTarget planes target) ≈
      cubeCoupledConditionalKernel w hw cutoff source target := by
  unfold cubeCoupledConditionalKernel
  exact divPos_eqv_congr_local
    (cubeCoupledPartition_pos hw cutoff
      (reflectCubeCompatibleSource cutoff planes source))
    (cubeCoupledPartition_pos hw cutoff source)
    (cubeCoupledRawWeight_reflection
      w cutoff planes source target)
    (cubeCoupledPartition_reflection
      w cutoff planes source)

/-- The actual plane of each face supplies the corrected-slab reflection
instance used by the closed cube component. -/
def geometricCubeReflectionPlanes : CubeReflectionPlanes :=
  fun face => (cubeFace face).2

theorem cubeCoupledConditionalKernel_geometric_reflection_equivariant
    (w : Q') (hw : (0 : Q') < w) (cutoff : Nat)
    (source : CubeStretchedCompatibleSource cutoff)
    (target : CubePairChannelState) :
    cubeCoupledConditionalKernel w hw cutoff
        (reflectCubeCompatibleSource cutoff
          geometricCubeReflectionPlanes source)
        (reflectCubeTarget geometricCubeReflectionPlanes target) ≈
      cubeCoupledConditionalKernel w hw cutoff source target :=
  cubeCoupledConditionalKernel_reflection_equivariant
    w hw cutoff geometricCubeReflectionPlanes source target

/-! ## 6. Explicit non-vacuity -/

def vacuumCubeCompatibleSource : CubeStretchedCompatibleSource 1 where
  packet := fun _ => vacuumBoundedFaceSpinPacket
  commonTotal := 0
  total_eq := by intro face; cases face <;> rfl

def oneFundamentalCubeCompatibleSource :
    CubeStretchedCompatibleSource 1 where
  packet := fun _ => oneFaceFundamentalBoundedPacket
  commonTotal := 1
  total_eq := by intro face; cases face <;> rfl

theorem vacuumCubePartition_pos
    {w : Q'} (hw : (0 : Q') < w) :
    (0 : Q') < cubeCoupledPartition w 1
      vacuumCubeCompatibleSource :=
  cubeCoupledPartition_pos hw 1 vacuumCubeCompatibleSource

theorem cubeCompatible_carrier_has_distinct_sources :
    (vacuumCubeCompatibleSource.packet .bottomXY).val ≠
      (oneFundamentalCubeCompatibleSource.packet .bottomXY).val := by
  intro heq
  have hspin := congrArg FaceSpinPacket.spin0 heq
  change (0 : Nat) = 1 at hspin
  omega

/-! ## Dependency gates -/

#print axioms cubePairChannelStateSpace_nodup
#print axioms cubeProductionIncidences_map_link
#print axioms cubeProductionIncidence_on_recorded_faces
#print axioms compatibleCubeTarget_mem
#print axioms compatibleCubeProductionLinkProduct_eqv_one
#print axioms compatibleCubeRawWeight_pos
#print axioms cubeCoupledPartition_pos
#print axioms cubeCoupledConditionalKernel_row_normalized
#print axioms reflectCubePairChannelStateSpace_perm
#print axioms cubeCoupledRawWeight_reflection
#print axioms cubeCoupledPartition_reflection
#print axioms cubeCoupledConditionalKernel_reflection_equivariant
#print axioms cubeCoupledConditionalKernel_geometric_reflection_equivariant
#print axioms vacuumCubePartition_pos
#print axioms cubeCompatible_carrier_has_distinct_sources

end YMGap.Continuum.Z4DyadicSlabCubeCoupledConditionalKernel
