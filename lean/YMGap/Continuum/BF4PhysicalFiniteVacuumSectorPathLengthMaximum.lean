/-
# Maximum quadratic path-length scale on a finite BF4 vacuum sector

The canonical-path endpoint estimate now costs the square of the displayed
path length rather than a recursively doubled exponential scale.  This module
takes the located finite maximum of those quadratic scales, proves that it
controls every endpoint pair, and proves that the resulting ceiling is no
larger than the former maximum-amplification ceiling.

This is a fixed-carrier quantitative improvement.  It does not provide a
uniform path-length bound or physical edge floor on expanding carriers, and
it does not assert a completed, thermodynamic, continuum, or Clay mass gap.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathLengthEnergy

namespace YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathLengthMaximum

set_option maxRecDepth 100000
set_option maxHeartbeats 15000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorDirichlet
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorEdgeFloor
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathCeiling
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEnergy
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathGlobalEnergy
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathLengthEnergy
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathMaximum
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

/-! ## 1. Monotonicity of the seeded finite maximum -/

theorem listQMaxZero_mono
    {State : Type} (left right : State → Q')
    (hle : ∀ state, left state ≤ right state) :
    ∀ states : List State,
      listQMaxZero left states ≤ listQMaxZero right states
  | [] => Q'.le_refl' 0
  | state :: states => by
      unfold listQMaxZero
      apply (Q'.max'_le_iff' _ _ _).mpr
      constructor
      · exact Q'.le_trans' _ _ _ (hle state)
          (Q'.le_max'_left _ _)
      · exact Q'.le_trans' _ _ _
          (listQMaxZero_mono left right hle states)
          (Q'.le_max'_right _ _)

/-! ## 2. Located maximum of the quadratic length scales -/

/-- Quadratic length scale of the canonical path between two attached sector
indices. -/
def centralPhysicalFiniteVacuumSectorPathLengthSquare
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat)
    (pair :
      {index // index ∈
        centralPhysicalFiniteVacuumSectorIndices w hw cutoff half} ×
      {index // index ∈
        centralPhysicalFiniteVacuumSectorIndices w hw cutoff half}) : Q' :=
  BF4PhysicalFiniteVacuumSectorPathLengthEnergy.PositiveKernelChainIn.quadraticLengthScale
    (centralPhysicalFiniteVacuumSectorPositivePath
      w hw cutoff half
      pair.1.val pair.2.val pair.1.property pair.2.property)

/-- Located maximum of every quadratic canonical-path length scale. -/
def centralPhysicalFiniteVacuumSectorPathLengthSquareMax
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat) : Q' :=
  listQMaxZero
    (centralPhysicalFiniteVacuumSectorPathLengthSquare w hw cutoff half)
    (cartesian
      (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half).attach
      (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half).attach)

/-- Positive ceiling obtained by adjoining the harmless unit fallback. -/
def centralPhysicalFiniteVacuumSectorPathLengthMaximum
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat) : Q' :=
  1 + centralPhysicalFiniteVacuumSectorPathLengthSquareMax
    w hw cutoff half

theorem centralPhysicalFiniteVacuumSectorPathLengthSquare_nonnegative
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat)
    (pair :
      {index // index ∈
        centralPhysicalFiniteVacuumSectorIndices w hw cutoff half} ×
      {index // index ∈
        centralPhysicalFiniteVacuumSectorIndices w hw cutoff half}) :
    (0 : Q') ≤ centralPhysicalFiniteVacuumSectorPathLengthSquare
      w hw cutoff half pair := by
  unfold centralPhysicalFiniteVacuumSectorPathLengthSquare
    BF4PhysicalFiniteVacuumSectorPathLengthEnergy.PositiveKernelChainIn.quadraticLengthScale
  rw [Q'.zero_le_iff_num_nonneg]
  exact Int.natCast_nonneg _

theorem centralPhysicalFiniteVacuumSectorPathLengthSquareMax_nonnegative
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat) :
    (0 : Q') ≤ centralPhysicalFiniteVacuumSectorPathLengthSquareMax
      w hw cutoff half := by
  unfold centralPhysicalFiniteVacuumSectorPathLengthSquareMax
  exact listQMaxZero_nonnegative _
    (centralPhysicalFiniteVacuumSectorPathLengthSquare_nonnegative
      w hw cutoff half) _

theorem centralPhysicalFiniteVacuumSectorPathLengthMaximum_pos
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat) :
    (0 : Q') < centralPhysicalFiniteVacuumSectorPathLengthMaximum
      w hw cutoff half := by
  unfold centralPhysicalFiniteVacuumSectorPathLengthMaximum
  exact Q'.pos_add_nonneg (by decide)
    (centralPhysicalFiniteVacuumSectorPathLengthSquareMax_nonnegative
      w hw cutoff half)

/-- Every endpoint-specific quadratic length scale lies below the located
finite ceiling. -/
theorem centralPhysicalFiniteVacuumSectorPathLengthSquare_le_maximum
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat)
    (left right : Nat)
    (hleft : left ∈
      centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
    (hright : right ∈
      centralPhysicalFiniteVacuumSectorIndices w hw cutoff half) :
    BF4PhysicalFiniteVacuumSectorPathLengthEnergy.PositiveKernelChainIn.quadraticLengthScale
        (centralPhysicalFiniteVacuumSectorPositivePath
          w hw cutoff half left right hleft hright) ≤
      centralPhysicalFiniteVacuumSectorPathLengthMaximum
        w hw cutoff half := by
  let states := centralPhysicalFiniteVacuumSectorIndices w hw cutoff half
  let leftEntry : {index // index ∈ states} := ⟨left, hleft⟩
  let rightEntry : {index // index ∈ states} := ⟨right, hright⟩
  have hpair : (leftEntry, rightEntry) ∈
      cartesian states.attach states.attach :=
    (mem_cartesian_iff _ _ _).mpr
      ⟨List.mem_attach _ leftEntry, List.mem_attach _ rightEntry⟩
  have hmax :
      centralPhysicalFiniteVacuumSectorPathLengthSquare
          w hw cutoff half (leftEntry, rightEntry) ≤
        centralPhysicalFiniteVacuumSectorPathLengthSquareMax
          w hw cutoff half := by
    unfold centralPhysicalFiniteVacuumSectorPathLengthSquareMax
    exact le_listQMaxZero_of_mem _ _ hpair
  have hmaxLe :
      centralPhysicalFiniteVacuumSectorPathLengthSquareMax w hw cutoff half ≤
        centralPhysicalFiniteVacuumSectorPathLengthMaximum
          w hw cutoff half := by
    unfold centralPhysicalFiniteVacuumSectorPathLengthMaximum
    have hadd := Q'.add_le_add_right
      (0 : Q') 1
      (centralPhysicalFiniteVacuumSectorPathLengthSquareMax
        w hw cutoff half)
      (by decide : (0 : Q') ≤ 1)
    rwa [Q'.zero_add'] at hadd
  change centralPhysicalFiniteVacuumSectorPathLengthSquare
      w hw cutoff half (leftEntry, rightEntry) ≤
    centralPhysicalFiniteVacuumSectorPathLengthMaximum w hw cutoff half
  exact Q'.le_trans' _ _ _ hmax hmaxLe

/-! ## 3. Comparison with the old maximum and endpoint domination -/

theorem centralPhysicalFiniteVacuumSectorPathLengthSquare_le_pathScale
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat)
    (pair :
      {index // index ∈
        centralPhysicalFiniteVacuumSectorIndices w hw cutoff half} ×
      {index // index ∈
        centralPhysicalFiniteVacuumSectorIndices w hw cutoff half}) :
    centralPhysicalFiniteVacuumSectorPathLengthSquare
        w hw cutoff half pair ≤
      centralPhysicalFiniteVacuumSectorPathScale
        w hw cutoff half pair := by
  exact
    BF4PhysicalFiniteVacuumSectorPathLengthEnergy.PositiveKernelChainIn.quadraticLengthScale_le_amplificationScale
      (centralPhysicalFiniteVacuumSectorPositivePath
        w hw cutoff half pair.1.val pair.2.val
        pair.1.property pair.2.property)

/-- The new quadratic-length ceiling is no larger than the former maximum of
the recursively doubled amplification scales. -/
theorem centralPhysicalFiniteVacuumSectorPathLengthMaximum_le_pathMaximum
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat) :
    centralPhysicalFiniteVacuumSectorPathLengthMaximum w hw cutoff half ≤
      centralPhysicalFiniteVacuumSectorPathMaximum w hw cutoff half := by
  let pairs := cartesian
    (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half).attach
    (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half).attach
  have hmax :
      listQMaxZero
          (centralPhysicalFiniteVacuumSectorPathLengthSquare
            w hw cutoff half) pairs ≤
        listQMaxZero
          (centralPhysicalFiniteVacuumSectorPathScale
            w hw cutoff half) pairs := by
    exact listQMaxZero_mono _ _
      (centralPhysicalFiniteVacuumSectorPathLengthSquare_le_pathScale
        w hw cutoff half) pairs
  change 1 + listQMaxZero
      (centralPhysicalFiniteVacuumSectorPathLengthSquare
        w hw cutoff half) pairs ≤
    1 + listQMaxZero
      (centralPhysicalFiniteVacuumSectorPathScale w hw cutoff half) pairs
  exact Q'.add_le_add_left 1 _ _ hmax

/-- The finite edge floor controls every endpoint square by the sharper
quadratic-length maximum times the full directed Dirichlet energy. -/
theorem centralPhysicalFiniteVacuumSector_floor_mul_endpoint_sq_le_pathLengthMaximum_mul_Dirichlet
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat)
    (coefficient : Nat → Q')
    (left right : Nat)
    (hleft : left ∈
      centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
    (hright : right ∈
      centralPhysicalFiniteVacuumSectorIndices w hw cutoff half) :
    centralPhysicalFiniteVacuumSectorEdgeFloor w hw cutoff half *
        ((coefficient left + -coefficient right) *
          (coefficient left + -coefficient right)) ≤
      centralPhysicalFiniteVacuumSectorPathLengthMaximum w hw cutoff half *
        finiteJointDirichletEnergy
          (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
          coefficient
          (centralPhysicalFiniteKernel w hw cutoff half) := by
  let energy := finiteJointDirichletEnergy
    (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
    coefficient (centralPhysicalFiniteKernel w hw cutoff half)
  have hlocal :=
    centralPhysicalFiniteVacuumSector_floor_mul_endpoint_sq_le_quadraticLength_mul_Dirichlet
      w hw cutoff half coefficient left right hleft hright
  have hscale :=
    centralPhysicalFiniteVacuumSectorPathLengthSquare_le_maximum
      w hw cutoff half left right hleft hright
  have henergy0 : (0 : Q') ≤ energy :=
    BF4PhysicalFiniteVacuumSectorPathCeiling.finiteJointDirichletEnergy_nonnegative
      (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
      coefficient (centralPhysicalFiniteKernel w hw cutoff half)
      (fun source target => by
        unfold centralPhysicalFiniteKernel
        exact centralNormalizedPhysicalReflectedKernel_nonnegative
          hw cutoff half _ _)
  exact Q'.le_trans' _ _ _ hlocal
    (Q'.mul_le_mul_of_nonneg_right _ _ energy hscale henergy0)

end YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathLengthMaximum

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathLengthMaximum.centralPhysicalFiniteVacuumSectorPathLengthMaximum_pos
#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathLengthMaximum.centralPhysicalFiniteVacuumSectorPathLengthMaximum_le_pathMaximum
#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathLengthMaximum.centralPhysicalFiniteVacuumSector_floor_mul_endpoint_sq_le_pathLengthMaximum_mul_Dirichlet
