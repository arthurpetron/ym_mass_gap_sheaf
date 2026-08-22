/-
# One finite amplification ceiling for every BF4 vacuum-sector path

Every canonical path already carries an explicit scale multiplying the global
Dirichlet energy.  To make that estimate uniform over endpoints, this module
packages sector membership in attached-list subtypes, enumerates their finite
Cartesian square, and sums all nonnegative path scales.  Adding `1` gives a
strictly positive coefficient-independent ceiling above each individual
scale.

Combining the common positive edge floor, local path domination, global path
comparison, and this ceiling yields one endpoint inequality valid for every
pair of indices in a fixed finite BF4 vacuum sector.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathGlobalEnergy

namespace YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathCeiling

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorDirichlet
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorEdgeFloor
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEnergy
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathGlobalEnergy
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

private theorem square_nonnegative (value : Q') :
    (0 : Q') ≤ value * value :=
  YMGap.Constructive.SumOfSquares.q_mul_self_nonneg value

/-! ## 1. Nonnegativity of the global energy -/

theorem finiteJointDirichletEnergy_nonnegative
    {State : Type} (states : List State)
    (coefficient : State → Q') (joint : State → State → Q')
    (hjoint : ∀ left right, (0 : Q') ≤ joint left right) :
    (0 : Q') ≤ finiteJointDirichletEnergy states coefficient joint := by
  unfold finiteJointDirichletEnergy
  apply listQSum_nonnegative_on
  intro left _hleft
  apply listQSum_nonnegative_on
  intro right _hright
  exact Q'.mul_nonneg _ _ (hjoint left right)
    (square_nonnegative _)

/-! ## 2. The attached finite family of canonical path scales -/

/-- Scale of the canonical path between two membership-carrying sector
indices. -/
def centralPhysicalFiniteVacuumSectorPathScale
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat)
    (pair :
      {index // index ∈
        centralPhysicalFiniteVacuumSectorIndices w hw cutoff half} ×
      {index // index ∈
        centralPhysicalFiniteVacuumSectorIndices w hw cutoff half}) : Q' :=
  BF4PhysicalFiniteVacuumSectorPathGlobalEnergy.PositiveKernelChainIn.amplificationScale
    (centralPhysicalFiniteVacuumSectorPositivePath
      w hw cutoff half
      pair.1.val pair.2.val pair.1.property pair.2.property)

theorem centralPhysicalFiniteVacuumSectorPathScale_nonnegative
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat)
    (pair :
      {index // index ∈
        centralPhysicalFiniteVacuumSectorIndices w hw cutoff half} ×
      {index // index ∈
        centralPhysicalFiniteVacuumSectorIndices w hw cutoff half}) :
    (0 : Q') ≤
      centralPhysicalFiniteVacuumSectorPathScale
        w hw cutoff half pair := by
  unfold centralPhysicalFiniteVacuumSectorPathScale
  exact
    BF4PhysicalFiniteVacuumSectorPathGlobalEnergy.PositiveKernelChainIn.amplificationScale_nonnegative
      _

/-- Sum of every canonical path scale over the finite attached Cartesian
square. -/
def centralPhysicalFiniteVacuumSectorPathScaleSum
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat) : Q' :=
  listQSum
    (centralPhysicalFiniteVacuumSectorPathScale w hw cutoff half)
    (cartesian
      (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half).attach
      (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half).attach)

/-- A strictly positive common ceiling above every canonical path scale. -/
def centralPhysicalFiniteVacuumSectorPathCeiling
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat) : Q' :=
  1 + centralPhysicalFiniteVacuumSectorPathScaleSum
    w hw cutoff half

theorem centralPhysicalFiniteVacuumSectorPathScaleSum_nonnegative
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat) :
    (0 : Q') ≤
      centralPhysicalFiniteVacuumSectorPathScaleSum
        w hw cutoff half := by
  unfold centralPhysicalFiniteVacuumSectorPathScaleSum
  exact listQSum_nonnegative_on _ _
    (fun pair _ =>
      centralPhysicalFiniteVacuumSectorPathScale_nonnegative
        w hw cutoff half pair)

theorem centralPhysicalFiniteVacuumSectorPathCeiling_pos
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat) :
    (0 : Q') <
      centralPhysicalFiniteVacuumSectorPathCeiling
        w hw cutoff half := by
  unfold centralPhysicalFiniteVacuumSectorPathCeiling
  exact Q'.pos_add_nonneg (by decide)
    (centralPhysicalFiniteVacuumSectorPathScaleSum_nonnegative
      w hw cutoff half)

/-- Every endpoint-specific canonical path scale lies below the common finite
ceiling. -/
theorem centralPhysicalFiniteVacuumSectorPathScale_le_ceiling
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat)
    (left right : Nat)
    (hleft : left ∈
      centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
    (hright : right ∈
      centralPhysicalFiniteVacuumSectorIndices w hw cutoff half) :
    BF4PhysicalFiniteVacuumSectorPathGlobalEnergy.PositiveKernelChainIn.amplificationScale
        (centralPhysicalFiniteVacuumSectorPositivePath
          w hw cutoff half left right hleft hright) ≤
      centralPhysicalFiniteVacuumSectorPathCeiling
        w hw cutoff half := by
  let states :=
    centralPhysicalFiniteVacuumSectorIndices w hw cutoff half
  let leftEntry : {index // index ∈ states} := ⟨left, hleft⟩
  let rightEntry : {index // index ∈ states} := ⟨right, hright⟩
  have hpair : (leftEntry, rightEntry) ∈
      cartesian states.attach states.attach := by
    apply (mem_cartesian_iff _ _ _).mpr
    exact ⟨List.mem_attach _ leftEntry,
      List.mem_attach _ rightEntry⟩
  have hmember :
      centralPhysicalFiniteVacuumSectorPathScale
          w hw cutoff half (leftEntry, rightEntry) ≤
        centralPhysicalFiniteVacuumSectorPathScaleSum
          w hw cutoff half := by
    unfold centralPhysicalFiniteVacuumSectorPathScaleSum
    exact listQSum_member_le_nonnegative
      (centralPhysicalFiniteVacuumSectorPathScale w hw cutoff half)
      (centralPhysicalFiniteVacuumSectorPathScale_nonnegative
        w hw cutoff half)
      (cartesian states.attach states.attach) hpair
  have hsumCeiling :
      centralPhysicalFiniteVacuumSectorPathScaleSum w hw cutoff half ≤
        centralPhysicalFiniteVacuumSectorPathCeiling
          w hw cutoff half := by
    unfold centralPhysicalFiniteVacuumSectorPathCeiling
    have hle := Q'.add_le_add_right
      (0 : Q') 1
      (centralPhysicalFiniteVacuumSectorPathScaleSum
        w hw cutoff half)
      (Q'.le_of_lt (by decide : (0 : Q') < 1))
    rwa [Q'.zero_add'] at hle
  change centralPhysicalFiniteVacuumSectorPathScale
      w hw cutoff half (leftEntry, rightEntry) ≤
    centralPhysicalFiniteVacuumSectorPathCeiling
      w hw cutoff half
  exact Q'.le_trans' _ _ _ hmember hsumCeiling

/-! ## 3. One endpoint bound using the common floor and ceiling -/

theorem centralPhysicalFiniteVacuumSector_floor_mul_endpoint_sq_le_ceiling_mul_Dirichlet
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
      centralPhysicalFiniteVacuumSectorPathCeiling w hw cutoff half *
        finiteJointDirichletEnergy
          (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
          coefficient
          (centralPhysicalFiniteKernel w hw cutoff half) := by
  let path := centralPhysicalFiniteVacuumSectorPositivePath
    w hw cutoff half left right hleft hright
  let globalEnergy := finiteJointDirichletEnergy
    (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
    coefficient (centralPhysicalFiniteKernel w hw cutoff half)
  have hlocal :=
    centralPhysicalFiniteVacuumSector_edgeFloor_mul_endpoint_sq_le_pathEnergy
      w hw cutoff half coefficient left right hleft hright
  have hglobal :=
    centralPhysicalFiniteVacuumSector_pathEnergy_le_scale_mul_Dirichlet
      w hw cutoff half coefficient left right hleft hright
  have hscale :=
    centralPhysicalFiniteVacuumSectorPathScale_le_ceiling
      w hw cutoff half left right hleft hright
  have henergy0 : (0 : Q') ≤ globalEnergy := by
    exact finiteJointDirichletEnergy_nonnegative
      (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
      coefficient (centralPhysicalFiniteKernel w hw cutoff half)
      (fun source target => by
        unfold centralPhysicalFiniteKernel
        exact centralNormalizedPhysicalReflectedKernel_nonnegative
          hw cutoff half _ _)
  have hscaled :
      BF4PhysicalFiniteVacuumSectorPathGlobalEnergy.PositiveKernelChainIn.amplificationScale
          path * globalEnergy ≤
        centralPhysicalFiniteVacuumSectorPathCeiling w hw cutoff half *
          globalEnergy :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hscale henergy0
  exact Q'.le_trans' _ _ _ hlocal
    (Q'.le_trans' _ _ _ hglobal hscaled)

end YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathCeiling

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathCeiling.finiteJointDirichletEnergy_nonnegative
#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathCeiling.centralPhysicalFiniteVacuumSectorPathCeiling_pos
#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathCeiling.centralPhysicalFiniteVacuumSectorPathScale_le_ceiling
#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathCeiling.centralPhysicalFiniteVacuumSector_floor_mul_endpoint_sq_le_ceiling_mul_Dirichlet
