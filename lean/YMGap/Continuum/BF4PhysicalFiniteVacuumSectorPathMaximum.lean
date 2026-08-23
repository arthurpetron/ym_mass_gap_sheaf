/-
# The sharp finite maximum of the BF4 vacuum-sector path scales

The first constructive path argument used `1 +` the sum of every endpoint
path scale as a common ceiling.  Finite located maxima give a strictly sharper
coefficient-independent witness: `1 +` the largest path scale.  This module
constructs that maximum, proves it is bounded by the earlier sum ceiling, and
re-runs the endpoint estimate with the sharper constant.

This improves the finite constant but does not assert that the maxima or edge
floors are uniform on an expanding family of carriers.  No completed gap,
thermodynamic or continuum limit, or Clay conclusion is claimed.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathCeiling

namespace YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathMaximum

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorDirichlet
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorEdgeFloor
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathCeiling
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEnergy
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathGlobalEnergy
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

/-! ## 1. A total located maximum and its sum comparison -/

/-- Maximum of a rational function on a finite list, seeded at zero. -/
def listQMaxZero {State : Type}
    (value : State → Q') : List State → Q'
  | [] => 0
  | state :: rest => Q'.max' (value state) (listQMaxZero value rest)

theorem le_listQMaxZero_of_mem
    {State : Type} (value : State → Q') :
    ∀ (states : List State) {state : State},
      state ∈ states → value state ≤ listQMaxZero value states
  | [], _, hmember => False.elim (List.not_mem_nil hmember)
  | head :: tail, state, hmember => by
      rcases List.mem_cons.mp hmember with hhead | htail
      · subst state
        exact Q'.le_max'_left _ _
      · exact Q'.le_trans' _ _ _
          (le_listQMaxZero_of_mem value tail htail)
          (Q'.le_max'_right _ _)

theorem listQMaxZero_nonnegative
    {State : Type} (value : State → Q')
    (hvalue : ∀ state, (0 : Q') ≤ value state) :
    ∀ states : List State, (0 : Q') ≤ listQMaxZero value states
  | [] => Q'.le_refl' 0
  | head :: _tail =>
      Q'.le_trans' _ _ _ (hvalue head) (Q'.le_max'_left _ _)

theorem listQMaxZero_le_listQSum_of_nonnegative
    {State : Type} (value : State → Q')
    (hvalue : ∀ state, (0 : Q') ≤ value state) :
    ∀ states : List State,
      listQMaxZero value states ≤ listQSum value states
  | [] => Q'.le_refl' 0
  | head :: tail => by
      unfold listQMaxZero listQSum
      apply (Q'.max'_le_iff' _ _ _).mpr
      constructor
      · exact Q'.add_le_self_of_nonneg _ _
          (listQSum_nonnegative_on value tail (fun state _ => hvalue state))
      · exact Q'.le_trans' _ _ _
          (listQMaxZero_le_listQSum_of_nonnegative value hvalue tail)
          (by
            have hadd := Q'.add_le_add_right
              (0 : Q') (value head) (listQSum value tail) (hvalue head)
            rwa [Q'.zero_add'] at hadd)

/-! ## 2. The maximum path ceiling -/

/-- Located maximum of all canonical path amplification scales. -/
def centralPhysicalFiniteVacuumSectorPathScaleMax
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat) : Q' :=
  listQMaxZero
    (centralPhysicalFiniteVacuumSectorPathScale w hw cutoff half)
    (cartesian
      (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half).attach
      (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half).attach)

/-- Positive maximum-based ceiling.  The added one avoids selecting a carrier
head and matches the earlier sum-ceiling convention. -/
def centralPhysicalFiniteVacuumSectorPathMaximum
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat) : Q' :=
  1 + centralPhysicalFiniteVacuumSectorPathScaleMax w hw cutoff half

theorem centralPhysicalFiniteVacuumSectorPathScaleMax_nonnegative
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat) :
    (0 : Q') ≤ centralPhysicalFiniteVacuumSectorPathScaleMax
      w hw cutoff half := by
  unfold centralPhysicalFiniteVacuumSectorPathScaleMax
  exact listQMaxZero_nonnegative _
    (centralPhysicalFiniteVacuumSectorPathScale_nonnegative
      w hw cutoff half) _

theorem centralPhysicalFiniteVacuumSectorPathMaximum_pos
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat) :
    (0 : Q') < centralPhysicalFiniteVacuumSectorPathMaximum
      w hw cutoff half := by
  unfold centralPhysicalFiniteVacuumSectorPathMaximum
  exact Q'.pos_add_nonneg (by decide)
    (centralPhysicalFiniteVacuumSectorPathScaleMax_nonnegative
      w hw cutoff half)

/-- The maximum-based ceiling is never worse than the original sum ceiling. -/
theorem centralPhysicalFiniteVacuumSectorPathMaximum_le_ceiling
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat) :
    centralPhysicalFiniteVacuumSectorPathMaximum w hw cutoff half ≤
      centralPhysicalFiniteVacuumSectorPathCeiling w hw cutoff half := by
  let pairs := cartesian
    (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half).attach
    (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half).attach
  change 1 + listQMaxZero
      (centralPhysicalFiniteVacuumSectorPathScale w hw cutoff half) pairs ≤
    1 + listQSum
      (centralPhysicalFiniteVacuumSectorPathScale w hw cutoff half) pairs
  exact Q'.add_le_add_left 1 _ _
    (listQMaxZero_le_listQSum_of_nonnegative _
      (centralPhysicalFiniteVacuumSectorPathScale_nonnegative
        w hw cutoff half) pairs)

theorem centralPhysicalFiniteVacuumSectorPathScale_le_maximum
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat)
    (left right : Nat)
    (hleft : left ∈
      centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
    (hright : right ∈
      centralPhysicalFiniteVacuumSectorIndices w hw cutoff half) :
    BF4PhysicalFiniteVacuumSectorPathGlobalEnergy.PositiveKernelChainIn.amplificationScale
        (centralPhysicalFiniteVacuumSectorPositivePath
          w hw cutoff half left right hleft hright) ≤
      centralPhysicalFiniteVacuumSectorPathMaximum
        w hw cutoff half := by
  let states := centralPhysicalFiniteVacuumSectorIndices w hw cutoff half
  let leftEntry : {index // index ∈ states} := ⟨left, hleft⟩
  let rightEntry : {index // index ∈ states} := ⟨right, hright⟩
  have hpair : (leftEntry, rightEntry) ∈
      cartesian states.attach states.attach := by
    exact (mem_cartesian_iff _ _ _).mpr
      ⟨List.mem_attach _ leftEntry, List.mem_attach _ rightEntry⟩
  have hmax :
      centralPhysicalFiniteVacuumSectorPathScale
          w hw cutoff half (leftEntry, rightEntry) ≤
        centralPhysicalFiniteVacuumSectorPathScaleMax
          w hw cutoff half := by
    unfold centralPhysicalFiniteVacuumSectorPathScaleMax
    exact le_listQMaxZero_of_mem _ _ hpair
  have hmaxLe :
      centralPhysicalFiniteVacuumSectorPathScaleMax w hw cutoff half ≤
        centralPhysicalFiniteVacuumSectorPathMaximum w hw cutoff half := by
    unfold centralPhysicalFiniteVacuumSectorPathMaximum
    have hadd := Q'.add_le_add_right
      (0 : Q') 1
      (centralPhysicalFiniteVacuumSectorPathScaleMax w hw cutoff half)
      (by decide : (0 : Q') ≤ 1)
    rwa [Q'.zero_add'] at hadd
  change centralPhysicalFiniteVacuumSectorPathScale
      w hw cutoff half (leftEntry, rightEntry) ≤
    centralPhysicalFiniteVacuumSectorPathMaximum w hw cutoff half
  exact Q'.le_trans' _ _ _ hmax hmaxLe

/-! ## 3. The sharper endpoint estimate -/

theorem centralPhysicalFiniteVacuumSector_floor_mul_endpoint_sq_le_maximum_mul_Dirichlet
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
      centralPhysicalFiniteVacuumSectorPathMaximum w hw cutoff half *
        finiteJointDirichletEnergy
          (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
          coefficient
          (centralPhysicalFiniteKernel w hw cutoff half) := by
  let path := centralPhysicalFiniteVacuumSectorPositivePath
    w hw cutoff half left right hleft hright
  let energy := finiteJointDirichletEnergy
    (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
    coefficient (centralPhysicalFiniteKernel w hw cutoff half)
  have hlocal :=
    centralPhysicalFiniteVacuumSector_edgeFloor_mul_endpoint_sq_le_pathEnergy
      w hw cutoff half coefficient left right hleft hright
  have hglobal :=
    centralPhysicalFiniteVacuumSector_pathEnergy_le_scale_mul_Dirichlet
      w hw cutoff half coefficient left right hleft hright
  have hscale :=
    centralPhysicalFiniteVacuumSectorPathScale_le_maximum
      w hw cutoff half left right hleft hright
  have henergy0 : (0 : Q') ≤ energy := by
    exact finiteJointDirichletEnergy_nonnegative
      (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
      coefficient (centralPhysicalFiniteKernel w hw cutoff half)
      (fun source target => by
        unfold centralPhysicalFiniteKernel
        exact centralNormalizedPhysicalReflectedKernel_nonnegative
          hw cutoff half _ _)
  have hscaled :
      BF4PhysicalFiniteVacuumSectorPathGlobalEnergy.PositiveKernelChainIn.amplificationScale
          path * energy ≤
        centralPhysicalFiniteVacuumSectorPathMaximum w hw cutoff half *
          energy :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hscale henergy0
  exact Q'.le_trans' _ _ _ hlocal
    (Q'.le_trans' _ _ _ hglobal hscaled)

end YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathMaximum

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathMaximum.centralPhysicalFiniteVacuumSectorPathMaximum_pos
#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathMaximum.centralPhysicalFiniteVacuumSectorPathMaximum_le_ceiling
#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathMaximum.centralPhysicalFiniteVacuumSectorPathScale_le_maximum
#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathMaximum.centralPhysicalFiniteVacuumSector_floor_mul_endpoint_sq_le_maximum_mul_Dirichlet
