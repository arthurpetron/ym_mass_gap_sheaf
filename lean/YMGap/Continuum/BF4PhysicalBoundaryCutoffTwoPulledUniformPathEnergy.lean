/-
# Uniform path energy on the fixed cutoff-two pulled carrier

The canonical cutoff-two vacuum paths live on one fixed finite index list.
Every positive edge in those paths remains positive after embedding into any
later representation cutoff.  This module proves that qualitative persistence
from the existing support-graph embedding, then transports the paths to each
later pulled kernel without changing their combinatorial amplification scale.

The only new analytic certificate is a common positive lower bound on positive
entries of the fixed pulled kernel after one cutoff.  Such a floor contracts
with the fixed cutoff-two path ceiling to a cutoff-uniform endpoint bound in
terms of the pulled Dirichlet energy.  The floor certificate is not inhabited
here.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledPoincareGap
import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorEmbedding
import YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathCeiling

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledUniformPathEnergy

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledEntryPerturbation
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledPoincareGap
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledRecenteringPerturbation
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalCutoffEmbeddedEntryCauchy
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorEmbedding
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorDirichlet
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathCeiling
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEnergy
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathGlobalEnergy
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteDeterministicKernelPushforward

/-! ## 1. Rekernel a positive path without changing its shape -/

namespace PositiveKernelChainIn

/-- Replace the kernel carried by a positive path when positivity of every
used edge transfers to the replacement kernel. -/
def rekernel
    {State : Type} {kernel replacement : State → State → Q'}
    {support : List State}
    (edgePositive : ∀ first next,
      first ∈ support → next ∈ support →
      (0 : Q') < kernel first next →
      (0 : Q') < replacement first next) :
    {first last : State} → first ∈ support →
      BF4PhysicalFiniteVacuumSectorPositiveConnectivity.PositiveKernelChainIn
        kernel support first last →
      BF4PhysicalFiniteVacuumSectorPositiveConnectivity.PositiveKernelChainIn
        replacement support first last
  | first, _, _hfirst,
      BF4PhysicalFiniteVacuumSectorPositiveConnectivity.PositiveKernelChainIn.refl _ =>
      BF4PhysicalFiniteVacuumSectorPositiveConnectivity.PositiveKernelChainIn.refl
        first
  | first, _, hfirst,
      BF4PhysicalFiniteVacuumSectorPositiveConnectivity.PositiveKernelChainIn.step
        (next := next) positive hnext rest =>
      BF4PhysicalFiniteVacuumSectorPositiveConnectivity.PositiveKernelChainIn.step
        (edgePositive first next hfirst hnext positive) hnext
        (rekernel edgePositive hnext rest)

/-- Rekernelled paths have exactly the same recursive amplification scale. -/
theorem amplificationScale_rekernel
    {State : Type} {kernel replacement : State → State → Q'}
    {support : List State}
    (edgePositive : ∀ first next,
      first ∈ support → next ∈ support →
      (0 : Q') < kernel first next →
      (0 : Q') < replacement first next) :
    {first last : State} → (hfirst : first ∈ support) →
      (path :
        BF4PhysicalFiniteVacuumSectorPositiveConnectivity.PositiveKernelChainIn
          kernel support first last) →
      BF4PhysicalFiniteVacuumSectorPathGlobalEnergy.PositiveKernelChainIn.amplificationScale
          (rekernel edgePositive hfirst path) =
        BF4PhysicalFiniteVacuumSectorPathGlobalEnergy.PositiveKernelChainIn.amplificationScale
          path
  | _, _, _,
      BF4PhysicalFiniteVacuumSectorPositiveConnectivity.PositiveKernelChainIn.refl _ =>
      rfl
  | _, _, _,
      BF4PhysicalFiniteVacuumSectorPositiveConnectivity.PositiveKernelChainIn.step
        (next := next) _positive hnext rest => by
      change
        (1 +
            BF4PhysicalFiniteVacuumSectorPathGlobalEnergy.PositiveKernelChainIn.amplificationScale
              (rekernel edgePositive hnext rest)) +
          (1 +
            BF4PhysicalFiniteVacuumSectorPathGlobalEnergy.PositiveKernelChainIn.amplificationScale
              (rekernel edgePositive hnext rest)) =
        (1 +
            BF4PhysicalFiniteVacuumSectorPathGlobalEnergy.PositiveKernelChainIn.amplificationScale
              rest) +
          (1 +
            BF4PhysicalFiniteVacuumSectorPathGlobalEnergy.PositiveKernelChainIn.amplificationScale
              rest)
      rw [amplificationScale_rekernel edgePositive hnext rest]

end PositiveKernelChainIn

/-! ## 2. Qualitative persistence of the fixed canonical paths -/

/-- A positive normalized edge on the cutoff-two vacuum sector remains
positive in every later pulled kernel. -/
theorem cutoffTwoPulledKernelAt_pos_of_base_pos
    {later left right : Nat} (hlater : 2 ≤ later)
    (hleft : left ∈ cutoffTwoPulledStates)
    (hright : right ∈ cutoffTwoPulledStates)
    (hpositive : (0 : Q') <
      centralPhysicalFiniteKernel
        cutoffTwoHalfCoupling (by decide) 2 0 left right) :
    (0 : Q') < cutoffTwoPulledKernelAt later left right := by
  have hleftLt := centralPhysicalFiniteVacuumSectorIndex_lt
    cutoffTwoHalfCoupling (by decide) 2 0 hleft
  have hrightLt := centralPhysicalFiniteVacuumSectorIndex_lt
    cutoffTwoHalfCoupling (by decide) 2 0 hright
  have hadjacentBase :
      centralPhysicalFiniteSupportAdjacentB
          cutoffTwoHalfCoupling (by decide) 2 0 left right = true :=
    (centralPhysicalFiniteSupportAdjacentB_true_iff_kernel_pos
      hleft hright).mpr hpositive
  have hadjacentLater :=
    centralPhysicalFiniteSupportAdjacentB_cutoffIndexMap
      hlater hleftLt hrightLt hadjacentBase
  have hleftLater :=
    centralPhysicalFiniteVacuumSectorIndexMap_mem hlater hleft
  have hrightLater :=
    centralPhysicalFiniteVacuumSectorIndexMap_mem hlater hright
  unfold cutoffTwoPulledKernelAt centralPhysicalFinitePulledKernel
  exact centralPhysicalFiniteKernel_pos_of_supportAdjacent
    hleftLater hrightLater hadjacentLater

/-- The cutoff-two canonical path, with the same endpoints and index support,
rekernelled by the later pulled physical kernel. -/
def cutoffTwoPulledPositivePath
    (later : Nat) (hlater : 2 ≤ later)
    (left right : Nat)
    (hleft : left ∈ cutoffTwoPulledStates)
    (hright : right ∈ cutoffTwoPulledStates) :
    BF4PhysicalFiniteVacuumSectorPositiveConnectivity.PositiveKernelChainIn
      (cutoffTwoPulledKernelAt later) cutoffTwoPulledStates left right :=
  PositiveKernelChainIn.rekernel
    (fun first next hfirst hnext hpositive =>
      cutoffTwoPulledKernelAt_pos_of_base_pos
        hlater hfirst hnext hpositive)
    hleft
    (centralPhysicalFiniteVacuumSectorPositivePath
      cutoffTwoHalfCoupling (by decide) 2 0
      left right hleft hright)

theorem cutoffTwoPulledPositivePath_amplificationScale_eq_base
    (later : Nat) (hlater : 2 ≤ later)
    (left right : Nat)
    (hleft : left ∈ cutoffTwoPulledStates)
    (hright : right ∈ cutoffTwoPulledStates) :
    BF4PhysicalFiniteVacuumSectorPathGlobalEnergy.PositiveKernelChainIn.amplificationScale
        (cutoffTwoPulledPositivePath
          later hlater left right hleft hright) =
      BF4PhysicalFiniteVacuumSectorPathGlobalEnergy.PositiveKernelChainIn.amplificationScale
        (centralPhysicalFiniteVacuumSectorPositivePath
          cutoffTwoHalfCoupling (by decide) 2 0
          left right hleft hright) := by
  unfold cutoffTwoPulledPositivePath
  exact PositiveKernelChainIn.amplificationScale_rekernel
    (fun first next hfirst hnext hpositive =>
      cutoffTwoPulledKernelAt_pos_of_base_pos
        hlater hfirst hnext hpositive)
    hleft
    (centralPhysicalFiniteVacuumSectorPositivePath
      cutoffTwoHalfCoupling (by decide) 2 0
      left right hleft hright)

/-! ## 3. A common quantitative floor and the fixed path ceiling -/

/-- The remaining fixed-carrier analytic input: all positive entries of the
65-state pulled kernel have one common positive floor along a cutoff tail. -/
structure CutoffTwoPulledUniformPositiveEdgeFloor : Type 1 where
  floor : Q'
  floor_pos : (0 : Q') < floor
  start : Nat
  start_ge_two : 2 ≤ start
  floor_le : ∀ later : Nat, start ≤ later →
    ∀ left right : Nat,
      left ∈ cutoffTwoPulledStates →
      right ∈ cutoffTwoPulledStates →
      (0 : Q') < cutoffTwoPulledKernelAt later left right →
      floor ≤ cutoffTwoPulledKernelAt later left right

/-- The fixed coefficient-independent ceiling of the cutoff-two canonical
paths. -/
def cutoffTwoPulledCanonicalPathCeiling : Q' :=
  centralPhysicalFiniteVacuumSectorPathCeiling
    cutoffTwoHalfCoupling (by decide) 2 0

theorem cutoffTwoPulledCanonicalPathCeiling_pos :
    (0 : Q') < cutoffTwoPulledCanonicalPathCeiling :=
  centralPhysicalFiniteVacuumSectorPathCeiling_pos
    cutoffTwoHalfCoupling (by decide) 2 0

namespace CutoffTwoPulledUniformPositiveEdgeFloor

/-- A uniform positive pulled edge floor controls every endpoint difference
by the fixed path ceiling times the later pulled Dirichlet energy. -/
theorem floor_mul_endpoint_sq_le_ceiling_mul_pulledDirichlet
    (certificate : CutoffTwoPulledUniformPositiveEdgeFloor)
    (later : Nat) (hlater : certificate.start ≤ later)
    (coefficient : Nat → Q')
    (left right : Nat)
    (hleft : left ∈ cutoffTwoPulledStates)
    (hright : right ∈ cutoffTwoPulledStates) :
    certificate.floor *
        ((coefficient left + -coefficient right) *
          (coefficient left + -coefficient right)) ≤
      cutoffTwoPulledCanonicalPathCeiling *
        finiteJointDirichletEnergy cutoffTwoPulledStates coefficient
          (cutoffTwoPulledKernelAt later) := by
  have htwoLater : 2 ≤ later :=
    Nat.le_trans certificate.start_ge_two hlater
  let path := cutoffTwoPulledPositivePath
    later htwoLater left right hleft hright
  let energy := finiteJointDirichletEnergy
    cutoffTwoPulledStates coefficient (cutoffTwoPulledKernelAt later)
  have hlocal :
      certificate.floor *
          ((coefficient left + -coefficient right) *
            (coefficient left + -coefficient right)) ≤
        BF4PhysicalFiniteVacuumSectorPathEnergy.PositiveKernelChainIn.amplifiedEnergy
          coefficient path := by
    exact
      BF4PhysicalFiniteVacuumSectorPathEnergy.PositiveKernelChainIn.floor_mul_endpointDifference_sq_le_amplifiedEnergy
        coefficient certificate.floor (Q'.le_of_lt certificate.floor_pos)
        (fun first next hfirst hnext hpositive =>
          certificate.floor_le later hlater first next
            hfirst hnext hpositive)
        hleft path
  have hkernel : ∀ source target,
      (0 : Q') ≤ cutoffTwoPulledKernelAt later source target := by
    intro source target
    unfold cutoffTwoPulledKernelAt centralPhysicalFinitePulledKernel
      centralPhysicalFiniteKernel
    exact centralNormalizedPhysicalReflectedKernel_nonnegative
      (by decide) later 0 _ _
  have hglobal :
      BF4PhysicalFiniteVacuumSectorPathEnergy.PositiveKernelChainIn.amplifiedEnergy
          coefficient path ≤
        BF4PhysicalFiniteVacuumSectorPathGlobalEnergy.PositiveKernelChainIn.amplificationScale
            path * energy := by
    exact
      BF4PhysicalFiniteVacuumSectorPathGlobalEnergy.PositiveKernelChainIn.amplifiedEnergy_le_scale_mul_finiteJointDirichletEnergy
        coefficient hkernel hleft path
  have hbaseScale :=
    centralPhysicalFiniteVacuumSectorPathScale_le_ceiling
      cutoffTwoHalfCoupling (by decide) 2 0
      left right hleft hright
  have hscale :
      BF4PhysicalFiniteVacuumSectorPathGlobalEnergy.PositiveKernelChainIn.amplificationScale
          path ≤ cutoffTwoPulledCanonicalPathCeiling := by
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (Q'.eqv_of_eq
          (cutoffTwoPulledPositivePath_amplificationScale_eq_base
            later htwoLater left right hleft hright)))
      hbaseScale
  have henergy0 : (0 : Q') ≤ energy :=
    finiteJointDirichletEnergy_nonnegative
      cutoffTwoPulledStates coefficient
      (cutoffTwoPulledKernelAt later) hkernel
  have hscaled :
      BF4PhysicalFiniteVacuumSectorPathGlobalEnergy.PositiveKernelChainIn.amplificationScale
          path * energy ≤
        cutoffTwoPulledCanonicalPathCeiling * energy :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hscale henergy0
  exact Q'.le_trans' _ _ _ hlocal
    (Q'.le_trans' _ _ _ hglobal hscaled)

end CutoffTwoPulledUniformPositiveEdgeFloor

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledUniformPathEnergy

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledUniformPathEnergy.PositiveKernelChainIn.amplificationScale_rekernel
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledUniformPathEnergy.cutoffTwoPulledKernelAt_pos_of_base_pos
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledUniformPathEnergy.cutoffTwoPulledPositivePath_amplificationScale_eq_base
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledUniformPathEnergy.cutoffTwoPulledCanonicalPathCeiling_pos
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledUniformPathEnergy.CutoffTwoPulledUniformPositiveEdgeFloor.floor_mul_endpoint_sq_le_ceiling_mul_pulledDirichlet
