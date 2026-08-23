/-
# Loop-free carrier-size path scale on finite BF4 vacuum sectors

The original connected-component witness may revisit vertices.  Constructive
loop erasure replaces it by a positive physical-kernel path whose vertex list
is duplicate-free and lies in the finite vacuum-sector carrier.  Hence its
edge length is bounded by the carrier length, and the finite Cauchy path
estimate has the explicit scale

  1 + (vacuum-sector carrier length)^2.

This removes the opaque maximum over recursively generated canonical walks.
The carrier length can still grow with the cutoff, and no uniform physical
edge-floor comparison, completed gap, thermodynamic/continuum limit, or Clay
conclusion is asserted.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathLengthEnergy
import YMGap.Continuum.FiniteBoolGraphSimplePaths

namespace YMGap.Continuum.BF4PhysicalFiniteVacuumSectorSimplePathScale

set_option maxRecDepth 100000
set_option maxHeartbeats 15000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorDirichlet
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorEdgeFloor
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathCeiling
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEnergy
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathLengthEnergy
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteBoolGraphComponents
open YMGap.Continuum.FiniteBoolGraphSimplePaths
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

/-! ## 1. A loop-free positive-kernel path -/

namespace PositiveKernelChainIn

def ofSupportedWalk
    {State : Type} [DecidableEq State]
    (adjacent : State → State → Bool)
    (kernel : State → State → Q') (support : List State)
    (edgePositive : ∀ first next,
      first ∈ support → next ∈ support →
      adjacent first next = true → (0 : Q') < kernel first next) :
    {first last : State} → first ∈ support →
      FiniteBoolGraphSimplePaths.Walk
        (supportedEdge adjacent support) first last →
      PositiveKernelChainIn kernel support first last
  | first, _, _hfirst, FiniteBoolGraphSimplePaths.Walk.single _ =>
      PositiveKernelChainIn.refl first
  | first, _, hfirst,
      FiniteBoolGraphSimplePaths.Walk.cons hedge rest => by
      have hparts := (Bool.and_eq_true _ _).mp hedge
      have hnext : rest.start ∈ support := of_decide_eq_true hparts.2
      exact PositiveKernelChainIn.step
        (edgePositive first rest.start hfirst hnext hparts.1) hnext
        (ofSupportedWalk adjacent kernel support edgePositive hnext rest)

theorem edgeLength_ofSupportedWalk
    {State : Type} [DecidableEq State]
    (adjacent : State → State → Bool)
    (kernel : State → State → Q') (support : List State)
    (edgePositive : ∀ first next,
      first ∈ support → next ∈ support →
      adjacent first next = true → (0 : Q') < kernel first next) :
    ∀ {first last : State} (hfirst : first ∈ support)
      (path : FiniteBoolGraphSimplePaths.Walk
        (supportedEdge adjacent support) first last),
      BF4PhysicalFiniteVacuumSectorPathLengthEnergy.PositiveKernelChainIn.edgeLength
          (ofSupportedWalk adjacent kernel support edgePositive hfirst path) =
        path.edgeLength
  | _, _, _, FiniteBoolGraphSimplePaths.Walk.single _ => rfl
  | _, _, hfirst,
      FiniteBoolGraphSimplePaths.Walk.cons hedge rest => by
      have hparts := (Bool.and_eq_true _ _).mp hedge
      have hnext : rest.start ∈ support := of_decide_eq_true hparts.2
      simp only [ofSupportedWalk,
        BF4PhysicalFiniteVacuumSectorPathLengthEnergy.PositiveKernelChainIn.edgeLength,
        FiniteBoolGraphSimplePaths.Walk.edgeLength]
      rw [edgeLength_ofSupportedWalk adjacent kernel support edgePositive
        hnext rest]
      rfl

end PositiveKernelChainIn

def centralPhysicalFiniteVacuumSectorSimpleWalk
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat)
    (left right : Nat)
    (hleft : left ∈
      centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
    (hright : right ∈
      centralPhysicalFiniteVacuumSectorIndices w hw cutoff half) :
    SupportBoundedSimpleWalk
      (centralPhysicalFiniteSupportAdjacentB w hw cutoff half)
      (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
      left right :=
  supportBoundedSimpleWalkOfChainIn
    (centralPhysicalFiniteSupportAdjacentB w hw cutoff half)
    (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
    hleft
    (centralPhysicalFiniteVacuumSector_connected
      w hw cutoff half left right hleft hright)

def centralPhysicalFiniteVacuumSectorSimplePositivePath
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat)
    (left right : Nat)
    (hleft : left ∈
      centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
    (hright : right ∈
      centralPhysicalFiniteVacuumSectorIndices w hw cutoff half) :
    PositiveKernelChainIn
      (centralPhysicalFiniteKernel w hw cutoff half)
      (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
      left right :=
  PositiveKernelChainIn.ofSupportedWalk
    (centralPhysicalFiniteSupportAdjacentB w hw cutoff half)
    (centralPhysicalFiniteKernel w hw cutoff half)
    (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
    (fun _first _next hfirst hnext hedge =>
      centralPhysicalFiniteKernel_pos_of_supportAdjacent
        hfirst hnext hedge)
    hleft
    (centralPhysicalFiniteVacuumSectorSimpleWalk
      w hw cutoff half left right hleft hright).walk

theorem centralPhysicalFiniteVacuumSectorSimplePositivePath_edgeLength_le
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat)
    (left right : Nat)
    (hleft : left ∈
      centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
    (hright : right ∈
      centralPhysicalFiniteVacuumSectorIndices w hw cutoff half) :
    BF4PhysicalFiniteVacuumSectorPathLengthEnergy.PositiveKernelChainIn.edgeLength
        (centralPhysicalFiniteVacuumSectorSimplePositivePath
          w hw cutoff half left right hleft hright) ≤
      (centralPhysicalFiniteVacuumSectorIndices
        w hw cutoff half).length := by
  let simple := centralPhysicalFiniteVacuumSectorSimpleWalk
    w hw cutoff half left right hleft hright
  have hlength := PositiveKernelChainIn.edgeLength_ofSupportedWalk
    (centralPhysicalFiniteSupportAdjacentB w hw cutoff half)
    (centralPhysicalFiniteKernel w hw cutoff half)
    (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
    (fun first next hfirst hnext hedge =>
      centralPhysicalFiniteKernel_pos_of_supportAdjacent
        hfirst hnext hedge)
    hleft simple.walk
  change BF4PhysicalFiniteVacuumSectorPathLengthEnergy.PositiveKernelChainIn.edgeLength
      (PositiveKernelChainIn.ofSupportedWalk
        (centralPhysicalFiniteSupportAdjacentB w hw cutoff half)
        (centralPhysicalFiniteKernel w hw cutoff half)
        (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
        _ hleft simple.walk) ≤ _
  rw [hlength]
  exact simple.edgeLength_le

/-! ## 2. Explicit carrier-square scale and endpoint energy -/

def centralPhysicalFiniteVacuumSectorSimpleCarrierSquareScale
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat) : Q' :=
  let size :=
    (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half).length
  1 + Q'.ofNat (size * size)

theorem centralPhysicalFiniteVacuumSectorSimpleCarrierSquareScale_pos
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat) :
    (0 : Q') <
      centralPhysicalFiniteVacuumSectorSimpleCarrierSquareScale
        w hw cutoff half := by
  unfold centralPhysicalFiniteVacuumSectorSimpleCarrierSquareScale
  exact Q'.pos_add_nonneg (by decide)
    (Q'.ofNat_le_ofNat (Nat.zero_le _))

theorem centralPhysicalFiniteVacuumSectorSimplePath_quadraticLength_le_scale
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat)
    (left right : Nat)
    (hleft : left ∈
      centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
    (hright : right ∈
      centralPhysicalFiniteVacuumSectorIndices w hw cutoff half) :
    BF4PhysicalFiniteVacuumSectorPathLengthEnergy.PositiveKernelChainIn.quadraticLengthScale
        (centralPhysicalFiniteVacuumSectorSimplePositivePath
          w hw cutoff half left right hleft hright) ≤
      centralPhysicalFiniteVacuumSectorSimpleCarrierSquareScale
        w hw cutoff half := by
  let path := centralPhysicalFiniteVacuumSectorSimplePositivePath
    w hw cutoff half left right hleft hright
  let size :=
    (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half).length
  have hlength :
      BF4PhysicalFiniteVacuumSectorPathLengthEnergy.PositiveKernelChainIn.edgeLength
          path ≤ size :=
    centralPhysicalFiniteVacuumSectorSimplePositivePath_edgeLength_le
      w hw cutoff half left right hleft hright
  have hsquare :
      BF4PhysicalFiniteVacuumSectorPathLengthEnergy.PositiveKernelChainIn.edgeLength path *
          BF4PhysicalFiniteVacuumSectorPathLengthEnergy.PositiveKernelChainIn.edgeLength path ≤
        size * size :=
    Nat.mul_le_mul hlength hlength
  have hcast := Q'.ofNat_le_ofNat hsquare
  have hceiling : Q'.ofNat (size * size) ≤
      1 + Q'.ofNat (size * size) := by
    have hadd := Q'.add_le_add_right
      (0 : Q') 1 (Q'.ofNat (size * size))
      (by decide : (0 : Q') ≤ 1)
    rwa [Q'.zero_add'] at hadd
  unfold
    BF4PhysicalFiniteVacuumSectorPathLengthEnergy.PositiveKernelChainIn.quadraticLengthScale
    centralPhysicalFiniteVacuumSectorSimpleCarrierSquareScale
  exact Q'.le_trans' _ _ _ hcast hceiling

theorem centralPhysicalFiniteVacuumSector_floor_mul_endpoint_sq_le_simpleCarrierSquareScale_mul_Dirichlet
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
      centralPhysicalFiniteVacuumSectorSimpleCarrierSquareScale
          w hw cutoff half *
        finiteJointDirichletEnergy
          (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
          coefficient
          (centralPhysicalFiniteKernel w hw cutoff half) := by
  let path := centralPhysicalFiniteVacuumSectorSimplePositivePath
    w hw cutoff half left right hleft hright
  let energy := finiteJointDirichletEnergy
    (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
    coefficient (centralPhysicalFiniteKernel w hw cutoff half)
  have hlocal :=
    BF4PhysicalFiniteVacuumSectorPathLengthEnergy.PositiveKernelChainIn.floor_mul_endpointDifference_sq_le_length_sq_mul_finiteJointDirichletEnergy
      coefficient
      (fun source target => by
        unfold centralPhysicalFiniteKernel
        exact centralNormalizedPhysicalReflectedKernel_nonnegative
          hw cutoff half _ _)
      (centralPhysicalFiniteVacuumSectorEdgeFloor w hw cutoff half)
      (Q'.le_of_lt
        (centralPhysicalFiniteVacuumSectorEdgeFloor_pos
          w hw cutoff half))
      (fun source target hsource htarget hpositive =>
        centralPhysicalFiniteVacuumSectorEdgeFloor_le_positive_entry
          w hw cutoff half source target hsource htarget hpositive)
      hleft path
  have hscale :=
    centralPhysicalFiniteVacuumSectorSimplePath_quadraticLength_le_scale
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

end YMGap.Continuum.BF4PhysicalFiniteVacuumSectorSimplePathScale

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSectorSimplePathScale.PositiveKernelChainIn.edgeLength_ofSupportedWalk
#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSectorSimplePathScale.centralPhysicalFiniteVacuumSectorSimplePositivePath_edgeLength_le
#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSectorSimplePathScale.centralPhysicalFiniteVacuumSectorSimpleCarrierSquareScale_pos
#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSectorSimplePathScale.centralPhysicalFiniteVacuumSectorSimplePath_quadraticLength_le_scale
#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSectorSimplePathScale.centralPhysicalFiniteVacuumSector_floor_mul_endpoint_sq_le_simpleCarrierSquareScale_mul_Dirichlet
