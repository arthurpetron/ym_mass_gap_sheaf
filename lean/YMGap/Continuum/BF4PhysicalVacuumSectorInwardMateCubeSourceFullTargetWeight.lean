/-
# Exact weight of one fixed-order target block

The fixed-order target tuple carrier has exactly the production SU(2)
multiplicity.  Since BF4 Haar counting assigns one unit to each accepted
fusion assignment, summing its exact face-factor weight reconstructs the
genuine physical spin-foam term.

This is the one-physical-target normalization.  Summation over all physical
targets and the root/size congestion estimate remain downstream.

No `Classical`, choice, `native_decide`, `sorry`, custom axiom,
noncomputable declaration, enlarged heartbeat budget, or trusted external
computation is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetCarrier
import YMGap.Continuum.FiniteBistochasticCarrierBalance

namespace YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetWeight

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetCarrier
open YMGap.Continuum.FiniteBistochasticCarrierBalance
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity

local infix:50 " ≈ " => Q'.eqv

/-- The common weight of every accepted tuple in one physical target block:
its heat factor times one Haar counting unit. -/
def cubeInwardMateFixedOrderTargetBlockEntryWeight
    (coupling : Q') (K : Nat) (target : EdgeLabelling) : Q' :=
  slabParametricKPhysicalFaceFactor coupling K 1 target * 1

/-- **Exact target-block normalization.**  The complete fixed-order tuple
carrier over one bounded target has exactly its genuine BF4 physical term. -/
theorem cubeInwardMateFixedOrderTargetTuples_weight_total
    (coupling : Q') (K : Nat) (target : EdgeLabelling)
    (hbounded : SlabFaceLabellingBounded K 1 target) :
    listQSum
        (Function.const (CubeInwardMateFixedOrderTargetTuple K target)
          (cubeInwardMateFixedOrderTargetBlockEntryWeight coupling K target))
        (cubeInwardMateFixedOrderTargetTuples K target) ≈
      slabParametricKPhysicalTerm coupling K 1 target := by
  unfold cubeInwardMateFixedOrderTargetBlockEntryWeight
  let factor := slabParametricKPhysicalFaceFactor coupling K 1 target
  let tuples := cubeInwardMateFixedOrderTargetTuples K target
  refine Q'.eqv_trans _ (factor * listQSum (fun _ => (1 : Q')) tuples)
    _ ?_ ?_
  · exact listQSum_mul_left factor (fun _ => (1 : Q')) tuples
  refine Q'.eqv_trans _ (factor * Q'.ofNat tuples.length) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left factor _ _
      (listQSum_one_eqv_ofNat_length tuples)
  · unfold factor tuples slabParametricKPhysicalTerm
    rw [cubeInwardMateFixedOrderTargetTuples_length K target hbounded]
    exact Q'.eqv_refl _

#print axioms cubeInwardMateFixedOrderTargetBlockEntryWeight
#print axioms cubeInwardMateFixedOrderTargetTuples_weight_total

end YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetWeight
