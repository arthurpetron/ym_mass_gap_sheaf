/-
# The weighted BF4 atom of the global inward-mate target

The accepted all-target presentation is now forgotten to its literal raw
payload and evaluated by the actual BF4 retained-fiber weight.  Since Haar
counting gives every accepted auxiliary atom weight one, this target weight
is exactly the heat-kernel face factor of the parity-flipped physical state.

The analytic input for the next transport step is also made parity-free:
at the physical nome `w = 1/2`, every source label—not just an even one—has
heat coefficient at most four times its `evenInwardMateLabel` target.

No target-fiber capacity, summed retained-mass transport, posterior variance,
Osterwalder--Schrader form bound, or spectral gap is asserted here.

No `Classical`, choice, `native_decide`, `sorry`, custom axiom,
noncomputable declaration, enlarged heartbeat budget, or trusted external
computation is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetPresentation
import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateHeatBound

namespace YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetWeight

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetPhysical
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetPresentation
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalSourceNormalization
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateHeatBound
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateStretchedDebtFiber
open YMGap.Continuum.BF4SU2FineIntertwinerPhysicalDisintegration
open YMGap.Continuum.CompactDualSlabExpandedFacePeelWeight
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.CompactDualSlabPresentedFusionGlobalFaceStrandEdges
open YMGap.Continuum.PlaquetteActivity
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. One coefficient comparison without a parity precondition -/

/-- At the physical nome, every label is bounded by four times its
parity-flipped inward mate.  Even labels use the existing four-bound; odd
labels pay the stronger one-quarter predecessor bound. -/
theorem coeffW_half_le_four_evenInwardMate (spin : Nat) :
    coeffW cutoffTwoHalfCoupling spin ≤
      four * coeffW cutoffTwoHalfCoupling (evenInwardMateLabel spin) := by
  by_cases heven : spin % 2 = 0
  · exact coeffW_half_even_le_four_mate spin heven
  · have hmod : spin % 2 < 2 := Nat.mod_lt spin (by decide)
    have hodd : spin % 2 = 1 := by omega
    have hpositive : 0 < spin := by omega
    have hquarter := coeffW_half_odd_le_quarter_mate spin hodd
    have hrate : oneQuarter ≤ four := by decide
    have hscaled := Q'.mul_le_mul_of_nonneg_right _ _ _ hrate
      (coeffW_nonneg (w := cutoffTwoHalfCoupling) (by decide)
        (oddInwardMateLabel spin))
    have hfour := Q'.le_trans' _ _ _ hquarter hscaled
    simpa [oddInwardMateLabel, evenInwardMateLabel,
      Nat.ne_of_gt hpositive] using hfour

/-! ## 2. The actual raw target atom and its weight -/

/-- Forget the accepted target presentation to the raw auxiliary payload
consumed by the BF4 retained-fiber formula. -/
def GlobalCubeInwardMateCertifiedTargetFullSource.targetRaw
    {K : Nat} {hK : 1 ≤ K}
    (source : GlobalCubeInwardMateCertifiedTargetFullSource K hK) :
    SlabFusionWitnessAssignment :=
  (boundaryCompleteSlabLinks 1).attach.map fun linked =>
    (linked.1,
      (GlobalCubeInwardMateCertifiedTargetFullSource.targetPresented
        source linked).auxiliary)

/-- The physical/raw pair of the realized all-target BF4 atom. -/
def GlobalCubeInwardMateCertifiedTargetFullSource.targetAtom
    {K : Nat} {hK : 1 ≤ K}
    (source : GlobalCubeInwardMateCertifiedTargetFullSource K hK) :
    SlabLabelling × SlabFusionWitnessAssignment :=
  (GlobalCubeInwardMateCertifiedTargetFullSource.targetPhysical source,
    GlobalCubeInwardMateCertifiedTargetFullSource.targetRaw source)

/-- The actual anchor retained-fiber weight of the realized target atom. -/
def GlobalCubeInwardMateCertifiedTargetFullSource.targetWeight
    {K : Nat} {hK : 1 ≤ K}
    (source : GlobalCubeInwardMateCertifiedTargetFullSource K hK) : Q' :=
  let D : SlabPhysicalData :=
    { coupling := anchorCoupling
      coupling_nonnegative := by decide
      cutoff := K
      half := 0 }
  retainedFineIntertwinerPhysicalFiberWeight D
    (GlobalCubeInwardMateCertifiedTargetFullSource.targetPhysical source)
    (GlobalCubeInwardMateCertifiedTargetFullSource.targetRaw source)

/-- Unit Haar counting identifies the target atom weight exactly with the
heat-kernel face factor of its parity-flipped physical field. -/
theorem GlobalCubeInwardMateCertifiedTargetFullSource.targetWeight_eqv_faceFactor
    {K : Nat} {hK : 1 ≤ K}
    (source : GlobalCubeInwardMateCertifiedTargetFullSource K hK) :
    GlobalCubeInwardMateCertifiedTargetFullSource.targetWeight source ≈
      slabParametricKPhysicalFaceFactor anchorCoupling K 1
        (GlobalCubeInwardMateCertifiedTargetFullSource.targetPhysical
          source) := by
  unfold GlobalCubeInwardMateCertifiedTargetFullSource.targetWeight
  simpa only [SlabPhysicalData.extent, Nat.zero_add, Nat.add_zero] using
    retainedFineIntertwinerPhysicalFiberWeight_eqv_faceFactor
      ({ coupling := anchorCoupling
         coupling_nonnegative := by decide
         cutoff := K
         half := 0 } : SlabPhysicalData)
      (GlobalCubeInwardMateCertifiedTargetFullSource.targetPhysical source)
      (GlobalCubeInwardMateCertifiedTargetFullSource.targetRaw source)

#print axioms coeffW_half_le_four_evenInwardMate
#print axioms GlobalCubeInwardMateCertifiedTargetFullSource.targetRaw
#print axioms GlobalCubeInwardMateCertifiedTargetFullSource.targetAtom
#print axioms GlobalCubeInwardMateCertifiedTargetFullSource.targetWeight
#print axioms GlobalCubeInwardMateCertifiedTargetFullSource.targetWeight_eqv_faceFactor

end YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetWeight
