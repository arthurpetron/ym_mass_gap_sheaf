/-
# Gram positivity on every finite canonical BF4 vacuum sector

The canonical vacuum component is a restriction of the positive-row physical
carrier.  This module proves directly, at every representation cutoff, that
the normalized reflected kernel restricted to that component remains a
finite weighted Gram matrix.  Its quadratic form is therefore nonnegative.

This is the lower spectral edge needed by the finite strict-gap route: once a
connected-support Poincare estimate proves an upper contraction, reflection
positivity turns it into the required absolute form bound.  No upper gap,
uniform cutoff estimate, thermodynamic/continuum limit, or Clay conclusion is
asserted here.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorBlockDecomposition
import YMGap.Continuum.FiniteWeightedGramSOS

namespace YMGap.Continuum.BF4PhysicalFiniteVacuumSectorGramPositivity

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorBlockDecomposition
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4SU2FixedMagneticPositiveKernelConvergence
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPartition
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

local macro "q_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Int.add_mul, Int.mul_add, Int.one_mul,
               Int.mul_one, Int.zero_mul, Int.mul_zero, Int.add_zero,
               Int.zero_add];
             try ac_rfl))

/-! ## 1. The normalized sector kernel is a literal weighted Gram -/

/-- The positive reciprocal of the finite physical partition. -/
def centralPhysicalFiniteVacuumSectorPartitionReciprocal
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat) : Q' :=
  Q'.recipPos
    (slabParametricKPhysicalPartition w cutoff (centralExtent half))
    (slabParametricKPhysicalPartition_pos
      hw cutoff (centralExtent half))

/-- Absorb the common partition reciprocal into every boundary-channel
weight. -/
def centralPhysicalFiniteVacuumSectorGramWeight
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat)
    (boundary : EdgeLabelling) : Q' :=
  centralBoundaryWeight w cutoff half boundary *
    centralPhysicalFiniteVacuumSectorPartitionReciprocal
      w hw cutoff half

/-- The physical half-amplitude read on the actual finite index carrier. -/
def centralPhysicalFiniteVacuumSectorGramAmplitude
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat)
    (index : Nat) (boundary : EdgeLabelling) : Q' :=
  centralHalfAmplitude w cutoff half
    (centralPhysicalFiniteStateAt w hw cutoff half index) boundary

theorem centralPhysicalFiniteVacuumSectorGramWeight_nonnegative
    {w : Q'} {hw : (0 : Q') ≤ w} {cutoff half : Nat}
    (boundary : EdgeLabelling)
    (hboundary : boundary ∈ centralBoundaryChannels cutoff half) :
    (0 : Q') ≤
      centralPhysicalFiniteVacuumSectorGramWeight
        w hw cutoff half boundary := by
  unfold centralPhysicalFiniteVacuumSectorGramWeight
    centralPhysicalFiniteVacuumSectorPartitionReciprocal
  exact Q'.mul_nonneg _ _
    (centralBoundaryWeight_nonnegative_on hw boundary hboundary)
    (Q'.le_of_lt
      (Q'.recipPos_pos _
        (slabParametricKPhysicalPartition_pos
          hw cutoff (centralExtent half))))

/-- Every kernel entry whose two indices lie in the canonical vacuum sector
is exactly the corresponding entry of the partition-scaled physical Gram. -/
theorem centralPhysicalFiniteKernel_eqv_vacuumSectorWeightedGram
    {w : Q'} {hw : (0 : Q') ≤ w} {cutoff half left right : Nat}
    (hleft : left ∈
      centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
    (hright : right ∈
      centralPhysicalFiniteVacuumSectorIndices w hw cutoff half) :
    centralPhysicalFiniteKernel w hw cutoff half left right ≈
      weightedGram
        (centralBoundaryChannels cutoff half)
        (centralPhysicalFiniteVacuumSectorGramWeight
          w hw cutoff half)
        (centralPhysicalFiniteVacuumSectorGramAmplitude
          w hw cutoff half)
        left right := by
  have hleftCarrier := centralPhysicalFiniteStateAt_mem_positive
    w hw cutoff half
    (centralPhysicalFiniteVacuumSectorIndex_lt
      w hw cutoff half hleft)
  have hrightCarrier := centralPhysicalFiniteStateAt_mem_positive
    w hw cutoff half
    (centralPhysicalFiniteVacuumSectorIndex_lt
      w hw cutoff half hright)
  have hleftHalf := (mem_centralPositiveHalfStates_iff.mp hleftCarrier).1
  have hrightHalf := (mem_centralPositiveHalfStates_iff.mp hrightCarrier).1
  let reciprocal :=
    centralPhysicalFiniteVacuumSectorPartitionReciprocal
      w hw cutoff half
  have hraw := centralPhysicalReflectedKernel_eq_weightedGram
    w hleftHalf hrightHalf
  unfold centralPhysicalFiniteKernel
    centralNormalizedPhysicalReflectedKernel Q'.divPos
  refine Q'.eqv_trans _
    (weightedGram
        (centralBoundaryChannels cutoff half)
        (centralBoundaryWeight w cutoff half)
        (centralPhysicalFiniteVacuumSectorGramAmplitude
          w hw cutoff half)
        left right * reciprocal) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ reciprocal hraw
  refine Q'.eqv_trans _
    (listQSum
      (fun boundary =>
        (centralBoundaryWeight w cutoff half boundary *
            (centralPhysicalFiniteVacuumSectorGramAmplitude
              w hw cutoff half left boundary *
              centralPhysicalFiniteVacuumSectorGramAmplitude
                w hw cutoff half right boundary)) * reciprocal)
      (centralBoundaryChannels cutoff half)) _ ?_ ?_
  · exact Q'.eqv_symm
      (listQSum_mul_right
        (fun boundary =>
          centralBoundaryWeight w cutoff half boundary *
            (centralPhysicalFiniteVacuumSectorGramAmplitude
              w hw cutoff half left boundary *
              centralPhysicalFiniteVacuumSectorGramAmplitude
                w hw cutoff half right boundary))
        reciprocal (centralBoundaryChannels cutoff half))
  unfold weightedGram centralPhysicalFiniteVacuumSectorGramWeight reciprocal
    centralPhysicalFiniteVacuumSectorPartitionReciprocal
  apply listQSum_congr
  intro boundary
  q_ring

/-! ## 2. The sector quadratic is a manifest sum of squares -/

theorem centralPhysicalFiniteVacuumSectorMatrixQuadratic_eqv_weightedGram
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat)
    (coefficient : Nat → Q') :
    centralPhysicalFiniteVacuumSectorMatrixQuadratic
        w hw cutoff half coefficient ≈
      weightedGramQuadratic
        (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
        (centralBoundaryChannels cutoff half)
        (centralPhysicalFiniteVacuumSectorGramWeight
          w hw cutoff half)
        (centralPhysicalFiniteVacuumSectorGramAmplitude
          w hw cutoff half)
        coefficient := by
  unfold centralPhysicalFiniteVacuumSectorMatrixQuadratic
    finiteJointQuadratic weightedGramQuadratic
  apply listQSum_congr_on
  intro left hleft
  apply listQSum_congr_on
  intro right hright
  exact Q'.mul_eqv_congr_left
    (coefficient left * coefficient right) _ _
    (centralPhysicalFiniteKernel_eqv_vacuumSectorWeightedGram
      hleft hright)

/-- Reflection positivity survives restriction to the canonical vacuum
component at every finite representation cutoff. -/
theorem centralPhysicalFiniteVacuumSectorMatrixQuadratic_nonnegative
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat)
    (coefficient : Nat → Q') :
    (0 : Q') ≤
      centralPhysicalFiniteVacuumSectorMatrixQuadratic
        w hw cutoff half coefficient := by
  have hgram : (0 : Q') ≤
      weightedGramQuadratic
        (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
        (centralBoundaryChannels cutoff half)
        (centralPhysicalFiniteVacuumSectorGramWeight
          w hw cutoff half)
        (centralPhysicalFiniteVacuumSectorGramAmplitude
          w hw cutoff half)
        coefficient :=
    weightedGramQuadratic_nonnegative _ _ _ _ _
      (centralPhysicalFiniteVacuumSectorGramWeight_nonnegative)
  exact Q'.le_trans' _ _ _ hgram
    (Q'.ge_of_eqv
      (centralPhysicalFiniteVacuumSectorMatrixQuadratic_eqv_weightedGram
        w hw cutoff half coefficient))

end YMGap.Continuum.BF4PhysicalFiniteVacuumSectorGramPositivity

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSectorGramPositivity.centralPhysicalFiniteVacuumSectorGramWeight_nonnegative
#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSectorGramPositivity.centralPhysicalFiniteKernel_eqv_vacuumSectorWeightedGram
#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSectorGramPositivity.centralPhysicalFiniteVacuumSectorMatrixQuadratic_eqv_weightedGram
#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSectorGramPositivity.centralPhysicalFiniteVacuumSectorMatrixQuadratic_nonnegative
