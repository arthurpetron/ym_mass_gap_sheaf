/-
# Explicit raw-row envelope for the matched spin-cube ray mass

Each displayed spin-cube stationary weight is its literal positive raw-row
mass times the common physical partition reciprocal.  The existing raw-row
theorem bounds that numerator by the sixth power of the spin heat coefficient
times an explicit nome-dependent residual-carrier ceiling.  Summing over all
admitted excited spins gives a fully explicit normalized envelope for the ray
mass.

On the matched same-action trajectory, tail zero of this envelope constructs
tail zero of the ray mass and therefore rules out every common assigned-ratio
ceiling.  The envelope tail estimate itself is not proved here.  No congestion
bound, finite gap, physical normalization, continuum theory, or Clay
conclusion is asserted.

No `Classical`, choice, `native_decide`, `sorry`, new axiom, or noncomputable
declaration is used.
-/

import YMGap.Continuum.BF4CentralSpinCubeRawRowCeiling
import YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedRayTailZeroNoGo

namespace YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedRayRawEnvelope

set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.BF4CentralLowerSpinCubePositiveRay
open YMGap.Continuum.BF4CentralSpinCubeRawRowCeiling
open YMGap.Continuum.BF4CentralSpinCubeResidualCarrierSumBound
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4MatchedPhysicalFarautTrajectory
open YMGap.Continuum.BF4MatchedPhysicalFiniteHeatWindow
open YMGap.Continuum.BF4PhysicalBoundaryCutoffOneCanonicalVacuumSectorStationaryPosterior
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorGramPositivity
open YMGap.Continuum.BF4PhysicalSpinCubeRayFlowCapacity
open YMGap.Continuum.BF4PhysicalSpinCubeRawReturnRatio
open YMGap.Continuum.BF4PhysicalSpinCubeVacuumSpokes
open YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedCofinalGate
open YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedRayTailZeroNoGo
open YMGap.Continuum.BF4ReflectedAllSpinAFRowRelative
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram

local infix:50 " ≈ " => Q'.eqv

private theorem listQSum_le_termwise_local {A : Type}
    (left right : A → Q') : ∀ items : List A,
      (∀ item, item ∈ items → left item ≤ right item) →
      listQSum left items ≤ listQSum right items
  | [], _ => Q'.le_refl' 0
  | head :: tail, hle =>
      Q'.add_le_add
        (hle head List.mem_cons_self)
        (listQSum_le_termwise_local left right tail
          (fun item hitem =>
            hle item (List.mem_cons_of_mem head hitem)))

/-! ## 1. One normalized spin-cube weight -/

/-- The stationary weight of one admitted spin cube is bounded by its exact
six-face heat activity, the explicit raw residual ceiling, and the common
physical partition reciprocal. -/
theorem centralPhysicalFiniteWeight_spinCubeIndex_le_rawEnvelope
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {K spin : Nat} (hspin : spin ≤ K) :
    centralPhysicalFiniteWeight w (Q'.le_of_lt hw0) K 0
        (centralLowerSpinCubeIndex w (Q'.le_of_lt hw0) K spin) ≤
      (((coeffW w spin) ^ 6) *
          explicitFixedNomeCentralSpinCubeResidualCarrierCeiling w) *
        centralPhysicalFiniteVacuumSectorPartitionReciprocal
          w (Q'.le_of_lt hw0) K 0 := by
  have hstate := centralPhysicalFiniteStateAt_spinCubeIndex_eq hw0 hspin
  have hrow :
      centralPhysicalRowMarginal w (Q'.le_of_lt hw0) K 0
          (centralLowerSpinCubeState spin) ≈
        centralPhysicalPositiveRawRowMass
            w (Q'.le_of_lt hw0) K 0
            (centralLowerSpinCubeState spin) *
          centralPhysicalFiniteVacuumSectorPartitionReciprocal
            w (Q'.le_of_lt hw0) K 0 := by
    simpa only [centralPhysicalPositiveRawRowMass] using
      (centralPhysicalRowMarginal_eqv_positiveRawRowMass_mul_partitionReciprocal
        (w := w) (hw := Q'.le_of_lt hw0) (K := K) (half := 0)
        (source := centralLowerSpinCubeState spin)
        (centralLowerSpinCubeState_mem_centralHalfStates hspin))
  have hraw :=
    centralLowerSpinCubePositiveRawRow_le_activity_mul_explicitFixedNomeCeiling
      hw0 hw1 hspin
  have hreciprocal : (0 : Q') ≤
      centralPhysicalFiniteVacuumSectorPartitionReciprocal
        w (Q'.le_of_lt hw0) K 0 :=
    Q'.le_of_lt (Q'.recipPos_pos _ _)
  have hscaled := Q'.mul_le_mul_of_nonneg_right _ _ _ hraw hreciprocal
  unfold centralPhysicalFiniteWeight
  rw [hstate]
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hrow) hscaled

/-! ## 2. The complete normalized ray envelope -/

/-- Explicit scalar envelope: the finite sixth-power heat-activity sum times
the raw residual ceiling and the physical partition reciprocal. -/
def centralLowerExcitedSpinCubeRawEnvelope
    (w : Q') (hw : (0 : Q') ≤ w) (K : Nat) : Q' :=
  (listQSum
      (fun offset => (coeffW w (offset + 1)) ^ 6)
      (List.range K) *
    explicitFixedNomeCentralSpinCubeResidualCarrierCeiling w) *
  centralPhysicalFiniteVacuumSectorPartitionReciprocal w hw K 0

/-- The exact normalized excited spin-cube ray mass lies below the explicit
raw-row/partition envelope at every positive finite cutoff. -/
theorem centralLowerExcitedSpinCubeRayMass_le_rawEnvelope
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K : Nat) :
    centralLowerExcitedSpinCubeRayMass w (Q'.le_of_lt hw0) K ≤
      centralLowerExcitedSpinCubeRawEnvelope
        w (Q'.le_of_lt hw0) K := by
  let weight := fun offset =>
    centralPhysicalFiniteWeight w (Q'.le_of_lt hw0) K 0
      (centralLowerExcitedSpinCubeIndex
        w (Q'.le_of_lt hw0) K offset)
  let activity := fun offset => (coeffW w (offset + 1)) ^ 6
  let ceiling := explicitFixedNomeCentralSpinCubeResidualCarrierCeiling w
  let reciprocal := centralPhysicalFiniteVacuumSectorPartitionReciprocal
    w (Q'.le_of_lt hw0) K 0
  have hsum : listQSum weight (List.range K) ≤
      listQSum
        (fun offset => (activity offset * ceiling) * reciprocal)
        (List.range K) := by
    apply listQSum_le_termwise_local
    intro offset hoffsetMem
    have hoffset := List.mem_range.mp hoffsetMem
    exact centralPhysicalFiniteWeight_spinCubeIndex_le_rawEnvelope
      hw0 hw1 (by omega)
  have hfactor :
      listQSum
          (fun offset => (activity offset * ceiling) * reciprocal)
          (List.range K) ≈
        (listQSum activity (List.range K) * ceiling) * reciprocal := by
    refine Q'.eqv_trans _
      (listQSum (fun offset => activity offset * ceiling) (List.range K) *
        reciprocal) _
      (listQSum_mul_right
        (fun offset => activity offset * ceiling) reciprocal
        (List.range K)) ?_
    exact Q'.mul_eqv_congr_right _ _ reciprocal
      (listQSum_mul_right activity ceiling (List.range K))
  exact Q'.le_trans' _ (listQSum weight (List.range K)) _
    (Q'.le_of_eqv
      (centralLowerExcitedSpinCubeRayMass_eqv_offset_sum
        w (Q'.le_of_lt hw0) K))
    (Q'.le_trans' _ _ _ hsum
      (Q'.le_of_eqv (by
        unfold centralLowerExcitedSpinCubeRawEnvelope
        exact hfactor)))

/-! ## 3. Matched same-action specialization -/

def matchedExcitedSpinCubeRawEnvelope
    (family : MatchedBlockFamily)
    (coupling : Nat → Q') (scale : Nat) : Q' :=
  centralLowerExcitedSpinCubeRawEnvelope
    (matchedAllSpinWeight family coupling scale)
    (matchedAllSpinWeight_nonnegative family coupling scale)
    (matchedAllSpinCutoff family coupling scale)

theorem matchedRayMass_le_rawEnvelope
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    (bridge :
      MatchedDyadicSameActionAFBridge
        family law spacing coupling)
    (scale : Nat) :
    centralLowerExcitedSpinCubeRayMass
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinWeight_nonnegative family coupling scale)
        (matchedAllSpinCutoff family coupling scale) ≤
      matchedExcitedSpinCubeRawEnvelope family coupling scale := by
  exact centralLowerExcitedSpinCubeRayMass_le_rawEnvelope
    (matchedAllSpinWeight_pos family coupling scale)
    (matchedPhysicalWeight_lt_one bridge scale)
    (matchedAllSpinCutoff family coupling scale)

/-- Located tail-zero data for the explicit raw-row/partition envelope. -/
structure MatchedDyadicExcitedSpinCubeRawEnvelopeTailZero
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    (_bridge :
      MatchedDyadicSameActionAFBridge
        family law spacing coupling) : Type where
  rate : Q' → Nat
  envelope_le : ∀ epsilon, (0 : Q') < epsilon →
    ∀ scale, rate epsilon ≤ scale →
      matchedExcitedSpinCubeRawEnvelope family coupling scale ≤ epsilon

def MatchedDyadicExcitedSpinCubeRawEnvelopeTailZero.toRayMassTailZero
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {bridge :
      MatchedDyadicSameActionAFBridge
        family law spacing coupling}
    (tail : MatchedDyadicExcitedSpinCubeRawEnvelopeTailZero bridge) :
    MatchedDyadicExcitedSpinCubeRayMassTailZero bridge where
  rate := tail.rate
  rayMass_le := by
    intro epsilon hepsilon scale hscale
    exact Q'.le_trans' _ _ _
      (matchedRayMass_le_rawEnvelope bridge scale)
      (tail.envelope_le epsilon hepsilon scale hscale)

/-- Tail zero of the explicit raw envelope is already sufficient to exclude
the common matched assigned-ratio producer. -/
theorem rawEnvelopeTailZero_excludes_cofinalAssignedRatio
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {bridge :
      MatchedDyadicSameActionAFBridge
        family law spacing coupling}
    (tail : MatchedDyadicExcitedSpinCubeRawEnvelopeTailZero bridge) :
    ¬ Nonempty
      (MatchedDyadicCofinalPositiveCentralFaceAssignedStationaryRatio
        bridge) :=
  tailZero_excludes_cofinalAssignedRatio tail.toRayMassTailZero

end YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedRayRawEnvelope

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedRayRawEnvelope.centralPhysicalFiniteWeight_spinCubeIndex_le_rawEnvelope
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedRayRawEnvelope.centralLowerExcitedSpinCubeRayMass_le_rawEnvelope
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedRayRawEnvelope.matchedRayMass_le_rawEnvelope
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedRayRawEnvelope.MatchedDyadicExcitedSpinCubeRawEnvelopeTailZero.toRayMassTailZero
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedRayRawEnvelope.rawEnvelopeTailZero_excludes_cofinalAssignedRatio
