/-
# Factor the BF4 physical-mass state load into weight and resistance

The physical-mass entropy bound leaves one pointwise quantity:

    stationaryWeight(state) * canonicalPathResistance(state, vacuum).

This module separates its two analytic mechanisms without weakening the
literal BF4 target.  If stationary weight decays like `W * s^mass` and the
actual canonical-path resistance grows like `R * t^mass`, then the state load
decays like `(W*R) * (s*t)^mass`.  Combined with the proved binary entropy
base, the exact summability condition is `2 * (s*t) < 1`.

No weight decay or resistance-growth estimate is inhabited here.  In
particular, `weight <= 1` alone cannot close the required ratio.  No continuum
or Clay conclusion is asserted.  No `Classical`, choice, `native_decide`,
`sorry`, new axiom, or noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceMassShellEntropy

namespace YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceMassShellStateLoadFactorization

set_option maxRecDepth 1000000
set_option maxHeartbeats 500000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorResistanceCauchy
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualFrontier
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceFlow
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceLengthShellFactorization
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceMassShell
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceMassShellEntropy
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceMoment
open YMGap.Continuum.BF4PhysicalSpinCubeRayCofinalReturnFloor
open YMGap.Continuum.BF4PhysicalVacuumSectorMassExactAdaptiveRootResistanceSimpleRouting
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Totalized literal canonical-path resistance -/

/-- Resistance of the actual canonical simple path from an off-ray state to
the vacuum, totalized by zero away from the off-ray carrier. -/
def centralLowerExcitedSpinCubeOffRayRootCanonicalPathResistance
    (w : Q') (hw : (0 : Q') ≤ w) (K state : Nat) : Q' :=
  if hstate : state ∈ centralLowerExcitedSpinCubeOffRayIndices w hw K then
    PositiveKernelChainIn.resistance
      (centralLowerExcitedSpinCubeOffRayRootPositivePath state hstate)
  else 0

theorem centralLowerExcitedSpinCubeOffRayRootCanonicalPathResistance_nonnegative
    (w : Q') (hw : (0 : Q') ≤ w) (K state : Nat) :
    (0 : Q') ≤
      centralLowerExcitedSpinCubeOffRayRootCanonicalPathResistance
        w hw K state := by
  unfold centralLowerExcitedSpinCubeOffRayRootCanonicalPathResistance
  by_cases hstate : state ∈ centralLowerExcitedSpinCubeOffRayIndices w hw K
  · rw [dif_pos hstate]
    exact PositiveKernelChainIn.resistance_nonnegative
      (centralLowerExcitedSpinCubeOffRayRootPositivePath state hstate)
  · rw [dif_neg hstate]
    exact Q'.le_refl' 0

theorem centralLowerExcitedSpinCubeOffRayRootStateResistanceLoad_eqv_weight_mul_pathResistance
    (w : Q') (hw : (0 : Q') ≤ w) (K state : Nat) :
    centralLowerExcitedSpinCubeOffRayRootStateResistanceLoad w hw K state ≈
      centralPhysicalFiniteWeight w hw K 0 state *
        centralLowerExcitedSpinCubeOffRayRootCanonicalPathResistance
          w hw K state := by
  unfold centralLowerExcitedSpinCubeOffRayRootStateResistanceLoad
    centralLowerExcitedSpinCubeOffRayRootCanonicalPathResistance
  by_cases hstate : state ∈ centralLowerExcitedSpinCubeOffRayIndices w hw K
  · rw [dif_pos hstate, dif_pos hstate]
    exact Q'.eqv_refl _
  · rw [dif_neg hstate, dif_neg hstate]
    exact Q'.eqv_symm (Q'.mul_zero_eqv _)

/-! ## 2. Independent decay/growth input and exact compiler -/

/-- A factorized version of the sole remaining physical-mass state-load
input.  The first field is stationary-probability decay; the second permits
controlled growth of the resistance of the actual canonical route. -/
structure FixedNomeCofinalSpinCubeOffRayRootResistancePhysicalMassWeightPathFactorizedDecay
    {w : Q'} (hw : (0 : Q') < w) : Type 1 where
  start : Nat
  stationaryAmplitude : Q'
  stationaryRatio : Q'
  resistanceAmplitude : Q'
  resistanceRatio : Q'
  budget : Q'
  stationaryAmplitude_nonnegative : (0 : Q') ≤ stationaryAmplitude
  stationaryRatio_nonnegative : (0 : Q') ≤ stationaryRatio
  resistanceAmplitude_nonnegative : (0 : Q') ≤ resistanceAmplitude
  resistanceRatio_nonnegative : (0 : Q') ≤ resistanceRatio
  combinedRatio_lt_one :
    physicalMassShellEntropyBase *
        (stationaryRatio * resistanceRatio) < (1 : Q')
  budget_nonnegative : (0 : Q') ≤ budget
  geometric_step :
    physicalMassShellEntropyAmplitude *
          (stationaryAmplitude * resistanceAmplitude) +
        (physicalMassShellEntropyBase *
            (stationaryRatio * resistanceRatio)) * budget ≤ budget
  stationaryWeight_le : ∀ K, start ≤ K →
    ∀ source target (shell state : Nat),
      shell < centralLowerExcitedSpinCubeOffRayRootPhysicalMassShellCount
        w (Q'.le_of_lt hw) K →
      state ∈ centralLowerExcitedSpinCubeOffRayRootEdgePhysicalMassShellStates
        w (Q'.le_of_lt hw) K source target shell →
      centralPhysicalFiniteWeight w (Q'.le_of_lt hw) K 0 state ≤
        stationaryAmplitude * stationaryRatio ^ shell
  canonicalPathResistance_le : ∀ K, start ≤ K →
    ∀ source target (shell state : Nat),
      shell < centralLowerExcitedSpinCubeOffRayRootPhysicalMassShellCount
        w (Q'.le_of_lt hw) K →
      state ∈ centralLowerExcitedSpinCubeOffRayRootEdgePhysicalMassShellStates
        w (Q'.le_of_lt hw) K source target shell →
      centralLowerExcitedSpinCubeOffRayRootCanonicalPathResistance
          w (Q'.le_of_lt hw) K state ≤
        resistanceAmplitude * resistanceRatio ^ shell

namespace FixedNomeCofinalSpinCubeOffRayRootResistancePhysicalMassWeightPathFactorizedDecay

def toPhysicalMassStateLoadDecay
    {w : Q'} {hw : (0 : Q') < w}
    (factorized :
      FixedNomeCofinalSpinCubeOffRayRootResistancePhysicalMassWeightPathFactorizedDecay
        hw) :
    FixedNomeCofinalSpinCubeOffRayRootResistancePhysicalMassStateLoadDecay
      hw where
  start := factorized.start
  loadAmplitude :=
    factorized.stationaryAmplitude * factorized.resistanceAmplitude
  loadRatio := factorized.stationaryRatio * factorized.resistanceRatio
  budget := factorized.budget
  loadAmplitude_nonnegative := Q'.mul_nonneg _ _
    factorized.stationaryAmplitude_nonnegative
    factorized.resistanceAmplitude_nonnegative
  loadRatio_nonnegative := Q'.mul_nonneg _ _
    factorized.stationaryRatio_nonnegative
    factorized.resistanceRatio_nonnegative
  combinedRatio_lt_one := factorized.combinedRatio_lt_one
  budget_nonnegative := factorized.budget_nonnegative
  geometric_step := factorized.geometric_step
  stateLoad_le := by
    intro K hK source target shell state hshell hstate
    let weight := centralPhysicalFiniteWeight w (Q'.le_of_lt hw) K 0 state
    let pathResistance :=
      centralLowerExcitedSpinCubeOffRayRootCanonicalPathResistance
        w (Q'.le_of_lt hw) K state
    let weightBound :=
      factorized.stationaryAmplitude * factorized.stationaryRatio ^ shell
    let resistanceBound :=
      factorized.resistanceAmplitude * factorized.resistanceRatio ^ shell
    have hweight0 : (0 : Q') ≤ weight := by
      exact centralPhysicalRowMarginal_nonnegative
        (Q'.le_of_lt hw) K 0
        (centralPhysicalFiniteStateAt w (Q'.le_of_lt hw) K 0 state)
    have hresistance0 : (0 : Q') ≤ pathResistance := by
      exact
        centralLowerExcitedSpinCubeOffRayRootCanonicalPathResistance_nonnegative
          w (Q'.le_of_lt hw) K state
    have hweightBound0 : (0 : Q') ≤ weightBound := by
      exact Q'.mul_nonneg _ _ factorized.stationaryAmplitude_nonnegative
        (Q'.pow_nonneg factorized.stationaryRatio
          factorized.stationaryRatio_nonnegative shell)
    have hresistanceBound0 : (0 : Q') ≤ resistanceBound := by
      exact Q'.mul_nonneg _ _ factorized.resistanceAmplitude_nonnegative
        (Q'.pow_nonneg factorized.resistanceRatio
          factorized.resistanceRatio_nonnegative shell)
    have hweight : weight ≤ weightBound :=
      factorized.stationaryWeight_le K hK source target shell state
        hshell hstate
    have hresistance : pathResistance ≤ resistanceBound :=
      factorized.canonicalPathResistance_le K hK source target shell state
        hshell hstate
    have hproduct : weight * pathResistance ≤
        weightBound * resistanceBound := by
      exact Q'.le_trans' _ (weightBound * pathResistance) _
        (Q'.mul_le_mul_of_nonneg_right
          weight weightBound pathResistance hweight hresistance0)
        (Q'.mul_le_mul_of_nonneg_left
          pathResistance resistanceBound weightBound
          hresistance hweightBound0)
    have hfactor : weightBound * resistanceBound ≈
        (factorized.stationaryAmplitude *
            factorized.resistanceAmplitude) *
          (factorized.stationaryRatio *
            factorized.resistanceRatio) ^ shell := by
      unfold weightBound resistanceBound
      calc
        (factorized.stationaryAmplitude *
              factorized.stationaryRatio ^ shell) *
            (factorized.resistanceAmplitude *
              factorized.resistanceRatio ^ shell) ≈
          factorized.stationaryAmplitude *
            (factorized.stationaryRatio ^ shell *
              (factorized.resistanceAmplitude *
                factorized.resistanceRatio ^ shell)) :=
          Q'.mul_assoc_eqv _ _ _
        _ ≈ factorized.stationaryAmplitude *
            ((factorized.stationaryRatio ^ shell *
                factorized.resistanceAmplitude) *
              factorized.resistanceRatio ^ shell) :=
          Q'.mul_eqv_congr_left _ _ _
            (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
        _ ≈ factorized.stationaryAmplitude *
            ((factorized.resistanceAmplitude *
                factorized.stationaryRatio ^ shell) *
              factorized.resistanceRatio ^ shell) :=
          Q'.mul_eqv_congr_left _ _ _
            (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv _ _))
        _ ≈ factorized.stationaryAmplitude *
            (factorized.resistanceAmplitude *
              (factorized.stationaryRatio ^ shell *
                factorized.resistanceRatio ^ shell)) :=
          Q'.mul_eqv_congr_left _ _ _ (Q'.mul_assoc_eqv _ _ _)
        _ ≈ (factorized.stationaryAmplitude *
              factorized.resistanceAmplitude) *
            (factorized.stationaryRatio ^ shell *
              factorized.resistanceRatio ^ shell) :=
          Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)
        _ ≈ (factorized.stationaryAmplitude *
              factorized.resistanceAmplitude) *
            (factorized.stationaryRatio *
              factorized.resistanceRatio) ^ shell :=
          Q'.mul_eqv_congr_left _ _ _
            (Q'.eqv_symm
              (mul_pow_eqv factorized.stationaryRatio
                factorized.resistanceRatio shell))
    change centralLowerExcitedSpinCubeOffRayRootStateResistanceLoad
        w (Q'.le_of_lt hw) K state ≤
      (factorized.stationaryAmplitude * factorized.resistanceAmplitude) *
        (factorized.stationaryRatio * factorized.resistanceRatio) ^ shell
    exact Q'.le_trans' _ (weight * pathResistance) _
      (Q'.le_of_eqv
        (centralLowerExcitedSpinCubeOffRayRootStateResistanceLoad_eqv_weight_mul_pathResistance
          w (Q'.le_of_lt hw) K state))
      (Q'.le_trans' _ _ _ hproduct (Q'.le_of_eqv hfactor))

def toResistanceCongestionBound
    {w : Q'} {hw : (0 : Q') < w}
    (factorized :
      FixedNomeCofinalSpinCubeOffRayRootResistancePhysicalMassWeightPathFactorizedDecay
        hw) :
    FixedNomeCofinalSpinCubeOffRayRootResistanceCongestionBound hw :=
  factorized.toPhysicalMassStateLoadDecay.toResistanceCongestionBound

def toSimpleRootResistanceCongestionBound
    {w : Q'} {hw : (0 : Q') < w}
    (factorized :
      FixedNomeCofinalSpinCubeOffRayRootResistancePhysicalMassWeightPathFactorizedDecay
        hw)
    (ray : FixedNomeCofinalSpinCubeRayCapacity hw) :
    FixedNomeCofinalVacuumSectorMassExactSimpleRootResistanceCongestionBound
      hw :=
  factorized.toPhysicalMassStateLoadDecay.toSimpleRootResistanceCongestionBound
    ray

end FixedNomeCofinalSpinCubeOffRayRootResistancePhysicalMassWeightPathFactorizedDecay

end YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceMassShellStateLoadFactorization

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceMassShellStateLoadFactorization.centralLowerExcitedSpinCubeOffRayRootCanonicalPathResistance_nonnegative
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceMassShellStateLoadFactorization.centralLowerExcitedSpinCubeOffRayRootStateResistanceLoad_eqv_weight_mul_pathResistance
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceMassShellStateLoadFactorization.FixedNomeCofinalSpinCubeOffRayRootResistancePhysicalMassWeightPathFactorizedDecay.toPhysicalMassStateLoadDecay
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceMassShellStateLoadFactorization.FixedNomeCofinalSpinCubeOffRayRootResistancePhysicalMassWeightPathFactorizedDecay.toResistanceCongestionBound
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayRootResistanceMassShellStateLoadFactorization.FixedNomeCofinalSpinCubeOffRayRootResistancePhysicalMassWeightPathFactorizedDecay.toSimpleRootResistanceCongestionBound
