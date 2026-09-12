/-
# A positive-norm centered observable in the actual reflected completion

Center the existing single-face spin-two cylinder by the previously
constructed moving rational root correction. At every stage its literal
observable is delta(probe) + c delta(root). A physical boundary channel
annihilates the root but detects the probe, uniformly in c. Its positive
heat weight, times the fixed-anchor normalization floor, survives the
existing reflected pairing limit.

Thus this SAME centered vector is nonzero in the reflected quotient, and
its connected conditional covariance at the first shifted index is positive.
No strict contraction, nonidentity transfer, geometric-time identification,
continuum limit or Clay conclusion is asserted.
-/

import YMGap.Continuum.BF4PhysicalCubeSeparatedChannel
import YMGap.Continuum.BF4PhysicalCubeSectorCenteredRealization
import YMGap.Continuum.BF4PhysicalCubeSectorDensePreimage
import YMGap.Continuum.RCStrictPositivity

namespace YMGap.Continuum.BF4PhysicalCubeCenteredPositiveNorm

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCubeGNSData
open YMGap.Continuum.BF4PhysicalCubeNormalizedKernelLimit
open YMGap.Continuum.BF4PhysicalCubeObservableRealization
open YMGap.Continuum.BF4PhysicalCubeReflectedCompletion
open YMGap.Continuum.BF4PhysicalCubeSectorComparison
open YMGap.Continuum.BF4PhysicalCubeSectorDensePreimage
open YMGap.Continuum.BF4PhysicalCubeSectorVacuumNorm
open YMGap.Continuum.BF4PhysicalCubeSectorCenteredRealization
open YMGap.Continuum.BF4PhysicalCubeSeparatedChannel
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalCutoffLinearGNSForm
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletion
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorLinearRealization
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorHeadCorrectionCauchy
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorMovingCenteredCompletion
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorMovingCenteredVacuumPairing
open YMGap.Continuum.RationalKernelSpan
open YMGap.Continuum.RCStrictPositivity
open YMGap.Continuum.ScaledGNSCompletion
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv
local notation "D" => cubeGNSData anchorCoupling (by decide)
local notation "M" => centralPhysicalVacuumSectorCylinderSquaredSeminorm
  (w := anchorCoupling) (by decide) (by decide) 0

def probePresentation : SectorPresentation := spanPresentation (basis probeState)

/-- Reuse the physical centering modulus and coefficient sequence as data. -/
def probeSourceCauchy : (M).Cauchy :=
  centralPhysicalVacuumSectorMovingCenteredCauchy (w := anchorCoupling)
    (by decide) (by decide) probePresentation.base 0 probePresentation.coefficient

def probeReflectedCauchy : cubeReflectedSeminorm.Cauchy := sectorCauchyToReflected probeSourceCauchy

def centeredProbe : CubeSectorVacuumComplement :=
  centeredCubeVector probePresentation.base probePresentation.coefficient

def probeCorrection (stage : Nat) : Q' :=
  -centralPhysicalFinitePulledVacuumSectorHeadCorrectionApprox
    (w := anchorCoupling) (by decide) probePresentation.base 0 probePresentation.coefficient stage

def reflectedProbeFloor : Q' := Q'.mkPos 64 65 (by decide) * channelFloor anchorCoupling

theorem reflectedProbeFloor_pos : (0 : Q') < reflectedProbeFloor :=
  Q'.mul_pos (by decide) (channelFloor_pos (w := anchorCoupling) (by decide))

private theorem dense_pairing (left right : CubeSpan) :
    cubeReflectedInner (cubeReflectedEmbed left) (cubeReflectedEmbed right) =
      Quotient.mk CReal.crealSetoid (normalizedFormLimit (w := anchorCoupling)
        (by decide) (by decide) left right) :=
  scaledCompletedInner_embed D anchorNormalization left right

private theorem moving_observable (p : SectorPresentation)
    (hraw : CentralPhysicalLinearObservable.Equivalent p.toLinearObservable (cubeObservable (basis probeState)))
    (stage : Nat) :
    CentralPhysicalLinearObservable.Equivalent
      (cubeObservable (presentationToCube (centralPhysicalVacuumSectorMovingCenteredPresentation
        (w := anchorCoupling) (by decide) p.base 0 p.coefficient stage)))
      (cubeObservable (rootCorrectedSpan (-centralPhysicalFinitePulledVacuumSectorHeadCorrectionApprox
        (w := anchorCoupling) (by decide) p.base 0 p.coefficient stage))) := by
  intro state
  rw [presentationToCube_observable]
  have h := centralPhysicalVacuumSectorMovingCentered_value_equiv_expansion
    (w := anchorCoupling) (by decide) p.base 0 p.coefficient stage state
  dsimp only at h
  rw [centralPhysicalFiniteStateAt_zero_eq_vacuum] at h
  refine Q'.eqv_trans _ _ _ h ?_
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _
    (hraw state)) ?_
  change (1 * (centralPhysicalStateCylinderUnitObservable 0 probeState.val).value state + 0) +
      (-centralPhysicalFinitePulledVacuumSectorHeadCorrectionApprox
        (w := anchorCoupling) (by decide) p.base 0 p.coefficient stage) *
        (centralPhysicalStateCylinderUnitObservable 0 rootState.val).value state ≈
    1 * (centralPhysicalStateCylinderUnitObservable 0 probeState.val).value state +
      ((-centralPhysicalFinitePulledVacuumSectorHeadCorrectionApprox
        (w := anchorCoupling) (by decide) p.base 0 p.coefficient stage) *
        (centralPhysicalStateCylinderUnitObservable 0 rootState.val).value state + 0)
  rw [Q'.add_zero', Q'.add_zero']
  exact Q'.eqv_refl _

private theorem centered_stage_observable (p : SectorPresentation)
    (hraw : CentralPhysicalLinearObservable.Equivalent p.toLinearObservable (cubeObservable (basis probeState)))
    (stage : Nat) :
    CentralPhysicalLinearObservable.Equivalent
      (cubeObservable ((sectorCauchyToReflected
        (centralPhysicalVacuumSectorMovingCenteredCauchy (w := anchorCoupling)
          (by decide) (by decide) p.base 0 p.coefficient)).seq stage))
      (cubeObservable (rootCorrectedSpan (-centralPhysicalFinitePulledVacuumSectorHeadCorrectionApprox
        (w := anchorCoupling) (by decide) p.base 0 p.coefficient stage))) :=
  moving_observable p hraw stage

theorem probe_stage_observable (stage : Nat) :
    CentralPhysicalLinearObservable.Equivalent (cubeObservable (probeReflectedCauchy.seq stage))
      (cubeObservable (rootCorrectedSpan (probeCorrection stage))) := by
  unfold probeReflectedCauchy probeSourceCauchy probeCorrection
  exact centered_stage_observable probePresentation (spanPresentation_observable (basis probeState)) stage

theorem probe_stage_recode (stage : Nat) :
    cubeReflectedEmbed (probeReflectedCauchy.seq stage) =
      cubeReflectedEmbed (rootCorrectedSpan (probeCorrection stage)) :=
  cubeReflectedSeminorm.embedRep_eq_of_null (cubeObservable_null_of_equivalent (probe_stage_observable stage))

theorem rootCorrected_reflected_floor (c : Q') :
    CReal.RCle (Quotient.mk CReal.crealSetoid (CReal.ofQ' reflectedProbeFloor))
      (cubeReflectedInner (cubeReflectedEmbed (rootCorrectedSpan c))
        (cubeReflectedEmbed (rootCorrectedSpan c))) := by
  rw [dense_pairing]
  intro epsilon hepsilon
  refine ⟨0, fun K _ => ?_⟩
  have hraw := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.mkPos 64 65 (by decide))
    (rootCorrectedSpan_floor (w := anchorCoupling) (by decide) c) (by decide)
  exact Q'.le_trans' _ _ _ hraw (Q'.le_trans' _ _ _
    (normalizedFormLimit_anchor_norm_bounds (rootCorrectedSpan c) K).1
    (Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt hepsilon)))

theorem probe_stage_floor (stage : Nat) :
    CReal.leEv (CReal.ofQ' reflectedProbeFloor)
      (normalizedFormLimit (w := anchorCoupling) (by decide) (by decide)
        (probeReflectedCauchy.seq stage) (probeReflectedCauchy.seq stage)) := by
  have h := rootCorrected_reflected_floor (probeCorrection stage)
  rw [← probe_stage_recode stage, dense_pairing] at h
  exact h

def probeNormLimit : CReal := cubeReflectedPairingLimit probeReflectedCauchy probeReflectedCauchy

theorem probeNormLimit_floor : CReal.leEv (CReal.ofQ' reflectedProbeFloor) probeNormLimit :=
  CReal.leEv_of_convergesTo_le (CReal.convergesTo_const (CReal.ofQ' reflectedProbeFloor))
    (cubeReflectedPairingLimit_converges probeReflectedCauchy probeReflectedCauchy) probe_stage_floor

theorem centeredProbe_norm : cubeReflectedInner centeredProbe.val centeredProbe.val =
    Quotient.mk CReal.crealSetoid probeNormLimit := rfl

theorem centeredProbe_norm_floor :
    CReal.RCle (Quotient.mk CReal.crealSetoid (CReal.ofQ' reflectedProbeFloor))
      (cubeReflectedInner centeredProbe.val centeredProbe.val) := by
  rw [centeredProbe_norm]
  exact probeNormLimit_floor

theorem centeredProbe_norm_positive : RCIsPositive (cubeReflectedInner centeredProbe.val centeredProbe.val) :=
  ⟨reflectedProbeFloor, reflectedProbeFloor_pos, centeredProbe_norm_floor⟩

theorem centeredProbe_ne_zero : centeredProbe.val ≠ cubeReflectedEmbed [] := by
  intro hzero
  have h := centeredProbe_norm_floor
  rw [hzero, cubeReflectedInner_zero_left] at h
  have hbad : reflectedProbeFloor ≤ 0 := YMGap.Continuum.GNSQuotient.GNSData.RCofQ'_le_reflect h
  exact (by decide : ¬ (0 : Q') < 0) (Q'.pos_of_lt_of_le reflectedProbeFloor_pos hbad)

/-- The literal connected conditional covariance at index one is the norm
at reflected index zero. This is not a physical-time decay estimate. -/
theorem centeredProbe_connected_one_positive :
    RCIsPositive (globalConditionalCovariance 1
      (centralPhysicalVacuumSectorCylinderCompletionToGlobal
        (centeredSectorSource probePresentation.base probePresentation.coefficient))
      (centralPhysicalVacuumSectorCylinderCompletionToGlobal
        (centeredSectorSource probePresentation.base probePresentation.coefficient))) := by
  rw [centeredCubeCorrelator_connected probePresentation.base probePresentation.coefficient 0]
  exact centeredProbe_norm_positive

end YMGap.Continuum.BF4PhysicalCubeCenteredPositiveNorm

#print axioms YMGap.Continuum.BF4PhysicalCubeCenteredPositiveNorm.probePresentation
#print axioms YMGap.Continuum.BF4PhysicalCubeCenteredPositiveNorm.probeSourceCauchy
#print axioms YMGap.Continuum.BF4PhysicalCubeCenteredPositiveNorm.probeReflectedCauchy
#print axioms YMGap.Continuum.BF4PhysicalCubeCenteredPositiveNorm.centeredProbe
#print axioms YMGap.Continuum.BF4PhysicalCubeCenteredPositiveNorm.probeCorrection
#print axioms YMGap.Continuum.BF4PhysicalCubeCenteredPositiveNorm.reflectedProbeFloor
#print axioms YMGap.Continuum.BF4PhysicalCubeCenteredPositiveNorm.reflectedProbeFloor_pos
#print axioms YMGap.Continuum.BF4PhysicalCubeCenteredPositiveNorm.probe_stage_observable
#print axioms YMGap.Continuum.BF4PhysicalCubeCenteredPositiveNorm.probe_stage_recode
#print axioms YMGap.Continuum.BF4PhysicalCubeCenteredPositiveNorm.rootCorrected_reflected_floor
#print axioms YMGap.Continuum.BF4PhysicalCubeCenteredPositiveNorm.probe_stage_floor
#print axioms YMGap.Continuum.BF4PhysicalCubeCenteredPositiveNorm.probeNormLimit
#print axioms YMGap.Continuum.BF4PhysicalCubeCenteredPositiveNorm.probeNormLimit_floor
#print axioms YMGap.Continuum.BF4PhysicalCubeCenteredPositiveNorm.centeredProbe_norm
#print axioms YMGap.Continuum.BF4PhysicalCubeCenteredPositiveNorm.centeredProbe_norm_floor
#print axioms YMGap.Continuum.BF4PhysicalCubeCenteredPositiveNorm.centeredProbe_norm_positive
#print axioms YMGap.Continuum.BF4PhysicalCubeCenteredPositiveNorm.centeredProbe_ne_zero
#print axioms YMGap.Continuum.BF4PhysicalCubeCenteredPositiveNorm.centeredProbe_connected_one_positive
