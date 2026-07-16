/-
# The elementary cube along a growing character cutoff

The fixed-cutoff independent-plaquette tail cannot be uniform in volume.
One alternative is to let the Peter--Weyl cutoff grow along the cofinal box
sequence.  This module proves the first necessary compatibility fact for
that route: the exact local cube amplitude, its stage-zero constructive-real
limit, and an enumerated positive physical mode persist for every cutoff
schedule bounded below by two.  A canonical schedule `K stage = stage + 2`
is both cofinal in volume and unbounded in cutoff.

This does not prove that the omitted character tail is summable for the
growing schedule, nor that the complete normalized functional converges.
It establishes that increasing the cutoff does not destroy or renormalize
the already-derived local nontrivial mode.
-/

import YMGap.Continuum.Z4UnitCubeCofinalNormFloor

namespace YMGap.Continuum.Z4UnitCubeGrowingCutoffCofinal

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.SpectralGap
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.Z4FiniteBoxHeatKernelCutoffPersistence
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4UnitCubeAllVolumeAmplitude
open YMGap.Continuum.Z4UnitCubeCofinalModeLimit
open YMGap.Continuum.Z4UnitCubeCofinalNormFloor

local infix:50 " ≈ " => Q'.eqv

/-- The exact local cube amplitude sampled at a varying cutoff. -/
def growingCutoffCubeAmplitudeSeq (cutoff : Nat → Nat) (stage : Nat) : Q' :=
  packetGraphProjectedAmplitude (usedResolutionEdges (stage + 2))
    (resolutionVertices (stage + 2))
    (gaugeHeatKernelBoxPacketsAtCutoff (cutoff stage) (stage + 2))
    (unitCubeSurfaceLabel (stage + 2))

/-- Every cutoff schedule staying above two has the same stage-zero local
amplitude limit as the fixed-cutoff tower. -/
theorem growingCutoffCubeAmplitude_converges
    (cutoff : Nat → Nat) (hcutoff : ∀ stage, 2 ≤ cutoff stage) :
    CReal.ConvergesTo
      (fun stage => CReal.ofQ' (growingCutoffCubeAmplitudeSeq cutoff stage))
      unitCubeCofinalAmplitudeLimit := by
  intro ε hε
  refine ⟨0, fun stage _ => ⟨0, fun precision _ => ?_⟩⟩
  simp only [growingCutoffCubeAmplitudeSeq, unitCubeCofinalAmplitudeLimit,
    CReal.ofQ'_approx]
  have hamp := unitCube_heatKernel_amplitude_exact_all_volumes_at_cutoff
    (hcutoff stage) (show 2 ≤ stage + 2 by omega)
  have hε0 : (0 : Q') ≤ ε := Q'.le_of_lt hε
  exact
    ⟨Q'.le_trans' _ _ _ (Q'.le_of_eqv hamp)
        (Q'.add_le_self_of_nonneg _ _ hε0),
      Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm hamp))
        (Q'.add_le_self_of_nonneg _ _ hε0)⟩

/-- The varying-cutoff time-zero spectral correlator retains the same exact
positive unnormalised floor at every stage. -/
theorem growingCutoffCubeCorrZero_ge
    (cutoff : Nat → Nat) (hcutoff : ∀ stage, 2 ≤ cutoff stage)
    (stage : Nat) :
    unitCubeNormFloor ≤
      corr
        (packetGraphSpectralModel (usedResolutionEdges (stage + 2))
          (resolutionVertices (stage + 2))
          (gaugeHeatKernelBoxPacketsAtCutoff
            (cutoff stage) (stage + 2))) 0 :=
  unitCube_packetGraphCorrZero_ge (hcutoff stage) (by omega)

/-- Data carried by a cofinal box tower with an unbounded character cutoff.
The mode field is stated in the actual varying finite enumeration. -/
structure GrowingCutoffCubeModeTower where
  cutoff : Nat → Nat
  cutoff_ge_two : ∀ stage, 2 ≤ cutoff stage
  cutoff_unbounded : ∀ bound, ∃ stage, bound ≤ cutoff stage
  edgeCountUnbounded : ∀ bound, ∃ stage,
    bound ≤ (usedResolutionEdges (stage + 2)).length
  amplitudeConverges : CReal.ConvergesTo
    (fun stage => CReal.ofQ'
      (growingCutoffCubeAmplitudeSeq cutoff stage))
    unitCubeCofinalAmplitudeLimit
  corrZeroFloor : ∀ stage,
    unitCubeNormFloor ≤
      corr
        (packetGraphSpectralModel (usedResolutionEdges (stage + 2))
          (resolutionVertices (stage + 2))
          (gaugeHeatKernelBoxPacketsAtCutoff
            (cutoff stage) (stage + 2))) 0
  cubeMode : ∀ stage,
    ∃ i, i < (physicalEdgeLabellings (cutoff stage)
        (usedResolutionEdges (stage + 2))
        (resolutionVertices (stage + 2))).length ∧
      packetGraphModeWeight (usedResolutionEdges (stage + 2))
        (resolutionVertices (stage + 2))
        (gaugeHeatKernelBoxPacketsAtCutoff (cutoff stage) (stage + 2)) i ≈
          unitCubeHeatKernelAmplitude * unitCubeHeatKernelAmplitude

/-- The canonical simultaneous schedule: box side and cutoff both equal
`stage + 2`. -/
def canonicalGrowingCutoffCubeModeTower : GrowingCutoffCubeModeTower where
  cutoff := fun stage => stage + 2
  cutoff_ge_two := fun stage => by omega
  cutoff_unbounded := fun bound => ⟨bound, by omega⟩
  edgeCountUnbounded := unitCubeCofinalEdges_unbounded
  amplitudeConverges := growingCutoffCubeAmplitude_converges
    (fun stage : Nat => stage + 2)
    (fun stage => show 2 ≤ (stage : Nat) + 2 by omega)
  corrZeroFloor := growingCutoffCubeCorrZero_ge
    (fun stage : Nat => stage + 2)
    (fun stage => show 2 ≤ (stage : Nat) + 2 by omega)
  cubeMode := fun stage =>
    unitCube_heatKernel_nonzero_mode_all_volumes_at_cutoff
      (show 2 ≤ stage + 2 by omega)
      (show 2 ≤ stage + 2 by omega)

#print axioms growingCutoffCubeAmplitude_converges
#print axioms growingCutoffCubeCorrZero_ge
#print axioms GrowingCutoffCubeModeTower
#print axioms canonicalGrowingCutoffCubeModeTower

end YMGap.Continuum.Z4UnitCubeGrowingCutoffCofinal
