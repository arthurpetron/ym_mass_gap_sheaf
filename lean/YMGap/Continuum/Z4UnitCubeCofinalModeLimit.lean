/-
# A constructive cofinal-box limit for the elementary cube mode

The exact all-volume amplitude supplies a genuine stage-zero convergence
modulus along the cofinal boxes of side `n + 2`.  This packages that local
mode together with unbounded four-dimensional graph size, the uniform
finite-state separator, and an exact positive spectral-mode witness at every
stage and every cutoff at least two.

This is a limit of one explicitly derived local mode.  It is not yet a limit
of the complete finite-volume probability functional or all correlators.
-/

import YMGap.Constructive.CRealAbs
import YMGap.Continuum.Z4UnitCubeAllVolumeAmplitude

namespace YMGap.Continuum.Z4UnitCubeCofinalModeLimit

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.SpectralGap
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphCompensatedRefinementPath
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphSupportedRefinementPath
open YMGap.Continuum.SU2PeterWeylWilsonBlock
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4FiniteBoxHeatKernelCutoffPersistence
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4UnitCubeAllVolumeAmplitude

local infix:50 " ≈ " => Q'.eqv

/-- The exact projected cube amplitude along the cofinal box sequence. -/
def unitCubeCofinalAmplitudeSeq (K n : Nat) : Q' :=
  packetGraphProjectedAmplitude (usedResolutionEdges (n + 2))
    (resolutionVertices (n + 2))
    (gaugeHeatKernelBoxPacketsAtCutoff K (n + 2))
    (unitCubeSurfaceLabel (n + 2))

/-- Its explicitly identified constructive-real limit. -/
def unitCubeCofinalAmplitudeLimit : CReal :=
  CReal.ofQ' unitCubeHeatKernelAmplitude

/-- The cofinal box graphs have unbounded edge count. -/
theorem unitCubeCofinalEdges_unbounded (bound : Nat) :
    ∃ n : Nat, bound ≤ (usedResolutionEdges (n + 2)).length := by
  let v := bound + 3
  have hv : 0 < v := by unfold v; omega
  have h1 : v ≤ v * v := Nat.le_mul_of_pos_right v hv
  have h2 : v * v ≤ (v * v) * v :=
    Nat.le_mul_of_pos_right (v * v) hv
  have h3 : (v * v) * v ≤ ((v * v) * v) * v :=
    Nat.le_mul_of_pos_right ((v * v) * v) hv
  have h4 : ((v * v) * v) * v ≤ (((v * v) * v) * v) * 6 :=
    Nat.le_mul_of_pos_right (((v * v) * v) * v) (by decide)
  refine ⟨bound + 1, ?_⟩
  unfold usedResolutionEdges plaquetteEdgeCount
  rw [List.length_append, List.length_range, boxPlaquettes_length]
  have hb : bound ≤ v := by unfold v; omega
  exact Nat.le_trans hb
    (Nat.le_trans h1 (Nat.le_trans h2 (Nat.le_trans h3
      (Nat.le_trans h4 (Nat.le_add_right _ _)))))

/-- Exact all-volume evaluation gives a stage-zero convergence modulus for
the local cube amplitude. -/
theorem unitCubeCofinalAmplitude_converges {K : Nat} (hK : 2 ≤ K) :
    CReal.ConvergesTo
      (fun n => CReal.ofQ' (unitCubeCofinalAmplitudeSeq K n))
      unitCubeCofinalAmplitudeLimit := by
  intro ε hε
  refine ⟨0, fun n _ => ⟨0, fun k _ => ?_⟩⟩
  simp only [unitCubeCofinalAmplitudeSeq, unitCubeCofinalAmplitudeLimit,
    CReal.ofQ'_approx]
  have hamp := unitCube_heatKernel_amplitude_exact_all_volumes_at_cutoff
    hK (show 2 ≤ n + 2 by omega)
  have hε0 : (0 : Q') ≤ ε := Q'.le_of_lt hε
  exact
    ⟨Q'.le_trans' _ _ _ (Q'.le_of_eqv hamp)
        (Q'.add_le_self_of_nonneg _ _ hε0),
      Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm hamp))
        (Q'.add_le_self_of_nonneg _ _ hε0)⟩

/-- A cofinal family carrying the local amplitude limit, a uniform separator,
and an exact positive cube mode at every stage. -/
structure CofinalCubeModeTower (K : Nat) where
  level : Nat → CompensatedGraphState K
  edgeCountUnbounded : ∀ bound : Nat, ∃ n : Nat,
    bound ≤ (level n).edges.length
  amplitudeSeq : Nat → Q'
  amplitudeLimit : CReal
  amplitudeConverges : CReal.ConvergesTo
    (fun n => CReal.ofQ' (amplitudeSeq n)) amplitudeLimit
  separator : Q'
  separator_pos : (0 : Q') < separator
  levelGap : ∀ n : Nat,
    SpectralGapBound (supportedGraphSpectralModel (level n)) separator
  cubeMode : ∀ n : Nat,
    ∃ i, i < (physicalEdgeLabellings K (usedResolutionEdges (n + 2))
        (resolutionVertices (n + 2))).length ∧
      packetGraphModeWeight (usedResolutionEdges (n + 2))
        (resolutionVertices (n + 2))
        (gaugeHeatKernelBoxPacketsAtCutoff K (n + 2)) i ≈
          unitCubeHeatKernelAmplitude * unitCubeHeatKernelAmplitude

/-- The genuine Z4 heat-kernel box family inhabits the cofinal local-mode
limit interface at every cutoff at least two. -/
def unitCubeCofinalModeTower {K : Nat} (hK : 2 ≤ K) :
    CofinalCubeModeTower K where
  level := fun n => gaugeHeatKernelBoxStateAtCutoff K (n + 2)
  edgeCountUnbounded := unitCubeCofinalEdges_unbounded
  amplitudeSeq := unitCubeCofinalAmplitudeSeq K
  amplitudeLimit := unitCubeCofinalAmplitudeLimit
  amplitudeConverges := unitCubeCofinalAmplitude_converges hK
  separator := eighth * eighth
  separator_pos := by decide
  levelGap := fun n => gaugeHeatKernelBoxStateAtCutoff_gap K (n + 2)
  cubeMode := fun n =>
    unitCube_heatKernel_nonzero_mode_all_volumes_at_cutoff hK
      (show 2 ≤ n + 2 by omega)

#print axioms unitCubeCofinalEdges_unbounded
#print axioms unitCubeCofinalAmplitude_converges
#print axioms CofinalCubeModeTower
#print axioms unitCubeCofinalModeTower

end YMGap.Continuum.Z4UnitCubeCofinalModeLimit
