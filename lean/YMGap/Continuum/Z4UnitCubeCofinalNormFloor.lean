/-
# A uniform unnormalised norm floor from the elementary cube mode

The all-volume cube theorem identifies one enumerated physical mode whose
weight is the same exact positive rational at every volume and every cutoff
at least two.  Since every graph-mode weight is nonnegative, that one term
gives a uniform lower bound for the complete finite-graph squared norm and
for the time-zero correlator of the concrete diagonal packet-graph model.

This is a genuine non-vacuity statement for the derived finite graph model.
It is deliberately stated for the unnormalised spectral norm.  It does not
bound the heat-kernel partition function from above and therefore does not,
by itself, give a volume-uniform lower bound after probability
normalisation.  That normalization/connected-tail step remains the
thermodynamic residual.
-/

import YMGap.Continuum.BondMovingMoment
import YMGap.Continuum.Z4UnitCubeCofinalModeLimit

namespace YMGap.Continuum.Z4UnitCubeCofinalNormFloor

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.BondMovingMoment
open YMGap.Continuum.SpectralGap
open YMGap.Continuum.SU2FiniteSpinNetworkSpectralEnvelope
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.Z4FiniteBoxHeatKernelCutoffPersistence
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4UnitCubeAllVolumeAmplitude
open YMGap.Continuum.Z4UnitCubeCofinalModeLimit

local infix:50 " ≈ " => Q'.eqv

/-- The squared exact cube amplitude, used as the uniform norm floor. -/
def unitCubeNormFloor : Q' :=
  unitCubeHeatKernelAmplitude * unitCubeHeatKernelAmplitude

/-- The floor is strictly positive, with no volume or cutoff parameter. -/
theorem unitCubeNormFloor_pos : (0 : Q') < unitCubeNormFloor := by
  unfold unitCubeNormFloor
  exact Q'.mul_pos unitCubeHeatKernelAmplitude_pos
    unitCubeHeatKernelAmplitude_pos

/-- The full unnormalised packet-graph squared norm contains the exact cube
mode and is therefore bounded below uniformly in volume and cutoff. -/
theorem unitCube_packetGraphExactNorm_ge
    {K n : Nat} (hK : 2 ≤ K) (hn : 2 ≤ n) :
    unitCubeNormFloor ≤
      packetGraphExactNorm (usedResolutionEdges n)
        (resolutionVertices n)
        (gaugeHeatKernelBoxPacketsAtCutoff K n) := by
  obtain ⟨i, hi, hmode⟩ :=
    unitCube_heatKernel_nonzero_mode_all_volumes_at_cutoff hK hn
  unfold packetGraphExactNorm finiteNetworkFamilyNorm
  exact Q'.le_trans' _ _ _
    (Q'.ge_of_eqv hmode)
    (fsum_term_le_of_nonneg
      (packetGraphModeWeight_nonneg (usedResolutionEdges n)
        (resolutionVertices n)
        (gaugeHeatKernelBoxPacketsAtCutoff K n)) i _ hi)

/-- The time-zero correlator of the concrete packet-graph spectral model has
the same uniform positive lower bound. -/
theorem unitCube_packetGraphCorrZero_ge
    {K n : Nat} (hK : 2 ≤ K) (hn : 2 ≤ n) :
    unitCubeNormFloor ≤
      corr
        (packetGraphSpectralModel (usedResolutionEdges n)
          (resolutionVertices n)
          (gaugeHeatKernelBoxPacketsAtCutoff K n)) 0 := by
  exact Q'.le_trans' _ _ _
    (unitCube_packetGraphExactNorm_ge hK hn)
    (Q'.ge_of_eqv
      (packetGraph_corr_zero_eq_exactNorm (usedResolutionEdges n)
        (resolutionVertices n)
        (gaugeHeatKernelBoxPacketsAtCutoff K n)))

/-- Cofinal specialization: the same rational floor holds at every stage of
the unbounded box tower. -/
theorem unitCubeCofinalCorrZero_ge
    {K : Nat} (hK : 2 ≤ K) (stage : Nat) :
    unitCubeNormFloor ≤
      corr
        (packetGraphSpectralModel (usedResolutionEdges (stage + 2))
          (resolutionVertices (stage + 2))
          (gaugeHeatKernelBoxPacketsAtCutoff K (stage + 2))) 0 :=
  unitCube_packetGraphCorrZero_ge hK (by omega)

#print axioms unitCubeNormFloor_pos
#print axioms unitCube_packetGraphExactNorm_ge
#print axioms unitCube_packetGraphCorrZero_ge
#print axioms unitCubeCofinalCorrZero_ge

end YMGap.Continuum.Z4UnitCubeCofinalNormFloor
