/-
# All-subunit coercivity from the actual adaptive tail and rooted head

The quarter-tail cutoff is a finite, nome-dependent base. The already
constructed persistent positive-edge floor controls that same rooted head
at every sufficiently late cutoff. Both estimates use the original physical
kernel and stationary norm. No head gap or analytic certificate is supplied.

Scope: SU(2), half=0, every rational 0<w<1. Neither the onset nor the
coercivity constant is claimed uniform in w or spatial volume. This is not
an original Yang--Mills geometric-time or continuum result.
-/

import YMGap.Continuum.BF4PhysicalCubeSubunitHighLabelTrace
import YMGap.Continuum.BF4PhysicalCubeAnchoredHeadBound

namespace YMGap.Continuum.BF4PhysicalCubeSubunitCoercivity

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCubeAnchoredHeadBound
open YMGap.Continuum.BF4PhysicalCubeTailAbsorption
open YMGap.Continuum.BF4PhysicalCubeSubunitHighLabelTrace
open YMGap.Continuum.BF4PhysicalCubeSubunitRadialTail
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorBlockDecomposition
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledBaseEdgeFloor
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledBaseEdgeFloorFormula
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorDirichlet
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorSimplePathScale
open YMGap.Continuum.BF4PhysicalVacuumSectorHeadTailGramGap

local infix:50 " ≈ " => Q'.eqv

/-- The computed fixed head whose complementary raw trace is at most 1/4. -/
def subunitHeadBase (w : Q') : Nat := subunitRadialTailCutoff w absorptionTailRate

/-- The existing persistent-edge onset at that very same finite base. -/
def subunitHeadStart (w : Q') : Nat :=
  fixedBasePulledEdgeFloorAnchor w (subunitHeadBase w) 0

theorem subunitHeadStart_ge_base (w : Q') :
    subunitHeadBase w ≤ subunitHeadStart w :=
  fixedBasePulledEdgeFloorAnchor_ge_base w (subunitHeadBase w) 0

/-- Explicit path-scale / edge-floor quotient, independent of the later cutoff. -/
def subunitHeadEnergyConstant (w : Q') (hw : (0 : Q') ≤ w) : Q' :=
  Q'.divPos (centralPhysicalFiniteVacuumSectorSimpleCarrierSquareScale w hw (subunitHeadBase w) 0)
    (fixedBasePulledPositiveEdgeFloorValue w hw (subunitHeadBase w) 0)
    (fixedBasePulledPositiveEdgeFloorValue_pos w hw (subunitHeadBase w) 0)

theorem subunitHeadEnergyConstant_pos (w : Q') (hw : (0 : Q') ≤ w) :
    (0 : Q') < subunitHeadEnergyConstant w hw :=
  Q'.divPos_pos _ _ _
    (centralPhysicalFiniteVacuumSectorSimpleCarrierSquareScale_pos w hw (subunitHeadBase w) 0)

/-- The rooted adaptive head is controlled by the full original later energy. -/
theorem subunit_anchored_head_bound {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (later : Nat) (hlater : subunitHeadStart w ≤ later) (f : Nat → Q') :
    centralPhysicalFiniteVacuumSectorDiagonalQuadratic w (Q'.le_of_lt hw0) later 0
      (centralPhysicalFiniteVacuumSectorEmbeddedHeadCoefficient w (Q'.le_of_lt hw0)
        (subunitHeadBase w) later 0 (rootShift f)) ≤
      subunitHeadEnergyConstant w (Q'.le_of_lt hw0) *
        finiteJointDirichletEnergy (centralPhysicalFiniteVacuumSectorIndices w (Q'.le_of_lt hw0) later 0)
          f (centralPhysicalFiniteKernel w (Q'.le_of_lt hw0) later 0) := by
  let hw := Q'.le_of_lt hw0
  let base := subunitHeadBase w
  let cert := explicitFixedBasePulledPositiveEdgeFloor hw0 hw1 base 0
  have hstart : cert.start = subunitHeadStart w :=
    explicitFixedBasePulledPositiveEdgeFloor_start_eq_anchor hw0 hw1 base 0
  have h := floor_mul_anchored_head_norm_le_energy cert later (by rw [hstart]; exact hlater) f
  have hf : cert.floor ≈ fixedBasePulledPositiveEdgeFloorValue w hw base 0 :=
    explicitFixedBasePulledPositiveEdgeFloor_floor_eqv_value hw0 hw1 base 0
  let E := finiteJointDirichletEnergy (centralPhysicalFiniteVacuumSectorIndices w hw later 0)
    f (centralPhysicalFiniteKernel w hw later 0)
  let F := fixedBasePulledPositiveEdgeFloorValue w hw base 0
  let S := centralPhysicalFiniteVacuumSectorSimpleCarrierSquareScale w hw base 0
  have hcancel : F * (subunitHeadEnergyConstant w hw * E) ≈ S * E := by
    refine Q'.eqv_trans _ ((F * subunitHeadEnergyConstant w hw) * E) _
      (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
    apply Q'.mul_eqv_congr_right
    exact Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) (Q'.divPos_mul_eqv S F _)
  apply Q'.le_of_mul_le_mul_left (c := F) _ (fixedBasePulledPositiveEdgeFloorValue_pos w hw base 0)
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.mul_eqv_congr_right _ _ _ hf))
    (Q'.le_trans' _ _ _ h (Q'.ge_of_eqv hcancel))

/-- Directed-energy coercivity constant, retaining all nome dependence. -/
def subunitCoercivityConstant (w : Q') (hw : (0 : Q') ≤ w) : Q' :=
  1 + 3 * subunitHeadEnergyConstant w hw

theorem subunitCoercivityConstant_pos (w : Q') (hw : (0 : Q') ≤ w) :
    (0 : Q') < subunitCoercivityConstant w hw :=
  Q'.add_pos (by decide) (Q'.mul_pos (by decide) (subunitHeadEnergyConstant_pos w hw))

private theorem energy_regroup (C E : Q') : E + 3 * (C * E) ≈ (1 + 3 * C) * E :=
  Q'.eqv_trans _ (1 * E + (3 * C) * E) _
    (Q'.add_eqv_congr' (Q'.eqv_symm (Q'.one_mul_eqv E)) (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)))
    (Q'.eqv_symm (Q'.add_mul_eqv _ _ _))

/-- Every centered physical coefficient is controlled by its own full
directed energy, with one computed constant for all later cutoffs. -/
theorem centered_norm_le_subunitCoercivity_mul_energy {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (later : Nat) (hlater : subunitHeadStart w ≤ later) (f : Nat → Q')
    (hcenter : centralPhysicalFiniteVacuumSectorWeightedMean w (Q'.le_of_lt hw0) later 0 f ≈ 0) :
    centralPhysicalFiniteVacuumSectorDiagonalQuadratic w (Q'.le_of_lt hw0) later 0 f ≤
      subunitCoercivityConstant w (Q'.le_of_lt hw0) *
        finiteJointDirichletEnergy (centralPhysicalFiniteVacuumSectorIndices w (Q'.le_of_lt hw0) later 0)
          f (centralPhysicalFiniteKernel w (Q'.le_of_lt hw0) later 0) := by
  have hbase := Nat.le_trans (subunitHeadStart_ge_base w) hlater
  have htrace := newTailSelfReturnTrace_small_subunit hw0 hw1
    absorptionTailRate absorptionTailRate_pos later hbase
  have habsorb := centered_norm_le_energy_add_anchored_head_of_selfReturnTrace
    hw0 (subunitHeadBase w) later hbase htrace f hcenter
  have hhead := subunit_anchored_head_bound hw0 hw1 later hlater f
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ 3 hhead (by decide)
  exact Q'.le_trans' _ _ _ habsorb
    (Q'.le_trans' _ _ _ (Q'.add_le_add_left _ _ _ hscaled)
      (Q'.le_of_eqv (energy_regroup _ _)))

end YMGap.Continuum.BF4PhysicalCubeSubunitCoercivity

#print axioms YMGap.Continuum.BF4PhysicalCubeSubunitCoercivity.subunitHeadBase
#print axioms YMGap.Continuum.BF4PhysicalCubeSubunitCoercivity.subunitHeadStart
#print axioms YMGap.Continuum.BF4PhysicalCubeSubunitCoercivity.subunitHeadStart_ge_base
#print axioms YMGap.Continuum.BF4PhysicalCubeSubunitCoercivity.subunitHeadEnergyConstant
#print axioms YMGap.Continuum.BF4PhysicalCubeSubunitCoercivity.subunitHeadEnergyConstant_pos
#print axioms YMGap.Continuum.BF4PhysicalCubeSubunitCoercivity.subunit_anchored_head_bound
#print axioms YMGap.Continuum.BF4PhysicalCubeSubunitCoercivity.subunitCoercivityConstant
#print axioms YMGap.Continuum.BF4PhysicalCubeSubunitCoercivity.subunitCoercivityConstant_pos
#print axioms YMGap.Continuum.BF4PhysicalCubeSubunitCoercivity.centered_norm_le_subunitCoercivity_mul_energy
