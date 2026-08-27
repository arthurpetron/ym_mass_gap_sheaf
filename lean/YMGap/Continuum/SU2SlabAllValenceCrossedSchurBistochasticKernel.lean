/-
# Complete crossed recoupling matrices at every slab-link valence

The production slab exposes degrees zero through six.  Below degree four the
complete recoupling matrix is the one-point identity.  Degrees four, five,
and six use the already completed crossed SU(2) associator matrices.  This
module contracts that finite case split into one dependent package carrying
both source and target types and both normalization laws.

This is a representation-theoretic matrix family, not a Gibbs conditional or
an Osterwalder--Schrader transfer operator.

Constructive contract: exact finite carriers, structural degree cases, no
choice, `Classical`, `sorry`, or new axiom.
-/

import YMGap.Continuum.FiniteBistochasticQKernelProduct
import YMGap.Continuum.SU2SlabAllValenceCrossedSchurKernel
import YMGap.Continuum.SU2SlabValenceFourCrossedSchurBistochasticKernel
import YMGap.Continuum.SU2SlabValenceFiveCrossedSchurBistochasticKernel
import YMGap.Continuum.SU2SlabValenceSixCrossedSchurBistochasticKernel

namespace YMGap.Continuum.SU2SlabAllValenceCrossedSchurBistochasticKernel

open YMGap.Constructive
open YMGap.Continuum.FiniteBistochasticQKernel
open YMGap.Continuum.FiniteBistochasticQKernelProduct
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2SlabAllValenceCrossedSchurKernel
open YMGap.Continuum.SU2SlabHigherValenceCrossedSchurCompiler
open YMGap.Continuum.SU2SlabValenceFourCrossedSchurBistochasticKernel
open YMGap.Continuum.SU2SlabValenceFourCrossedSchurCompiler
open YMGap.Continuum.SU2SlabValenceFiveCrossedSchurBistochasticKernel
open YMGap.Continuum.SU2SlabValenceSixCrossedSchurBistochasticKernel

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The complete trivial matrix -/

def unitFiniteBistochasticQKernel :
    FiniteBistochasticQKernel Unit Unit where
  sources := [()]
  targets := [()]
  weight := fun _ _ => 1
  weight_nonnegative := fun _ _ => Q'.zero_le_one
  row_normalized := fun _ => Q'.eqv_of_eq (Q'.add_zero' 1)
  column_normalized := fun _ => Q'.eqv_of_eq (Q'.add_zero' 1)

def unitFiniteBistochasticQKernelPackage :
    FiniteBistochasticQKernelPackage where
  Source := Unit
  Target := Unit
  kernel := unitFiniteBistochasticQKernel

/-! ## 2. One complete matrix package at every actual degree -/

/-- The exact complete crossed recoupling matrix at an actual slab link. -/
def crossedLinkBistochasticKernelPackage {K extent : Nat} :
    (degree : Nat) → CrossedSlabSwitchData K extent degree →
      FiniteBistochasticQKernelPackage
  | 0, _ => unitFiniteBistochasticQKernelPackage
  | 1, _ => unitFiniteBistochasticQKernelPackage
  | 2, _ => unitFiniteBistochasticQKernelPackage
  | 3, _ => unitFiniteBistochasticQKernelPackage
  | 4, D =>
      let D₄ := CrossedSlabSwitchData.toValenceFour D
      { Source := CrossedSchurSource D₄
        Target := CrossedSchurTarget D₄
        kernel := crossedSchurBistochasticKernel D₄ }
  | 5, D =>
      { Source := CrossedValenceFiveMatrixSource D
        Target := CrossedValenceFiveMatrixTarget D
        kernel := crossedValenceFiveBistochasticKernel D }
  | 6, D =>
      { Source := CrossedValenceSixMatrixSource D
        Target := CrossedValenceSixMatrixTarget D
        kernel := crossedValenceSixBistochasticKernel D }
  | degree + 7, D => False.elim (by
      have hdegree := CrossedSlabSwitchData.degree_le_six D
      omega)

/-- The actual production fusion witnesses select one source of the complete
matrix at every link degree. -/
def crossedLinkBistochasticProductionSource {K extent : Nat} :
    (degree : Nat) → (D : CrossedSlabSwitchData K extent degree) →
      (crossedLinkBistochasticKernelPackage degree D).Source
  | 0, _ => ()
  | 1, _ => ()
  | 2, _ => ()
  | 3, _ => ()
  | 4, D =>
      let D₄ := CrossedSlabSwitchData.toValenceFour D
      (crossedLeftChannel D₄, crossedRightChannel D₄)
  | 5, D => crossedValenceFiveProductionSource D
  | 6, D => crossedValenceSixProductionSource D
  | degree + 7, D => False.elim (by
      have hdegree := CrossedSlabSwitchData.degree_le_six D
      omega)

def crossedLinkPointedBistochasticKernelPackage {K extent degree : Nat}
    (D : CrossedSlabSwitchData K extent degree) :
    PointedFiniteBistochasticQKernelPackage where
  package := crossedLinkBistochasticKernelPackage degree D
  source := crossedLinkBistochasticProductionSource degree D

theorem crossedLinkBistochasticKernelPackage_weight_nonnegative
    {K extent degree : Nat} (D : CrossedSlabSwitchData K extent degree)
    (source : (crossedLinkBistochasticKernelPackage degree D).Source)
    (target : (crossedLinkBistochasticKernelPackage degree D).Target) :
    (0 : Q') ≤
      (crossedLinkBistochasticKernelPackage degree D).kernel.weight
        source target :=
  (crossedLinkBistochasticKernelPackage degree D).kernel.weight_nonnegative
    source target

theorem crossedLinkBistochasticKernelPackage_row_normalized
    {K extent degree : Nat} (D : CrossedSlabSwitchData K extent degree)
    (source : (crossedLinkBistochasticKernelPackage degree D).Source) :
    listQSum
        ((crossedLinkBistochasticKernelPackage degree D).kernel.weight source)
        (crossedLinkBistochasticKernelPackage degree D).kernel.targets ≈ 1 :=
  (crossedLinkBistochasticKernelPackage degree D).kernel.row_normalized source

theorem crossedLinkBistochasticProductionSource_row_normalized
    {K extent degree : Nat} (D : CrossedSlabSwitchData K extent degree) :
    listQSum
        ((crossedLinkBistochasticKernelPackage degree D).kernel.weight
          (crossedLinkBistochasticProductionSource degree D))
        (crossedLinkBistochasticKernelPackage degree D).kernel.targets ≈ 1 :=
  (crossedLinkBistochasticKernelPackage degree D).kernel.row_normalized
    (crossedLinkBistochasticProductionSource degree D)

theorem crossedLinkBistochasticKernelPackage_column_normalized
    {K extent degree : Nat} (D : CrossedSlabSwitchData K extent degree)
    (target : (crossedLinkBistochasticKernelPackage degree D).Target) :
    listQSum
        (fun source =>
          (crossedLinkBistochasticKernelPackage degree D).kernel.weight
            source target)
        (crossedLinkBistochasticKernelPackage degree D).kernel.sources ≈ 1 :=
  (crossedLinkBistochasticKernelPackage degree D).kernel.column_normalized
    target

end YMGap.Continuum.SU2SlabAllValenceCrossedSchurBistochasticKernel

#print axioms YMGap.Continuum.SU2SlabAllValenceCrossedSchurBistochasticKernel.unitFiniteBistochasticQKernel
#print axioms YMGap.Continuum.SU2SlabAllValenceCrossedSchurBistochasticKernel.crossedLinkBistochasticKernelPackage
#print axioms YMGap.Continuum.SU2SlabAllValenceCrossedSchurBistochasticKernel.crossedLinkBistochasticProductionSource
#print axioms YMGap.Continuum.SU2SlabAllValenceCrossedSchurBistochasticKernel.crossedLinkPointedBistochasticKernelPackage
#print axioms YMGap.Continuum.SU2SlabAllValenceCrossedSchurBistochasticKernel.crossedLinkBistochasticKernelPackage_weight_nonnegative
#print axioms YMGap.Continuum.SU2SlabAllValenceCrossedSchurBistochasticKernel.crossedLinkBistochasticKernelPackage_row_normalized
#print axioms YMGap.Continuum.SU2SlabAllValenceCrossedSchurBistochasticKernel.crossedLinkBistochasticProductionSource_row_normalized
#print axioms YMGap.Continuum.SU2SlabAllValenceCrossedSchurBistochasticKernel.crossedLinkBistochasticKernelPackage_column_normalized
