/-
# The one-sided time limit of the original selected-chain scalar

At time length steps the ambient extent is literally width+steps, the lower
endpoint is at time zero, and the upper endpoint is empty. The scalar is the
pre-existing original finiteValue with its original selected action and
reciprocal partition normalization. The exact carrier pin identifies this
varying-extent stream with the already constructed source-probe mass ratio.

The inherited rational modulus and convergence therefore apply to this
original stream. Width, nome, probe and heat-cutoff stage remain fixed as
time grows. Only this one-sided boundary scalar limit is asserted: there is
no stationary law, two-sided bulk limit, OS identification, physical mass
gap, cutoff removal or spatial-volume uniformity here.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialBoundaryTimeLimit
import YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBracketOriginalScalar

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialOriginalTimeLimit

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabTemporalSweep (FaceFactor)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialChainGeometry (chainIds chainIds_physical)
open YMGap.Continuum.BF4ExactSlabFixedSpatialIterationLimit (endpointInsertion)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBracketDecay (sourceProbeMassRatio)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBracketOriginalScalar
open YMGap.Continuum.BF4ExactSlabFixedSpatialBoundaryTimeLimit
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4ExactSlabAllNomeFaceSetExpectation (finiteValue)

local infix:50 " ≈ " => Q'.eqv

/-- The original finite-chain expectation on an explicit admissible growing
ambient box. Only the selected fixed-width chain carries action factors. -/
def originalTimeScalar {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width : Nat) (fs : List FaceFactor) (stage steps : Nat) : Q' :=
  finiteValue w hw0 hw1 (width+steps) (chainIds (width+steps) width 0 steps)
    (fun _ hi => chainIds_physical hi)
    (endpointInsertion (width+steps) 0 steps fs []) stage

/-- Exact equality with the same compact normalized iterate, retaining the
original physical face-membership guard. Both geometry guards are proved
from the displayed ambient schedule, including at zero steps or zero width. -/
theorem originalTimeScalar_pin {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width : Nat) (fs : List FaceFactor)
    (hfs : ∀ f, f ∈ fs → f.1 ∈ spatialFaces width) (stage steps : Nat) :
    originalTimeScalar hw0 hw1 width fs stage steps ≈
      sourceProbeMassRatio hw0 hw1 (headCutoff w+stage) width
        (Nat.le_add_right _ _) steps fs := by
  exact Q'.eqv_symm (sourceProbeMassRatio_originalFiniteValue hw0 hw1
    (width := width) (start := 0) (steps := steps) (extent := width+steps)
    (Nat.le_add_right _ _) (by omega) fs hfs stage)

-- Use the exact scalar pin rather than unfolding the growing action or Haar sums.
attribute [local irreducible] originalTimeScalar sourceProbeMassRatio

/-- A Type-level Cauchy witness for the literal original varying-extent
stream, using the already constructed boundary-time modulus without loss. -/
def originalTimeCauchy {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width : Nat) (fs : List FaceFactor)
    (hfs : ∀ f, f ∈ fs → f.1 ∈ spatialFaces width) (stage : Nat) :
    QCauchy (originalTimeScalar hw0 hw1 width fs stage) where
  M := (boundaryTimeCauchy hw0 hw1 (headCutoff w+stage) width
    (Nat.le_add_right _ _) fs).M
  bound := by
    intro epsilon he i j hi hj
    have h := (boundaryTimeCauchy hw0 hw1 (headCutoff w+stage) width
      (Nat.le_add_right _ _) fs).bound epsilon he i j hi hj
    have hip := originalTimeScalar_pin hw0 hw1 width fs hfs stage i
    have hjp := originalTimeScalar_pin hw0 hw1 width fs hfs stage j
    exact ⟨Q'.le_trans' _ _ _ (Q'.le_of_eqv hip)
        (Q'.le_trans' _ _ _ h.1
          (Q'.ge_of_eqv (Q'.add_eqv_congr_right _ _ epsilon hjp))),
      Q'.le_trans' _ _ _ (Q'.le_of_eqv hjp)
        (Q'.le_trans' _ _ _ h.2
          (Q'.ge_of_eqv (Q'.add_eqv_congr_right _ _ epsilon hip)))⟩

/-- The original stream inherits the explicit geometric modulus, which
does not depend on the late heat-cutoff stage. -/
theorem originalTimeCauchy_modulus {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width : Nat) (fs : List FaceFactor)
    (hfs : ∀ f, f ∈ fs → f.1 ∈ spatialFaces width) (stage : Nat) (epsilon : Q') :
    (originalTimeCauchy hw0 hw1 width fs hfs stage).M epsilon =
      boundaryTimeModulus hw0 hw1 width fs epsilon := rfl

/-- The genuinely original selected-chain scalar converges to the SAME
constructed one-sided boundary limit, not a separately supplied limit. -/
theorem originalTime_converges {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width : Nat) (fs : List FaceFactor)
    (hfs : ∀ f, f ∈ fs → f.1 ∈ spatialFaces width) (stage : Nat) :
    ConvergesTo (fun steps => ofQ' (originalTimeScalar hw0 hw1 width fs stage steps))
      (boundaryTimeLimit hw0 hw1 (headCutoff w+stage) width (Nat.le_add_right _ _) fs) :=
  TrigAddCReal.convergesTo_congr_seq
    (s := fun steps => ofQ' (sourceProbeMassRatio hw0 hw1 (headCutoff w+stage) width
      (Nat.le_add_right _ _) steps fs))
    (fun steps => SumOfSquares.Equiv_of_approx_eqv
      (fun _ => Q'.eqv_symm (originalTimeScalar_pin hw0 hw1 width fs hfs stage steps)))
    (boundaryTime_converges hw0 hw1 (headCutoff w+stage) width (Nat.le_add_right _ _) fs)

end YMGap.Continuum.BF4ExactSlabFixedSpatialOriginalTimeLimit

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialOriginalTimeLimit.originalTimeScalar
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialOriginalTimeLimit.originalTimeScalar_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialOriginalTimeLimit.originalTimeCauchy
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialOriginalTimeLimit.originalTimeCauchy_modulus
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialOriginalTimeLimit.originalTime_converges
