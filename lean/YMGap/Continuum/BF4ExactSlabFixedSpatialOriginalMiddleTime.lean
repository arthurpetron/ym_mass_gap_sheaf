/-
# Two-sided time limit of the original selected-chain middle observable

The original finiteValue is placed on extent width+(m+n), with a chain
starting at zero and the physical signed probe at time m. The geometric pin
identifies it with the actual middle ratio at distances m,n from its two
boundaries. Thus the original stream inherits the same explicit Cauchy
modulus and the same constructed CReal, with a full rectangular bound.

The spatial width, nome, probe and retained heat cutoff are fixed. This is
a scalar interior-time limit, not a stationary cylinder law, physical vacuum,
OS identification, cutoff removal or thermodynamic/continuum construction.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialOriginalMiddle
import YMGap.Continuum.BF4ExactSlabFixedSpatialMiddleTimeLimit

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialOriginalMiddleTime

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabTemporalSweep (FaceFactor sweptProduct)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialChainGeometry (chainIds chainIds_physical)
open YMGap.Continuum.BF4ExactSlabFixedSpatialProbe (placeProbes sourceProbe)
open YMGap.Continuum.BF4ExactSlabFixedSpatialProbeInterval (probeCap)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferMixingRate (mixRate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialMiddlePairing (middleRatio)
open YMGap.Continuum.BF4ExactSlabFixedSpatialOriginalMiddle
open YMGap.Continuum.BF4ExactSlabFixedSpatialMiddleTimeLimit
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4ExactSlabAllNomeFaceSetExpectation (finiteValue)

local infix:50 " ≈ " => Q'.eqv

/-- Literal original selected-chain expectation with the probe at its
interior slice. The ambient box is only an admissible encoding carrier. -/
def originalMiddleScalar {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width : Nat) (fs : List FaceFactor) (stage m n : Nat) : Q' :=
  finiteValue w hw0 hw1 (width+(m+n)) (chainIds (width+(m+n)) width 0 (m+n))
    (fun _ hi => chainIds_physical hi)
    (sweptProduct (width+(m+n)) 0 (placeProbes m fs)) stage

/-- All geometry guards follow from the displayed schedule; physical face
membership remains explicit. The original reciprocal partition is unchanged. -/
theorem originalMiddleScalar_pin {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width : Nat) (fs : List FaceFactor)
    (hfs : ∀ f, f ∈ fs → f.1 ∈ spatialFaces width) (stage m n : Nat) :
    originalMiddleScalar hw0 hw1 width fs stage m n ≈
      middleRatio hw0 hw1 (headCutoff w+stage) width (Nat.le_add_right _ _) m n
        (sourceProbe width fs) := by
  simpa only [Nat.zero_add] using
    (Q'.eqv_symm (middleRatio_originalFiniteValue hw0 hw1
      (width := width) (start := 0) (m := m) (n := n) (extent := width+(m+n))
      (Nat.le_add_right _ _) (by omega) fs hfs stage))

-- Match exact scalar APIs without unfolding the changing ambient action.
attribute [local irreducible] originalMiddleScalar middleRatio

/-- Cauchy witness for the original diagonal with both boundaries receding.
The witness retains the cutoff-independent geometric modulus as data. -/
def originalMiddleCauchy {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width : Nat) (fs : List FaceFactor)
    (hfs : ∀ f, f ∈ fs → f.1 ∈ spatialFaces width) (stage : Nat) :
    QCauchy (fun t => originalMiddleScalar hw0 hw1 width fs stage t t) where
  M := middleTimeModulus hw0 hw1 width fs
  bound := by
    intro epsilon he i j hi hj
    have h := (middleTimeCauchy hw0 hw1 (headCutoff w+stage) width
      (Nat.le_add_right _ _) fs).bound epsilon he i j hi hj
    have hip := originalMiddleScalar_pin hw0 hw1 width fs hfs stage i i
    have hjp := originalMiddleScalar_pin hw0 hw1 width fs hfs stage j j
    exact ⟨Q'.le_trans' _ _ _ (Q'.le_of_eqv hip)
        (Q'.le_trans' _ _ _ h.1
          (Q'.ge_of_eqv (Q'.add_eqv_congr_right _ _ epsilon hjp))),
      Q'.le_trans' _ _ _ (Q'.le_of_eqv hjp)
        (Q'.le_trans' _ _ _ h.2
          (Q'.ge_of_eqv (Q'.add_eqv_congr_right _ _ epsilon hip)))⟩

theorem originalMiddleCauchy_modulus {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width : Nat) (fs : List FaceFactor)
    (hfs : ∀ f, f ∈ fs → f.1 ∈ spatialFaces width) (stage : Nat) (epsilon : Q') :
    (originalMiddleCauchy hw0 hw1 width fs hfs stage).M epsilon =
      middleTimeModulus hw0 hw1 width fs epsilon := rfl

/-- The actual original diagonal reaches the SAME constructed interior
scalar; there is no separate supplied limit or new normalization. -/
theorem originalMiddle_converges {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width : Nat) (fs : List FaceFactor)
    (hfs : ∀ f, f ∈ fs → f.1 ∈ spatialFaces width) (stage : Nat) :
    ConvergesTo (fun t => ofQ' (originalMiddleScalar hw0 hw1 width fs stage t t))
      (middleTimeLimit hw0 hw1 (headCutoff w+stage) width (Nat.le_add_right _ _) fs) :=
  TrigAddCReal.convergesTo_congr_seq
    (s := fun t => ofQ' (middleRatio hw0 hw1 (headCutoff w+stage) width
      (Nat.le_add_right _ _) t t (sourceProbe width fs)))
    (fun t => SumOfSquares.Equiv_of_approx_eqv
      (fun _ => Q'.eqv_symm (originalMiddleScalar_pin hw0 hw1 width fs hfs stage t t)))
    (middleTime_converges hw0 hw1 (headCutoff w+stage) width (Nat.le_add_right _ _) fs)

/-- The original observable with arbitrary two boundary distances approaches
that same scalar, with an explicit representative threshold and geometric error. -/
theorem originalMiddle_approx_rectangular {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width : Nat) (fs : List FaceFactor)
    (hfs : ∀ f, f ∈ fs → f.1 ∈ spatialFaces width) (stage s m n k : Nat)
    (hsm : s ≤ m) (hsn : s ≤ n) (hsk : s ≤ k) :
    originalMiddleScalar hw0 hw1 width fs stage m n ≤
        (middleTimeLimit hw0 hw1 (headCutoff w+stage) width (Nat.le_add_right _ _) fs).approx k +
          mixRate hw0 hw1 width ^ s * ((probeCap fs + probeCap fs) + (probeCap fs + probeCap fs)) ∧
      (middleTimeLimit hw0 hw1 (headCutoff w+stage) width (Nat.le_add_right _ _) fs).approx k ≤
        originalMiddleScalar hw0 hw1 width fs stage m n +
          mixRate hw0 hw1 width ^ s * ((probeCap fs + probeCap fs) + (probeCap fs + probeCap fs)) := by
  have hb := middleTime_approx_rectangular hw0 hw1 (headCutoff w+stage) width
    (Nat.le_add_right _ _) fs s m n k hsm hsn hsk
  have he := originalMiddleScalar_pin hw0 hw1 width fs hfs stage m n
  exact ⟨Q'.le_trans' _ _ _ (Q'.le_of_eqv he) hb.1,
    Q'.le_trans' _ _ _ hb.2 (Q'.add_le_add_right _ _ _ (Q'.ge_of_eqv he))⟩

end YMGap.Continuum.BF4ExactSlabFixedSpatialOriginalMiddleTime

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialOriginalMiddleTime.originalMiddleScalar
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialOriginalMiddleTime.originalMiddleScalar_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialOriginalMiddleTime.originalMiddleCauchy
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialOriginalMiddleTime.originalMiddleCauchy_modulus
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialOriginalMiddleTime.originalMiddle_converges
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialOriginalMiddleTime.originalMiddle_approx_rectangular
