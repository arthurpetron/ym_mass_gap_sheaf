/-
# Positivity of the original finite conditional covariance diagonal

The diagonal finite variance is the existing normalized pairing of the
actual centered vector on the original completed full-action carrier.
-/

import YMGap.Continuum.BF4ExactSlabConditionalCovariance
import YMGap.Continuum.RCScaleClose
import YMGap.Continuum.GNSDynamics
import YMGap.Continuum.RCCauchySchwarz

namespace YMGap.Continuum.BF4ExactSlabConditionalVariancePositive

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.BF4ExactSlabConditionalCovariance
open YMGap.Continuum.BF4ExactSlabConnectedFaceResponse
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabAllNomeFaceSetReciprocal
open YMGap.Continuum.BF4ExactSlabStarFullActionProbe
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (extent stage : Nat)

local notation "K" => headCutoff w + stage
local notation "hK" => Nat.le_add_right (headCutoff w) stage
local notation "F" => fullData hw0 hw1 K extent hK
local notation "ids" => slabPhysicalFaceEdges extent
local notation "physical" => (fun (id : Nat) (h : id ∈ ids) => h)

/-- Products of nonnegative completed real scalars remain nonnegative. -/
theorem product_nonnegative {a b : RC} (ha : RCnonneg a) (hb : RCnonneg b) :
    RCnonneg (RCmul a b) := by
  refine Quotient.inductionOn₂ a b ?_ ha hb
  intro A B hA hB
  exact CReal.mul_nonneg hA hB

/-- The ORIGINAL normalized finite covariance has nonnegative diagonal.
The proof uses its exact completed-covariance pin and the positive reciprocal
of the original finite partition; no replacement normalization is made. -/
theorem finiteVariance_nonnegative (p : (F).V) :
    RCnonneg (Quotient.mk crealSetoid (ofQ'
      (finiteCovariance w hw0 hw1 extent ids physical p.val p.val stage))) := by
  have hrpos : (0 : Q') < inversePartition hw0 hw1 extent stage := by
    unfold inversePartition BF4ExactSlabAllNomeFaceSetReciprocal.reciprocalTerm
    exact Q'.recipPos_pos _ _
  have hr : (0 : Q') ≤ inversePartition hw0 hw1 extent stage :=
    Q'.le_of_lt hrpos
  have hdiag := (F).cinner_self_nonneg
    (embedV F (centered hw0 hw1 extent stage p))
  have hscaled := RCscale_mono hr hdiag
  rw [RCscale_RCzero] at hscaled
  rw [← completed_covariance hw0 hw1 extent stage p p] at hscaled
  exact hscaled

#print axioms product_nonnegative
#print axioms finiteVariance_nonnegative

end YMGap.Continuum.BF4ExactSlabConditionalVariancePositive
