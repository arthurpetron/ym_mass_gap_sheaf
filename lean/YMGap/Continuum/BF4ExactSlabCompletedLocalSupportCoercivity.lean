/-
# Completed original Dirichlet coercivity for supplied local representatives

A caller supplies a Cauchy representative whose every polynomial term is
literally supported on the same finite link list. Dense centering preserves
that support and its supplied modulus. The support-only dense coefficient
then passes to the SAME original completed full-action carrier. No local
representative for an arbitrary completed vector is selected or asserted.
-/

import YMGap.Continuum.BF4ExactSlabCompletedFiniteVolumeCoercivity
import YMGap.Continuum.BF4ExactSlabLocalSupportCoercivity

namespace YMGap.Continuum.BF4ExactSlabCompletedLocalSupportCoercivity

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.GNSModulusCompletion
open YMGap.Continuum.GNSProjectionSweep
open YMGap.Continuum.GNSProjectionSweep.Family
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabStarFullActionProbe
open YMGap.Continuum.BF4ExactSlabConditionalCovariance
open YMGap.Continuum.BF4ExactSlabConditionalCenteredCompletion
open YMGap.Continuum.BF4ExactSlabConditionalSweep
open YMGap.Continuum.BF4ExactSlabEightLayerCone
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabLocalSupportVariance
open YMGap.Continuum.BF4ExactSlabLocalSupportCoercivity
open YMGap.Continuum.BF4ExactSlabCompletedFiniteVolumeCoercivity
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (extent stage : Nat) (S : List Z4Link) (size : Nat) (hsize : S.length ≤ size)

local notation "K" => headCutoff w + stage
local notation "hK" => Nat.le_add_right (headCutoff w) stage
local notation "F" => fullData hw0 hw1 K extent hK
local notation "P" => projections hw0 hw1 K extent hK
local notation "U" => unit hw0 hw1 extent stage

include hsize

/-- The support-only coefficient extends to a completed vector when its
explicit Cauchy representative is termwise local and its class is centered
for the original full action. The residuals remain the actual completed
conditional residuals. -/
theorem completed_local_coercivity (X : CauchyGNS F)
    (hlocal : ∀ n, LinkLocal extent S (X.seq n).val)
    (hcenter : (F).cinnerCompl (Quotient.mk (cauchySetoid F) X)
      (embedV F U) = CReal.RCzero) :
    CReal.RCle
      (CReal.RCscale (supportRatio hw0 hw1 size)
        (normSq (Quotient.mk (cauchySetoid F) X)))
      ((P).finalEnergy (schedule extent)
        (Quotient.mk (cauchySetoid F) X)) := by
  let Y := centeredCauchy hw0 hw1 extent stage X
  have hYlocal (n : Nat) : LinkLocal extent S (Y.seq n).val :=
    centered_local hw0 hw1 extent stage S (X.seq n) (hlocal n)
  have hY := completed_of_termwise_bound hw0 hw1 extent stage
    (supportRatio hw0 hw1 size) Y
    (fun n => dense_local_coercivity hw0 hw1 K extent hK S size hsize
      (Y.seq n) (hYlocal n)
      (centeredCauchy_term_centered hw0 hw1 extent stage X n))
  have hsame := centeredCauchy_same_class hw0 hw1 extent stage X hcenter
  rw [hsame] at hY
  exact hY

end YMGap.Continuum.BF4ExactSlabCompletedLocalSupportCoercivity

#print axioms YMGap.Continuum.BF4ExactSlabCompletedLocalSupportCoercivity.completed_local_coercivity
