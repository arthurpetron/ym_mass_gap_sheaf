/-
# Original separated covariance with a constructed finite-volume coefficient

The completed coercivity producer supplies the actual auxiliary reverse
energy at c=2+2*delta/625>2. The scalar Chebyshev denominator is positive by
its recurrence. Thus no analytic reverse-energy premise remains here.

Both original normalized variances and the original covariance are retained.
The coefficient depends on nome and ALL physical faces, though not on the
late heat cutoff. This is not spatially/spacing-uniform control or an OS
time/Hamiltonian/continuum mass gap.
-/

import YMGap.Continuum.BF4ExactSlabFiniteVolumeReverseEnergy
import YMGap.Continuum.BF4ExactSlabChebyshevCovarianceBound
import YMGap.Continuum.ChebyshevAboveOne

namespace YMGap.Continuum.BF4ExactSlabFiniteVolumeChebyshevCovariance

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabStarFullActionProbe
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabEightLayerCone
open YMGap.Continuum.BF4ExactSlabConditionalCovariance
open YMGap.Continuum.BF4ExactSlabSweepChebyshev
open YMGap.Continuum.BF4ExactSlabFiniteVolumeReverseEnergy
open YMGap.Continuum.BF4ExactSlabConnectedFaceResponse (finiteCovariance)
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

private def rat (q : Q') : RC := Quotient.mk crealSetoid (ofQ' q)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (extent stage : Nat)

local notation "K" => headCutoff w + stage
local notation "hK" => Nat.le_add_right (headCutoff w) stage
local notation "F" => fullData hw0 hw1 K extent hK
local notation "c" => reverseCoefficient hw0 hw1 extent
local notation "ids" => slabPhysicalFaceEdges extent
local notation "physical" => (fun (id : Nat) (h : id ∈ ids) => h)

/-- The concrete strict coefficient supplies its own denominator guard. -/
theorem denominator_positive (n : Nat) : (0 : Q') < Cheb.T n (c + (-(1 : Q'))) := by
  apply ChebyshevAboveOne.T_positive
  exact Q'.le_trans' _ _ _
    (by decide : (1 : Q') ≤ (2 : Q') + (-(1 : Q')))
    (Q'.add_le_add_right _ _ (-(1 : Q'))
      (Q'.le_of_lt (reverseCoefficient_gt_two hw0 hw1 extent)))

/-- Explicit rational reciprocal of the actual Chebyshev normalizer.
No heat-cutoff argument occurs in this coefficient. -/
def covarianceFactor (n : Nat) : Q' :=
  Q'.recipPos (Cheb.T n (c + (-(1 : Q')))) (denominator_positive hw0 hw1 extent n)

/-- The original finite covariance bound, now without an assumed
reverse-energy estimate or Chebyshev positivity premise. -/
theorem finiteCovariance_sq_bound (n : Nat)
    (support testSupport : List Z4Link) (p q : (F).V)
    (hp : LinkLocal extent support p.val)
    (hq : LinkLocal extent testSupport q.val)
    (hsep : LinksDisjoint (grow extent (16*n) support) testSupport) :
    RCle
      (RCmul
        (rat (finiteCovariance w hw0 hw1 extent ids physical p.val q.val stage))
        (rat (finiteCovariance w hw0 hw1 extent ids physical p.val q.val stage)))
      (RCscale (covarianceFactor hw0 hw1 extent n * covarianceFactor hw0 hw1 extent n)
        (RCmul
          (rat (finiteCovariance w hw0 hw1 extent ids physical p.val p.val stage))
          (rat (finiteCovariance w hw0 hw1 extent ids physical q.val q.val stage)))) := by
  exact BF4ExactSlabChebyshevCovarianceBound.finiteCovariance_sq_bound
    hw0 hw1 extent stage c (reverseCoefficient_nonnegative hw0 hw1 extent) n
    (denominator_positive hw0 hw1 extent n) support testSupport p q hp hq hsep
    (coupled_auxiliary_reverse_energy hw0 hw1 extent stage
      (embedV F (centered hw0 hw1 extent stage p))
      (completed_centered_unit hw0 hw1 extent stage p) n)

#print axioms denominator_positive
#print axioms covarianceFactor
#print axioms finiteCovariance_sq_bound

end YMGap.Continuum.BF4ExactSlabFiniteVolumeChebyshevCovariance
