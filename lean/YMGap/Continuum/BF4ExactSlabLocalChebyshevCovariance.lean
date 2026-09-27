/-
# Original finite covariance from a support-budgeted auxiliary estimate

The actual completed auxiliary is built from the original centered local
polynomial. Its constructed literal-local representative supplies the
reverse-energy inequality at degree n+1. The reciprocal Chebyshev factor
therefore depends on nome, initial support size and degree, not finite
extent or late heat cutoff. The support budget still grows with degree;
no thermodynamic, changing-nome, OS-time or continuum gap follows.
-/

import YMGap.Continuum.BF4ExactSlabLocalAuxiliaryCoercivity
import YMGap.Continuum.BF4ExactSlabChebyshevCovarianceBound
import YMGap.Continuum.ChebyshevAboveOne

namespace YMGap.Continuum.BF4ExactSlabLocalChebyshevCovariance

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
open YMGap.Continuum.BF4ExactSlabLocalCauchyRepresentative
open YMGap.Continuum.BF4ExactSlabLocalAuxiliaryCoercivity
open YMGap.Continuum.BF4ExactSlabConnectedFaceResponse (finiteCovariance)
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

private def rat (q : Q') : RC := Quotient.mk crealSetoid (ofQ' q)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))

/-- Positivity at the actual degree n+1, with no extent or heat-cutoff
argument in the denominator. -/
theorem denominator_positive (size n : Nat) :
    (0 : Q') < Cheb.T (n+1)
      (localCoefficient hw0 hw1 size n + (-(1 : Q'))) := by
  apply ChebyshevAboveOne.T_positive
  exact Q'.le_trans' _ _ _
    (by decide : (1 : Q') ≤ (2 : Q') + (-(1 : Q')))
    (Q'.add_le_add_right _ _ (-(1 : Q'))
      (Q'.le_of_lt (localCoefficient_gt_two hw0 hw1 size n)))

/-- Explicit original-covariance factor, depending only on nome, initial
support-size budget and degree. -/
def covarianceFactor (size n : Nat) : Q' :=
  Q'.recipPos
    (Cheb.T (n+1) (localCoefficient hw0 hw1 size n + (-(1 : Q'))))
    (denominator_positive hw0 hw1 size n)

variable (extent stage : Nat)

local notation "K" => headCutoff w + stage
local notation "hK" => Nat.le_add_right (headCutoff w) stage
local notation "F" => fullData hw0 hw1 K extent hK
local notation "ids" => slabPhysicalFaceEdges extent
local notation "physical" => (fun (id : Nat) (h : id ∈ ids) => h)

/-- The SAME original diagonal finite covariances control the separated
mixed covariance. Only the supplied literal test support and the computed
degree-dependent cone enter the coefficient and separation premise. -/
theorem finiteCovariance_sq_bound (n : Nat)
    (support testSupport : List Z4Link) (p q : (F).V)
    (hp : LinkLocal extent support p.val)
    (hq : LinkLocal extent testSupport q.val)
    (hsep : LinksDisjoint (grow extent (16*(n+1)) support) testSupport) :
    RCle
      (RCmul
        (rat (finiteCovariance w hw0 hw1 extent ids physical p.val q.val stage))
        (rat (finiteCovariance w hw0 hw1 extent ids physical p.val q.val stage)))
      (RCscale
        (covarianceFactor hw0 hw1 support.length n *
          covarianceFactor hw0 hw1 support.length n)
        (RCmul
          (rat (finiteCovariance w hw0 hw1 extent ids physical p.val p.val stage))
          (rat (finiteCovariance w hw0 hw1 extent ids physical q.val q.val stage)))) := by
  let seed := centered hw0 hw1 extent stage p
  let x := embedV F seed
  have hseed : LinkLocal extent support seed.val :=
    centered_local hw0 hw1 extent stage support p hp
  have hrep : LocalRep hw0 hw1 K extent hK support x :=
    LocalRep.embed hw0 hw1 K extent hK support seed hseed
  have hlocalized : Localized hw0 hw1 K extent hK support x :=
    localized_embed hw0 hw1 K extent hK support seed hseed
  have hcenter : Centered hw0 hw1 K extent hK x :=
    completed_centered_unit hw0 hw1 extent stage p
  exact BF4ExactSlabChebyshevCovarianceBound.finiteCovariance_sq_bound
    hw0 hw1 extent stage
    (localCoefficient hw0 hw1 support.length n)
    (localCoefficient_nonnegative hw0 hw1 support.length n)
    (n+1) (denominator_positive hw0 hw1 support.length n)
    support testSupport p q hp hq hsep
    (auxiliary_reverse_energy hw0 hw1 extent stage n support x
      hrep hlocalized hcenter)

end YMGap.Continuum.BF4ExactSlabLocalChebyshevCovariance

#print axioms YMGap.Continuum.BF4ExactSlabLocalChebyshevCovariance.denominator_positive
#print axioms YMGap.Continuum.BF4ExactSlabLocalChebyshevCovariance.covarianceFactor
#print axioms YMGap.Continuum.BF4ExactSlabLocalChebyshevCovariance.finiteCovariance_sq_bound
