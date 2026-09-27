/-
# Finite rational-test consumer for the original covariance

A successful explicit rational margin test for the actual completed
Chebyshev auxiliary supplies the reverse-energy premise of the existing
finite covariance theorem. This file does not show that the test succeeds
at any parameter, or uniformly over cutoff, volume, or spacing.
-/

import YMGap.Continuum.BF4ExactSlabChebyshevFiniteTest
import YMGap.Continuum.BF4ExactSlabChebyshevCovarianceBound

namespace YMGap.Continuum.BF4ExactSlabChebyshevFiniteCovariance

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.GNSProjectionSweep
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabStarFullActionProbe
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabEightLayerCone
open YMGap.Continuum.BF4ExactSlabConditionalSweep
open YMGap.Continuum.BF4ExactSlabConditionalCovariance
open YMGap.Continuum.BF4ExactSlabSweepChebyshev
open YMGap.Continuum.BF4ExactSlabChebyshevFiniteTest
open YMGap.Continuum.BF4ExactSlabChebyshevCovarianceBound
open YMGap.Continuum.BF4ExactSlabConnectedFaceResponse (finiteCovariance)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

private def rat (q : Q') : RC := Quotient.mk crealSetoid (ofQ' q)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (extent stage : Nat)

local notation "K" => headCutoff w + stage
local notation "hK" => Nat.le_add_right (headCutoff w) stage
local notation "F" => fullData hw0 hw1 K extent hK
local notation "P" => projections hw0 hw1 K extent hK
local notation "B" => Family.balanced P (schedule extent)
local notation "W" => Family.sweep P (schedule extent)
local notation "ids" => slabPhysicalFaceEdges extent
local notation "physical" => (fun (id : Nat) (h : id ∈ ids) => h)

/-- The SAME original finite covariance bound follows when its one required
auxiliary reverse-energy estimate is certified by the displayed finite
rational comparison. No success or scaling-uniformity is claimed. -/
theorem finiteCovariance_sq_bound_of_finite_test (c : Q') (hc : (0 : Q') ≤ c)
    (n : Nat) (ht : (0 : Q') < Cheb.T n (c + (-(1 : Q'))))
    (support testSupport : List Z4Link) (p q : (F).V)
    (hp : LinkLocal extent support p.val)
    (hq : LinkLocal extent testSupport q.val)
    (hsep : LinksDisjoint (grow extent (16*n) support) testSupport)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (htest : epsilon ≤ marginValue hw0 hw1 K extent hK c
      (constCauchy F (centered hw0 hw1 extent stage p)) n epsilon) :
    RCle
      (RCmul
        (rat (finiteCovariance w hw0 hw1 extent ids physical p.val q.val stage))
        (rat (finiteCovariance w hw0 hw1 extent ids physical p.val q.val stage)))
      (RCscale
        ((Q'.recipPos (Cheb.T n (c + (-(1 : Q')))) ht) *
          (Q'.recipPos (Cheb.T n (c + (-(1 : Q')))) ht))
        (RCmul
          (rat (finiteCovariance w hw0 hw1 extent ids physical p.val p.val stage))
          (rat (finiteCovariance w hw0 hw1 extent ids physical q.val q.val stage)))) := by
  have hrev :
      let x := embedV F (centered hw0 hw1 extent stage p)
      let u := (coupled hw0 hw1 K extent hK c x n).2
      RCle (RCscale c (normSq (B u))) (RCscale 2 (normSq (W u))) :=
    reverse_energy_of_finite_test hw0 hw1 K extent hK c
      (constCauchy F (centered hw0 hw1 extent stage p)) n epsilon hepsilon htest
  exact finiteCovariance_sq_bound hw0 hw1 extent stage
    c hc n ht support testSupport p q hp hq hsep hrev

#print axioms finiteCovariance_sq_bound_of_finite_test

end YMGap.Continuum.BF4ExactSlabChebyshevFiniteCovariance
