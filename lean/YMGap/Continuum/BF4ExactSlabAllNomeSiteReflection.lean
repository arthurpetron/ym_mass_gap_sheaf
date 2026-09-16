/-
# Original site reflection positivity at every rational nome

The existing fullAction_square keeps all original even-slab action factors
and the shared fixed-slice links. The actual fixedHeat has a positive
certificate for every 0 < w < 1 once K >= headCutoff(w), so the original
site-reflected numerator is nonnegative at each such cutoff.

The SAME all-nome normalized face-set expectation inherits this positivity
after cutoff removal at fixed even volume. Only the original supported
one-sided polynomial is fixed in the limit; its cutoff-dependent dressed
conditional square stays inside the finite proof.

This supplies no thermodynamic pairing identification, geometric one-step
operator, centered decay, physical mass normalization, or continuum gap.
-/

import YMGap.Continuum.BF4ExactSlabSiteHeatAction
import YMGap.Continuum.BF4ExactSlabAllNomeFaceSetExpectation

namespace YMGap.Continuum.BF4ExactSlabAllNomeSiteReflection

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactSlabVacuumReflection
open YMGap.Continuum.BF4ExactSlabSiteHaarFactorization
open YMGap.Continuum.BF4ExactSlabSiteConditionalSquare
open YMGap.Continuum.BF4ExactSlabSiteHeatAction
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabAllNomeFaceSetExpectation
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenCrossPlaneGeometry
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenJointFaceSlabFubini

/-- Every original fixed face is certified at the same explicit cutoff. -/
def fixedHeatCertificate {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K radius : Nat) (hK : headCutoff w ≤ K) :
    Certificate (blockCount radius) (fixedHeat w K radius) :=
  headProduct_certificate hw0 hw1 K _ hK _
    (fun _ hi => (mem_adjacentEvenFixedFaceIds.mp hi).1)

/-- Finite site reflection positivity for the FULL original heat action,
without the old small-nome guards. -/
theorem fullAction_nonnegative {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K radius : Nat) (hK : headCutoff w ≤ K) (p : RatPoly)
    (hp : OneSided radius p) (hs : SupportedQuaternionBlocks (blockCount radius) p) :
    (0 : Q') ≤ quaternionHaar (blockCount radius)
      (polyMul (polyMul (reflectCorrectedSlabPolynomial (adjacentEvenExtent radius) p) p)
        (fullHeat w K radius)) :=
  Q'.le_trans' _ _ _
    ((fixedHeatCertificate hw0 hw1 K radius hK).square_insertion_nonnegative _
      (conditional_supported radius _ (hp.mul (lowerHeat_oneSided w K radius))))
    (Q'.ge_of_eqv (fullAction_square w K radius p hp hs))

variable (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (radius : Nat) (p : RatPoly) (hp : OneSided radius p)
  (hs : SupportedQuaternionBlocks (blockCount radius) p)

local notation "extent" => adjacentEvenExtent radius
local notation "faces" => slabPhysicalFaceEdges extent
local notation "insertion" => polyMul (reflectCorrectedSlabPolynomial extent p) p

include hp hs in
/-- Original numerator and SAME positive denominator at cutoff headCutoff(w)+n. -/
theorem finite_site_nonnegative (n : Nat) :
    (0 : Q') ≤ finiteValue w hw0 hw1 extent faces (fun _ h => h) insertion n := by
  unfold finiteValue
  apply Q'.mul_nonneg
  · exact fullAction_nonnegative hw0 hw1 (headCutoff w + n) radius
      (Nat.le_add_right _ _) p hp hs
  · exact Q'.le_of_lt (PositiveRationalCauchyReciprocal.term_pos _ _ _ n)

include hp hs in
/-- Cutoff-limit site reflection positivity for the existing all-nome original
law at fixed volume; the changing conditional square is not a limit insertion. -/
theorem site_nonnegative :
    leEv (ofQ' 0) (expectation w hw0 hw1 extent faces (fun _ h => h) insertion) :=
  leEv_of_convergesTo_le (convergesTo_const _)
    (finite_converges w hw0 hw1 extent faces (fun _ h => h) insertion)
    (fun n => leEv_ofQ'_of_approx_ge
      (fun _ => finite_site_nonnegative w hw0 hw1 radius p hp hs n))

end YMGap.Continuum.BF4ExactSlabAllNomeSiteReflection

#print axioms YMGap.Continuum.BF4ExactSlabAllNomeSiteReflection.fixedHeatCertificate
#print axioms YMGap.Continuum.BF4ExactSlabAllNomeSiteReflection.fullAction_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabAllNomeSiteReflection.finite_site_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabAllNomeSiteReflection.site_nonnegative
