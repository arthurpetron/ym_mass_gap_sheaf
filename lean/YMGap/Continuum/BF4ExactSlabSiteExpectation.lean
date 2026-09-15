/-
# Normalized site reflection positivity after ORIGINAL heat-cutoff removal

At every finite cutoff the full original site-reflected numerator is
nonnegative and its SAME partition is strictly positive under the explicit
small-nome guards. The constructed normalized cutoff limit therefore retains
site reflection positivity for every supported one-sided polynomial.

Only the original insertion p is held fixed while the cutoff varies.
The conditional polynomial C(p*L_K) remains inside the finite proof; it is
not passed through a fixed-observable limit or asserted to be an OS state.
The expectation and both cutoff/representative moduli come from the generic
face-set construction, whose odd specialization equals the existing law.

This removes the heat cutoff at fixed even volume. Comparing that volume
family to the existing thermodynamic one-step pairing remains open, as do
completed T1/root identification, arbitrary-state transfer range, time zero,
physical mass normalization and the continuum/all-group Clay target.
-/

import YMGap.Continuum.BF4ExactSlabFaceSetExpectation
import YMGap.Continuum.BF4ExactSlabSiteHeatAction

namespace YMGap.Continuum.BF4ExactSlabSiteExpectation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactSlabVacuumReflection
open YMGap.Continuum.BF4ExactSlabSiteHaarFactorization
open YMGap.Continuum.BF4ExactSlabSiteConditionalSquare
open YMGap.Continuum.BF4ExactSlabSiteHeatAction
open YMGap.Continuum.BF4ExactSlabFaceSetExpectation
open YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeCertificate
open YMGap.Continuum.BF4ExactSlabSmallNomeHaarComparison
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.QuaternionHaarCharacterInterval
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenCrossPlaneGeometry

variable (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (radius : Nat) (p : RatPoly) (hp : OneSided radius p)
  (hs : SupportedQuaternionBlocks (blockCount radius) p)

local notation "extent" => adjacentEvenExtent radius
local notation "faces" => slabPhysicalFaceEdges extent
local notation "insertion" => polyMul (reflectCorrectedSlabPolynomial extent p) p

include hp hs in
theorem finite_site_nonnegative (K : Nat) :
    (0 : Q') ≤ finiteValue w hw0 hw1 hsmall hd extent faces (fun _ h => h) insertion K := by
  unfold finiteValue
  apply Q'.mul_nonneg
  · exact fullAction_nonnegative (Q'.le_of_lt hw0) (Q'.le_of_lt hw1) hsmall (Q'.le_of_lt hd) K radius p hp hs
  · exact Q'.le_of_lt (PositiveRationalCauchyReciprocal.term_pos _ _ _ K)

include hp hs in
/-- Same full action and denominator; only the original p is fixed in this limit. -/
theorem site_nonnegative :
    leEv (ofQ' 0) (expectation w hw0 hw1 hsmall hd extent faces (fun _ h => h) insertion) :=
  leEv_of_convergesTo_le (convergesTo_const _)
    (finite_converges w hw0 hw1 hsmall hd extent faces (fun _ h => h) insertion)
    (fun K => leEv_ofQ'_of_approx_ge
      (fun _ => finite_site_nonnegative w hw0 hw1 hsmall hd radius p hp hs K))

include hp hs in
theorem existingNome_site_nonnegative :
    leEv (ofQ' 0) (expectation nome nome_pos nome_lt_one existingNome_guards.1 existingNome_guards.2
      extent faces (fun _ h => h) insertion) :=
  site_nonnegative nome nome_pos nome_lt_one existingNome_guards.1 existingNome_guards.2 radius p hp hs

end YMGap.Continuum.BF4ExactSlabSiteExpectation

#print axioms YMGap.Continuum.BF4ExactSlabSiteExpectation.finite_site_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabSiteExpectation.site_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabSiteExpectation.existingNome_site_nonnegative
