/-
# Cauchy--Schwarz for the FULL original site-reflected heat action

The mixed conditional identity identifies the original form with a
weighted boundary pairing. The fixed-face weight has the existing concrete
square certificate. Sharp weighted Cauchy--Schwarz thus bounds the original
mixed numerator by its two ORIGINAL site diagonals. The same partition
normalizes all three quantities and the inequality passes through the old
heat-cutoff limits. No auxiliary probability law or density premise enters.

The small-nome guards are explicit. This finite-volume inequality is not
yet a completed transfer-relative bound, time-zero theorem or Clay closure.
-/

import YMGap.Continuum.BF4ExactSlabSiteMixedSquare
import YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz
import YMGap.Continuum.BF4ExactSlabFaceSetExpectation
import YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz

namespace YMGap.Continuum.BF4ExactSlabSiteCauchySchwarz

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactSlabVacuumReflection
open YMGap.Continuum.BF4ExactSlabSiteHaarFactorization
open YMGap.Continuum.BF4ExactSlabSiteConditionalSquare
open YMGap.Continuum.BF4ExactSlabSiteHeatAction
open YMGap.Continuum.BF4ExactSlabSiteMixedSquare
open YMGap.Continuum.BF4ExactSlabFaceSetExpectation
open YMGap.Continuum.BF4ExactSlabSmallNomeHaarComparison
open YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz
open YMGap.Continuum.QuaternionHaarCharacterInterval
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenCrossPlaneGeometry

local infix:50 " ≈ " => Q'.eqv

def siteInsertion (radius : Nat) (p q : RatPoly) : RatPoly :=
  polyMul (reflectCorrectedSlabPolynomial (adjacentEvenExtent radius) p) q

def rawForm (w : Q') (K radius : Nat) (p q : RatPoly) : Q' :=
  quaternionHaar (blockCount radius) (polyMul (siteInsertion radius p q) (fullHeat w K radius))

private theorem mul_congr {a b c d : Q'} (h : a ≈ b) (h' : c ≈ d) : a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h) (Q'.mul_eqv_congr_left _ _ _ h')

theorem raw_cauchySchwarz {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w ≤ 1)
    (K radius : Nat) (p q : RatPoly) (lp : OneSided radius p) (lq : OneSided radius q)
    (hp : SupportedQuaternionBlocks (blockCount radius) p) (hq : SupportedQuaternionBlocks (blockCount radius) q) :
    rawForm w K radius p q * rawForm w K radius p q ≤ rawForm w K radius p p * rawForm w K radius q q := by
  have h := fullAction_pair w K radius p q lp lq hp hq
  have hP := fullAction_pair w K radius p p lp lp hp hp
  have hQ := fullAction_pair w K radius q q lq lq hq hq
  have hcs := weighted_cauchySchwarz (blockCount radius) (fixedHeat w K radius) _ _
    (fixedHeatCertificate hw0 hw1 hsmall hd K radius)
    (conditional_supported radius _ (lp.mul (lowerHeat_oneSided w K radius)))
    (conditional_supported radius _ (lq.mul (lowerHeat_oneSided w K radius)))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (mul_congr h h))
    (Q'.le_trans' _ _ _ hcs (Q'.ge_of_eqv (mul_congr hP hQ)))

private theorem normalize_product (a b r : Q') : (a*r)*(b*r) ≈ (a*b)*(r*r) :=
  RingNormaliser.poly_identity_of_normal_eq
    (.mul (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 2)))
    (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 2))) (by decide)
    (fun | 0 => a | 1 => b | _ => r)

variable (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (radius : Nat) (p q : RatPoly) (lp : OneSided radius p) (lq : OneSided radius q)
  (hp : SupportedQuaternionBlocks (blockCount radius) p) (hq : SupportedQuaternionBlocks (blockCount radius) q)

local notation "extent" => adjacentEvenExtent radius
local notation "faces" => slabPhysicalFaceEdges extent
local notation "F" => finiteValue w hw0 hw1 hsmall hd extent faces (fun _ hi => hi)
local notation "E" => expectation w hw0 hw1 hsmall hd extent faces (fun _ hi => hi)

include lp lq hp hq in
/-- The same-cutoff original partition scales both diagonals and the mixed term. -/
theorem finite_cauchySchwarz (K : Nat) :
    F (siteInsertion radius p q) K * F (siteInsertion radius p q) K ≤
      F (siteInsertion radius p p) K * F (siteInsertion radius q q) K := by
  unfold finiteValue
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (normalize_product _ _ _)) ?_
  exact Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ _
      (raw_cauchySchwarz (Q'.le_of_lt hw0) (Q'.le_of_lt hw1) hsmall (Q'.le_of_lt hd) K radius p q lp lq hp hq)
      (SumOfSquares.q_mul_self_nonneg _))
    (Q'.ge_of_eqv (normalize_product _ _ _))

include lp lq hp hq in
/-- Cutoff removed, with the original one-sided tests held fixed. -/
theorem expectation_cauchySchwarz :
    leEv (CReal.mul (E (siteInsertion radius p q)) (E (siteInsertion radius p q)))
      (CReal.mul (E (siteInsertion radius p p)) (E (siteInsertion radius q q))) :=
  leEv_of_convergesTo_le
    (Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz.CReal.convergesTo_mul_general
      (finite_converges w hw0 hw1 hsmall hd extent faces (fun _ hi => hi) _)
      (finite_converges w hw0 hw1 hsmall hd extent faces (fun _ hi => hi) _))
    (Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz.CReal.convergesTo_mul_general
      (finite_converges w hw0 hw1 hsmall hd extent faces (fun _ hi => hi) _)
      (finite_converges w hw0 hw1 hsmall hd extent faces (fun _ hi => hi) _))
    (fun K => (leEv_congr (CRealAlg.ofQ'_mul _ _) (CRealAlg.ofQ'_mul _ _)).mp
      (leEv_ofQ'_of_approx_ge (fun _ => finite_cauchySchwarz w hw0 hw1 hsmall hd radius p q lp lq hp hq K)))

end YMGap.Continuum.BF4ExactSlabSiteCauchySchwarz

#print axioms YMGap.Continuum.BF4ExactSlabSiteCauchySchwarz.siteInsertion
#print axioms YMGap.Continuum.BF4ExactSlabSiteCauchySchwarz.rawForm
#print axioms YMGap.Continuum.BF4ExactSlabSiteCauchySchwarz.raw_cauchySchwarz
#print axioms YMGap.Continuum.BF4ExactSlabSiteCauchySchwarz.finite_cauchySchwarz
#print axioms YMGap.Continuum.BF4ExactSlabSiteCauchySchwarz.expectation_cauchySchwarz
