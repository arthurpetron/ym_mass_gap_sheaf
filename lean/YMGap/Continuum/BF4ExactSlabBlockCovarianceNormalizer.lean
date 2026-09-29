/-
# Original completed conditional covariance with its actual normalizer

The signed conditional numerator is divided by the constructed original block
normalizer, not a floor. Its pairing with the background unit is exactly the
original completed union-centered covariance. Every input product is a dense
supported polynomial. The proof does not assume a multiplication operator on
arbitrary completed states, nor a conditional angle, scaling or OS estimate.
-/

import YMGap.Continuum.BF4ExactSlabBlockInverseAlgebra
import YMGap.Continuum.BF4ExactSlabBlockConditionalProjection
import YMGap.Continuum.SU2QuaternionFamilyCovarianceReplica

namespace YMGap.Continuum.BF4ExactSlabBlockCovarianceNormalizer

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.GNSModulusCompletion
open YMGap.Continuum.HamiltonianScalar
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabLocalSupportComparison
open YMGap.Continuum.BF4ExactSlabBlockNormalizer
open YMGap.Continuum.BF4ExactSlabBlockNormalizerMap
open YMGap.Continuum.BF4ExactSlabBlockInverseApproximation
open YMGap.Continuum.BF4ExactSlabBlockInverseAlgebra
open YMGap.Continuum.BF4ExactSlabBlockCompletedInverse
open YMGap.Continuum.BF4ExactSlabBlockConditionalApproximation
open YMGap.Continuum.BF4ExactSlabBlockOriginalConditional
open YMGap.Continuum.BF4ExactSlabBlockConditionalProjection
open YMGap.Continuum.BF4ExactSlabStarFullActionProbe
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionHaarFamilyProjection
open YMGap.Continuum.SU2QuaternionFamilyCovarianceReplica
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K extent : Nat) (hK : headCutoff w ≤ K) (links : List Z4Link)
  (hl : ∀ link, link ∈ links → link ∈ boundaryCompleteSlabLinks extent)

local notation "G" => backgroundData hw0 hw1 K extent hK links
local notation "F" => fullData hw0 hw1 K extent hK
local notation "M" => normalizerMap hw0 hw1 K extent hK links
local notation "A" => approximateInverse hw0 hw1 K extent hK links
local notation "I" => inverseState hw0 hw1 K extent hK links hl
local notation "Q" => conditionalUpdate hw0 hw1 K extent hK links hl
local notation "N" => numeratorVector hw0 hw1 K extent hK links
local notation "mulV" => productVector hw0 hw1 K extent hK links

def backgroundUnit : (G).V :=
  ⟨polyOne, supported_one _⟩

/-- Linearity of the actual inverse on dense inputs, proved from its explicit
sequences. This does not select a representative of an arbitrary quotient. -/
theorem inverseState_sub (r t : (G).V) : I ((G).sub r t) = (G).cSub (I r) (I t) := by
  apply Quotient.sound
  intro epsilon hepsilon
  refine ⟨0, fun n _ => ?_⟩
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (rad_of_veq G (approximateInverse_sub hw0 hw1 K extent hK links r t n)))
    (Q'.le_of_lt hepsilon)

/-- Move a fixed dense polynomial across the constructed inverse pairing.
Both sides are existing Cauchy sequences, so no completed multiplier is used. -/
theorem inverseState_product_pair (r t : (G).V) :
    (G).cinnerCompl (I r) (embedV G t) =
      (G).cinnerCompl (I (mulV r t)) (embedV G (backgroundUnit hw0 hw1 K extent hK links)) := by
  apply Quotient.sound
  refine CReal.Equiv_of_limit_of_equal ?_
    (CReal.convergesTo_ofQ'CauchySeq _ _) (CReal.convergesTo_ofQ'CauchySeq _ _)
  intro n
  apply CReal.ofQ'_equiv_of_eqv
  have h : RatPolyCoeffEqv (A (mulV r t) n).val (polyMul (A r n).val t.val) :=
    approximateInverse_mul_right hw0 hw1 K extent hK links r t n
  exact Q'.eqv_symm (haar_of_coeff
    (((RatPolyCoeffEqv.mul_one _).trans h).mul_right (background w K extent links)))

/-- D*N_pq-N_p*N_q as an actual vector on the SAME detached background. -/
def covarianceVector (p q : (F).V) : (G).V :=
  (G).sub (M (N (polyMul p.val q.val) (supported_polyMul p.property q.property)))
    (mulV (N p.val p.property) (N q.val q.property))

/-- This vector is precisely the previously proved family covariance
numerator for the original collar, up to coefficient equality and multiplication
order only. No background factor is squared here. -/
theorem covarianceVector_pin (p q : (F).V) :
    RatPolyCoeffEqv (covarianceVector hw0 hw1 K extent hK links p q).val
      (covarianceNumerator (slots extent links) (collarHeat w K extent links) p.val q.val) := by
  have hprod := familyProject_congr (slots extent links)
    (RatPolyCoeffEqv.mul_comm (polyMul p.val q.val) (collarHeat w K extent links))
  have hp := familyProject_congr (slots extent links)
    (RatPolyCoeffEqv.mul_comm p.val (collarHeat w K extent links))
  have hq := familyProject_congr (slots extent links)
    (RatPolyCoeffEqv.mul_comm q.val (collarHeat w K extent links))
  exact ((hprod.mul_right _).trans (RatPolyCoeffEqv.mul_comm _ _)).add
    (((hp.mul hq).smul (-1)).trans (QuaternionHaarAngularCarrier.neg_smul _).symm)

include hl in
/-- The original dense full-action pairing is the background mean of its
actual inserted numerator. This is an equality of constructive-real classes. -/
theorem inserted_product_mean (p q : (F).V) :
    (G).cinnerCompl
      (embedV G (N (polyMul p.val q.val) (supported_polyMul p.property q.property)))
      (embedV G (backgroundUnit hw0 hw1 K extent hK links)) =
    (F).cinnerCompl (embedV F p) (embedV F q) := by
  have hmean := full_insertion_pin w K extent links hl (polyMul p.val q.val)
  have h : (G).B (N (polyMul p.val q.val) (supported_polyMul p.property q.property))
      (backgroundUnit hw0 hw1 K extent hK links) ≈ (F).B p q :=
    Q'.eqv_trans _ _ _ (haar_of_coeff
      (((RatPolyCoeffEqv.mul_one _).mul_right _).trans (RatPolyCoeffEqv.mul_comm _ _)))
      (Q'.eqv_symm hmean)
  apply Quotient.sound
  exact SumOfSquares.Equiv_of_approx_eqv (fun _ => h)

/-- Both constructed conditional outputs are tested on the original
completion; their common union normalizer is cancelled exactly. -/
theorem conditional_pair_background (p q : (F).V) :
    (F).cinnerCompl (Q p) (Q q) =
      (G).cinnerCompl (I (N p.val p.property)) (embedV G (N q.val q.property)) := by
  rw [conditionalUpdate_pairing]
  exact toFull_test_of_independent hw0 hw1 K extent hK links hl
    (inverseCauchy hw0 hw1 K extent hK links hl (N p.val p.property))
    (inverseCauchy_independent hw0 hw1 K extent hK links hl p) q

/-- Exact normalization join. The left side means E*N/D using the actual
constructed inverse, not E*N nor N divided by a worst-case floor. The full
partition normalization, if desired, is the same scalar on both sides. -/
theorem covariance_normalizer_pair (p q : (F).V) :
    (G).cinnerCompl (I (covarianceVector hw0 hw1 K extent hK links p q))
      (embedV G (backgroundUnit hw0 hw1 K extent hK links)) =
    CReal.RCsub ((F).cinnerCompl (embedV F p) (embedV F q))
      ((F).cinnerCompl (Q p) (Q q)) := by
  unfold covarianceVector
  rw [inverseState_sub, (G).cinnerCompl_cSub_left, inverseState_normalizer,
    inserted_product_mean hw0 hw1 K extent hK links hl,
    ← inverseState_product_pair, ← conditional_pair_background]

/-- Same identity with the actual completed projection, not a newly
postulated conditional operator. Inputs remain dense supported polynomials. -/
theorem covariance_normalizer_projection (p q : (F).V) :
    let C := conditionalProjection hw0 hw1 K extent hK links hl;
    (G).cinnerCompl (I (covarianceVector hw0 hw1 K extent hK links p q))
      (embedV G (backgroundUnit hw0 hw1 K extent hK links)) =
    CReal.RCsub ((F).cinnerCompl (embedV F p) (embedV F q))
      ((F).cinnerCompl (C (embedV F p)) (C (embedV F q))) := by
  dsimp only
  rw [conditionalProjection_embed, conditionalProjection_embed]
  exact covariance_normalizer_pair hw0 hw1 K extent hK links hl p q

#print axioms backgroundUnit
#print axioms inverseState_sub
#print axioms inverseState_product_pair
#print axioms covarianceVector
#print axioms covarianceVector_pin
#print axioms inserted_product_mean
#print axioms conditional_pair_background
#print axioms covariance_normalizer_pair
#print axioms covariance_normalizer_projection

end YMGap.Continuum.BF4ExactSlabBlockCovarianceNormalizer
