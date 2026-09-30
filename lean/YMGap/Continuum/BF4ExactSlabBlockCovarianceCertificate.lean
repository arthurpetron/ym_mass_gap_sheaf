/-
# Original polynomial certificates feed the completed residual estimate

The certificate is for the literal signed covariance budget on the original
background carrier. The proved positive inverse functional divides by the
ACTUAL conditional normalizer, with no loss in rho. The existing explicit
prediction approximants and limit theorem then give the signed residual
bound on the SAME completed state.

This checks a supplied SOS witness; it does not produce a useful rho or the
certificates required on a scaling family. No new analytic bundle is added.
-/

import YMGap.Continuum.BF4ExactSlabBlockInversePositive
import YMGap.Continuum.BF4ExactSlabBlockPredictionAngle

namespace YMGap.Continuum.BF4ExactSlabBlockCovarianceCertificate

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.GNSProjectionSweep
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabStarFullActionProbe
open YMGap.Continuum.BF4ExactSlabBlockNormalizerMap
open YMGap.Continuum.BF4ExactSlabBlockCompletedInverse
open YMGap.Continuum.BF4ExactSlabBlockConditionalProjection
open YMGap.Continuum.BF4ExactSlabBlockCovarianceNormalizer
open YMGap.Continuum.BF4ExactSlabBlockPredictionCovariance
open YMGap.Continuum.BF4ExactSlabBlockPredictionAngle
open YMGap.Continuum.BF4ExactSlabBlockInversePositive
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K extent : Nat) (hK : headCutoff w ≤ K) (links : List Z4Link)

local notation "F" => fullData hw0 hw1 K extent hK
local notation "G" => backgroundData hw0 hw1 K extent hK links
local notation "N" => covarianceVector hw0 hw1 K extent hK links

/-- rho*(N_pp+N_qq)-2*N_pq, as an actual supported polynomial vector. -/
def covarianceBudget (rho : Q') (p q : (F).V) : (G).V :=
  (G).sub ((G).smul rho ((G).add (N p p) (N q q))) ((G).smul 2 (N p q))

variable (hl : ∀ link, link ∈ links → link ∈ boundaryCompleteSlabLinks extent)

local notation "I" => inverseState hw0 hw1 K extent hK links hl
local notation "unitV" => backgroundUnit hw0 hw1 K extent hK links
local notation "meanI" => inverseMean hw0 hw1 K extent hK links hl

/-- The same coefficient survives division by D. This is a verifier of
the supplied algebraic witness, not a producer of covariance smallness. -/
theorem inverse_covariance_bound (rho : Q') (p q : (F).V)
    (P : Certificate (boundaryCompleteSlabLinks extent).length
      (covarianceBudget hw0 hw1 K extent hK links rho p q).val) :
    RCle (RCscale 2 ((G).cinnerCompl (I (N p q)) (embedV G unitV)))
      (RCscale rho (RCadd
        ((G).cinnerCompl (I (N p p)) (embedV G unitV))
        ((G).cinnerCompl (I (N q q)) (embedV G unitV)))) := by
  have h := inverseMean_mono hw0 hw1 K extent hK links hl
    ((G).smul 2 (N p q)) ((G).smul rho ((G).add (N p p) (N q q))) P
  rwa [inverseMean_smul, inverseMean_smul, inverseMean_add,
    inverseMean_pin, inverseMean_pin, inverseMean_pin] at h

theorem inverse_covariance_sequence_bound (rho : Q') (X Y : CauchyGNS F) (n : Nat)
    (P : Certificate (boundaryCompleteSlabLinks extent).length
      (covarianceBudget hw0 hw1 K extent hK links rho (X.seq n) (Y.seq n)).val) :
    leEv (CReal.mul (ofQ' 2)
      (inverseCovarianceSequence hw0 hw1 K extent hK links hl X Y n))
      (CReal.mul (ofQ' rho) (CReal.add
        (inverseCovarianceSequence hw0 hw1 K extent hK links hl X X n)
        (inverseCovarianceSequence hw0 hw1 K extent hK links hl Y Y n))) :=
  inverse_covariance_bound hw0 hw1 K extent hK links hl rho (X.seq n) (Y.seq n) P

omit links hl in
/-- Certificates for the actual prediction approximants suffice. Their
construction, uniformity and useful rho remain genuine open inputs. -/
theorem residual_pair_lower_of_certificates
    (A B : List Z4Link)
    (hA : ∀ link, link ∈ A → link ∈ boundaryCompleteSlabLinks extent)
    (hB : ∀ link, link ∈ B → link ∈ boundaryCompleteSlabLinks extent)
    (rho : Q') (hrho0 : (0 : Q') ≤ rho) (hrho1 : rho ≤ 1)
    (X : CauchyGNS F)
    (certificates : ∀ n, Certificate (boundaryCompleteSlabLinks extent).length
      (covarianceBudget hw0 hw1 K extent hK (A ++ B) rho
        ((predictionRep hw0 hw1 K extent hK A hA X).seq n)
        ((predictionRep hw0 hw1 K extent hK B hB X).seq n)).val) :
    let x := Quotient.mk (cauchySetoid F) X;
    let u := (F).cSub x (conditionalProjection hw0 hw1 K extent hK A hA x);
    let v := (F).cSub x (conditionalProjection hw0 hw1 K extent hK B hB x);
    RCle (RCneg (RCscale (HalfPow.half*rho) (RCadd (normSq u) (normSq v))))
      ((F).cinnerCompl u v) := by
  apply residual_pair_lower_of_dense_covariance_bound hw0 hw1 K extent hK A B hA hB
    rho hrho0 hrho1 X
  intro n
  exact inverse_covariance_sequence_bound hw0 hw1 K extent hK (A ++ B)
    (union_physical extent A B hA hB) rho
    (predictionRep hw0 hw1 K extent hK A hA X)
    (predictionRep hw0 hw1 K extent hK B hB X) n (certificates n)

#print axioms covarianceBudget
#print axioms inverse_covariance_bound
#print axioms inverse_covariance_sequence_bound
#print axioms residual_pair_lower_of_certificates

end YMGap.Continuum.BF4ExactSlabBlockCovarianceCertificate
