/-
# Original block prediction covariance implies a sharp residual-pair bound

The SAME completed conditional projections and union normalizer are used.
The sole analytic premise is a one-sided normalized prediction covariance
bound at the supplied state. The positive-square identity converts it into
the residual-energy bound consumed by signed neighbor estimates, with
coefficient rho/2. No useful rho, uniformity or physical gap is produced.
-/

import YMGap.Continuum.BF4ExactSlabBlockPredictionCovariance
import YMGap.Continuum.BF4ExactSlabFullActionScalar
import YMGap.Continuum.GNSPredictionAngleResidual

namespace YMGap.Continuum.BF4ExactSlabBlockPredictionAngle

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.GNSProjectionSweep
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabStarFullActionProbe
open YMGap.Continuum.BF4ExactSlabFullActionScalar
open YMGap.Continuum.BF4ExactSlabBlockNormalizer
open YMGap.Continuum.BF4ExactSlabBlockConditionalProjection
open YMGap.Continuum.BF4ExactSlabBlockTower
open YMGap.Continuum.BF4ExactSlabBlockPredictionCovariance
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K extent : Nat) (hK : headCutoff w ≤ K)
  (A B : List Z4Link)
  (hA : ∀ link, link ∈ A → link ∈ boundaryCompleteSlabLinks extent)
  (hB : ∀ link, link ∈ B → link ∈ boundaryCompleteSlabLinks extent)

local notation "F" => fullData hw0 hw1 K extent hK
local notation "PA" => conditionalProjection hw0 hw1 K extent hK A hA
local notation "PB" => conditionalProjection hw0 hw1 K extent hK B hB
local notation "CU" => conditionalProjection hw0 hw1 K extent hK (A ++ B)
  (union_physical extent A B hA hB)

/-- Relative to the actual common union projection, not a free variance. -/
def predictionVarianceSum (x : GNSCompletionSpace F) : RC :=
  RCadd (normSq ((F).cSub (PA x) (CU x)))
    (normSq ((F).cSub (PB x) (CU x)))

/-- Includes overlapping physical blocks. The input is at this x only;
it may be proved along a specified recurrence rather than every state. -/
theorem residual_pair_lower_of_prediction_bound
    (rho : Q') (hrho0 : (0 : Q') ≤ rho) (hrho1 : rho ≤ 1)
    (x : GNSCompletionSpace F)
    (hcov : RCle
      (RCscale 2 (predictionCovariance hw0 hw1 K extent hK A B hA hB x))
      (RCscale rho (predictionVarianceSum hw0 hw1 K extent hK A B hA hB x))) :
    RCle (RCneg (RCscale (HalfPow.half*rho)
      (RCadd (normSq ((F).cSub x (PA x))) (normSq ((F).cSub x (PB x))))))
      ((F).cinnerCompl ((F).cSub x (PA x)) ((F).cSub x (PB x))) := by
  have hi := reverse_tower hw0 hw1 K extent hK A (A ++ B) hA
    (union_physical extent A B hA hB)
    (slots_subset_of_links_subset extent A (A ++ B) (fun _ h => List.mem_append_left B h))
  have hj := reverse_tower hw0 hw1 K extent hK B (A ++ B) hB
    (union_physical extent A B hA hB)
    (slots_subset_of_links_subset extent B (A ++ B) (fun _ h => List.mem_append_right A h))
  apply GNSPredictionAngleResidual.projection_residual_lower
    (fullScalarData hw0 hw1 K extent hK) (blockFamily hw0 hw1 K extent hK)
    ⟨A, hA⟩ ⟨B, hB⟩ ⟨A ++ B, union_physical extent A B hA hB⟩
    hi hj rho hrho0 hrho1 x
  change RCle (RCscale 2 ((F).cinnerCompl ((F).cSub (PA x) (CU x))
    ((F).cSub (PB x) (CU x)))) _
  rw [predictionCovariance_centered]
  exact hcov

/-- The diagonal of the actual inverse-normalized covariance limit is
the variance after the SAME block projection, not a replacement norm. -/
theorem covarianceLimit_diagonal (links : List Z4Link)
    (hl : ∀ link, link ∈ links → link ∈ boundaryCompleteSlabLinks extent)
    (X : CauchyGNS F) :
    Quotient.mk crealSetoid (covarianceLimit hw0 hw1 K extent hK links hl X X) =
      normSq ((F).cSub (Quotient.mk (cauchySetoid F) X)
        (conditionalProjection hw0 hw1 K extent hK links hl
          (Quotient.mk (cauchySetoid F) X))) := by
  let x := Quotient.mk (cauchySetoid F) X
  change RCsub (normSq x)
    (normSq (conditionalProjection hw0 hw1 K extent hK links hl x)) = _
  exact ((blockFamily hw0 hw1 K extent hK).single_loss ⟨links, hl⟩ x).symm

local notation "XA" X => predictionRep hw0 hw1 K extent hK A hA X
local notation "XB" X => predictionRep hw0 hw1 K extent hK B hB X
local notation "Vlim" => covarianceLimit hw0 hw1 K extent hK (A ++ B)
  (union_physical extent A B hA hB)
local notation "Nseq" => inverseCovarianceSequence hw0 hw1 K extent hK (A ++ B)
  (union_physical extent A B hA hB)

theorem prediction_variance_sum_limit (X : CauchyGNS F) :
    RCadd (Quotient.mk crealSetoid (Vlim (XA X) (XA X)))
      (Quotient.mk crealSetoid (Vlim (XB X) (XB X))) =
      predictionVarianceSum hw0 hw1 K extent hK A B hA hB
        (Quotient.mk (cauchySetoid F) X) := by
  rw [covarianceLimit_diagonal, covarianceLimit_diagonal,
    predictionRep_class, predictionRep_class]
  rw [reverse_tower hw0 hw1 K extent hK A (A ++ B) hA
    (union_physical extent A B hA hB)
    (slots_subset_of_links_subset extent A (A ++ B) (fun _ h => List.mem_append_left B h)),
    reverse_tower hw0 hw1 K extent hK B (A ++ B) hB
      (union_physical extent A B hA hB)
      (slots_subset_of_links_subset extent B (A ++ B) (fun _ h => List.mem_append_right A h))]
  rfl

/-- A bound on the actual normalized dense numerators along the supplied
prediction approximants suffices, with the SAME coefficient after passage
to the completion. This theorem does not supply that analytic bound. -/
theorem residual_pair_lower_of_dense_covariance_bound
    (rho : Q') (hrho0 : (0 : Q') ≤ rho) (hrho1 : rho ≤ 1)
    (X : CauchyGNS F)
    (hcov : ∀ n, leEv
      (CReal.mul (ofQ' 2) (Nseq (XA X) (XB X) n))
      (CReal.mul (ofQ' rho)
        (CReal.add (Nseq (XA X) (XA X) n) (Nseq (XB X) (XB X) n)))) :
    let x := Quotient.mk (cauchySetoid F) X;
    RCle (RCneg (RCscale (HalfPow.half*rho)
      (RCadd (normSq ((F).cSub x (PA x))) (normSq ((F).cSub x (PB x))))))
      ((F).cinnerCompl ((F).cSub x (PA x)) ((F).cSub x (PB x))) := by
  have hlim := leEv_of_convergesTo_le
    (convergesTo_constMul 2 (inverseCovarianceSequence_converges
      hw0 hw1 K extent hK (A ++ B) (union_physical extent A B hA hB) (XA X) (XB X)))
    (convergesTo_constMul rho (convergesTo_add
      (inverseCovarianceSequence_converges hw0 hw1 K extent hK (A ++ B)
        (union_physical extent A B hA hB) (XA X) (XA X))
      (inverseCovarianceSequence_converges hw0 hw1 K extent hK (A ++ B)
        (union_physical extent A B hA hB) (XB X) (XB X)))) hcov
  change RCle (RCscale 2 (Quotient.mk crealSetoid (Vlim (XA X) (XB X))))
    (RCscale rho (RCadd (Quotient.mk crealSetoid (Vlim (XA X) (XA X)))
      (Quotient.mk crealSetoid (Vlim (XB X) (XB X))))) at hlim
  rw [prediction_covariance_limit, prediction_variance_sum_limit] at hlim
  exact residual_pair_lower_of_prediction_bound hw0 hw1 K extent hK A B hA hB
    rho hrho0 hrho1 _ hlim

#print axioms predictionVarianceSum
#print axioms residual_pair_lower_of_prediction_bound
#print axioms covarianceLimit_diagonal
#print axioms prediction_variance_sum_limit
#print axioms residual_pair_lower_of_dense_covariance_bound

end YMGap.Continuum.BF4ExactSlabBlockPredictionAngle
