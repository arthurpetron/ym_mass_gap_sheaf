/-
# Actual block predictions, signed residuals, and normalized covariance limits

The two predictions and their common exterior projection are constructed
on the SAME full-action completion. Their signed covariance is exactly the
limit of dense covariance numerators divided by the actual union normalizer.
The prediction approximants retain the required block independence term by
term, with the existing explicit completion modulus; no representative is
chosen from a quotient and no completed multiplication is postulated.

The residual-pair decomposition retains its positive defect square. This
joins the existing numerator machinery to the actual conditional dynamics,
but proves no small covariance coefficient, range angle, OS gap, or scaling
claim. In particular, the inverse approximation rate is not a mixing rate.
-/

import YMGap.Continuum.BF4ExactSlabBlockTower
import YMGap.Continuum.BF4ExactSlabBlockCovarianceNormalizer
import YMGap.Continuum.GNSProjectionPredictionCovariance

namespace YMGap.Continuum.BF4ExactSlabBlockPredictionCovariance

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.GNSProjectionSweep
open YMGap.Continuum.GNSDenseCompletionExtension
open YMGap.Continuum.GNSDenseCompletionLaws
open YMGap.Continuum.GNSJointPairingContinuity
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabStarFullActionProbe
open YMGap.Continuum.BF4ExactSlabBlockNormalizer
open YMGap.Continuum.BF4ExactSlabBlockNormalizerMap
open YMGap.Continuum.BF4ExactSlabBlockCompletedInverse
open YMGap.Continuum.BF4ExactSlabBlockOriginalConditional
open YMGap.Continuum.BF4ExactSlabBlockConditionalProjection
open YMGap.Continuum.BF4ExactSlabBlockCovarianceNormalizer
open YMGap.Continuum.BF4ExactSlabBlockTower
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K extent : Nat) (hK : headCutoff w ≤ K)

local notation "F" => fullData hw0 hw1 K extent hK

section Representatives

variable (links : List Z4Link)
  (hl : ∀ link, link ∈ links → link ∈ boundaryCompleteSlabLinks extent)

/-- The existing cofinal diagonal, not a selected quotient representative. -/
def predictionRep (X : CauchyGNS F) : CauchyGNS F :=
  (conditionalDenseMap hw0 hw1 K extent hK links hl).mapRep X

theorem predictionRep_class (X : CauchyGNS F) :
    Quotient.mk (cauchySetoid F) (predictionRep hw0 hw1 K extent hK links hl X) =
      conditionalProjection hw0 hw1 K extent hK links hl
        (Quotient.mk (cauchySetoid F) X) := rfl

/-- The supplied representative carries an explicit Type-level modulus. -/
theorem predictionRep_modulus (X : CauchyGNS F) (epsilon : Q') :
    (predictionRep hw0 hw1 K extent hK links hl X).modulus epsilon =
      gMod epsilon := rfl

/-- Every dense approximant is independent of the integrated block.
Arbitrary exterior dependence is retained. -/
theorem predictionRep_independent (X : CauchyGNS F) (n i : Nat)
    (hi : i ∈ slots extent links) :
    QuaternionBlockIndependent i
      ((predictionRep hw0 hw1 K extent hK links hl X).seq n).val := by
  let O := (conditionalDenseMap hw0 hw1 K extent hK links hl).mapOuter X
  change QuaternionBlockIndependent i
    ((conditionalRep hw0 hw1 K extent hK links hl
      (X.seq (O.phi n))).seq (O.reindex.Jidx n)).val
  exact inverseCauchy_independent hw0 hw1 K extent hK links hl
    (X.seq (O.phi n)) (O.reindex.Jidx n) i hi

local notation "G" => backgroundData hw0 hw1 K extent hK links

/-- At each index, divide the actual dense covariance numerator by D.
There is only one detached exterior action in this pairing. -/
def inverseCovarianceSequence (X Y : CauchyGNS F) (n : Nat) : CReal :=
  (G).cinnerRep
    (inverseCauchy hw0 hw1 K extent hK links hl
      (covarianceVector hw0 hw1 K extent hK links (X.seq n) (Y.seq n)))
    (constCauchy G (backgroundUnit hw0 hw1 K extent hK links))

/-- Explicit constructive-real limit on the SAME original carrier. -/
def covarianceLimit (X Y : CauchyGNS F) : CReal :=
  CReal.sub ((F).cinnerRep X Y)
    ((F).cinnerRep (predictionRep hw0 hw1 K extent hK links hl X)
      (predictionRep hw0 hw1 K extent hK links hl Y))

private theorem dense_pairing_converges (X Y : CauchyGNS F) :
    CReal.ConvergesTo
      (fun n => (F).cinnerRep (constCauchy F (X.seq n)) (constCauchy F (Y.seq n)))
      ((F).cinnerRep X Y) := by
  apply CReal.convergesTo_limit_congr (pairing_converges (inputOuter X) (inputOuter Y))
  apply Quotient.exact (s := CReal.crealSetoid)
  change (F).cinnerCompl
      (Quotient.mk (cauchySetoid F) (inputOuter X).lim)
      (Quotient.mk (cauchySetoid F) (inputOuter Y).lim) = _
  rw [inputOuter_lim_class, inputOuter_lim_class]
  rfl

/-- Exact normalization survives joint approximation of both tests. No
uniform inverse bound over input polynomial degrees is being assumed. -/
theorem inverseCovarianceSequence_converges (X Y : CauchyGNS F) :
    CReal.ConvergesTo (inverseCovarianceSequence hw0 hw1 K extent hK links hl X Y)
      (covarianceLimit hw0 hw1 K extent hK links hl X Y) := by
  let T := conditionalDenseMap hw0 hw1 K extent hK links hl
  have h := CReal.convergesTo_add (dense_pairing_converges hw0 hw1 K extent hK X Y)
    (CReal.convergesTo_neg (pairing_converges (T.mapOuter X) (T.mapOuter Y)))
  apply TrigAddCReal.convergesTo_congr_seq (fun n => ?_) h
  exact (Quotient.exact (s := CReal.crealSetoid)
    (covariance_normalizer_pair hw0 hw1 K extent hK links hl (X.seq n) (Y.seq n))).symm

end Representatives

variable (A B : List Z4Link)
  (hA : ∀ link, link ∈ A → link ∈ boundaryCompleteSlabLinks extent)
  (hB : ∀ link, link ∈ B → link ∈ boundaryCompleteSlabLinks extent)

include hA hB in
theorem union_physical :
    ∀ link, link ∈ A ++ B → link ∈ boundaryCompleteSlabLinks extent := by
  intro link h
  exact (List.mem_append.mp h).elim (hA link) (hB link)

private theorem left_slots : ∀ i, i ∈ slots extent A → i ∈ slots extent (A ++ B) :=
  slots_subset_of_links_subset extent A (A ++ B) (fun _ h => List.mem_append_left B h)

private theorem right_slots : ∀ i, i ∈ slots extent B → i ∈ slots extent (A ++ B) :=
  slots_subset_of_links_subset extent B (A ++ B) (fun _ h => List.mem_append_right A h)

local notation "PA" => conditionalProjection hw0 hw1 K extent hK A hA
local notation "PB" => conditionalProjection hw0 hw1 K extent hK B hB
local notation "CU" => conditionalProjection hw0 hw1 K extent hK (A ++ B)
  (union_physical extent A B hA hB)
local notation "P" => blockFamily hw0 hw1 K extent hK

/-- The signed covariance of the actual predictions, not arbitrary tests. -/
def predictionCovariance (x : GNSCompletionSpace F) : RC :=
  RCsub ((F).cinnerCompl (PA x) (PB x)) (normSq (CU x))

/-- The positive term that a residual-pair estimate must retain or discard
using its proved nonnegativity, not by pretending covariance equals residual. -/
def predictionDefect (x : GNSCompletionSpace F) : GNSCompletionSpace F :=
  (F).cSub ((F).cSub x (PA x)) ((F).cSub (PB x) (CU x))

theorem predictionCovariance_centered (x : GNSCompletionSpace F) :
    (F).cinnerCompl ((F).cSub (PA x) (CU x)) ((F).cSub (PB x) (CU x)) =
      predictionCovariance hw0 hw1 K extent hK A B hA hB x := by
  exact (P).centered_prediction_pairing ⟨A, hA⟩ ⟨B, hB⟩
    ⟨A ++ B, union_physical extent A B hA hB⟩
    (reverse_tower hw0 hw1 K extent hK A (A ++ B) hA
      (union_physical extent A B hA hB) (left_slots extent A B))
    (reverse_tower hw0 hw1 K extent hK B (A ++ B) hB
      (union_physical extent A B hA hB) (right_slots extent A B)) x

/-- Exact SAME-operator join on every completed state, for arbitrary finite
physical blocks, including overlapping blocks. No commuting-pair hypothesis. -/
theorem residual_pair_decomposition (x : GNSCompletionSpace F) :
    (F).cinnerCompl ((F).cSub x (PA x)) ((F).cSub x (PB x)) =
      RCsub (normSq (predictionDefect hw0 hw1 K extent hK A B hA hB x))
        (predictionCovariance hw0 hw1 K extent hK A B hA hB x) := by
  exact (P).residual_pair_prediction_decomposition ⟨A, hA⟩ ⟨B, hB⟩
    ⟨A ++ B, union_physical extent A B hA hB⟩
    (tower hw0 hw1 K extent hK A (A ++ B) hA
      (union_physical extent A B hA hB) (left_slots extent A B))
    (reverse_tower hw0 hw1 K extent hK B (A ++ B) hB
      (union_physical extent A B hA hB) (right_slots extent A B)) x

/-- The explicit limit of normalized dense numerators IS the prediction
covariance in that residual decomposition. The quotient input is supplied
by its Cauchy data, never extracted by choice. -/
theorem prediction_covariance_limit (X : CauchyGNS F) :
    Quotient.mk CReal.crealSetoid
      (covarianceLimit hw0 hw1 K extent hK (A ++ B)
        (union_physical extent A B hA hB)
        (predictionRep hw0 hw1 K extent hK A hA X)
        (predictionRep hw0 hw1 K extent hK B hB X)) =
      predictionCovariance hw0 hw1 K extent hK A B hA hB
        (Quotient.mk (cauchySetoid F) X) := by
  let x := Quotient.mk (cauchySetoid F) X
  change RCsub ((F).cinnerCompl (PA x) (PB x))
    ((F).cinnerCompl (CU (PA x)) (CU (PB x))) = _
  rw [reverse_tower hw0 hw1 K extent hK A (A ++ B) hA
      (union_physical extent A B hA hB) (left_slots extent A B),
    reverse_tower hw0 hw1 K extent hK B (A ++ B) hB
      (union_physical extent A B hA hB) (right_slots extent A B)]
  rfl

#print axioms predictionRep
#print axioms predictionRep_class
#print axioms predictionRep_modulus
#print axioms predictionRep_independent
#print axioms inverseCovarianceSequence
#print axioms covarianceLimit
#print axioms inverseCovarianceSequence_converges
#print axioms union_physical
#print axioms predictionCovariance
#print axioms predictionDefect
#print axioms predictionCovariance_centered
#print axioms residual_pair_decomposition
#print axioms prediction_covariance_limit

end YMGap.Continuum.BF4ExactSlabBlockPredictionCovariance
