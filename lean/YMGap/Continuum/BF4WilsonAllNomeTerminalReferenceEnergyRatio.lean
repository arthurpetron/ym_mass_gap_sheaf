/-
# One original reference depth controls later completed energy ratios

The actual terminal comparison propagates a SUPPLIED finite-depth estimate
through every later depth and then through the constructed diagonal limits.
The source, its own marginal center, and the original completed carrier are
unchanged. This file does not prove the reference estimate, a changing-scale
rate, continuum survival, or physical mass calibration.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalEnergyComparison
import YMGap.Continuum.BF4WilsonAllNomeMarginalVarianceLimit
import YMGap.Continuum.FCLimitContinuity

namespace YMGap.Continuum.BF4WilsonAllNomeTerminalReferenceEnergyRatio

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow (normalizedEnergy)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyVarianceWard (oddVariance)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalComparison (comparisonEta)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalEnergyComparison
  (finite_reference_all_later)
open YMGap.Continuum.BF4WilsonAllNomeTemporalEnergyLimit
  (finiteEnergy energyCauchy energyLimit energyLimit_completed_pin)
open YMGap.Continuum.BF4WilsonAllNomeMarginalVarianceLimit
  (finiteVariance varianceCauchy varianceLimit varianceLimit_completed_pin)
open YMGap.Continuum.BF4WilsonAllNomeZeroRadiusIncrement (state)
open YMGap.Continuum.BF4WilsonAllNomeCenteredTransferBondLimit (singleSlice)
open YMGap.Continuum.BF4WilsonAllNomeCenteredVector (centeredVector)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner (completedInner)
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime (completedTime)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity

/-- The terminal-comparison loss is independent of cutoff and later depth. -/
def referenceCoefficient {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width s : Nat) (c : Q') : Q' :=
  c*((1+comparisonEta hw0 hw1 width s)*(1+comparisonEta hw0 hw1 width s))

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  {width : Nat} (e : WindowExpression width) (he : Within 0 e)

include he in
/-- A supplied estimate at ONE actual terminal depth controls all later
depths, with the same signed source and its own interacting variance. -/
theorem finite_reference_ratio (s k0 : Nat) {c : Q'} (hc : (0 : Q') ≤ c)
    (href : ∀ k : Nat, k0 ≤ k →
      finiteEnergy hw0 hw1 e k (s+1) ≤ c*finiteVariance hw0 hw1 e k (s+1))
    (k r : Nat) (hk : k0 ≤ k) :
    finiteEnergy hw0 hw1 e k (s+1+r) ≤
      referenceCoefficient hw0 hw1 width s c *
        finiteVariance hw0 hw1 e k (s+1+r) := by
  have hf : SupportedQuaternionBlocks (List.length (baseLinks width))
      (sourcePolynomial e) := by
    simpa only [Nat.zero_add, Nat.one_mul] using source_supported 0 e he
  have hreference := href k hk
  change normalizedEnergy hw0 hw1 (headCutoff w+k) width
      (Nat.le_add_right _ _) (s+1) (sourcePolynomial e) ≤
    c*oddVariance hw0 hw1 (headCutoff w+k) width
      (Nat.le_add_right _ _) (s+1) (sourcePolynomial e) at hreference
  have h := finite_reference_all_later hw0 hw1 (headCutoff w+k) width
    (Nat.le_add_right _ _) s hf hc hreference r
  change finiteEnergy hw0 hw1 e k (s+1+r) ≤
    referenceCoefficient hw0 hw1 width s c *
      finiteVariance hw0 hw1 e k (s+1+r) at h
  exact h

include he in
/-- An explicit diagonal onset: the cutoff is late and the terminal depth
has passed the supplied reference depth. -/
theorem finite_reference_diagonal (s k0 : Nat) {c : Q'} (hc : (0 : Q') ≤ c)
    (href : ∀ k : Nat, k0 ≤ k →
      finiteEnergy hw0 hw1 e k (s+1) ≤ c*finiteVariance hw0 hw1 e k (s+1))
    (k : Nat) (hk : max k0 (s+1) ≤ k) :
    finiteEnergy hw0 hw1 e k k ≤
      referenceCoefficient hw0 hw1 width s c * finiteVariance hw0 hw1 e k k := by
  have hk0 : k0 ≤ k := Nat.le_trans (Nat.le_max_left _ _) hk
  have htime : s+1 ≤ k := Nat.le_trans (Nat.le_max_right _ _) hk
  have h := finite_reference_ratio hw0 hw1 e he s k0 hc href
    k (k-(s+1)) hk0
  have hdepth : s+1+(k-(s+1)) = k := by omega
  rw [hdepth] at h
  exact h

private theorem scaled_variance_converges (D : Q') :
    ConvergesTo
      (fun k => ofQ' (D*finiteVariance hw0 hw1 e k k))
      (CReal.mul (ofQ' D) (varianceLimit hw0 hw1 e he)) := by
  unfold varianceLimit
  exact TrigAddCReal.convergesTo_congr_seq
    (fun k => (CRealAlg.ofQ'_mul D (finiteVariance hw0 hw1 e k k)).symm)
    (convergesTo_const_mul (ofQ' D)
      (convergesTo_ofQ'CauchySeq _ (varianceCauchy hw0 hw1 e he)))

/-- The one-sided diagonal limit uses the ALREADY constructed energy and
variance Cauchy witnesses; no convergence premise is introduced. -/
theorem energyLimit_reference_ratio (s k0 : Nat) {c : Q'} (hc : (0 : Q') ≤ c)
    (href : ∀ k : Nat, k0 ≤ k →
      finiteEnergy hw0 hw1 e k (s+1) ≤ c*finiteVariance hw0 hw1 e k (s+1)) :
    leEv (energyLimit hw0 hw1 e he)
      (CReal.mul (ofQ' (referenceCoefficient hw0 hw1 width s c))
        (varianceLimit hw0 hw1 e he)) := by
  let D := referenceCoefficient hw0 hw1 width s c
  have hE : ConvergesTo (fun k => ofQ' (finiteEnergy hw0 hw1 e k k))
      (energyLimit hw0 hw1 e he) := by
    unfold energyLimit
    exact convergesTo_ofQ'CauchySeq _ (energyCauchy hw0 hw1 e he)
  have hV := scaled_variance_converges hw0 hw1 e he D
  exact leEv_of_ofQ'_limit_le hE hV (fun epsilon hp =>
    ⟨max k0 (s+1), fun k hk =>
      Q'.le_trans' _ _ _
        (finite_reference_diagonal hw0 hw1 e he s k0 hc href k hk)
        (Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt hp))⟩)

/-- The exact SAME-carrier consumer: completed one-step time loss is bounded
by the original centered ambient norm with the propagated coefficient. -/
theorem completed_reference_ratio (s k0 : Nat) {c : Q'} (hc : (0 : Q') ≤ c)
    (href : ∀ k : Nat, k0 ≤ k →
      finiteEnergy hw0 hw1 e k (s+1) ≤ c*finiteVariance hw0 hw1 e k (s+1)) :
    RCle
      (RCsub
        (completedInner hw0 hw1 (centeredVector hw0 hw1 (state e he))
          (centeredVector hw0 hw1 (state e he)))
        (completedInner hw0 hw1 (centeredVector hw0 hw1 (state e he))
          (completedTime hw0 hw1 1 (centeredVector hw0 hw1 (state e he)))))
      (RCscale (referenceCoefficient hw0 hw1 width s c)
        (completedInner hw0 hw1 (centeredVector hw0 hw1 (state e he))
          (centeredVector hw0 hw1 (state e he)))) := by
  have hlim := energyLimit_reference_ratio hw0 hw1 e he s k0 hc href
  have hRC : RCle (Quotient.mk crealSetoid (energyLimit hw0 hw1 e he))
      (RCscale (referenceCoefficient hw0 hw1 width s c)
        (Quotient.mk crealSetoid (varianceLimit hw0 hw1 e he))) := hlim
  rw [energyLimit_completed_pin, varianceLimit_completed_pin] at hRC
  simpa only [singleSlice, state] using hRC

#print axioms referenceCoefficient
#print axioms finite_reference_ratio
#print axioms finite_reference_diagonal
#print axioms energyLimit_reference_ratio
#print axioms completed_reference_ratio

end YMGap.Continuum.BF4WilsonAllNomeTerminalReferenceEnergyRatio
