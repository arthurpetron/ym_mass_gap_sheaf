/-
# Constructed one-sided boundary-time limit of the original mass ratios

Nested actual transfer brackets put every pair of later normalized ratios
in one interval of width q^n*(probeCap+probeCap). The existing constructive
geometric cutoff therefore supplies a time-Cauchy modulus independent of
the late heat cutoff K. Its rate still depends on nome and spatial width.

The returned CReal is a fixed-width, fixed-K boundary functional as the
opposite time boundary recedes. No stationarity, bulk vacuum, reflected OS
realization, cutoff-limit interchange, continuum passage or physical gap
is asserted. The terminal spatial weight and original normalization remain.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBracketNesting
import YMGap.Continuum.PositiveContractionResidual
import YMGap.Continuum.GNSHilbertSpace

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialBoundaryTimeLimit

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabTemporalSweep (FaceFactor)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferMixingRate
open YMGap.Continuum.BF4ExactSlabFixedSpatialProbeInterval
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBracketDecay
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBracketNesting
open YMGap.Continuum.PositiveContractionResidual (geometricCutoff geometric_bound)

/-- Executable time threshold; no heat-cutoff argument or hidden dependence.
The existing geometric cutoff includes q=0 and zero probe cap. -/
def boundaryTimeModulus {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width : Nat) (fs : List FaceFactor) (epsilon : Q') : Nat :=
  geometricCutoff (mixRate hw0 hw1 width) (probeCap fs + probeCap fs) epsilon

theorem boundaryTime_budget {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width : Nat) (fs : List FaceFactor) (epsilon : Q') (he : (0 : Q') < epsilon)
    (n : Nat) (hn : boundaryTimeModulus hw0 hw1 width fs epsilon ≤ n) :
    mixRate hw0 hw1 width ^ n * (probeCap fs + probeCap fs) ≤ epsilon :=
  geometric_bound (mixRate_nonnegative hw0 hw1 width) (mixRate_lt_one hw0 hw1 width)
    (Q'.zero_le_add _ _ (sourceProbe_interval width fs).nonnegative
      (sourceProbe_interval width fs).nonnegative) he n hn

/-- Time-Cauchy data for the actual normalized messages, with positive masses
already constructed from the original spatial product. -/
def boundaryTimeCauchy {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (fs : List FaceFactor) :
    QCauchy (fun n => sourceProbeMassRatio hw0 hw1 K width hK n fs) where
  M := boundaryTimeModulus hw0 hw1 width fs
  bound := by
    intro epsilon he i j hi hj
    have hb := sourceProbeMassRatio_commonTail hw0 hw1 K width hK
      (boundaryTimeModulus hw0 hw1 width fs epsilon) i j fs hi hj
    have heq := boundaryTime_budget hw0 hw1 width fs epsilon he
      (boundaryTimeModulus hw0 hw1 width fs epsilon) (Nat.le_refl _)
    exact ⟨Q'.le_trans' _ _ _ hb.1 (Q'.add_le_add_left _ _ _ heq),
      Q'.le_trans' _ _ _ hb.2 (Q'.add_le_add_left _ _ _ heq)⟩

/-- The explicit one-sided boundary limit, not a stationary or OS state. -/
def boundaryTimeLimit {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (fs : List FaceFactor) : CReal :=
  ofQ'CauchySeq _ (boundaryTimeCauchy hw0 hw1 K width hK fs)

theorem boundaryTime_converges {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (fs : List FaceFactor) :
    ConvergesTo (fun n => ofQ' (sourceProbeMassRatio hw0 hw1 K width hK n fs))
      (boundaryTimeLimit hw0 hw1 K width hK fs) :=
  convergesTo_ofQ'CauchySeq _ (boundaryTimeCauchy hw0 hw1 K width hK fs)

/-- Geometric control against the actual limit representative; the displayed
representative threshold is n, without an existentially selected index. -/
theorem boundaryTime_approx_geometric {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (fs : List FaceFactor)
    (n k : Nat) (hnk : n ≤ k) :
    sourceProbeMassRatio hw0 hw1 K width hK n fs ≤
        (boundaryTimeLimit hw0 hw1 K width hK fs).approx k +
          mixRate hw0 hw1 width ^ n * (probeCap fs + probeCap fs) ∧
      (boundaryTimeLimit hw0 hw1 K width hK fs).approx k ≤
        sourceProbeMassRatio hw0 hw1 K width hK n fs +
          mixRate hw0 hw1 width ^ n * (probeCap fs + probeCap fs) :=
  sourceProbeMassRatio_commonTail hw0 hw1 K width hK n n
    (QMhat _ (boundaryTimeCauchy hw0 hw1 K width hK fs) k) fs
    (Nat.le_refl _) (Nat.le_trans hnk (self_le_QMhat _ _ k))

/-- The same CReal lies in every constructed bracket. Nesting, rather than
width decay alone, justifies this retained interval bound. -/
theorem boundaryTime_bracket {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (fs : List FaceFactor) (n : Nat) :
    leEv (ofQ' (sourceProbeBracket hw0 hw1 K width hK n fs).lower)
        (boundaryTimeLimit hw0 hw1 K width hK fs) ∧
      leEv (boundaryTimeLimit hw0 hw1 K width hK fs)
        (ofQ' (sourceProbeBracket hw0 hw1 K width hK n fs).upper) := by
  constructor
  · intro epsilon he
    refine ⟨n, fun k hk => ?_⟩
    have hb := sourceProbeMassRatio_later_bounds hw0 hw1 K width hK n
      (QMhat _ (boundaryTimeCauchy hw0 hw1 K width hK fs) k) fs
      (Nat.le_trans hk (self_le_QMhat _ _ k))
    exact Q'.le_trans' _ _ _ hb.1
      (Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt he))
  · intro epsilon he
    refine ⟨n, fun k hk => ?_⟩
    have hb := sourceProbeMassRatio_later_bounds hw0 hw1 K width hK n
      (QMhat _ (boundaryTimeCauchy hw0 hw1 K width hK fs) k) fs
      (Nat.le_trans hk (self_le_QMhat _ _ k))
    exact Q'.le_trans' _ _ _ hb.2
      (Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt he))

end YMGap.Continuum.BF4ExactSlabFixedSpatialBoundaryTimeLimit

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialBoundaryTimeLimit.boundaryTimeModulus
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialBoundaryTimeLimit.boundaryTime_budget
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialBoundaryTimeLimit.boundaryTimeCauchy
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialBoundaryTimeLimit.boundaryTimeLimit
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialBoundaryTimeLimit.boundaryTime_converges
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialBoundaryTimeLimit.boundaryTime_approx_geometric
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialBoundaryTimeLimit.boundaryTime_bracket
