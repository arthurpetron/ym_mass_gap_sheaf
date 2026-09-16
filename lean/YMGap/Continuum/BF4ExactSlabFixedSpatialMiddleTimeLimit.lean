/-
# Constructed two-sided interior time limit at fixed heat cutoff

The actual middle ratios at any two pairs of boundary lengths beyond s
differ in both order directions by at most 4*probeCap*mixRate^s. The existing
geometric cutoff supplies a rational Cauchy modulus for the diagonal, with
no dependence on the late heat cutoff. The returned CReal is also approached
by arbitrary rectangles whose two boundary lengths recede independently.

Every ratio retains the actual K/V messages and their original product
denominator, with one spatial V at the insertion. This is a fixed-nome,
fixed-width, fixed-cutoff scalar limit. Original geometric placement is a
separate pin; no stationary cylinder law, vacuum, cutoff removal, physical
OS identification, spacing-uniform bound or mass gap is asserted here.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialMiddleBracket
import YMGap.Continuum.PositiveContractionResidual
import YMGap.Continuum.GNSHilbertSpace

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialMiddleTimeLimit

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabTemporalSweep (FaceFactor)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferMixingRate
open YMGap.Continuum.BF4ExactSlabFixedSpatialProbe
open YMGap.Continuum.BF4ExactSlabFixedSpatialProbeInterval
open YMGap.Continuum.BF4ExactSlabFixedSpatialMiddlePairing (middleRatio)
open YMGap.Continuum.BF4ExactSlabFixedSpatialMiddleBracket (middleRatio_commonTail)
open YMGap.Continuum.PositiveContractionResidual (geometricCutoff geometric_bound)

/-- Computed common boundary-length threshold. There is no cutoff argument;
the existing geometric cutoff includes zero rate and zero probe cap. -/
def middleTimeModulus {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width : Nat) (fs : List FaceFactor) (epsilon : Q') : Nat :=
  geometricCutoff (mixRate hw0 hw1 width)
    ((probeCap fs + probeCap fs) + (probeCap fs + probeCap fs)) epsilon

theorem middleTime_budget {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width : Nat) (fs : List FaceFactor) (epsilon : Q') (he : (0 : Q') < epsilon)
    (s : Nat) (hs : middleTimeModulus hw0 hw1 width fs epsilon ≤ s) :
    mixRate hw0 hw1 width ^ s *
      ((probeCap fs + probeCap fs) + (probeCap fs + probeCap fs)) ≤ epsilon := by
  have hc := Q'.zero_le_add _ _ (sourceProbe_interval width fs).nonnegative
    (sourceProbe_interval width fs).nonnegative
  exact geometric_bound (mixRate_nonnegative hw0 hw1 width) (mixRate_lt_one hw0 hw1 width)
    (Q'.zero_le_add _ _ hc hc) he s hs

/-- The actual normalized interior diagonal, with denominator positivity
already supplied by the original transfer floor. -/
def middleTimeCauchy {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (fs : List FaceFactor) :
    QCauchy (fun t => middleRatio hw0 hw1 K width hK t t (sourceProbe width fs)) where
  M := middleTimeModulus hw0 hw1 width fs
  bound := by
    intro epsilon he i j hi hj
    have hb := middleRatio_commonTail hw0 hw1 K width hK
      (middleTimeModulus hw0 hw1 width fs epsilon) i i j j fs hi hi hj hj
    have heq := middleTime_budget hw0 hw1 width fs epsilon he
      (middleTimeModulus hw0 hw1 width fs epsilon) (Nat.le_refl _)
    exact ⟨Q'.le_trans' _ _ _ hb.1 (Q'.add_le_add_left _ _ _ heq),
      Q'.le_trans' _ _ _ hb.2 (Q'.add_le_add_left _ _ _ heq)⟩

/-- The Type-level Cauchy witness retains the displayed cutoff-independent modulus. -/
theorem middleTimeCauchy_modulus {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (fs : List FaceFactor) (epsilon : Q') :
    (middleTimeCauchy hw0 hw1 K width hK fs).M epsilon =
      middleTimeModulus hw0 hw1 width fs epsilon := rfl

/-- The explicit interior scalar limit, not a stationary law or a vacuum. -/
def middleTimeLimit {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (fs : List FaceFactor) : CReal :=
  ofQ'CauchySeq _ (middleTimeCauchy hw0 hw1 K width hK fs)

theorem middleTime_converges {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (fs : List FaceFactor) :
    ConvergesTo (fun t => ofQ' (middleRatio hw0 hw1 K width hK t t (sourceProbe width fs)))
      (middleTimeLimit hw0 hw1 K width hK fs) :=
  convergesTo_ofQ'CauchySeq _ (middleTimeCauchy hw0 hw1 K width hK fs)

/-- Every late rectangle approaches the SAME diagonal limit representative.
The two boundary lengths and representative index need only exceed s; they
need not be equal, ordered relative to each other, or follow a chosen schedule. -/
theorem middleTime_approx_rectangular {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (fs : List FaceFactor)
    (s m n k : Nat) (hsm : s ≤ m) (hsn : s ≤ n) (hsk : s ≤ k) :
    middleRatio hw0 hw1 K width hK m n (sourceProbe width fs) ≤
        (middleTimeLimit hw0 hw1 K width hK fs).approx k +
          mixRate hw0 hw1 width ^ s *
            ((probeCap fs + probeCap fs) + (probeCap fs + probeCap fs)) ∧
      (middleTimeLimit hw0 hw1 K width hK fs).approx k ≤
        middleRatio hw0 hw1 K width hK m n (sourceProbe width fs) +
          mixRate hw0 hw1 width ^ s *
            ((probeCap fs + probeCap fs) + (probeCap fs + probeCap fs)) :=
  middleRatio_commonTail hw0 hw1 K width hK s m n
    (QMhat _ (middleTimeCauchy hw0 hw1 K width hK fs) k)
    (QMhat _ (middleTimeCauchy hw0 hw1 K width hK fs) k) fs hsm hsn
    (Nat.le_trans hsk (self_le_QMhat _ _ k))
    (Nat.le_trans hsk (self_le_QMhat _ _ k))

end YMGap.Continuum.BF4ExactSlabFixedSpatialMiddleTimeLimit

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialMiddleTimeLimit.middleTimeModulus
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialMiddleTimeLimit.middleTime_budget
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialMiddleTimeLimit.middleTimeCauchy
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialMiddleTimeLimit.middleTimeCauchy_modulus
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialMiddleTimeLimit.middleTimeLimit
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialMiddleTimeLimit.middleTime_converges
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialMiddleTimeLimit.middleTime_approx_rectangular
