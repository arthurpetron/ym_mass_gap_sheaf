/-
# Original multi-time Wilson expressions reach the existing window state

Each source generator is a supplied closed spatial loop on the width-only
link carrier. Its offset, spin and every signed algebra operation are retained
by physical placement. One common temporal sweep acts on the expression AND
the full selected chain action. Exact placement then identifies the original
numerator with the pre-existing window pairing. Both reciprocals normalize
the SAME partition at the SAME retained heat cutoff.

The original finiteValue diagonal has the existing polynomialWindowLimit and
its explicit Cauchy modulus. Nome, width, fixed window and heat cutoff stay
fixed; only the two external time boundaries recede. This is not a cutoff/
spatial limit, enlarged OS completion, strict bound or continuum construction.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
import YMGap.Continuum.BF4ExactSlabFixedSpatialOriginalWindow

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowTimeLimit

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialChainCarrier (embedding)
open YMGap.Continuum.BF4ExactSlabFixedSpatialChainGeometry (chainIds chainIds_physical)
open YMGap.Continuum.BF4ExactSlabFixedSpatialChainAction
open YMGap.Continuum.BF4ExactSlabFixedSpatialOriginalIteration
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialMiddlePairing (terminalPair_total)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich (weightedMass)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferMixingRate (mixRate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialIterationLimit
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBracketOriginalScalar
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPairing
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowTwoBoundary (windowTimeCap)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowTimeLimit
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowEmbedding
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.BF4ExactSlabTemporalInvariantSweep
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4ExactSlabAllNomeFaceSetReciprocal (reciprocalTerm)
open YMGap.Continuum.BF4ExactSlabAllNomeFaceSetExpectation (finiteValue)
open YMGap.Continuum.BF4ExactSlabPolynomialInsertionLimit (numerator)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHaarBlockEmbedding
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.QuaternionHaarSupportedPolynomialInterval (polynomialCap)
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local notation:max "B" extent:arg => List.length (boundaryCompleteSlabLinks extent)
local infix:50 " ≈ " => Q'.eqv

/-- Whole original expression and action, with every signed cross term and
the terminal spatial weight retained. -/
theorem original_window_pairing {width start m L n extent : Nat}
    (hw : width ≤ extent) (ht : start+(m+(L+n)) ≤ extent) (w : Q') (K : Nat)
    (e : WindowExpression width) (he : Within L e) :
    quaternionHaar (B extent)
      (polyMul (placedPolynomial extent (start+m) e)
        (originalChainAction w K extent width start (m+(L+n)))) ≈
      weightedMass w K width
        (polyMul (observedMessage w K width m L (sourcePolynomial e))
          (terminalMessage w K width n)) := by
  have hm : start+m+L ≤ extent := by omega
  let E := embedding L (start := start+m) hw hm
  have hpin := expression_pin hw hm e he
  have ha := ambientChain_supported w K extent width start (m+(L+n))
  have hreplace := (hpin.symm.mul (.refl _ _)).haar
    (supported_polyMul (placed_supported extent (start+m) e) ha)
    (supported_polyMul (E.polynomial_supported (sourcePolynomial e)) ha)
  have horiginal := invariant_original_chain_pairing w K extent width start (m+(L+n))
    (placedPolynomial extent (start+m) e) (placed_supported extent (start+m) e)
    (fun cut => placed_ledger_invariant hw hm e he cut)
  exact Q'.eqv_trans _ _ _ horiginal (Q'.eqv_trans _ _ _ hreplace
    (swept_window_pairing hw ht w K (sourcePolynomial e) (source_supported L e he)))

/-- Exact original finiteValue normalization, not a replacement cylinder law. -/
theorem windowRatio_originalFiniteValue {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width start m L n extent : Nat} (hw : width ≤ extent) (ht : start+(m+(L+n)) ≤ extent)
    (e : WindowExpression width) (he : Within L e) (stage : Nat) :
    windowRatio hw0 hw1 (headCutoff w+stage) width (Nat.le_add_right _ _)
        m L n (sourcePolynomial e) ≈
      finiteValue w hw0 hw1 extent (chainIds extent width start (m+(L+n)))
        (fun _ hi => chainIds_physical hi) (placedPolynomial extent (start+m) e) stage := by
  let K := headCutoff w+stage
  let z := weightedMass w K width
    (polyMul (terminalMessage w K width (m+L)) (terminalMessage w K width n))
  have hz : (0 : Q') < z := terminalPair_positive hw0 hw1 K width (Nat.le_add_right _ _) (m+L) n
  let r := Q'.recipPos z hz
  let s := reciprocalTerm w hw0 hw1 extent (chainIds extent width start (m+(L+n)))
    (fun _ hi => chainIds_physical hi) stage
  have hr : z*r ≈ 1 := Q'.mul_recipPos_eqv z hz
  have hpartition : z ≈ compactPartition w K width (m+(L+n)) := by
    simpa only [Nat.add_assoc] using Q'.eqv_trans _ _ _ (terminalPair_total w K width (m+L) n)
      (weightedMass_iterate_compactPartition w K width ((m+L)+n))
  have hs : z*s ≈ 1 := Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ s hpartition)
    (compactPartition_reciprocal w hw0 hw1 hw ht stage)
  have hrs : r ≈ s := Q'.mul_left_cancel_of_pos hz (Q'.eqv_trans _ _ _ hr (Q'.eqv_symm hs))
  change weightedMass w K width
      (polyMul (observedMessage w K width m L (sourcePolynomial e))
        (terminalMessage w K width n)) * r ≈
    numerator w (B extent) extent (chainIds extent width start (m+(L+n)))
      (placedPolynomial extent (start+m) e) K * s
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ r (Q'.eqv_symm (original_window_pairing hw ht w K e he)))
    (Q'.mul_eqv_congr_left _ _ _ hrs)

/-- Computed original ambient slab and actual moving expression placement. -/
def originalWindowScalar {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width : Nat} (L : Nat) (e : WindowExpression width) (stage m n : Nat) : Q' :=
  finiteValue w hw0 hw1 (width+(m+(L+n)))
    (chainIds (width+(m+(L+n))) width 0 (m+(L+n)))
    (fun _ hi => chainIds_physical hi) (placedPolynomial (width+(m+(L+n))) m e) stage

theorem originalWindowScalar_pin {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width : Nat} (L : Nat) (e : WindowExpression width) (he : Within L e)
    (stage m n : Nat) :
    originalWindowScalar hw0 hw1 L e stage m n ≈
      windowRatio hw0 hw1 (headCutoff w+stage) width (Nat.le_add_right _ _)
        m L n (sourcePolynomial e) := by
  simpa only [Nat.zero_add] using Q'.eqv_symm (windowRatio_originalFiniteValue hw0 hw1
    (start := 0) (m := m) (L := L) (n := n) (extent := width+(m+(L+n)))
    (Nat.le_add_right _ _) (by omega) e he stage)

attribute [local irreducible] originalWindowScalar windowRatio baseLinks

/-- Actual original-law Cauchy data. The stored modulus keeps nome, width and
the full signed source expression's computed cap, but has no heat-stage input. -/
def originalWindowCauchy {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width : Nat} (L : Nat) (e : WindowExpression width) (he : Within L e) (stage : Nat) :
    QCauchy (fun t => originalWindowScalar hw0 hw1 L e stage t t) where
  M := windowTimeModulus hw0 hw1 width (polynomialCap (sourcePolynomial e))
  bound := by
    intro epsilon heps i j hi hj
    have h := (polynomialWindowCauchy hw0 hw1 (headCutoff w+stage) width
      (Nat.le_add_right _ _) L (sourcePolynomial e) (source_supported L e he)).bound
      epsilon heps i j hi hj
    have hip := originalWindowScalar_pin hw0 hw1 L e he stage i i
    have hjp := originalWindowScalar_pin hw0 hw1 L e he stage j j
    exact ⟨Q'.le_trans' _ _ _ (Q'.le_of_eqv hip)
        (Q'.le_trans' _ _ _ h.1 (Q'.ge_of_eqv (Q'.add_eqv_congr_right _ _ epsilon hjp))),
      Q'.le_trans' _ _ _ (Q'.le_of_eqv hjp)
        (Q'.le_trans' _ _ _ h.2 (Q'.ge_of_eqv (Q'.add_eqv_congr_right _ _ epsilon hip)))⟩

theorem originalWindowCauchy_modulus {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width : Nat} (L : Nat) (e : WindowExpression width) (he : Within L e)
    (stage : Nat) (epsilon : Q') :
    (originalWindowCauchy hw0 hw1 L e he stage).M epsilon =
      windowTimeModulus hw0 hw1 width (polynomialCap (sourcePolynomial e)) epsilon := rfl

/-- SAME constructed CReal window limit, now identified with original multi-time
Wilson expressions. No new limiting object or normalization is substituted. -/
theorem originalWindow_converges {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width : Nat} (L : Nat) (e : WindowExpression width) (he : Within L e) (stage : Nat) :
    ConvergesTo (fun t => ofQ' (originalWindowScalar hw0 hw1 L e stage t t))
      (polynomialWindowLimit hw0 hw1 (headCutoff w+stage) width (Nat.le_add_right _ _)
        L (sourcePolynomial e) (source_supported L e he)) :=
  TrigAddCReal.convergesTo_congr_seq
    (s := fun t => ofQ' (windowRatio hw0 hw1 (headCutoff w+stage) width
      (Nat.le_add_right _ _) t L t (sourcePolynomial e)))
    (fun t => SumOfSquares.Equiv_of_approx_eqv
      (fun _ => Q'.eqv_symm (originalWindowScalar_pin hw0 hw1 L e he stage t t)))
    (polynomialWindow_converges hw0 hw1 (headCutoff w+stage) width (Nat.le_add_right _ _)
      L (sourcePolynomial e) (source_supported L e he))

/-- Both original boundary distances and the CReal representative index vary
independently, retaining the explicit common geometric error. -/
theorem originalWindow_approx_rectangular {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width : Nat} (L : Nat) (e : WindowExpression width) (he : Within L e)
    (stage s m n k : Nat) (hm : s+1 ≤ m) (hn : s+1 ≤ n) (hk : s+1 ≤ k) :
    originalWindowScalar hw0 hw1 L e stage m n ≤
        (polynomialWindowLimit hw0 hw1 (headCutoff w+stage) width (Nat.le_add_right _ _)
          L (sourcePolynomial e) (source_supported L e he)).approx k +
          mixRate hw0 hw1 width ^ s * windowTimeCap hw0 hw1 width (polynomialCap (sourcePolynomial e)) ∧
      (polynomialWindowLimit hw0 hw1 (headCutoff w+stage) width (Nat.le_add_right _ _)
        L (sourcePolynomial e) (source_supported L e he)).approx k ≤
        originalWindowScalar hw0 hw1 L e stage m n +
          mixRate hw0 hw1 width ^ s * windowTimeCap hw0 hw1 width (polynomialCap (sourcePolynomial e)) := by
  have hb := polynomialWindow_approx_rectangular hw0 hw1 (headCutoff w+stage) width
    (Nat.le_add_right _ _) L (sourcePolynomial e) (source_supported L e he) s m n k hm hn hk
  have hp := originalWindowScalar_pin hw0 hw1 L e he stage m n
  exact ⟨Q'.le_trans' _ _ _ (Q'.le_of_eqv hp) hb.1,
    Q'.le_trans' _ _ _ hb.2 (Q'.add_le_add_right _ _ _ (Q'.ge_of_eqv hp))⟩

end YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowTimeLimit

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowTimeLimit.original_window_pairing
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowTimeLimit.windowRatio_originalFiniteValue
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowTimeLimit.originalWindowScalar
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowTimeLimit.originalWindowScalar_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowTimeLimit.originalWindowCauchy
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowTimeLimit.originalWindowCauchy_modulus
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowTimeLimit.originalWindow_converges
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowTimeLimit.originalWindow_approx_rectangular
