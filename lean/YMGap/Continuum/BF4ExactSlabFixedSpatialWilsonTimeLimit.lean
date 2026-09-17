/-
# Original closed Wilson loops reach the existing polynomial time state

A supplied ordered loop on the width-only source slice is placed at the
literal middle time of the SAME selected original chain. Its actual temporal
ledger invariance and coefficient-sensitive source pin identify the original
numerator with the existing terminal-message pairing. The two reciprocals
cancel the SAME partition; no normalization or gauge observable is assumed.

Consequently the actual varying-extent finiteValue diagonal has the existing
polynomial-state CReal limit and its computed Cauchy modulus. The nome, width,
loop and heat cutoff stay fixed. This removes a physical realization gap for
these loop expectations, not the enlarged reflected OS pairing, cutoff/spatial
limit, full observable density, completed strict bound or continuum mass gap.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe
import YMGap.Continuum.BF4ExactSlabTemporalInvariantSweep
import YMGap.Continuum.BF4ExactSlabFixedSpatialOriginalMiddle
import YMGap.Continuum.BF4ExactSlabFixedSpatialPolynomialState
import YMGap.Constructive.ExpAddConv

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonTimeLimit

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialChainGeometry (chainIds chainIds_physical)
open YMGap.Continuum.BF4ExactSlabFixedSpatialChainAction
open YMGap.Continuum.BF4ExactSlabFixedSpatialOriginalIteration
open YMGap.Continuum.BF4ExactSlabFixedSpatialOriginalMiddle (swept_middle_pairing)
open YMGap.Continuum.BF4ExactSlabFixedSpatialMiddlePairing
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich (weightedMass)
open YMGap.Continuum.BF4ExactSlabFixedSpatialIterationLimit
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBracketOriginalScalar
open YMGap.Continuum.BF4ExactSlabFixedSpatialPolynomialMiddleTime (intervalMiddleModulus)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPolynomialState
open YMGap.Continuum.BF4ExactSlabTemporalGaugeWilsonWord
open YMGap.Continuum.BF4ExactSlabTemporalInvariantSweep
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe
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

/-- Original ordered loop, full original selected action and literal source
placement share one exact numerator. No face-trace recoding is used. -/
theorem original_loop_pairing {width start m n extent : Nat}
    (hw : width ≤ extent) (ht : start+(m+n) ≤ extent) (w : Q') (K : Nat)
    (loop : SourceLoop width) (spin : Nat) :
    quaternionHaar (B extent)
      (polyMul (character extent (loop.edges.map (shiftEntry (start+m))) spin)
        (originalChainAction w K extent width start (m+n))) ≈
      weightedMass w K width
        (polyMul (polyMul (terminalMessage w K width m)
          (sourceCharacter width loop.edges spin)) (terminalMessage w K width n)) := by
  have hm : start+m ≤ extent := by omega
  let placed := placeLoop hw hm loop
  let p := sourceCharacter width loop.edges spin
  let E := BF4ExactSlabFixedSpatialSliceCarrier.embedding hw hm
  have hpin : PaddedPolynomialCoeffEqv (B extent)
      (E.polynomial p) (character extent placed.edges spin) :=
    .of_prefix (sourceCharacter_pin hw hm loop.edges loop.physical spin)
  have ha := ambientChain_supported w K extent width start (m+n)
  have hreplace := (hpin.symm.mul (.refl _ _)).haar
    (supported_polyMul (character_supported extent placed.edges spin) ha)
    (supported_polyMul (E.polynomial_supported p) ha)
  have horiginal := invariant_original_chain_pairing w K extent width start (m+n)
    (character extent placed.edges spin) (character_supported extent placed.edges spin)
    (fun cut => ledger_invariant placed cut spin)
  exact Q'.eqv_trans _ _ _ horiginal (Q'.eqv_trans _ _ _ hreplace
    (swept_middle_pairing hw ht w K p (sourceCharacter_supported width loop.edges spin)))

/-- The existing positive middle denominator and the original finiteValue
reciprocal are reciprocals of the SAME selected-chain partition. -/
theorem middleRatio_originalLoop {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width start m n extent : Nat} (hw : width ≤ extent) (ht : start+(m+n) ≤ extent)
    (loop : SourceLoop width) (spin stage : Nat) :
    middleRatio hw0 hw1 (headCutoff w+stage) width (Nat.le_add_right _ _)
        m n (sourceCharacter width loop.edges spin) ≈
      finiteValue w hw0 hw1 extent (chainIds extent width start (m+n))
        (fun _ hi => chainIds_physical hi)
        (character extent (loop.edges.map (shiftEntry (start+m))) spin) stage := by
  let K := headCutoff w+stage
  let z := weightedMass w K width
    (polyMul (terminalMessage w K width m) (terminalMessage w K width n))
  have hz : (0 : Q') < z := terminalPair_positive hw0 hw1 K width (Nat.le_add_right _ _) m n
  let r := Q'.recipPos z hz
  let s := reciprocalTerm w hw0 hw1 extent (chainIds extent width start (m+n))
    (fun _ hi => chainIds_physical hi) stage
  have hr : z*r ≈ 1 := Q'.mul_recipPos_eqv z hz
  have hpartition : z ≈ compactPartition w K width (m+n) :=
    Q'.eqv_trans _ _ _ (terminalPair_total w K width m n)
      (weightedMass_iterate_compactPartition w K width (m+n))
  have hs : z*s ≈ 1 := Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ s hpartition)
    (compactPartition_reciprocal w hw0 hw1 hw ht stage)
  have hrs : r ≈ s := Q'.mul_left_cancel_of_pos hz (Q'.eqv_trans _ _ _ hr (Q'.eqv_symm hs))
  change weightedMass w K width
      (polyMul (polyMul (terminalMessage w K width m) (sourceCharacter width loop.edges spin))
        (terminalMessage w K width n)) * r ≈
    numerator w (B extent) extent (chainIds extent width start (m+n))
      (character extent (loop.edges.map (shiftEntry (start+m))) spin) K * s
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ r (Q'.eqv_symm (original_loop_pairing hw ht w K loop spin)))
    (Q'.mul_eqv_congr_left _ _ _ hrs)

/-- The original finite law on an explicitly admissible ambient slab. -/
def originalLoopScalar {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width : Nat} (loop : SourceLoop width) (spin stage m n : Nat) : Q' :=
  finiteValue w hw0 hw1 (width+(m+n))
    (chainIds (width+(m+n)) width 0 (m+n)) (fun _ hi => chainIds_physical hi)
    (character (width+(m+n)) (loop.edges.map (shiftEntry m)) spin) stage

theorem originalLoopScalar_pin {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width : Nat} (loop : SourceLoop width) (spin stage m n : Nat) :
    originalLoopScalar hw0 hw1 loop spin stage m n ≈
      middleRatio hw0 hw1 (headCutoff w+stage) width (Nat.le_add_right _ _)
        m n (sourceCharacter width loop.edges spin) := by
  simpa only [Nat.zero_add] using Q'.eqv_symm (middleRatio_originalLoop hw0 hw1
    (start := 0) (extent := width+(m+n)) (Nat.le_add_right _ _) (by omega) loop spin stage)

attribute [local irreducible] originalLoopScalar middleRatio baseLinks

/-- The actual original-loop diagonal carries the existing computed time modulus.
It is independent of the retained heat stage, not of nome, width or observable. -/
def originalLoopCauchy {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width : Nat} (loop : SourceLoop width) (spin stage : Nat) :
    QCauchy (fun t => originalLoopScalar hw0 hw1 loop spin stage t t) where
  M := intervalMiddleModulus hw0 hw1 width (polynomialCap (sourceCharacter width loop.edges spin))
  bound := by
    intro epsilon he i j hi hj
    have h := (polynomialCauchy hw0 hw1 (headCutoff w+stage) width (Nat.le_add_right _ _)
      (sourceCharacter width loop.edges spin) (sourceCharacter_supported width loop.edges spin)).bound
      epsilon he i j hi hj
    have hip := originalLoopScalar_pin hw0 hw1 loop spin stage i i
    have hjp := originalLoopScalar_pin hw0 hw1 loop spin stage j j
    exact ⟨Q'.le_trans' _ _ _ (Q'.le_of_eqv hip)
        (Q'.le_trans' _ _ _ h.1 (Q'.ge_of_eqv (Q'.add_eqv_congr_right _ _ epsilon hjp))),
      Q'.le_trans' _ _ _ (Q'.le_of_eqv hjp)
        (Q'.le_trans' _ _ _ h.2 (Q'.ge_of_eqv (Q'.add_eqv_congr_right _ _ epsilon hip)))⟩

theorem originalLoopCauchy_modulus {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width : Nat} (loop : SourceLoop width) (spin stage : Nat) (epsilon : Q') :
    (originalLoopCauchy hw0 hw1 loop spin stage).M epsilon =
      intervalMiddleModulus hw0 hw1 width
        (polynomialCap (sourceCharacter width loop.edges spin)) epsilon := rfl

/-- The target is the ALREADY constructed polynomial expectation with the
same source, parameters and normalization, not a newly chosen limit. -/
theorem originalLoop_converges {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width : Nat} (loop : SourceLoop width) (spin stage : Nat) :
    ConvergesTo (fun t => ofQ' (originalLoopScalar hw0 hw1 loop spin stage t t))
      (expectation hw0 hw1 (headCutoff w+stage) width (Nat.le_add_right _ _)
        (sourceCharacter width loop.edges spin) (sourceCharacter_supported width loop.edges spin)) :=
  TrigAddCReal.convergesTo_congr_seq
    (s := fun t => ofQ' (middleRatio hw0 hw1 (headCutoff w+stage) width
      (Nat.le_add_right _ _) t t (sourceCharacter width loop.edges spin)))
    (fun t => SumOfSquares.Equiv_of_approx_eqv
      (fun _ => Q'.eqv_symm (originalLoopScalar_pin hw0 hw1 loop spin stage t t)))
    (expectation_converges hw0 hw1 (headCutoff w+stage) width (Nat.le_add_right _ _)
      (sourceCharacter width loop.edges spin) (sourceCharacter_supported width loop.edges spin))

end YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonTimeLimit

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonTimeLimit.original_loop_pairing
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonTimeLimit.middleRatio_originalLoop
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonTimeLimit.originalLoopScalar
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonTimeLimit.originalLoopScalar_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonTimeLimit.originalLoopCauchy
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonTimeLimit.originalLoopCauchy_modulus
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonTimeLimit.originalLoop_converges
