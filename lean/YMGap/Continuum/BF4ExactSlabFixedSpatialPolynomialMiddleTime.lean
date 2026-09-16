/-
# The actual interior limit for any certified supported polynomial

The two-boundary argument uses a polynomial only through its support and
computed interval certificate. Keep that input general so addition and
signed scaling stay in one observable algebra. The scalar is always the
existing middleRatio with its SAME original terminal-pair denominator.

This module consumes an interval as Type-level data. The separate finite
polynomial compiler supplies it for every supported polynomial. No physical
OS state, stationary cylinder law, cutoff removal or mass gap is asserted.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialMiddleBracket
import YMGap.Continuum.PositiveContractionResidual
import YMGap.Continuum.GNSHilbertSpace

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialPolynomialMiddleTime

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat (kineticWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich (weightedMass)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferMixingRate
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBracketDecay
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBracketNesting
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialMiddlePairing (middleRatio)
open YMGap.Continuum.BF4ExactSlabFixedSpatialMiddleRatioPins
open YMGap.Continuum.BF4ExactSlabFixedSpatialMiddleBracket (intervalTimesMessage)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHeadChainComposition
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.PositiveContractionResidual (geometricCutoff geometric_bound)

local notation:max "N" width:arg => List.length (baseLinks width)
local infix:50 " ≈ " => Q'.eqv

attribute [local irreducible] weightedMass kineticWeight spatialWeight baseLinks mixRate middleRatio

private def bracket {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (m n : Nat) {p : RatPoly} {c : Q'}
    (I : Interval (N width) p c) :
    Bracket width
      (iterateStep (N width) (kineticWeight w K width) (spatialWeight w K width) n
        (polyMul (terminalMessage w K width m) p))
      (iterateStep (N width) (kineticWeight w K width) (spatialWeight w K width) n
        (terminalMessage w K width m)) :=
  iterateBracket hw0 hw1 K width hK n
    (supported_polyMul (terminalMessage_supported w K width m) I.support)
    (terminalMessage_supported w K width m)
    (terminalMessage_certificate hw0 hw1 K width hK m)
    (terminalMessage_mass_positive hw0 hw1 K width hK m)
    (intervalTimesMessage I (terminalMessage_certificate hw0 hw1 K width hK m))

private theorem bracket_width {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (m n : Nat) {p : RatPoly} {c : Q'}
    (I : Interval (N width) p c) :
    (bracket hw0 hw1 K width hK m n I).upper + -(bracket hw0 hw1 K width hK m n I).lower ≈
      mixRate hw0 hw1 width ^ n * (c+c) :=
  Q'.eqv_trans _ _ _
    (iterateBracket_width hw0 hw1 K width hK n
      (supported_polyMul (terminalMessage_supported w K width m) I.support)
      (terminalMessage_supported w K width m)
      (terminalMessage_certificate hw0 hw1 K width hK m)
      (terminalMessage_mass_positive hw0 hw1 K width hK m)
      (intervalTimesMessage I (terminalMessage_certificate hw0 hw1 K width hK m)))
    (Q'.mul_eqv_congr_left _ _ _ (Q'.add_eqv_congr' (Q'.eqv_refl _) (Q'.neg_neg_eqv c)))

private theorem later_bounds {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (m n j : Nat) {p : RatPoly} {c : Q'}
    (I : Interval (N width) p c) (hnj : n ≤ j) :
    (bracket hw0 hw1 K width hK m n I).lower ≤ middleRatio hw0 hw1 K width hK m j p ∧
      middleRatio hw0 hw1 K width hK m j p ≤ (bracket hw0 hw1 K width hK m n I).upper := by
  have he := middleRatio_iterate hw0 hw1 K width hK m j I.support
  have hb := massRatio_bounds hw0 hw1 K width hK
    (iterateWeightedMass_positive hw0 hw1 K width hK j
      (terminalMessage_supported w K width m)
      (terminalMessage_certificate hw0 hw1 K width hK m)
      (terminalMessage_mass_positive hw0 hw1 K width hK m))
    (bracket hw0 hw1 K width hK m j I)
  have hn := iterateBracket_nested hw0 hw1 K width hK n j hnj
    (supported_polyMul (terminalMessage_supported w K width m) I.support)
    (terminalMessage_supported w K width m)
    (terminalMessage_certificate hw0 hw1 K width hK m)
    (terminalMessage_mass_positive hw0 hw1 K width hK m)
    (intervalTimesMessage I (terminalMessage_certificate hw0 hw1 K width hK m))
  exact ⟨Q'.le_trans' _ _ _ hn.1 (Q'.le_trans' _ _ _ hb.1 (Q'.ge_of_eqv he)),
    Q'.le_trans' _ _ _ (Q'.le_of_eqv he) (Q'.le_trans' _ _ _ hb.2 hn.2)⟩

private theorem common_interval (l u x y C : Q')
    (hx : l ≤ x ∧ x ≤ u) (hy : l ≤ y ∧ y ≤ u) (hc : u + -l ≈ C) :
    x ≤ y+C ∧ y ≤ x+C := by
  have hcancel : l + (u + -l) ≈ u := poly_identity_of_normal_eq
    (.add (.var 0) (.add (.var 1) (.neg (.var 0)))) (.var 1) (by decide)
    (fun | 0 => l | _ => u)
  have hup (z : Q') (hz : l ≤ z) : u ≤ z+C :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv hcancel)
      (Q'.le_trans' _ _ _ (Q'.add_le_add_right l z (u + -l) hz)
        (Q'.le_of_eqv (Q'.add_eqv_congr' (Q'.eqv_refl z) hc)))
  exact ⟨Q'.le_trans' _ _ _ hx.2 (hup y hy.1), Q'.le_trans' _ _ _ hy.2 (hup x hx.1)⟩

private theorem right_tail {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (m s n j : Nat) {p : RatPoly} {c : Q'}
    (I : Interval (N width) p c) (hsn : s ≤ n) (hsj : s ≤ j) :
    middleRatio hw0 hw1 K width hK m n p ≤ middleRatio hw0 hw1 K width hK m j p +
        mixRate hw0 hw1 width ^ s * (c+c) ∧
      middleRatio hw0 hw1 K width hK m j p ≤ middleRatio hw0 hw1 K width hK m n p +
        mixRate hw0 hw1 width ^ s * (c+c) :=
  common_interval _ _ _ _ _
    (later_bounds hw0 hw1 K width hK m s n I hsn)
    (later_bounds hw0 hw1 K width hK m s j I hsj)
    (bracket_width hw0 hw1 K width hK m s I)

private theorem two_hops (x y z r c : Q') (hxy : x ≤ y+r*c) (hyz : y ≤ z+r*c) :
    x ≤ z+r*(c+c) :=
  Q'.le_trans' _ _ _ hxy
    (Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ (r*c) hyz)
      (Q'.le_of_eqv (poly_identity_of_normal_eq
        (.add (.add (.var 0) (.mul (.var 1) (.var 2))) (.mul (.var 1) (.var 2)))
        (.add (.var 0) (.mul (.var 1) (.add (.var 2) (.var 2)))) (by decide)
        (fun | 0 => z | 1 => r | _ => c))))

/-- The same quantitative two-sided estimate on ANY certified supported
polynomial. No special probe-list representation is required. -/
theorem intervalMiddle_commonTail {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (s m n i j : Nat) {p : RatPoly} {c : Q'}
    (I : Interval (N width) p c) (hsm : s ≤ m) (hsn : s ≤ n) (hsi : s ≤ i) (hsj : s ≤ j) :
    middleRatio hw0 hw1 K width hK m n p ≤ middleRatio hw0 hw1 K width hK i j p +
        mixRate hw0 hw1 width ^ s * ((c+c)+(c+c)) ∧
      middleRatio hw0 hw1 K width hK i j p ≤ middleRatio hw0 hw1 K width hK m n p +
        mixRate hw0 hw1 width ^ s * ((c+c)+(c+c)) := by
  have hr := right_tail hw0 hw1 K width hK m s n j I hsn hsj
  have hl := right_tail hw0 hw1 K width hK j s m i I hsm hsi
  have hm := middleRatio_swap hw0 hw1 K width hK m j p
  have hi := middleRatio_swap hw0 hw1 K width hK i j p
  have hforward := Q'.le_trans' _ _ _ (Q'.le_of_eqv hm)
    (Q'.le_trans' _ _ _ hl.1 (Q'.add_le_add_right _ _ _ (Q'.ge_of_eqv hi)))
  have hback := Q'.le_trans' _ _ _ (Q'.le_of_eqv hi)
    (Q'.le_trans' _ _ _ hl.2 (Q'.add_le_add_right _ _ _ (Q'.ge_of_eqv hm)))
  exact ⟨two_hops _ _ _ _ _ hr.1 hforward, two_hops _ _ _ _ _ hback hr.2⟩

/-- Explicit time modulus from the supplied rational cap, with no K argument. -/
def intervalMiddleModulus {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width : Nat) (c epsilon : Q') : Nat :=
  geometricCutoff (mixRate hw0 hw1 width) ((c+c)+(c+c)) epsilon

/-- Cauchy data for the actual normalized polynomial diagonal. -/
def intervalMiddleCauchy {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) {p : RatPoly} {c : Q'}
    (I : Interval (N width) p c) :
    QCauchy (fun t => middleRatio hw0 hw1 K width hK t t p) where
  M := intervalMiddleModulus hw0 hw1 width c
  bound := by
    intro epsilon he i j hi hj
    let s := intervalMiddleModulus hw0 hw1 width c epsilon
    have hb := intervalMiddle_commonTail hw0 hw1 K width hK s i i j j I hi hi hj hj
    have hc := Q'.zero_le_add _ _ I.nonnegative I.nonnegative
    have heq := geometric_bound (mixRate_nonnegative hw0 hw1 width)
      (mixRate_lt_one hw0 hw1 width) (Q'.zero_le_add _ _ hc hc) he s (Nat.le_refl s)
    exact ⟨Q'.le_trans' _ _ _ hb.1 (Q'.add_le_add_left _ _ _ heq),
      Q'.le_trans' _ _ _ hb.2 (Q'.add_le_add_left _ _ _ heq)⟩

/-- Constructed polynomial expectation. Its algebraic laws are supplied by
the same-denominator finite laws and uniqueness of this actual limit. -/
def intervalMiddleLimit {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) {p : RatPoly} {c : Q'}
    (I : Interval (N width) p c) : CReal :=
  ofQ'CauchySeq _ (intervalMiddleCauchy hw0 hw1 K width hK I)

theorem intervalMiddle_converges {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) {p : RatPoly} {c : Q'}
    (I : Interval (N width) p c) :
    ConvergesTo (fun t => ofQ' (middleRatio hw0 hw1 K width hK t t p))
      (intervalMiddleLimit hw0 hw1 K width hK I) :=
  convergesTo_ofQ'CauchySeq _ (intervalMiddleCauchy hw0 hw1 K width hK I)

/-- The full late rectangle approaches the returned CReal, including
independent boundary lengths and independent representative index. -/
theorem intervalMiddle_approx_rectangular {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) {p : RatPoly} {c : Q'}
    (I : Interval (N width) p c) (s m n k : Nat) (hsm : s ≤ m) (hsn : s ≤ n) (hsk : s ≤ k) :
    middleRatio hw0 hw1 K width hK m n p ≤
        (intervalMiddleLimit hw0 hw1 K width hK I).approx k +
          mixRate hw0 hw1 width ^ s * ((c+c)+(c+c)) ∧
      (intervalMiddleLimit hw0 hw1 K width hK I).approx k ≤
        middleRatio hw0 hw1 K width hK m n p + mixRate hw0 hw1 width ^ s * ((c+c)+(c+c)) :=
  intervalMiddle_commonTail hw0 hw1 K width hK s m n
    (QMhat _ (intervalMiddleCauchy hw0 hw1 K width hK I) k)
    (QMhat _ (intervalMiddleCauchy hw0 hw1 K width hK I) k) I hsm hsn
    (Nat.le_trans hsk (self_le_QMhat _ _ k)) (Nat.le_trans hsk (self_le_QMhat _ _ k))

end YMGap.Continuum.BF4ExactSlabFixedSpatialPolynomialMiddleTime

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPolynomialMiddleTime.intervalMiddle_commonTail
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPolynomialMiddleTime.intervalMiddleModulus
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPolynomialMiddleTime.intervalMiddleCauchy
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPolynomialMiddleTime.intervalMiddleLimit
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPolynomialMiddleTime.intervalMiddle_converges
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPolynomialMiddleTime.intervalMiddle_approx_rectangular
