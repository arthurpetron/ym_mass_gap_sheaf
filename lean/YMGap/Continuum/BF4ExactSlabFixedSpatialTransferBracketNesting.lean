/-
# Nested actual-transfer brackets and common-tail ratio bounds

The two certified residual gains are nonnegative. Thus refresh increases
the lower endpoint and decreases the upper endpoint. Induction through the
existing actual K/V bracket recursion makes every later interval lie inside
every earlier one, with all comparison-message mass positivity propagated.

Every later signed-source-probe mass ratio consequently lies in the earlier
bracket. Two ratios beyond the same time n differ in both order directions
by at most mixRate^n * (probeCap + probeCap). The actual V-weighted numerator
and denominator are unchanged, including the terminal V. No absolute-value
or positive-rate hypothesis is needed; the rate-zero case is included.

This is fixed-nome, fixed-width, late-cutoff temporal control. Original
geometric placement still uses its existing face and extent guards. No
stationary state, OS identification, width/spacing-uniform estimate, or
physical mass gap is asserted here.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBracketDecay

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBracketNesting

set_option autoImplicit false
set_option maxHeartbeats 2000000

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactSlabTemporalSweep (FaceFactor)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat (kineticWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferOrder
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich (weightedMass)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferMixingRate
open YMGap.Continuum.BF4ExactSlabFixedSpatialWeightedMass
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBracketDecay
open YMGap.Continuum.BF4ExactSlabFixedSpatialProbe
open YMGap.Continuum.BF4ExactSlabFixedSpatialProbeInterval
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.QuaternionHaarSquareCertificate

local notation:max "N" width:arg => List.length (baseLinks width)
local infix:50 " ≈ " => Q'.eqv

-- Match the proved APIs without reducing face enumeration or Haar arithmetic.
attribute [local irreducible] weightedMass kineticWeight spatialWeight baseLinks
attribute [local irreducible] gain mixRate sourceProbeMassRatio

private theorem sub_le_self (a b : Q') (hb : (0 : Q') ≤ b) : a + -b ≤ a := by
  have hn : -b ≤ (0 : Q') := by simpa only using Q'.neg_le_neg hb
  exact Q'.le_trans' _ _ _ (Q'.add_le_add_left a _ _ hn)
    (Q'.le_of_eqv (QPoly.q_add_zero_eqv a))

/-- Each nonnegative actual gain tightens its own endpoint. -/
theorem refresh_nested {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) {f g : RatPoly}
    (hf : SupportedQuaternionBlocks (N width) f) (hg : SupportedQuaternionBlocks (N width) g)
    (G : Certificate (N width) g) (hmass : (0 : Q') < weightedMass w K width g)
    (B : Bracket width f g) :
    B.lower ≤ (refresh hw0 hw1 K width hK hf hg G hmass B).lower ∧
      (refresh hw0 hw1 K width hK hf hg G hmass B).upper ≤ B.upper :=
  ⟨Q'.add_le_self_of_nonneg B.lower _
      (gain_nonnegative hw0 hw1 K width hK g _ hmass B.lowerCertificate),
    sub_le_self B.upper _
      (gain_nonnegative hw0 hw1 K width hK g _ hmass B.upperCertificate)⟩

/-- Successive iterates are nested, following the actual tail-recursive step order. -/
theorem iterateBracket_successor_nested {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) {f g : RatPoly}
    (hf : SupportedQuaternionBlocks (N width) f) (hg : SupportedQuaternionBlocks (N width) g)
    (G : Certificate (N width) g) (hmass : (0 : Q') < weightedMass w K width g)
    (B : Bracket width f g) :
    (iterateBracket hw0 hw1 K width hK n hf hg G hmass B).lower ≤
        (iterateBracket hw0 hw1 K width hK (n+1) hf hg G hmass B).lower ∧
      (iterateBracket hw0 hw1 K width hK (n+1) hf hg G hmass B).upper ≤
        (iterateBracket hw0 hw1 K width hK n hf hg G hmass B).upper := by
  induction n generalizing f g with
  | zero => exact refresh_nested hw0 hw1 K width hK hf hg G hmass B
  | succ n ih =>
      exact ih (f := transferStep w K width f) (g := transferStep w K width g)
        (transferStep_supported w K width (input := f) hf)
        (transferStep_supported w K width (input := g) hg)
        (transferStep_certificate hw0 hw1 K width hK (f := g) hg G)
        (weightedMass_transfer_positive hw0 hw1 K width hK (f := g) hg G hmass)
        (refresh hw0 hw1 K width hK (f := f) (g := g) hf hg G hmass B)

private theorem endpoint_sequences_nested (l u : Nat → Q')
    (hstep : ∀ k, l k ≤ l (k+1) ∧ u (k+1) ≤ u k)
    (n m : Nat) (hnm : n ≤ m) : l n ≤ l m ∧ u m ≤ u n := by
  induction hnm with
  | refl => exact ⟨Q'.le_refl' _, Q'.le_refl' _⟩
  | @step m _ ih =>
      exact ⟨Q'.le_trans' _ _ _ ih.1 (hstep m).1,
        Q'.le_trans' _ _ _ (hstep m).2 ih.2⟩

/-- Any later actual bracket lies inside the earlier one. -/
theorem iterateBracket_nested {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n m : Nat) (hnm : n ≤ m) {f g : RatPoly}
    (hf : SupportedQuaternionBlocks (N width) f) (hg : SupportedQuaternionBlocks (N width) g)
    (G : Certificate (N width) g) (hmass : (0 : Q') < weightedMass w K width g)
    (B : Bracket width f g) :
    (iterateBracket hw0 hw1 K width hK n hf hg G hmass B).lower ≤
        (iterateBracket hw0 hw1 K width hK m hf hg G hmass B).lower ∧
      (iterateBracket hw0 hw1 K width hK m hf hg G hmass B).upper ≤
        (iterateBracket hw0 hw1 K width hK n hf hg G hmass B).upper :=
  endpoint_sequences_nested
    (fun k => (iterateBracket hw0 hw1 K width hK k hf hg G hmass B).lower)
    (fun k => (iterateBracket hw0 hw1 K width hK k hf hg G hmass B).upper)
    (fun k => iterateBracket_successor_nested hw0 hw1 K width hK k hf hg G hmass B)
    n m hnm

/-- Inhabited signed-probe brackets inherit the same all-later-time nesting. -/
theorem sourceProbeBracket_nested {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n m : Nat) (fs : List FaceFactor) (hnm : n ≤ m) :
    (sourceProbeBracket hw0 hw1 K width hK n fs).lower ≤
        (sourceProbeBracket hw0 hw1 K width hK m fs).lower ∧
      (sourceProbeBracket hw0 hw1 K width hK m fs).upper ≤
        (sourceProbeBracket hw0 hw1 K width hK n fs).upper :=
  iterateBracket_nested hw0 hw1 K width hK n m hnm (f := sourceProbe width fs) (g := polyOne)
    (sourceProbe_supported width fs) (supported_one (N width)) (Certificate.one (N width))
    (weightedMass_one_positive hw0 hw1 K width hK) (ofInterval (sourceProbe_interval width fs))

/-- Every later original V-weighted mass ratio is contained in the earlier interval. -/
theorem sourceProbeMassRatio_later_bounds {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n m : Nat) (fs : List FaceFactor) (hnm : n ≤ m) :
    (sourceProbeBracket hw0 hw1 K width hK n fs).lower ≤
        sourceProbeMassRatio hw0 hw1 K width hK m fs ∧
      sourceProbeMassRatio hw0 hw1 K width hK m fs ≤
        (sourceProbeBracket hw0 hw1 K width hK n fs).upper := by
  have hn := sourceProbeBracket_nested hw0 hw1 K width hK n m fs hnm
  have hm := sourceProbeMassRatio_bounds hw0 hw1 K width hK m fs
  exact ⟨Q'.le_trans' _ _ _ hn.1 hm.1, Q'.le_trans' _ _ _ hm.2 hn.2⟩

private theorem common_interval_bound (l u x y C : Q')
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

/-- A common earlier threshold controls BOTH arbitrary later times. No time
order split, power monotonicity, or division by the rate is used. -/
theorem sourceProbeMassRatio_commonTail {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n i j : Nat) (fs : List FaceFactor)
    (hni : n ≤ i) (hnj : n ≤ j) :
    sourceProbeMassRatio hw0 hw1 K width hK i fs ≤
        sourceProbeMassRatio hw0 hw1 K width hK j fs +
          mixRate hw0 hw1 width ^ n * (probeCap fs + probeCap fs) ∧
      sourceProbeMassRatio hw0 hw1 K width hK j fs ≤
        sourceProbeMassRatio hw0 hw1 K width hK i fs +
          mixRate hw0 hw1 width ^ n * (probeCap fs + probeCap fs) :=
  common_interval_bound _ _ _ _ _
    (sourceProbeMassRatio_later_bounds hw0 hw1 K width hK n i fs hni)
    (sourceProbeMassRatio_later_bounds hw0 hw1 K width hK n j fs hnj)
    (sourceProbeBracket_width hw0 hw1 K width hK n fs)

/-- The requested two-time bound, normalized by the actual original mass at each time. -/
theorem sourceProbeMassRatio_twoTime {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n m : Nat) (fs : List FaceFactor) (hnm : n ≤ m) :
    sourceProbeMassRatio hw0 hw1 K width hK m fs ≤
        sourceProbeMassRatio hw0 hw1 K width hK n fs +
          mixRate hw0 hw1 width ^ n * (probeCap fs + probeCap fs) ∧
      sourceProbeMassRatio hw0 hw1 K width hK n fs ≤
        sourceProbeMassRatio hw0 hw1 K width hK m fs +
          mixRate hw0 hw1 width ^ n * (probeCap fs + probeCap fs) :=
  sourceProbeMassRatio_commonTail hw0 hw1 K width hK n m n fs hnm (Nat.le_refl n)

end YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBracketNesting

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBracketNesting.refresh_nested
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBracketNesting.iterateBracket_successor_nested
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBracketNesting.iterateBracket_nested
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBracketNesting.sourceProbeBracket_nested
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBracketNesting.sourceProbeMassRatio_later_bounds
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBracketNesting.sourceProbeMassRatio_commonTail
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBracketNesting.sourceProbeMassRatio_twoTime
