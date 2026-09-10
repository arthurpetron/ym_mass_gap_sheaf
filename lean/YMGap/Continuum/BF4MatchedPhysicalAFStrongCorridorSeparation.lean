/-
# Separate the matched AF chart from the proved strong-coupling corridor

The connected terminal-history compiler is valid on the explicit corridor
`rate <= anchorCoupling = 1/400`.  The exact BF4 matched trajectory instead
uses the heat nome `blockedWeight family g`, whose margin is quadratic in the
weak-coupling coordinate `g`.

This module records the resulting causal separation.  The existing cubic
margin law proves, on the explicit subchart `g <= 1/2`, that

  blockedWeight family g >= 1/2 > 1/400.

Consequently no common rate can both dominate the physical matched nome and
lie in the proved strong-coupling corridor.  The theorem is deliberately
stated both for the matched family and for a literal `SlabScalePair` whose
coarse coupling is identified with that matched weight.  This rules out a
false composition of the strong-coupling posterior carrier with the UV BF4
trajectory; it does not weaken either result.

The remaining AF route must therefore control the centered coarse-versus-
blocked change of measure (or construct a genuine weak-to-strong RG
intertwiner), with its dependence on `g` and physical spacing explicit.

Constructive contract: rational order algebra only; no `Classical`, choice,
`native_decide`, proof hole, noncomputable declaration, trusted external
computation, enlarged heartbeat budget, or new axiom.
-/

import YMGap.Continuum.BF4MatchedPhysicalAFBridge
import YMGap.Continuum.PhysicalSeparatorLinearTail
import YMGap.Continuum.Z4StrongCouplingParametricAnchor
import YMGap.Continuum.CompactDualSlabPhysicalData

namespace YMGap.Continuum.BF4MatchedPhysicalAFStrongCorridorSeparation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BareAFDiagnostic
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.PhysicalSeparatorLinearTail
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

/-! ## 1. The matched nome is already outside the anchor corridor -/

/-- On the explicit small-`g` half-chart, the exact matched BF4 heat nome is
at least `1/2`.  This is the direct order-theoretic content of the existing
upper margin estimate `1 - blockedWeight <= 2*g^2`. -/
theorem half_le_blockedWeight_of_le_half
    (family : MatchedBlockFamily)
    (law : CubicMarginLaw family)
    (g : Q') (hg : (0 : Q') < g) (hgle : g <= law.g₁)
    (hgHalf : g <= half) :
    half <= blockedWeight family g := by
  have hsquare : g * g <= half * half :=
    Q'.mul_le_mul_of_nonneg hgHalf hgHalf
      (by decide) (Q'.le_of_lt hg)
  have htwiceSquare : Q'.ofNat 2 * (g * g) <= half := by
    exact Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 2)
        hsquare (by decide))
      (Q'.le_of_eqv (by decide))
  have hmargin : blockedMargin family g <= half :=
    Q'.le_trans' _ _ _
      (blockedMargin_le_two_square family law g hg hgle)
      htwiceSquare
  apply LinearMarginTail.half_le_of_one_sub_le_half
  simpa only [blockedMargin, Q'.sub] using hmargin

/-- The exact matched BF4 heat nome cannot lie below the strong-coupling
anchor throughout the same explicit half-chart. -/
theorem blockedWeight_not_le_anchorCoupling_of_le_half
    (family : MatchedBlockFamily)
    (law : CubicMarginLaw family)
    (g : Q') (hg : (0 : Q') < g) (hgle : g <= law.g₁)
    (hgHalf : g <= half) :
    ¬ blockedWeight family g <= anchorCoupling := by
  intro hweightAnchor
  have hhalfWeight :=
    half_le_blockedWeight_of_le_half family law g hg hgle hgHalf
  have hweightHalf : blockedWeight family g < half :=
    Q'.lt_of_le_of_lt hweightAnchor (by decide)
  have hbad : half < half :=
    Q'.lt_of_le_of_lt hhalfWeight hweightHalf
  exact Int.lt_irrefl _ hbad

/-! ## 2. Direct incompatibility with every corridor-dominating rate -/

/-- No rational rate can simultaneously dominate the matched physical nome
and satisfy the strong-coupling anchor premise. -/
theorem not_rate_dominates_blockedWeight_and_le_anchor
    (family : MatchedBlockFamily)
    (law : CubicMarginLaw family)
    (g : Q') (hg : (0 : Q') < g) (hgle : g <= law.g₁)
    (hgHalf : g <= half)
    (rate : Q') :
    ¬ (blockedWeight family g <= rate ∧ rate <= anchorCoupling) := by
  intro hcorridor
  have hweightAnchor : blockedWeight family g <= anchorCoupling :=
    Q'.le_trans' _ _ _ hcorridor.1 hcorridor.2
  exact
    (blockedWeight_not_le_anchorCoupling_of_le_half
      family law g hg hgle hgHalf) hweightAnchor

/-- Literal `SlabScalePair` specialization: once its coarse coupling is the
matched BF4 nome, the coarse-rate and anchor-rate premises used by the
terminal-history corridor cannot coexist. -/
theorem slabScalePair_not_coarseRate_and_anchorRate
    (S : SlabScalePair)
    (family : MatchedBlockFamily)
    (law : CubicMarginLaw family)
    (g : Q') (hg : (0 : Q') < g) (hgle : g <= law.g₁)
    (hgHalf : g <= half)
    (hcoarse : S.coarse.coupling = blockedWeight family g)
    (rate : Q') :
    ¬ (S.coarse.coupling <= rate ∧ rate <= anchorCoupling) := by
  intro hcorridor
  apply not_rate_dominates_blockedWeight_and_le_anchor
    family law g hg hgle hgHalf rate
  exact ⟨hcoarse ▸ hcorridor.1, hcorridor.2⟩

/-! ## 3. Axiom audit -/

#print axioms half_le_blockedWeight_of_le_half
#print axioms blockedWeight_not_le_anchorCoupling_of_le_half
#print axioms not_rate_dominates_blockedWeight_and_le_anchor
#print axioms slabScalePair_not_coarseRate_and_anchorRate

end YMGap.Continuum.BF4MatchedPhysicalAFStrongCorridorSeparation
