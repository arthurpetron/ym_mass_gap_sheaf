/-
Exact closure of the first scale beyond the banked harmonic prefix.

The recurrence file supplies a cancellation-preserving boundary form and
dyadic-tail-certified rational intervals for the three normalizers and
Dirichlet deficits at scales 37, 38, and 39.  Here those intervals are
composed with their correct signs.  The resulting disjoint rational
enclosures prove that the normalized full slack is nondecreasing from
37 to 38, hence discharge the balanced transition premise and the full
moving-determinant inequality at k=38.
-/

import YMGap.Continuum.HarmonicMovingDeterminantRecurrence

namespace YMGap.Continuum.HarmonicMovingDeterminantK38

set_option maxHeartbeats 1200000
set_option maxRecDepth 20000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BakryEmery
open YMGap.Continuum.HarmonicFusedSchurObstruction
open YMGap.Continuum.HarmonicMovingDeterminantDirect
open YMGap.Continuum.HarmonicMovingDeterminantRecurrence
open YMGap.Continuum.HarmonicWeightDriftFence

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Closed rational interval endpoints -/

private def d37Lo : Q' := Q'.mkPos 394172 10000 (by decide)
private def d37Hi : Q' := Q'.mkPos 394173 10000 (by decide)
private def d38Lo : Q' := Q'.mkPos 409092 10000 (by decide)
private def d38Hi : Q' := Q'.mkPos 409093 10000 (by decide)
private def d39Hi : Q' := Q'.mkPos 424198 10000 (by decide)

private def e37Lo : Q' := Q'.mkPos 151929 100000 (by decide)
private def e38Lo : Q' := Q'.mkPos 153729 100000 (by decide)
private def e39Lo : Q' := Q'.mkPos 155508 100000 (by decide)
private def e38Hi : Q' :=
  Q'.mkPos 37579 1000000 (by decide) * d38Hi

private def c37 : Q' := Q'.mkPos 497 1600 (by decide)
private def c38 : Q' := Q'.mkPos 13104 42025 (by decide)

/-- Upper enclosure for one copy of the scale-37 boundary core. -/
def slack37UpperCore : Q' :=
  (shellDropFraction * e38Hi) * d37Hi - (c37 * e37Lo) * d38Lo

/-- Lower enclosure for one copy of the scale-38 boundary core. -/
def slack38LowerCore : Q' :=
  (shellDropFraction * e39Lo) * d38Lo - (c38 * e38Hi) * d39Hi

def slack37UpperEnclosure : Q' := slack37UpperCore + slack37UpperCore
def slack38LowerEnclosure : Q' := slack38LowerCore + slack38LowerCore

/-! ## 2. Signed interval composition -/

theorem boundarySlackForm37_le_upperEnclosure :
    boundarySlackForm37 ≤ slack37UpperEnclosure := by
  have hE38 : harmonicD 38 - harmonicA 38 ≤ e38Hi := by
    unfold e38Hi d38Hi
    exact harmonicDeficit_upper_k38
  have hD37 : harmonicD 37 ≤ d37Hi := by
    unfold d37Hi
    exact harmonicD_upper_k37
  have hpositive₁ :
      shellDropFraction * (harmonicD 38 - harmonicA 38) ≤
        shellDropFraction * e38Hi :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hE38 (by decide)
  have hpositive :
      (shellDropFraction * (harmonicD 38 - harmonicA 38)) * harmonicD 37 ≤
        (shellDropFraction * e38Hi) * d37Hi := by
    exact Q'.mul_le_mul_of_nonneg hpositive₁ hD37
      (Q'.mul_nonneg _ _ (by decide) (by unfold e38Hi d38Hi; decide))
      (Q'.le_of_lt (harmonicD_pos 37))
  have hE37 : e37Lo ≤ harmonicD 37 - harmonicA 37 := by
    unfold e37Lo
    exact harmonicDeficit_lower_k37
  have hD38 : d38Lo ≤ harmonicD 38 := by
    unfold d38Lo
    exact harmonicD_lower_k38
  have hdemand₁ : c37 * e37Lo ≤ c37 * (harmonicD 37 - harmonicA 37) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hE37 (by unfold c37; decide)
  have hdemand : (c37 * e37Lo) * d38Lo ≤
      (c37 * (harmonicD 37 - harmonicA 37)) * harmonicD 38 := by
    exact Q'.mul_le_mul_of_nonneg hdemand₁ hD38
      (Q'.mul_nonneg _ _ (by unfold c37; decide)
        (Q'.le_trans' _ _ _ (by unfold e37Lo; decide) hE37))
      (by unfold d38Lo; decide)
  have hcore :
      (shellDropFraction * (harmonicD 38 - harmonicA 38)) * harmonicD 37 -
          (c37 * (harmonicD 37 - harmonicA 37)) * harmonicD 38 ≤
        slack37UpperCore := by
    unfold slack37UpperCore
    exact Q'.add_le_add hpositive (Q'.neg_le_neg hdemand)
  unfold boundarySlackForm37 slack37UpperEnclosure
  dsimp only
  exact Q'.add_le_add hcore hcore

theorem lowerEnclosure_le_boundarySlackForm38 :
    slack38LowerEnclosure ≤ boundarySlackForm38 := by
  have hE39 : e39Lo ≤ harmonicD 39 - harmonicA 39 := by
    unfold e39Lo
    exact harmonicDeficit_lower_k39
  have hD38 : d38Lo ≤ harmonicD 38 := by
    unfold d38Lo
    exact harmonicD_lower_k38
  have hpositive₁ : shellDropFraction * e39Lo ≤
      shellDropFraction * (harmonicD 39 - harmonicA 39) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hE39 (by decide)
  have hpositive : (shellDropFraction * e39Lo) * d38Lo ≤
      (shellDropFraction * (harmonicD 39 - harmonicA 39)) * harmonicD 38 := by
    exact Q'.mul_le_mul_of_nonneg hpositive₁ hD38
      (Q'.mul_nonneg _ _ (by decide)
        (Q'.le_trans' _ _ _ (by unfold e39Lo; decide) hE39))
      (by unfold d38Lo; decide)
  have hE38 : harmonicD 38 - harmonicA 38 ≤ e38Hi := by
    unfold e38Hi d38Hi
    exact harmonicDeficit_upper_k38
  have hD39 : harmonicD 39 ≤ d39Hi := by
    unfold d39Hi
    exact harmonicD_upper_k39
  have hdemand₁ : c38 * (harmonicD 38 - harmonicA 38) ≤ c38 * e38Hi :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hE38 (by unfold c38; decide)
  have hdemand :
      (c38 * (harmonicD 38 - harmonicA 38)) * harmonicD 39 ≤
        (c38 * e38Hi) * d39Hi := by
    exact Q'.mul_le_mul_of_nonneg hdemand₁ hD39
      (Q'.mul_nonneg _ _ (by unfold c38; decide)
        (by unfold e38Hi d38Hi; decide))
      (Q'.le_of_lt (harmonicD_pos 39))
  have hcore : slack38LowerCore ≤
      (shellDropFraction * (harmonicD 39 - harmonicA 39)) * harmonicD 38 -
        (c38 * (harmonicD 38 - harmonicA 38)) * harmonicD 39 := by
    unfold slack38LowerCore
    exact Q'.add_le_add hpositive (Q'.neg_le_neg hdemand)
  unfold boundarySlackForm38 slack38LowerEnclosure
  dsimp only
  exact Q'.add_le_add hcore hcore

/-- The two exact rational enclosures are separated by a strict margin. -/
theorem boundaryEnclosures_strict :
    slack37UpperEnclosure < slack38LowerEnclosure := by
  unfold slack37UpperEnclosure slack38LowerEnclosure
    slack37UpperCore slack38LowerCore e38Hi d37Hi d38Lo d38Hi
    d39Hi e37Lo e39Lo c37 c38 shellDropFraction
  decide

/-! ## 3. The first tail scale -/

theorem boundarySlackForm37_le_boundarySlackForm38 :
    boundarySlackForm37 ≤ boundarySlackForm38 := by
  exact Q'.le_trans' _ _ _ boundarySlackForm37_le_upperEnclosure
    (Q'.le_trans' _ _ _ (Q'.le_of_lt boundaryEnclosures_strict)
      lowerEnclosure_le_boundarySlackForm38)

theorem normalizedGlobalSlack_37_le_38 :
    normalizedGlobalSlack 37 ≤ normalizedGlobalSlack 38 := by
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv normalizedGlobalSlack_37_eq_boundaryForm)
    (Q'.le_trans' _ _ _ boundarySlackForm37_le_boundarySlackForm38
      (Q'.ge_of_eqv normalizedGlobalSlack_38_eq_boundaryForm))

theorem normalizedBalance_k37 :
    normalizedTotalDemand 38 + normalizedPayment 37 ≤
      normalizedTotalDemand 37 + normalizedPayment 38 := by
  exact (normalizedBalance_iff_slack_mono 37).2 normalizedGlobalSlack_37_le_38

theorem normalizedGlobalSlack_nonneg_k38 :
    (0 : Q') ≤ normalizedGlobalSlack 38 :=
  Q'.le_trans' _ _ _ normalizedGlobalSlack_nonneg_k37
    normalizedGlobalSlack_37_le_38

theorem fullDeterminant_k38 :
    (shellDropFraction * harmonicMassCross 38) * harmonicSpacing 38 ≤
      movingSpacingPayment 38 :=
  fullDeterminant_of_normalizedGlobalSlack_nonneg
    38 normalizedGlobalSlack_nonneg_k38

theorem harmonicMass_shell_spacing_k38 :
    harmonicMass 38 * harmonicSpacing 39 ≤
      harmonicShell 38 * harmonicSpacing 38 :=
  harmonicMass_shell_spacing_of_fullDeterminant 38 fullDeterminant_k38

#print axioms slack37UpperCore
#print axioms slack38LowerCore
#print axioms slack37UpperEnclosure
#print axioms slack38LowerEnclosure
#print axioms boundarySlackForm37_le_upperEnclosure
#print axioms lowerEnclosure_le_boundarySlackForm38
#print axioms boundaryEnclosures_strict
#print axioms boundarySlackForm37_le_boundarySlackForm38
#print axioms normalizedGlobalSlack_37_le_38
#print axioms normalizedBalance_k37
#print axioms normalizedGlobalSlack_nonneg_k38
#print axioms fullDeterminant_k38
#print axioms harmonicMass_shell_spacing_k38

end YMGap.Continuum.HarmonicMovingDeterminantK38
