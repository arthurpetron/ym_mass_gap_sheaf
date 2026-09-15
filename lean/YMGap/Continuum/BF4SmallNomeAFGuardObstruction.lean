/-
# The original small-nome guard cannot cover the supplied AF chart

The original thermodynamic construction uses heatRemainderBound(w) < 1.
That returned cap is 128*w^3, hence is already at least 2 when w >= 1/4.
For any supplied CubicMarginLaw, the fine margin is g^2 and the matched
one-step blocked margin is at most 2*g^2. At every chart point g <= 1/2,
both nomes therefore violate this guard. The witness min(g1,1/2) is data.

This is an obstruction to REUSING the old perturbative guard, not a lower
bound on the actual heat remainder, not a refutation of the AF law, and
not a refutation of Yang--Mills existence. No AF law is constructed here.
Arbitrary-nome pointwise heat-tail convergence does not make the complete
positive-label remainder small. A same-action scale/volume estimate that
replaces this guard remains open, as do physical scaling and Clay closure.
-/

import YMGap.Continuum.QuaternionHaarCharacterInterval
import YMGap.Continuum.BF4MatchedPhysicalAFBridge
import YMGap.Continuum.FusedAmplitudeDerivation

namespace YMGap.Continuum.BF4SmallNomeAFGuardObstruction

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.HalfPow (half half_nonneg)
open YMGap.Continuum.RGTransport (qpow)
open YMGap.Continuum.QuaternionHaarCharacterInterval
open YMGap.Continuum.FusedAmplitudeDerivation (qpow_mono_base)
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)

def guardThreshold : Q' := Q'.invSucc 3

/-- A lower bound on the RETURNED CAP, not on the actual heat remainder. -/
theorem remainder_cap_ge_two {w : Q'} (hw : guardThreshold ≤ w) :
    (2 : Q') ≤ heatRemainderBound w :=
  Q'.le_trans' _ _ _ (by decide : (2 : Q') ≤ 128 * qpow guardThreshold 3)
    (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ 128
        (qpow_mono_base (by decide : (0 : Q') ≤ guardThreshold) hw 3) (by decide))
      (Q'.ge_of_eqv (heatRemainderBound_eq w)))

theorem guard_fails {w : Q'} (hw : guardThreshold ≤ w) :
    ¬ heatRemainderBound w < 1 := by
  intro h
  exact (by decide : ¬ ((2 : Q') < 1))
    (Q'.lt_of_le_of_lt (remainder_cap_ge_two hw) h)

theorem guard_forces_small_nome {w : Q'} (h : heatRemainderBound w < 1) :
    w < guardThreshold := by
  have hn : ¬ guardThreshold ≤ w := fun hw => guard_fails hw h
  exact Int.not_le.mp hn

theorem nome_lower_of_margin_le (w c : Q') (h : 1 + -w ≤ c) :
    1 + -c ≤ w := by
  have hn := Q'.add_le_add_right _ _ 1 (Q'.neg_le_neg h)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.add_comm_eqv 1 (-c)))
    (Q'.le_trans' _ _ _ hn (Q'.le_of_eqv (poly_identity_of_normal_eq
      (.add (.neg (.add (.const 1) (.neg (.var 0)))) (.const 1))
      (.var 0) (by decide) (fun _ => w))))

theorem square_le_quarter {g : Q'} (hg0 : (0 : Q') ≤ g) (hg : g ≤ half) :
    g * g ≤ half * half :=
  Q'.mul_le_mul_of_nonneg hg hg half_nonneg hg0

/-- This bound uses the actual fine-nome pin of the supplied AF law. -/
theorem fine_nome_ge_threshold (family : MatchedBlockFamily)
    (law : CubicMarginLaw family) (g : Q')
    (hg : (0 : Q') < g) (hgle : g ≤ law.g₁) (hsmall : g ≤ half) :
    guardThreshold ≤ fineWeight family g := by
  have hm : 1 + -(fineWeight family g) ≤ half * half :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (law.current_margin g hg hgle))
      (square_le_quarter (Q'.le_of_lt hg) hsmall)
  exact Q'.le_trans' _ _ _ (by decide : guardThreshold ≤ 1 + -(half * half))
    (nome_lower_of_margin_le _ _ hm)

/-- One existing matched blocking step does not restore the old guard. -/
theorem blocked_nome_ge_threshold (family : MatchedBlockFamily)
    (law : CubicMarginLaw family) (g : Q')
    (hg : (0 : Q') < g) (hgle : g ≤ law.g₁) (hsmall : g ≤ half) :
    guardThreshold ≤ blockedWeight family g := by
  have hm : 1 + -(blockedWeight family g) ≤ 2 * (half * half) :=
    Q'.le_trans' _ _ _ (blockedMargin_le_two_square family law g hg hgle)
      (Q'.mul_le_mul_of_nonneg_left _ _ 2
        (square_le_quarter (Q'.le_of_lt hg) hsmall) (by decide))
  exact Q'.le_trans' _ _ _ (by decide : guardThreshold ≤ 1 + -(2 * (half * half)))
    (nome_lower_of_margin_le _ _ hm)

theorem fine_guard_fails (family : MatchedBlockFamily)
    (law : CubicMarginLaw family) (g : Q')
    (hg : (0 : Q') < g) (hgle : g ≤ law.g₁) (hsmall : g ≤ half) :
    ¬ heatRemainderBound (fineWeight family g) < 1 :=
  guard_fails (fine_nome_ge_threshold family law g hg hgle hsmall)

theorem blocked_guard_fails (family : MatchedBlockFamily)
    (law : CubicMarginLaw family) (g : Q')
    (hg : (0 : Q') < g) (hgle : g ≤ law.g₁) (hsmall : g ≤ half) :
    ¬ heatRemainderBound (blockedWeight family g) < 1 :=
  guard_fails (blocked_nome_ge_threshold family law g hg hgle hsmall)

def chartWitness {family : MatchedBlockFamily} (law : CubicMarginLaw family) : Q' :=
  Q'.min' law.g₁ half

theorem chartWitness_positive {family : MatchedBlockFamily} (law : CubicMarginLaw family) :
    (0 : Q') < chartWitness law := by
  unfold chartWitness Q'.min'
  split
  · exact law.g₁_pos
  · exact (by decide : (0 : Q') < half)

/-- The concrete coupling, its chart guards and both failed-cap certificates
remain available as data; no existential witness is erased. -/
def obstructionWitness (family : MatchedBlockFamily) (law : CubicMarginLaw family) :
    Σ' g : Q', ((0 : Q') < g) ×' (g ≤ law.g₁) ×' (g ≤ half) ×'
      ((2 : Q') ≤ heatRemainderBound (fineWeight family g)) ×'
      ((2 : Q') ≤ heatRemainderBound (blockedWeight family g)) :=
  ⟨chartWitness law, chartWitness_positive law,
    Q'.min_le_left' _ _, Q'.min_le_right' _ _,
    remainder_cap_ge_two (fine_nome_ge_threshold family law _
      (chartWitness_positive law) (Q'.min_le_left' _ _) (Q'.min_le_right' _ _)),
    remainder_cap_ge_two (blocked_nome_ge_threshold family law _
      (chartWitness_positive law) (Q'.min_le_left' _ _) (Q'.min_le_right' _ _))⟩

theorem no_fine_guard_on_chart (family : MatchedBlockFamily) (law : CubicMarginLaw family) :
    ¬ (∀ g : Q', (0 : Q') < g → g ≤ law.g₁ → heatRemainderBound (fineWeight family g) < 1) := by
  intro h
  exact fine_guard_fails family law _ (chartWitness_positive law)
    (Q'.min_le_left' _ _) (Q'.min_le_right' _ _)
    (h _ (chartWitness_positive law) (Q'.min_le_left' _ _))

theorem no_blocked_guard_on_chart (family : MatchedBlockFamily) (law : CubicMarginLaw family) :
    ¬ (∀ g : Q', (0 : Q') < g → g ≤ law.g₁ → heatRemainderBound (blockedWeight family g) < 1) := by
  intro h
  exact blocked_guard_fails family law _ (chartWitness_positive law)
    (Q'.min_le_left' _ _) (Q'.min_le_right' _ _)
    (h _ (chartWitness_positive law) (Q'.min_le_left' _ _))

end YMGap.Continuum.BF4SmallNomeAFGuardObstruction

#print axioms YMGap.Continuum.BF4SmallNomeAFGuardObstruction.guardThreshold
#print axioms YMGap.Continuum.BF4SmallNomeAFGuardObstruction.remainder_cap_ge_two
#print axioms YMGap.Continuum.BF4SmallNomeAFGuardObstruction.guard_fails
#print axioms YMGap.Continuum.BF4SmallNomeAFGuardObstruction.guard_forces_small_nome
#print axioms YMGap.Continuum.BF4SmallNomeAFGuardObstruction.nome_lower_of_margin_le
#print axioms YMGap.Continuum.BF4SmallNomeAFGuardObstruction.square_le_quarter
#print axioms YMGap.Continuum.BF4SmallNomeAFGuardObstruction.fine_nome_ge_threshold
#print axioms YMGap.Continuum.BF4SmallNomeAFGuardObstruction.blocked_nome_ge_threshold
#print axioms YMGap.Continuum.BF4SmallNomeAFGuardObstruction.fine_guard_fails
#print axioms YMGap.Continuum.BF4SmallNomeAFGuardObstruction.blocked_guard_fails
#print axioms YMGap.Continuum.BF4SmallNomeAFGuardObstruction.chartWitness
#print axioms YMGap.Continuum.BF4SmallNomeAFGuardObstruction.chartWitness_positive
#print axioms YMGap.Continuum.BF4SmallNomeAFGuardObstruction.obstructionWitness
#print axioms YMGap.Continuum.BF4SmallNomeAFGuardObstruction.no_fine_guard_on_chart
#print axioms YMGap.Continuum.BF4SmallNomeAFGuardObstruction.no_blocked_guard_on_chart
