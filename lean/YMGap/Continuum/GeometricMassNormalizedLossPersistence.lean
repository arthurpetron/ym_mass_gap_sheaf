/-
M3h -- constructive geometric normalized-loss budget.

The direction-neutral persistence theorem consumes a `SummableDistortion` for
the dimensionful one-step rate loss.  This file constructs that entire budget
from the sharper local estimate

  rateLoss k <= C * (1/2)^k.

The cap is the explicit geometric tail `2*C`; the modulus rescales an arbitrary
positive tolerance by `1 + 2*C` and then uses the repository's constructive
`HalfPow.pow_half_le` witness.  Thus an analytic proof of the pointwise
geometric estimate no longer also has to manufacture summability data.

This is reduction machinery only.  It does not prove that an actual BF4/RG
trajectory has geometric normalized loss, nor does it construct a physical
separator or a continuum Yang--Mills measure.
-/

import YMGap.Continuum.KPLimit
import YMGap.Continuum.MassNormalizedLossPersistence
import YMGap.RG.DominatedSummableDistortion

namespace YMGap.Continuum.GeometricMassNormalizedLossPersistence

open YMGap.Constructive
open YMGap.Constructive.HalfPow
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.MassNormalizedLossPersistence
open YMGap.RG.DominatedSummableDistortion
open YMGap.RG.StableDynamics

/-! ## A fully constructive budget for the geometric majorant -/

/-- The positive rescaling denominator `1 + 2*C`. -/
def toleranceScale (C : Q') : Q' :=
  1 + Q'.ofNat 2 * C

theorem toleranceScale_pos (C : Q') (hC : (0 : Q') <= C) :
    (0 : Q') < toleranceScale C := by
  unfold toleranceScale
  exact Q'.pos_add_nonneg (by decide)
    (Q'.mul_nonneg _ _ (by decide) hC)

/-- A positive target small enough that multiplying it by `2*C` stays below
the original target.  The definition is data even before positivity of
`epsilon` is supplied to the tail theorem. -/
def rescaledTolerance (C : Q') (hC : (0 : Q') <= C)
    (epsilon : Q') : Q' :=
  Q'.divPos epsilon (toleranceScale C) (toleranceScale_pos C hC)

theorem rescaledTolerance_pos (C : Q') (hC : (0 : Q') <= C)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon) :
    (0 : Q') < rescaledTolerance C hC epsilon :=
  Q'.divPos_pos epsilon (toleranceScale C)
    (toleranceScale_pos C hC) hepsilon

/-- The rescaling pays the complete geometric coefficient:
`(2*C) * (epsilon/(1+2*C)) <= epsilon`. -/
theorem coefficient_mul_rescaledTolerance_le
    (C : Q') (hC : (0 : Q') <= C)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon) :
    (Q'.ofNat 2 * C) * rescaledTolerance C hC epsilon <= epsilon := by
  let B : Q' := Q'.ofNat 2 * C
  have hB : (0 : Q') <= B := Q'.mul_nonneg _ _ (by decide) hC
  have hscale : (0 : Q') < 1 + B := Q'.pos_add_nonneg (by decide) hB
  have hdelta : (0 : Q') <=
      Q'.divPos epsilon (1 + B) hscale :=
    Q'.le_of_lt (Q'.divPos_pos epsilon (1 + B) hscale hepsilon)
  have hBle : B <= 1 + B := by
    have h := Q'.add_le_add_right 0 1 B (by decide)
    rw [Q'.zero_add'] at h
    exact h
  have hmul : B * Q'.divPos epsilon (1 + B) hscale <=
      (1 + B) * Q'.divPos epsilon (1 + B) hscale :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hBle hdelta
  have hcollapse :
      ((1 + B) * Q'.divPos epsilon (1 + B) hscale).eqv epsilon := by
    refine Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) ?_
    exact Q'.divPos_mul_eqv epsilon (1 + B) hscale
  have hresult : B * Q'.divPos epsilon (1 + B) hscale <= epsilon :=
    Q'.le_trans' _ _ _ hmul (Q'.le_of_eqv hcollapse)
  exact hresult

/-- The geometric majorant `C*(1/2)^k` carries a complete constructive
summability certificate.  Its cap is `geoTail C 0 = 2*C`, and its modulus is
the denominator of the explicitly rescaled tolerance. -/
def geometricBudget (C : Q') (hC : (0 : Q') <= C) :
    SummableDistortion (geoIncr C) where
  cap := geoTail C 0
  capNonnegative := geoTail_nonneg C hC 0
  termNonnegative := geoIncr_nonneg C hC
  partialSumBound := by
    intro length
    simpa only [Nat.zero_add] using geoTail_series_le C hC 0 length
  modulus := fun epsilon => (rescaledTolerance C hC epsilon).den
  tailBound := by
    intro epsilon hepsilon start hstart length
    have hdelta : (0 : Q') < rescaledTolerance C hC epsilon :=
      rescaledTolerance_pos C hC epsilon hepsilon
    have hpow : half ^ start <= rescaledTolerance C hC epsilon :=
      Q'.le_trans' _ _ _
        (half_pow_antitone
          (rescaledTolerance C hC epsilon).den start hstart)
        (pow_half_le (rescaledTolerance C hC epsilon) hdelta)
    have hcoeff : (0 : Q') <= Q'.ofNat 2 * C :=
      Q'.mul_nonneg _ _ (by decide) hC
    have htail : geoTail C start <= epsilon := by
      unfold geoTail
      exact Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_left _ _ _ hpow hcoeff)
        (coefficient_mul_rescaledTolerance_le C hC epsilon hepsilon)
    exact Q'.le_trans' _ _ _
      (geoTail_series_le C hC start length) htail

@[simp] theorem geometricBudget_cap (C : Q') (hC : (0 : Q') <= C) :
    (geometricBudget C hC).cap = geoTail C 0 := rfl

/-! ## Pointwise geometric control of normalized physical loss -/

/-- The remaining local analytic estimate: normalized one-step physical loss
is bounded by a geometric stream.  This is Type-valued proof data and does not
assert that any particular Yang--Mills trajectory supplies it. -/
structure GeometricRateLossControl (flow : MassNormalizedLossFlow) : Type where
  coefficient : Q'
  coefficient_nonnegative : (0 : Q') <= coefficient
  rateLoss_le : forall k : Nat,
    flow.rateLoss k <= geoIncr coefficient k

namespace GeometricRateLossControl

/-- Pointwise domination transfers the explicit geometric cap and modulus to
the actual normalized-loss stream. -/
def lossBudget {flow : MassNormalizedLossFlow}
    (control : GeometricRateLossControl flow) :
    SummableDistortion flow.rateLoss :=
  ofPointwiseDomination
    flow.rateLoss (geoIncr control.coefficient)
    flow.rateLoss_nonnegative control.rateLoss_le
    (geometricBudget control.coefficient control.coefficient_nonnegative)

@[simp] theorem lossBudget_cap {flow : MassNormalizedLossFlow}
    (control : GeometricRateLossControl flow) :
    control.lossBudget.cap = geoTail control.coefficient 0 := rfl

/-- Once the anchor mass exceeds the explicit total geometric loss, the
general direction-neutral persistence theorem is inhabited constructively. -/
def persistence {flow : MassNormalizedLossFlow}
    (control : GeometricRateLossControl flow)
    (anchorDominates : geoTail control.coefficient 0 < flow.mass 0) :
    MassNormalizedLossPersistence flow where
  lossBudget := control.lossBudget
  anchorDominates := anchorDominates

@[simp] theorem persistence_floorWitness {flow : MassNormalizedLossFlow}
    (control : GeometricRateLossControl flow)
    (anchorDominates : geoTail control.coefficient 0 < flow.mass 0) :
    (control.persistence anchorDominates).floorWitness =
      flow.mass 0 + -geoTail control.coefficient 0 := rfl

theorem persistent_floor_pos {flow : MassNormalizedLossFlow}
    (control : GeometricRateLossControl flow)
    (anchorDominates : geoTail control.coefficient 0 < flow.mass 0) :
    (0 : Q') < (control.persistence anchorDominates).floorWitness :=
  (control.persistence anchorDominates).floorWitness_pos

theorem persistent_floor_le_mass {flow : MassNormalizedLossFlow}
    (control : GeometricRateLossControl flow)
    (anchorDominates : geoTail control.coefficient 0 < flow.mass 0)
    (k : Nat) :
    (control.persistence anchorDominates).floorWitness <= flow.mass k :=
  (control.persistence anchorDominates).floorWitness_le_mass k

end GeometricRateLossControl

end YMGap.Continuum.GeometricMassNormalizedLossPersistence

#print axioms YMGap.Continuum.GeometricMassNormalizedLossPersistence.toleranceScale_pos
#print axioms YMGap.Continuum.GeometricMassNormalizedLossPersistence.coefficient_mul_rescaledTolerance_le
#print axioms YMGap.Continuum.GeometricMassNormalizedLossPersistence.geometricBudget
#print axioms YMGap.Continuum.GeometricMassNormalizedLossPersistence.GeometricRateLossControl.lossBudget
#print axioms YMGap.Continuum.GeometricMassNormalizedLossPersistence.GeometricRateLossControl.persistence
#print axioms YMGap.Continuum.GeometricMassNormalizedLossPersistence.GeometricRateLossControl.persistent_floor_pos
#print axioms YMGap.Continuum.GeometricMassNormalizedLossPersistence.GeometricRateLossControl.persistent_floor_le_mass
