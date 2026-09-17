/-
# Time-zero Wilson multiplication balances the SAME intrinsic OS form

The loop character is inserted exactly at the common reflection center.
Reflection fixes this insertion, so coefficient commutation and associativity
move it between the two slots of the original mixed reflected polynomial.
The existing same-action spatial-limit congruence preserves that identity.

The intrinsic result uses one computed common horizon, retaining the original
loop, action, partition and small-nome guards. It is a balance identity for
the existing CReal-valued form; no new Hilbert carrier, canonical observable
representation, strict transfer bound or continuum conclusion is asserted.
-/

import YMGap.Continuum.BF4WilsonTimeZeroIntrinsicMultiplier

namespace YMGap.Continuum.BF4WilsonTimeZeroIntrinsicSymmetry

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe (SourceLoop)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSpatialComparison
  (chartInsertion chartScalar)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSpatialLimit (spatialLimit)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSpatialFunctionalLaws (spatialLimit_congr)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonReflectedCauchySchwarz (form)
open YMGap.Continuum.BF4WilsonTimeZeroIntrinsicMultiplier (multiply chart_multiply)
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential

attribute [local irreducible] chartScalar spatialLimit

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
  {base : Nat} (hb : 0<base)

/-- The fixed-center loop moves between slots inside the actual limiting form. -/
theorem form_timeZero_multiplier_balance (H : Nat) (L : SourceLoop base) (spin : Nat)
    (e f : WindowExpression base) (he : Within H e) (hf : Within H f) :
    Equiv (form hw0 hw1 hsmall hd hs hb H
      (.mul (.loop H L spin) e) f ⟨Nat.le_refl H, he⟩ hf)
      (form hw0 hw1 hsmall hd hs hb H
        e (.mul (.loop H L spin) f) he ⟨Nat.le_refl H, hf⟩) := by
  apply spatialLimit_congr hw0 hw1 hsmall hd hs hb H
    (.mul (mirror H (.mul (.loop H L spin) e)) f)
    (.mul (mirror H e) (.mul (.loop H L spin) f))
    ⟨mirror_within H (.mul (.loop H L spin) e),
      within_mono (by omega : H ≤ 2*H) f hf⟩
    ⟨mirror_within H e,
      within_mono (by omega : H ≤ 2*H) (.mul (.loop H L spin) f) ⟨Nat.le_refl H, hf⟩⟩
  intro r t
  change RatPolyCoeffEqv
    (polyMul (polyMul (chartInsertion r H t (.loop (2*H-H) L spin))
      (chartInsertion r H t (mirror H e))) (chartInsertion r H t f))
    (polyMul (chartInsertion r H t (mirror H e))
      (polyMul (chartInsertion r H t (.loop H L spin)) (chartInsertion r H t f)))
  rw [show 2*H-H=H by omega]
  exact ((RatPolyCoeffEqv.mul_comm (chartInsertion r H t (.loop H L spin))
    (chartInsertion r H t (mirror H e))).mul_right (chartInsertion r H t f)).trans
      (RatPolyCoeffEqv.mul_assoc (chartInsertion r H t (mirror H e))
        (chartInsertion r H t (.loop H L spin)) (chartInsertion r H t f))

attribute [local irreducible] form

/-- Balance on the actual intrinsic carrier, using one common reflection center. -/
theorem intrinsicForm_multiplier_balance (L : SourceLoop base) (spin : Nat)
    (x y : IntrinsicExpression base) :
    Equiv (intrinsicForm hw0 hw1 hsmall hd hs hb (multiply L spin x) y)
      (intrinsicForm hw0 hw1 hsmall hd hs hb x (multiply L spin y)) := by
  let H := max x.radius y.radius
  have hx : x.radius ≤ H := Nat.le_max_left _ _
  have hy : y.radius ≤ H := Nat.le_max_right _ _
  have hleft := intrinsicForm_chart hw0 hw1 hsmall hd hs hb
    (multiply L spin x) y H hx hy
  have hright := intrinsicForm_chart hw0 hw1 hsmall hd hs hb
    x (multiply L spin y) H hx hy
  simp only [chart_multiply H L spin x hx] at hleft
  simp only [chart_multiply H L spin y hy] at hright
  exact hleft.trans ((form_timeZero_multiplier_balance hw0 hw1 hsmall hd hs hb H L spin
    (chart H x) (chart H y) (chart_within H x hx) (chart_within H y hy)).trans hright.symm)

#print axioms form_timeZero_multiplier_balance
#print axioms intrinsicForm_multiplier_balance

end YMGap.Continuum.BF4WilsonTimeZeroIntrinsicSymmetry
