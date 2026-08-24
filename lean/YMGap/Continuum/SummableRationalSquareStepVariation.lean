/-
# Bounded rational variation survives squaring

A normalized observable often carries a rational scale `r_j`, while its norm
debt is `r_j * r_j`.  Summability of the scale variation alone does not control
the square unless the scale is uniformly bounded.  This file states that
missing condition explicitly and compiles it:

* a positive uniform ceiling `K` for a nonnegative rational stream;
* a summable two-sided step variation `v_j` for that stream;

give a summable two-sided step variation `(K + K) * v_j` for its square.
The proof also constructs the antitone tail modulus after multiplication by a
positive rational constant.

No physical bound or variation estimate is inhabited here.  No
`Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Constructive.FinSumAlg
import YMGap.Constructive.RegularCRealArith
import YMGap.Continuum.SummableRationalStepVariation

namespace YMGap.Continuum.SummableRationalSquareStepVariation

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.SummableCRealStepVariation
open YMGap.Continuum.SummableRationalStepVariation

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Positive constant scaling of a summable tail -/

private theorem divPos_le_divPos_of_le
    {left right denominator : Q'}
    (denominator_pos : (0 : Q') < denominator)
    (bound : left <= right) :
    Q'.divPos left denominator denominator_pos <=
      Q'.divPos right denominator denominator_pos := by
  show left * Q'.recipPos denominator denominator_pos <=
    right * Q'.recipPos denominator denominator_pos
  exact Q'.mul_le_mul_of_nonneg_right left right
    (Q'.recipPos denominator denominator_pos) bound
    (Q'.le_of_lt (Q'.recipPos_pos denominator denominator_pos))

/-- Multiplication by one positive rational constant preserves an explicit
antitone summable-tail control. -/
def scaledAntitoneTailControl
    {variation : Nat -> Q'}
    (data : AntitoneTailControl variation)
    (multiplier : Q') (multiplier_pos : (0 : Q') < multiplier) :
    AntitoneTailControl (fun scale => multiplier * variation scale) where
  tailRate := fun epsilon =>
    data.tailRate (Q'.divPos epsilon multiplier multiplier_pos)
  tailRate_antitone := by
    intro epsilon delta delta_pos delta_le_epsilon
    exact data.tailRate_antitone
      (Q'.divPos epsilon multiplier multiplier_pos)
      (Q'.divPos delta multiplier multiplier_pos)
      (Q'.divPos_pos delta multiplier multiplier_pos delta_pos)
      (divPos_le_divPos_of_le multiplier_pos delta_le_epsilon)
  tailBound := by
    intro epsilon epsilon_pos start start_bound length
    have sourceBound := data.tailBound
      (Q'.divPos epsilon multiplier multiplier_pos)
      (Q'.divPos_pos epsilon multiplier multiplier_pos epsilon_pos)
      start start_bound length
    have scaledBound :
        multiplier *
            finSum (fun offset => variation (start + offset)) length <=
          multiplier * Q'.divPos epsilon multiplier multiplier_pos :=
      Q'.mul_le_mul_of_nonneg_left _ _ multiplier sourceBound
        (Q'.le_of_lt multiplier_pos)
    have sumEqv :
        multiplier *
            finSum (fun offset => variation (start + offset)) length ≈
          finSum
            (fun offset => multiplier * variation (start + offset)) length :=
      RationalTail.const_mul_finSum
        (fun offset => variation (start + offset)) multiplier length
    have collapse :
        multiplier * Q'.divPos epsilon multiplier multiplier_pos ≈ epsilon :=
      Q'.eqv_trans _ _ _
        (Q'.mul_comm_eqv multiplier
          (Q'.divPos epsilon multiplier multiplier_pos))
        (Q'.divPos_mul_eqv epsilon multiplier multiplier_pos)
    exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv sumEqv)
      (Q'.le_trans' _ _ _ scaledBound (Q'.le_of_eqv collapse))

/-! ## 2. One bounded square step -/

/-- If `x` and `y` are nonnegative and bounded by `K`, and `y <= x + v`,
then `y^2 <= x^2 + 2*K*v`.  The rational expression uses `(K + K) * v`
to avoid importing any numeral normalization. -/
theorem square_step_le
    (x y variation ceiling : Q')
    (x_nonnegative : (0 : Q') <= x)
    (y_nonnegative : (0 : Q') <= y)
    (variation_nonnegative : (0 : Q') <= variation)
    (x_le_ceiling : x <= ceiling)
    (y_le_ceiling : y <= ceiling)
    (step : y <= x + variation) :
    y * y <= x * x + (ceiling + ceiling) * variation := by
  have firstProduct : y * y <= (x + variation) * y :=
    Q'.mul_le_mul_of_nonneg_right y (x + variation) y step y_nonnegative
  have firstExpanded :
      y * y <= x * y + variation * y :=
    Q'.le_trans' _ _ _ firstProduct
      (Q'.le_of_eqv (Q'.add_mul_eqv x variation y))
  have mixedProduct : x * y <= x * (x + variation) :=
    Q'.mul_le_mul_of_nonneg_left y (x + variation) x step x_nonnegative
  have mixedExpanded : x * y <= x * x + x * variation :=
    Q'.le_trans' _ _ _ mixedProduct
      (Q'.le_of_eqv (Q'.mul_add_eqv x x variation))
  have replaceMixed :
      x * y + variation * y <=
        (x * x + x * variation) + variation * y :=
    Q'.add_le_add_right _ _ (variation * y) mixedExpanded
  have xVariation : x * variation <= ceiling * variation :=
    Q'.mul_le_mul_of_nonneg_right x ceiling variation
      x_le_ceiling variation_nonnegative
  have yVariation : variation * y <= variation * ceiling :=
    Q'.mul_le_mul_of_nonneg_left y ceiling variation
      y_le_ceiling variation_nonnegative
  have replaceXVariation :
      (x * x + x * variation) + variation * y <=
        (x * x + ceiling * variation) + variation * y :=
    Q'.add_le_add_right _ _ (variation * y)
      (Q'.add_le_add_left (x * x) (x * variation)
        (ceiling * variation) xVariation)
  have replaceYVariation :
      (x * x + ceiling * variation) + variation * y <=
        (x * x + ceiling * variation) + variation * ceiling :=
    Q'.add_le_add_left (x * x + ceiling * variation)
      (variation * y) (variation * ceiling) yVariation
  have collect :
      (x * x + ceiling * variation) + variation * ceiling ≈
        x * x + (ceiling + ceiling) * variation := by
    refine Q'.eqv_trans _
      ((x * x + ceiling * variation) + ceiling * variation) _ ?_ ?_
    · exact Q'.add_eqv_congr_left (x * x + ceiling * variation)
        (variation * ceiling) (ceiling * variation)
        (Q'.mul_comm_eqv variation ceiling)
    · refine Q'.eqv_trans _ _ _
        (Q'.add_assoc_eqv (x * x) (ceiling * variation)
          (ceiling * variation)) ?_
      exact Q'.add_eqv_congr_left (x * x)
        (ceiling * variation + ceiling * variation)
        ((ceiling + ceiling) * variation)
        (Q'.eqv_symm (Q'.add_mul_eqv ceiling ceiling variation))
  exact Q'.le_trans' _ _ _ firstExpanded
    (Q'.le_trans' _ _ _ replaceMixed
      (Q'.le_trans' _ _ _ replaceXVariation
        (Q'.le_trans' _ _ _ replaceYVariation (Q'.le_of_eqv collect))))

/-! ## 3. Compile a bounded stream's square variation -/

/-- A positive uniform ceiling turns summable step variation of a nonnegative
rational stream into summable step variation of its square. -/
def SummableRationalStepVariation.square
    {stream : Nat -> Q'}
    (data : SummableRationalStepVariation stream)
    (ceiling : Q') (ceiling_pos : (0 : Q') < ceiling)
    (stream_nonnegative : forall scale, (0 : Q') <= stream scale)
    (stream_le_ceiling : forall scale, stream scale <= ceiling) :
    SummableRationalStepVariation
      (fun scale => stream scale * stream scale) where
  variation := fun scale =>
    (ceiling + ceiling) * data.variation scale
  variation_nonnegative := by
    intro scale
    exact Q'.mul_nonneg _ _
      (Q'.zero_le_add ceiling ceiling
        (Q'.le_of_lt ceiling_pos) (Q'.le_of_lt ceiling_pos))
      (data.variation_nonnegative scale)
  tailControl := scaledAntitoneTailControl data.tailControl
    (ceiling + ceiling)
    (Q'.add_pos ceiling_pos ceiling_pos)
  stepBound := by
    intro scale
    exact
      ⟨square_step_le
          (stream scale) (stream (scale + 1)) (data.variation scale) ceiling
          (stream_nonnegative scale) (stream_nonnegative (scale + 1))
          (data.variation_nonnegative scale)
          (stream_le_ceiling scale) (stream_le_ceiling (scale + 1))
          (data.stepBound scale).1,
        square_step_le
          (stream (scale + 1)) (stream scale) (data.variation scale) ceiling
          (stream_nonnegative (scale + 1)) (stream_nonnegative scale)
          (data.variation_nonnegative scale)
          (stream_le_ceiling (scale + 1)) (stream_le_ceiling scale)
          (data.stepBound scale).2⟩

end YMGap.Continuum.SummableRationalSquareStepVariation

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.SummableRationalSquareStepVariation.scaledAntitoneTailControl
#print axioms
  YMGap.Continuum.SummableRationalSquareStepVariation.square_step_le
#print axioms
  YMGap.Continuum.SummableRationalSquareStepVariation.SummableRationalStepVariation.square
