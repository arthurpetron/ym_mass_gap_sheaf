/-
M2q -- reduce the exact-log tail inputs to a linear physical-margin estimate
and an explicit spacing-to-zero modulus.

The exact logarithmic certificate needs two eventual facts: `sep_j >= 1/2`
and a bounded margin rate `(1-sep_j)/a_j`.  A Gibbs or transfer argument is
more likely to produce the cross-multiplied dimensional estimate

    1 - sep_j <= M * a_j.

If `a_j -> 0` with a Type-level modulus, this one estimate supplies both
requirements.  The rate ceiling follows by positive division, while the
half-window follows once `M*a_j <= 1/2`.  This module performs that reduction
constructively and computes the tail start.
-/

import YMGap.Continuum.PhysicalSeparatorFullLogHalfWindow

namespace YMGap.Continuum.PhysicalSeparatorLinearTail

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.PhysicalSeparator
open YMGap.Continuum.PhysicalSeparatorLogRate
open YMGap.Continuum.PhysicalSeparatorFullLogHalfWindow

/-! ## 1. Analytic input surfaces -/

/-- An explicit modulus witnessing that the positive physical spacing tends to
zero.  The modulus is data, not a `Prop`-level existential. -/
structure SpacingToZero (A : PhysicalSpacing) : Type where
  modulus : Q' -> Nat
  spacing_le : forall epsilon : Q', (0 : Q') < epsilon ->
    forall j : Nat, modulus epsilon <= j -> A.spacing j <= epsilon

/-- The natural cross-multiplied upper estimate on the physical separator
margin.  This is the remaining Gibbs/dimensional-transmutation upper seam. -/
structure LinearMarginTail
    (P : PhysicalSeparator) (A : PhysicalSpacing) : Type where
  start : Nat
  ceiling : Q'
  margin_le : forall j : Nat, start <= j ->
    P.physMargin j <= ceiling * A.spacing j

namespace LinearMarginTail

variable {P : PhysicalSeparator} {A : PhysicalSpacing}

/-- The linear coefficient is automatically positive: it bounds a strictly
positive margin divided by a positive spacing at the first tail index. -/
theorem ceiling_pos (L : LinearMarginTail P A) :
    (0 : Q') < L.ceiling := by
  have hratePos :
      (0 : Q') < Q'.divPos (P.physMargin L.start)
        (A.spacing L.start) (A.spacing_pos L.start) :=
    Q'.divPos_pos _ _ (A.spacing_pos L.start) (P.physMargin_pos L.start)
  have hrateLe :
      Q'.divPos (P.physMargin L.start)
          (A.spacing L.start) (A.spacing_pos L.start) <= L.ceiling :=
    Q'.divPos_le_of_le_mul _ _ (A.spacing_pos L.start)
      (L.margin_le L.start (Nat.le_refl _))
  exact Q'.pos_of_lt_of_le hratePos hrateLe

/-- Positive denominator used to choose a safe half-window spacing. -/
def thresholdDenominator (L : LinearMarginTail P A) : Q' :=
  (1 : Q') + L.ceiling

theorem thresholdDenominator_pos (L : LinearMarginTail P A) :
    (0 : Q') < L.thresholdDenominator :=
  Q'.pos_add_nonneg (by decide) (Q'.le_of_lt L.ceiling_pos)

/-- A positive spacing threshold forcing `ceiling * spacing <= 1/2`. -/
def spacingThreshold (L : LinearMarginTail P A) : Q' :=
  Q'.divPos HalfPow.half L.thresholdDenominator L.thresholdDenominator_pos

theorem spacingThreshold_pos (L : LinearMarginTail P A) :
    (0 : Q') < L.spacingThreshold :=
  Q'.divPos_pos _ _ L.thresholdDenominator_pos (by decide)

theorem ceiling_mul_spacingThreshold_le_half
    (L : LinearMarginTail P A) :
    L.ceiling * L.spacingThreshold <= HalfPow.half := by
  have hceilingDen : L.ceiling <= L.thresholdDenominator := by
    have h := Q'.add_le_add_right (0 : Q') 1 L.ceiling Q'.zero_le_one
    rw [Q'.zero_add'] at h
    exact h
  have hscaled :
      L.ceiling * L.spacingThreshold <=
        L.thresholdDenominator * L.spacingThreshold :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hceilingDen
      (Q'.le_of_lt L.spacingThreshold_pos)
  have hcollapse :
      (L.thresholdDenominator * L.spacingThreshold).eqv HalfPow.half := by
    exact Q'.eqv_trans _ _ _
      (Q'.mul_comm_eqv L.thresholdDenominator L.spacingThreshold)
      (Q'.divPos_mul_eqv HalfPow.half L.thresholdDenominator
        L.thresholdDenominator_pos)
  exact Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv hcollapse)

/-- The computed scale at which both the linear estimate and the small-spacing
estimate are valid. -/
def eventualStart (L : LinearMarginTail P A) (Z : SpacingToZero A) : Nat :=
  max L.start (Z.modulus L.spacingThreshold)

/-- Algebraic conversion of `1-q <= 1/2` into `1/2 <= q`. -/
theorem half_le_of_one_sub_le_half {q : Q'}
    (h : (1 : Q') - q <= HalfPow.half) :
    HalfPow.half <= q := by
  have hadd := Q'.add_le_add_right ((1 : Q') - q) HalfPow.half q h
  have hcancel : (((1 : Q') - q) + q).eqv (1 : Q') :=
    Q'.eqv_trans _ _ _
      (Q'.add_assoc_eqv 1 (-q) q)
      (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left 1 ((-q) + q) 0
          (Q'.neg_add_self_eqv q))
        (Q'.eqv_of_eq (Q'.add_zero' 1)))
  have hone : (1 : Q') <= HalfPow.half + q :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv hcancel) hadd
  have hsub : (1 : Q') + (-HalfPow.half) <= q :=
    Q'.sub_le_of_le_add hone
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (by decide)) hsub

/-- The cross-multiplied tail estimate gives the rational margin-rate ceiling
at the computed common start. -/
def toTailMarginRateCeiling
    (L : LinearMarginTail P A) (Z : SpacingToZero A) :
    TailMarginRateCeiling P A (L.eventualStart Z) where
  ceiling := L.ceiling
  margin_bound := fun j hj => by
    apply Q'.divPos_le_of_le_mul
    exact L.margin_le j
      (Nat.le_trans (Nat.le_max_left _ _) hj)

/-- Vanishing spacing turns the same linear margin estimate into the eventual
direct logarithm half-window. -/
def toEventualHalfWindow
    (L : LinearMarginTail P A) (Z : SpacingToZero A) :
    EventualSeparatorHalfWindow P (L.eventualStart Z) where
  sep_ge_half := fun j hj => by
    have htail : L.start <= j :=
      Nat.le_trans (Nat.le_max_left _ _) hj
    have hsmallStart : Z.modulus L.spacingThreshold <= j :=
      Nat.le_trans (Nat.le_max_right _ _) hj
    have hspacing : A.spacing j <= L.spacingThreshold :=
      Z.spacing_le L.spacingThreshold L.spacingThreshold_pos j hsmallStart
    have hscaled :
        L.ceiling * A.spacing j <=
          L.ceiling * L.spacingThreshold :=
      Q'.mul_le_mul_of_nonneg_left _ _ _ hspacing
        (Q'.le_of_lt L.ceiling_pos)
    have hmarginHalf : P.physMargin j <= HalfPow.half :=
      Q'.le_trans' _ _ _ (L.margin_le j htail)
        (Q'.le_trans' _ _ _ hscaled L.ceiling_mul_spacingThreshold_le_half)
    exact half_le_of_one_sub_le_half hmarginHalf

end LinearMarginTail

end YMGap.Continuum.PhysicalSeparatorLinearTail

#print axioms YMGap.Continuum.PhysicalSeparatorLinearTail.LinearMarginTail.ceiling_pos
#print axioms YMGap.Continuum.PhysicalSeparatorLinearTail.LinearMarginTail.spacingThreshold_pos
#print axioms YMGap.Continuum.PhysicalSeparatorLinearTail.LinearMarginTail.ceiling_mul_spacingThreshold_le_half
#print axioms YMGap.Continuum.PhysicalSeparatorLinearTail.LinearMarginTail.half_le_of_one_sub_le_half
#print axioms YMGap.Continuum.PhysicalSeparatorLinearTail.LinearMarginTail.toTailMarginRateCeiling
#print axioms YMGap.Continuum.PhysicalSeparatorLinearTail.LinearMarginTail.toEventualHalfWindow
