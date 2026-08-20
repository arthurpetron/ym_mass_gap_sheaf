/-
M4e -- summability of the direct-log quadratic remainder from physical data.

The exact logarithmic mass differs from its rational margin proxy by

    quadraticRateError_j = 3 (1-q_j)^2 / a_j.

Once a linear physical-margin estimate `1-q_j <= M a_j` holds, this error is
bounded by `3 M^2 a_j`.  Consequently an inverse-square spacing tail gives an
explicit antitone tail control for the exact logarithmic error.  This file is
pure constructive rational algebra: it neither assumes nor extracts a hidden
convergence modulus.
-/

import YMGap.Continuum.DirectLogQuadraticRemainder
import YMGap.Continuum.PhysicalSeparatorLinearTail
import YMGap.Continuum.InverseSquareAntitoneTailControl

namespace YMGap.Continuum.QuadraticRateErrorTailControl

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.DirectLogQuadraticRemainder
open YMGap.Continuum.InverseSquareAntitoneTailControl
open YMGap.Continuum.PhysicalSeparator
open YMGap.Continuum.PhysicalSeparatorLinearTail
open YMGap.Continuum.PhysicalSeparatorLogRate
open YMGap.Continuum.SummableCRealStepVariation
open YMGap.Continuum.SummableInverseSquare

/-- A named inverse-square majorant for a physical spacing after a finite
cutoff.  The shift is explicit, so no estimate is asserted for the discarded
finite prefix. -/
structure InverseSquareSpacingTail (A : PhysicalSpacing) (start : Nat) : Type where
  coefficient : Q'
  coefficient_nonnegative : (0 : Q') <= coefficient
  spacing_le : forall k : Nat,
    A.spacing (start + k) <= coefficient * invSqTerm 2 (by decide) k

namespace InverseSquareSpacingTail

variable {A : PhysicalSpacing} {start : Nat}

/-- Drop a further finite prefix from an inverse-square spacing majorant. -/
def shifted (S : InverseSquareSpacingTail A start) (shift : Nat) :
    InverseSquareSpacingTail A (start + shift) where
  coefficient := S.coefficient
  coefficient_nonnegative := S.coefficient_nonnegative
  spacing_le := by
    intro k
    have hspacing := S.spacing_le (shift + k)
    have hinverse :
        invSqTerm 2 (by decide) (shift + k) <=
          invSqTerm 2 (by decide) k :=
      invSqTerm_antitone 2 (by decide) (by omega)
    have hscaled := Q'.mul_le_mul_of_nonneg_left
      (invSqTerm 2 (by decide) (shift + k))
      (invSqTerm 2 (by decide) k) S.coefficient hinverse
      S.coefficient_nonnegative
    simpa only [Nat.add_assoc] using
      Q'.le_trans' _ _ _ hspacing hscaled

end InverseSquareSpacingTail

namespace LinearMarginTail

variable {P : PhysicalSeparator} {A : PhysicalSpacing}

/-- Three copies of the square of the linear margin coefficient. -/
def quadraticSpacingCoefficient (L : LinearMarginTail P A) : Q' :=
  let square := L.ceiling * L.ceiling
  square + (square + square)

theorem quadraticSpacingCoefficient_nonnegative
    (L : LinearMarginTail P A) :
    (0 : Q') <= quadraticSpacingCoefficient L := by
  let square := L.ceiling * L.ceiling
  have hsquare : (0 : Q') <= square :=
    Q'.mul_nonneg _ _ (Q'.le_of_lt L.ceiling_pos)
      (Q'.le_of_lt L.ceiling_pos)
  exact Q'.zero_le_add _ _ hsquare (Q'.zero_le_add _ _ hsquare hsquare)

/-- Regrouping identity behind cancellation of one positive spacing factor. -/
private theorem triple_scaled_square_eqv
    (ceiling spacing : Q') :
    let scaled := ceiling * spacing
    let square := ceiling * ceiling
    (scaled * scaled + (scaled * scaled + scaled * scaled)).eqv
      (((square + (square + square)) * spacing) * spacing) := by
  dsimp
  show _ * (_ : Int) = _ * (_ : Int)
  simp only [Q'.add_num_cast, Q'.add_den_cast,
    Q'.mul_num_cast, Q'.mul_den_cast, Int.add_mul]
  ac_rfl

/-- A linear margin tail converts the exact-log quadratic error into a
multiple of the physical spacing. -/
theorem quadraticRateError_le_spacing
    (L : LinearMarginTail P A) (j : Nat) (hj : L.start <= j) :
    quadraticRateError P A j <=
      quadraticSpacingCoefficient L * A.spacing j := by
  let margin := P.physMargin j
  let spacing := A.spacing j
  let scaled := L.ceiling * spacing
  have hmargin : margin <= scaled := L.margin_le j hj
  have hmargin0 : (0 : Q') <= margin := Q'.le_of_lt (P.physMargin_pos j)
  have hscaled0 : (0 : Q') <= scaled :=
    Q'.mul_nonneg _ _ (Q'.le_of_lt L.ceiling_pos)
      (Q'.le_of_lt (A.spacing_pos j))
  have hsquare : margin * margin <= scaled * scaled :=
    Q'.mul_le_mul_of_nonneg hmargin hmargin hscaled0 hmargin0
  have htriple :
      margin * margin + (margin * margin + margin * margin) <=
        scaled * scaled + (scaled * scaled + scaled * scaled) :=
    Q'.add_le_add hsquare (Q'.add_le_add hsquare hsquare)
  have htarget :
      (scaled * scaled + (scaled * scaled + scaled * scaled)).eqv
        ((quadraticSpacingCoefficient L * spacing) * spacing) := by
    exact triple_scaled_square_eqv L.ceiling spacing
  apply Q'.divPos_le_of_le_mul
  exact Q'.le_trans' _ _ _ htriple (Q'.le_of_eqv htarget)

/-- A linear margin estimate and an inverse-square spacing tail produce the
explicit tail control required by the exact-rate proxy engine. -/
def quadraticRateErrorTailControl
    (L : LinearMarginTail P A) (start : Nat) (hstart : L.start <= start)
    (S : InverseSquareSpacingTail A start) :
    AntitoneTailControl
      (fun k => quadraticRateError P A (start + k)) := by
  let coefficient := quadraticSpacingCoefficient L * S.coefficient
  have hcoefficient : (0 : Q') <= coefficient :=
    Q'.mul_nonneg _ _ (quadraticSpacingCoefficient_nonnegative L)
      S.coefficient_nonnegative
  apply inverseSquareTermTailControl
    (fun k => quadraticRateError P A (start + k)) 2 (by decide)
    coefficient hcoefficient
  intro k
  have herror := quadraticRateError_le_spacing L
    (start + k) (Nat.le_trans hstart (by omega))
  have hscaled := Q'.mul_le_mul_of_nonneg_left
    (A.spacing (start + k))
    (S.coefficient * invSqTerm 2 (by decide) k)
    (quadraticSpacingCoefficient L) (S.spacing_le k)
    (quadraticSpacingCoefficient_nonnegative L)
  have hregroup :
      (quadraticSpacingCoefficient L *
        (S.coefficient * invSqTerm 2 (by decide) k)).eqv
      (coefficient * invSqTerm 2 (by decide) k) :=
    Q'.eqv_symm
      (Q'.mul_assoc_eqv (quadraticSpacingCoefficient L) S.coefficient
        (invSqTerm 2 (by decide) k))
  exact Q'.le_trans' _ _ _ herror
    (Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv hregroup))

end LinearMarginTail

end YMGap.Continuum.QuadraticRateErrorTailControl

#print axioms YMGap.Continuum.QuadraticRateErrorTailControl.LinearMarginTail.quadraticSpacingCoefficient_nonnegative
#print axioms YMGap.Continuum.QuadraticRateErrorTailControl.InverseSquareSpacingTail.shifted
#print axioms YMGap.Continuum.QuadraticRateErrorTailControl.LinearMarginTail.quadraticRateError_le_spacing
#print axioms YMGap.Continuum.QuadraticRateErrorTailControl.LinearMarginTail.quadraticRateErrorTailControl
