/-
# Explicit norm-one scaling of the SAME dyadic Wilson excitation

The actual centered dyadic norm has an explicit QCauchy representative and
a positive starRatio floor at each nome. The existing clamped inverse-root
construction therefore scales this very excitation to norm one on its SAME
all-nome completion. Its actual time response scales by the same real square.

This is an explicitly renormalized observable, not an unrenormalized uniform
norm floor. No changing-nome/width carrier identification, scaling Cauchy
modulus, continuum survival or Yang--Mills local-field identification is
asserted. Normalization does not improve the original relative response.
-/

import YMGap.Continuum.BF4WilsonAllNomeDyadicSpectatorResponse
import YMGap.Continuum.BF4WilsonAllNomeRealScalarLaws
import YMGap.Continuum.PositiveCRealNormalizationScalar

namespace YMGap.Continuum.BF4WilsonAllNomeDyadicUnitExcitation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Constructive.CRealAlg
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4DyadicWilsonSquare
open YMGap.Continuum.BF4ExactSlabLocalStarComparison (starRatio starRatio_positive)
open YMGap.Continuum.BF4WilsonAllNomeLoopTimePin (loopState)
open YMGap.Continuum.BF4WilsonAllNomeCenteredMoments
  (centeredTimeMoment centeredTimeMomentCauchy)
open YMGap.Continuum.BF4WilsonAllNomeDyadicVariance (centered_norm_floor)
open YMGap.Continuum.BF4WilsonAllNomeDyadicExcitation
  (dyadicExcitation dyadicExcitation_correlator_pin)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4WilsonAllNomeCompletedRealScalar
open YMGap.Continuum.BF4WilsonAllNomeRealScalarLaws
open YMGap.Continuum.BF4WilsonAllNomeLinear (completedZero)
open YMGap.Continuum.BF4WilsonAllNomeBilinearTime (completedInner_zero_left)
open YMGap.Continuum.BF4ExactSlabPlaquetteRealScalarAlgebra (scalarMulCauchy)
open YMGap.Continuum.BF4DyadicWilsonSquareSpectatorResponse (squareResponseFraction)
open YMGap.Continuum.BF4WilsonAllNomeDyadicSpectatorResponse
  (dyadicExcitation_time_geometric_fraction)

local notation "Rq" a:arg => Quotient.mk crealSetoid (ofQ' a)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (scale width : Nat) (hwidth : side scale < width)

local notation "x" => loopState (paddedSquare scale width hwidth)
local notation "v" => Subtype.val (dyadicExcitation hw0 hw1 scale width hwidth)
local notation "B" => completedInner hw0 hw1
local notation "T" => completedTime hw0 hw1

/-- Representative of the actual original centered norm, not a surrogate. -/
def dyadicOriginalNorm : CReal := centeredTimeMoment hw0 hw1 0 x x

def dyadicOriginalNormCauchy : QCauchy (dyadicOriginalNorm hw0 hw1 scale width hwidth).approx :=
  centeredTimeMomentCauchy hw0 hw1 0 x x

theorem dyadicOriginalNorm_pin :
    B v v = Quotient.mk crealSetoid (dyadicOriginalNorm hw0 hw1 scale width hwidth) := by
  have h := dyadicExcitation_correlator_pin hw0 hw1 scale width hwidth 0
  rw [completedTime_zero] at h
  exact h

theorem dyadicOriginalNorm_floor :
    leEv (ofQ' (starRatio w)) (dyadicOriginalNorm hw0 hw1 scale width hwidth) :=
  centered_norm_floor hw0 hw1 scale width hwidth

/-- Constructive inverse square root, with no choice of representative/modulus. -/
def dyadicNormalizer : CReal :=
  PositiveCRealNormalizationScalar.scalar
    (dyadicOriginalNorm hw0 hw1 scale width hwidth)
    (dyadicOriginalNormCauchy hw0 hw1 scale width hwidth)
    (starRatio w) (starRatio_positive hw0 hw1)

def dyadicNormalizerCauchy : QCauchy (dyadicNormalizer hw0 hw1 scale width hwidth).approx :=
  PositiveCRealNormalizationScalar.scalarCauchy
    (dyadicOriginalNorm hw0 hw1 scale width hwidth)
    (dyadicOriginalNormCauchy hw0 hw1 scale width hwidth)
    (starRatio w) (starRatio_positive hw0 hw1)

theorem dyadicNormalizer_normalizes :
    Equiv (mul (dyadicNormalizer hw0 hw1 scale width hwidth)
      (mul (dyadicNormalizer hw0 hw1 scale width hwidth)
        (dyadicOriginalNorm hw0 hw1 scale width hwidth))) cone :=
  PositiveCRealNormalizationScalar.scalar_normalizes
    (dyadicOriginalNorm hw0 hw1 scale width hwidth)
    (dyadicOriginalNormCauchy hw0 hw1 scale width hwidth)
    (starRatio w) (starRatio_positive hw0 hw1)
    (dyadicOriginalNorm_floor hw0 hw1 scale width hwidth)

/-- The SAME vacuum-complement state, explicitly scaled by its own norm. -/
def dyadicUnitExcitation : VacuumComplement hw0 hw1 (width := width) :=
  vacuumComplementRealSmul hw0 hw1
    (dyadicNormalizer hw0 hw1 scale width hwidth)
    (dyadicNormalizerCauchy hw0 hw1 scale width hwidth)
    (dyadicExcitation hw0 hw1 scale width hwidth)

local notation "u" => Subtype.val (dyadicUnitExcitation hw0 hw1 scale width hwidth)
local notation "s" => dyadicNormalizer hw0 hw1 scale width hwidth
local notation "cs" => dyadicNormalizerCauchy hw0 hw1 scale width hwidth

theorem dyadicUnitExcitation_norm : B u u = Rq 1 := by
  change B (completedRealSmul hw0 hw1 s cs v) (completedRealSmul hw0 hw1 s cs v) = _
  rw [completedInner_realSmul_diagonal, dyadicOriginalNorm_pin]
  exact Quotient.sound (dyadicNormalizer_normalizes hw0 hw1 scale width hwidth)

theorem dyadicUnitExcitation_norm_ne_zero : B u u ≠ RCzero := by
  intro hz
  have he : Equiv (ofQ' 1) czero :=
    Quotient.exact ((dyadicUnitExcitation_norm hw0 hw1 scale width hwidth).symm.trans hz)
  have hbad : (1 : Q') ≤ 0 := by
    apply Q'.le_of_forall_pos_add
    intro epsilon hepsilon
    obtain ⟨N, hN⟩ := he epsilon hepsilon
    exact (hN N (Nat.le_refl N)).1
  exact (by decide : ¬ (1 : Q') ≤ 0) hbad

theorem dyadicUnitExcitation_ne_zero : u ≠ completedZero hw0 hw1 width := by
  intro hz
  apply dyadicUnitExcitation_norm_ne_zero hw0 hw1 scale width hwidth
  rw [hz, completedInner_zero_left]

/-- Original centered correlator times the exact inverse norm square. -/
def dyadicUnitResponse (lag : Nat) : CReal :=
  mul s (mul s (centeredTimeMoment hw0 hw1 lag x x))

def dyadicUnitResponseCauchy (lag : Nat) :
    QCauchy (dyadicUnitResponse hw0 hw1 scale width hwidth lag).approx :=
  scalarMulCauchy _ _ cs
    (scalarMulCauchy _ _ cs (centeredTimeMomentCauchy hw0 hw1 lag x x))

theorem dyadicUnitResponse_pin (lag : Nat) :
    B u (T lag u) =
      Quotient.mk crealSetoid (dyadicUnitResponse hw0 hw1 scale width hwidth lag) := by
  change B (completedRealSmul hw0 hw1 s cs v)
    (T lag (completedRealSmul hw0 hw1 s cs v)) = _
  rw [completedTime_realSmul, completedInner_realSmul_left,
    completedInner_realSmul_right, dyadicExcitation_correlator_pin]
  rfl

/-- The existing actual relative floor survives normalization unchanged.
It is not a uniform changing-family or growing-lag floor. -/
theorem dyadicUnitResponse_geometric_floor (lag : Nat) :
    leEv (ofQ' ((squareResponseFraction hw0 hw1 scale)^lag))
      (dyadicUnitResponse hw0 hw1 scale width hwidth lag) := by
  let r := (squareResponseFraction hw0 hw1 scale)^lag
  let A := dyadicOriginalNorm hw0 hw1 scale width hwidth
  have h := dyadicExcitation_time_geometric_fraction hw0 hw1 scale width hwidth lag
  rw [dyadicOriginalNorm_pin, dyadicExcitation_correlator_pin] at h
  have h0 : leEv (mul (ofQ' r) A) (centeredTimeMoment hw0 hw1 lag x x) := h
  have hs : leEv czero s := PositiveCRealNormalizationScalar.scalar_nonnegative
    A (dyadicOriginalNormCauchy hw0 hw1 scale width hwidth)
    (starRatio w) (starRatio_positive hw0 hw1)
  have hscaled := leEv_mul_nonneg_left hs (leEv_mul_nonneg_left hs h0)
  have hr : Equiv (mul s (mul s (mul (ofQ' r) A))) (ofQ' r) :=
    (SumOfSquares.Equiv_of_approx_eqv (fun n =>
      poly_identity_of_normal_eq
        (.mul (.var 0) (.mul (.var 0) (.mul (.var 1) (.var 2))))
        (.mul (.var 1) (.mul (.var 0) (.mul (.var 0) (.var 2))))
        (by decide) (fun
          | 0 => (s).approx n
          | 1 => r
          | _ => A.approx n))).trans
      ((Pivot2.mul_congr_right (dyadicNormalizer_normalizes hw0 hw1 scale width hwidth)).trans
        (cmul_cone (ofQ' r)))
  exact leEv_trans (leEv_of_equiv hr.symm) hscaled

#print axioms dyadicOriginalNorm
#print axioms dyadicOriginalNormCauchy
#print axioms dyadicOriginalNorm_pin
#print axioms dyadicOriginalNorm_floor
#print axioms dyadicNormalizer
#print axioms dyadicNormalizerCauchy
#print axioms dyadicNormalizer_normalizes
#print axioms dyadicUnitExcitation
#print axioms dyadicUnitExcitation_norm
#print axioms dyadicUnitExcitation_norm_ne_zero
#print axioms dyadicUnitExcitation_ne_zero
#print axioms dyadicUnitResponse
#print axioms dyadicUnitResponseCauchy
#print axioms dyadicUnitResponse_pin
#print axioms dyadicUnitResponse_geometric_floor

end YMGap.Continuum.BF4WilsonAllNomeDyadicUnitExcitation
