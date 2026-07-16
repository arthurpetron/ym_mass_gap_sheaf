/-
# Polarized doubled-time identity for the strict OS cylinder form

The derived doubled-time reflection identity was initially stated on the
diagonal,

  `Q(T_s v) = B(v, T_(2s) v)`.

Because the strict cylinder form and both geometric transports are genuinely
linear on their quotient-free presentations, constructive real polarization
recovers its full symmetric off-diagonal content.  For two presentations the
result is

  `B(T_s x, T_s y) = 1/2 * (B(x, T_(2s) y) + B(y, T_(2s) x))`,

with the source arguments canonically zero-extended to the common outer box.
The coefficient `1/2` is represented without division as two copies of the
already derived exact polarization quarter.

This is the strongest consequence of diagonal doubled-time covariance alone.
It does not identify the two oriented cross terms and therefore does not
assert time-translation self-adjointness.
-/

import YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderBaseTransportBilinear
import YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSIdentity
import YMGap.Continuum.RingNormaliser

namespace YMGap.Continuum.Z4HalfTimeReflectionStrictJointPolarizedDoubledTimeIdentity

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderBaseTransportBilinear
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderBilinearTimeTranslation
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderSeminorm
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSBilinear
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSIdentity
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast_local (a : Q') : (-a).num = -(a.num) := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast_local,
               Q'.mkPos_num, Q'.mkPos_den,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one,
               Int.zero_mul, Int.mul_zero, Int.zero_add, Int.add_zero]; ac_rfl))

private theorem creal_mul_congr_right_local
    {scalar left right : CReal} (h : CReal.Equiv left right) :
    CReal.Equiv (CReal.mul scalar left) (CReal.mul scalar right) :=
  CReal.Equiv.trans (CRealAlg.cmul_comm scalar left)
    (CReal.Equiv.trans (CReal.mul_congr_left h)
      (CRealAlg.cmul_comm right scalar))

private theorem cmul_neg_one_equiv_neg (value : CReal) :
    CReal.Equiv
      (CReal.mul (CReal.ofQ' (-1)) value)
      (CReal.neg value) :=
  SumOfSquares.Equiv_of_approx_eqv (fun stage => by
    show ((-1 : Q') * value.approx stage) ≈
      -(value.approx stage)
    ring_qeqv)

private theorem cmul_neg_one_twice_equiv (value : CReal) :
    CReal.Equiv
      (CReal.mul (CReal.ofQ' (-1))
        (CReal.mul (CReal.ofQ' (-1)) value))
      value :=
  SumOfSquares.Equiv_of_approx_eqv (fun stage => by
    show ((-1 : Q') * ((-1 : Q') * value.approx stage)) ≈
      value.approx stage
    ring_qeqv)

private theorem reflectionBilinear_add_add_expand
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat}
    (a b c d : StrictJointCylinderVector base) :
    CReal.Equiv
      (strictJointCylinderReflectionBilinear hcoupling hle
        (a.add b) (c.add d))
      (CReal.add
        (CReal.add
          (strictJointCylinderReflectionBilinear hcoupling hle a c)
          (strictJointCylinderReflectionBilinear hcoupling hle a d))
        (CReal.add
          (strictJointCylinderReflectionBilinear hcoupling hle b c)
          (strictJointCylinderReflectionBilinear hcoupling hle b d))) := by
  exact CReal.Equiv.trans
    (strictJointCylinderReflectionBilinear_add_left
      hcoupling hle a b (c.add d))
    (CReal.Equiv_add
      (strictJointCylinderReflectionBilinear_add_right
        hcoupling hle a c d)
      (strictJointCylinderReflectionBilinear_add_right
        hcoupling hle b c d))

private theorem reflectionBilinear_sub_sub_expand
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat}
    (a b c d : StrictJointCylinderVector base) :
    CReal.Equiv
      (strictJointCylinderReflectionBilinear hcoupling hle
        (a.add (b.smul (-1))) (c.add (d.smul (-1))))
      (CReal.add
        (CReal.add
          (strictJointCylinderReflectionBilinear hcoupling hle a c)
          (CReal.neg
            (strictJointCylinderReflectionBilinear hcoupling hle a d)))
        (CReal.add
          (CReal.neg
            (strictJointCylinderReflectionBilinear hcoupling hle b c))
          (strictJointCylinderReflectionBilinear hcoupling hle b d))) := by
  have hexpand := reflectionBilinear_add_add_expand
    hcoupling hle a (b.smul (-1)) c (d.smul (-1))
  have had : CReal.Equiv
      (strictJointCylinderReflectionBilinear hcoupling hle
        a (d.smul (-1)))
      (CReal.neg
        (strictJointCylinderReflectionBilinear hcoupling hle a d)) :=
    CReal.Equiv.trans
      (strictJointCylinderReflectionBilinear_smul_right
        hcoupling hle (-1) a d)
      (cmul_neg_one_equiv_neg
        (strictJointCylinderReflectionBilinear hcoupling hle a d))
  have hbc : CReal.Equiv
      (strictJointCylinderReflectionBilinear hcoupling hle
        (b.smul (-1)) c)
      (CReal.neg
        (strictJointCylinderReflectionBilinear hcoupling hle b c)) :=
    CReal.Equiv.trans
      (strictJointCylinderReflectionBilinear_smul_left
        hcoupling hle (-1) b c)
      (cmul_neg_one_equiv_neg
        (strictJointCylinderReflectionBilinear hcoupling hle b c))
  have hbdInner := strictJointCylinderReflectionBilinear_smul_right
    hcoupling hle (-1) b d
  have hbdOuter := strictJointCylinderReflectionBilinear_smul_left
    hcoupling hle (-1) b (d.smul (-1))
  have hbd : CReal.Equiv
      (strictJointCylinderReflectionBilinear hcoupling hle
        (b.smul (-1)) (d.smul (-1)))
      (strictJointCylinderReflectionBilinear hcoupling hle b d) :=
    CReal.Equiv.trans hbdOuter
      (CReal.Equiv.trans
        (creal_mul_congr_right_local hbdInner)
        (cmul_neg_one_twice_equiv
          (strictJointCylinderReflectionBilinear hcoupling hle b d)))
  exact CReal.Equiv.trans hexpand
    (CReal.Equiv_add
      (CReal.Equiv_add (CReal.Equiv.refl _) had)
      (CReal.Equiv_add hbc hbd))

private def polarizedCrossL : PolyExpr :=
  let q := PolyExpr.var 0
  let diagonalLeft := PolyExpr.var 1
  let crossForward := PolyExpr.var 2
  let crossBackward := PolyExpr.var 3
  let diagonalRight := PolyExpr.var 4
  .mul q
    (.add
      (.add (.add diagonalLeft crossForward)
        (.add crossBackward diagonalRight))
      (.neg
        (.add (.add diagonalLeft (.neg crossForward))
          (.add (.neg crossBackward) diagonalRight))))

private def polarizedCrossR : PolyExpr :=
  let q := PolyExpr.var 0
  let crossForward := PolyExpr.var 2
  let crossBackward := PolyExpr.var 3
  .mul (.add q q) (.add crossForward crossBackward)

private theorem polarizedCross_normal :
    normalize polarizedCrossL = normalize polarizedCrossR := by
  decide

private theorem rational_polarized_cross_algebra
    (q diagonalLeft crossForward crossBackward diagonalRight : Q') :
    q *
        (((diagonalLeft + crossForward) +
            (crossBackward + diagonalRight)) +
          (-((diagonalLeft + (-crossForward)) +
            ((-crossBackward) + diagonalRight)))) ≈
      (q + q) * (crossForward + crossBackward) := by
  let ρ : Nat → Q' := fun n =>
    if n = 0 then q else if n = 1 then diagonalLeft
    else if n = 2 then crossForward else if n = 3 then crossBackward
    else diagonalRight
  have h := poly_identity_of_normal_eq
    polarizedCrossL polarizedCrossR polarizedCross_normal ρ
  simpa [polarizedCrossL, polarizedCrossR,
    RingNormaliser.eval, ρ] using h

private theorem polarized_cross_algebra
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat}
    (a b c d : StrictJointCylinderVector base) :
    CReal.Equiv
      (CReal.mul (CReal.ofQ' strictJointPolarizationQuarter)
        (CReal.add
          (strictJointCylinderReflectionBilinear hcoupling hle
            (a.add b) (c.add d))
          (CReal.neg
            (strictJointCylinderReflectionBilinear hcoupling hle
              (a.add (b.smul (-1)))
              (c.add (d.smul (-1)))))))
      (CReal.mul
        (CReal.ofQ'
          (strictJointPolarizationQuarter +
            strictJointPolarizationQuarter))
        (CReal.add
          (strictJointCylinderReflectionBilinear hcoupling hle a d)
          (strictJointCylinderReflectionBilinear hcoupling hle b c))) := by
  have hplus := reflectionBilinear_add_add_expand
    hcoupling hle a b c d
  have hminus := reflectionBilinear_sub_sub_expand
    hcoupling hle a b c d
  have hinside := CReal.Equiv.trans
    (CReal.add_congr_left hplus)
    (CReal.add_congr_right (CReal.neg_congr hminus))
  refine CReal.Equiv.trans (creal_mul_congr_right_local hinside) ?_
  exact SumOfSquares.Equiv_of_approx_eqv (fun stage => by
    show
      strictJointPolarizationQuarter *
          ((((strictJointCylinderReflectionBilinear hcoupling hle a c).approx stage +
              (strictJointCylinderReflectionBilinear hcoupling hle a d).approx stage) +
            ((strictJointCylinderReflectionBilinear hcoupling hle b c).approx stage +
              (strictJointCylinderReflectionBilinear hcoupling hle b d).approx stage)) +
          (-((((strictJointCylinderReflectionBilinear hcoupling hle a c).approx stage +
                (-(strictJointCylinderReflectionBilinear hcoupling hle a d).approx stage)) +
              ((-(strictJointCylinderReflectionBilinear hcoupling hle b c).approx stage) +
                (strictJointCylinderReflectionBilinear hcoupling hle b d).approx stage))))) ≈
        (strictJointPolarizationQuarter + strictJointPolarizationQuarter) *
          ((strictJointCylinderReflectionBilinear hcoupling hle a d).approx stage +
            (strictJointCylinderReflectionBilinear hcoupling hle b c).approx stage)
    exact rational_polarized_cross_algebra
      strictJointPolarizationQuarter
      ((strictJointCylinderReflectionBilinear hcoupling hle a c).approx stage)
      ((strictJointCylinderReflectionBilinear hcoupling hle a d).approx stage)
      ((strictJointCylinderReflectionBilinear hcoupling hle b c).approx stage)
      ((strictJointCylinderReflectionBilinear hcoupling hle b d).approx stage))

/-- Full symmetric off-diagonal content of the derived doubled-time OS
identity.  Both source arguments are canonically zero-extended to the common
box `base + 2 * shift`; the two target arguments are literal time translates
by `2 * shift`.

The right side is exactly one half of the sum of the two oriented cross
terms.  No equality between those oriented terms is inferred. -/
theorem strictJointDoubledTimeMixedOSIdentity_polarized
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat} (shift : Nat)
    (left right : StrictJointCylinderVector base) :
    CReal.Equiv
      (strictJointCylinderReflectionBilinear hcoupling hle
        (timeTranslateStrictJointCylinderVector shift left)
        (timeTranslateStrictJointCylinderVector shift right))
      (CReal.mul
        (CReal.ofQ'
          (strictJointPolarizationQuarter +
            strictJointPolarizationQuarter))
        (CReal.add
          (strictJointCylinderReflectionBilinear hcoupling hle
            (strictJointDoubledTimeMixedSource shift left)
            (strictJointDoubledTimeMixedTarget shift right))
          (strictJointCylinderReflectionBilinear hcoupling hle
            (strictJointDoubledTimeMixedSource shift right)
            (strictJointDoubledTimeMixedTarget shift left)))) := by
  let plus := left.add right
  let minus := left.add (right.smul (-1))
  have hplusRaw := strictJointDoubledTimeMixedOSIdentity_derived
    hcoupling hle (fixedStage := shift + shift)
      (Nat.le_refl (shift + shift)) plus
  have hminusRaw := strictJointDoubledTimeMixedOSIdentity_derived
    hcoupling hle (fixedStage := shift + shift)
      (Nat.le_refl (shift + shift)) minus
  have hplus : CReal.Equiv
      (((timeTranslateStrictJointCylinderVector shift left).add
        (timeTranslateStrictJointCylinderVector shift right)).reflectionQuadratic
          hcoupling hle)
      (strictJointCylinderReflectionBilinear hcoupling hle
        ((strictJointDoubledTimeMixedSource shift left).add
          (strictJointDoubledTimeMixedSource shift right))
        ((strictJointDoubledTimeMixedTarget shift left).add
          (strictJointDoubledTimeMixedTarget shift right))) := by
    simpa only [plus, StrictJointDoubledTimeMixedOSIdentity,
      strictJointDoubledTimeMixedOSBilinear,
      strictJointDoubledTimeMixedSource,
      strictJointDoubledTimeMixedTarget,
      boxTransportStrictJointCylinderVector_add,
      timeTranslateStrictJointCylinderVector_add] using hplusRaw
  have hminus : CReal.Equiv
      (((timeTranslateStrictJointCylinderVector shift left).add
        ((timeTranslateStrictJointCylinderVector shift right).smul (-1))).reflectionQuadratic
          hcoupling hle)
      (strictJointCylinderReflectionBilinear hcoupling hle
        ((strictJointDoubledTimeMixedSource shift left).add
          ((strictJointDoubledTimeMixedSource shift right).smul (-1)))
        ((strictJointDoubledTimeMixedTarget shift left).add
          ((strictJointDoubledTimeMixedTarget shift right).smul (-1)))) := by
    simpa only [minus, StrictJointDoubledTimeMixedOSIdentity,
      strictJointDoubledTimeMixedOSBilinear,
      strictJointDoubledTimeMixedSource,
      strictJointDoubledTimeMixedTarget,
      boxTransportStrictJointCylinderVector_add,
      boxTransportStrictJointCylinderVector_smul,
      timeTranslateStrictJointCylinderVector_add,
      timeTranslateStrictJointCylinderVector_smul] using hminusRaw
  change CReal.Equiv
    (CReal.mul (CReal.ofQ' strictJointPolarizationQuarter)
      (CReal.add
        (((timeTranslateStrictJointCylinderVector shift left).add
          (timeTranslateStrictJointCylinderVector shift right)).reflectionQuadratic
            hcoupling hle)
        (CReal.neg
          (((timeTranslateStrictJointCylinderVector shift left).add
            ((timeTranslateStrictJointCylinderVector shift right).smul (-1))).reflectionQuadratic
              hcoupling hle)))) _
  have hdiagonal : CReal.Equiv
      (CReal.mul (CReal.ofQ' strictJointPolarizationQuarter)
        (CReal.add
          (((timeTranslateStrictJointCylinderVector shift left).add
            (timeTranslateStrictJointCylinderVector shift right)).reflectionQuadratic
              hcoupling hle)
          (CReal.neg
            (((timeTranslateStrictJointCylinderVector shift left).add
              ((timeTranslateStrictJointCylinderVector shift right).smul (-1))).reflectionQuadratic
                hcoupling hle))))
      (CReal.mul (CReal.ofQ' strictJointPolarizationQuarter)
        (CReal.add
          (strictJointCylinderReflectionBilinear hcoupling hle
            ((strictJointDoubledTimeMixedSource shift left).add
              (strictJointDoubledTimeMixedSource shift right))
            ((strictJointDoubledTimeMixedTarget shift left).add
              (strictJointDoubledTimeMixedTarget shift right)))
          (CReal.neg
            (strictJointCylinderReflectionBilinear hcoupling hle
              ((strictJointDoubledTimeMixedSource shift left).add
                ((strictJointDoubledTimeMixedSource shift right).smul (-1)))
              ((strictJointDoubledTimeMixedTarget shift left).add
                ((strictJointDoubledTimeMixedTarget shift right).smul (-1))))))) :=
    creal_mul_congr_right_local
      (scalar := CReal.ofQ' strictJointPolarizationQuarter)
      (CReal.Equiv.trans
        (CReal.add_congr_left hplus)
        (CReal.add_congr_right (CReal.neg_congr hminus)))
  exact CReal.Equiv.trans hdiagonal
    (polarized_cross_algebra hcoupling hle
      (strictJointDoubledTimeMixedSource shift left)
      (strictJointDoubledTimeMixedSource shift right)
      (strictJointDoubledTimeMixedTarget shift left)
      (strictJointDoubledTimeMixedTarget shift right))

/-! ## The remaining oriented covariance defect -/

/-- One oriented one-sided transfer coefficient in a common source box.
Self-adjointness of time translation is exactly symmetry of this function in
`left` and `right`. -/
def strictJointOneSidedTimeCross
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat} (shift : Nat)
    (left right : StrictJointCylinderVector base) : CReal :=
  strictJointCylinderReflectionBilinear hcoupling hle
    (boxTransportStrictJointCylinderVector
      (Nat.le_add_right base shift) left)
    (timeTranslateStrictJointCylinderVector shift right)

/-- Exact mixed off-diagonal covariance still needed for self-adjoint time
translation.  It is exposed on inhabited strict-cylinder presentations and
does not follow merely by naming a diagonal positivity or contraction
property. -/
def StrictJointOneSidedTimeCovariance
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat} (shift : Nat)
    (left right : StrictJointCylinderVector base) : Prop :=
  CReal.Equiv
    (strictJointOneSidedTimeCross hcoupling hle shift left right)
    (strictJointOneSidedTimeCross hcoupling hle shift right left)

/-- The polarized identity fixes the symmetric part of every even-time
one-sided transfer coefficient.  The only piece it leaves undetermined is
the antisymmetric difference between the two displayed cross terms. -/
theorem strictJointEvenTimeCross_symmetrization
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat} (shift : Nat)
    (left right : StrictJointCylinderVector base) :
    CReal.Equiv
      (strictJointCylinderReflectionBilinear hcoupling hle
        (timeTranslateStrictJointCylinderVector shift left)
        (timeTranslateStrictJointCylinderVector shift right))
      (CReal.mul
        (CReal.ofQ'
          (strictJointPolarizationQuarter +
            strictJointPolarizationQuarter))
        (CReal.add
          (strictJointOneSidedTimeCross hcoupling hle
            (shift + shift) left right)
          (strictJointOneSidedTimeCross hcoupling hle
            (shift + shift) right left))) := by
  simpa only [strictJointOneSidedTimeCross,
    strictJointDoubledTimeMixedSource,
    strictJointDoubledTimeMixedTarget] using
      (strictJointDoubledTimeMixedOSIdentity_polarized
        hcoupling hle shift left right)

#print axioms strictJointDoubledTimeMixedOSIdentity_polarized
#print axioms strictJointEvenTimeCross_symmetrization

end YMGap.Continuum.Z4HalfTimeReflectionStrictJointPolarizedDoubledTimeIdentity
