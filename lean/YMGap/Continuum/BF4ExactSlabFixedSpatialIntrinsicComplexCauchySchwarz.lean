/-
# Sharp complex Cauchy--Schwarz on the intrinsic physical-span carrier

All four real components are placed in one computed intrinsic chart.  The
checked reflected-form complex inequality is then transported back to the
original physical spans.  No quotient representative or scalar choice is
made here.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialReflectedComplexCauchySchwarz
import YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicLinear

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicComplexCauchySchwarz

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialReflectedForm
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicReflectedForm
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicLinear
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicSeminorm (PhysicalSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialReflectedCauchySchwarz
open YMGap.Continuum.BF4ExactSlabFixedSpatialFiniteComplexRealification
open YMGap.Continuum.BF4ExactSlabFixedSpatialReflectedComplexCauchySchwarz

attribute [local irreducible] pairing form

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (width stage : Nat)

abbrev IntrinsicComplexCarrier := PhysicalSpan width × PhysicalSpan width

/-- Real part of the complexified intrinsic pairing. -/
def intrinsicRealifiedPairing
    (x y : IntrinsicComplexCarrier width) : CReal :=
  add (pairing hw0 hw1 width x.1.val y.1.val stage)
    (pairing hw0 hw1 width x.2.val y.2.val stage)

/-- Literal multiplication by `i` on the intrinsic realification. -/
def intrinsicQuarterTurn (y : IntrinsicComplexCarrier width) :
    IntrinsicComplexCarrier width :=
  (smulSpan (-1) y.2, y.1)

/-- Imaginary companion of the intrinsic complex pairing. -/
def intrinsicQuarterTurnPairing
    (x y : IntrinsicComplexCarrier width) : CReal :=
  intrinsicRealifiedPairing hw0 hw1 width stage x
    (intrinsicQuarterTurn width y)

/-- Conventional imaginary part `B(x₁,y₂)-B(x₂,y₁)`. -/
def intrinsicImaginaryPairing
    (x y : IntrinsicComplexCarrier width) : CReal :=
  sub (pairing hw0 hw1 width x.1.val y.2.val stage)
    (pairing hw0 hw1 width x.2.val y.1.val stage)

private def commonHeight (x y : IntrinsicComplexCarrier width) : Nat :=
  max (max (radius x.1.val) (radius x.2.val))
    (max (radius y.1.val) (radius y.2.val))

private def chartAt (H : Nat) (x : PhysicalSpan width)
    (hx : radius x.val ≤ H) : guardedSpan width H :=
  ⟨encodeChart H x.val, encodeChart_within H x.val hx,
    encodeChart_physical H x.val x.property⟩

private def chartComplex (x y : IntrinsicComplexCarrier width) :
    guardedSpan width (commonHeight width x y) ×
      guardedSpan width (commonHeight width x y) :=
  let H := commonHeight width x y
  (chartAt width H x.1 (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)),
    chartAt width H x.2 (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)))

private def chartComplexRight (x y : IntrinsicComplexCarrier width) :
    guardedSpan width (commonHeight width x y) ×
      guardedSpan width (commonHeight width x y) :=
  let H := commonHeight width x y
  (chartAt width H y.1 (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)),
    chartAt width H y.2 (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)))

private theorem realified_chart
    (x y : IntrinsicComplexCarrier width) :
    Equiv
      (realifiedForm hw0 hw1 width (commonHeight width x y) stage
        (chartComplex width x y) (chartComplexRight width x y))
      (intrinsicRealifiedPairing hw0 hw1 width stage x y) := by
  unfold realifiedForm intrinsicRealifiedPairing chartComplex chartComplexRight chartAt
  exact Equiv_add
    (Equiv.symm (pairing_chart hw0 hw1 width (commonHeight width x y)
      x.1.val y.1.val
      (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _))
      (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) stage))
    (Equiv.symm (pairing_chart hw0 hw1 width (commonHeight width x y)
      x.2.val y.2.val
      (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _))
      (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) stage))

private theorem quarter_chart
    (x y : IntrinsicComplexCarrier width) :
    Equiv
      (quarterTurnForm hw0 hw1 width (commonHeight width x y) stage
        (chartComplex width x y) (chartComplexRight width x y))
      (intrinsicQuarterTurnPairing hw0 hw1 width stage x y) := by
  unfold quarterTurnForm intrinsicQuarterTurnPairing intrinsicRealifiedPairing
  unfold chartComplex chartComplexRight chartAt quarterTurn guardedSmul intrinsicQuarterTurn
  have hc := Equiv_add
    (Equiv.symm (pairing_chart hw0 hw1 width (commonHeight width x y)
      x.1.val (scaleSpan (-1) y.2.val)
      (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _))
      (by rw [radius_scale]; exact Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))
      stage))
    (Equiv.symm (pairing_chart hw0 hw1 width (commonHeight width x y)
      x.2.val y.1.val
      (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _))
      (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) stage))
  simpa only [encodeChart_scale] using hc

private theorem mul_congr {a b c d : CReal} (hab : Equiv a b) (hcd : Equiv c d) :
    Equiv (mul a c) (mul b d) :=
  Equiv.trans (CReal.mul_congr_left hab) (TrigSignedAdd.mul_congr_right hcd)

private theorem quarter_eq_neg_imaginary
    (x y : IntrinsicComplexCarrier width) :
    Equiv (intrinsicQuarterTurnPairing hw0 hw1 width stage x y)
      (neg (intrinsicImaginaryPairing hw0 hw1 width stage x y)) := by
  unfold intrinsicQuarterTurnPairing intrinsicQuarterTurn intrinsicRealifiedPairing
  unfold intrinsicImaginaryPairing
  have hs := pairing_smul_right hw0 hw1 width (-1) x.1.val y.2.val stage
  refine Equiv.trans (Equiv_add hs (Equiv.refl _)) ?_
  apply SumOfSquares.Equiv_of_approx_eqv
  intro n
  exact RingNormaliser.poly_identity_of_normal_eq
    (.add (.mul (.const (-1)) (.var 0)) (.var 1))
    (.neg (.add (.var 0) (.neg (.var 1)))) (by decide)
    (fun | 0 => (pairing hw0 hw1 width x.1.val y.2.val stage).approx n
         | _ => (pairing hw0 hw1 width x.2.val y.1.val stage).approx n)

private theorem quarter_square_eq_imaginary_square
    (x y : IntrinsicComplexCarrier width) :
    Equiv
      (mul (intrinsicQuarterTurnPairing hw0 hw1 width stage x y)
        (intrinsicQuarterTurnPairing hw0 hw1 width stage x y))
      (mul (intrinsicImaginaryPairing hw0 hw1 width stage x y)
        (intrinsicImaginaryPairing hw0 hw1 width stage x y)) := by
  refine Equiv.trans
    (mul_congr (quarter_eq_neg_imaginary hw0 hw1 width stage x y)
      (quarter_eq_neg_imaginary hw0 hw1 width stage x y)) ?_
  apply SumOfSquares.Equiv_of_approx_eqv
  intro n
  exact RingNormaliser.poly_identity_of_normal_eq
    (.mul (.neg (.var 0)) (.neg (.var 0))) (.mul (.var 0) (.var 0))
    (by decide)
    (fun _ => (intrinsicImaginaryPairing hw0 hw1 width stage x y).approx n)

/-- Sharp complex Cauchy--Schwarz for the actual intrinsic physical spans. -/
theorem intrinsicComplex_cauchySchwarz
    (x y : IntrinsicComplexCarrier width) :
    leEv
      (add
        (mul (intrinsicRealifiedPairing hw0 hw1 width stage x y)
          (intrinsicRealifiedPairing hw0 hw1 width stage x y))
        (mul (intrinsicQuarterTurnPairing hw0 hw1 width stage x y)
          (intrinsicQuarterTurnPairing hw0 hw1 width stage x y)))
      (mul (intrinsicRealifiedPairing hw0 hw1 width stage x x)
        (intrinsicRealifiedPairing hw0 hw1 width stage y y)) := by
  let H := commonHeight width x y
  let X := chartComplex width x y
  let Y := chartComplexRight width x y
  have h := formComplex_cauchySchwarz hw0 hw1 width H stage X Y
  have hxy := realified_chart hw0 hw1 width stage x y
  have hj := quarter_chart hw0 hw1 width stage x y
  have hxx : Equiv (realifiedForm hw0 hw1 width H stage X X)
      (intrinsicRealifiedPairing hw0 hw1 width stage x x) := by
    unfold realifiedForm intrinsicRealifiedPairing X chartComplex chartAt H commonHeight
    exact Equiv_add
      (Equiv.symm (pairing_chart hw0 hw1 width _ x.1.val x.1.val
        (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _))
        (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)) stage))
      (Equiv.symm (pairing_chart hw0 hw1 width _ x.2.val x.2.val
        (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _))
        (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)) stage))
  have hyy : Equiv (realifiedForm hw0 hw1 width H stage Y Y)
      (intrinsicRealifiedPairing hw0 hw1 width stage y y) := by
    unfold realifiedForm intrinsicRealifiedPairing Y chartComplexRight chartAt H commonHeight
    exact Equiv_add
      (Equiv.symm (pairing_chart hw0 hw1 width _ y.1.val y.1.val
        (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _))
        (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) stage))
      (Equiv.symm (pairing_chart hw0 hw1 width _ y.2.val y.2.val
        (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))
        (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) stage))
  exact leEv_trans
    (leEv_of_equiv (Equiv.symm (Equiv_add (mul_congr hxy hxy) (mul_congr hj hj))))
    (leEv_trans h (leEv_of_equiv (mul_congr hxx hyy)))

/-- Conventional `(Re²+Im²) ≤ ||x||²||y||²` API for downstream cutoff
and completion transport. -/
theorem pairingComplex_cauchySchwarz
    (x y : IntrinsicComplexCarrier width) :
    leEv
      (add
        (mul (intrinsicRealifiedPairing hw0 hw1 width stage x y)
          (intrinsicRealifiedPairing hw0 hw1 width stage x y))
        (mul (intrinsicImaginaryPairing hw0 hw1 width stage x y)
          (intrinsicImaginaryPairing hw0 hw1 width stage x y)))
      (mul (intrinsicRealifiedPairing hw0 hw1 width stage x x)
        (intrinsicRealifiedPairing hw0 hw1 width stage y y)) := by
  exact leEv_trans
    (leEv_of_equiv (Equiv_add (Equiv.refl _)
      (Equiv.symm (quarter_square_eq_imaginary_square hw0 hw1 width stage x y))))
    (intrinsicComplex_cauchySchwarz hw0 hw1 width stage x y)

end YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicComplexCauchySchwarz

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicComplexCauchySchwarz.intrinsicRealifiedPairing
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicComplexCauchySchwarz.intrinsicQuarterTurn
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicComplexCauchySchwarz.intrinsicComplex_cauchySchwarz
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicComplexCauchySchwarz.pairingComplex_cauchySchwarz
