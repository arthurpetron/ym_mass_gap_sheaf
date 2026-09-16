/-
# Connected physical correlators with ONE original finite partition

The joint expectation and both unit-inserted marginals use the same explicit
chart H, boundary depth t, ambient extent, selected chain action and cutoff.
Their literal connected rational stream has constructed QCauchy data.
Its limit is exactly the original completed centered pairing; advancing the
second presentation pins the actual centered physical-time correlator.

The finite boundary depth is not the physical lag. Nothing here bounds
decay in that lag, supplies a strict gap, exchanges cutoff/time limits,
or proves a full Hilbert/continuum theory. All lattice parameters stay fixed.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialCommonChartCorrelator
import YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredPhysicalTime
import YMGap.Continuum.BF4ExactSlabPlaquetteRealScalarAlgebra

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialOriginalConnectedCorrelator

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicReflectedForm
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicSeminorm (PhysicalSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedPhysicalTime
open YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedInner
open YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredCompletion
open YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredPhysicalTime
open YMGap.Continuum.BF4ExactSlabFixedSpatialCommonChartCorrelator
open YMGap.Continuum.BF4ExactSlabPlaquetteRealScalarAlgebra
  (scalarAddCauchy scalarNegCauchy scalarMulCauchy)

/-- The supplied modulus remains available separately; this helper only
allows reuse of generic scalar arithmetic without reindexing the raw stream. -/
private def rawReal (r : Nat → Q') (c : QCauchy r) : CReal where
  approx := r
  cauchy := fun epsilon he => ⟨c.M epsilon, c.bound epsilon he⟩

private def connectedStreamCauchy (a b c : Nat → Q')
    (ha : QCauchy a) (hb : QCauchy b) (hc : QCauchy c) :
    QCauchy (fun t => a t + -(b t*c t)) :=
  let A := rawReal a ha
  let B := rawReal b hb
  let C := rawReal c hc
  let hBC := scalarMulCauchy B C hb hc
  scalarAddCauchy A (CReal.neg (CReal.mul B C)) ha
    (scalarNegCauchy (CReal.mul B C) hBC)

private theorem connectedStream_converges {a b c : Nat → Q'} {A B C : CReal}
    (ha : ConvergesTo (fun t => ofQ' (a t)) A)
    (hb : ConvergesTo (fun t => ofQ' (b t)) B)
    (hc : ConvergesTo (fun t => ofQ' (c t)) C) :
    ConvergesTo (fun t => ofQ' (a t + -(b t*c t))) (CReal.sub A (CReal.mul B C)) := by
  have hp : ConvergesTo (fun t => CReal.mul (ofQ' (b t)) (ofQ' (c t))) (CReal.mul B C) :=
    Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz.CReal.convergesTo_mul_general hb hc
  have hs : ConvergesTo
      (fun t => CReal.add (ofQ' (a t)) (CReal.neg (CReal.mul (ofQ' (b t)) (ofQ' (c t)))))
      (CReal.sub A (CReal.mul B C)) :=
    TrigAddCReal.convergesTo_add ha (TrigAddCReal.convergesTo_neg hp)
  exact TrigAddCReal.convergesTo_congr_seq
    (fun _ => SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.eqv_refl _)) hs

attribute [local irreducible] chartScalar

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (width stage : Nat)

/-- Each occurrence of chartScalar uses the SAME H and t, hence the SAME
finite action and partition. No independently minimized charts are used. -/
def connectedScalar (H : Nat) (x y : PhysicalSpan width) (t : Nat) : Q' :=
  chartScalar hw0 hw1 width stage H x y t +
    -(chartScalar hw0 hw1 width stage H x (unit width) t *
      chartScalar hw0 hw1 width stage H (unit width) y t)

private theorem unit_radius_le (H : Nat) : radius (unit width).val ≤ H := Nat.zero_le H

def connectedCauchy (H : Nat) (x y : PhysicalSpan width)
    (hx : radius x.val ≤ H) (hy : radius y.val ≤ H) :
    QCauchy (connectedScalar hw0 hw1 width stage H x y) :=
  connectedStreamCauchy _ _ _
    (chartCauchy hw0 hw1 width stage H x y hx hy)
    (chartCauchy hw0 hw1 width stage H x (unit width) hx (unit_radius_le width H))
    (chartCauchy hw0 hw1 width stage H (unit width) y (unit_radius_le width H) hy)

def connectedLimit (H : Nat) (x y : PhysicalSpan width)
    (hx : radius x.val ≤ H) (hy : radius y.val ≤ H) : CReal :=
  ofQ'CauchySeq (connectedScalar hw0 hw1 width stage H x y)
    (connectedCauchy hw0 hw1 width stage H x y hx hy)

theorem connectedScalar_converges (H : Nat) (x y : PhysicalSpan width)
    (hx : radius x.val ≤ H) (hy : radius y.val ≤ H) :
    ConvergesTo (fun t => ofQ' (connectedScalar hw0 hw1 width stage H x y t))
      (CReal.sub (pairing hw0 hw1 width x.val y.val stage)
        (CReal.mul (pairing hw0 hw1 width x.val (unit width).val stage)
          (pairing hw0 hw1 width (unit width).val y.val stage))) := by
  have hxy := chartScalar_converges hw0 hw1 width stage H x y hx hy
  have hxu := chartScalar_converges hw0 hw1 width stage H x (unit width) hx (unit_radius_le width H)
  have huy := chartScalar_converges hw0 hw1 width stage H (unit width) y (unit_radius_le width H) hy
  unfold connectedScalar
  exact connectedStream_converges hxy hxu huy

theorem connectedLimit_pin (H : Nat) (x y : PhysicalSpan width)
    (hx : radius x.val ≤ H) (hy : radius y.val ≤ H) :
    Equiv (connectedLimit hw0 hw1 width stage H x y hx hy)
      (CReal.sub (pairing hw0 hw1 width x.val y.val stage)
        (CReal.mul (pairing hw0 hw1 width x.val (unit width).val stage)
          (pairing hw0 hw1 width (unit width).val y.val stage))) :=
  Equiv_of_limit_of_equal (fun t => Equiv.refl (ofQ' (connectedScalar hw0 hw1 width stage H x y t)))
    (convergesTo_ofQ'CauchySeq _ (connectedCauchy hw0 hw1 width stage H x y hx hy))
    (connectedScalar_converges hw0 hw1 width stage H x y hx hy)

/-- Actual centering equals the constructed connected limit of one finite
action family, with a common chart and no interchanged limits. -/
theorem centered_originalCorrelator (H : Nat) (x y : PhysicalSpan width)
    (hx : radius x.val ≤ H) (hy : radius y.val ≤ H) :
    completedInner hw0 hw1 width stage
        (center hw0 hw1 width stage (embedSpan hw0 hw1 width stage x))
        (center hw0 hw1 width stage (embedSpan hw0 hw1 width stage y)) =
      Quotient.mk crealSetoid (connectedLimit hw0 hw1 width stage H x y hx hy) := by
  rw [centered_inner_embedSpan]
  exact Quotient.sound (Equiv.symm (connectedLimit_pin hw0 hw1 width stage H x y hx hy))

/-- Physical lag n is kept separate from the receding finite boundary t.
All three connected finite moments use the chart containing x and T_n y. -/
theorem centeredTime_originalCorrelator (n H : Nat) (x y : PhysicalSpan width)
    (hx : radius x.val ≤ H) (hy : radius (physicalTime n y).val ≤ H) :
    completedInner hw0 hw1 width stage
        (center hw0 hw1 width stage (embedSpan hw0 hw1 width stage x))
        (completedTime hw0 hw1 width stage n
          (center hw0 hw1 width stage (embedSpan hw0 hw1 width stage y))) =
      Quotient.mk crealSetoid
        (connectedLimit hw0 hw1 width stage H x (physicalTime n y) hx hy) := by
  rw [completedTime_center, completedTime_embedSpan]
  exact centered_originalCorrelator hw0 hw1 width stage H x (physicalTime n y) hx hy

end YMGap.Continuum.BF4ExactSlabFixedSpatialOriginalConnectedCorrelator

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialOriginalConnectedCorrelator.connectedScalar
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialOriginalConnectedCorrelator.connectedCauchy
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialOriginalConnectedCorrelator.connectedLimit
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialOriginalConnectedCorrelator.connectedScalar_converges
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialOriginalConnectedCorrelator.connectedLimit_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialOriginalConnectedCorrelator.centered_originalCorrelator
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialOriginalConnectedCorrelator.centeredTime_originalCorrelator
