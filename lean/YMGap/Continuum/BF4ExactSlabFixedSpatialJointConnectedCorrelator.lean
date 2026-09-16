/-
# The cutoff-removed centered form is an original connected finite limit

At every raw diagonal index s, the joint expectation and both unit
marginals use identical cutoff s, boundary depth s, common chart H,
selected action and partition. Constructed QCauchy data for the three
chart diagonals give QCauchy data for their literal connected difference.
The limit equals the joint centered physical moment already bounded in
JointCenteredForm. Equality is at the scalar limit, not a claim that the
three separately regularized jointPairing approximants share a chart.

Physical lag is held fixed while cutoff and boundary depth recede.
Width and nome stay fixed. This does not construct a cutoff-removed
completed carrier, identify old cutoff-dependent carriers, or provide
spatial/spacing-uniform control.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialJointCenteredForm

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialJointConnectedCorrelator

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicSeminorm (PhysicalSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicReflectedForm
open YMGap.Continuum.BF4ExactSlabFixedSpatialPhysicalTimeContraction (pairing_unit_invariant)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPhysicalTimeShift (radius_advance_le)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPhysicalCovariance
  (connectedScalar_abs_le separationCap)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferMixingRate (mixRate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedPhysicalTime (physicalTime unit)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCommonChartCorrelator (chartScalar)
open YMGap.Continuum.BF4ExactSlabFixedSpatialChartJointCauchy
open YMGap.Continuum.BF4ExactSlabFixedSpatialChartJointLimits
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointCenteredForm
open YMGap.Continuum.BF4ExactSlabFixedSpatialOriginalConnectedCorrelator (connectedScalar)
open YMGap.Continuum.BF4ExactSlabPlaquetteRealScalarAlgebra
  (scalarAddCauchy scalarNegCauchy scalarMulCauchy)

private def rawReal (r : Nat → Q') (c : QCauchy r) : CReal where
  approx := r
  cauchy := fun epsilon he => ⟨c.M epsilon, c.bound epsilon he⟩

private def connectedStreamCauchy (a b c : Nat → Q')
    (ha : QCauchy a) (hb : QCauchy b) (hc : QCauchy c) :
    QCauchy (fun s => a s + -(b s*c s)) :=
  let A := rawReal a ha
  let B := rawReal b hb
  let C := rawReal c hc
  scalarAddCauchy A (neg (mul B C)) ha
    (scalarNegCauchy (mul B C) (scalarMulCauchy B C hb hc))

private theorem connectedStream_converges {a b c : Nat → Q'} {A B C : CReal}
    (ha : ConvergesTo (fun s => ofQ' (a s)) A)
    (hb : ConvergesTo (fun s => ofQ' (b s)) B)
    (hc : ConvergesTo (fun s => ofQ' (c s)) C) :
    ConvergesTo (fun s => ofQ' (a s + -(b s*c s))) (sub A (mul B C)) := by
  have h := TrigAddCReal.convergesTo_add ha
    (TrigAddCReal.convergesTo_neg
      (Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz.CReal.convergesTo_mul_general
        hb hc))
  exact TrigAddCReal.convergesTo_congr_seq
    (fun _ => SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.eqv_refl _)) h

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (width : Nat)

/-- The fixed unit's right coefficient stays invariant after cutoff removal. -/
theorem jointPairing_unit_time (n : Nat) (y : PhysicalSpan width) :
    Equiv (jointPairing hw0 hw1 width (unit width) (physicalTime n y))
      (jointPairing hw0 hw1 width (unit width) y) := by
  apply Equiv_of_limit_of_equal (aSeq := fun stage =>
    pairing hw0 hw1 width (unit width).val (physicalTime n y).val stage)
    (bSeq := fun stage => pairing hw0 hw1 width (unit width).val y.val stage)
  · intro stage
    exact Equiv.trans
      (pairing_symm hw0 hw1 width (unit width).val (physicalTime n y).val
        (unit width).property (physicalTime n y).property stage)
      (Equiv.trans (pairing_unit_invariant hw0 hw1 width n y.val y.property stage)
        (pairing_symm hw0 hw1 width y.val (unit width).val
          y.property (unit width).property stage))
  · exact pairing_converges_jointPairing hw0 hw1 width (unit width) (physicalTime n y)
  · exact pairing_converges_jointPairing hw0 hw1 width (unit width) y

variable (H : Nat) (x y : PhysicalSpan width)
  (hx : radius x.val ≤ H) (hy : radius y.val ≤ H)

/-- The original connected scalar with cutoff and boundary index both s.
No independently minimized chart or approximation index occurs here. -/
def jointConnectedCauchy :
    QCauchy (fun s => connectedScalar hw0 hw1 width s H x y s) :=
  connectedStreamCauchy _ _ _
    (chartJointCauchy hw0 hw1 width H x y hx hy)
    (chartJointCauchy hw0 hw1 width H x (unit width) hx (Nat.zero_le H))
    (chartJointCauchy hw0 hw1 width H (unit width) y (Nat.zero_le H) hy)

def jointConnectedLimit : CReal :=
  ofQ'CauchySeq (fun s => connectedScalar hw0 hw1 width s H x y s)
    (jointConnectedCauchy hw0 hw1 width H x y hx hy)

theorem jointConnected_diagonal_converges :
    ConvergesTo (fun s => ofQ' (connectedScalar hw0 hw1 width s H x y s))
      (jointConnectedLimit hw0 hw1 width H x y hx hy) :=
  convergesTo_ofQ'CauchySeq _ (jointConnectedCauchy hw0 hw1 width H x y hx hy)

/-- Each of the three common-chart limits is identified with the canonical
pairing only after taking its own proved limit. -/
theorem jointConnectedLimit_pin :
    Equiv (jointConnectedLimit hw0 hw1 width H x y hx hy)
      (sub (jointPairing hw0 hw1 width x y)
        (mul (jointPairing hw0 hw1 width x (unit width))
          (jointPairing hw0 hw1 width (unit width) y))) := by
  have hxy := convergesTo_limit_congr
    (chartJoint_diagonal_converges hw0 hw1 width H x y hx hy)
    (jointPairing_chart hw0 hw1 width H x y hx hy).symm
  have hxu := convergesTo_limit_congr
    (chartJoint_diagonal_converges hw0 hw1 width H x (unit width) hx (Nat.zero_le H))
    (jointPairing_chart hw0 hw1 width H x (unit width) hx (Nat.zero_le H)).symm
  have huy := convergesTo_limit_congr
    (chartJoint_diagonal_converges hw0 hw1 width H (unit width) y (Nat.zero_le H) hy)
    (jointPairing_chart hw0 hw1 width H (unit width) y (Nat.zero_le H) hy).symm
  exact Equiv_of_limit_of_equal
    (fun s => Equiv.refl (ofQ' (connectedScalar hw0 hw1 width s H x y s)))
    (jointConnected_diagonal_converges hw0 hw1 width H x y hx hy)
    (connectedStream_converges hxy hxu huy)

/-- Physical lag n and receding cutoff/boundary indices remain distinct.
This is the SAME finite connected family realizing the strict scalar form. -/
theorem jointConnectedLimit_physical_pin (n : Nat)
    (hyTime : radius (physicalTime n y).val ≤ H) :
    Equiv (jointConnectedLimit hw0 hw1 width H x (physicalTime n y) hx hyTime)
      (jointCenteredMoment hw0 hw1 width n x y) :=
  Equiv.trans (jointConnectedLimit_pin hw0 hw1 width H x (physicalTime n y) hx hyTime)
    (Equiv_add (Equiv.refl _)
      (neg_congr (TrigSignedAdd.mul_congr_right (jointPairing_unit_time hw0 hw1 width n y))))

/-- Both sides of the geometric envelope survive the joint passage, using
the literal original finite connected scalar at each regularized diagonal
index. The prefactor depends on x,y but not physical lag or retained stage. -/
theorem jointCenteredMoment_bounds (n : Nat) :
    let E := separationCap width x.val y.val * mixRate hw0 hw1 width ^ n
    leEv (ofQ' (-E)) (jointCenteredMoment hw0 hw1 width n x y) ∧
      leEv (jointCenteredMoment hw0 hw1 width n x y) (ofQ' E) := by
  let R := max (radius x.val) (radius y.val)
  have hxR : radius x.val ≤ R := Nat.le_max_left _ _
  have hyR : radius y.val ≤ R := Nat.le_max_right _ _
  have hxH : radius x.val ≤ R+n := Nat.le_trans hxR (Nat.le_add_right _ _)
  have hyH : radius (physicalTime n y).val ≤ R+n :=
    Nat.le_trans (radius_advance_le n y.val) (Nat.add_le_add_right hyR n)
  let Z := jointConnectedLimit hw0 hw1 width (R+n) x (physicalTime n y) hxH hyH
  have hp : Equiv Z (jointCenteredMoment hw0 hw1 width n x y) :=
    jointConnectedLimit_physical_pin hw0 hw1 width (R+n) x y hxH n hyH
  have hlo : leEv (ofQ' (-(separationCap width x.val y.val * mixRate hw0 hw1 width ^ n))) Z := by
    apply leEv_ofQ'_of_approx_ge
    intro k
    simp only [Z, jointConnectedLimit, ofQ'CauchySeq_approx]
    exact Q'.le_trans' _ _ _
      (Q'.neg_le_neg (connectedScalar_abs_le hw0 hw1 width _ R n x y hxR hyR _))
      (ExpNeg.neg_abs_le _)
  have hhi : leEv Z (ofQ' (separationCap width x.val y.val * mixRate hw0 hw1 width ^ n)) := by
    apply leEv_le_ofQ'_of_approx_le
    intro k
    simp only [Z, jointConnectedLimit, ofQ'CauchySeq_approx]
    exact Q'.le_trans' _ _ _ (Q'.le_abs_self _)
      (connectedScalar_abs_le hw0 hw1 width _ R n x y hxR hyR _)
  exact ⟨leEv_trans hlo (leEv_of_equiv hp), leEv_trans (leEv_of_equiv hp.symm) hhi⟩

end YMGap.Continuum.BF4ExactSlabFixedSpatialJointConnectedCorrelator

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointConnectedCorrelator.jointPairing_unit_time
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointConnectedCorrelator.jointConnectedCauchy
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointConnectedCorrelator.jointConnectedLimit
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointConnectedCorrelator.jointConnected_diagonal_converges
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointConnectedCorrelator.jointConnectedLimit_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointConnectedCorrelator.jointConnectedLimit_physical_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointConnectedCorrelator.jointCenteredMoment_bounds
