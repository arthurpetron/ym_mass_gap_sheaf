/-
# Cutoff-removed centered physical moments at fixed spatial width

The three actual joint chart-pairing limits supply explicit QCauchy data
for their centered difference. Continuity of their scalar arithmetic
identifies this value with the cutoff limit of the already constructed
fixed-cutoff centered physical moments. Their physical covariance bound,
even-time positivity and prefactor-free two-step bound therefore pass to
the SAME scalar limit.

Nome, spatial width and lattice spacing remain fixed. The physical lag
is distinct from the receding boundary index. The comparison rate retains
its nome and width dependence. This file constructs no cutoff-removed
completed carrier and does not identify the different fixed-cutoff
seminorm completions. No continuum or Hamiltonian-gap claim is made.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialChartJointLimits
import YMGap.Continuum.BF4ExactSlabFixedSpatialDenseCenteredGap
import YMGap.Continuum.BF4ExactSlabPlaquetteRealScalarAlgebra

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialJointCenteredForm

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicSeminorm (PhysicalSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedPhysicalTime (physicalTime unit)
open YMGap.Continuum.BF4ExactSlabFixedSpatialChartJointLimits
open YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredMoments
open YMGap.Continuum.BF4ExactSlabFixedSpatialPhysicalCovariance
  (separationCap centeredMoment_le)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferMixingRate (mixRate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDenseCenteredGap
  (twoStepRate evenMoment_first_le)
open YMGap.Continuum.BF4ExactSlabPlaquetteRealScalarAlgebra
  (scalarAddCauchy scalarNegCauchy scalarMulCauchy)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (width : Nat)

/-- The centered joint limit of the actual physical lag n. The two unit
coefficients are the same unshifted coefficients as in centeredMoment. -/
def jointCenteredMoment (n : Nat) (x y : PhysicalSpan width) : CReal :=
  sub (jointPairing hw0 hw1 width x (physicalTime n y))
    (mul (jointPairing hw0 hw1 width x (unit width))
      (jointPairing hw0 hw1 width (unit width) y))

/-- All three scalar approximation moduli are supplied by the actual joint
limits. Product ceilings are computed from these moduli, not postulated to
be uniform across the old heat-cutoff family. -/
def jointCenteredMomentCauchy (n : Nat) (x y : PhysicalSpan width) :
    QCauchy (jointCenteredMoment hw0 hw1 width n x y).approx :=
  let A := jointPairing hw0 hw1 width x (physicalTime n y)
  let B := jointPairing hw0 hw1 width x (unit width)
  let C := jointPairing hw0 hw1 width (unit width) y
  let cA := jointPairingCauchy hw0 hw1 width x (physicalTime n y)
  let cB := jointPairingCauchy hw0 hw1 width x (unit width)
  let cC := jointPairingCauchy hw0 hw1 width (unit width) y
  scalarAddCauchy A (neg (mul B C)) cA
    (scalarNegCauchy (mul B C) (scalarMulCauchy B C cB cC))

/-- Cutoff convergence is obtained from the SAME three joint pairing
limits; no multiplication modulus is extracted from a legacy Prop field. -/
theorem centeredMoment_converges_joint (n : Nat) (x y : PhysicalSpan width) :
    ConvergesTo (fun stage => centeredMoment hw0 hw1 width stage n x y)
      (jointCenteredMoment hw0 hw1 width n x y) := by
  have htime := pairing_converges_jointPairing hw0 hw1 width x (physicalTime n y)
  have hleft := pairing_converges_jointPairing hw0 hw1 width x (unit width)
  have hright := pairing_converges_jointPairing hw0 hw1 width (unit width) y
  exact TrigAddCReal.convergesTo_add htime
    (TrigAddCReal.convergesTo_neg
      (Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz.CReal.convergesTo_mul_general
        hleft hright))

/-- The actual physical covariance envelope survives heat-cutoff removal.
Its presentation prefactor is independent of lag, not of the observable. -/
theorem jointCenteredMoment_le (n : Nat) (x y : PhysicalSpan width) :
    leEv (jointCenteredMoment hw0 hw1 width n x y)
      (ofQ' (separationCap width x.val y.val * mixRate hw0 hw1 width ^ n)) :=
  leEv_of_convergesTo_le
    (centeredMoment_converges_joint hw0 hw1 width n x y)
    (convergesTo_const
      (ofQ' (separationCap width x.val y.val * mixRate hw0 hw1 width ^ n)))
    (fun stage => centeredMoment_le hw0 hw1 width stage n x y)

/-- Positivity retains the genuine even-time restriction supplied by site
reflection. No positivity assertion for one physical time step is added. -/
theorem jointEvenMoment_nonnegative (x : PhysicalSpan width) (k : Nat) :
    leEv czero (jointCenteredMoment hw0 hw1 width (2*k) x x) :=
  leEv_of_convergesTo_le (convergesTo_const czero)
    (centeredMoment_converges_joint hw0 hw1 width (2*k) x x)
    (fun stage => evenMoment_nonnegative hw0 hw1 width stage x k)

theorem jointEvenMoment_le_zero (x : PhysicalSpan width) (k : Nat) :
    leEv (jointCenteredMoment hw0 hw1 width (2*k) x x)
      (jointCenteredMoment hw0 hw1 width 0 x x) :=
  leEv_of_convergesTo_le
    (centeredMoment_converges_joint hw0 hw1 width (2*k) x x)
    (centeredMoment_converges_joint hw0 hw1 width 0 x x)
    (fun stage => evenMoment_le_zero hw0 hw1 width stage x k)

/-- The prefactor-free strict two-step scalar form inequality passes through
the actual cutoff limit. Its rate is the same q^2, including q=0. This is a
statement about dense physical presentations, not a new completed operator. -/
theorem joint_twoStep_form_gap (x : PhysicalSpan width) :
    leEv (jointCenteredMoment hw0 hw1 width 2 x x)
      (mul (ofQ' (twoStepRate hw0 hw1 width))
        (jointCenteredMoment hw0 hw1 width 0 x x)) :=
  leEv_of_convergesTo_le
    (centeredMoment_converges_joint hw0 hw1 width 2 x x)
    (convergesTo_const_mul (ofQ' (twoStepRate hw0 hw1 width))
      (centeredMoment_converges_joint hw0 hw1 width 0 x x))
    (fun stage => evenMoment_first_le hw0 hw1 width stage x)

/-- The actual dyadic Cauchy--Schwarz moment inequality also survives the
cutoff limit, with the same physical-time indices and centered diagonal. -/
theorem jointEvenMoment_dyadic (x : PhysicalSpan width) (k : Nat) :
    leEv
      (mul (jointCenteredMoment hw0 hw1 width (2*k) x x)
        (jointCenteredMoment hw0 hw1 width (2*k) x x))
      (mul (jointCenteredMoment hw0 hw1 width (2*(k+k)) x x)
        (jointCenteredMoment hw0 hw1 width 0 x x)) :=
  leEv_of_convergesTo_le
    (Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz.CReal.convergesTo_mul_general
      (centeredMoment_converges_joint hw0 hw1 width (2*k) x x)
      (centeredMoment_converges_joint hw0 hw1 width (2*k) x x))
    (Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz.CReal.convergesTo_mul_general
      (centeredMoment_converges_joint hw0 hw1 width (2*(k+k)) x x)
      (centeredMoment_converges_joint hw0 hw1 width 0 x x))
    (fun stage => evenMoment_dyadic hw0 hw1 width stage x k)

end YMGap.Continuum.BF4ExactSlabFixedSpatialJointCenteredForm

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointCenteredForm.jointCenteredMoment
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointCenteredForm.jointCenteredMomentCauchy
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointCenteredForm.centeredMoment_converges_joint
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointCenteredForm.jointCenteredMoment_le
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointCenteredForm.jointEvenMoment_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointCenteredForm.jointEvenMoment_le_zero
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointCenteredForm.joint_twoStep_form_gap
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointCenteredForm.jointEvenMoment_dyadic
