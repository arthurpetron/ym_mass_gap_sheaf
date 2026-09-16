/-
# Actual centered vectors realize the original joint connected moments

The rational centering streams live in the already constructed joint
completion. Their pairing with the original unit vanishes. Pairing two
such vectors, with the SAME completed physical time acting on the second,
is exactly jointCenteredMoment. No completed real vector action or choice
of a representative is needed for this construction on physical probes.

This identifies original connected correlators with actual completed
vectors. It is fixed-width, fixed-nome SU(2) mathematics, not a continuum
Hilbert/OS reconstruction or a physical Hamiltonian gap.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialJointCenteredStream
import YMGap.Continuum.BF4ExactSlabFixedSpatialJointCenteredForm
import YMGap.Continuum.ArctanTrigConvergesProof

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialJointCenteredPairing

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicSeminorm (PhysicalSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedPhysicalTime
  (unit zero physicalTime physicalTime_zero physicalTime_unit)
open YMGap.Continuum.BF4ExactSlabFixedSpatialChartJointLimits
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointPairingLaws
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointSeminorm
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointPhysicalTime
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointPairingLimit
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointCompletedInner
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointCenteredForm
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointCenterAlgebra
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointCenteredStream

private def crossForm (A B P q r : CReal) : CReal :=
  sub (sub A (mul q B)) (sub (mul r P) (mul q r))

private theorem crossForm_cancel (A B P R : CReal) :
    Equiv (crossForm A B P P R) (sub A (mul P B)) := by
  have hz : Equiv (sub (mul R P) (mul P R)) czero :=
    (Equiv_add (CRealAlg.cmul_comm R P) (Equiv.refl _)).trans
      (sub_self_eqv_zero (mul P R))
  exact (Equiv_add (Equiv.refl _) (neg_congr hz)).trans
    (SumOfSquares.Equiv_of_approx_eqv (fun n =>
      Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left _ _ _ (by decide : Q'.eqv (-(0 : Q')) 0))
        (QPoly.q_add_zero_eqv _)))

private theorem crossForm_converges {qs rs : Nat → CReal} {P R : CReal}
    (hq : ConvergesTo qs P) (hr : ConvergesTo rs R) (A B : CReal) :
    ConvergesTo (fun k => crossForm A B P (qs k) (rs k)) (sub A (mul P B)) := by
  have hc : ConvergesTo (fun k => crossForm A B P (qs k) (rs k))
      (crossForm A B P P R) :=
    TrigAddCReal.convergesTo_add
      (TrigAddCReal.convergesTo_add (convergesTo_const A)
        (TrigAddCReal.convergesTo_neg
          (Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz.CReal.convergesTo_mul_general
            hq (convergesTo_const B))))
      (TrigAddCReal.convergesTo_neg
        (TrigAddCReal.convergesTo_add
          (Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz.CReal.convergesTo_mul_general
            hr (convergesTo_const P))
          (TrigAddCReal.convergesTo_neg
            (Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz.CReal.convergesTo_mul_general hq hr))))
  exact ArctanTrigConvergesProof.convergesTo_of_equiv hc (crossForm_cancel A B P R)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (width : Nat)

local notation "D" => jointSeminorm hw0 hw1 width
local notation "J" => jointPairing hw0 hw1 width
local notation "B" => completedInner hw0 hw1 width
local notation "C" => centeredStream hw0 hw1 width
local notation "v" => centeredVector hw0 hw1 width

attribute [local irreducible] jointPairing

/-- The explicit mean approximations converge to that SAME unit coefficient. -/
theorem centered_unit_representative (x : PhysicalSpan width) :
    Equiv (representativeInner hw0 hw1 width (C x) ((D).constant (unit width))) czero := by
  have hc : ConvergesTo
      (fun k => sub (mean hw0 hw1 width x) (ofQ' ((mean hw0 hw1 width x).approx k)))
      (sub (mean hw0 hw1 width x) (mean hw0 hw1 width x)) :=
    TrigAddCReal.convergesTo_add (convergesTo_const _)
      (TrigAddCReal.convergesTo_neg (mean_approximations_converge hw0 hw1 width x))
  exact (Equiv_of_limit_of_equal
    (fun k => centerApprox_unit hw0 hw1 width x ((mean hw0 hw1 width x).approx k))
    (pairSequence_converges hw0 hw1 width (C x) ((D).constant (unit width))) hc).trans
      (sub_self_eqv_zero _)

theorem centeredVector_orthogonal (x : PhysicalSpan width) :
    B (v x) (jointCompletedUnit hw0 hw1 width) = RCzero :=
  Quotient.sound (centered_unit_representative hw0 hw1 width x)

private theorem unit_time_pairing (n : Nat) (y : PhysicalSpan width) :
    Equiv (J (unit width) (physicalTime n y)) (J (unit width) y) := by
  simpa only [physicalTime_unit] using
    (jointPairing_time_balance hw0 hw1 width n (unit width) y).symm

/-- Original centering, physical time and scalar limit all use the same
presentations; in particular no fixed-cutoff carrier is substituted. -/
theorem centered_time_representative (n : Nat) (x y : PhysicalSpan width) :
    Equiv (representativeInner hw0 hw1 width (C x)
      ((jointTimeNonexpansive hw0 hw1 width n).mapCauchy (C y)))
      (jointCenteredMoment hw0 hw1 width n x y) := by
  let P := mean hw0 hw1 width x
  let R := mean hw0 hw1 width y
  have hc := crossForm_converges
    (mean_approximations_converge hw0 hw1 width x)
    (mean_approximations_converge hw0 hw1 width y)
    (J x (physicalTime n y)) (J (unit width) (physicalTime n y))
  have h := Equiv_of_limit_of_equal
    (aSeq := pairSequence hw0 hw1 width (C x)
      ((jointTimeNonexpansive hw0 hw1 width n).mapCauchy (C y)))
    (bSeq := fun k => crossForm (J x (physicalTime n y))
      (J (unit width) (physicalTime n y)) P (ofQ' (P.approx k)) (ofQ' (R.approx k)))
    (fun k => by
      change Equiv (J (centerApprox x (P.approx k))
        (physicalTime n (centerApprox y (R.approx k)))) _
      rw [physicalTime_centerApprox]
      exact (centerApprox_pairing hw0 hw1 width x (physicalTime n y)
        (P.approx k) (R.approx k)).trans
          (SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.eqv_refl _)))
    (pairSequence_converges hw0 hw1 width (C x)
      ((jointTimeNonexpansive hw0 hw1 width n).mapCauchy (C y))) hc
  exact h.trans (Equiv_add (Equiv.refl _) (neg_congr
    (TrigSignedAdd.mul_congr_right (unit_time_pairing hw0 hw1 width n y))))

/-- The completed correlation is EXACTLY the original connected moment. -/
theorem centeredVector_time_pairing (n : Nat) (x y : PhysicalSpan width) :
    B (v x) (jointCompletedTime hw0 hw1 width n (v y)) =
      Quotient.mk crealSetoid (jointCenteredMoment hw0 hw1 width n x y) :=
  Quotient.sound (centered_time_representative hw0 hw1 width n x y)

theorem centeredVector_pairing (x y : PhysicalSpan width) :
    B (v x) (v y) = Quotient.mk crealSetoid (jointCenteredMoment hw0 hw1 width 0 x y) := by
  simpa only [jointCompletedTime_zero] using centeredVector_time_pairing hw0 hw1 width 0 x y

theorem jointCompletedZero_norm :
    B (jointEmbedSpan hw0 hw1 width (zero width))
      (jointEmbedSpan hw0 hw1 width (zero width)) = RCzero := by
  rw [completedInner_embedSpan]
  exact Quotient.sound (jointDistSq_refl hw0 hw1 width (zero width))

end YMGap.Continuum.BF4ExactSlabFixedSpatialJointCenteredPairing

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointCenteredPairing.centered_unit_representative
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointCenteredPairing.centeredVector_orthogonal
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointCenteredPairing.centered_time_representative
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointCenteredPairing.centeredVector_time_pairing
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointCenteredPairing.centeredVector_pairing
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointCenteredPairing.jointCompletedZero_norm
