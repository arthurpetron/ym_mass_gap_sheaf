/-
M4f -- inverse-square physical spacing along the proved AF trajectory.

The AF recurrence already yields a fixed-offset bound

    tau_j^2 <= R^2 / (j+2)^2.

Composing it with the independent physical spacing envelope

    a(tau_j) Lambda <= C tau_j^2

produces a genuine inverse-square majorant for the BF4 physical spacing.  The
constant records both the AF offset inflation and the physical conversion
factor; no asymptotic notation is used.
-/

import YMGap.Continuum.BF4AFPhysicalSpacingToZero
import YMGap.Continuum.QuadraticRateErrorTailControl
import YMGap.Continuum.SummabilityCapstone

namespace YMGap.Continuum.BF4AFPhysicalSpacingInverseSquare

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.AFTrajectoryCertificate
open YMGap.Continuum.AFRateCalibration
open YMGap.Continuum.BF4AFPhysicalSpacingToZero
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.ContinuumGapModulus
open YMGap.Continuum.QuadraticRateErrorTailControl
open YMGap.Continuum.SummabilityCapstone
open YMGap.Continuum.SummableInverseSquare

/-- The explicit coefficient in the AF inverse-square physical-spacing
majorant. -/
def physicalSpacingCoefficient
    {g₁ : Q'} (E : PhysicalSpacingEnvelope g₁)
    (C : AFTrajectoryCertificate) : Q' :=
  Q'.divPos
    (E.C *
      (rateScaled (afRateModulus_of_AFCertificate C) *
        rateScaled (afRateModulus_of_AFCertificate C)))
    E.Λ E.Λ_pos

theorem physicalSpacingCoefficient_nonnegative
    {g₁ : Q'} (E : PhysicalSpacingEnvelope g₁)
    (C : AFTrajectoryCertificate) :
    (0 : Q') <= physicalSpacingCoefficient E C := by
  unfold physicalSpacingCoefficient Q'.divPos
  exact Q'.mul_nonneg _ _
    (Q'.mul_nonneg _ _ (Q'.le_of_lt E.C_pos)
      (Q'.mul_nonneg _ _
        (rateScaled_nonneg (afRateModulus_of_AFCertificate C))
        (rateScaled_nonneg (afRateModulus_of_AFCertificate C))))
    (Q'.le_of_lt (Q'.recipPos_pos E.Λ E.Λ_pos))

/-- Moving the fixed physical denominator through the inverse-square factor. -/
private theorem physical_quotient_eqv
    (numerator inverseSquare denominator : Q')
    (hdenominator : (0 : Q') < denominator) :
    (Q'.divPos (numerator * inverseSquare) denominator hdenominator).eqv
      (Q'.divPos numerator denominator hdenominator * inverseSquare) := by
  unfold Q'.divPos
  show _ * (_ : Int) = _ * (_ : Int)
  simp only [Q'.mul_num_cast, Q'.mul_den_cast]
  ac_rfl

/-- The identified AF coupling is dominated by the fixed-offset rate used by
the constructive inverse-square summability endpoint. -/
theorem coupling_le_fixedRate
    (C : AFTrajectoryCertificate) (coupling : Nat -> Q')
    (H : ShiftedAFTrajectoryIdentification C coupling) (k : Nat) :
    coupling k <=
      Q'.divPos
        (rateScaled (afRateModulus_of_AFCertificate C))
        (harmDen2 k) (harmDen2_pos k) := by
  let afr := afRateModulus_of_AFCertificate C
  have hrate := margin_le_scaled afr k
  have heqv : (afSchedule C k).eqv ((1 : Q') - afr.w k) := by
    dsimp [afSchedule, afr, afRateModulus_of_AFCertificate]
    exact Q'.eqv_symm
      (AFRateCalibration.one_sub_one_sub_eqv (C.τ (C.k0 + k)))
  rw [H.coupling_eq k]
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv heqv) hrate

/-- The physical spacing evaluated on an identified AF trajectory has an
explicit global inverse-square majorant. -/
def spacingInverseSquareTailOfAFTrajectory
    {g₁ : Q'} (E : PhysicalSpacingEnvelope g₁)
    (coupling : Nat -> Q')
    (coupling_pos : forall j, (0 : Q') < coupling j)
    (coupling_le_window : forall j, coupling j <= g₁)
    (C : AFTrajectoryCertificate)
    (H : ShiftedAFTrajectoryIdentification C coupling) :
    InverseSquareSpacingTail
      (physicalSpacingOfEnvelope E coupling coupling_pos coupling_le_window) 0 where
  coefficient := physicalSpacingCoefficient E C
  coefficient_nonnegative := physicalSpacingCoefficient_nonnegative E C
  spacing_le := by
    intro k
    let afr := afRateModulus_of_AFCertificate C
    let r := Q'.divPos (rateScaled afr) (harmDen2 k) (harmDen2_pos k)
    have hcoupling : coupling k <= r := coupling_le_fixedRate C coupling H k
    have hcoupling0 : (0 : Q') <= coupling k := Q'.le_of_lt (coupling_pos k)
    have hrateScaledPos : (0 : Q') < rateScaled afr := by
      unfold rateScaled
      exact Q'.mul_pos
        (InverseSquareAntitoneTailControl.ofNat_pos
          (Nat.lt_of_lt_of_le (by decide) (inflM_ge_one afr)))
        afr.A_pos
    have hr0 : (0 : Q') <= r :=
      Q'.le_of_lt (Q'.divPos_pos _ _ (harmDen2_pos k)
        hrateScaledPos)
    have hsquare : coupling k * coupling k <= r * r :=
      Q'.mul_le_mul_of_nonneg hcoupling hcoupling hr0 hcoupling0
    have hinverse :
        r * r <=
          (rateScaled afr * rateScaled afr) * invSqTerm 2 (by decide) k :=
      scaledMargin_sq_le_invSq afr k
    have hcouplingInverse :
        coupling k * coupling k <=
          (rateScaled afr * rateScaled afr) * invSqTerm 2 (by decide) k :=
      Q'.le_trans' _ _ _ hsquare hinverse
    have hphysical :=
      E.spacing_quad (coupling k) (coupling_pos k) (coupling_le_window k)
    have hscaled :
        E.C * (coupling k * coupling k) <=
          E.C * ((rateScaled afr * rateScaled afr) *
            invSqTerm 2 (by decide) k) :=
      Q'.mul_le_mul_of_nonneg_left _ _ E.C hcouplingInverse
        (Q'.le_of_lt E.C_pos)
    have hnumerator :
        E.a (coupling k) * E.Λ <=
          (E.C * (rateScaled afr * rateScaled afr)) *
            invSqTerm 2 (by decide) k := by
      have hregroup :
          (E.C * ((rateScaled afr * rateScaled afr) *
            invSqTerm 2 (by decide) k)).eqv
          ((E.C * (rateScaled afr * rateScaled afr)) *
            invSqTerm 2 (by decide) k) :=
        Q'.eqv_symm
          (Q'.mul_assoc_eqv E.C (rateScaled afr * rateScaled afr)
            (invSqTerm 2 (by decide) k))
      exact Q'.le_trans' _ _ _ hphysical
        (Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv hregroup))
    have hquot := Q'.le_divPos_of_mul_le
      ((E.C * (rateScaled afr * rateScaled afr)) *
        invSqTerm 2 (by decide) k) E.Λ E.Λ_pos hnumerator
    have heqv :
        (Q'.divPos
          ((E.C * (rateScaled afr * rateScaled afr)) *
            invSqTerm 2 (by decide) k) E.Λ E.Λ_pos).eqv
        (physicalSpacingCoefficient E C *
          invSqTerm 2 (by decide) k) := by
      exact physical_quotient_eqv
        (E.C * (rateScaled afr * rateScaled afr))
        (invSqTerm 2 (by decide) k) E.Λ E.Λ_pos
    simpa only [Nat.zero_add] using
      Q'.le_trans' _ _ _ hquot (Q'.le_of_eqv heqv)

end YMGap.Continuum.BF4AFPhysicalSpacingInverseSquare

/-! ## BF4/Faraut producer specialization -/

namespace YMGap.Continuum.BF4FarautPhysicalSeparatorProducer

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.AFTrajectoryCertificate
open YMGap.Continuum.BF4AFPhysicalSpacingInverseSquare
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalSeparatorProducer
open YMGap.Continuum.PhysicalSeparator
open YMGap.Continuum.QuadraticRateErrorTailControl

namespace BF4FarautQuarterPhysicalSeparatorProducer

variable {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat -> Q'}
    {bits : Nat -> Nat}
    {P : PhysicalSeparator.PhysicalSeparator}

/-- The BF4 producer's physical spacing inherits the proved AF inverse-square
majorant without an additional summability hypothesis. -/
def physicalSpacingInverseSquareOfAFTrajectory
    (producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P)
    (C : AFTrajectoryCertificate)
    (H : producer.ShiftedAFCoupling C) :
    InverseSquareSpacingTail
      producer.toBF4QuarterPhysicalSeparatorProducer.physicalSpacing 0 := by
  exact spacingInverseSquareTailOfAFTrajectory spacing coupling
    producer.bf4.coupling_pos producer.bf4.coupling_le_window C H

end BF4FarautQuarterPhysicalSeparatorProducer

end YMGap.Continuum.BF4FarautPhysicalSeparatorProducer

#print axioms YMGap.Continuum.BF4AFPhysicalSpacingInverseSquare.physicalSpacingCoefficient_nonnegative
#print axioms YMGap.Continuum.BF4AFPhysicalSpacingInverseSquare.coupling_le_fixedRate
#print axioms YMGap.Continuum.BF4AFPhysicalSpacingInverseSquare.spacingInverseSquareTailOfAFTrajectory
#print axioms YMGap.Continuum.BF4FarautPhysicalSeparatorProducer.BF4FarautQuarterPhysicalSeparatorProducer.physicalSpacingInverseSquareOfAFTrajectory
