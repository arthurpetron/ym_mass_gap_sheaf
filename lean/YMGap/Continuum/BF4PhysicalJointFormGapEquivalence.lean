/-
# The central and reflected-joint completed form gaps are equivalent

On the canonical comparison image, a joint gap gives
`||T x||^2 <= q * <T x,x>`. Ordinary completed Cauchy--Schwarz then gives
`<T x,x>^2 <= (q * ||x||^2) * <T x,x>`. Constructive nonnegative-factor
cancellation recovers the central gap, without an inverse, lower coercivity,
or a positive-norm case split. The constructed centered density supplies the
other direction at exactly the same rate.

This identifies two finite-cutoff analytic obligations; it does not supply
either strict estimate, select a vacuum sector, identify geometric time, or
construct a thermodynamic/continuum Yang--Mills theory.
-/

import YMGap.Continuum.BF4PhysicalJointCenteredDensity
import YMGap.Continuum.RCCauchySchwarz

namespace YMGap.Continuum.BF4PhysicalJointFormGapEquivalence

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.PositiveContractionOneStepCompletion
open YMGap.Continuum.BF4PhysicalJointFormTransfer
open YMGap.Continuum.BF4PhysicalJointFormGapExtension
open YMGap.Continuum.BF4PhysicalJointCenteredDensity
open YMGap.Continuum.BF4PhysicalCompletedOperatorNormGap
open YMGap.Continuum.BF4PhysicalMarkovGNSCompletion
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCompletedOperatorNormGap

private theorem product_scale_right (q : Q') (a b : CReal.RC) :
    CReal.RCmul a (CReal.RCscale q b) =
      CReal.RCmul (CReal.RCscale q a) b := by
  refine Quotient.inductionOn₂ a b ?_
  intro A B
  exact Quotient.sound
    (YMGap.Constructive.SumOfSquares.Equiv_of_approx_eqv
      (fun n => by
        change (A.approx n * (q * B.approx n)).eqv
          ((q * A.approx n) * B.approx n)
        show _ * (_ : Int) = _ * (_ : Int)
        simp only [Q'.mul_num_cast, Q'.mul_den_cast]
        ac_rfl))

/-- A strict joint-completion form bound implies the central bound with the
same rate. No reverse comparison or extra range hypothesis is required. -/
theorem centralCompletedVacuumFormGap_of_joint_form_gap
    {w rate : Q'} (hw : (0 : Q') ≤ w) (K half : Nat)
    (gap : PhysicalJointCompletedVacuumFormGap w hw K half rate) :
    CentralPhysicalCompletedVacuumFormGap w hw K half rate := by
  refine ⟨gap.1, gap.2.1, ?_⟩
  intro x horthogonal
  let D := (centralPhysicalSmulGNS w hw K half).toGNSData
  let E := (physicalJointSmulGNS w hw K half).toGNSData
  let Tx := centralPhysicalCompletedMarkovTransfer w hw K half x
  let F := D.cinnerCompl Tx x
  let N := D.cinnerCompl x x
  have hjoint := gap.2.2 (physicalJointComparison w hw K half x)
    ((physicalJointComparison_vacuumOrthogonal_iff w hw K half x).mpr
      horthogonal)
  have hleft :
      E.cinnerCompl
          (physicalJointTransfer w hw K half
            (physicalJointComparison w hw K half x))
          (physicalJointComparison w hw K half x) =
        D.cinnerCompl Tx Tx := by
    rw [← physicalJointComparison_intertwines]
    simpa only [actionIterate, Nat.zero_add] using
      (physicalJointComparison_moments w hw K half 0 Tx x)
  have hright :
      E.cinnerCompl (physicalJointComparison w hw K half x)
          (physicalJointComparison w hw K half x) = F := by
    have h := physicalJointComparison_moments w hw K half 0 x x
    simp only [actionIterate] at h
    exact h.trans (D.cinnerCompl_comm x Tx)
  rw [hleft, hright] at hjoint
  have hN : CReal.RCnonneg N := D.cinner_self_nonneg x
  have hF : CReal.RCnonneg F :=
    centralPhysicalCompletedMarkovTransfer_positive w hw K half x
  have hscaledN : CReal.RCnonneg (CReal.RCscale rate N) := by
    have h := CReal.RCscale_mono gap.1 hN
    rwa [CReal.RCscale_RCzero] at h
  have hcs : CReal.RCle (CReal.RCmul F F)
      (CReal.RCmul N (D.cinnerCompl Tx Tx)) := by
    have h := D.RC_cauchy_schwarz Tx x
    rw [CReal.RCmul_comm (D.cinnerCompl Tx Tx) (D.cinnerCompl x x)] at h
    exact h
  have hproduct := CReal.RCmul_mono_nonnegative_left_local hN hjoint
  rw [product_scale_right] at hproduct
  exact CReal.RCle_of_mul_self_le_mul_right_nonnegative hF hscaledN
    (CReal.RCle_trans hcs hproduct)

/-- The two completed strict-form obligations are equivalent, with no change
of coupling, cutoff, half-extent or rate. This theorem constructs no gap. -/
theorem completedVacuumFormGap_iff
    {w rate : Q'} (hw : (0 : Q') ≤ w) (K half : Nat) :
    CentralPhysicalCompletedVacuumFormGap w hw K half rate ↔
      PhysicalJointCompletedVacuumFormGap w hw K half rate :=
  ⟨physicalJointCompletedVacuumFormGap_of_central_form_gap hw K half,
    centralCompletedVacuumFormGap_of_joint_form_gap hw K half⟩

#print axioms centralCompletedVacuumFormGap_of_joint_form_gap
#print axioms completedVacuumFormGap_iff

end YMGap.Continuum.BF4PhysicalJointFormGapEquivalence
