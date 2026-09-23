/-
# Cutoff-two obstruction to a completed full-carrier physical form gap

The literal cutoff-two positive carrier contains a nonzero centered fixed mode.
Consequently the existing finite upper-gap obstruction also rules out every
strict completed vacuum-complement form gap on that same carrier.  This is an
exact statement only at `cutoffTwoHalfCoupling`, cutoff `2`, and half extent
`0`; it makes no claim about other couplings, cutoffs, or vacuum-sector
restrictions.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorReducibilityObstruction
import YMGap.Continuum.BF4PhysicalCompletedOperatorNormGap
import YMGap.Continuum.BF4PhysicalJointFormGapEquivalence

namespace YMGap.Continuum.BF4PhysicalCompletedFullCarrierObstruction

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorReducibilityObstruction
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalCompletedCenteredFormGap
open YMGap.Continuum.BF4PhysicalCompletedMacroCorrelator
open YMGap.Continuum.BF4PhysicalCompletedOperatorNormGap
open YMGap.Continuum.BF4PhysicalJointFormGapEquivalence
open YMGap.Continuum.BF4PhysicalJointFormGapExtension
open YMGap.Continuum.BF4PhysicalMarkovGNSCompletion
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4WeightedJointPerronPerturbation
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph

/-- Eventual order between two rational constant reals reflects the underlying
rational order. -/
private theorem le_of_constant_leEv {a b : Q'}
    (h : CReal.leEv (CReal.ofQ' a) (CReal.ofQ' b)) : a ≤ b := by
  refine Q'.le_of_forall_pos_add (fun epsilon hepsilon => ?_)
  obtain ⟨N, hN⟩ := h epsilon hepsilon
  simpa using hN N (Nat.le_refl N)

/-- No strict completed form-gap contract exists on the literal full positive
carrier at the explicit cutoff-two test point. -/
theorem no_cutoffTwo_completed_fullCarrier_vacuum_form_gap
    (rate : Q') :
    ¬ CentralPhysicalCompletedVacuumFormGap
      cutoffTwoHalfCoupling
      (by decide : (0 : Q') ≤ cutoffTwoHalfCoupling)
      2 0 rate := by
  intro gap
  apply no_cutoffTwo_fullCarrier_strict_upper_gap rate gap.2.1
  intro observable hmean
  let hw : (0 : Q') ≤ cutoffTwoHalfCoupling := by decide
  let vector := centralPhysicalCompletedObservable
    cutoffTwoHalfCoupling hw 2 0 observable
  have hcompleted := gap.2.2 vector
    (centralPhysicalCompletedObservable_vacuumOrthogonal
      cutoffTwoHalfCoupling hw 2 0 observable hmean)
  have hleft :
      (centralPhysicalSmulGNS cutoffTwoHalfCoupling hw 2 0).toGNSData.cinnerCompl
          (centralPhysicalCompletedMarkovTransfer
            cutoffTwoHalfCoupling hw 2 0 vector) vector =
        physicalConstantRC
          (centralPhysicalJointQuadratic
            cutoffTwoHalfCoupling hw 2 0 observable) := by
    exact (centralPhysicalCompletedMarkovTransfer_selfAdjoint
      cutoffTwoHalfCoupling hw 2 0 vector vector).trans
        (centralPhysicalCompletedObservable_macroCoefficient
          cutoffTwoHalfCoupling hw 2 0 observable)
  have hright :
      (centralPhysicalSmulGNS cutoffTwoHalfCoupling hw 2 0).toGNSData.cinnerCompl
          vector vector =
        physicalConstantRC
          (centralPhysicalWeightedInner
            cutoffTwoHalfCoupling hw 2 0 observable observable) :=
    centralPhysicalCompletedObservable_inner
      cutoffTwoHalfCoupling hw 2 0 observable observable
  rw [hleft, hright] at hcompleted
  change CReal.leEv
    (CReal.ofQ'
      (centralPhysicalJointQuadratic
        cutoffTwoHalfCoupling hw 2 0 observable))
    (CReal.mul (CReal.ofQ' rate)
      (CReal.ofQ'
        (centralPhysicalWeightedInner
          cutoffTwoHalfCoupling hw 2 0 observable observable))) at hcompleted
  have hconstant : CReal.leEv
      (CReal.ofQ'
        (centralPhysicalJointQuadratic
          cutoffTwoHalfCoupling hw 2 0 observable))
      (CReal.ofQ'
        (rate * centralPhysicalWeightedInner
          cutoffTwoHalfCoupling hw 2 0 observable observable)) :=
    CReal.leEv_trans hcompleted
      (CReal.leEv_of_equiv
        (CReal.Equiv.symm
          (CRealAlg.ofQ'_mul rate
            (centralPhysicalWeightedInner
              cutoffTwoHalfCoupling hw 2 0 observable observable))))
  exact le_of_constant_leEv hconstant

/-- Passing to the reflected-joint completion does not remove the extra
fixed mode: a joint gap would imply the already-refuted central gap. -/
theorem no_cutoffTwo_completed_joint_fullCarrier_vacuum_form_gap
    (rate : Q') :
    ¬ PhysicalJointCompletedVacuumFormGap
      cutoffTwoHalfCoupling
      (by decide : (0 : Q') ≤ cutoffTwoHalfCoupling)
      2 0 rate := by
  intro gap
  exact no_cutoffTwo_completed_fullCarrier_vacuum_form_gap rate
    (centralCompletedVacuumFormGap_of_joint_form_gap
      (by decide : (0 : Q') ≤ cutoffTwoHalfCoupling) 2 0 gap)

#print axioms no_cutoffTwo_completed_fullCarrier_vacuum_form_gap
#print axioms no_cutoffTwo_completed_joint_fullCarrier_vacuum_form_gap

end YMGap.Continuum.BF4PhysicalCompletedFullCarrierObstruction
