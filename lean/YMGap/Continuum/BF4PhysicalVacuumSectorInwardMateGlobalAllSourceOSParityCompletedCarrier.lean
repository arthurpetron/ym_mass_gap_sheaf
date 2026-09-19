/-
# The inward-mate parity witness on the completed physical carrier

The finite inward-mate construction supplies one explicit centered parity
observable with a cutoff-independent strict form margin.  This module carries
that same observable, unchanged, into the completed physical GNS carrier.

The result is intentionally one-vector data: it proves vacuum orthogonality,
nonzero completed norm, the exact same-object matrix coefficient, and the
strict completed form bound for that vector.  It does not assert an
all-observable Poincare inequality, a completed operator gap, a thermodynamic
limit, or a continuum Yang--Mills theory.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
`noncomputable` declaration is used.
-/

import YMGap.Continuum.BF4PhysicalCompletedMacroCorrelator
import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSParityFormGap
import YMGap.Continuum.RCStrictPositivity

namespace YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSParityCompletedCarrier

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000

open YMGap.Constructive
open YMGap.Constructive.ExpNeg
open YMGap.Continuum
open YMGap.Continuum.BF4PhysicalCompletedMacroCorrelator
open YMGap.Continuum.BF4PhysicalMarkovGNSCompletion
open YMGap.Continuum.BF4PhysicalMarkovTransferLaws
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSParityFormGap
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4WeightedJointPerronPerturbation
open YMGap.Continuum.OSReconstructionProgress
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

private theorem physicalConstantRC_mul_eq_scale (factor value : Q') :
    physicalConstantRC (factor * value) =
      CReal.RCscale factor (physicalConstantRC value) := by
  apply Quotient.sound
  exact YMGap.Constructive.CRealAlg.ofQ'_mul factor value

/-- The literal finite parity observable embedded in the completed carrier. -/
def globalInwardMateCenteredParityCompletedObservable (K : Nat) :
    CentralPhysicalGNSCompletion anchorCoupling (by decide) K 0 :=
  centralPhysicalCompletedObservable anchorCoupling (by decide) K 0
    (globalInwardMateCenteredParity K)

theorem globalInwardMateCenteredParityCompletedObservable_vacuumOrthogonal
    (K : Nat) :
    CentralPhysicalCompletedVacuumOrthogonal anchorCoupling (by decide) K 0
      (globalInwardMateCenteredParityCompletedObservable K) := by
  exact centralPhysicalCompletedObservable_vacuumOrthogonal
    anchorCoupling (by decide) K 0 (globalInwardMateCenteredParity K)
    (globalInwardMateCenteredParity_meanZero K)

/-- Its completed norm is exactly the finite weighted norm. -/
theorem globalInwardMateCenteredParityCompletedObservable_norm_eq
    (K : Nat) :
    (centralPhysicalSmulGNS anchorCoupling (by decide) K 0).toGNSData.cinnerCompl
      (globalInwardMateCenteredParityCompletedObservable K)
      (globalInwardMateCenteredParityCompletedObservable K) =
      physicalConstantRC
        (centralPhysicalWeightedInner anchorCoupling (by decide) K 0
          (globalInwardMateCenteredParity K)
          (globalInwardMateCenteredParity K)) := by
  exact centralPhysicalCompletedObservable_inner
    anchorCoupling (by decide) K 0
    (globalInwardMateCenteredParity K)
    (globalInwardMateCenteredParity K)

/-- The completed norm inherits the cutoff-independent finite margin. -/
theorem globalInwardMateCenteredParityCompletedObservable_norm_floor
    (K : Nat) (hK : 1 <= K) :
    CReal.RCle (physicalConstantRC globalInwardMateParityFormMargin)
      ((centralPhysicalSmulGNS anchorCoupling (by decide) K 0).toGNSData.cinnerCompl
        (globalInwardMateCenteredParityCompletedObservable K)
        (globalInwardMateCenteredParityCompletedObservable K)) := by
  rw [globalInwardMateCenteredParityCompletedObservable_norm_eq]
  exact physicalConstantRC_le_of_rat
    (globalInwardMateParityFormMargin_le_centeredNorm K hK)

/-- The completed parity vector is strictly positive in the quotient real. -/
theorem globalInwardMateCenteredParityCompletedObservable_norm_positive
    (K : Nat) (hK : 1 <= K) :
    YMGap.Continuum.RCStrictPositivity.RCIsPositive
      ((centralPhysicalSmulGNS anchorCoupling (by decide) K 0).toGNSData.cinnerCompl
        (globalInwardMateCenteredParityCompletedObservable K)
        (globalInwardMateCenteredParityCompletedObservable K)) := by
  exact ⟨globalInwardMateParityFormMargin,
    globalInwardMateParityFormMargin_positive,
    globalInwardMateCenteredParityCompletedObservable_norm_floor K hK⟩

/-- The same completed vector has the exact finite joint quadratic coefficient. -/
theorem globalInwardMateCenteredParityCompletedObservable_sameObjectCoefficient
    (K : Nat) :
    (centralPhysicalSmulGNS anchorCoupling (by decide) K 0).toGNSData.cinnerCompl
      (globalInwardMateCenteredParityCompletedObservable K)
      (centralPhysicalCompletedMarkovTransfer anchorCoupling (by decide) K 0
        (globalInwardMateCenteredParityCompletedObservable K)) =
      physicalConstantRC
        (centralPhysicalJointQuadratic anchorCoupling (by decide) K 0
          (globalInwardMateCenteredParity K)) := by
  exact centralPhysicalCompletedObservable_macroCoefficient
    anchorCoupling (by decide) K 0 (globalInwardMateCenteredParity K)

/-- The finite strict parity form is a completed-carrier strict form bound. -/
theorem globalInwardMateCenteredParityCompletedObservable_strict_form
    (K : Nat) (hK : 1 <= K) :
    let D := (centralPhysicalSmulGNS anchorCoupling (by decide) K 0).toGNSData
    let vector := globalInwardMateCenteredParityCompletedObservable K
    CReal.RCle
      (D.cinnerCompl
        (centralPhysicalCompletedMarkovTransfer anchorCoupling (by decide) K 0 vector)
        vector)
      (CReal.RCscale globalInwardMateParityFormRate
        (D.cinnerCompl vector vector)) := by
  dsimp only
  let D := (centralPhysicalSmulGNS anchorCoupling (by decide) K 0).toGNSData
  let vector := globalInwardMateCenteredParityCompletedObservable K
  have hfiniteAbs := globalInwardMateCenteredParity_abs_strict_form K hK
  have hjointNonneg := centralPhysicalJointQuadratic_nonnegative
    anchorCoupling (by decide) K 0 (globalInwardMateCenteredParity K)
  have hfiniteAbsJoint :
      Q'.abs (centralPhysicalJointQuadratic anchorCoupling (by decide) K 0
          (globalInwardMateCenteredParity K)) ≤
        globalInwardMateParityFormRate *
          centralPhysicalWeightedInner anchorCoupling (by decide) K 0
            (globalInwardMateCenteredParity K)
            (globalInwardMateCenteredParity K) := by
    apply le_of_eqv_le
      (Q'.eqv_symm
        (Q'.abs_eqv_congr
          (centralPhysicalWeightedMarkovQuadratic_eq_joint
            anchorCoupling (by decide) K 0
              (globalInwardMateCenteredParity K))))
    exact hfiniteAbs
  have hfinite :
      centralPhysicalJointQuadratic anchorCoupling (by decide) K 0
          (globalInwardMateCenteredParity K) ≤
        globalInwardMateParityFormRate *
          centralPhysicalWeightedInner anchorCoupling (by decide) K 0
            (globalInwardMateCenteredParity K)
            (globalInwardMateCenteredParity K) := by
    rw [abs_of_nonneg hjointNonneg] at hfiniteAbsJoint
    exact hfiniteAbsJoint
  have hrat := physicalConstantRC_le_of_rat hfinite
  rw [centralPhysicalCompletedMarkovTransfer_selfAdjoint]
  rw [globalInwardMateCenteredParityCompletedObservable_sameObjectCoefficient,
    globalInwardMateCenteredParityCompletedObservable_norm_eq,
    ← physicalConstantRC_mul_eq_scale]
  exact hrat

structure GlobalInwardMateParityCompletedCarrierCertificate
    (K : Nat) (hK : 1 <= K) : Type where
  vector : CentralPhysicalGNSCompletion anchorCoupling (by decide) K 0
  vector_eq : vector = globalInwardMateCenteredParityCompletedObservable K
  vacuum_orthogonal :
    CentralPhysicalCompletedVacuumOrthogonal anchorCoupling (by decide) K 0 vector
  norm_floor :
    CReal.RCle (physicalConstantRC globalInwardMateParityFormMargin)
      ((centralPhysicalSmulGNS anchorCoupling (by decide) K 0).toGNSData.cinnerCompl
        vector vector)
  norm_positive :
    YMGap.Continuum.RCStrictPositivity.RCIsPositive
      ((centralPhysicalSmulGNS anchorCoupling (by decide) K 0).toGNSData.cinnerCompl
        vector vector)
  same_object_coefficient :
    (centralPhysicalSmulGNS anchorCoupling (by decide) K 0).toGNSData.cinnerCompl
      vector
      (centralPhysicalCompletedMarkovTransfer anchorCoupling (by decide) K 0 vector) =
      physicalConstantRC
        (centralPhysicalJointQuadratic anchorCoupling (by decide) K 0
          (globalInwardMateCenteredParity K))
  strict_form :
    CReal.RCle
      ((centralPhysicalSmulGNS anchorCoupling (by decide) K 0).toGNSData.cinnerCompl
        (centralPhysicalCompletedMarkovTransfer anchorCoupling (by decide) K 0 vector)
        vector)
      (CReal.RCscale globalInwardMateParityFormRate
        ((centralPhysicalSmulGNS anchorCoupling (by decide) K 0).toGNSData.cinnerCompl
          vector vector))

def globalInwardMateParityCompletedCarrierCertificate
    (K : Nat) (hK : 1 <= K) :
    GlobalInwardMateParityCompletedCarrierCertificate K hK :=
  { vector := globalInwardMateCenteredParityCompletedObservable K
    vector_eq := rfl
    vacuum_orthogonal :=
      globalInwardMateCenteredParityCompletedObservable_vacuumOrthogonal K
    norm_floor := globalInwardMateCenteredParityCompletedObservable_norm_floor K hK
    norm_positive :=
      globalInwardMateCenteredParityCompletedObservable_norm_positive K hK
    same_object_coefficient :=
      globalInwardMateCenteredParityCompletedObservable_sameObjectCoefficient K
    strict_form := globalInwardMateCenteredParityCompletedObservable_strict_form K hK }

end YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSParityCompletedCarrier

#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSParityCompletedCarrier.globalInwardMateCenteredParityCompletedObservable
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSParityCompletedCarrier.globalInwardMateCenteredParityCompletedObservable_vacuumOrthogonal
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSParityCompletedCarrier.globalInwardMateCenteredParityCompletedObservable_norm_floor
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSParityCompletedCarrier.globalInwardMateCenteredParityCompletedObservable_norm_positive
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSParityCompletedCarrier.globalInwardMateCenteredParityCompletedObservable_sameObjectCoefficient
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSParityCompletedCarrier.globalInwardMateCenteredParityCompletedObservable_strict_form
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSParityCompletedCarrier.globalInwardMateParityCompletedCarrierCertificate
