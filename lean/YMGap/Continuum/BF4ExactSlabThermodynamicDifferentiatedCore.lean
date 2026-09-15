/-
# The ACTUAL derivative on the existing original dense domain

Reuse LogarithmicCore.CorePoint's domain states T2y and their already
constructed density witnesses. The image HERE is the actual derivative
J(y); the separate CorePoint.image=L(y) is neither changed nor silently
identified with J. The new image is well-defined, positive, symmetric,
linear for rational and supplied constructive real scalars, and zero on
the vacuum. Its remainder is exactly the proved real-time remainder.

The derivative's transfer-defect lower bound and the OLD completed T2
gap give B(H0v,v) >= (1/2) B(v,v) for original centered domain states.
Explicit Cauchy graph rows also prove closability: state limit zero forces
image limit zero, by symmetry and injectivity of the ORIGINAL T2.

This is a dense-domain derivative form gap, not a self-adjoint spectral
theorem. A maximal/self-adjoint realization, identification with L,
physical time/spacing/beta(a), continuum QFT and all required gauge groups
remain open. SU(2), nome 1/1024, fixed spacing and T2-time units only.
-/

import YMGap.Continuum.BF4ExactSlabThermodynamicDerivativeLaws
import YMGap.Continuum.BF4ExactSlabThermodynamicLogarithmicCore

namespace YMGap.Continuum.BF4ExactSlabThermodynamicDifferentiatedCore

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.PositiveRealDyadicTimeData (PositiveTime)
open YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletionLinear
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedInner
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedBilinear
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedGeometry
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedRealScalar
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedTime
open YMGap.Continuum.BF4ExactSlabThermodynamicCenteredCompletion (completedInner_sub_left)
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedGap (complement_twoStep_form_gap)
open YMGap.Continuum.BF4ExactSlabThermodynamicFullSpaceZeroContinuity (transfer_kernel_trivial)
open YMGap.Continuum.BF4ExactSlabThermodynamicCauchyRows
open YMGap.Continuum.BF4ExactSlabThermodynamicRowPairingOrder
open YMGap.Continuum.BF4ExactSlabThermodynamicTimeDefectMoments (sub_nonnegative)
open YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialFunctional (rc_add_zero)
open YMGap.Continuum.BF4ExactSlabThermodynamicDyadicTimeMeshes (generator_zero)
open YMGap.Continuum.BF4ExactSlabThermodynamicDyadicDefectDecay (defect)
open YMGap.Continuum.BF4ExactSlabThermodynamicDyadicDerivative (derivativeAction)
open YMGap.Continuum.BF4ExactSlabThermodynamicMeshDerivative (derivativeRepresentative derivativeRepresentative_pin)
open YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimePins
open YMGap.Continuum.BF4ExactSlabThermodynamicRealDerivative
open YMGap.Continuum.BF4ExactSlabThermodynamicDerivativeLaws
open YMGap.Continuum.BF4ExactSlabThermodynamicLogarithmicCore (CorePoint vacuumPoint)

local notation "B" => completedInner
local notation "point" X => Quotient.mk seminorm.completionSetoid X
local notation "rat" q => Quotient.mk crealSetoid (ofQ' q)

/-- Actual derivative image on the OLD domain; distinct from CorePoint.image. -/
def image (p : CorePoint) : Completion := derivativeAction p.preimage

theorem image_welldef (p q : CorePoint) (h : p.state=q.state) : image p=image q :=
  congrArg image (p.state_injective q h)

theorem image_add (p q : CorePoint) : image (p.add q)=completedAdd (image p) (image q) :=
  derivative_add p.preimage q.preimage

theorem image_smul (c : Q') (p : CorePoint) : image (p.smul c)=completedSmul c (image p) :=
  derivative_smul c p.preimage

def realSmulPoint (s : CReal) (cs : QCauchy s.approx) (p : CorePoint) : CorePoint :=
  ⟨completedRealSmul s cs p.preimage⟩

theorem realSmulPoint_laws (s : CReal) (cs : QCauchy s.approx) (p : CorePoint) :
    (realSmulPoint s cs p).state=completedRealSmul s cs p.state ∧
      image (realSmulPoint s cs p)=completedRealSmul s cs (image p) :=
  ⟨completedTime_realSmul 2 s cs p.preimage,derivative_realSmul s cs p.preimage⟩

theorem image_symmetric (p q : CorePoint) : B (image p) q.state=B p.state (image q) := by
  change B (derivativeAction p.preimage) (twoStepTransfer q.preimage)=
    B (twoStepTransfer p.preimage) (derivativeAction q.preimage)
  rw [derivative_symmetric,derivative_transfer,twoStepTransfer_symmetric]

theorem image_nonnegative (p : CorePoint) : RCnonneg (B (image p) p.state) :=
  derivative_transfer_nonnegative p.preimage

/-- Bounded in the PREIMAGE norm, not a boundedness claim for H0 on domain states. -/
theorem image_preimage_bound (p : CorePoint) : RCle (B (image p) (image p)) (B p.preimage p.preimage) :=
  derivative_contraction p.preimage

theorem vacuum_image : image vacuumPoint=completedZero := derivative_unit

theorem image_orthogonal_unit (p : CorePoint) : B (image p) completedUnit=RCzero := by
  unfold image
  rw [derivative_symmetric,derivative_unit,completedInner_zero_right]

private theorem half_le_sub (a b : RC) (h : RCle b (RCscale HalfPow.half a)) :
    RCle (RCscale HalfPow.half a) (RCsub a b) := by
  have hb := RCadd_le_add (RCle_refl (RCscale HalfPow.half a))
    (sub_nonnegative _ _ h)
  rw [rc_add_zero] at hb
  have heq : RCadd (RCscale HalfPow.half a) (RCsub (RCscale HalfPow.half a) b)=RCsub a b := by
    refine Quotient.inductionOn₂ a b ?_
    intro A C
    exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
      Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.add_assoc_eqv _ _ _))
        (Q'.add_eqv_congr_right _ _ _ (ExpNeg.two_halves (A.approx n)))))
  rw [heq] at hb
  exact hb

/-- A derivative FORM gap on the actual centered dense domain, in T2-time units. -/
theorem image_form_gap (p : CorePoint) (hp : B p.state completedUnit=RCzero) :
    RCle (RCscale HalfPow.half (B p.state p.state)) (B (image p) p.state) := by
  have hg := (complement_twoStep_form_gap ⟨p.state,hp⟩).2
  have hd := half_le_sub (B p.state p.state) (B p.state (twoStepTransfer p.state)) hg
  have hl := derivative_form_lower p.preimage
  change RCle (B (defect 0 p.state) p.state) (B (image p) p.state) at hl
  unfold defect at hl
  rw [generator_zero,completedInner_sub_left,completedInner_symm (twoStepTransfer p.state) p.state] at hl
  exact RCle_trans hd hl

def remainder (D : PositiveTime) (p : CorePoint) : Completion :=
  completedSub (completedSub p.state (realTimeAction (timeValue D) p.state))
    (completedRealSmul D.real D.cauchy (image p))

theorem remainder_pin (D : PositiveTime) (p : CorePoint) : remainder D p=realRemainder D p.preimage := rfl

/-- Existing original representative data compute the derivative radius on this domain. -/
def derivativeCertificate (X : seminorm.Cauchy) (epsilon : Q') (he : (0 : Q')<epsilon) :
    Σ' radius : Q', ((0 : Q')<radius) ×'
      (∀ D : PositiveTime, RCle (realValue (timeValue D)) (rat radius) →
        RCle (B (remainder D ⟨point X⟩) (remainder D ⟨point X⟩))
          (RCmul (RCmul (realValue (timeValue D)) (realValue (timeValue D))) (rat epsilon))) :=
  realTaylorCertificate X epsilon he

/-- Closability for supplied ORIGINAL Cauchy graph rows, with no new completion or chosen limit. -/
theorem graph_rows_closable (p : Nat → CorePoint) (R S : CauchyRows)
    (hr : ∀ n,rowPoint R n=(p n).state) (hs : ∀ n,rowPoint S n=image (p n))
    (hzero : rowLimit R=completedZero) : rowLimit S=completedZero := by
  apply transfer_kernel_trivial (rowLimit S)
  apply completed_eq_of_pairings
  intro z
  rw [twoStepTransfer_symmetric,completedInner_zero_left]
  refine Quotient.inductionOn z ?_
  intro Z
  have h := rowLimit_pairing_eq S (constantRows (timeCauchy 2 Z)) R (constantRows (derivativeRepresentative Z)) (by
    intro n
    rw [hr,hs,constantRows_pin,constantRows_pin,derivativeRepresentative_pin]
    exact image_symmetric (p n) ⟨point Z⟩)
  rw [rowLimit_constant,rowLimit_constant,derivativeRepresentative_pin,hzero,completedInner_zero_left] at h
  exact h

end YMGap.Continuum.BF4ExactSlabThermodynamicDifferentiatedCore

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDifferentiatedCore.image
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDifferentiatedCore.image_welldef
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDifferentiatedCore.image_add
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDifferentiatedCore.image_smul
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDifferentiatedCore.realSmulPoint
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDifferentiatedCore.realSmulPoint_laws
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDifferentiatedCore.image_symmetric
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDifferentiatedCore.image_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDifferentiatedCore.image_preimage_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDifferentiatedCore.vacuum_image
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDifferentiatedCore.image_orthogonal_unit
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDifferentiatedCore.image_form_gap
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDifferentiatedCore.remainder
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDifferentiatedCore.remainder_pin
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDifferentiatedCore.derivativeCertificate
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDifferentiatedCore.graph_rows_closable
