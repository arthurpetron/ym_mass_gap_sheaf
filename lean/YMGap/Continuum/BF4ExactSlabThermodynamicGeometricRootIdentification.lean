/-
# The constructed positive root IS the original geometric one-step time

Geometric time commutes with each original T2 polynomial, hence with its
constructed uniform-sequence action by the existing represented pairing
limits. Let A=T1, B=rootAction and d=Ax-Bx. The same square and commutation
give (A+B)d=0. Positivity of A forces <Bd,d><=0. The already constructed
next root C has <Bd,d>=||Cd||^2, so Cd=Bd=Ad=0. Symmetry then gives
||d||^2=<x,(A-B)d>=0. Thus A=B, without a spectral theorem or inverse.

This identifies operators on the SAME original thermodynamic completion
at SU(2) nome 1/1024 and fixed spacing. It does not prove either operator
injective, range density, full-space time-zero continuity, a physical
Hamiltonian, continuum scaling, other groups, or the Clay target.
-/

import YMGap.Continuum.BF4ExactSlabThermodynamicOneStepPositivity
import YMGap.Continuum.BF4ExactSlabThermodynamicDyadicTimeMeshes

namespace YMGap.Continuum.BF4ExactSlabThermodynamicGeometricRootIdentification

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletionLinear
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedInner
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedBilinear
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedGeometry
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedPosdef (completedInner_posdef)
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedRealScalar (completed_eq_of_pairings)
open YMGap.Continuum.BF4ExactSlabThermodynamicCenteredCompletion (completedInner_sub_left completedSub_zero)
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedTime
open YMGap.Continuum.BF4ExactSlabThermodynamicRelaxation (completedTime_sub)
open YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinPolynomialMoments (polynomialVector)
open YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialOperator
open YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialFunctional (rc_zero_add)
open YMGap.Continuum.BF4ExactSlabThermodynamicCauchyRows
open YMGap.Continuum.BF4ExactSlabThermodynamicRowPairingOrder
open YMGap.Continuum.BF4ExactSlabThermodynamicUniformPolynomialAction
open YMGap.Continuum.BF4ExactSlabThermodynamicUniformPolynomialLinear
open YMGap.Continuum.BF4ExactSlabThermodynamicSquareRootAction
open YMGap.Continuum.BF4ExactSlabThermodynamicUniformRootAction (sequenceAction_zero)
open YMGap.Continuum.BF4ExactSlabThermodynamicDyadicTimeMeshes
open YMGap.Continuum.BF4ExactSlabThermodynamicOneStepPositivity

local notation "point" X => Quotient.mk seminorm.completionSetoid X
local notation "B" => completedInner

theorem time_polynomialVector (lag : Nat) (p : QPoly.Poly) (r : Nat) (x : Completion) :
    completedTime lag (polynomialVector x p r)=polynomialVector (completedTime lag x) p r := by
  induction p generalizing r with
  | nil => exact completedTime_zeroState lag
  | cons c p ih =>
      simp only [polynomialVector,completedTime_add,completedTime_smul,completedTime_comp,ih]
      rw [Nat.add_comm (r+r) lag]

theorem time_polynomialOperator (lag : Nat) (p : QPoly.Poly) (x : Completion) :
    completedTime lag (polynomialOperator p x)=polynomialOperator p (completedTime lag x) :=
  time_polynomialVector lag p 0 x

/-- Commutation passes through the SAME explicit-modulus pairing limits. -/
theorem sequenceAction_time (P : UniformSequence) (lag : Nat) (x : Completion) :
    sequenceAction P (completedTime lag x)=completedTime lag (sequenceAction P x) := by
  apply completed_eq_of_pairings
  intro y
  refine Quotient.inductionOn₂ x y ?_
  intro X Y
  have h := rowLimit_pairing_eq (actionRows P (timeCauchy lag X)) (constantRows Y)
    (actionRows P X) (constantRows (timeCauchy lag Y)) (by
      intro n
      rw [actionRows_pin,constantRows_pin,actionRows_pin,constantRows_pin]
      change B (polynomialOperator (P.polynomial n) (completedTime lag (point X))) (point Y)=
        B (polynomialOperator (P.polynomial n) (point X)) (completedTime lag (point Y))
      rw [← time_polynomialOperator,completedTime_symmetric])
  rw [rowLimit_constant,rowLimit_constant] at h
  change B (sequenceAction P (completedTime lag (point X))) (point Y)=
    B (sequenceAction P (point X)) (completedTime lag (point Y)) at h
  exact h.trans (completedTime_symmetric lag _ _).symm

theorem rootAction_time (lag : Nat) (x : Completion) :
    rootAction (completedTime lag x)=completedTime lag (rootAction x) := sequenceAction_time _ lag x

/-- Positivity identifies the constructed root with geometric time, even if a kernel remains. -/
theorem geometric_one_eq_root (x : Completion) : completedTime 1 x=rootAction x := by
  let d := completedSub (completedTime 1 x) (rootAction x)
  have hA : completedTime 1 d=completedSub (twoStepTransfer x) (rootAction (completedTime 1 x)) := by
    dsimp only [d]
    rw [completedTime_sub,completedTime_comp,← rootAction_time]
    rfl
  have hB : rootAction d=completedSub (rootAction (completedTime 1 x)) (twoStepTransfer x) := by
    change sequenceAction _ (completedSub _ _)=_
    rw [sequenceAction_sub]
    change completedSub _ (rootAction (rootAction x))=_
    rw [rootAction_square]
    rfl
  have hcancel : completedAdd (completedTime 1 d) (rootAction d)=completedZero := by
    rw [hA,hB]
    unfold completedSub
    rw [completedAdd_assoc,← completedAdd_assoc (completedNeg (rootAction (completedTime 1 x)))
      (rootAction (completedTime 1 x)) (completedNeg (twoStepTransfer x)),
      completedNeg_add,completedZero_add,completedAdd_comm,completedNeg_add]
  have hle : RCle (B (rootAction d) d) RCzero := by
    have h := RCadd_le_add (completedTime_one_nonnegative d) (RCle_refl (B (rootAction d) d))
    rw [rc_zero_add,← completedInner_add_left,hcancel,completedInner_zero_left] at h
    exact h
  have hC : generator 2 d=completedZero := by
    apply (completedInner_posdef _).mp
    apply RCle_antisymm ?_ (completedInner_nonnegative _)
    rw [generator_pairing 1,generator_one]
    exact hle
  have hBd : rootAction d=completedZero := by
    calc
      rootAction d=generator 2 (generator 2 d) := (generator_square 1 d).symm
      _=generator 2 completedZero := congrArg (generator 2) hC
      _=completedZero := sequenceAction_zero _
  have hAd : completedTime 1 d=completedZero := by
    rw [hBd,completedAdd_zero] at hcancel
    exact hcancel
  apply (completedDist_zero_iff _ _).mp
  change B d d=RCzero
  calc
    B d d=RCsub (B x (completedTime 1 d)) (B x (rootAction d)) := by
      change B (completedSub _ _) d=_
      rw [completedInner_sub_left,completedTime_symmetric,rootAction_symmetric]
    _=B (completedSub completedZero completedZero) x := by
      rw [hAd,hBd,completedInner_sub_left,completedInner_zero_left,completedInner_zero_right]
    _=RCzero := by rw [completedSub_self,completedInner_zero_left]

/-- The first dyadic refinement now retains literal original one-step time. -/
theorem generator_one_geometric (x : Completion) : generator 1 x=completedTime 1 x :=
  (generator_one x).trans (geometric_one_eq_root x).symm

end YMGap.Continuum.BF4ExactSlabThermodynamicGeometricRootIdentification

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicGeometricRootIdentification.time_polynomialVector
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicGeometricRootIdentification.time_polynomialOperator
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicGeometricRootIdentification.sequenceAction_time
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicGeometricRootIdentification.rootAction_time
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicGeometricRootIdentification.geometric_one_eq_root
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicGeometricRootIdentification.generator_one_geometric
