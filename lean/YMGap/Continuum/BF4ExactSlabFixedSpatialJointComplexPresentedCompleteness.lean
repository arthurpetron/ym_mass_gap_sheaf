/-
# Represented complex limits on the SAME reflected carrier

The Cauchy condition uses the actual complex squared norm. Its two nonnegative
real components supply represented real Cauchy families, whose constructed
limits are paired. All representatives and outer moduli remain explicit data.
The actual discrete transfer commutes with this construction.

This is represented completeness at fixed nome and spatial width, not a lift
of arbitrary quotient-valued sequences, a continuous-time Hamiltonian, or a
continuum/QFT construction.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialJointComplexification
import YMGap.Continuum.BF4ExactSlabFixedSpatialJointPresentedLimitLaws

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialJointComplexPresentedCompleteness

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.CRealSeminormCompletion
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointSeminorm
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointPhysicalTime
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointLinear
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointCompletedInner
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointPresentedCompleteness
  (completedDistSq)
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointComplexification


variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (width : Nat)

local notation "D" => jointSeminorm hw0 hw1 width
local notation "VC" => ComplexCarrier hw0 hw1 width
local notation "RD" => completedDistSq hw0 hw1 width

def complexSub (x y : VC) : VC :=
  (completedSub hw0 hw1 width x.1 y.1, completedSub hw0 hw1 width x.2 y.2)

/-- Squared distance from the existing complex pairing, not a new norm. -/
def complexDistSq (x y : VC) : RC :=
  (inner hw0 hw1 width (complexSub hw0 hw1 width x y)
    (complexSub hw0 hw1 width x y)).1

theorem complexDistSq_components (x y : VC) :
    complexDistSq hw0 hw1 width x y = RCadd (RD x.1 y.1) (RD x.2 y.2) := rfl

private theorem rc_add_zero (a : RC) : RCadd a RCzero = a := by
  refine Quotient.inductionOn a ?_
  exact fun A => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => QPoly.q_add_zero_eqv (A.approx n)))

private theorem rc_zero_add (a : RC) : RCadd RCzero a = a := by
  refine Quotient.inductionOn a ?_
  exact fun A => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => QPoly.q_zero_add_eqv (A.approx n)))

private theorem rc_two_halves (epsilon : Q') :
    RCadd (Quotient.mk crealSetoid (ofQ' (HalfPow.half * epsilon)))
        (Quotient.mk crealSetoid (ofQ' (HalfPow.half * epsilon))) =
      Quotient.mk crealSetoid (ofQ' epsilon) := by
  change Quotient.mk crealSetoid
    (add (ofQ' (HalfPow.half * epsilon)) (ofQ' (HalfPow.half * epsilon))) = _
  rw [ofQ'_add]
  exact Quotient.sound (ofQ'_equiv_of_eqv (ExpNeg.two_halves epsilon))

theorem realDistSq_le_complex (x y : VC) :
    RCle (RD x.1 y.1) (complexDistSq hw0 hw1 width x y) := by
  have h := RCadd_le_add (RCle_refl (RD x.1 y.1))
    (completedInner_nonnegative hw0 hw1 width (completedSub hw0 hw1 width x.2 y.2))
  rw [rc_add_zero] at h
  exact h

theorem imagDistSq_le_complex (x y : VC) :
    RCle (RD x.2 y.2) (complexDistSq hw0 hw1 width x y) := by
  have h := RCadd_le_add
    (completedInner_nonnegative hw0 hw1 width (completedSub hw0 hw1 width x.1 y.1))
    (RCle_refl (RD x.2 y.2))
  rw [rc_zero_add] at h
  exact h

/-- Supplied representatives, with Cauchy control in the ACTUAL complex norm. -/
structure PresentedComplexCauchy where
  pt : Nat → (D).Cauchy × (D).Cauchy
  modulus : Q' → Nat
  cauchy : ∀ epsilon, (0 : Q') < epsilon → ∀ p q,
    modulus epsilon ≤ p → modulus epsilon ≤ q →
    RCle (complexDistSq hw0 hw1 width
      (Quotient.mk (D).completionSetoid (pt p).1,
        Quotient.mk (D).completionSetoid (pt p).2)
      (Quotient.mk (D).completionSetoid (pt q).1,
        Quotient.mk (D).completionSetoid (pt q).2))
      (Quotient.mk crealSetoid (ofQ' epsilon))

namespace PresentedComplexCauchy

variable (X : PresentedComplexCauchy hw0 hw1 width)

def point (p : Nat) : VC :=
  (Quotient.mk (D).completionSetoid (X.pt p).1,
    Quotient.mk (D).completionSetoid (X.pt p).2)

def realPart : BF4ExactSlabFixedSpatialJointPresentedCompleteness.PresentedNormCauchy hw0 hw1 width where
  pt p := (X.pt p).1
  modulus := X.modulus
  cauchy epsilon he p q hp hq :=
    RCle_trans (realDistSq_le_complex hw0 hw1 width
      (X.point hw0 hw1 width p) (X.point hw0 hw1 width q))
      (X.cauchy epsilon he p q hp hq)

def imagPart : BF4ExactSlabFixedSpatialJointPresentedCompleteness.PresentedNormCauchy hw0 hw1 width where
  pt p := (X.pt p).2
  modulus := X.modulus
  cauchy epsilon he p q hp hq :=
    RCle_trans (imagDistSq_le_complex hw0 hw1 width
      (X.point hw0 hw1 width p) (X.point hw0 hw1 width q))
      (X.cauchy epsilon he p q hp hq)

def limit : VC :=
  ((X.realPart hw0 hw1 width).limit hw0 hw1 width,
    (X.imagPart hw0 hw1 width).limit hw0 hw1 width)

def limitRate (epsilon : Q') : Nat :=
  max ((X.realPart hw0 hw1 width).limitRate hw0 hw1 width (HalfPow.half * epsilon))
    ((X.imagPart hw0 hw1 width).limitRate hw0 hw1 width (HalfPow.half * epsilon))

/-- Explicit convergence in the existing complex squared norm. -/
theorem limit_converges (epsilon : Q') (he : (0 : Q') < epsilon)
    (p : Nat) (hp : X.limitRate hw0 hw1 width epsilon ≤ p) :
    RCle (complexDistSq hw0 hw1 width (X.point hw0 hw1 width p)
      (X.limit hw0 hw1 width)) (Quotient.mk crealSetoid (ofQ' epsilon)) := by
  have hr := (X.realPart hw0 hw1 width).limit_converges hw0 hw1 width
    (HalfPow.half * epsilon) (ExpNeg.half_mul_pos epsilon he) p
    (Nat.le_trans (Nat.le_max_left _ _) hp)
  have hi := (X.imagPart hw0 hw1 width).limit_converges hw0 hw1 width
    (HalfPow.half * epsilon) (ExpNeg.half_mul_pos epsilon he) p
    (Nat.le_trans (Nat.le_max_right _ _) hp)
  have h := RCadd_le_add hr hi
  rw [rc_two_halves] at h
  exact h

end PresentedComplexCauchy

/-- Candidate limit data, again retaining the representatives and modulus. -/
structure CandidateLimit (X : PresentedComplexCauchy hw0 hw1 width) where
  representative : (D).Cauchy × (D).Cauchy
  modulus : Q' → Nat
  converges : ∀ epsilon, (0 : Q') < epsilon → ∀ p, modulus epsilon ≤ p →
    RCle (complexDistSq hw0 hw1 width (X.point hw0 hw1 width p)
      (Quotient.mk (D).completionSetoid representative.1,
        Quotient.mk (D).completionSetoid representative.2))
      (Quotient.mk crealSetoid (ofQ' epsilon))

/-- Uniqueness uses only the supplied candidate witnesses. -/
theorem CandidateLimit.eq_constructed_limit
    (X : PresentedComplexCauchy hw0 hw1 width) (C : CandidateLimit hw0 hw1 width X) :
    (Quotient.mk (D).completionSetoid C.representative.1,
      Quotient.mk (D).completionSetoid C.representative.2) = X.limit hw0 hw1 width := by
  let R : BF4ExactSlabFixedSpatialJointPresentedLimitLaws.CandidateLimit hw0 hw1 width (X.realPart hw0 hw1 width) := {
    representative := C.representative.1
    modulus := C.modulus
    converges := fun epsilon he p hp => RCle_trans
      (realDistSq_le_complex hw0 hw1 width (X.point hw0 hw1 width p)
        (Quotient.mk (D).completionSetoid C.representative.1,
          Quotient.mk (D).completionSetoid C.representative.2))
      (C.converges epsilon he p hp) }
  let I : BF4ExactSlabFixedSpatialJointPresentedLimitLaws.CandidateLimit hw0 hw1 width (X.imagPart hw0 hw1 width) := {
    representative := C.representative.2
    modulus := C.modulus
    converges := fun epsilon he p hp => RCle_trans
      (imagDistSq_le_complex hw0 hw1 width (X.point hw0 hw1 width p)
        (Quotient.mk (D).completionSetoid C.representative.1,
          Quotient.mk (D).completionSetoid C.representative.2))
      (C.converges epsilon he p hp) }
  exact Prod.ext (R.eq_constructed_limit hw0 hw1 width (X.realPart hw0 hw1 width))
    (I.eq_constructed_limit hw0 hw1 width (X.imagPart hw0 hw1 width))

namespace PresentedComplexCauchy

/-- Assemble independently supplied real and imaginary Cauchy families. -/
def ofComponents (R I : BF4ExactSlabFixedSpatialJointPresentedCompleteness.PresentedNormCauchy hw0 hw1 width) :
    PresentedComplexCauchy hw0 hw1 width where
  pt p := (R.pt p,I.pt p)
  modulus epsilon := max (R.modulus (HalfPow.half * epsilon))
    (I.modulus (HalfPow.half * epsilon))
  cauchy := by
    intro epsilon he p q hp hq
    have hr := R.cauchy _ (ExpNeg.half_mul_pos epsilon he) p q
      (Nat.le_trans (Nat.le_max_left _ _) hp) (Nat.le_trans (Nat.le_max_left _ _) hq)
    have hi := I.cauchy _ (ExpNeg.half_mul_pos epsilon he) p q
      (Nat.le_trans (Nat.le_max_right _ _) hp) (Nat.le_trans (Nat.le_max_right _ _) hq)
    have h := RCadd_le_add hr hi
    rw [rc_two_halves] at h
    exact h

theorem ofComponents_limit (R I : BF4ExactSlabFixedSpatialJointPresentedCompleteness.PresentedNormCauchy hw0 hw1 width) :
    (ofComponents hw0 hw1 width R I).limit hw0 hw1 width =
      (R.limit hw0 hw1 width,I.limit hw0 hw1 width) := by
  let C : CandidateLimit hw0 hw1 width (ofComponents hw0 hw1 width R I) := {
    representative := ((R.toPresented hw0 hw1 width).diagonal,
      (I.toPresented hw0 hw1 width).diagonal)
    modulus := fun epsilon => max (R.limitRate hw0 hw1 width (HalfPow.half * epsilon))
      (I.limitRate hw0 hw1 width (HalfPow.half * epsilon))
    converges := by
      intro epsilon he p hp
      have hr := R.limit_converges hw0 hw1 width _ (ExpNeg.half_mul_pos epsilon he) p
        (Nat.le_trans (Nat.le_max_left _ _) hp)
      have hi := I.limit_converges hw0 hw1 width _ (ExpNeg.half_mul_pos epsilon he) p
        (Nat.le_trans (Nat.le_max_right _ _) hp)
      have h := RCadd_le_add hr hi
      rw [rc_two_halves] at h
      exact h }
  exact (C.eq_constructed_limit hw0 hw1 width (ofComponents hw0 hw1 width R I)).symm

/-- Apply the actual discrete transfer to the supplied streams. -/
def mapTime (X : PresentedComplexCauchy hw0 hw1 width) (time : Nat) :
    PresentedComplexCauchy hw0 hw1 width :=
  ofComponents hw0 hw1 width
    (BF4ExactSlabFixedSpatialJointPresentedLimitLaws.PresentedNormCauchy.mapTime hw0 hw1 width (X.realPart hw0 hw1 width) time)
    (BF4ExactSlabFixedSpatialJointPresentedLimitLaws.PresentedNormCauchy.mapTime hw0 hw1 width (X.imagPart hw0 hw1 width) time)

theorem mapTime_point (X : PresentedComplexCauchy hw0 hw1 width) (time p : Nat) :
    (X.mapTime hw0 hw1 width time).point hw0 hw1 width p =
      complexTime hw0 hw1 width time (X.point hw0 hw1 width p) := rfl

/-- The constructed complex norm limit commutes with the SAME transfer. -/
theorem mapTime_limit (X : PresentedComplexCauchy hw0 hw1 width) (time : Nat) :
    (X.mapTime hw0 hw1 width time).limit hw0 hw1 width =
      complexTime hw0 hw1 width time (X.limit hw0 hw1 width) := by
  rw [mapTime, ofComponents_limit, BF4ExactSlabFixedSpatialJointPresentedLimitLaws.PresentedNormCauchy.mapTime_limit,
    BF4ExactSlabFixedSpatialJointPresentedLimitLaws.PresentedNormCauchy.mapTime_limit]
  rfl

end PresentedComplexCauchy

end YMGap.Continuum.BF4ExactSlabFixedSpatialJointComplexPresentedCompleteness

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointComplexPresentedCompleteness.complexDistSq_components
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointComplexPresentedCompleteness.realDistSq_le_complex
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointComplexPresentedCompleteness.imagDistSq_le_complex
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointComplexPresentedCompleteness.PresentedComplexCauchy.realPart
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointComplexPresentedCompleteness.PresentedComplexCauchy.imagPart
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointComplexPresentedCompleteness.PresentedComplexCauchy.limit
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointComplexPresentedCompleteness.PresentedComplexCauchy.limit_converges
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointComplexPresentedCompleteness.CandidateLimit.eq_constructed_limit
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointComplexPresentedCompleteness.PresentedComplexCauchy.ofComponents_limit
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointComplexPresentedCompleteness.PresentedComplexCauchy.mapTime
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointComplexPresentedCompleteness.PresentedComplexCauchy.mapTime_point
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointComplexPresentedCompleteness.PresentedComplexCauchy.mapTime_limit
