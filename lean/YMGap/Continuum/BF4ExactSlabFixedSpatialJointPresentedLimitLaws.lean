/-
# Uniqueness and time covariance of represented joint norm limits

Represented norm-Cauchy families on the actual fixed-width joint reflected
completion have a unique limit among candidates supplied with representatives
and explicit convergence moduli.  The existing discrete physical-time
nonexpansive map preserves these represented limits.

No representative is selected from a quotient point.  The results concern
represented completeness only, at fixed nome and width; they do not construct
an arbitrary quotient lift, continuous-time generator, or continuum theory.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialJointPresentedCompleteness

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialJointPresentedLimitLaws

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.CRealSeminormCompletion
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointSeminorm
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointPhysicalTime
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointLinear
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointPresentedCompleteness

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (width : Nat)

local notation "D" => jointSeminorm hw0 hw1 width
local notation "V" => JointCompletion hw0 hw1 width

private def quarter (epsilon : Q') : Q' :=
  HalfPow.half * (HalfPow.half * epsilon)

private theorem quarter_pos {epsilon : Q'} (he : (0 : Q') < epsilon) :
    (0 : Q') < quarter epsilon :=
  ExpNeg.half_mul_pos _ (ExpNeg.half_mul_pos epsilon he)

private theorem four_quarters (epsilon : Q') :
    ((quarter epsilon + quarter epsilon) +
      (quarter epsilon + quarter epsilon)).eqv epsilon := by
  have h : (quarter epsilon + quarter epsilon).eqv (HalfPow.half * epsilon) :=
    ExpNeg.two_halves (HalfPow.half * epsilon)
  exact Q'.eqv_trans _ _ _ (QPoly.q_add_congr h h) (ExpNeg.two_halves epsilon)

/-- A candidate represented limit for the supplied norm-Cauchy family.  Its
representative and convergence modulus are data. -/
structure CandidateLimit
    (X : PresentedNormCauchy hw0 hw1 width) where
  representative : (D).Cauchy
  modulus : Q' → Nat
  converges : ∀ epsilon, (0 : Q') < epsilon → ∀ p, modulus epsilon ≤ p →
    RCle (completedDistSq hw0 hw1 width
        (Quotient.mk (D).completionSetoid (X.pt p))
        (Quotient.mk (D).completionSetoid representative))
      (Quotient.mk crealSetoid (ofQ' epsilon))

namespace CandidateLimit

variable (X : PresentedNormCauchy hw0 hw1 width)

/-- Explicit outer point used to compare a candidate with the constructed
diagonal limit. -/
def comparisonPoint (C : CandidateLimit hw0 hw1 width X) (epsilon : Q') : Nat :=
  max (C.modulus (HalfPow.half * quarter epsilon))
    (X.limitRate hw0 hw1 width (HalfPow.half * quarter epsilon))

/-- Explicit inner rate at the common outer comparison point. -/
def comparisonInnerRate (C : CandidateLimit hw0 hw1 width X) (epsilon : Q') : Nat :=
  let p := C.comparisonPoint hw0 hw1 width X epsilon
  max (distanceRate hw0 hw1 width (X.pt p) C.representative
      (HalfPow.half * quarter epsilon))
    (distanceRate hw0 hw1 width (X.pt p)
      (X.toPresented hw0 hw1 width).diagonal (HalfPow.half * quarter epsilon))

/-- The supplied candidate representative is asymptotically close to the
constructed diagonal representative, with no quotient representative choice. -/
def closeDiagonal (C : CandidateLimit hw0 hw1 width X) :
    (D).Close C.representative (X.toPresented hw0 hw1 width).diagonal where
  modulus := C.comparisonInnerRate hw0 hw1 width X
  close := by
    intro epsilon he n hn
    let t := quarter epsilon
    let p := C.comparisonPoint hw0 hw1 width X epsilon
    have ht : (0 : Q') < t := quarter_pos he
    have hh : (0 : Q') < HalfPow.half * t := ExpNeg.half_mul_pos t ht
    have hpC : C.modulus (HalfPow.half * t) ≤ p := Nat.le_max_left _ _
    have hpX : X.limitRate hw0 hw1 width (HalfPow.half * t) ≤ p :=
      Nat.le_max_right _ _
    have hnC : distanceRate hw0 hw1 width (X.pt p) C.representative
        (HalfPow.half * t) ≤ n :=
      Nat.le_trans (Nat.le_max_left _ _) hn
    have hnX : distanceRate hw0 hw1 width (X.pt p)
        (X.toPresented hw0 hw1 width).diagonal (HalfPow.half * t) ≤ n :=
      Nat.le_trans (Nat.le_max_right _ _) hn
    have hC := late_distSq_le hw0 hw1 width (X.pt p) C.representative t ht
      (C.converges (HalfPow.half * t) hh p hpC) n hnC
    have hX := late_distSq_le hw0 hw1 width (X.pt p)
      (X.toPresented hw0 hw1 width).diagonal t ht
      (X.limit_converges hw0 hw1 width (HalfPow.half * t) hh p hpX) n hnX
    have hCs : leEv ((D).distSq (C.representative.seq n) ((X.pt p).seq n))
        (ofQ' t) :=
      leEv_trans (leEv_of_equiv ((D).distSq_symm _ _)) hC
    have htri := leEv_trans
      ((D).distSq_triangle (C.representative.seq n) ((X.pt p).seq n)
        ((X.toPresented hw0 hw1 width).diagonal.seq n))
      (leEv_add (leEv_add hCs hCs) (leEv_add hX hX))
    exact leEv_trans htri
      (leEv_of_equiv (ofQ'_equiv_of_eqv (four_quarters epsilon)))

/-- Uniqueness of the represented norm limit. -/
theorem eq_constructed_limit (C : CandidateLimit hw0 hw1 width X) :
    Quotient.mk (D).completionSetoid C.representative = X.limit hw0 hw1 width := by
  exact Quotient.sound ⟨C.closeDiagonal hw0 hw1 width X⟩

end CandidateLimit

namespace PresentedNormCauchy

variable (X : PresentedNormCauchy hw0 hw1 width)

/-- Map every supplied representative through the actual nonexpansive
discrete-time action. -/
def mapTime (time : Nat) : PresentedNormCauchy hw0 hw1 width where
  pt p := (jointTimeNonexpansive hw0 hw1 width time).mapCauchy (X.pt p)
  modulus epsilon := X.modulus (HalfPow.half * epsilon)
  cauchy := by
    intro epsilon he p q hp hq
    apply completedDistSq_le_of_eventual hw0 hw1 width
      ((jointTimeNonexpansive hw0 hw1 width time).mapCauchy (X.pt p))
      ((jointTimeNonexpansive hw0 hw1 width time).mapCauchy (X.pt q)) epsilon
      (distanceRate hw0 hw1 width (X.pt p) (X.pt q) (HalfPow.half * epsilon))
    intro n hn
    exact leEv_trans
      (jointPhysicalTime_contraction hw0 hw1 width time ((X.pt p).seq n) ((X.pt q).seq n))
      (late_distSq_le hw0 hw1 width (X.pt p) (X.pt q) epsilon he
        (X.cauchy (HalfPow.half * epsilon) (ExpNeg.half_mul_pos epsilon he)
          p q hp hq) n hn)

/-- The time image of the constructed diagonal is a represented candidate
limit of the time-mapped family. -/
def timeCandidate (time : Nat) :
    CandidateLimit hw0 hw1 width (mapTime hw0 hw1 width X time) where
  representative :=
    (jointTimeNonexpansive hw0 hw1 width time).mapCauchy
      (X.toPresented hw0 hw1 width).diagonal
  modulus epsilon := X.limitRate hw0 hw1 width (HalfPow.half * epsilon)
  converges := by
    intro epsilon he p hp
    apply completedDistSq_le_of_eventual hw0 hw1 width
      ((jointTimeNonexpansive hw0 hw1 width time).mapCauchy (X.pt p))
      ((jointTimeNonexpansive hw0 hw1 width time).mapCauchy
        (X.toPresented hw0 hw1 width).diagonal) epsilon
      (distanceRate hw0 hw1 width (X.pt p)
        (X.toPresented hw0 hw1 width).diagonal (HalfPow.half * epsilon))
    intro n hn
    exact leEv_trans
      (jointPhysicalTime_contraction hw0 hw1 width time ((X.pt p).seq n)
        ((X.toPresented hw0 hw1 width).diagonal.seq n))
      (late_distSq_le hw0 hw1 width (X.pt p)
        (X.toPresented hw0 hw1 width).diagonal epsilon he
        (X.limit_converges hw0 hw1 width (HalfPow.half * epsilon)
          (ExpNeg.half_mul_pos epsilon he) p hp) n hn)

/-- Constructed represented limits commute with the actual discrete physical
time action on the SAME joint completion. -/
theorem mapTime_limit (time : Nat) :
    (mapTime hw0 hw1 width X time).limit hw0 hw1 width =
      jointCompletedTime hw0 hw1 width time (X.limit hw0 hw1 width) := by
  have h := (timeCandidate hw0 hw1 width X time).eq_constructed_limit
    hw0 hw1 width (mapTime hw0 hw1 width X time)
  exact h.symm

end PresentedNormCauchy

end YMGap.Continuum.BF4ExactSlabFixedSpatialJointPresentedLimitLaws

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointPresentedLimitLaws.CandidateLimit.closeDiagonal
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointPresentedLimitLaws.CandidateLimit.eq_constructed_limit
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointPresentedLimitLaws.PresentedNormCauchy.mapTime
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointPresentedLimitLaws.PresentedNormCauchy.timeCandidate
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointPresentedLimitLaws.PresentedNormCauchy.mapTime_limit
