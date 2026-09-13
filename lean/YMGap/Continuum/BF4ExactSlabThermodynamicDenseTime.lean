/-
# Geometric time translation descends to the ORIGINAL dense OS state space

The same-object moment identity gives ||T^t p||^2 = B(p,T^(2t)p).
Thus a null input has a null translated output, by positive definiteness,
without presuming contraction. Linearity gives independence of OS-equivalent
presentations. Two quotient lifts define a time semigroup on the EXISTING
original OS null quotient, not a replacement state space.

The dense operators retain the original translated completed-state pin,
linearity, symmetry, unit and original mean. No arbitrary representative is
selected. Norm-relative boundedness and extension to the completion remain
open, as do strict gap, continuum construction and the Clay target.
-/

import YMGap.Continuum.BF4ExactSlabThermodynamicTimeBalance

namespace YMGap.Continuum.BF4ExactSlabThermodynamicDenseTime

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabThermodynamicPresentation
open YMGap.Continuum.BF4ExactSlabThermodynamicLowerFunctional
open YMGap.Continuum.BF4ExactSlabThermodynamicNullQuotient
open YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedInner
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedPosdef
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletionLinear
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedBilinear
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedGeometry
open YMGap.Continuum.BF4ExactSlabThermodynamicTimeGeometry
open YMGap.Continuum.BF4ExactSlabThermodynamicTimeAlgebra
open YMGap.Continuum.BF4ExactSlabThermodynamicTimeStates
open YMGap.Continuum.BF4ExactSlabThermodynamicTimeBalance

local notation "B" => completedInner

theorem timeState_subtract (lag : Nat) (p q : Presentation) :
    timeState lag (presentationSubtract p q) = completedSub (timeState lag p) (timeState lag q) := by
  unfold presentationSubtract completedSub completedNeg
  rw [timeState_add, timeState_smul]

/-- Null preservation follows from reflection and positivity, not a contraction premise. -/
theorem timeState_of_zero (lag : Nat) (p : Presentation) (h : embedPresentation p = completedZero) :
    timeState lag p = completedZero := by
  apply (completedInner_posdef _).mp
  rw [time_sum lag lag p p, timeState_zero, h, completedInner_zero_left]

private theorem embedPresentation_subtract (p q : Presentation) :
    embedPresentation (presentationSubtract p q) = completedSub (embedPresentation p) (embedPresentation q) := by
  unfold presentationSubtract completedSub completedNeg
  rw [completedSmul_embedPresentation, completedAdd_embedPresentation]

theorem timeState_congr (lag : Nat) {p q : Presentation} (h : embedPresentation p = embedPresentation q) :
    timeState lag p = timeState lag q := by
  apply (completedDist_zero_iff _ _).mp
  change B (completedSub (timeState lag p) (timeState lag q)) (completedSub (timeState lag p) (timeState lag q)) = RCzero
  rw [← timeState_subtract]
  apply (completedInner_posdef _).mpr
  apply timeState_of_zero
  rw [embedPresentation_subtract, h, completedSub_self]

/-- Semantic observables map to actual OS states; no preservation of a stronger
state-independent observable relation is asserted. -/
def semanticTime (lag : Nat) : Observable → Carrier :=
  Quotient.lift (fun p => project (timeObservable lag p)) (fun p q h => by
    apply embedOSQuotient_injective
    exact timeState_congr lag (congrArg embedObservable (Quotient.sound h)))

theorem semanticTime_embed (lag : Nat) (p : Presentation) :
    semanticTime lag (embed p) = project (timeObservable lag p) := rfl

theorem semanticTime_null (lag : Nat) {x y : Observable} (h : Null x y) :
    semanticTime lag x = semanticTime lag y := by
  revert h
  refine Quotient.inductionOn₂ x y ?_
  intro p q h
  apply embedOSQuotient_injective
  exact timeState_congr lag ((embedObservable_eq_iff (embed p) (embed q)).mpr h)

/-- The EXISTING original OS null quotient carries the actual time semigroup. -/
def denseTime (lag : Nat) : Carrier → Carrier :=
  Quotient.lift (semanticTime lag) (fun _ _ h => semanticTime_null lag h)

theorem denseTime_presented (lag : Nat) (p : Presentation) :
    denseTime lag (project (embed p)) = project (timeObservable lag p) := rfl

theorem denseTime_completed_pin (lag : Nat) (p : Presentation) :
    embedOSQuotient (denseTime lag (project (embed p))) = timeState lag p := rfl

theorem denseTime_zero (x : Carrier) : denseTime 0 x = x := by
  refine Quotient.inductionOn x ?_
  intro o
  refine Quotient.inductionOn o ?_
  intro p
  change project (timeObservable 0 p) = project (embed p)
  rw [timeObservable_zero]

theorem denseTime_comp (s t : Nat) (x : Carrier) : denseTime t (denseTime s x) = denseTime (s+t) x := by
  refine Quotient.inductionOn x ?_
  intro o
  refine Quotient.inductionOn o ?_
  intro p
  change project (timeObservable t (translate s p)) = project (timeObservable (s+t) p)
  rw [timeObservable_comp]

theorem denseTime_add (lag : Nat) (x y : Carrier) :
    denseTime lag (osAdd x y) = osAdd (denseTime lag x) (denseTime lag y) := by
  refine Quotient.inductionOn₂ x y ?_
  intro a b
  refine Quotient.inductionOn₂ a b ?_
  intro p q
  change project (timeObservable lag (add p q)) = project (qadd (timeObservable lag p) (timeObservable lag q))
  rw [timeObservable_add]

theorem denseTime_smul (lag : Nat) (c : Q') (x : Carrier) :
    denseTime lag (osSmul c x) = osSmul c (denseTime lag x) := by
  refine Quotient.inductionOn x ?_
  intro o
  refine Quotient.inductionOn o ?_
  intro p
  change project (timeObservable lag (smul c p)) = project (qsmul c (timeObservable lag p))
  rw [timeObservable_smul]

theorem denseTime_unit (lag : Nat) : denseTime lag osUnit = osUnit := by
  change project (timeObservable lag one) = project unit
  rw [timeObservable_one]

theorem denseTime_mean (lag : Nat) (x : Carrier) : unitCoefficient (denseTime lag x) = unitCoefficient x := by
  refine Quotient.inductionOn x ?_
  intro o
  refine Quotient.inductionOn o ?_
  exact fun p => value_timeObservable lag p

/-- Symmetry on the dense OS carrier, not self-adjointness on a completed domain. -/
theorem denseTime_symmetric (lag : Nat) (x y : Carrier) : inner (denseTime lag x) y = inner x (denseTime lag y) := by
  refine Quotient.inductionOn₂ x y ?_
  intro a b
  refine Quotient.inductionOn₂ a b ?_
  intro p q
  have h := time_sum lag 0 p q
  rw [Nat.add_zero, timeState_zero, timeState_zero] at h
  exact (completedInner_embedOSQuotient (project (timeObservable lag p)) (project (embed q))).symm.trans
    (h.trans (completedInner_embedOSQuotient (project (embed p)) (project (timeObservable lag q))))

theorem denseTime_moments (s t : Nat) (x y : Carrier) :
    inner (denseTime s x) (denseTime t y) = inner x (denseTime (s+t) y) := by
  rw [denseTime_symmetric, denseTime_comp, Nat.add_comm t s]

end YMGap.Continuum.BF4ExactSlabThermodynamicDenseTime

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDenseTime.timeState_subtract
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDenseTime.timeState_of_zero
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDenseTime.timeState_congr
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDenseTime.semanticTime
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDenseTime.semanticTime_embed
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDenseTime.semanticTime_null
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDenseTime.denseTime
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDenseTime.denseTime_presented
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDenseTime.denseTime_completed_pin
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDenseTime.denseTime_zero
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDenseTime.denseTime_comp
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDenseTime.denseTime_add
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDenseTime.denseTime_smul
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDenseTime.denseTime_unit
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDenseTime.denseTime_mean
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDenseTime.denseTime_symmetric
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDenseTime.denseTime_moments
