/-
# ORIGINAL completed geometric time and its positive two-step transfer

The proved OS-distance contraction translates every supplied Cauchy sequence
without changing its modulus. Quotient descent therefore acts on the EXISTING
original thermodynamic completion. The actual dense translated states are
retained, as are composition, linearity, symmetry, the unit and its complement.
The original completed norm and distance are nonincreasing at every lag.

Two steps give a positive symmetric contraction with the original same-object
moments. These results hold at nome 1/1024 and fixed lattice spacing. The unit
is fixed, but nonzero excitations, its uniqueness/isolation, a strict gap,
full required observables/completeness and the continuum Clay target remain
open. No conditional surrogate dynamics or gap premise is used.
-/

import YMGap.Continuum.BF4ExactSlabThermodynamicTimeContraction

namespace YMGap.Continuum.BF4ExactSlabThermodynamicCompletedTime

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabThermodynamicPresentation
open YMGap.Continuum.BF4ExactSlabThermodynamicLowerFunctional
open YMGap.Continuum.BF4ExactSlabThermodynamicReflectedObservable
open YMGap.Continuum.BF4ExactSlabThermodynamicNullQuotient
open YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion
open YMGap.Continuum.BF4ExactSlabThermodynamicPairingLimit
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedInner
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletionLinear
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedBilinear
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedGeometry
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedRealScalar
open YMGap.Continuum.BF4ExactSlabThermodynamicCenteredCompletion
open YMGap.Continuum.BF4ExactSlabThermodynamicTimeGeometry
open YMGap.Continuum.BF4ExactSlabThermodynamicTimeAlgebra
open YMGap.Continuum.BF4ExactSlabThermodynamicTimeStates
open YMGap.Continuum.BF4ExactSlabThermodynamicTimeCorrelations
open YMGap.Continuum.BF4ExactSlabThermodynamicDenseTime
open YMGap.Continuum.BF4ExactSlabThermodynamicTimeContraction

local notation "D" => seminorm
local notation "B" => completedInner

def timeCauchy (lag : Nat) (X : (D).Cauchy) : (D).Cauchy :=
  (timeNonexpansive lag).mapCauchy X

theorem timeCauchy_modulus (lag : Nat) (X : (D).Cauchy) :
    (timeCauchy lag X).modulus = X.modulus := rfl

def completedTime (lag : Nat) : Completion → Completion :=
  (timeNonexpansive lag).completionMap

theorem completedTime_mk (lag : Nat) (X : (D).Cauchy) :
    completedTime lag (Quotient.mk (D).completionSetoid X) =
      Quotient.mk (D).completionSetoid (timeCauchy lag X) := rfl

theorem completedTime_embedPresentation (lag : Nat) (p : Presentation) :
    completedTime lag (embedPresentation p) = timeState lag p := rfl

theorem completedTime_embedOSQuotient (lag : Nat) (x : Carrier) :
    completedTime lag (embedOSQuotient x) = embedOSQuotient (denseTime lag x) := by
  refine Quotient.inductionOn x ?_
  intro o
  refine Quotient.inductionOn o ?_
  exact fun _ => rfl

theorem completedTime_zero (x : Completion) : completedTime 0 x = x := by
  refine Quotient.inductionOn x ?_
  intro X
  exact completion_eq_of_pointwise (fun k => timeObservable_zero (X.seq k))

theorem completedTime_comp (s t : Nat) (x : Completion) :
    completedTime t (completedTime s x) = completedTime (s+t) x := by
  refine Quotient.inductionOn x ?_
  intro X
  exact completion_eq_of_pointwise (fun k => timeObservable_comp s t (X.seq k))

theorem completedTime_add (lag : Nat) (x y : Completion) :
    completedTime lag (completedAdd x y) = completedAdd (completedTime lag x) (completedTime lag y) := by
  refine Quotient.inductionOn₂ x y ?_
  intro X Y
  exact completion_eq_of_pointwise (fun k => timeObservable_add lag (X.seq k) (Y.seq k))

theorem completedTime_smul (lag : Nat) (c : Q') (x : Completion) :
    completedTime lag (completedSmul c x) = completedSmul c (completedTime lag x) := by
  refine Quotient.inductionOn x ?_
  intro X
  exact completion_eq_of_pointwise (fun k => timeObservable_smul lag c (X.seq k))

theorem completedTime_unit (lag : Nat) : completedTime lag completedUnit = completedUnit := by
  change completedTime lag (embedOSQuotient osUnit) = embedOSQuotient osUnit
  rw [completedTime_embedOSQuotient, denseTime_unit]

theorem completedTime_zeroState (lag : Nat) : completedTime lag completedZero = completedZero := by
  calc
    completedTime lag completedZero = completedTime lag (completedSmul 0 completedUnit) :=
      congrArg (completedTime lag) (completedSmul_zero completedUnit).symm
    _ = completedSmul 0 (completedTime lag completedUnit) := completedTime_smul lag 0 completedUnit
    _ = completedZero := completedSmul_zero _

theorem presentedForm_time_symmetric (lag : Nat) (p q : Presentation) :
    Equiv (presentedForm (translate lag p) q) (presentedForm p (translate lag q)) :=
  Quotient.exact (denseTime_symmetric lag (project (embed p)) (project (embed q)))

theorem representativeInner_time_symmetric (lag : Nat) (X Y : (D).Cauchy) :
    Equiv (representativeInner (timeCauchy lag X) Y) (representativeInner X (timeCauchy lag Y)) :=
  Equiv_of_limit_of_equal (fun k => presentedForm_time_symmetric lag (X.seq k) (Y.seq k))
    (pairSequence_converges (timeCauchy lag X) Y) (pairSequence_converges X (timeCauchy lag Y))

theorem completedTime_symmetric (lag : Nat) (x y : Completion) :
    B (completedTime lag x) y = B x (completedTime lag y) := by
  refine Quotient.inductionOn₂ x y ?_
  exact fun X Y => Quotient.sound (representativeInner_time_symmetric lag X Y)

theorem representativeInner_time_contraction (lag : Nat) (X : (D).Cauchy) :
    leEv (representativeInner (timeCauchy lag X) (timeCauchy lag X)) (representativeInner X X) := by
  apply leEv_of_convergesTo_le (pairSequence_converges (timeCauchy lag X) (timeCauchy lag X))
    (pairSequence_converges X X)
  intro k
  have h := timeNorm_le_anchor lag (X.seq k)
  simpa only [timeNorm, translate_zero] using h

theorem completedTime_contraction (lag : Nat) (x : Completion) :
    RCle (B (completedTime lag x) (completedTime lag x)) (B x x) := by
  refine Quotient.inductionOn x ?_
  exact representativeInner_time_contraction lag

theorem representativeDist_time_contraction (lag : Nat) (X Y : (D).Cauchy) :
    leEv (representativeDist (timeCauchy lag X) (timeCauchy lag Y)) (representativeDist X Y) :=
  leEv_of_convergesTo_le
    (representativeDist_converges (timeCauchy lag X) (timeCauchy lag Y))
    (representativeDist_converges X Y) (fun k => distSq_translate lag (X.seq k) (Y.seq k))

theorem completedTime_distance_contraction (lag : Nat) (x y : Completion) :
    RCle (completedDist (completedTime lag x) (completedTime lag y)) (completedDist x y) := by
  refine Quotient.inductionOn₂ x y ?_
  exact representativeDist_time_contraction lag

theorem completedTime_realSmul (lag : Nat) (s : CReal) (cs : QCauchy s.approx) (x : Completion) :
    completedTime lag (completedRealSmul s cs x) = completedRealSmul s cs (completedTime lag x) := by
  apply completed_eq_of_pairings
  intro z
  rw [completedTime_symmetric, completedInner_realSmul_left,
    completedInner_realSmul_left, completedTime_symmetric]

theorem completedTime_mean (lag : Nat) (x : Completion) :
    B (completedTime lag x) completedUnit = B x completedUnit := by
  rw [completedTime_symmetric, completedTime_unit]

theorem completedTime_moments (s t : Nat) (x y : Completion) :
    B (completedTime s x) (completedTime t y) = B x (completedTime (s+t) y) := by
  rw [completedTime_symmetric, completedTime_comp, Nat.add_comm t s]

theorem completedTime_even_nonnegative (lag : Nat) (x : Completion) :
    RCnonneg (B x (completedTime (lag+lag) x)) := by
  rw [← completedTime_moments]
  exact completedInner_nonnegative _

theorem completedTime_center (lag : Nat) (x : Completion) :
    completedTime lag (center x) = center (completedTime lag x) := by
  apply completed_eq_of_pairings
  intro z
  rw [completedTime_symmetric, center_pairing, center_pairing, completedTime_mean,
    completedInner_symm completedUnit (completedTime lag z), completedTime_mean,
    completedInner_symm z completedUnit, completedTime_symmetric]

def complementTime (lag : Nat) (x : UnitComplement) : UnitComplement :=
  ⟨completedTime lag x.val, by rw [completedTime_mean]; exact x.property⟩

theorem complementTime_contraction (lag : Nat) (x : UnitComplement) :
    RCle (B (complementTime lag x).val (complementTime lag x).val) (B x.val x.val) :=
  completedTime_contraction lag x.val

theorem complementTime_centeredState (lag : Nat) (p : Presentation) :
    complementTime lag (centeredState (embedPresentation p)) = centeredTimeState lag p := by
  apply Subtype.ext
  exact (completedTime_center lag (embedPresentation p)).trans
    (congrArg center (completedTime_embedPresentation lag p))

/-- The original connected-correlation limit is a moment of THIS operator. -/
theorem timeCovariance_operator (s t : Nat) (p q : Presentation) :
    timeCovariance s t p q =
      B (completedTime s (center (embedPresentation p))) (completedTime t (center (embedPresentation q))) := by
  rw [completedTime_center, completedTime_center,
    completedTime_embedPresentation, completedTime_embedPresentation]
  rfl

theorem timeCovariance_operator_sum (s t : Nat) (p q : Presentation) :
    timeCovariance s t p q =
      B (center (embedPresentation p)) (completedTime (s+t) (center (embedPresentation q))) := by
  rw [timeCovariance_operator, completedTime_moments]

/-- Two units of the actual lattice time, not a heat-bath generator. -/
def twoStepTransfer : Completion → Completion := completedTime 2

theorem twoStepTransfer_advance (n : Nat) (x : Completion) :
    twoStepTransfer (completedTime (2*n) x) = completedTime (2*(n+1)) x := by
  change completedTime 2 (completedTime (2*n) x) = _
  rw [completedTime_comp, Nat.mul_add]

theorem twoStepTransfer_symmetric (x y : Completion) :
    B (twoStepTransfer x) y = B x (twoStepTransfer y) := completedTime_symmetric 2 x y

theorem twoStepTransfer_positive (x : Completion) : RCnonneg (B x (twoStepTransfer x)) :=
  completedTime_even_nonnegative 1 x

theorem twoStepTransfer_contraction (x : Completion) :
    RCle (B (twoStepTransfer x) (twoStepTransfer x)) (B x x) := completedTime_contraction 2 x

theorem twoStepTransfer_unit : twoStepTransfer completedUnit = completedUnit := completedTime_unit 2

end YMGap.Continuum.BF4ExactSlabThermodynamicCompletedTime

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletedTime.timeCauchy
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletedTime.timeCauchy_modulus
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletedTime.completedTime
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletedTime.completedTime_mk
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletedTime.completedTime_embedPresentation
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletedTime.completedTime_embedOSQuotient
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletedTime.completedTime_zero
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletedTime.completedTime_comp
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletedTime.completedTime_add
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletedTime.completedTime_smul
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletedTime.completedTime_unit
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletedTime.completedTime_zeroState
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletedTime.presentedForm_time_symmetric
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletedTime.representativeInner_time_symmetric
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletedTime.completedTime_symmetric
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletedTime.representativeInner_time_contraction
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletedTime.completedTime_contraction
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletedTime.representativeDist_time_contraction
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletedTime.completedTime_distance_contraction
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletedTime.completedTime_realSmul
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletedTime.completedTime_mean
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletedTime.completedTime_moments
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletedTime.completedTime_even_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletedTime.completedTime_center
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletedTime.complementTime
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletedTime.complementTime_contraction
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletedTime.complementTime_centeredState
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletedTime.timeCovariance_operator
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletedTime.timeCovariance_operator_sum
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletedTime.twoStepTransfer
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletedTime.twoStepTransfer_advance
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletedTime.twoStepTransfer_symmetric
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletedTime.twoStepTransfer_positive
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletedTime.twoStepTransfer_contraction
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletedTime.twoStepTransfer_unit
