/-
# A convergent regularized logarithm series on the ORIGINAL Wilson carrier

Construct the actual limit of sum_{k=1}^n (I-T)^k T x/k, using the SAME
completed time map and inner product. Each finite row has a constructed
Cauchy representative; both its inner modulus and the outer convergence
modulus remain data. Quotient descent uses equality of the finite rows,
not a choice of representatives.

This constructs the regularized series map, not an unbounded Hamiltonian,
an exponential/logarithm identity, a continuous-time semigroup, or a physical
mass bound. The original boundary kernel is retained. No new carrier or
spatial/scaling comparison is introduced.
-/

import YMGap.Continuum.BF4WilsonAllNomeLogPartial
import YMGap.Continuum.BF4WilsonAllNomeLogPartialLaws
import YMGap.Continuum.BF4WilsonAllNomeCauchyRows

namespace YMGap.Continuum.BF4WilsonAllNomeLogSeries

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicAlgebra (zero)
open YMGap.Continuum.BF4WilsonAllNomeSeminorm (seminorm)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4WilsonAllNomeLinear
open YMGap.Continuum.BF4WilsonAllNomeDistance
open YMGap.Continuum.BF4WilsonAllNomeCauchyRows
open YMGap.Continuum.BF4WilsonAllNomeTimeDefectMoments
open YMGap.Continuum.BF4WilsonAllNomePositiveTimeTail
open YMGap.Continuum.BF4WilsonAllNomeLogPartial
open YMGap.Continuum.BF4WilsonAllNomeLogPartialLaws
open YMGap.Continuum.CRealSeminormPairingCompletion
  (normCeiling normCeiling_nonnegative completedInner_diagonal_le_normCeiling)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "D" => seminorm hw0 hw1 (width := width)
local notation "PD" => pairingData hw0 hw1 (width := width)
local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "Class" => Quotient.mk
  (CRealSeminormCompletion.SquaredSeminorm.completionSetoid
    (seminorm hw0 hw1 (width := width)))
local notation "Rq" => fun q : Q' => Quotient.mk crealSetoid (ofQ' q)

/-- The actual defect on a supplied original representative, including its modulus. -/
def defectCauchy (X : (D).Cauchy) : (D).Cauchy :=
  differenceCauchy hw0 hw1 X ((timeNonexpansive hw0 hw1 1).mapCauchy X)

theorem defectCauchy_pin (X : (D).Cauchy) :
    Class (defectCauchy hw0 hw1 X) = defect hw0 hw1 (Class X) := rfl

def defectPowerCauchy : Nat → (D).Cauchy → (D).Cauchy
  | 0, X => X
  | n+1, X => defectCauchy hw0 hw1 (defectPowerCauchy n X)

theorem defectPowerCauchy_pin (n : Nat) (X : (D).Cauchy) :
    Class (defectPowerCauchy hw0 hw1 n X) = defectPower hw0 hw1 n (Class X) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change Class (defectCauchy hw0 hw1 (defectPowerCauchy hw0 hw1 n X)) = _
      rw [defectCauchy_pin, ih]
      rfl

def positiveTimeTailCauchy (n : Nat) (X : (D).Cauchy) : (D).Cauchy :=
  defectPowerCauchy hw0 hw1 n ((timeNonexpansive hw0 hw1 1).mapCauchy X)

theorem positiveTimeTailCauchy_pin (n : Nat) (X : (D).Cauchy) :
    Class (positiveTimeTailCauchy hw0 hw1 n X) = positiveTimeTail hw0 hw1 n (Class X) :=
  defectPowerCauchy_pin hw0 hw1 n _

def logTermCauchy (n : Nat) (X : (D).Cauchy) : (D).Cauchy :=
  (scalarContinuous hw0 hw1 (Q'.invSucc n)).mapCauchy
    (positiveTimeTailCauchy hw0 hw1 (n+1) X)

theorem logTermCauchy_pin (n : Nat) (X : (D).Cauchy) :
    Class (logTermCauchy hw0 hw1 n X) = logTerm hw0 hw1 n (Class X) := by
  change completedSmul hw0 hw1 (Q'.invSucc n)
    (Class (positiveTimeTailCauchy hw0 hw1 (n+1) X)) = _
  rw [positiveTimeTailCauchy_pin]
  rfl

def logTailCauchy : Nat → Nat → (D).Cauchy → (D).Cauchy
  | _, 0, _ => (D).constant (zero width)
  | start, len+1, X => (addition hw0 hw1).mapCauchy
      (logTermCauchy hw0 hw1 start X) (logTailCauchy (start+1) len X)

theorem logTailCauchy_pin (start len : Nat) (X : (D).Cauchy) :
    Class (logTailCauchy hw0 hw1 start len X) = logTail hw0 hw1 start len (Class X) := by
  induction len generalizing start with
  | zero => rfl
  | succ len ih =>
      change completedAdd hw0 hw1 (Class (logTermCauchy hw0 hw1 start X))
        (Class (logTailCauchy hw0 hw1 (start+1) len X)) = _
      rw [logTermCauchy_pin, ih]
      rfl

/-- The ceiling is computed from the supplied stream, not from a quotient choice. -/
def seriesModulus (X : (D).Cauchy) (epsilon : Q') : Nat :=
  max (normCeiling PD X).num.toNat epsilon.den

private theorem cap_tail_small (cap epsilon : Q') (hc : (0 : Q') ≤ cap)
    (he : (0 : Q') < epsilon) (n : Nat)
    (hn : max cap.num.toNat epsilon.den ≤ n) :
    (Q'.invSucc n * Q'.invSucc n) * cap ≤ epsilon := by
  have hcap : cap * Q'.invSucc n ≤ 1 :=
    Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ _
        (ExpNeg.invSucc_le_of_le (Nat.le_trans (Nat.le_max_left _ _) hn)) hc)
      (ExpNeg.mul_invSucc_toNat_le_one cap hc)
  have heq : Q'.eqv ((Q'.invSucc n * Q'.invSucc n)*cap)
      ((cap * Q'.invSucc n)*Q'.invSucc n) :=
    RingNormaliser.poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.var 0)) (.var 1))
      (.mul (.mul (.var 1) (.var 0)) (.var 0)) (by decide)
      (fun | 0 => Q'.invSucc n | _ => cap)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv heq) (Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ _ hcap (Q'.invSucc_nonneg n))
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.one_mul_eqv _))
      (Q'.le_trans' _ _ _
        (ExpNeg.invSucc_le_of_le (Nat.le_trans (Nat.le_max_right _ _) hn))
        (HalfPow.invSucc_den_le epsilon he))))

private theorem scale_rat (s t : Q') : RCscale s (Rq t) = Rq (s*t) :=
  Quotient.sound (CRealAlg.ofQ'_mul s t).symm

private theorem partial_distance_small (X : (D).Cauchy)
    (epsilon : Q') (he : (0 : Q') < epsilon) (m n : Nat)
    (hmn : m ≤ n) (hm : seriesModulus hw0 hw1 X epsilon ≤ m) :
    RCle (completedDist hw0 hw1 (logPartial hw0 hw1 m (Class X))
      (logPartial hw0 hw1 n (Class X))) (Rq epsilon) := by
  have h := RCle_trans (logPartial_ordered_distance_bound hw0 hw1 (Class X) m n hmn)
    (RCscale_mono (SumOfSquares.q_mul_self_nonneg (Q'.invSucc m))
      (completedInner_diagonal_le_normCeiling PD X))
  rw [scale_rat] at h
  exact RCle_trans h (leEv_le_ofQ'_of_approx_le (fun _ =>
    cap_tail_small (normCeiling PD X) epsilon (normCeiling_nonnegative PD X) he m hm))

/-- The finite polynomial rows with BOTH inner and outer moduli as data. -/
def logRows (X : (D).Cauchy) : RepresentedCauchy hw0 hw1 (width := width) where
  row := fun n => logTailCauchy hw0 hw1 0 n X
  modulus := seriesModulus hw0 hw1 X
  isCauchy := by
    intro epsilon he m n hm hn
    change RCle (completedDist hw0 hw1
      (Class (logTailCauchy hw0 hw1 0 m X))
      (Class (logTailCauchy hw0 hw1 0 n X))) _
    rw [logTailCauchy_pin, logTailCauchy_pin]
    change RCle (completedDist hw0 hw1 (logPartial hw0 hw1 m (Class X))
      (logPartial hw0 hw1 n (Class X))) _
    rcases Nat.le_total m n with hmn | hnm
    · exact partial_distance_small hw0 hw1 X epsilon he m n hmn hm
    · rw [completedDist_symm]
      exact partial_distance_small hw0 hw1 X epsilon he n m hnm hn

theorem logRows_point (X : (D).Cauchy) (n : Nat) :
    rowPoint hw0 hw1 (logRows hw0 hw1 X) n = logPartial hw0 hw1 n (Class X) :=
  logTailCauchy_pin hw0 hw1 0 n X

/-- Actual limit on the pre-existing quotient, independent of its presentation. -/
def regularizedLog : V → V :=
  Quotient.lift (fun X => limit hw0 hw1 (logRows hw0 hw1 X)) (fun X Y h => by
    apply limit_independent hw0 hw1
    intro n
    rw [logRows_point, logRows_point, Quotient.sound h])

theorem regularizedLog_mk (X : (D).Cauchy) :
    regularizedLog hw0 hw1 (Class X) = limit hw0 hw1 (logRows hw0 hw1 X) := rfl

/-- Includes the generic represented-limit epsilon/16 loss explicitly. -/
def convergenceModulus (X : (D).Cauchy) (epsilon : Q') : Nat :=
  limitRate hw0 hw1 (logRows hw0 hw1 X) epsilon

theorem regularizedLog_approximation (X : (D).Cauchy)
    (epsilon : Q') (he : (0 : Q') < epsilon) (n : Nat)
    (hn : convergenceModulus hw0 hw1 X epsilon ≤ n) :
    RCle (completedDist hw0 hw1 (logPartial hw0 hw1 n (Class X))
      (regularizedLog hw0 hw1 (Class X))) (Rq epsilon) := by
  rw [regularizedLog_mk, ← logRows_point]
  exact limit_bound hw0 hw1 (logRows hw0 hw1 X) epsilon he n hn

/-- The original carrier element AND its quantitative convergence witness. -/
def regularizedLogCertificate (X : (D).Cauchy) :
    Σ' y : V, Σ' modulus : Q' → Nat,
      (y = regularizedLog hw0 hw1 (Class X)) ×'
      (∀ epsilon, (0 : Q') < epsilon → ∀ n, modulus epsilon ≤ n →
        RCle (completedDist hw0 hw1 (logPartial hw0 hw1 n (Class X)) y)
          (Rq epsilon)) :=
  ⟨regularizedLog hw0 hw1 (Class X), convergenceModulus hw0 hw1 X, rfl,
    regularizedLog_approximation hw0 hw1 X⟩

/-- The computed series limit commutes with every ORIGINAL discrete time map. -/
theorem regularizedLog_commutes_time (time : Nat) (x : V) :
    regularizedLog hw0 hw1 (completedTime hw0 hw1 time x) =
      completedTime hw0 hw1 time (regularizedLog hw0 hw1 x) := by
  refine Quotient.inductionOn x ?_
  intro X
  change limit hw0 hw1 (logRows hw0 hw1
    ((timeNonexpansive hw0 hw1 time).mapCauchy X)) =
      completedTime hw0 hw1 time (limit hw0 hw1 (logRows hw0 hw1 X))
  rw [← limit_timeRows]
  apply limit_independent hw0 hw1
  intro n
  rw [logRows_point, timeRows_rowPoint, logRows_point]
  exact logPartial_commutes_time hw0 hw1 n time (Class X)

private theorem regularizedLog_zero_of_partials_zero (x : V)
    (h : ∀ n, logPartial hw0 hw1 n x = completedZero hw0 hw1 width) :
    regularizedLog hw0 hw1 x = completedZero hw0 hw1 width := by
  revert h
  refine Quotient.inductionOn x ?_
  intro X h
  rw [regularizedLog_mk]
  apply limit_unique hw0 hw1 (logRows hw0 hw1 X)
    (completedZero hw0 hw1 width) (fun _ => 0)
  intro epsilon he n _
  rw [logRows_point, h n,
    (completedDist_zero_iff hw0 hw1 _ _).mpr rfl]
  exact leEv_le_ofQ'_of_approx_le (fun _ => Q'.le_of_lt he)

/-- The actual one-step kernel is retained, not removed from the carrier. -/
theorem regularizedLog_kernel_zero (x : V)
    (hx : completedTime hw0 hw1 1 x = completedZero hw0 hw1 width) :
    regularizedLog hw0 hw1 x = completedZero hw0 hw1 width :=
  regularizedLog_zero_of_partials_zero hw0 hw1 x
    (fun n => logPartial_kernel_zero hw0 hw1 n x hx)

/-- The actual normalized vacuum is annihilated by the computed limit. -/
theorem regularizedLog_unit_zero :
    regularizedLog hw0 hw1 (unitState hw0 hw1 width) =
      completedZero hw0 hw1 width :=
  regularizedLog_zero_of_partials_zero hw0 hw1 (unitState hw0 hw1 width)
    (fun n => logPartial_unit_zero hw0 hw1 n)

#print axioms defectCauchy
#print axioms defectCauchy_pin
#print axioms defectPowerCauchy
#print axioms defectPowerCauchy_pin
#print axioms positiveTimeTailCauchy
#print axioms positiveTimeTailCauchy_pin
#print axioms logTermCauchy
#print axioms logTermCauchy_pin
#print axioms logTailCauchy
#print axioms logTailCauchy_pin
#print axioms seriesModulus
#print axioms logRows
#print axioms logRows_point
#print axioms regularizedLog
#print axioms regularizedLog_mk
#print axioms convergenceModulus
#print axioms regularizedLog_approximation
#print axioms regularizedLogCertificate
#print axioms regularizedLog_commutes_time
#print axioms regularizedLog_kernel_zero
#print axioms regularizedLog_unit_zero

end YMGap.Continuum.BF4WilsonAllNomeLogSeries
