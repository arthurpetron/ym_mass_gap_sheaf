/-
# Constructed scalar dual test on the ORIGINAL thermodynamic completion

The coefficient-one original-distance estimate makes test values on every
supplied original Cauchy sequence Cauchy, with an explicit scalar modulus.
Their diagonal CReal limit is independent of the supplied representative.
It therefore defines a bounded rational-linear test on the EXISTING original
completion, with exact presentation, observable and OS-quotient pins.

All limits use the already constructed scalar test and the original squared
distance/inner product. No Hilbert representation theorem, state-algebra
recoding, separating-family premise, time-preimage or spectral assertion is
introduced. An actual-transfer comparison remains a separate obligation.
-/

import YMGap.Continuum.BF4ExactSlabBulkScalarQuotientTest
import YMGap.Continuum.BF4ExactSlabThermodynamicCompletedGeometry

namespace YMGap.Continuum.BF4ExactSlabBulkScalarCompletedTest

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabBulkScalarThermodynamicTest (meanLimit meanLimitCauchy)
open YMGap.Continuum.BF4ExactSlabBulkScalarQuotientTest
open YMGap.Continuum.BF4ExactSlabThermodynamicPresentation
open YMGap.Continuum.BF4ExactSlabThermodynamicLowerFunctional
open YMGap.Continuum.BF4ExactSlabThermodynamicReflectedObservable
open YMGap.Continuum.BF4ExactSlabThermodynamicNullQuotient
open YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion
open YMGap.Continuum.BF4ExactSlabThermodynamicPairingLimit
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedInner
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletionLinear
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedGeometry

local notation "D" => seminorm

def testSequence (X : (D).Cauchy) (n : Nat) : CReal := meanLimit (X.seq n).expression

def rawRate (X : (D).Cauchy) (epsilon : Q') : Nat := X.modulus (testTolerance epsilon)

theorem testSequence_raw_bound (X : (D).Cauchy) : LeRatBound (testSequence X) (rawRate X) :=
  fun epsilon he m n hm hn => presentedTest_close (X.seq m) (X.seq n) epsilon he
    (X.isCauchy (testTolerance epsilon) (testTolerance_pos he) m n hm hn)

/-- Computable antitone closure of the supplied Cauchy modulus. -/
def testRate (X : (D).Cauchy) : Q' → Nat := closedRate canonicalReciprocalIndexData (rawRate X)

theorem testRate_antitone (X : (D).Cauchy) : MmonoPred (testRate X) :=
  closedRate_mmonoPred canonicalReciprocalIndexData (rawRate X)

theorem testSequence_bound (X : (D).Cauchy) : LeRatBound (testSequence X) (testRate X) :=
  LeRatBound.closed canonicalReciprocalIndexData (testSequence_raw_bound X)

def testReg (X : (D).Cauchy) (n : Nat) : Q' → Nat := (meanLimitCauchy (X.seq n).expression).M

theorem testSequence_regular (X : (D).Cauchy) : RegPred (testSequence X) (testReg X) :=
  fun n => (meanLimitCauchy (X.seq n).expression).bound

def representativeTest (X : (D).Cauchy) : CReal :=
  completeLimitFromRate (testSequence X) (testRate X) (testReg X)
    (testSequence_regular X) (testSequence_bound X)

theorem testSequence_converges (X : (D).Cauchy) : ConvergesTo (testSequence X) (representativeTest X) :=
  convergesTo_completeLimitFromRate _ _ _ (testSequence_regular X) (testSequence_bound X) (testRate_antitone X)

private def diagonalCauchy (s : Nat → CReal) (M : Q' → Nat) (reg : Nat → Q' → Nat)
    (hr : RegPred s reg) (hb : LeRatBound s M) :
    QCauchy (completeLimitFromRate s M reg hr hb).approx where
  M epsilon := (HalfPow.half * (HalfPow.half * epsilon)).den
  bound := by
    intro epsilon he m n hm hn
    rcases Nat.le_total m n with hmn | hnm
    · exact diagSeqR_directed s M reg hr hb epsilon he m n hmn hm
    · exact (diagSeqR_directed s M reg hr hb epsilon he n m hnm hn).symm

def representativeTestCauchy (X : (D).Cauchy) : QCauchy (representativeTest X).approx :=
  diagonalCauchy (testSequence X) (testRate X) (testReg X) (testSequence_regular X) (testSequence_bound X)

def closeRate {X Y : (D).Cauchy} (h : (D).Close X Y) (epsilon : Q') : Nat :=
  h.modulus (testTolerance epsilon)

theorem testSequence_close {X Y : (D).Cauchy} (h : (D).Close X Y)
    (epsilon : Q') (he : (0 : Q') < epsilon) (n : Nat) (hn : closeRate h epsilon ≤ n) :
    leRat (CReal.sub (testSequence X n) (testSequence Y n)) epsilon ∧
    leRat (CReal.sub (testSequence Y n) (testSequence X n)) epsilon :=
  presentedTest_close (X.seq n) (Y.seq n) epsilon he
    (h.close (testTolerance epsilon) (testTolerance_pos he) n hn)

theorem representativeTest_welldef {X Y : (D).Cauchy} (h : (D).Close X Y) :
    Equiv (representativeTest X) (representativeTest Y) := by
  apply Equiv_of_limit_of_close (testSequence_converges X) (testSequence_converges Y)
  intro epsilon he
  have hh := ExpNeg.half_mul_pos epsilon he
  refine ⟨closeRate h (HalfPow.half * epsilon), fun n hn => ?_⟩
  have hb := testSequence_close h (HalfPow.half * epsilon) hh n hn
  obtain ⟨K, hK⟩ := evTwoSided_of_leRat hb.1 hb.2 hh
  refine ⟨K, fun k hk => ?_⟩
  exact ⟨Q'.le_trans' _ _ _ (hK k hk).1
      (Q'.add_le_add_left _ _ _ (Q'.le_of_eqv (ExpNeg.two_halves epsilon))),
    Q'.le_trans' _ _ _ (hK k hk).2
      (Q'.add_le_add_left _ _ _ (Q'.le_of_eqv (ExpNeg.two_halves epsilon)))⟩

/-- Quotient elimination, with no selection of a Cauchy representative. -/
def completedTest : Completion → RC :=
  Quotient.lift (fun X => Quotient.mk crealSetoid (representativeTest X))
    (fun _ _ ⟨h⟩ => Quotient.sound (representativeTest_welldef h))

theorem completedTest_mk (X : (D).Cauchy) :
    completedTest (Quotient.mk (D).completionSetoid X) = Quotient.mk crealSetoid (representativeTest X) := rfl

def completedTestRepresentative (X : (D).Cauchy) :
    Σ' r : CReal, QCauchy r.approx ×'
      (completedTest (Quotient.mk (D).completionSetoid X) = Quotient.mk crealSetoid r) :=
  ⟨representativeTest X, representativeTestCauchy X, rfl⟩

theorem completedTest_embedPresentation (p : Presentation) :
    completedTest (embedPresentation p) = observableTest (embed p) :=
  Quotient.sound (Equiv_of_limit_of_equal (fun _ => Equiv.refl (meanLimit p.expression))
    (testSequence_converges ((D).constant p)) (convergesTo_const _))

theorem completedTest_embedObservable (x : Observable) :
    completedTest (embedObservable x) = observableTest x := by
  refine Quotient.inductionOn x ?_
  exact completedTest_embedPresentation

theorem completedTest_embedOSQuotient (x : Carrier) :
    completedTest (embedOSQuotient x) = osTest x := by
  refine Quotient.inductionOn x ?_
  exact completedTest_embedObservable

theorem representativeTest_bound (X : (D).Cauchy) :
    leEv (CReal.mul (representativeTest X) (representativeTest X)) (representativeInner X X) :=
  leEv_of_convergesTo_le
    (Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz.CReal.convergesTo_mul_general
      (testSequence_converges X) (testSequence_converges X))
    (pairSequence_converges X X) (fun n => observableTest_bound (embed (X.seq n)))

theorem completedTest_bound (x : Completion) :
    RCle (RCmul (completedTest x) (completedTest x)) (completedInner x x) := by
  refine Quotient.inductionOn x ?_
  exact representativeTest_bound

theorem completedTest_add (x y : Completion) :
    completedTest (completedAdd x y) = RCadd (completedTest x) (completedTest y) := by
  refine Quotient.inductionOn₂ x y ?_
  intro X Y
  exact Quotient.sound (Equiv_of_limit_of_equal
    (fun n => Quotient.exact (observableTest_add (embed (X.seq n)) (embed (Y.seq n))))
    (testSequence_converges ((addition).mapCauchy X Y))
    (convergesTo_add (testSequence_converges X) (testSequence_converges Y)))

theorem completedTest_smul (c : Q') (x : Completion) :
    completedTest (completedSmul c x) = RCmul (Quotient.mk crealSetoid (ofQ' c)) (completedTest x) := by
  refine Quotient.inductionOn x ?_
  intro X
  exact Quotient.sound (Equiv_of_limit_of_equal
    (fun n => Quotient.exact (observableTest_smul c (embed (X.seq n))))
    (testSequence_converges ((scalarContinuous c).mapCauchy X))
    (convergesTo_const_mul (ofQ' c) (testSequence_converges X)))

theorem representativeTest_distance_bound (X Y : (D).Cauchy) :
    leEv (CReal.mul (CReal.sub (representativeTest X) (representativeTest Y))
      (CReal.sub (representativeTest X) (representativeTest Y))) (representativeDist X Y) := by
  have hs := convergesTo_add (testSequence_converges X)
    (TrigAddCReal.convergesTo_neg (testSequence_converges Y))
  exact leEv_of_convergesTo_le
    (Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz.CReal.convergesTo_mul_general hs hs)
    (representativeDist_converges X Y)
    (fun n => presentedTest_distance_bound (X.seq n) (Y.seq n))

theorem completedTest_distance_bound (x y : Completion) :
    RCle (RCmul (RCsub (completedTest x) (completedTest y)) (RCsub (completedTest x) (completedTest y)))
      (completedDist x y) := by
  refine Quotient.inductionOn₂ x y ?_
  exact representativeTest_distance_bound

end YMGap.Continuum.BF4ExactSlabBulkScalarCompletedTest

#print axioms YMGap.Continuum.BF4ExactSlabBulkScalarCompletedTest.testSequence
#print axioms YMGap.Continuum.BF4ExactSlabBulkScalarCompletedTest.rawRate
#print axioms YMGap.Continuum.BF4ExactSlabBulkScalarCompletedTest.testSequence_raw_bound
#print axioms YMGap.Continuum.BF4ExactSlabBulkScalarCompletedTest.testRate
#print axioms YMGap.Continuum.BF4ExactSlabBulkScalarCompletedTest.testRate_antitone
#print axioms YMGap.Continuum.BF4ExactSlabBulkScalarCompletedTest.testSequence_bound
#print axioms YMGap.Continuum.BF4ExactSlabBulkScalarCompletedTest.testReg
#print axioms YMGap.Continuum.BF4ExactSlabBulkScalarCompletedTest.testSequence_regular
#print axioms YMGap.Continuum.BF4ExactSlabBulkScalarCompletedTest.representativeTest
#print axioms YMGap.Continuum.BF4ExactSlabBulkScalarCompletedTest.testSequence_converges
#print axioms YMGap.Continuum.BF4ExactSlabBulkScalarCompletedTest.representativeTestCauchy
#print axioms YMGap.Continuum.BF4ExactSlabBulkScalarCompletedTest.closeRate
#print axioms YMGap.Continuum.BF4ExactSlabBulkScalarCompletedTest.testSequence_close
#print axioms YMGap.Continuum.BF4ExactSlabBulkScalarCompletedTest.representativeTest_welldef
#print axioms YMGap.Continuum.BF4ExactSlabBulkScalarCompletedTest.completedTest
#print axioms YMGap.Continuum.BF4ExactSlabBulkScalarCompletedTest.completedTest_mk
#print axioms YMGap.Continuum.BF4ExactSlabBulkScalarCompletedTest.completedTestRepresentative
#print axioms YMGap.Continuum.BF4ExactSlabBulkScalarCompletedTest.completedTest_embedPresentation
#print axioms YMGap.Continuum.BF4ExactSlabBulkScalarCompletedTest.completedTest_embedObservable
#print axioms YMGap.Continuum.BF4ExactSlabBulkScalarCompletedTest.completedTest_embedOSQuotient
#print axioms YMGap.Continuum.BF4ExactSlabBulkScalarCompletedTest.representativeTest_bound
#print axioms YMGap.Continuum.BF4ExactSlabBulkScalarCompletedTest.completedTest_bound
#print axioms YMGap.Continuum.BF4ExactSlabBulkScalarCompletedTest.completedTest_add
#print axioms YMGap.Continuum.BF4ExactSlabBulkScalarCompletedTest.completedTest_smul
#print axioms YMGap.Continuum.BF4ExactSlabBulkScalarCompletedTest.representativeTest_distance_bound
#print axioms YMGap.Continuum.BF4ExactSlabBulkScalarCompletedTest.completedTest_distance_bound
