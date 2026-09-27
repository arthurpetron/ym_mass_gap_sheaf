/-
# The original reflected null quotient inside the SAME Wilson completion

The reflected mean of a supported difference is exactly its existing
completed squared distance. Quotienting supported observables by this null
relation therefore gives an injective state map into the existing physical
completion, preserving the original reflected form and forward time.

Explicit dense approximants are returned from SUPPLIED Cauchy representatives.
No representative is selected from a completion class, and no new completion
or product on OS-null classes is assumed. This is fixed-spacing RC-valued
structure, not the rational canonical OS root or a continuum QFT construction.
-/

import YMGap.Continuum.BF4WilsonSignedTimeUnionSupportedEmbedding
import YMGap.Continuum.BF4WilsonSpatialUnionCompletedDistance

namespace YMGap.Continuum.BF4WilsonSignedTimeUnionOS

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4WilsonSpatialUnionSeminorm
open YMGap.Continuum.BF4WilsonSpatialUnionPairingData (completedInner)
open YMGap.Continuum.BF4WilsonSpatialUnionLinear (completedNeg)
open YMGap.Continuum.BF4WilsonSpatialUnionBilinear (completedSub)
open YMGap.Continuum.BF4WilsonSpatialUnionCompletedDistance
  (completedDist completedDist_nonnegative completedDist_zero_iff distanceData)
open YMGap.Continuum.BF4WilsonSignedTimeUnionSupportedEmbedding
  (embedding embedding_reflected_mean)
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)

local notation "O" => BF4WilsonSpatialUnionObservableQuotient.Observable hw0 hw1 hsmall hd hs
local notation "S" => BF4WilsonSpatialUnionObservableQuotient.state hw0 hw1 hsmall hd hs
local notation "F" => BF4WilsonSpatialUnionObservableQuotient.forward hw0 hw1 hsmall hd hs
local notation "j" => embedding hw0 hw1 hsmall hd hs
local notation "D" => unionSeminorm hw0 hw1 hsmall hd hs
local notation "V" => UnionCompletion hw0 hw1 hsmall hd hs
local notation "B" => completedInner hw0 hw1 hsmall hd hs
local notation "dist" => completedDist hw0 hw1 hsmall hd hs

def supportedDifference (a b : O) : O :=
  BF4WilsonSpatialUnionObservableQuotient.add hw0 hw1 hsmall hd hs a
    (BF4WilsonSpatialUnionObservableQuotient.smul hw0 hw1 hsmall hd hs (-1) b)

theorem state_difference (a b : O) :
    S (supportedDifference hw0 hw1 hsmall hd hs a b) =
      completedSub hw0 hw1 hsmall hd hs (S a) (S b) := by
  unfold supportedDifference
  rw [BF4WilsonSpatialUnionObservableQuotient.state_add,
    BF4WilsonSpatialUnionObservableQuotient.state_smul]
  rfl

/-- The original ambient mean with physical reflection, not ordinary star. -/
def reflectedForm (a b : O) : RC :=
  BF4WilsonSignedTimeUnionObservable.meanRC hw0 hw1 hsmall hd hs
    (BF4WilsonSignedTimeUnionObservable.mul hw0 hw1 hsmall hd hs
      (BF4WilsonSignedTimeUnionObservable.reflection hw0 hw1 hsmall hd hs (j a)) (j b))

theorem reflectedForm_eq (a b : O) :
    reflectedForm hw0 hw1 hsmall hd hs a b = B (S a) (S b) :=
  embedding_reflected_mean hw0 hw1 hsmall hd hs a b

def reflectedDistance (a b : O) : RC :=
  reflectedForm hw0 hw1 hsmall hd hs (supportedDifference hw0 hw1 hsmall hd hs a b)
    (supportedDifference hw0 hw1 hsmall hd hs a b)

/-- The actual reflected mean of the actual observable difference is the
existing completed distance, not a newly assumed seminorm. -/
theorem reflectedDistance_eq (a b : O) :
    reflectedDistance hw0 hw1 hsmall hd hs a b = dist (S a) (S b) := by
  unfold reflectedDistance
  rw [reflectedForm_eq, state_difference]
  rfl

theorem reflectedDistance_nonnegative (a b : O) :
    RCnonneg (reflectedDistance hw0 hw1 hsmall hd hs a b) := by
  rw [reflectedDistance_eq]
  exact completedDist_nonnegative hw0 hw1 hsmall hd hs (S a) (S b)

theorem reflectedDistance_zero_iff (a b : O) :
    reflectedDistance hw0 hw1 hsmall hd hs a b = RCzero ↔ S a = S b := by
  rw [reflectedDistance_eq]
  exact completedDist_zero_iff hw0 hw1 hsmall hd hs (S a) (S b)

/-- This relation uses the original reflected null form. It is not the
stronger multiplication-tested observable equivalence. -/
def nullSetoid : Setoid O where
  r a b := reflectedDistance hw0 hw1 hsmall hd hs a b = RCzero
  iseqv := ⟨fun a => (reflectedDistance_zero_iff hw0 hw1 hsmall hd hs a a).mpr rfl,
    fun {a b} h => (reflectedDistance_zero_iff hw0 hw1 hsmall hd hs b a).mpr
      ((reflectedDistance_zero_iff hw0 hw1 hsmall hd hs a b).mp h).symm,
    fun {a b c} h k => (reflectedDistance_zero_iff hw0 hw1 hsmall hd hs a c).mpr
      (((reflectedDistance_zero_iff hw0 hw1 hsmall hd hs a b).mp h).trans
        ((reflectedDistance_zero_iff hw0 hw1 hsmall hd hs b c).mp k))⟩

def OSObservable : Type := Quotient (nullSetoid hw0 hw1 hsmall hd hs)

local notation "QOS" => OSObservable hw0 hw1 hsmall hd hs

def ofObservable (a : O) : QOS := Quotient.mk (nullSetoid hw0 hw1 hsmall hd hs) a

def state : QOS → V := Quotient.lift S
  (fun a b h => (reflectedDistance_zero_iff hw0 hw1 hsmall hd hs a b).mp h)

theorem state_ofObservable (a : O) :
    state hw0 hw1 hsmall hd hs (ofObservable hw0 hw1 hsmall hd hs a) = S a := rfl

theorem state_injective (x y : QOS)
    (h : state hw0 hw1 hsmall hd hs x = state hw0 hw1 hsmall hd hs y) : x = y := by
  induction x using Quotient.inductionOn with
  | h a =>
    induction y using Quotient.inductionOn with
    | h b =>
      exact Quotient.sound ((reflectedDistance_zero_iff hw0 hw1 hsmall hd hs a b).mpr h)

/-- The existing physical form, identified with the original reflected
observable mean below. No independent GNS form is supplied. -/
def inner (x y : QOS) : RC := B (state hw0 hw1 hsmall hd hs x) (state hw0 hw1 hsmall hd hs y)

theorem inner_ofObservable (a b : O) :
    inner hw0 hw1 hsmall hd hs (ofObservable hw0 hw1 hsmall hd hs a)
      (ofObservable hw0 hw1 hsmall hd hs b) = reflectedForm hw0 hw1 hsmall hd hs a b :=
  (reflectedForm_eq hw0 hw1 hsmall hd hs a b).symm

def forwardTime (n : Nat) : QOS → QOS := Quotient.lift
  (fun a => ofObservable hw0 hw1 hsmall hd hs (F n a))
  (fun a b h => Quotient.sound ((reflectedDistance_zero_iff hw0 hw1 hsmall hd hs (F n a) (F n b)).mpr
    (by
      rw [BF4WilsonSpatialUnionObservableQuotient.state_forward,
        BF4WilsonSpatialUnionObservableQuotient.state_forward]
      exact congrArg (completedTime hw0 hw1 hsmall hd hs n)
        ((reflectedDistance_zero_iff hw0 hw1 hsmall hd hs a b).mp h))))

theorem state_forwardTime (n : Nat) (x : QOS) :
    state hw0 hw1 hsmall hd hs (forwardTime hw0 hw1 hsmall hd hs n x) =
      completedTime hw0 hw1 hsmall hd hs n (state hw0 hw1 hsmall hd hs x) := by
  refine Quotient.inductionOn x ?_
  exact fun a => BF4WilsonSpatialUnionObservableQuotient.state_forward hw0 hw1 hsmall hd hs n a

theorem inner_forwardTime (n : Nat) (x y : QOS) :
    inner hw0 hw1 hsmall hd hs x (forwardTime hw0 hw1 hsmall hd hs n y) =
      B (state hw0 hw1 hsmall hd hs x)
        (completedTime hw0 hw1 hsmall hd hs n (state hw0 hw1 hsmall hd hs y)) := by
  unfold inner
  rw [state_forwardTime]

/-- An actual null-quotient observable and its distance certificate, computed
from the supplied representative's own modulus. No quotient choice. -/
def approximationData (X : (D).Cauchy) (epsilon : Q') (he : (0 : Q') < epsilon) :
    Σ' x : QOS,
      RCle (dist (state hw0 hw1 hsmall hd hs x) (Quotient.mk (D).completionSetoid X))
        (Quotient.mk crealSetoid (ofQ' epsilon)) := by
  let p := CRealSeminormCompletedApproximation.approximationData
    (distanceData hw0 hw1 hsmall hd hs) X epsilon he
  exact ⟨ofObservable hw0 hw1 hsmall hd hs
    (BF4WilsonSpatialUnionObservableQuotient.ofStage hw0 hw1 hsmall hd hs p.1), p.2⟩

theorem approximationData_witness (X : (D).Cauchy) (epsilon : Q') (he : (0 : Q') < epsilon) :
    (approximationData hw0 hw1 hsmall hd hs X epsilon he).1 =
      ofObservable hw0 hw1 hsmall hd hs
        (BF4WilsonSpatialUnionObservableQuotient.ofStage hw0 hw1 hsmall hd hs
          (X.seq (X.modulus epsilon))) := rfl

/-- Addition descends because its physical state is the completed sum.
There is deliberately no analogous assertion for arbitrary products. -/
def add : QOS → QOS → QOS := Quotient.lift₂
  (fun a b => ofObservable hw0 hw1 hsmall hd hs
    (BF4WilsonSpatialUnionObservableQuotient.add hw0 hw1 hsmall hd hs a b))
  (fun a c b d hab hcd => Quotient.sound
    ((reflectedDistance_zero_iff hw0 hw1 hsmall hd hs _ _).mpr (by
      rw [BF4WilsonSpatialUnionObservableQuotient.state_add,
        BF4WilsonSpatialUnionObservableQuotient.state_add,
        (reflectedDistance_zero_iff hw0 hw1 hsmall hd hs a b).mp hab,
        (reflectedDistance_zero_iff hw0 hw1 hsmall hd hs c d).mp hcd])))

theorem state_add (x y : QOS) :
    state hw0 hw1 hsmall hd hs (add hw0 hw1 hsmall hd hs x y) =
      BF4WilsonSpatialUnionLinear.completedAdd hw0 hw1 hsmall hd hs
        (state hw0 hw1 hsmall hd hs x) (state hw0 hw1 hsmall hd hs y) := by
  refine Quotient.inductionOn₂ x y ?_
  exact fun a b => BF4WilsonSpatialUnionObservableQuotient.state_add hw0 hw1 hsmall hd hs a b

def smul (c : Q') : QOS → QOS := Quotient.lift
  (fun a => ofObservable hw0 hw1 hsmall hd hs
    (BF4WilsonSpatialUnionObservableQuotient.smul hw0 hw1 hsmall hd hs c a))
  (fun a b h => Quotient.sound ((reflectedDistance_zero_iff hw0 hw1 hsmall hd hs _ _).mpr (by
    rw [BF4WilsonSpatialUnionObservableQuotient.state_smul,
      BF4WilsonSpatialUnionObservableQuotient.state_smul,
      (reflectedDistance_zero_iff hw0 hw1 hsmall hd hs a b).mp h])))

theorem state_smul (c : Q') (x : QOS) :
    state hw0 hw1 hsmall hd hs (smul hw0 hw1 hsmall hd hs c x) =
      BF4WilsonSpatialUnionLinear.completedSmul hw0 hw1 hsmall hd hs c
        (state hw0 hw1 hsmall hd hs x) := by
  refine Quotient.inductionOn x ?_
  exact fun a => BF4WilsonSpatialUnionObservableQuotient.state_smul hw0 hw1 hsmall hd hs c a

end YMGap.Continuum.BF4WilsonSignedTimeUnionOS

#print axioms YMGap.Continuum.BF4WilsonSignedTimeUnionOS.supportedDifference
#print axioms YMGap.Continuum.BF4WilsonSignedTimeUnionOS.state_difference
#print axioms YMGap.Continuum.BF4WilsonSignedTimeUnionOS.reflectedForm
#print axioms YMGap.Continuum.BF4WilsonSignedTimeUnionOS.reflectedForm_eq
#print axioms YMGap.Continuum.BF4WilsonSignedTimeUnionOS.reflectedDistance
#print axioms YMGap.Continuum.BF4WilsonSignedTimeUnionOS.reflectedDistance_eq
#print axioms YMGap.Continuum.BF4WilsonSignedTimeUnionOS.reflectedDistance_nonnegative
#print axioms YMGap.Continuum.BF4WilsonSignedTimeUnionOS.reflectedDistance_zero_iff
#print axioms YMGap.Continuum.BF4WilsonSignedTimeUnionOS.nullSetoid
#print axioms YMGap.Continuum.BF4WilsonSignedTimeUnionOS.OSObservable
#print axioms YMGap.Continuum.BF4WilsonSignedTimeUnionOS.ofObservable
#print axioms YMGap.Continuum.BF4WilsonSignedTimeUnionOS.state
#print axioms YMGap.Continuum.BF4WilsonSignedTimeUnionOS.state_ofObservable
#print axioms YMGap.Continuum.BF4WilsonSignedTimeUnionOS.state_injective
#print axioms YMGap.Continuum.BF4WilsonSignedTimeUnionOS.inner
#print axioms YMGap.Continuum.BF4WilsonSignedTimeUnionOS.inner_ofObservable
#print axioms YMGap.Continuum.BF4WilsonSignedTimeUnionOS.forwardTime
#print axioms YMGap.Continuum.BF4WilsonSignedTimeUnionOS.state_forwardTime
#print axioms YMGap.Continuum.BF4WilsonSignedTimeUnionOS.inner_forwardTime
#print axioms YMGap.Continuum.BF4WilsonSignedTimeUnionOS.approximationData
#print axioms YMGap.Continuum.BF4WilsonSignedTimeUnionOS.approximationData_witness
#print axioms YMGap.Continuum.BF4WilsonSignedTimeUnionOS.add
#print axioms YMGap.Continuum.BF4WilsonSignedTimeUnionOS.state_add
#print axioms YMGap.Continuum.BF4WilsonSignedTimeUnionOS.smul
#print axioms YMGap.Continuum.BF4WilsonSignedTimeUnionOS.state_smul
