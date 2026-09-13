/-
# Squared-distance geometry of the ORIGINAL thermodynamic completion

Completed subtraction uses the proved linear operations. Its squared norm
is the limit of the ORIGINAL presentation distances, retains a real
QCauchy modulus, and agrees with the semantic OS distance on embedded
observables. Symmetry and the square-root-free triangle law pass through
the SAME limits. Zero distance is exactly equality of completed states.

The existing completed sharp CS is not reproved or replaced. No physical
time operator, stationary vacuum, spectral gap or continuum is supplied.
-/

import YMGap.Continuum.BF4ExactSlabThermodynamicCompletedBilinear

namespace YMGap.Continuum.BF4ExactSlabThermodynamicCompletedGeometry

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
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedPosdef
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletionLinear
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedBilinear

local notation "D" => seminorm

def differenceCauchy (X Y : (D).Cauchy) : (D).Cauchy :=
  (addition).mapCauchy X ((scalarContinuous (-1)).mapCauchy Y)

def completedSub (x y : Completion) : Completion :=
  completedAdd x (completedNeg y)

theorem completedSub_mk (X Y : (D).Cauchy) :
    completedSub (Quotient.mk (D).completionSetoid X) (Quotient.mk (D).completionSetoid Y) =
      Quotient.mk (D).completionSetoid (differenceCauchy X Y) := rfl

def representativeDist (X Y : (D).Cauchy) : CReal :=
  representativeInner (differenceCauchy X Y) (differenceCauchy X Y)

def representativeDistCauchy (X Y : (D).Cauchy) : QCauchy (representativeDist X Y).approx :=
  representativeInnerCauchy (differenceCauchy X Y) (differenceCauchy X Y)

def completedDist (x y : Completion) : RC :=
  completedInner (completedSub x y) (completedSub x y)

theorem completedDist_mk (X Y : (D).Cauchy) :
    completedDist (Quotient.mk (D).completionSetoid X) (Quotient.mk (D).completionSetoid Y) =
      Quotient.mk crealSetoid (representativeDist X Y) := rfl

theorem representativeDist_converges (X Y : (D).Cauchy) :
    ConvergesTo (fun n => distSq (X.seq n) (Y.seq n)) (representativeDist X Y) :=
  pairSequence_converges (differenceCauchy X Y) (differenceCauchy X Y)

theorem completedDist_embedPresentation (e f : Presentation) :
    completedDist (embedPresentation e) (embedPresentation f) =
      Quotient.mk crealSetoid (distSq e f) :=
  completedInner_embedPresentation (presentationSubtract e f) (presentationSubtract e f)

theorem completedSub_embedObservable (x y : Observable) :
    completedSub (embedObservable x) (embedObservable y) = embedObservable (subtract x y) := by
  unfold completedSub completedNeg subtract
  rw [completedSmul_embedObservable, completedAdd_embedObservable]

theorem completedDist_embedObservable (x y : Observable) :
    completedDist (embedObservable x) (embedObservable y) = pairing (subtract x y) (subtract x y) := by
  unfold completedDist
  rw [completedSub_embedObservable, completedInner_embedObservable]

theorem completedDist_nonnegative (x y : Completion) :
    RCnonneg (completedDist x y) := completedInner_nonnegative (completedSub x y)

theorem completedAdd_zero (x : Completion) :
    completedAdd x (completedZero) = x := by
  rw [completedAdd_comm, completedZero_add]

theorem completedSub_add_cancel (x y : Completion) :
    completedAdd (completedSub x y) y = x := by
  change completedAdd (completedAdd x (completedNeg y)) y = x
  rw [completedAdd_assoc, completedNeg_add, completedAdd_zero]

theorem completedSub_self (x : Completion) :
    completedSub x x = completedZero := by
  change completedAdd x (completedNeg x) = completedZero
  rw [completedAdd_comm, completedNeg_add]

theorem completedDist_zero_iff (x y : Completion) :
    completedDist x y = RCzero ↔ x = y := by
  constructor
  · intro h
    have hz := (completedInner_posdef (completedSub x y)).mp h
    have hxy := congrArg (fun z => completedAdd z y) hz
    change completedAdd (completedSub x y) y =
      completedAdd (completedZero) y at hxy
    rw [completedSub_add_cancel, completedZero_add] at hxy
    exact hxy
  · intro h
    unfold completedDist
    rw [h, completedSub_self, completedInner_zero_left]

theorem representativeDist_symm (X Y : (D).Cauchy) :
    Equiv (representativeDist X Y) (representativeDist Y X) :=
  Equiv_of_limit_of_equal (fun n => distSq_symm (X.seq n) (Y.seq n))
    (representativeDist_converges X Y) (representativeDist_converges Y X)

theorem completedDist_symm (x y : Completion) :
    completedDist x y = completedDist y x := by
  refine Quotient.inductionOn₂ x y ?_
  exact fun X Y => Quotient.sound (representativeDist_symm X Y)

theorem representativeDist_triangle (X Y Z : (D).Cauchy) :
    leEv (representativeDist X Z)
      (CReal.add (CReal.add (representativeDist X Y) (representativeDist X Y))
        (CReal.add (representativeDist Y Z) (representativeDist Y Z))) := by
  have hXY := representativeDist_converges X Y
  have hYZ := representativeDist_converges Y Z
  have hsum := TrigAddCReal.convergesTo_add (TrigAddCReal.convergesTo_add hXY hXY) (TrigAddCReal.convergesTo_add hYZ hYZ)
  exact leEv_of_convergesTo_le (representativeDist_converges X Z) hsum
    (fun n => distSq_triangle (X.seq n) (Y.seq n) (Z.seq n))

theorem completedDist_triangle (x y z : Completion) :
    RCle (completedDist x z)
      (RCadd (RCadd (completedDist x y) (completedDist x y))
        (RCadd (completedDist y z) (completedDist y z))) := by
  refine Quotient.inductionOn₃ x y z ?_
  exact representativeDist_triangle

end YMGap.Continuum.BF4ExactSlabThermodynamicCompletedGeometry

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletedGeometry.differenceCauchy
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletedGeometry.completedSub
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletedGeometry.completedSub_mk
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletedGeometry.representativeDist
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletedGeometry.representativeDistCauchy
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletedGeometry.completedDist
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletedGeometry.completedDist_mk
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletedGeometry.representativeDist_converges
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletedGeometry.completedDist_embedPresentation
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletedGeometry.completedSub_embedObservable
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletedGeometry.completedDist_embedObservable
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletedGeometry.completedDist_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletedGeometry.completedAdd_zero
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletedGeometry.completedSub_add_cancel
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletedGeometry.completedSub_self
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletedGeometry.completedDist_zero_iff
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletedGeometry.representativeDist_symm
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletedGeometry.completedDist_symm
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletedGeometry.representativeDist_triangle
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletedGeometry.completedDist_triangle
