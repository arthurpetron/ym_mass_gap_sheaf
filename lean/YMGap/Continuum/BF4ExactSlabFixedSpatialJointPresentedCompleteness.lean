/-
# Represented norm completeness of the SAME joint reflected carrier

An outer Cauchy family is supplied by explicit representatives, but its Cauchy
condition is measured in the ACTUAL completed inner product, not by an extra
assumption on those representatives.  The constructed pairing rate turns this
condition into the representative comparison needed by the generic diagonal.
Passing its eventual distance estimate back through the SAME pairing limit
proves convergence in the actual completed squared norm, with an explicit
outer modulus.

No representative is selected from a quotient point.  This proves completeness
for represented Cauchy families, not a choice-based lift of arbitrary
quotient-valued sequences.  Nome and spatial width remain fixed.  Full Hilbert,
continuous-time, spatial/scaling, QFT and Clay obligations remain open.
-/

import YMGap.Continuum.CRealSeminormPresentedCompleteness
import YMGap.Continuum.BF4ExactSlabFixedSpatialJointGeometry

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialJointPresentedCompleteness

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.CRealSeminormCompletion
open YMGap.Continuum.CRealSeminormPresentedCompleteness
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointSeminorm
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointPhysicalTime
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointLinear
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointPairingLimit
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointCompletedInner
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointGeometry

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (width : Nat)

local notation "D" => jointSeminorm hw0 hw1 width
local notation "V" => JointCompletion hw0 hw1 width
local notation "B" => completedInner hw0 hw1 width

-- Their established limit APIs suffice; do not expand the scalar algorithms.
attribute [local irreducible] representativeInner
  BF4ExactSlabFixedSpatialChartJointLimits.jointPairing

/-- Literal difference of supplied streams using the existing completed
linear operations and their explicit moduli. -/
def differenceCauchy (X Y : (D).Cauchy) : (D).Cauchy :=
  (addition hw0 hw1 width).mapCauchy X
    ((scalarContinuous hw0 hw1 width (-1)).mapCauchy Y)

/-- Squared distance is the actual inner product of the actual difference. -/
def completedDistSq (x y : V) : RC :=
  B (completedSub hw0 hw1 width x y) (completedSub hw0 hw1 width x y)

def representativeDistSq (X Y : (D).Cauchy) : CReal :=
  representativeInner hw0 hw1 width
    (differenceCauchy hw0 hw1 width X Y) (differenceCauchy hw0 hw1 width X Y)

theorem completedDistSq_mk (X Y : (D).Cauchy) :
    completedDistSq hw0 hw1 width
        (Quotient.mk (D).completionSetoid X) (Quotient.mk (D).completionSetoid Y) =
      Quotient.mk crealSetoid (representativeDistSq hw0 hw1 width X Y) := rfl

/-- The limit is of the SAME joint squared distances, not finite-cutoff or
ordinary-GNS distances. -/
theorem representativeDistSq_converges (X Y : (D).Cauchy) :
    ConvergesTo (fun n => (D).distSq (X.seq n) (Y.seq n))
      (representativeDistSq hw0 hw1 width X Y) :=
  pairSequence_converges hw0 hw1 width
    (differenceCauchy hw0 hw1 width X Y) (differenceCauchy hw0 hw1 width X Y)

/-- Explicit late index for the actual difference pairing. -/
def distanceRate (X Y : (D).Cauchy) (epsilon : Q') : Nat :=
  pairRate hw0 hw1 width
    (differenceCauchy hw0 hw1 width X Y) (differenceCauchy hw0 hw1 width X Y) epsilon

/-- Half the tolerance bounds the completed norm; the other half pays for
the computed representative-to-limit error. -/
theorem late_distSq_le (X Y : (D).Cauchy) (epsilon : Q')
    (he : (0 : Q') < epsilon)
    (hXY : RCle (completedDistSq hw0 hw1 width
        (Quotient.mk (D).completionSetoid X) (Quotient.mk (D).completionSetoid Y))
      (Quotient.mk crealSetoid (ofQ' (HalfPow.half * epsilon))))
    (n : Nat) (hn : distanceRate hw0 hw1 width X Y (HalfPow.half * epsilon) ≤ n) :
    leEv ((D).distSq (X.seq n) (Y.seq n)) (ofQ' epsilon) := by
  rw [completedDistSq_mk, RCle_mk] at hXY
  let L := representativeDistSq hw0 hw1 width X Y
  let d := (D).distSq (X.seq n) (Y.seq n)
  have hL : leEv L (ofQ' (HalfPow.half * epsilon)) := hXY
  have hd : leRat (sub d L) (HalfPow.half * epsilon) :=
    (pairSequence_limit_close hw0 hw1 width
      (differenceCauchy hw0 hw1 width X Y) (differenceCauchy hw0 hw1 width X Y)
      (HalfPow.half * epsilon) (ExpNeg.half_mul_pos epsilon he) n hn).1
  have hcancel : Equiv d (add L (sub d L)) :=
    SumOfSquares.Equiv_of_approx_eqv (fun k =>
      Q'.add_sub_cancel_eqv (d.approx k) (L.approx k))
  have hd' : leEv (sub d L) (ofQ' (HalfPow.half * epsilon)) := hd
  have hsum := leEv_add hL hd'
  rw [ofQ'_add] at hsum
  exact leEv_trans (leEv_of_equiv hcancel)
    (leEv_trans hsum (leEv_of_equiv (ofQ'_equiv_of_eqv (ExpNeg.two_halves epsilon))))

private theorem convergesTo_max {s : Nat → CReal} {L : CReal}
    (h : ConvergesTo s L) (base : Nat) : ConvergesTo (fun n => s (max n base)) L := by
  intro epsilon he
  obtain ⟨N, hN⟩ := h epsilon he
  exact ⟨N, fun n hn => hN (max n base) (Nat.le_trans hn (Nat.le_max_left _ _))⟩

/-- A supplied eventual representative bound descends to the actual completed
norm with no tolerance loss.  The late index remains explicit input data. -/
theorem completedDistSq_le_of_eventual (X Y : (D).Cauchy) (epsilon : Q') (N : Nat)
    (h : ∀ n, N ≤ n → leEv ((D).distSq (X.seq n) (Y.seq n)) (ofQ' epsilon)) :
    RCle (completedDistSq hw0 hw1 width
        (Quotient.mk (D).completionSetoid X) (Quotient.mk (D).completionSetoid Y))
      (Quotient.mk crealSetoid (ofQ' epsilon)) :=
  leEv_of_convergesTo_le
    (convergesTo_max (representativeDistSq_converges hw0 hw1 width X Y) N)
    (convergesTo_const (ofQ' epsilon)) (fun n => h (max n N) (Nat.le_max_right _ _))

/-- A norm-Cauchy family on the actual completion, with supplied representatives
and outer modulus.  No representative-comparison hypothesis is added. -/
structure PresentedNormCauchy where
  pt : Nat → (D).Cauchy
  modulus : Q' → Nat
  cauchy : ∀ epsilon, (0 : Q') < epsilon → ∀ p q,
    modulus epsilon ≤ p → modulus epsilon ≤ q →
    RCle (completedDistSq hw0 hw1 width
        (Quotient.mk (D).completionSetoid (pt p)) (Quotient.mk (D).completionSetoid (pt q)))
      (Quotient.mk crealSetoid (ofQ' epsilon))

namespace PresentedNormCauchy

variable (X : PresentedNormCauchy hw0 hw1 width)

/-- The additional bridge rate required by the generic diagonal is COMPUTED
from the existing pairing rate and actual norm-Cauchy condition. -/
def toPresented : GeneralPresentedCauchy (D) where
  pt := X.pt
  modulus epsilon := X.modulus (HalfPow.half * epsilon)
  bridge epsilon p q := distanceRate hw0 hw1 width (X.pt p) (X.pt q) (HalfPow.half * epsilon)
  cauchy := by
    intro epsilon he p q hp hq n hn
    exact late_distSq_le hw0 hw1 width (X.pt p) (X.pt q) epsilon he
      (X.cauchy _ (ExpNeg.half_mul_pos epsilon he) p q hp hq) n hn

/-- The constructed limit is a point of the SAME reflected completion. -/
def limit : V :=
  Quotient.mk (D).completionSetoid (X.toPresented hw0 hw1 width).diagonal

/-- Explicit outer modulus for convergence in the SAME completed squared norm. -/
def limitRate (epsilon : Q') : Nat :=
  (X.toPresented hw0 hw1 width).convergenceOuterRate epsilon

/-- Represented completeness in the actual norm.  This does not extract
representatives of an arbitrary quotient-valued sequence. -/
theorem limit_converges (epsilon : Q') (he : (0 : Q') < epsilon)
    (p : Nat) (hp : X.limitRate hw0 hw1 width epsilon ≤ p) :
    RCle (completedDistSq hw0 hw1 width
        (Quotient.mk (D).completionSetoid (X.pt p)) (X.limit hw0 hw1 width))
      (Quotient.mk crealSetoid (ofQ' epsilon)) := by
  exact completedDistSq_le_of_eventual hw0 hw1 width (X.pt p)
    (X.toPresented hw0 hw1 width).diagonal epsilon
    ((X.toPresented hw0 hw1 width).convergenceInnerRate epsilon p)
    (fun n hn => (X.toPresented hw0 hw1 width).convergesToDiagonal epsilon he p hp n hn)

end PresentedNormCauchy

end YMGap.Continuum.BF4ExactSlabFixedSpatialJointPresentedCompleteness

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointPresentedCompleteness.differenceCauchy
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointPresentedCompleteness.completedDistSq_mk
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointPresentedCompleteness.representativeDistSq_converges
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointPresentedCompleteness.late_distSq_le
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointPresentedCompleteness.completedDistSq_le_of_eventual
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointPresentedCompleteness.PresentedNormCauchy.toPresented
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointPresentedCompleteness.PresentedNormCauchy.limit
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointPresentedCompleteness.PresentedNormCauchy.limit_converges
