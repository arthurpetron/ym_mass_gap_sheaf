/-
# Even-time self-adjointness on the completed strict-cylinder OS carrier

The already derived oriented covariance theorem identifies the two one-sided
matrix coefficients for every even lattice-time shift.  This file transports
that identity to arbitrary staged representatives and then passes it through
the choice-free pairing limit to the actual strict OS completion.

Only even shifts are discharged here.  No odd-time square root, spectral
theorem, or continuum Hamiltonian is asserted.
-/

import YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedInnerLaws
import YMGap.Continuum.Z4HalfTimeReflectionStrictJointOrientedDoubledTimeCovariance

namespace YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedTimeSelfAdjoint

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum.CRealSeminormCompletion
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedInner
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedInnerLaws
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletionBilinearOuter
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealDirectLimitSeminorm
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderBaseTransportBilinear
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderBilinearTimeTranslation
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderDirectLimit
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderSeminorm
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDirectLimitBilinear
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSBilinear
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointOrientedDoubledTimeCovariance
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointPolarizedDoubledTimeIdentity
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

/-! ## 1. The fixed-base even-time adjoint identity -/

/-- In one common source box, symmetry of the reflection form and the derived
one-sided covariance give the operator-oriented adjoint identity for an even
time shift. -/
theorem strictJointCylinderEvenTimeTranslate_self_adjoint
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    {base : Nat} (shift : Nat)
    (left right : StrictJointCylinderVector base) :
    CReal.Equiv
      (strictJointCylinderReflectionBilinear hcoupling hle
        (timeTranslateStrictJointCylinderVector (shift + shift) left)
        (boxTransportStrictJointCylinderVector
          (Nat.le_add_right base (shift + shift)) right))
      (strictJointCylinderReflectionBilinear hcoupling hle
        (boxTransportStrictJointCylinderVector
          (Nat.le_add_right base (shift + shift)) left)
        (timeTranslateStrictJointCylinderVector (shift + shift) right)) := by
  have hsymm := StrictJointCylinderVector.reflectionBilinear_symm
    hcoupling hle
    (timeTranslateStrictJointCylinderVector (shift + shift) left)
    (boxTransportStrictJointCylinderVector
      (Nat.le_add_right base (shift + shift)) right)
  have hcovariance := strictJointEvenOneSidedTimeCovariance_derived
    hcoupling hle shift left right
  change CReal.Equiv
    (strictJointCylinderReflectionBilinear hcoupling hle
      (boxTransportStrictJointCylinderVector
        (Nat.le_add_right base (shift + shift)) left)
      (timeTranslateStrictJointCylinderVector (shift + shift) right))
    (strictJointCylinderReflectionBilinear hcoupling hle
      (boxTransportStrictJointCylinderVector
        (Nat.le_add_right base (shift + shift)) right)
      (timeTranslateStrictJointCylinderVector (shift + shift) left))
      at hcovariance
  exact CReal.Equiv.trans hsymm (CReal.Equiv.symm hcovariance)

/-! ## 2. Passage to arbitrary staged vectors -/

/-- The even-time adjoint identity on the base-independent staged carrier.
Both sides are evaluated in the explicit common box
`max left.base right.base + 2 * shift`. -/
theorem strictJointCylinderStageEvenTimeTranslate_self_adjoint
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (shift : Nat) (left right : StrictJointCylinderStage) :
    CReal.Equiv
      (strictJointCylinderStageReflectionBilinear hcoupling hle
        (left.timeTranslate (shift + shift)) right)
      (strictJointCylinderStageReflectionBilinear hcoupling hle
        left (right.timeTranslate (shift + shift))) := by
  let outer := max left.base right.base
  let evenShift := shift + shift
  have hleft : left.base <= outer := Nat.le_max_left _ _
  have hright : right.base <= outer := Nat.le_max_right _ _
  have houterFinal : outer <= outer + evenShift := Nat.le_add_right _ _
  have hleftFinal : left.base <= outer + evenShift :=
    Nat.le_trans hleft houterFinal
  have hrightFinal : right.base <= outer + evenShift :=
    Nat.le_trans hright houterFinal
  let L := boxTransportStrictJointCylinderVector hleft left.vector
  let R := boxTransportStrictJointCylinderVector hright right.vector
  have hfirst := strictJointCylinderStageReflectionBilinear_at_common
    hcoupling hle (left.timeTranslate evenShift) right
      (Nat.add_le_add_right hleft evenShift) hrightFinal
  have hsecond := strictJointCylinderStageReflectionBilinear_at_common
    hcoupling hle left (right.timeTranslate evenShift)
      hleftFinal (Nat.add_le_add_right hright evenShift)
  have htranslatedLeft :
      boxTransportStrictJointCylinderVector
          (Nat.add_le_add_right hleft evenShift)
          (timeTranslateStrictJointCylinderVector evenShift left.vector) =
        timeTranslateStrictJointCylinderVector evenShift L :=
    (timeTranslate_boxTransportStrictJointCylinderVector
      hleft evenShift left.vector).symm
  have htranslatedRight :
      boxTransportStrictJointCylinderVector
          (Nat.add_le_add_right hright evenShift)
          (timeTranslateStrictJointCylinderVector evenShift right.vector) =
        timeTranslateStrictJointCylinderVector evenShift R :=
    (timeTranslate_boxTransportStrictJointCylinderVector
      hright evenShift right.vector).symm
  have htransportLeft :
      boxTransportStrictJointCylinderVector hleftFinal left.vector =
        boxTransportStrictJointCylinderVector houterFinal L :=
    (boxTransportStrictJointCylinderVector_trans
      hleft houterFinal left.vector).symm
  have htransportRight :
      boxTransportStrictJointCylinderVector hrightFinal right.vector =
        boxTransportStrictJointCylinderVector houterFinal R :=
    (boxTransportStrictJointCylinderVector_trans
      hright houterFinal right.vector).symm
  dsimp only [StrictJointCylinderStage.timeTranslate] at hfirst hsecond
  rw [htranslatedLeft, htransportRight] at hfirst
  rw [htransportLeft, htranslatedRight] at hsecond
  have hfixed := strictJointCylinderEvenTimeTranslate_self_adjoint
    hcoupling hle shift L R
  exact CReal.Equiv.trans (CReal.Equiv.symm hfirst)
    (CReal.Equiv.trans hfixed hsecond)

/-! ## 3. Passage through the constructive pairing limit -/

/-- The two representative matrix-coefficient sequences have equivalent
choice-free limits for every even time shift. -/
theorem cauchyPairingLimit_evenTimeTranslate_self_adjoint
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (shift : Nat)
    (X Y : (strictJointCylinderStageSquaredSeminorm hcoupling hle).Cauchy) :
    CReal.Equiv
      (cauchyPairingLimit hcoupling hle
        ((strictJointCylinderStageTimeTranslateNonexpansive
          hcoupling hle (shift + shift)).mapCauchy X) Y)
      (cauchyPairingLimit hcoupling hle X
        ((strictJointCylinderStageTimeTranslateNonexpansive
          hcoupling hle (shift + shift)).mapCauchy Y)) := by
  let TX := (strictJointCylinderStageTimeTranslateNonexpansive
    hcoupling hle (shift + shift)).mapCauchy X
  let TY := (strictJointCylinderStageTimeTranslateNonexpansive
    hcoupling hle (shift + shift)).mapCauchy Y
  apply CReal.Equiv_of_limit_of_equal
    (aSeq := cauchyPairingSeq hcoupling hle TX Y)
    (bSeq := cauchyPairingSeq hcoupling hle X TY)
  · intro n
    exact strictJointCylinderStageEvenTimeTranslate_self_adjoint
      hcoupling hle shift (X.seq n) (Y.seq n)
  · exact cauchyPairingSeq_converges hcoupling hle TX Y
  · exact cauchyPairingSeq_converges hcoupling hle X TY

/-! ## 4. Completed even-time self-adjointness -/

/-- Every even element of the completed Euclidean-time semigroup is
self-adjoint for the constructed strict-cylinder OS inner form. -/
theorem strictJointCylinderCompletedEvenTimeTranslate_self_adjoint
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (shift : Nat)
    (left right : StrictJointCylinderOSCompletion hcoupling hle) :
    strictJointCylinderCompletedInner hcoupling hle
        (strictJointCylinderCompletedTimeTranslate
          hcoupling hle (shift + shift) left) right =
      strictJointCylinderCompletedInner hcoupling hle left
        (strictJointCylinderCompletedTimeTranslate
          hcoupling hle (shift + shift) right) := by
  refine Quotient.inductionOn₂ left right ?_
  intro X Y
  exact Quotient.sound
    (cauchyPairingLimit_evenTimeTranslate_self_adjoint
      hcoupling hle shift X Y)

#print axioms strictJointCylinderEvenTimeTranslate_self_adjoint
#print axioms strictJointCylinderStageEvenTimeTranslate_self_adjoint
#print axioms cauchyPairingLimit_evenTimeTranslate_self_adjoint
#print axioms strictJointCylinderCompletedEvenTimeTranslate_self_adjoint

end YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedTimeSelfAdjoint
