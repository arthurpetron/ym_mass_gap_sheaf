/-
# Algebraic laws of the completed strict-cylinder OS inner form

This file begins the intrinsic qualification of the completed `RC`-valued
form.  The laws are proved on arbitrary Cauchy representatives by uniqueness
of the constructed outer limits and then descend through the completion
quotient.
-/

import YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedInner
import YMGap.Continuum.SelfAdjointHamiltonian
import YMGap.Continuum.RCScaleClose
import YMGap.Continuum.EffMassConvergence

namespace YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedInnerLaws

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum.CRealSeminormCompletion
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletionBilinearOuter
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletionAdd
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletionScalar
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletionZeroNeg
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedInner
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealDirectLimitSeminorm
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealStageBilinearGeometry
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderDirectLimit
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

/-! ## 1. Symmetry -/

theorem cauchyPairingLimit_symm
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (X Y : (strictJointCylinderStageSquaredSeminorm hcoupling hle).Cauchy) :
    CReal.Equiv (cauchyPairingLimit hcoupling hle X Y)
      (cauchyPairingLimit hcoupling hle Y X) := by
  apply CReal.Equiv_of_limit_of_equal
    (aSeq := cauchyPairingSeq hcoupling hle X Y)
    (bSeq := cauchyPairingSeq hcoupling hle Y X)
  · intro n
    exact strictJointCylinderStageReflectionBilinear_symm
      hcoupling hle (X.seq n) (Y.seq n)
  · exact cauchyPairingSeq_converges hcoupling hle X Y
  · exact cauchyPairingSeq_converges hcoupling hle Y X

theorem strictJointCylinderCompletedInner_symm
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (left right : StrictJointCylinderOSCompletion hcoupling hle) :
    strictJointCylinderCompletedInner hcoupling hle left right =
      strictJointCylinderCompletedInner hcoupling hle right left := by
  refine Quotient.inductionOn₂ left right ?_
  intro X Y
  exact Quotient.sound (cauchyPairingLimit_symm hcoupling hle X Y)

/-! ## 2. Diagonal positivity -/

private theorem leEv_czero_of_convergesTo_nonneg
    {s : Nat -> CReal} {L : CReal}
    (hconv : CReal.ConvergesTo s L)
    (hnonneg : forall n : Nat, CReal.leEv CReal.czero (s n)) :
    CReal.leEv CReal.czero L := by
  intro epsilon hepsilon
  let q := HalfPow.half * epsilon
  have hqpos : (0 : Q') < q := ExpNeg.half_mul_pos epsilon hepsilon
  obtain ⟨N, hN⟩ := hconv q hqpos
  obtain ⟨Kconv, hKconv⟩ := hN N (Nat.le_refl _)
  obtain ⟨Knonneg, hKnonneg⟩ := hnonneg N q hqpos
  refine ⟨max Kconv Knonneg, fun k hk => ?_⟩
  have hkconv : Kconv <= k := Nat.le_trans (Nat.le_max_left _ _) hk
  have hknonneg : Knonneg <= k := Nat.le_trans (Nat.le_max_right _ _) hk
  have hsL := (hKconv k hkconv).1
  have hzeroS := hKnonneg k hknonneg
  refine Q'.le_trans' _ _ _ hzeroS ?_
  refine Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ q hsL) ?_
  exact Q'.le_of_eqv (Q'.eqv_trans _ _ _
    (Q'.add_assoc_eqv (L.approx k) q q)
    (Q'.add_eqv_congr_left (L.approx k) (q + q) epsilon
      (ExpNeg.two_halves epsilon)))

theorem cauchyPairingLimit_self_nonneg
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (X : (strictJointCylinderStageSquaredSeminorm hcoupling hle).Cauchy) :
    CReal.leEv CReal.czero (cauchyPairingLimit hcoupling hle X X) := by
  apply leEv_czero_of_convergesTo_nonneg
    (cauchyPairingSeq_converges hcoupling hle X X)
  intro n
  exact CReal.leEv_trans
    (strictJointCylinderStageReflectionDistSq_nonneg
      hcoupling hle (X.seq n) strictJointCylinderStageZero)
    (CReal.leEv_of_equiv (CReal.Equiv.symm
      (strictJointCylinderStageReflectionBilinear_self_equiv_distSq_zero
        hcoupling hle (X.seq n))))

theorem strictJointCylinderCompletedInner_self_nonneg
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (vector : StrictJointCylinderOSCompletion hcoupling hle) :
    CReal.RCnonneg
      (strictJointCylinderCompletedInner hcoupling hle vector vector) := by
  refine Quotient.inductionOn vector ?_
  intro X
  exact cauchyPairingLimit_self_nonneg hcoupling hle X

/-! ## 3. Additivity -/

theorem cauchyPairingLimit_add_left
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (X Y Z : (strictJointCylinderStageSquaredSeminorm hcoupling hle).Cauchy) :
    CReal.Equiv
      (cauchyPairingLimit hcoupling hle
        ((strictJointCylinderStageAddQuadraticLipschitz
          hcoupling hle).mapCauchy X Y) Z)
      (CReal.add (cauchyPairingLimit hcoupling hle X Z)
        (cauchyPairingLimit hcoupling hle Y Z)) := by
  let XY := (strictJointCylinderStageAddQuadraticLipschitz
    hcoupling hle).mapCauchy X Y
  let rightSeq := fun n => CReal.add
    (cauchyPairingSeq hcoupling hle X Z n)
    (cauchyPairingSeq hcoupling hle Y Z n)
  apply CReal.Equiv_of_limit_of_equal
    (aSeq := cauchyPairingSeq hcoupling hle XY Z)
    (bSeq := rightSeq)
  · intro n
    exact strictJointCylinderStageReflectionBilinear_add_left
      hcoupling hle (X.seq n) (Y.seq n) (Z.seq n)
  · exact cauchyPairingSeq_converges hcoupling hle XY Z
  · exact YMGap.Constructive.TrigAddCReal.convergesTo_add
      (cauchyPairingSeq_converges hcoupling hle X Z)
      (cauchyPairingSeq_converges hcoupling hle Y Z)

theorem cauchyPairingLimit_add_right
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (X Y Z : (strictJointCylinderStageSquaredSeminorm hcoupling hle).Cauchy) :
    CReal.Equiv
      (cauchyPairingLimit hcoupling hle X
        ((strictJointCylinderStageAddQuadraticLipschitz
          hcoupling hle).mapCauchy Y Z))
      (CReal.add (cauchyPairingLimit hcoupling hle X Y)
        (cauchyPairingLimit hcoupling hle X Z)) := by
  let YZ := (strictJointCylinderStageAddQuadraticLipschitz
    hcoupling hle).mapCauchy Y Z
  let rightSeq := fun n => CReal.add
    (cauchyPairingSeq hcoupling hle X Y n)
    (cauchyPairingSeq hcoupling hle X Z n)
  apply CReal.Equiv_of_limit_of_equal
    (aSeq := cauchyPairingSeq hcoupling hle X YZ)
    (bSeq := rightSeq)
  · intro n
    exact strictJointCylinderStageReflectionBilinear_add_right
      hcoupling hle (X.seq n) (Y.seq n) (Z.seq n)
  · exact cauchyPairingSeq_converges hcoupling hle X YZ
  · exact YMGap.Constructive.TrigAddCReal.convergesTo_add
      (cauchyPairingSeq_converges hcoupling hle X Y)
      (cauchyPairingSeq_converges hcoupling hle X Z)

theorem strictJointCylinderCompletedInner_add_left
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (left right test : StrictJointCylinderOSCompletion hcoupling hle) :
    strictJointCylinderCompletedInner hcoupling hle
        (strictJointCylinderCompletedAdd hcoupling hle left right) test =
      CReal.RCadd
        (strictJointCylinderCompletedInner hcoupling hle left test)
        (strictJointCylinderCompletedInner hcoupling hle right test) := by
  refine Quotient.inductionOn₃ left right test ?_
  intro X Y Z
  exact Quotient.sound (cauchyPairingLimit_add_left hcoupling hle X Y Z)

theorem strictJointCylinderCompletedInner_add_right
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (test left right : StrictJointCylinderOSCompletion hcoupling hle) :
    strictJointCylinderCompletedInner hcoupling hle test
        (strictJointCylinderCompletedAdd hcoupling hle left right) =
      CReal.RCadd
        (strictJointCylinderCompletedInner hcoupling hle test left)
        (strictJointCylinderCompletedInner hcoupling hle test right) := by
  refine Quotient.inductionOn₃ test left right ?_
  intro X Y Z
  exact Quotient.sound (cauchyPairingLimit_add_right hcoupling hle X Y Z)

/-! ## 4. Rational homogeneity -/

theorem cauchyPairingLimit_smul_left
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (scalar : Q')
    (X Y : (strictJointCylinderStageSquaredSeminorm hcoupling hle).Cauchy) :
    CReal.Equiv
      (cauchyPairingLimit hcoupling hle
        ((strictJointCylinderStageSmulContinuous
          hcoupling hle scalar).mapCauchy X) Y)
      (CReal.mul (CReal.ofQ' scalar)
        (cauchyPairingLimit hcoupling hle X Y)) := by
  let SX := (strictJointCylinderStageSmulContinuous
    hcoupling hle scalar).mapCauchy X
  let rightSeq := fun n => CReal.mul (CReal.ofQ' scalar)
    (cauchyPairingSeq hcoupling hle X Y n)
  apply CReal.Equiv_of_limit_of_equal
    (aSeq := cauchyPairingSeq hcoupling hle SX Y)
    (bSeq := rightSeq)
  · intro n
    exact strictJointCylinderStageReflectionBilinear_smul_left
      hcoupling hle scalar (X.seq n) (Y.seq n)
  · exact cauchyPairingSeq_converges hcoupling hle SX Y
  · exact YMGap.Continuum.EffMassConvergence.convergesTo_scale scalar
      (cauchyPairingSeq_converges hcoupling hle X Y)

theorem cauchyPairingLimit_smul_right
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (scalar : Q')
    (X Y : (strictJointCylinderStageSquaredSeminorm hcoupling hle).Cauchy) :
    CReal.Equiv
      (cauchyPairingLimit hcoupling hle X
        ((strictJointCylinderStageSmulContinuous
          hcoupling hle scalar).mapCauchy Y))
      (CReal.mul (CReal.ofQ' scalar)
        (cauchyPairingLimit hcoupling hle X Y)) := by
  let SY := (strictJointCylinderStageSmulContinuous
    hcoupling hle scalar).mapCauchy Y
  let rightSeq := fun n => CReal.mul (CReal.ofQ' scalar)
    (cauchyPairingSeq hcoupling hle X Y n)
  apply CReal.Equiv_of_limit_of_equal
    (aSeq := cauchyPairingSeq hcoupling hle X SY)
    (bSeq := rightSeq)
  · intro n
    exact strictJointCylinderStageReflectionBilinear_smul_right
      hcoupling hle scalar (X.seq n) (Y.seq n)
  · exact cauchyPairingSeq_converges hcoupling hle X SY
  · exact YMGap.Continuum.EffMassConvergence.convergesTo_scale scalar
      (cauchyPairingSeq_converges hcoupling hle X Y)

theorem strictJointCylinderCompletedInner_smul_left
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (scalar : Q')
    (left right : StrictJointCylinderOSCompletion hcoupling hle) :
    strictJointCylinderCompletedInner hcoupling hle
        (strictJointCylinderCompletedSmul hcoupling hle scalar left) right =
      CReal.RCscale scalar
        (strictJointCylinderCompletedInner hcoupling hle left right) := by
  refine Quotient.inductionOn₂ left right ?_
  intro X Y
  exact Quotient.sound
    (cauchyPairingLimit_smul_left hcoupling hle scalar X Y)

theorem strictJointCylinderCompletedInner_smul_right
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (scalar : Q')
    (left right : StrictJointCylinderOSCompletion hcoupling hle) :
    strictJointCylinderCompletedInner hcoupling hle left
        (strictJointCylinderCompletedSmul hcoupling hle scalar right) =
      CReal.RCscale scalar
        (strictJointCylinderCompletedInner hcoupling hle left right) := by
  refine Quotient.inductionOn₂ left right ?_
  intro X Y
  exact Quotient.sound
    (cauchyPairingLimit_smul_right hcoupling hle scalar X Y)

#print axioms cauchyPairingLimit_symm
#print axioms strictJointCylinderCompletedInner_symm
#print axioms cauchyPairingLimit_self_nonneg
#print axioms strictJointCylinderCompletedInner_self_nonneg
#print axioms cauchyPairingLimit_add_left
#print axioms cauchyPairingLimit_add_right
#print axioms strictJointCylinderCompletedInner_add_left
#print axioms strictJointCylinderCompletedInner_add_right
#print axioms cauchyPairingLimit_smul_left
#print axioms cauchyPairingLimit_smul_right
#print axioms strictJointCylinderCompletedInner_smul_left
#print axioms strictJointCylinderCompletedInner_smul_right

end YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedInnerLaws
