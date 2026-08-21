/-
# Laws of the completed physical BF4 cutoff inner form

The completed `RC`-valued form is now qualified intrinsically.  Each law is
proved first for arbitrary explicit-modulus Cauchy representatives by
uniqueness of the constructed outer limits, then descended through the
completion quotient.

The result is a positive symmetric rational-bilinear form on the actual
fixed-nome, fixed-half-extent completed carrier.  It is not yet equipped with
a cutoff-independent transfer, and no thermodynamic, continuum, or mass-gap
claim is made.

## Axiom gate

Only constructive convergence, quotient induction, and the proved dense
physical form laws are used.  No classical choice, noncomputable declaration,
custom axiom, or unproved placeholder is present.
-/

import YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInner
import YMGap.Continuum.SelfAdjointHamiltonian
import YMGap.Continuum.RCScaleClose
import YMGap.Continuum.EffMassConvergence

namespace YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInnerLaws

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffLinearGNSForm
open YMGap.Continuum.BF4PhysicalCutoffLinearGNSForm.CentralPhysicalLinearObservable
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletion
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedAlgebra
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInner
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInnerOuter
open YMGap.Continuum.CRealSeminormCompletion

/-! ## 1. Symmetry -/

theorem physicalCauchyPairingLimit_symm
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (X Y : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy) :
    CReal.Equiv
      (physicalCauchyPairingLimit hw0 hw1 half X Y)
      (physicalCauchyPairingLimit hw0 hw1 half Y X) := by
  apply CReal.Equiv_of_limit_of_equal
    (aSeq := physicalCauchyPairingSeq hw0 hw1 half X Y)
    (bSeq := physicalCauchyPairingSeq hw0 hw1 half Y X)
  · intro n
    exact innerLimit_symm hw0 hw1 half (X.seq n) (Y.seq n)
  · exact physicalCauchyPairingSeq_converges hw0 hw1 half X Y
  · exact physicalCauchyPairingSeq_converges hw0 hw1 half Y X

theorem centralPhysicalCutoffCompletedInner_symm
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (left right : CentralPhysicalCutoffLinearCompletion hw0 hw1 half) :
    centralPhysicalCutoffCompletedInner hw0 hw1 half left right =
      centralPhysicalCutoffCompletedInner hw0 hw1 half right left := by
  refine Quotient.inductionOn₂ left right ?_
  intro X Y
  exact Quotient.sound
    (physicalCauchyPairingLimit_symm hw0 hw1 half X Y)

/-! ## 2. Diagonal positivity -/

private theorem leEv_czero_of_convergesTo_nonneg
    {s : Nat -> CReal} {limit : CReal}
    (hconv : CReal.ConvergesTo s limit)
    (hnonneg : forall n : Nat, CReal.leEv CReal.czero (s n)) :
    CReal.leEv CReal.czero limit := by
  intro epsilon hepsilon
  let q := HalfPow.half * epsilon
  have hqpos : (0 : Q') < q := ExpNeg.half_mul_pos epsilon hepsilon
  obtain ⟨N, hN⟩ := hconv q hqpos
  obtain ⟨Kconv, hKconv⟩ := hN N (Nat.le_refl _)
  obtain ⟨Knonneg, hKnonneg⟩ := hnonneg N q hqpos
  refine ⟨max Kconv Knonneg, fun k hk => ?_⟩
  have hkconv : Kconv <= k := Nat.le_trans (Nat.le_max_left _ _) hk
  have hknonneg : Knonneg <= k := Nat.le_trans (Nat.le_max_right _ _) hk
  have hsLimit := (hKconv k hkconv).1
  have hzeroS := hKnonneg k hknonneg
  refine Q'.le_trans' _ _ _ hzeroS ?_
  refine Q'.le_trans' _ _ _
    (Q'.add_le_add_right _ _ q hsLimit) ?_
  exact Q'.le_of_eqv (Q'.eqv_trans _ _ _
    (Q'.add_assoc_eqv (limit.approx k) q q)
    (Q'.add_eqv_congr_left (limit.approx k) (q + q) epsilon
      (ExpNeg.two_halves epsilon)))

theorem physicalCauchyPairingLimit_self_nonneg
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (X : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy) :
    CReal.leEv CReal.czero
      (physicalCauchyPairingLimit hw0 hw1 half X X) := by
  apply leEv_czero_of_convergesTo_nonneg
    (physicalCauchyPairingSeq_converges hw0 hw1 half X X)
  intro n
  exact innerLimit_self_nonnegative hw0 hw1 half (X.seq n)

theorem centralPhysicalCutoffCompletedInner_self_nonneg
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (vector : CentralPhysicalCutoffLinearCompletion hw0 hw1 half) :
    CReal.RCnonneg
      (centralPhysicalCutoffCompletedInner hw0 hw1 half vector vector) := by
  refine Quotient.inductionOn vector ?_
  intro X
  exact physicalCauchyPairingLimit_self_nonneg hw0 hw1 half X

/-! ## 3. Additivity -/

theorem physicalCauchyPairingLimit_add_left
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (X Y Z : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy) :
    CReal.Equiv
      (physicalCauchyPairingLimit hw0 hw1 half
        ((physicalLinearAddQuadraticLipschitz
          hw0 hw1 half).mapCauchy X Y) Z)
      (CReal.add
        (physicalCauchyPairingLimit hw0 hw1 half X Z)
        (physicalCauchyPairingLimit hw0 hw1 half Y Z)) := by
  let XY := (physicalLinearAddQuadraticLipschitz
    hw0 hw1 half).mapCauchy X Y
  let rightSeq := fun n => CReal.add
    (physicalCauchyPairingSeq hw0 hw1 half X Z n)
    (physicalCauchyPairingSeq hw0 hw1 half Y Z n)
  apply CReal.Equiv_of_limit_of_equal
    (aSeq := physicalCauchyPairingSeq hw0 hw1 half XY Z)
    (bSeq := rightSeq)
  · intro n
    exact innerLimit_add_left hw0 hw1 half
      (X.seq n) (Y.seq n) (Z.seq n)
  · exact physicalCauchyPairingSeq_converges hw0 hw1 half XY Z
  · exact YMGap.Constructive.TrigAddCReal.convergesTo_add
      (physicalCauchyPairingSeq_converges hw0 hw1 half X Z)
      (physicalCauchyPairingSeq_converges hw0 hw1 half Y Z)

theorem physicalCauchyPairingLimit_add_right
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (X Y Z : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy) :
    CReal.Equiv
      (physicalCauchyPairingLimit hw0 hw1 half X
        ((physicalLinearAddQuadraticLipschitz
          hw0 hw1 half).mapCauchy Y Z))
      (CReal.add
        (physicalCauchyPairingLimit hw0 hw1 half X Y)
        (physicalCauchyPairingLimit hw0 hw1 half X Z)) := by
  let YZ := (physicalLinearAddQuadraticLipschitz
    hw0 hw1 half).mapCauchy Y Z
  let rightSeq := fun n => CReal.add
    (physicalCauchyPairingSeq hw0 hw1 half X Y n)
    (physicalCauchyPairingSeq hw0 hw1 half X Z n)
  apply CReal.Equiv_of_limit_of_equal
    (aSeq := physicalCauchyPairingSeq hw0 hw1 half X YZ)
    (bSeq := rightSeq)
  · intro n
    exact innerLimit_add_right hw0 hw1 half
      (X.seq n) (Y.seq n) (Z.seq n)
  · exact physicalCauchyPairingSeq_converges hw0 hw1 half X YZ
  · exact YMGap.Constructive.TrigAddCReal.convergesTo_add
      (physicalCauchyPairingSeq_converges hw0 hw1 half X Y)
      (physicalCauchyPairingSeq_converges hw0 hw1 half X Z)

theorem centralPhysicalCutoffCompletedInner_add_left
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (left right test : CentralPhysicalCutoffLinearCompletion hw0 hw1 half) :
    centralPhysicalCutoffCompletedInner hw0 hw1 half
        (completedPhysicalLinearAdd hw0 hw1 half left right) test =
      CReal.RCadd
        (centralPhysicalCutoffCompletedInner hw0 hw1 half left test)
        (centralPhysicalCutoffCompletedInner hw0 hw1 half right test) := by
  refine Quotient.inductionOn₃ left right test ?_
  intro X Y Z
  exact Quotient.sound
    (physicalCauchyPairingLimit_add_left hw0 hw1 half X Y Z)

theorem centralPhysicalCutoffCompletedInner_add_right
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (test left right : CentralPhysicalCutoffLinearCompletion hw0 hw1 half) :
    centralPhysicalCutoffCompletedInner hw0 hw1 half test
        (completedPhysicalLinearAdd hw0 hw1 half left right) =
      CReal.RCadd
        (centralPhysicalCutoffCompletedInner hw0 hw1 half test left)
        (centralPhysicalCutoffCompletedInner hw0 hw1 half test right) := by
  refine Quotient.inductionOn₃ test left right ?_
  intro X Y Z
  exact Quotient.sound
    (physicalCauchyPairingLimit_add_right hw0 hw1 half X Y Z)

/-! ## 4. Rational homogeneity -/

private theorem creal_mul_congr_right
    {scalar left right : CReal} (h : CReal.Equiv left right) :
    CReal.Equiv (CReal.mul scalar left) (CReal.mul scalar right) :=
  CReal.Equiv.trans (CRealAlg.cmul_comm scalar left)
    (CReal.Equiv.trans (CReal.mul_congr_left h)
      (CRealAlg.cmul_comm right scalar))

private theorem innerLimit_smul_right_local
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) (scalar : Q')
    (left right : CentralPhysicalLinearObservable) :
    CReal.Equiv
      (innerLimit hw0 hw1 half left (smul scalar right))
      (CReal.mul (CReal.ofQ' scalar)
        (innerLimit hw0 hw1 half left right)) :=
  CReal.Equiv.trans
    (innerLimit_symm hw0 hw1 half left (smul scalar right))
    (CReal.Equiv.trans
      (innerLimit_smul_left hw0 hw1 half scalar right left)
      (creal_mul_congr_right
        (innerLimit_symm hw0 hw1 half right left)))

theorem physicalCauchyPairingLimit_smul_left
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) (scalar : Q')
    (X Y : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy) :
    CReal.Equiv
      (physicalCauchyPairingLimit hw0 hw1 half
        ((physicalLinearSmulContinuous
          hw0 hw1 half scalar).mapCauchy X) Y)
      (CReal.mul (CReal.ofQ' scalar)
        (physicalCauchyPairingLimit hw0 hw1 half X Y)) := by
  let SX := (physicalLinearSmulContinuous
    hw0 hw1 half scalar).mapCauchy X
  let rightSeq := fun n => CReal.mul (CReal.ofQ' scalar)
    (physicalCauchyPairingSeq hw0 hw1 half X Y n)
  apply CReal.Equiv_of_limit_of_equal
    (aSeq := physicalCauchyPairingSeq hw0 hw1 half SX Y)
    (bSeq := rightSeq)
  · intro n
    exact innerLimit_smul_left hw0 hw1 half scalar (X.seq n) (Y.seq n)
  · exact physicalCauchyPairingSeq_converges hw0 hw1 half SX Y
  · exact YMGap.Continuum.EffMassConvergence.convergesTo_scale scalar
      (physicalCauchyPairingSeq_converges hw0 hw1 half X Y)

theorem physicalCauchyPairingLimit_smul_right
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) (scalar : Q')
    (X Y : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy) :
    CReal.Equiv
      (physicalCauchyPairingLimit hw0 hw1 half X
        ((physicalLinearSmulContinuous
          hw0 hw1 half scalar).mapCauchy Y))
      (CReal.mul (CReal.ofQ' scalar)
        (physicalCauchyPairingLimit hw0 hw1 half X Y)) := by
  let SY := (physicalLinearSmulContinuous
    hw0 hw1 half scalar).mapCauchy Y
  let rightSeq := fun n => CReal.mul (CReal.ofQ' scalar)
    (physicalCauchyPairingSeq hw0 hw1 half X Y n)
  apply CReal.Equiv_of_limit_of_equal
    (aSeq := physicalCauchyPairingSeq hw0 hw1 half X SY)
    (bSeq := rightSeq)
  · intro n
    exact innerLimit_smul_right_local hw0 hw1 half scalar
      (X.seq n) (Y.seq n)
  · exact physicalCauchyPairingSeq_converges hw0 hw1 half X SY
  · exact YMGap.Continuum.EffMassConvergence.convergesTo_scale scalar
      (physicalCauchyPairingSeq_converges hw0 hw1 half X Y)

theorem centralPhysicalCutoffCompletedInner_smul_left
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) (scalar : Q')
    (left right : CentralPhysicalCutoffLinearCompletion hw0 hw1 half) :
    centralPhysicalCutoffCompletedInner hw0 hw1 half
        (completedPhysicalLinearSmul hw0 hw1 half scalar left) right =
      CReal.RCscale scalar
        (centralPhysicalCutoffCompletedInner hw0 hw1 half left right) := by
  refine Quotient.inductionOn₂ left right ?_
  intro X Y
  exact Quotient.sound
    (physicalCauchyPairingLimit_smul_left
      hw0 hw1 half scalar X Y)

theorem centralPhysicalCutoffCompletedInner_smul_right
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) (scalar : Q')
    (left right : CentralPhysicalCutoffLinearCompletion hw0 hw1 half) :
    centralPhysicalCutoffCompletedInner hw0 hw1 half left
        (completedPhysicalLinearSmul hw0 hw1 half scalar right) =
      CReal.RCscale scalar
        (centralPhysicalCutoffCompletedInner hw0 hw1 half left right) := by
  refine Quotient.inductionOn₂ left right ?_
  intro X Y
  exact Quotient.sound
    (physicalCauchyPairingLimit_smul_right
      hw0 hw1 half scalar X Y)

/-! ## Axiom audit -/

#print axioms physicalCauchyPairingLimit_symm
#print axioms centralPhysicalCutoffCompletedInner_symm
#print axioms physicalCauchyPairingLimit_self_nonneg
#print axioms centralPhysicalCutoffCompletedInner_self_nonneg
#print axioms physicalCauchyPairingLimit_add_left
#print axioms physicalCauchyPairingLimit_add_right
#print axioms centralPhysicalCutoffCompletedInner_add_left
#print axioms centralPhysicalCutoffCompletedInner_add_right
#print axioms physicalCauchyPairingLimit_smul_left
#print axioms physicalCauchyPairingLimit_smul_right
#print axioms centralPhysicalCutoffCompletedInner_smul_left
#print axioms centralPhysicalCutoffCompletedInner_smul_right

end YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInnerLaws
