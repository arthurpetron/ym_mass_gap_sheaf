/-
# Cauchy--Schwarz for the completed positive physical BF4 Markov form

The physical macro transfer is self-adjoint and positive on its stationary
GNS carrier.  Therefore

  B_T(left,right) = <T left,right>

is itself a positive rational bilinear form.  This module packages that form
as a genuine `SmulGNSData`, obtains its sharp finite Cauchy--Schwarz inequality
from the existing constructive GNS algebra, and passes the inequality through
the explicit CReal completion.

This is finite-cutoff operator algebra.  It assumes no strict gap and makes no
continuum or cross-model claim.
-/

import YMGap.Continuum.BF4PhysicalMarkovGNSCompletion
import YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz

namespace YMGap.Continuum.BF4PhysicalCompletedMarkovFormCauchySchwarz

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4PhysicalMarkovGNSCompletion
open YMGap.Continuum.BF4PhysicalMarkovTransferLaws
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.HamiltonianScalar
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz

/-! ## 1. The finite positive Markov form -/

/-- The positive form selected by one physical BF4 macro transfer. -/
def centralPhysicalMarkovFormData
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat) : GNSData := by
  let D := (centralPhysicalSmulGNS w hw K half).toGNSData
  exact {
    V := D.V
    veq := D.veq
    veq_refl := D.veq_refl
    veq_symm := @D.veq_symm
    veq_trans := @D.veq_trans
    zero := D.zero
    add := D.add
    neg := D.neg
    smul := D.smul
    add_congr := @D.add_congr
    neg_congr := @D.neg_congr
    smul_congr := D.smul_congr
    add_assoc := D.add_assoc
    add_comm := D.add_comm
    zero_add := D.zero_add
    neg_add := D.neg_add
    B := fun left right =>
      D.B (centralPhysicalMarkovApply w hw K half left) right
    B_congr_left := by
      intro left left' right hleft
      exact D.B_congr_left right
        (centralPhysicalMarkovApply_congr w hw K half hleft)
    B_add_left := by
      intro left right test
      exact Q'.eqv_trans _ _ _
        (D.B_congr_left test
          (centralPhysicalMarkovApply_add w hw K half left right))
        (D.B_add_left
          (centralPhysicalMarkovApply w hw K half left)
          (centralPhysicalMarkovApply w hw K half right) test)
    B_smul_left := by
      intro scalar left right
      exact Q'.eqv_trans _ _ _
        (D.B_congr_left right
          (centralPhysicalMarkovApply_smul
            w hw K half scalar left))
        (D.B_smul_left scalar
          (centralPhysicalMarkovApply w hw K half left) right)
    B_symm := by
      intro left right
      exact Q'.eqv_trans _ _ _
        (Q'.eqv_symm
          (centralPhysicalMarkovApply_self_adjoint
            w hw K half left right))
        (D.B_symm left
          (centralPhysicalMarkovApply w hw K half right))
    self_nonneg := by
      intro observable
      exact centralPhysicalMarkovApply_positive_left
        w hw K half observable
  }

/-- The Markov form retains the physical rational module action. -/
def centralPhysicalMarkovFormGNS
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat) : SmulGNSData where
  toGNSData := centralPhysicalMarkovFormData w hw K half
  smul_sub := (centralPhysicalSmulGNS w hw K half).smul_sub

/-- Opaque computation rule for the Markov form. -/
theorem centralPhysicalMarkovFormGNS_B_eq
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat)
    (left right : EdgeLabelling → Q') :
    (centralPhysicalMarkovFormGNS w hw K half).toGNSData.B left right =
      centralPhysicalWeightedInner w hw K half
        (centralPhysicalMarkovApply w hw K half left) right :=
  rfl

/-- Sharp rational Cauchy--Schwarz for the positive physical Markov form. -/
theorem centralPhysicalMarkovForm_cauchy_schwarz
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat)
    (left right : EdgeLabelling → Q') :
    let form := fun first second =>
      centralPhysicalWeightedInner w hw K half
        (centralPhysicalMarkovApply w hw K half first) second
    form left right * form left right ≤
      form left left * form right right := by
  dsimp only
  exact (centralPhysicalMarkovFormGNS w hw K half).toGNSData.cauchy_schwarz
    left right

/-! ## 2. Passage through the physical GNS completion -/

/-- Representative-level Cauchy--Schwarz for the completed Markov form. -/
theorem centralPhysical_cinnerRep_markovForm_cauchy_schwarz
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat)
    (X Y : CauchyGNS
      (centralPhysicalSmulGNS w hw K half).toGNSData) :
    CReal.leEv
      (CReal.mul
        ((centralPhysicalSmulGNS w hw K half).toGNSData.cinnerRep
          ((centralPhysicalMarkovSymbol w hw K half).cDiagCauchy X) Y)
        ((centralPhysicalSmulGNS w hw K half).toGNSData.cinnerRep
          ((centralPhysicalMarkovSymbol w hw K half).cDiagCauchy X) Y))
      (CReal.mul
        ((centralPhysicalSmulGNS w hw K half).toGNSData.cinnerRep
          ((centralPhysicalMarkovSymbol w hw K half).cDiagCauchy X) X)
        ((centralPhysicalSmulGNS w hw K half).toGNSData.cinnerRep
          ((centralPhysicalMarkovSymbol w hw K half).cDiagCauchy Y) Y)) := by
  let D := (centralPhysicalSmulGNS w hw K half).toGNSData
  let TX := (centralPhysicalMarkovSymbol w hw K half).cDiagCauchy X
  let TY := (centralPhysicalMarkovSymbol w hw K half).cDiagCauchy Y
  apply CReal.leEv_of_convergesTo_le
    (CReal.convergesTo_mul_general
      (CReal.convergesTo_ofQ'CauchySeq
        (D.cInnerSeq TX Y) (D.cInnerQCauchy TX Y))
      (CReal.convergesTo_ofQ'CauchySeq
        (D.cInnerSeq TX Y) (D.cInnerQCauchy TX Y)))
    (CReal.convergesTo_mul_general
      (CReal.convergesTo_ofQ'CauchySeq
        (D.cInnerSeq TX X) (D.cInnerQCauchy TX X))
      (CReal.convergesTo_ofQ'CauchySeq
        (D.cInnerSeq TY Y) (D.cInnerQCauchy TY Y)))
  intro n
  let A := centralPhysicalWeightedInner w hw K half
    (centralPhysicalMarkovApply w hw K half (X.seq n)) (Y.seq n)
  let B := centralPhysicalWeightedInner w hw K half
    (centralPhysicalMarkovApply w hw K half (X.seq n)) (X.seq n)
  let C := centralPhysicalWeightedInner w hw K half
    (centralPhysicalMarkovApply w hw K half (Y.seq n)) (Y.seq n)
  have hfinite : A * A ≤ B * C :=
    centralPhysicalMarkovForm_cauchy_schwarz
      w hw K half (X.seq n) (Y.seq n)
  have hlift : CReal.leEv
      (CReal.mul (CReal.ofQ' A) (CReal.ofQ' A))
      (CReal.mul (CReal.ofQ' B) (CReal.ofQ' C)) := by
    intro epsilon hepsilon
    exact ⟨0, fun stage _ => Q'.le_trans' _ _ _ hfinite
      (Q'.add_le_self_of_nonneg _ epsilon (Q'.le_of_lt hepsilon))⟩
  simpa only [D, TX, TY, GNSData.cInnerSeq,
    DiagonalTransferSymbol.cDiagCauchy,
    centralPhysicalSmulGNS_B_eq, centralPhysicalMarkovSymbol_Dv_eq,
    A, B, C] using hlift

/-- Sharp Cauchy--Schwarz for `(x,y) |-> <T x,y>` on the completed physical
BF4 carrier. -/
theorem centralPhysicalCompletedMarkovForm_cauchy_schwarz
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat)
    (left right : CentralPhysicalGNSCompletion w hw K half) :
    CReal.RCle
      (CReal.RCmul
        ((centralPhysicalSmulGNS w hw K half).toGNSData.cinnerCompl
          (centralPhysicalCompletedMarkovTransfer w hw K half left) right)
        ((centralPhysicalSmulGNS w hw K half).toGNSData.cinnerCompl
          (centralPhysicalCompletedMarkovTransfer w hw K half left) right))
      (CReal.RCmul
        ((centralPhysicalSmulGNS w hw K half).toGNSData.cinnerCompl
          (centralPhysicalCompletedMarkovTransfer w hw K half left) left)
        ((centralPhysicalSmulGNS w hw K half).toGNSData.cinnerCompl
          (centralPhysicalCompletedMarkovTransfer w hw K half right) right)) := by
  refine Quotient.inductionOn₂ left right ?_
  intro X Y
  exact centralPhysical_cinnerRep_markovForm_cauchy_schwarz
    w hw K half X Y

end YMGap.Continuum.BF4PhysicalCompletedMarkovFormCauchySchwarz

#print axioms YMGap.Continuum.BF4PhysicalCompletedMarkovFormCauchySchwarz.centralPhysicalMarkovFormGNS
#print axioms YMGap.Continuum.BF4PhysicalCompletedMarkovFormCauchySchwarz.centralPhysicalMarkovForm_cauchy_schwarz
#print axioms YMGap.Continuum.BF4PhysicalCompletedMarkovFormCauchySchwarz.centralPhysical_cinnerRep_markovForm_cauchy_schwarz
#print axioms YMGap.Continuum.BF4PhysicalCompletedMarkovFormCauchySchwarz.centralPhysicalCompletedMarkovForm_cauchy_schwarz
