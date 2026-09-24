/-
# Completion of the literal-width all-nome Wilson reflected form

The squared-distance Cauchy quotient and its mixed pairing are constructed
from the SAME original fixed-width form. Both inner and outer moduli are
data. Dense Wilson loops retain their original two-time moments, and the
constant state has norm one. No face-span or small-nome completion is used.

This constructs a represented Cauchy completion with a pairing, not the full
Hilbert/OS/QFT package. Completed time descent, a same-carrier strict gap,
spatial/scaling control and nonzero continuum survival are separate claims.
-/

import YMGap.Continuum.BF4WilsonAllNomePairingContinuity
import YMGap.Continuum.BF4WilsonAllNomeLoopTimePin
import YMGap.Continuum.CRealSeminormPairingPosdef
import YMGap.Continuum.BoundedRationalCauchyProduct

namespace YMGap.Continuum.BF4WilsonAllNomeCompletedInner

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowJointCauchy
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm
  (IntrinsicExpression chart chart_within unit)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPhysicalTime (advance)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe (SourceLoop)
open YMGap.Continuum.BF4WilsonAllNomeReflectedForm
open YMGap.Continuum.BF4WilsonAllNomeFormLaws (intrinsicForm_unit_unit)
open YMGap.Continuum.BF4WilsonAllNomeCauchySchwarz (intrinsicForm_cauchySchwarz)
open YMGap.Continuum.BF4WilsonAllNomeSeminorm (seminorm)
open YMGap.Continuum.BF4WilsonAllNomeLoopTimePin (loopState time_pairing_lag)
open YMGap.Continuum.BF4WilsonAllNomeMomentConvexity (lagMoment)
open YMGap.Continuum.CRealSeminormPairingCompletion (PairingData)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))

/-- The original diagonal sequence supplies the actual inner modulus;
no witness is extracted from the propositional CReal Cauchy field. -/
def intrinsicFormCauchy {width : Nat} (x y : IntrinsicExpression width) :
    QCauchy (intrinsicForm hw0 hw1 x y).approx :=
  BoundedRationalCauchyProduct.representativeCauchy _
    (originalJointCauchy hw0 hw1 (2 * max x.radius y.radius)
      (.mul (mirror (max x.radius y.radius) (chart (max x.radius y.radius) x))
        (chart (max x.radius y.radius) y))
      ⟨mirror_within _ _, within_mono (by omega) _
        (chart_within _ y (Nat.le_max_right _ _))⟩)

/-- All quantitative fields are proved on the actual form. -/
def pairingData {width : Nat} : PairingData (seminorm hw0 hw1 (width := width)) where
  pairing := intrinsicForm hw0 hw1
  pairingCauchy := intrinsicFormCauchy hw0 hw1
  diagonal_anchor_bound := BF4WilsonAllNomePairingContinuity.diagonal_anchor_bound hw0 hw1
  pairing_close := BF4WilsonAllNomePairingContinuity.pairing_close hw0 hw1

def Completion (width : Nat) := (seminorm hw0 hw1 (width := width)).Completion

def embed {width : Nat} (x : IntrinsicExpression width) : Completion hw0 hw1 width :=
  (seminorm hw0 hw1).embedRep x

def completedInner {width : Nat} (x y : Completion hw0 hw1 width) : RC :=
  CRealSeminormPairingCompletion.completedInner (pairingData hw0 hw1) x y

theorem completedInner_embed {width : Nat} (x y : IntrinsicExpression width) :
    completedInner hw0 hw1 (embed hw0 hw1 x) (embed hw0 hw1 y) =
      Quotient.mk crealSetoid (intrinsicForm hw0 hw1 x y) :=
  CRealSeminormPairingCompletion.completedInner_embedRep (pairingData hw0 hw1) x y

theorem completedInner_symm {width : Nat} (x y : Completion hw0 hw1 width) :
    completedInner hw0 hw1 x y = completedInner hw0 hw1 y x :=
  CRealSeminormPairingCompletion.completedInner_symm (pairingData hw0 hw1)
    (intrinsicForm_symm hw0 hw1) x y

theorem completedInner_nonnegative {width : Nat} (x : Completion hw0 hw1 width) :
    RCnonneg (completedInner hw0 hw1 x x) :=
  CRealSeminormPairingCompletion.completedInner_nonnegative (pairingData hw0 hw1)
    (intrinsicForm_nonnegative hw0 hw1) x

theorem completedInner_cauchySchwarz {width : Nat} (x y : Completion hw0 hw1 width) :
    RCle (RCmul (completedInner hw0 hw1 x y) (completedInner hw0 hw1 x y))
      (RCmul (completedInner hw0 hw1 x x) (completedInner hw0 hw1 y y)) :=
  CRealSeminormPairingCompletion.completedInner_cauchySchwarz (pairingData hw0 hw1)
    (intrinsicForm_cauchySchwarz hw0 hw1) x y

def unitState (width : Nat) : Completion hw0 hw1 width := embed hw0 hw1 (unit width)

theorem unitState_norm_one (width : Nat) :
    completedInner hw0 hw1 (unitState hw0 hw1 width) (unitState hw0 hw1 width) =
      Quotient.mk crealSetoid (ofQ' 1) :=
  CRealSeminormPairingCompletion.completedInner_unit_norm_one (pairingData hw0 hw1)
    (unit width) (intrinsicForm_unit_unit hw0 hw1)

/-- These are embeddings of actual advanced expressions, not a silently
assumed completed time operator. -/
theorem completed_loop_time_pairing {width : Nat} (loop : SourceLoop width) (m n : Nat) :
    completedInner hw0 hw1 (embed hw0 hw1 (advance m (loopState loop)))
      (embed hw0 hw1 (advance n (loopState loop))) =
        Quotient.mk crealSetoid (lagMoment hw0 hw1 loop (m+n)) :=
  (completedInner_embed hw0 hw1 _ _).trans
    (Quotient.sound (time_pairing_lag hw0 hw1 loop m n))

#print axioms intrinsicFormCauchy
#print axioms pairingData
#print axioms completedInner
#print axioms completedInner_embed
#print axioms completedInner_symm
#print axioms completedInner_nonnegative
#print axioms completedInner_cauchySchwarz
#print axioms unitState_norm_one
#print axioms completed_loop_time_pairing

end YMGap.Continuum.BF4WilsonAllNomeCompletedInner
