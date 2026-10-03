/-
# Literal root-polynomial pins to the EXISTING original finite maps

The quotient is N*(I-R_depth)*T(1), and the finite log sum has terms
invSucc(k)*T(1)*(I-T(1))^(k+1), k<m. The coarse moment pins identify
these actual diagonal forms on the same completion. No inequality, inverse,
spectral interpretation or equality of the two limiting maps is asserted.
-/

import YMGap.Continuum.BF4WilsonAllNomeRootCoarseMoment
import YMGap.Continuum.BF4WilsonAllNomeDyadicDerivative
import YMGap.Continuum.BF4WilsonAllNomeLogPartial

namespace YMGap.Continuum.BF4WilsonAllNomeRootLogMapPins

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Constructive.QPolyPositivePrimitive (polynomialPower)
open YMGap.Constructive.QPolyRootLogDifference (rootDefect)
open YMGap.Constructive.QPolyFiniteLogDerivative (finiteLog)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4WilsonAllNomeLinear (completedAdd completedZero)
open YMGap.Continuum.BF4WilsonAllNomeLinearLaws (completedAdd_zero)
open YMGap.Continuum.BF4WilsonAllNomeBilinearTime
open YMGap.Continuum.BF4WilsonAllNomeDyadicSemigroup (meshAction)
open YMGap.Continuum.BF4WilsonAllNomeDyadicEnergy (full_mesh_time)
open YMGap.Continuum.BF4WilsonAllNomeDyadicDefectDecay (defect time_defect moment)
open YMGap.Continuum.BF4WilsonAllNomeTimeDefectMoments (mixedMoment time_defectPower)
open YMGap.Continuum.BF4WilsonAllNomeRootPolynomialForm
open YMGap.Continuum.BF4WilsonAllNomeRootCoarseMoment
open YMGap.Continuum.BF4WilsonAllNomeDyadicDerivative (differenceQuotient)
open YMGap.Continuum.BF4WilsonAllNomeLogPartial (logTerm logTail logPartial logPartial_add_tail)
open YMGap.Continuum.BF4WilsonAllNomePositiveTimeTail (positiveTimeTail)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "T" => completedTime hw0 hw1

/-- The actual quotient diagonal is the actual full-stride root moment,
including depth zero and states in the one-step boundary kernel. -/
theorem differenceQuotient_diagonal_pin (depth : Nat) (x : V) :
    B x (differenceQuotient hw0 hw1 depth x) =
      RCscale (Q'.ofNat (2^depth)) (moment hw0 hw1 depth x (2^depth) 1) := by
  unfold differenceQuotient
  rw [completedInner_smul_right]
  apply congrArg (RCscale (Q'.ofNat (2^depth)))
  have h : meshAction hw0 hw1 depth (2^depth) (defect hw0 hw1 depth x) =
      defect hw0 hw1 depth (T 1 x) :=
    (time_defect hw0 hw1 depth (2^depth) depth x).trans
      (congrArg (defect hw0 hw1 depth) (full_mesh_time hw0 hw1 depth x))
  change B x (defect hw0 hw1 depth (T 1 x)) =
    B x (meshAction hw0 hw1 depth (2^depth) (defect hw0 hw1 depth x))
  exact congrArg (B x) h.symm

private theorem logPartial_succ (m : Nat) (x : V) :
    logPartial hw0 hw1 (m+1) x =
      completedAdd hw0 hw1 (logPartial hw0 hw1 m x) (logTerm hw0 hw1 m x) := by
  simpa only [logTail, completedAdd_zero] using logPartial_add_tail hw0 hw1 x m 1

private theorem logTerm_diagonal_pin (k : Nat) (x : V) :
    B x (logTerm hw0 hw1 k x) =
      RCscale (Q'.invSucc k) (mixedMoment hw0 hw1 x 1 (k+1)) := by
  unfold logTerm
  rw [completedInner_smul_right]
  apply congrArg (RCscale (Q'.invSucc k))
  change B x (BF4WilsonAllNomeTimeDefectMoments.defectPower hw0 hw1 (k+1) (T 1 x)) =
    B x (T 1 (BF4WilsonAllNomeTimeDefectMoments.defectPower hw0 hw1 (k+1) x))
  exact congrArg (B x) (time_defectPower hw0 hw1 (k+1) 1 x).symm

/-- The ACTUAL root-polynomial finite log form is the diagonal of the existing
logPartial map. The term exponent is k+1 and the scalar is invSucc(k). -/
theorem finiteLog_diagonal_pin (depth : Nat) (x : V) (m : Nat) :
    form hw0 hw1 depth x (2^depth) (finiteLog (rootDefect (2^depth-1)) m) 0 =
      B x (logPartial hw0 hw1 m x) := by
  induction m with
  | zero =>
      change RCzero = B x (completedZero hw0 hw1 width)
      rw [completedInner_zero_right]
  | succ m ih =>
      change form hw0 hw1 depth x (2^depth)
        (QPoly.padd (finiteLog (rootDefect (2^depth-1)) m)
          (QPoly.pscale (Q'.invSucc m)
            (polynomialPower (rootDefect (2^depth-1)) (m+1)))) 0 = _
      rw [form_padd, form_pscale, ih, logPartial_succ, completedInner_add_right,
        logTerm_diagonal_pin]
      have h := form_coarseDefectPower hw0 hw1 depth x 1 (m+1)
      simpa only [Nat.one_mul] using congrArg
        (fun z => RCadd (B x (logPartial hw0 hw1 m x)) (RCscale (Q'.invSucc m) z)) h

#print axioms differenceQuotient_diagonal_pin
#print axioms finiteLog_diagonal_pin

end YMGap.Continuum.BF4WilsonAllNomeRootLogMapPins
