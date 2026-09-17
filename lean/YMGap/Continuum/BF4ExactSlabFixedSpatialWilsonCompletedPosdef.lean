/-
# Positive definiteness on the actual completed Wilson carrier

The dense zero and distance-to-zero identity are proved for the SAME
intrinsic Wilson form. The existing generic separation theorem therefore
applies to its represented Cauchy completion. A zero representative norm
constructs closeness to the constant dense zero with the existing computed
pairing rate; no quotient representative or modulus is chosen from Prop.

This establishes completed norm separation and zero pairings, not full
Hilbert completeness, completed module laws, a new strict transfer bound,
full observable coverage, or a physical continuum limit.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCompletedInner
import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicAlgebra

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCompletedPosdef

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicSeminorm
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicAlgebra
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCompletedInner
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
  {base : Nat} (hb : 0<base)

local notation "D" => seminorm hw0 hw1 hsmall hd hs hb
local notation "P" => pairingData hw0 hw1 hsmall hd hs hb
local notation "V" => Completion hw0 hw1 hsmall hd hs hb
local notation "B" => completedInner hw0 hw1 hsmall hd hs hb

def completedZero : V := embed hw0 hw1 hsmall hd hs hb (zero base)

/-- Actual Type-valued closeness, with the SAME computed generic pairing rate. -/
def closeZeroOfInnerZero (X : (D).Cauchy)
    (h : Equiv (representativeInner hw0 hw1 hsmall hd hs hb X X) czero) :
    (D).Close X ((D).constant (zero base)) :=
  CRealSeminormPairingCompletion.closeZeroOfInnerZero P (zero base)
    (distSq_zero hw0 hw1 hsmall hd hs hb) X h

theorem closeZeroOfInnerZero_modulus (X : (D).Cauchy)
    (h : Equiv (representativeInner hw0 hw1 hsmall hd hs hb X X) czero) :
    (closeZeroOfInnerZero hw0 hw1 hsmall hd hs hb X h).modulus =
      CRealSeminormPairingCompletion.pairRate P X X := rfl

private theorem representativeInner_zero_left (X : (D).Cauchy) :
    Equiv (representativeInner hw0 hw1 hsmall hd hs hb ((D).constant (zero base)) X) czero :=
  Equiv_of_limit_of_equal
    (fun n => intrinsicForm_zero_left hw0 hw1 hsmall hd hs hb (X.seq n))
    (CRealSeminormPairingCompletion.pairSequence_converges P ((D).constant (zero base)) X)
    (convergesTo_const czero)

theorem completedInner_zero_left (x : V) :
    B (completedZero hw0 hw1 hsmall hd hs hb) x = RCzero := by
  refine Quotient.inductionOn x ?_
  intro X
  exact Quotient.sound (representativeInner_zero_left hw0 hw1 hsmall hd hs hb X)

theorem completedInner_zero_right (x : V) :
    B x (completedZero hw0 hw1 hsmall hd hs hb) = RCzero :=
  (completedInner_symm hw0 hw1 hsmall hd hs hb x (completedZero hw0 hw1 hsmall hd hs hb)).trans
    (completedInner_zero_left hw0 hw1 hsmall hd hs hb x)

theorem completedZero_inner_zero :
    B (completedZero hw0 hw1 hsmall hd hs hb) (completedZero hw0 hw1 hsmall hd hs hb) = RCzero :=
  completedInner_zero_left hw0 hw1 hsmall hd hs hb (completedZero hw0 hw1 hsmall hd hs hb)

/-- No new null vectors survive in this SAME represented Cauchy quotient. -/
theorem completedInner_posdef (x : V) :
    B x x = RCzero ↔ x = completedZero hw0 hw1 hsmall hd hs hb :=
  CRealSeminormPairingCompletion.completedInner_posdef P (zero base)
    (distSq_zero hw0 hw1 hsmall hd hs hb)
    (intrinsicForm_zero_left hw0 hw1 hsmall hd hs hb (zero base)) x

end YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCompletedPosdef

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCompletedPosdef.completedZero
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCompletedPosdef.closeZeroOfInnerZero
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCompletedPosdef.closeZeroOfInnerZero_modulus
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCompletedPosdef.completedInner_zero_left
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCompletedPosdef.completedInner_zero_right
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCompletedPosdef.completedZero_inner_zero
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCompletedPosdef.completedInner_posdef
