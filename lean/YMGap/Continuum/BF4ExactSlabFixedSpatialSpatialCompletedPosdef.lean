/-
# Positive definiteness of the actual spatial completed pairing

The computed outer pairing rate controls each late term against its actual
limit. A zero limiting diagonal therefore supplies an explicit closeness
witness to the constant zero sequence, on the SAME spatial Cauchy quotient.
No representative or modulus is chosen from a propositional existence.

Completed Cauchy--Schwarz also follows from the same pairing limits. These
are pairing/separation results, not completed vector-space laws, metric
completeness, a full OS reconstruction or a continuum Hamiltonian.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialCompletedInner
import YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedPosdef

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialCompletedPosdef

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicSeminorm (PhysicalSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicDifference (difference)
open YMGap.Continuum.BF4ExactSlabFixedSpatialReflectedForm (scaleSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointPairingLaws (differenceSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedPhysicalTime (zero)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialPairingLaws
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialSeminorm
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialPhysicalTime
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialPairingLimit
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialCompletedInner
open YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedPosdef (late_limit_bound)
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (base : Nat)
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1) (hb : 0 < base)

local notation "D" => spatialSeminorm hw0 hw1 base hsmall hd hs hb
local notation "P" => spatialPairing hw0 hw1 base hsmall hd hs hb
local notation "B" => completedInner hw0 hw1 base hsmall hd hs hb

def completedZero : SpatialCompletion hw0 hw1 base hsmall hd hs hb :=
  spatialEmbedSpan hw0 hw1 base hsmall hd hs hb (zero base)

/-- The supplied pairing rate, not an extracted existence witness. -/
theorem pairSequence_limit_close (X Y : (D).Cauchy)
    (epsilon : Q') (he : (0 : Q') < epsilon) (n : Nat)
    (hn : pairRate hw0 hw1 base hsmall hd hs hb X Y epsilon ≤ n) :
    leRat (sub (pairSequence hw0 hw1 base hsmall hd hs hb X Y n)
      (representativeInner hw0 hw1 base hsmall hd hs hb X Y)) epsilon ∧
    leRat (sub (representativeInner hw0 hw1 base hsmall hd hs hb X Y)
      (pairSequence hw0 hw1 base hsmall hd hs hb X Y n)) epsilon :=
  late_limit_bound (pairSequence_converges hw0 hw1 base hsmall hd hs hb X Y)
    (pairSequence_bound hw0 hw1 base hsmall hd hs hb X Y) epsilon he n hn

theorem distSq_zero (x : PhysicalSpan base) :
    Equiv (spatialDistSq hw0 hw1 base hsmall hd hs hb x (zero base)) (P x x) := by
  have hz : differenceSpan x (zero base) = x := by
    apply Subtype.ext
    simp only [differenceSpan, zero, difference, scaleSpan, List.map_nil, List.append_nil]
  unfold spatialDistSq
  rw [hz]
  exact Equiv.refl _

/-- Zero norm constructs an actual closeness datum with the computed rate. -/
def closeZeroOfInnerZero (X : (D).Cauchy)
    (h : Equiv (representativeInner hw0 hw1 base hsmall hd hs hb X X) czero) :
    (D).Close X ((D).constant (zero base)) where
  modulus := pairRate hw0 hw1 base hsmall hd hs hb X X
  close := by
    intro epsilon he n hn
    have hbound := (pairSequence_limit_close hw0 hw1 base hsmall hd hs hb X X epsilon he n hn).1
    have hsub : Equiv
        (sub (pairSequence hw0 hw1 base hsmall hd hs hb X X n)
          (representativeInner hw0 hw1 base hsmall hd hs hb X X))
        (pairSequence hw0 hw1 base hsmall hd hs hb X X n) :=
      (CReal.sub_congr_right h).trans (SumOfSquares.Equiv_of_approx_eqv (fun k =>
        Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ (by decide : Q'.eqv (-0) 0))
          (QPoly.q_add_zero_eqv ((pairSequence hw0 hw1 base hsmall hd hs hb X X n).approx k))))
    exact leEv_trans (leEv_of_equiv (distSq_zero hw0 hw1 base hsmall hd hs hb (X.seq n)))
      (CReal.leRat_of_equiv hsub.symm hbound)

theorem completedZero_inner_zero :
    B (completedZero hw0 hw1 base hsmall hd hs hb)
      (completedZero hw0 hw1 base hsmall hd hs hb) = RCzero := by
  unfold completedZero
  rw [completedInner_embedSpan]
  exact Quotient.sound ((distSq_zero hw0 hw1 base hsmall hd hs hb (zero base)).symm.trans
    (spatialDistSq_refl hw0 hw1 base hsmall hd hs hb (zero base)))

/-- Positive definiteness on the actual Cauchy quotient, without completed linearity. -/
theorem completedInner_posdef (x : SpatialCompletion hw0 hw1 base hsmall hd hs hb) :
    B x x = RCzero ↔ x = completedZero hw0 hw1 base hsmall hd hs hb := by
  constructor
  · refine Quotient.inductionOn x ?_
    intro X h
    exact Quotient.sound ⟨closeZeroOfInnerZero hw0 hw1 base hsmall hd hs hb X (Quotient.exact h)⟩
  · intro h
    rw [h]
    exact completedZero_inner_zero hw0 hw1 base hsmall hd hs hb

theorem representativeInner_cauchySchwarz (X Y : (D).Cauchy) :
    leEv
      (mul (representativeInner hw0 hw1 base hsmall hd hs hb X Y)
        (representativeInner hw0 hw1 base hsmall hd hs hb X Y))
      (mul (representativeInner hw0 hw1 base hsmall hd hs hb X X)
        (representativeInner hw0 hw1 base hsmall hd hs hb Y Y)) :=
  leEv_of_convergesTo_le
    (Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz.CReal.convergesTo_mul_general
      (pairSequence_converges hw0 hw1 base hsmall hd hs hb X Y)
      (pairSequence_converges hw0 hw1 base hsmall hd hs hb X Y))
    (Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz.CReal.convergesTo_mul_general
      (pairSequence_converges hw0 hw1 base hsmall hd hs hb X X)
      (pairSequence_converges hw0 hw1 base hsmall hd hs hb Y Y))
    (fun n => spatialPairing_cauchySchwarz hw0 hw1 base hsmall hd hs hb (X.seq n) (Y.seq n))

theorem completedInner_cauchySchwarz (x y : SpatialCompletion hw0 hw1 base hsmall hd hs hb) :
    RCle (RCmul (B x y) (B x y)) (RCmul (B x x) (B y y)) := by
  refine Quotient.inductionOn₂ x y ?_
  exact representativeInner_cauchySchwarz hw0 hw1 base hsmall hd hs hb

#print axioms completedZero
#print axioms pairSequence_limit_close
#print axioms distSq_zero
#print axioms closeZeroOfInnerZero
#print axioms completedZero_inner_zero
#print axioms completedInner_posdef
#print axioms representativeInner_cauchySchwarz
#print axioms completedInner_cauchySchwarz

end YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialCompletedPosdef
