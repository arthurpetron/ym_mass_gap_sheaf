/-
# Constructive mixed-pairing limit on ORIGINAL plaquette Cauchy representatives

The norm ceiling is computed from a Cauchy anchor, the original insertion
coefficient bound and the original partition reciprocal. The pairing
continuity estimate then constructs an outer Cauchy rate. Per-term original
expectation moduli provide the inner regularity of the diagonal limit.

No boundedness or convergence premise is added. The representatives here
are those of the actual reflected seminorm completion; quotient descent is
the subsequent obligation.
-/

import YMGap.Continuum.BF4ExactSlabPlaquettePairingContinuity
import YMGap.Constructive.CRealCanonicalReciprocalIndex

namespace YMGap.Continuum.BF4ExactSlabPlaquettePairingLimit

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabPlaquetteFiniteGNS
open YMGap.Continuum.BF4ExactSlabPlaquetteReflectedForm
open YMGap.Continuum.BF4ExactSlabPlaquetteNullQuotient
open YMGap.Continuum.BF4ExactSlabPlaquetteSeminormCompletion
open YMGap.Continuum.BF4ExactSlabPlaquettePairingContinuity
open YMGap.Continuum.BF4ExactSlabOriginalActionReciprocal

private theorem four_bound {A B : CReal} {a b : Q'}
    (hA : leEv A (ofQ' a)) (hB : leEv B (ofQ' b)) :
    leEv (CReal.add (CReal.add A A) (CReal.add B B)) (ofQ' ((a + a) + (b + b))) := by
  have h := leEv_add (leEv_add hA hA) (leEv_add hB hB)
  rw [ofQ'_add, ofQ'_add, ofQ'_add] at h
  exact h

variable (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {half : Nat}

local notation "D" => seminorm w hw0 hw1 half

def diagonalCeiling (e : PlaquetteExpression half) : Q' :=
  rawBound w e e * reciprocalCeiling w hw0 hw1 half

theorem diagonalCeiling_nonnegative (e : PlaquetteExpression half) : (0 : Q') ≤ diagonalCeiling w hw0 hw1 e :=
  Q'.mul_nonneg _ _ (rawBound_nonnegative w hw0 e e) (Q'.le_of_lt (reciprocalCeiling_pos w hw0 hw1 half))

theorem diagonal_approx_le (e : PlaquetteExpression half) (n : Nat) :
    (form w hw0 hw1 e e).approx n ≤ diagonalCeiling w hw0 hw1 e :=
  Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _
    (Q'.le_trans' _ _ _ (Q'.le_abs_self _) (rawLimit_approx_abs_le w hw0 hw1 e e n))
    (Q'.le_of_lt (actionReciprocal_approx_pos w hw0 hw1 half n)))
    (Q'.mul_le_mul_of_nonneg_left _ _ _ (actionReciprocal_approx_le w hw0 hw1 half n)
      (rawBound_nonnegative w hw0 e e))

theorem diagonal_le_ceiling (e : PlaquetteExpression half) :
    leEv (form w hw0 hw1 e e) (ofQ' (diagonalCeiling w hw0 hw1 e)) :=
  leEv_le_ofQ'_of_approx_le (diagonal_approx_le w hw0 hw1 e)

def normBase (X : (D).Cauchy) : Nat := X.modulus 1

def normCeiling (X : (D).Cauchy) : Q' :=
  (1 + 1) + (diagonalCeiling w hw0 hw1 (X.seq (normBase w hw0 hw1 X)) +
    diagonalCeiling w hw0 hw1 (X.seq (normBase w hw0 hw1 X)))

theorem normCeiling_nonnegative (X : (D).Cauchy) : (0 : Q') ≤ normCeiling w hw0 hw1 X :=
  Q'.zero_le_add _ _ (by decide)
    (Q'.zero_le_add _ _ (diagonalCeiling_nonnegative w hw0 hw1 _) (diagonalCeiling_nonnegative w hw0 hw1 _))

theorem diagonal_anchor_bound (e anchor : PlaquetteExpression half) :
    leEv (form w hw0 hw1 e e)
      (CReal.add
        (CReal.add (distSq w hw0 hw1 e anchor) (distSq w hw0 hw1 e anchor))
        (CReal.add (form w hw0 hw1 anchor anchor) (form w hw0 hw1 anchor anchor))) := by
  have he : expressionEqv (.add (subtract e anchor) anchor) e :=
    (finiteGNSData w (Q'.le_of_lt hw0) 0 half).sub_add_cancel e anchor
  have h := pairing_add_bound w hw0 hw1 (subtract e anchor) anchor
  rw [pairing_congr w hw0 hw1 he he] at h
  exact h

theorem diagonal_le_normCeiling (X : (D).Cauchy) (n : Nat) (hn : normBase w hw0 hw1 X ≤ n) :
    leEv (form w hw0 hw1 (X.seq n) (X.seq n)) (ofQ' (normCeiling w hw0 hw1 X)) := by
  let anchor := X.seq (normBase w hw0 hw1 X)
  have hdist : leEv (distSq w hw0 hw1 (X.seq n) anchor) (ofQ' 1) :=
    X.isCauchy 1 (by decide) n (normBase w hw0 hw1 X) hn (Nat.le_refl _)
  exact leEv_trans (diagonal_anchor_bound w hw0 hw1 (X.seq n) anchor)
    (four_bound hdist (diagonal_le_ceiling w hw0 hw1 anchor))

def pairCeiling (X Y : (D).Cauchy) : Q' := Q'.max' (normCeiling w hw0 hw1 X) (normCeiling w hw0 hw1 Y)

theorem pairCeiling_nonnegative (X Y : (D).Cauchy) : (0 : Q') ≤ pairCeiling w hw0 hw1 X Y :=
  Q'.le_trans' _ _ _ (normCeiling_nonnegative w hw0 hw1 X) (Q'.le_max'_left _ _)

def pairSequence (X Y : (D).Cauchy) (n : Nat) : CReal := form w hw0 hw1 (X.seq n) (Y.seq n)

def pairDelta (X Y : (D).Cauchy) (epsilon : Q') : Q' :=
  pairingTolerance (pairCeiling w hw0 hw1 X Y) (pairCeiling_nonnegative w hw0 hw1 X Y) epsilon

def rawRate (X Y : (D).Cauchy) (epsilon : Q') : Nat :=
  max (max (normBase w hw0 hw1 X) (normBase w hw0 hw1 Y))
    (max (X.modulus (pairDelta w hw0 hw1 X Y epsilon)) (Y.modulus (pairDelta w hw0 hw1 X Y epsilon)))

theorem pairSequence_raw_bound (X Y : (D).Cauchy) : LeRatBound (pairSequence w hw0 hw1 X Y) (rawRate w hw0 hw1 X Y) := by
  intro epsilon he m n hm hn
  let B := pairCeiling w hw0 hw1 X Y
  let hB := pairCeiling_nonnegative w hw0 hw1 X Y
  let delta := pairDelta w hw0 hw1 X Y epsilon
  have hd : (0 : Q') < delta := pairingTolerance_pos B hB he
  have hXbase : normBase w hw0 hw1 X ≤ n :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)) hn
  have hYbase : normBase w hw0 hw1 Y ≤ m :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)) hm
  have hXm : X.modulus delta ≤ m := Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) hm
  have hXn : X.modulus delta ≤ n := Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) hn
  have hYm : Y.modulus delta ≤ m := Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) hm
  have hYn : Y.modulus delta ≤ n := Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) hn
  exact pairing_close w hw0 hw1 (X.seq m) (X.seq n) (Y.seq m) (Y.seq n) B hB epsilon he
    (X.isCauchy delta hd m n hXm hXn) (Y.isCauchy delta hd m n hYm hYn)
    (leRat_mono (diagonal_le_normCeiling w hw0 hw1 Y m hYbase) (Q'.le_max'_right _ _))
    (leRat_mono (diagonal_le_normCeiling w hw0 hw1 X n hXbase) (Q'.le_max'_left _ _))

def pairRate (X Y : (D).Cauchy) : Q' → Nat := closedRate canonicalReciprocalIndexData (rawRate w hw0 hw1 X Y)

theorem pairRate_antitone (X Y : (D).Cauchy) : MmonoPred (pairRate w hw0 hw1 X Y) :=
  closedRate_mmonoPred canonicalReciprocalIndexData (rawRate w hw0 hw1 X Y)

theorem pairSequence_bound (X Y : (D).Cauchy) : LeRatBound (pairSequence w hw0 hw1 X Y) (pairRate w hw0 hw1 X Y) :=
  LeRatBound.closed canonicalReciprocalIndexData (pairSequence_raw_bound w hw0 hw1 X Y)

def pairReg (X Y : (D).Cauchy) (n : Nat) (epsilon : Q') : Nat :=
  (formCauchy w hw0 hw1 (X.seq n) (Y.seq n)).M epsilon

theorem pairSequence_regular (X Y : (D).Cauchy) : RegPred (pairSequence w hw0 hw1 X Y) (pairReg w hw0 hw1 X Y) :=
  fun n => (formCauchy w hw0 hw1 (X.seq n) (Y.seq n)).bound

/-- Diagonal limit constructed from explicit outer and inner moduli. -/
def representativeInner (X Y : (D).Cauchy) : CReal :=
  completeLimitFromRate (pairSequence w hw0 hw1 X Y) (pairRate w hw0 hw1 X Y) (pairReg w hw0 hw1 X Y)
    (pairSequence_regular w hw0 hw1 X Y) (pairSequence_bound w hw0 hw1 X Y)

theorem pairSequence_converges (X Y : (D).Cauchy) :
    ConvergesTo (pairSequence w hw0 hw1 X Y) (representativeInner w hw0 hw1 X Y) :=
  convergesTo_completeLimitFromRate _ _ _ (pairSequence_regular w hw0 hw1 X Y)
    (pairSequence_bound w hw0 hw1 X Y) (pairRate_antitone w hw0 hw1 X Y)

/-- The completed representative itself retains an explicit approximation modulus. -/
def representativeInnerCauchy (X Y : (D).Cauchy) : QCauchy (representativeInner w hw0 hw1 X Y).approx where
  M := fun epsilon => (HalfPow.half * (HalfPow.half * epsilon)).den
  bound := by
    intro epsilon he i j hi hj
    rcases Nat.le_total i j with hij | hji
    · exact diagSeqR_directed _ _ _ (pairSequence_regular w hw0 hw1 X Y) (pairSequence_bound w hw0 hw1 X Y) epsilon he i j hij hi
    · exact (diagSeqR_directed _ _ _ (pairSequence_regular w hw0 hw1 X Y) (pairSequence_bound w hw0 hw1 X Y) epsilon he j i hji hj).symm

end YMGap.Continuum.BF4ExactSlabPlaquettePairingLimit

#print axioms YMGap.Continuum.BF4ExactSlabPlaquettePairingLimit.diagonalCeiling
#print axioms YMGap.Continuum.BF4ExactSlabPlaquettePairingLimit.diagonalCeiling_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabPlaquettePairingLimit.diagonal_approx_le
#print axioms YMGap.Continuum.BF4ExactSlabPlaquettePairingLimit.diagonal_le_ceiling
#print axioms YMGap.Continuum.BF4ExactSlabPlaquettePairingLimit.normBase
#print axioms YMGap.Continuum.BF4ExactSlabPlaquettePairingLimit.normCeiling
#print axioms YMGap.Continuum.BF4ExactSlabPlaquettePairingLimit.normCeiling_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabPlaquettePairingLimit.diagonal_anchor_bound
#print axioms YMGap.Continuum.BF4ExactSlabPlaquettePairingLimit.diagonal_le_normCeiling
#print axioms YMGap.Continuum.BF4ExactSlabPlaquettePairingLimit.pairCeiling
#print axioms YMGap.Continuum.BF4ExactSlabPlaquettePairingLimit.pairCeiling_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabPlaquettePairingLimit.pairSequence
#print axioms YMGap.Continuum.BF4ExactSlabPlaquettePairingLimit.pairDelta
#print axioms YMGap.Continuum.BF4ExactSlabPlaquettePairingLimit.rawRate
#print axioms YMGap.Continuum.BF4ExactSlabPlaquettePairingLimit.pairSequence_raw_bound
#print axioms YMGap.Continuum.BF4ExactSlabPlaquettePairingLimit.pairRate
#print axioms YMGap.Continuum.BF4ExactSlabPlaquettePairingLimit.pairRate_antitone
#print axioms YMGap.Continuum.BF4ExactSlabPlaquettePairingLimit.pairSequence_bound
#print axioms YMGap.Continuum.BF4ExactSlabPlaquettePairingLimit.pairReg
#print axioms YMGap.Continuum.BF4ExactSlabPlaquettePairingLimit.pairSequence_regular
#print axioms YMGap.Continuum.BF4ExactSlabPlaquettePairingLimit.representativeInner
#print axioms YMGap.Continuum.BF4ExactSlabPlaquettePairingLimit.pairSequence_converges
#print axioms YMGap.Continuum.BF4ExactSlabPlaquettePairingLimit.representativeInnerCauchy
