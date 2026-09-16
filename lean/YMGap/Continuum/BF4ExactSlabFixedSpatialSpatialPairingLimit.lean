/-
# Constructed mixed-pairing limit on the actual spatial Cauchy carrier

Representative-specific anchor ceilings and limiting sharp CS give an
explicit outer Cauchy rate. The actual spatialPairing is definitionally
the proved spatial ofQ'CauchySeq construction; its inner regularity is
therefore epsilon.den, by the directed rational constructor itself.
No canonical indexing is assumed and no existential modulus is chosen.

The completed scalar retains its explicit approximation-modulus witness.
Quotient descent is the next consumer; no metric-completeness assertion
or identification with fixed-width completions is made here.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialPairingBounds
import YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialPairingContinuity
import YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCanonicalPairingCompletion
import YMGap.Constructive.CRealCanonicalReciprocalIndex

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialPairingLimit

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialPairingLaws
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialSeminorm
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialPairingBounds
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialPairingContinuity
open YMGap.Continuum.BF4ExactSlabPlaquettePairingContinuity
  (pairingTolerance pairingTolerance_pos)

open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (base : Nat)
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1) (hb : 0 < base)

local notation "D" => spatialSeminorm hw0 hw1 base hsmall hd hs hb

def pairCeiling (X Y : (D).Cauchy) : Q' :=
  Q'.max' (normCeiling hw0 hw1 base hsmall hd hs hb X) (normCeiling hw0 hw1 base hsmall hd hs hb Y)

theorem pairCeiling_nonnegative (X Y : (D).Cauchy) :
    (0 : Q') ≤ pairCeiling hw0 hw1 base hsmall hd hs hb X Y :=
  Q'.le_trans' _ _ _ (normCeiling_nonnegative hw0 hw1 base hsmall hd hs hb X) (Q'.le_max'_left _ _)

def pairSequence (X Y : (D).Cauchy) (n : Nat) : CReal :=
  spatialPairing hw0 hw1 base hsmall hd hs hb (X.seq n) (Y.seq n)

def pairDelta (X Y : (D).Cauchy) (epsilon : Q') : Q' :=
  pairingTolerance (pairCeiling hw0 hw1 base hsmall hd hs hb X Y)
    (pairCeiling_nonnegative hw0 hw1 base hsmall hd hs hb X Y) epsilon

/-- The two original Cauchy moduli and their anchor indices remain data. -/
def rawRate (X Y : (D).Cauchy) (epsilon : Q') : Nat :=
  max (max (normBase hw0 hw1 base hsmall hd hs hb X) (normBase hw0 hw1 base hsmall hd hs hb Y))
    (max (X.modulus (pairDelta hw0 hw1 base hsmall hd hs hb X Y epsilon))
      (Y.modulus (pairDelta hw0 hw1 base hsmall hd hs hb X Y epsilon)))

theorem pairSequence_raw_bound (X Y : (D).Cauchy) :
    LeRatBound (pairSequence hw0 hw1 base hsmall hd hs hb X Y) (rawRate hw0 hw1 base hsmall hd hs hb X Y) := by
  intro epsilon he m n hm hn
  let B := pairCeiling hw0 hw1 base hsmall hd hs hb X Y
  let hB := pairCeiling_nonnegative hw0 hw1 base hsmall hd hs hb X Y
  let delta := pairDelta hw0 hw1 base hsmall hd hs hb X Y epsilon
  have hdeltaPos : (0 : Q') < delta := pairingTolerance_pos B hB he
  have hXbase : normBase hw0 hw1 base hsmall hd hs hb X ≤ n :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)) hn
  have hYbase : normBase hw0 hw1 base hsmall hd hs hb Y ≤ m :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)) hm
  have hXm : X.modulus delta ≤ m :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) hm
  have hXn : X.modulus delta ≤ n :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) hn
  have hYm : Y.modulus delta ≤ m :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) hm
  have hYn : Y.modulus delta ≤ n :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) hn
  exact pairing_close hw0 hw1 base hsmall hd hs hb (X.seq m) (X.seq n) (Y.seq m) (Y.seq n) B hB epsilon he
    (X.isCauchy delta hdeltaPos m n hXm hXn) (Y.isCauchy delta hdeltaPos m n hYm hYn)
    (leRat_mono (diagonal_le_normCeiling hw0 hw1 base hsmall hd hs hb Y m hYbase) (Q'.le_max'_right _ _))
    (leRat_mono (diagonal_le_normCeiling hw0 hw1 base hsmall hd hs hb X n hXbase) (Q'.le_max'_left _ _))

def pairRate (X Y : (D).Cauchy) : Q' → Nat :=
  closedRate canonicalReciprocalIndexData (rawRate hw0 hw1 base hsmall hd hs hb X Y)

theorem pairRate_antitone (X Y : (D).Cauchy) :
    MmonoPred (pairRate hw0 hw1 base hsmall hd hs hb X Y) :=
  closedRate_mmonoPred canonicalReciprocalIndexData (rawRate hw0 hw1 base hsmall hd hs hb X Y)

theorem pairSequence_bound (X Y : (D).Cauchy) :
    LeRatBound (pairSequence hw0 hw1 base hsmall hd hs hb X Y) (pairRate hw0 hw1 base hsmall hd hs hb X Y) :=
  LeRatBound.closed canonicalReciprocalIndexData (pairSequence_raw_bound hw0 hw1 base hsmall hd hs hb X Y)

/-- This explicit inner modulus comes from the actual spatial rational
Cauchy construction, not from elimination of any legacy existential. -/
theorem pairSequence_regular (X Y : (D).Cauchy) :
    RegPred (pairSequence hw0 hw1 base hsmall hd hs hb X Y) (fun _ epsilon => epsilon.den) := by
  unfold pairSequence spatialPairing BF4ExactSlabFixedSpatialSpatialLimit.spatialLimit
  exact ofQ'CauchySeq_family_regPred _ _

def representativeInner (X Y : (D).Cauchy) : CReal :=
  completeLimitFromRate (pairSequence hw0 hw1 base hsmall hd hs hb X Y)
    (pairRate hw0 hw1 base hsmall hd hs hb X Y) (fun _ epsilon => epsilon.den)
    (pairSequence_regular hw0 hw1 base hsmall hd hs hb X Y) (pairSequence_bound hw0 hw1 base hsmall hd hs hb X Y)

theorem pairSequence_converges (X Y : (D).Cauchy) :
    ConvergesTo (pairSequence hw0 hw1 base hsmall hd hs hb X Y)
      (representativeInner hw0 hw1 base hsmall hd hs hb X Y) :=
  convergesTo_completeLimitFromRate _ _ _ (pairSequence_regular hw0 hw1 base hsmall hd hs hb X Y)
    (pairSequence_bound hw0 hw1 base hsmall hd hs hb X Y) (pairRate_antitone hw0 hw1 base hsmall hd hs hb X Y)

/-- Approximation-modulus data for the newly computed scalar representative. -/
def representativeInnerCauchy (X Y : (D).Cauchy) :
    QCauchy (representativeInner hw0 hw1 base hsmall hd hs hb X Y).approx where
  M := fun epsilon => (HalfPow.half * (HalfPow.half * epsilon)).den
  bound := by
    intro epsilon he i j hi hj
    rcases Nat.le_total i j with hij | hji
    · exact diagSeqR_directed _ _ _ (pairSequence_regular hw0 hw1 base hsmall hd hs hb X Y)
        (pairSequence_bound hw0 hw1 base hsmall hd hs hb X Y) epsilon he i j hij hi
    · exact (diagSeqR_directed _ _ _ (pairSequence_regular hw0 hw1 base hsmall hd hs hb X Y)
        (pairSequence_bound hw0 hw1 base hsmall hd hs hb X Y) epsilon he j i hji hj).symm

end YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialPairingLimit

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialPairingLimit.pairCeiling
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialPairingLimit.pairCeiling_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialPairingLimit.pairSequence
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialPairingLimit.pairDelta
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialPairingLimit.rawRate
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialPairingLimit.pairSequence_raw_bound
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialPairingLimit.pairRate
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialPairingLimit.pairRate_antitone
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialPairingLimit.pairSequence_bound
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialPairingLimit.pairSequence_regular
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialPairingLimit.representativeInner
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialPairingLimit.pairSequence_converges
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialPairingLimit.representativeInnerCauchy
