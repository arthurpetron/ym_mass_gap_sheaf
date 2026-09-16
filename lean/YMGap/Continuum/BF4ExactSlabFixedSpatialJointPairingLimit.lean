/-
# Constructive representative limit of the actual joint reflected pairing

Computed anchor ceilings and actual joint-pairing continuity give an outer
Cauchy rate. The original joint chart construction is literally an
ofQ'CauchySeq, so its inner regularity is the explicit epsilon.den. Closing
the outer rate and taking the generic explicit diagonal constructs this
representative without a chosen modulus or an assumed boundedness premise.
The pairing is not yet descended here; nome and spatial width remain fixed.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialJointPairingBounds
import YMGap.Continuum.BF4ExactSlabFixedSpatialJointPairingContinuity
import YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCanonicalPairingCompletion
import YMGap.Constructive.CRealCanonicalReciprocalIndex

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialJointPairingLimit

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialChartJointLimits
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointSeminorm
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointPairingBounds
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointPairingContinuity
open YMGap.Continuum.BF4ExactSlabPlaquettePairingContinuity
  (pairingTolerance pairingTolerance_pos)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (width : Nat)

local notation "D" => jointSeminorm hw0 hw1 width

def pairCeiling (X Y : (D).Cauchy) : Q' :=
  Q'.max' (normCeiling hw0 hw1 width X) (normCeiling hw0 hw1 width Y)

theorem pairCeiling_nonnegative (X Y : (D).Cauchy) :
    (0 : Q') ≤ pairCeiling hw0 hw1 width X Y :=
  Q'.le_trans' _ _ _ (normCeiling_nonnegative hw0 hw1 width X) (Q'.le_max'_left _ _)

def pairSequence (X Y : (D).Cauchy) (n : Nat) : CReal :=
  jointPairing hw0 hw1 width (X.seq n) (Y.seq n)

def pairDelta (X Y : (D).Cauchy) (epsilon : Q') : Q' :=
  pairingTolerance (pairCeiling hw0 hw1 width X Y)
    (pairCeiling_nonnegative hw0 hw1 width X Y) epsilon

/-- The two original Cauchy moduli and their anchor indices remain data. -/
def rawRate (X Y : (D).Cauchy) (epsilon : Q') : Nat :=
  max (max (normBase hw0 hw1 width X) (normBase hw0 hw1 width Y))
    (max (X.modulus (pairDelta hw0 hw1 width X Y epsilon))
      (Y.modulus (pairDelta hw0 hw1 width X Y epsilon)))

theorem pairSequence_raw_bound (X Y : (D).Cauchy) :
    LeRatBound (pairSequence hw0 hw1 width X Y) (rawRate hw0 hw1 width X Y) := by
  intro epsilon he m n hm hn
  let B := pairCeiling hw0 hw1 width X Y
  let hB := pairCeiling_nonnegative hw0 hw1 width X Y
  let delta := pairDelta hw0 hw1 width X Y epsilon
  have hd : (0 : Q') < delta := pairingTolerance_pos B hB he
  have hXbase : normBase hw0 hw1 width X ≤ n :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)) hn
  have hYbase : normBase hw0 hw1 width Y ≤ m :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)) hm
  have hXm : X.modulus delta ≤ m :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) hm
  have hXn : X.modulus delta ≤ n :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) hn
  have hYm : Y.modulus delta ≤ m :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) hm
  have hYn : Y.modulus delta ≤ n :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) hn
  exact pairing_close hw0 hw1 width (X.seq m) (X.seq n) (Y.seq m) (Y.seq n) B hB epsilon he
    (X.isCauchy delta hd m n hXm hXn) (Y.isCauchy delta hd m n hYm hYn)
    (leRat_mono (diagonal_le_normCeiling hw0 hw1 width Y m hYbase) (Q'.le_max'_right _ _))
    (leRat_mono (diagonal_le_normCeiling hw0 hw1 width X n hXbase) (Q'.le_max'_left _ _))

def pairRate (X Y : (D).Cauchy) : Q' → Nat :=
  closedRate canonicalReciprocalIndexData (rawRate hw0 hw1 width X Y)

theorem pairRate_antitone (X Y : (D).Cauchy) :
    MmonoPred (pairRate hw0 hw1 width X Y) :=
  closedRate_mmonoPred canonicalReciprocalIndexData (rawRate hw0 hw1 width X Y)

theorem pairSequence_bound (X Y : (D).Cauchy) :
    LeRatBound (pairSequence hw0 hw1 width X Y) (pairRate hw0 hw1 width X Y) :=
  LeRatBound.closed canonicalReciprocalIndexData (pairSequence_raw_bound hw0 hw1 width X Y)

/-- This explicit inner modulus comes from the actual joint chart rational
Cauchy construction, not from elimination of any legacy existential. -/
theorem pairSequence_regular (X Y : (D).Cauchy) :
    RegPred (pairSequence hw0 hw1 width X Y) (fun _ epsilon => epsilon.den) := by
  unfold pairSequence jointPairing BF4ExactSlabFixedSpatialChartJointCauchy.chartJointLimit
  exact ofQ'CauchySeq_family_regPred _ _

def representativeInner (X Y : (D).Cauchy) : CReal :=
  completeLimitFromRate (pairSequence hw0 hw1 width X Y)
    (pairRate hw0 hw1 width X Y) (fun _ epsilon => epsilon.den)
    (pairSequence_regular hw0 hw1 width X Y) (pairSequence_bound hw0 hw1 width X Y)

theorem pairSequence_converges (X Y : (D).Cauchy) :
    ConvergesTo (pairSequence hw0 hw1 width X Y)
      (representativeInner hw0 hw1 width X Y) :=
  convergesTo_completeLimitFromRate _ _ _ (pairSequence_regular hw0 hw1 width X Y)
    (pairSequence_bound hw0 hw1 width X Y) (pairRate_antitone hw0 hw1 width X Y)

/-- Approximation-modulus data for the newly computed scalar representative. -/
def representativeInnerCauchy (X Y : (D).Cauchy) :
    QCauchy (representativeInner hw0 hw1 width X Y).approx where
  M := fun epsilon => (HalfPow.half * (HalfPow.half * epsilon)).den
  bound := by
    intro epsilon he i j hi hj
    rcases Nat.le_total i j with hij | hji
    · exact diagSeqR_directed _ _ _ (pairSequence_regular hw0 hw1 width X Y)
        (pairSequence_bound hw0 hw1 width X Y) epsilon he i j hij hi
    · exact (diagSeqR_directed _ _ _ (pairSequence_regular hw0 hw1 width X Y)
        (pairSequence_bound hw0 hw1 width X Y) epsilon he j i hji hj).symm

end YMGap.Continuum.BF4ExactSlabFixedSpatialJointPairingLimit

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointPairingLimit.pairCeiling
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointPairingLimit.pairCeiling_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointPairingLimit.pairSequence
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointPairingLimit.pairDelta
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointPairingLimit.rawRate
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointPairingLimit.pairSequence_raw_bound
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointPairingLimit.pairRate
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointPairingLimit.pairRate_antitone
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointPairingLimit.pairSequence_bound
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointPairingLimit.pairSequence_regular
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointPairingLimit.representativeInner
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointPairingLimit.pairSequence_converges
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointPairingLimit.representativeInnerCauchy
