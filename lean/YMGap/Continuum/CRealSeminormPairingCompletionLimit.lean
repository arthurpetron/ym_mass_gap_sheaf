/-
# Explicit mixed-pairing limits on squared-seminorm Cauchy representatives

The supplied dense scalar moduli determine every inner approximation
index. Computed anchor ceilings and the quantitative dense continuity law
determine the outer Cauchy rate. Its constructive monotone closure gives a
scalar limit with its own explicit QCauchy witness. No canonical inner
indexing, stream norm bound or completed pairing is assumed.
-/

import YMGap.Continuum.CRealSeminormPairingCompletionBounds
import YMGap.Constructive.CRealCanonicalReciprocalIndex

namespace YMGap.Continuum.CRealSeminormPairingCompletion

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.CRealSeminormCompletion (SquaredSeminorm)
open YMGap.Continuum.BF4ExactSlabPlaquettePairingContinuity
  (pairingTolerance pairingTolerance_pos)

variable {D : SquaredSeminorm} (P : PairingData D)

def pairCeiling (X Y : D.Cauchy) : Q' :=
  Q'.max' (normCeiling P X) (normCeiling P Y)

theorem pairCeiling_nonnegative (X Y : D.Cauchy) :
    (0 : Q') ≤ pairCeiling P X Y :=
  Q'.le_trans' _ _ _ (normCeiling_nonnegative P X) (Q'.le_max'_left _ _)

def pairSequence (X Y : D.Cauchy) (n : Nat) : CReal :=
  P.pairing (X.seq n) (Y.seq n)

def pairDelta (X Y : D.Cauchy) (epsilon : Q') : Q' :=
  pairingTolerance (pairCeiling P X Y)
    (pairCeiling_nonnegative P X Y) epsilon

/-- The two original Cauchy moduli and their anchor indices remain data. -/
def rawRate (X Y : D.Cauchy) (epsilon : Q') : Nat :=
  max (max (normBase P X) (normBase P Y))
    (max (X.modulus (pairDelta P X Y epsilon))
      (Y.modulus (pairDelta P X Y epsilon)))

theorem pairSequence_raw_bound (X Y : D.Cauchy) :
    LeRatBound (pairSequence P X Y) (rawRate P X Y) := by
  intro epsilon he m n hm hn
  let B := pairCeiling P X Y
  let hB := pairCeiling_nonnegative P X Y
  let delta := pairDelta P X Y epsilon
  have hdeltaPos : (0 : Q') < delta := pairingTolerance_pos B hB he
  have hXbase : normBase P X ≤ n :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)) hn
  have hYbase : normBase P Y ≤ m :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)) hm
  have hXm : X.modulus delta ≤ m :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) hm
  have hXn : X.modulus delta ≤ n :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) hn
  have hYm : Y.modulus delta ≤ m :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) hm
  have hYn : Y.modulus delta ≤ n :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) hn
  exact P.pairing_close (X.seq m) (X.seq n) (Y.seq m) (Y.seq n) B hB epsilon he
    (X.isCauchy delta hdeltaPos m n hXm hXn) (Y.isCauchy delta hdeltaPos m n hYm hYn)
    (leRat_mono (diagonal_le_normCeiling P Y m hYbase) (Q'.le_max'_right _ _))
    (leRat_mono (diagonal_le_normCeiling P X n hXbase) (Q'.le_max'_left _ _))

def pairRate (X Y : D.Cauchy) : Q' → Nat :=
  closedRate canonicalReciprocalIndexData (rawRate P X Y)

theorem pairRate_antitone (X Y : D.Cauchy) :
    MmonoPred (pairRate P X Y) :=
  closedRate_mmonoPred canonicalReciprocalIndexData (rawRate P X Y)

theorem pairSequence_bound (X Y : D.Cauchy) :
    LeRatBound (pairSequence P X Y) (pairRate P X Y) :=
  LeRatBound.closed canonicalReciprocalIndexData (pairSequence_raw_bound P X Y)

/-- Use each supplied dense scalar's actual modulus, not canonical indices. -/
def pairRegularity (X Y : D.Cauchy) (i : Nat) (epsilon : Q') : Nat :=
  (P.pairingCauchy (X.seq i) (Y.seq i)).M epsilon

theorem pairSequence_regular (X Y : D.Cauchy) :
    RegPred (pairSequence P X Y) (pairRegularity P X Y) := by
  intro i epsilon he p q hp hq
  exact (P.pairingCauchy (X.seq i) (Y.seq i)).bound epsilon he p q hp hq

def representativeInner (X Y : D.Cauchy) : CReal :=
  completeLimitFromRate (pairSequence P X Y)
    (pairRate P X Y) (pairRegularity P X Y)
    (pairSequence_regular P X Y) (pairSequence_bound P X Y)

theorem pairSequence_converges (X Y : D.Cauchy) :
    ConvergesTo (pairSequence P X Y)
      (representativeInner P X Y) :=
  convergesTo_completeLimitFromRate _ _ _ (pairSequence_regular P X Y)
    (pairSequence_bound P X Y) (pairRate_antitone P X Y)

/-- Approximation-modulus data for the newly computed scalar representative. -/
def representativeInnerCauchy (X Y : D.Cauchy) :
    QCauchy (representativeInner P X Y).approx where
  M := fun epsilon => (HalfPow.half * (HalfPow.half * epsilon)).den
  bound := by
    intro epsilon he i j hi hj
    rcases Nat.le_total i j with hij | hji
    · exact diagSeqR_directed _ _ _ (pairSequence_regular P X Y)
        (pairSequence_bound P X Y) epsilon he i j hij hi
    · exact (diagSeqR_directed _ _ _ (pairSequence_regular P X Y)
        (pairSequence_bound P X Y) epsilon he j i hji hj).symm

end YMGap.Continuum.CRealSeminormPairingCompletion

#print axioms YMGap.Continuum.CRealSeminormPairingCompletion.pairCeiling
#print axioms YMGap.Continuum.CRealSeminormPairingCompletion.pairCeiling_nonnegative
#print axioms YMGap.Continuum.CRealSeminormPairingCompletion.pairSequence
#print axioms YMGap.Continuum.CRealSeminormPairingCompletion.pairDelta
#print axioms YMGap.Continuum.CRealSeminormPairingCompletion.rawRate
#print axioms YMGap.Continuum.CRealSeminormPairingCompletion.pairSequence_raw_bound
#print axioms YMGap.Continuum.CRealSeminormPairingCompletion.pairRate
#print axioms YMGap.Continuum.CRealSeminormPairingCompletion.pairRate_antitone
#print axioms YMGap.Continuum.CRealSeminormPairingCompletion.pairSequence_bound
#print axioms YMGap.Continuum.CRealSeminormPairingCompletion.pairRegularity
#print axioms YMGap.Continuum.CRealSeminormPairingCompletion.pairSequence_regular
#print axioms YMGap.Continuum.CRealSeminormPairingCompletion.representativeInner
#print axioms YMGap.Continuum.CRealSeminormPairingCompletion.pairSequence_converges
#print axioms YMGap.Continuum.CRealSeminormPairingCompletion.representativeInnerCauchy
