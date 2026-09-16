/-
# Constructive limit of the SAME intrinsic reflected pairing

Every Cauchy representative supplies its own anchor and computed norm
ceiling. Actual pairing continuity gives an outer Cauchy rate; the original
time-limit representation supplies the inner regularity epsilon.den.
Closing the outer rate and taking an explicit diagonal constructs the
mixed pairing limit, without a supplied boundedness/convergence premise.

This is a limit on representatives. Independence of close representatives
and descent to the existing physical Cauchy carrier are subsequent steps.
Nome, spatial width and retained cutoff remain fixed.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialPairingBounds
import YMGap.Continuum.BF4ExactSlabFixedSpatialPairingContinuity
import YMGap.Constructive.CRealCanonicalReciprocalIndex

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialPairingLimit

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicReflectedForm
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicSeminorm
open YMGap.Continuum.BF4ExactSlabFixedSpatialPairingBounds
open YMGap.Continuum.BF4ExactSlabFixedSpatialPairingContinuity
open YMGap.Continuum.BF4ExactSlabPlaquettePairingContinuity (pairingTolerance pairingTolerance_pos)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (width stage : Nat)

local notation "D" => seminorm hw0 hw1 width stage

def pairCeiling (X Y : (D).Cauchy) : Q' :=
  Q'.max' (normCeiling hw0 hw1 width stage X) (normCeiling hw0 hw1 width stage Y)

theorem pairCeiling_nonnegative (X Y : (D).Cauchy) :
    (0 : Q') ≤ pairCeiling hw0 hw1 width stage X Y :=
  Q'.le_trans' _ _ _ (normCeiling_nonnegative hw0 hw1 width stage X) (Q'.le_max'_left _ _)

def pairSequence (X Y : (D).Cauchy) (n : Nat) : CReal :=
  pairing hw0 hw1 width (X.seq n).val (Y.seq n).val stage

def pairDelta (X Y : (D).Cauchy) (epsilon : Q') : Q' :=
  pairingTolerance (pairCeiling hw0 hw1 width stage X Y)
    (pairCeiling_nonnegative hw0 hw1 width stage X Y) epsilon

/-- The two anchor indices and the two supplied Cauchy moduli are retained. -/
def rawRate (X Y : (D).Cauchy) (epsilon : Q') : Nat :=
  max (max (normBase hw0 hw1 width stage X) (normBase hw0 hw1 width stage Y))
    (max (X.modulus (pairDelta hw0 hw1 width stage X Y epsilon))
      (Y.modulus (pairDelta hw0 hw1 width stage X Y epsilon)))

theorem pairSequence_raw_bound (X Y : (D).Cauchy) :
    LeRatBound (pairSequence hw0 hw1 width stage X Y) (rawRate hw0 hw1 width stage X Y) := by
  intro epsilon he m n hm hn
  let B := pairCeiling hw0 hw1 width stage X Y
  let hB := pairCeiling_nonnegative hw0 hw1 width stage X Y
  let delta := pairDelta hw0 hw1 width stage X Y epsilon
  have hd : (0 : Q') < delta := pairingTolerance_pos B hB he
  have hXbase : normBase hw0 hw1 width stage X ≤ n :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)) hn
  have hYbase : normBase hw0 hw1 width stage Y ≤ m :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)) hm
  have hXm : X.modulus delta ≤ m :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) hm
  have hXn : X.modulus delta ≤ n :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) hn
  have hYm : Y.modulus delta ≤ m :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) hm
  have hYn : Y.modulus delta ≤ n :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) hn
  exact pairing_close hw0 hw1 width stage (X.seq m) (X.seq n) (Y.seq m) (Y.seq n) B hB epsilon he
    (X.isCauchy delta hd m n hXm hXn) (Y.isCauchy delta hd m n hYm hYn)
    (leRat_mono (diagonal_le_normCeiling hw0 hw1 width stage Y m hYbase) (Q'.le_max'_right _ _))
    (leRat_mono (diagonal_le_normCeiling hw0 hw1 width stage X n hXbase) (Q'.le_max'_left _ _))

def pairRate (X Y : (D).Cauchy) : Q' → Nat :=
  closedRate canonicalReciprocalIndexData (rawRate hw0 hw1 width stage X Y)

theorem pairRate_antitone (X Y : (D).Cauchy) :
    MmonoPred (pairRate hw0 hw1 width stage X Y) :=
  closedRate_mmonoPred canonicalReciprocalIndexData (rawRate hw0 hw1 width stage X Y)

theorem pairSequence_bound (X Y : (D).Cauchy) :
    LeRatBound (pairSequence hw0 hw1 width stage X Y) (pairRate hw0 hw1 width stage X Y) :=
  LeRatBound.closed canonicalReciprocalIndexData (pairSequence_raw_bound hw0 hw1 width stage X Y)

/-- Inner regularity comes from the actual original time-limit construction,
not elimination of an arbitrary existential CReal.cauchy threshold. -/
theorem pairSequence_regular (X Y : (D).Cauchy) :
    RegPred (pairSequence hw0 hw1 width stage X Y) (fun _ epsilon => epsilon.den) := by
  have regular : ∀ (r : Nat → Nat → Q') (c : ∀ i, QCauchy (r i)),
      RegPred (fun i => ofQ'CauchySeq (r i) (c i)) (fun _ epsilon => epsilon.den) := by
    intro r c i epsilon he p q hp hq
    change r i (QMhat (r i) (c i) p) ≤ r i (QMhat (r i) (c i) q) + epsilon ∧
      r i (QMhat (r i) (c i) q) ≤ r i (QMhat (r i) (c i) p) + epsilon
    rcases Nat.le_total p q with hpq | hqp
    · exact QMhat_directed (r i) (c i) epsilon he p q hpq hp
    · exact (QMhat_directed (r i) (c i) epsilon he q p hqp hq).symm
  unfold pairSequence pairing
    BF4ExactSlabFixedSpatialReflectedForm.form
    BF4ExactSlabFixedSpatialWindowTimeLimit.polynomialWindowLimit
    BF4ExactSlabFixedSpatialWindowTimeLimit.windowTimeLimit
  exact regular _ _

/-- The explicit outer rate and inner regularity construct this CReal. -/
def representativeInner (X Y : (D).Cauchy) : CReal :=
  completeLimitFromRate (pairSequence hw0 hw1 width stage X Y)
    (pairRate hw0 hw1 width stage X Y) (fun _ epsilon => epsilon.den)
    (pairSequence_regular hw0 hw1 width stage X Y) (pairSequence_bound hw0 hw1 width stage X Y)

theorem pairSequence_converges (X Y : (D).Cauchy) :
    ConvergesTo (pairSequence hw0 hw1 width stage X Y)
      (representativeInner hw0 hw1 width stage X Y) :=
  convergesTo_completeLimitFromRate _ _ _ (pairSequence_regular hw0 hw1 width stage X Y)
    (pairSequence_bound hw0 hw1 width stage X Y) (pairRate_antitone hw0 hw1 width stage X Y)

/-- The new scalar representative also carries a named approximation modulus. -/
def representativeInnerCauchy (X Y : (D).Cauchy) :
    QCauchy (representativeInner hw0 hw1 width stage X Y).approx where
  M := fun epsilon => (HalfPow.half * (HalfPow.half * epsilon)).den
  bound := by
    intro epsilon he i j hi hj
    rcases Nat.le_total i j with hij | hji
    · exact diagSeqR_directed _ _ _ (pairSequence_regular hw0 hw1 width stage X Y)
        (pairSequence_bound hw0 hw1 width stage X Y) epsilon he i j hij hi
    · exact (diagSeqR_directed _ _ _ (pairSequence_regular hw0 hw1 width stage X Y)
        (pairSequence_bound hw0 hw1 width stage X Y) epsilon he j i hji hj).symm

end YMGap.Continuum.BF4ExactSlabFixedSpatialPairingLimit

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPairingLimit.pairCeiling
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPairingLimit.pairCeiling_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPairingLimit.pairSequence
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPairingLimit.pairDelta
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPairingLimit.rawRate
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPairingLimit.pairSequence_raw_bound
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPairingLimit.pairRate
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPairingLimit.pairRate_antitone
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPairingLimit.pairSequence_bound
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPairingLimit.pairSequence_regular
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPairingLimit.representativeInner
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPairingLimit.pairSequence_converges
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPairingLimit.representativeInnerCauchy
