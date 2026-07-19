/-
# Canonical pre-quotient completion of the strict staged reflection pairing

Task-work draft only.  This leaf deliberately stops before quotient descent.
For two explicit staged-seminorm Cauchy representatives `X` and `Y`, it:

1. co-presents every staged pair in its canonical maximum box;
2. completes the resulting direct rational strict-pairing sequence with
   `CReal.ofQ'CauchySeq`;
3. identifies that canonical term with the already proved polarized staged
   pairing by `CReal.Equiv`;
4. transfers the raw outer `LeRatBound` pointwise to the canonical terms;
5. closes the arbitrary raw rate with the executable canonical reciprocal
   index; and
6. applies `CReal.completeLimitFromRate` with the explicit inner regularity
   modulus `epsilon.den`.

The result is a genuine `CReal` and a genuine `CReal.ConvergesTo` theorem on
representatives.  No quotient lift is attempted here: representative
independence is the next mathematical obligation.
-/

import YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealPairingRawOuterRate
import YMGap.Constructive.CRealCanonicalReciprocalIndex

namespace YMGap.Constructive

namespace CReal

/-! ## 1. Two generic completion adapters -/

/-- A Nat-indexed family of rational Cauchy sequences, lifted memberwise by
`ofQ'CauchySeq`, has the uniform explicit inner regularity modulus
`epsilon.den` required by `completeLimitFromRate`.

This proof uses the directed core of `ofQ'CauchySeq` itself.  In particular it
does not eliminate the existential threshold in a generic `CReal.cauchy`
proof, so the regularity modulus remains Type-level data. -/
theorem ofQ'CauchySeq_family_regPred
    (r : Nat -> Nat -> Q') (c : forall i : Nat, QCauchy (r i)) :
    RegPred
      (fun i => ofQ'CauchySeq (r i) (c i))
      (fun _ epsilon => epsilon.den) := by
  intro i epsilon hepsilon p q hp hq
  change
    r i (QMhat (r i) (c i) p) <=
        r i (QMhat (r i) (c i) q) + epsilon /\
      r i (QMhat (r i) (c i) q) <=
        r i (QMhat (r i) (c i) p) + epsilon
  rcases Nat.le_total p q with hpq | hqp
  · exact QMhat_directed (r i) (c i) epsilon hepsilon p q hpq hp
  · exact (QMhat_directed (r i) (c i) epsilon hepsilon q p hqp hq).symm

/-- `LeRatBound` is invariant under pointwise constructive-real equivalence.

The direction is chosen for completion work: a bound on `t` is transported to
a pointwise equivalent canonical sequence `s`. -/
theorem LeRatBound.of_pointwise_equiv
    {s t : Nat -> CReal} {M : Q' -> Nat}
    (hst : forall n : Nat, Equiv (s n) (t n))
    (ht : LeRatBound t M) :
    LeRatBound s M := by
  intro epsilon hepsilon m n hm hn
  obtain ⟨hmn, hnm⟩ := ht epsilon hepsilon m n hm hn
  exact
    ⟨leRat_of_equiv
        (Equiv_add (hst m) (neg_congr (hst n))) hmn,
      leRat_of_equiv
        (Equiv_add (hst n) (neg_congr (hst m))) hnm⟩

end CReal

end YMGap.Constructive

namespace YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCanonicalPairingCompletion

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

open YMGap.Constructive
open YMGap.Continuum.CRealSeminormCompletion
open YMGap.Continuum.OSReconstructionProgress
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealDirectLimitSeminorm
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealPairingContinuity
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealPairingRawOuterRate
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderBilinearTimeTranslation
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderDirectLimit
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderSeminorm
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDirectLimitBilinear
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSBilinear
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

/-! ## 2. Canonical maximum-box pairing of two staged vectors -/

/-- Canonical common box of a staged pair. -/
def strictJointCylinderStagePairingBase
    (left right : StrictJointCylinderStage) : Nat :=
  max left.base right.base

/-- Left input transported into the canonical common box. -/
def strictJointCylinderStagePairingLeft
    (left right : StrictJointCylinderStage) :
    StrictJointCylinderVector
      (strictJointCylinderStagePairingBase left right) :=
  boxTransportStrictJointCylinderVector
    (Nat.le_max_left left.base right.base) left.vector

/-- Right input transported into the canonical common box. -/
def strictJointCylinderStagePairingRight
    (left right : StrictJointCylinderStage) :
    StrictJointCylinderVector
      (strictJointCylinderStagePairingBase left right) :=
  boxTransportStrictJointCylinderVector
    (Nat.le_max_right left.base right.base) right.vector

/-- The direct rational strict-pairing sequence in the canonical maximum box. -/
def strictJointCylinderStageReflectionBilinearRationalSequence
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (left right : StrictJointCylinderStage) : Nat -> Q' :=
  strictJointCylinderReflectionBilinearSequence coupling hcoupling
    (strictJointCylinderStagePairingLeft left right)
    (strictJointCylinderStagePairingRight left right)

/-- Explicit rational Cauchy datum for the canonical maximum-box sequence. -/
def strictJointCylinderStageReflectionBilinearRationalQCauchy
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (left right : StrictJointCylinderStage) :
    CReal.QCauchy
      (strictJointCylinderStageReflectionBilinearRationalSequence
        hcoupling left right) :=
  strictJointCylinderReflectionBilinearQCauchy hcoupling hle
    (strictJointCylinderStagePairingLeft left right)
    (strictJointCylinderStagePairingRight left right)

/-- Canonical pre-quotient pairing of two staged vectors: first co-present in
`max left.base right.base`, then complete the direct rational sequence. -/
def strictJointCylinderStageReflectionBilinearSequenceLimit
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (left right : StrictJointCylinderStage) : CReal :=
  CReal.ofQ'CauchySeq
    (strictJointCylinderStageReflectionBilinearRationalSequence
      hcoupling left right)
    (strictJointCylinderStageReflectionBilinearRationalQCauchy
      hcoupling hle left right)

/-- The canonical maximum-box rational-sequence completion represents the
same constructive real as the existing polarized staged pairing. -/
theorem strictJointCylinderStageReflectionBilinearSequenceLimit_equiv
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (left right : StrictJointCylinderStage) :
    CReal.Equiv
      (strictJointCylinderStageReflectionBilinearSequenceLimit
        hcoupling hle left right)
      (strictJointCylinderStageReflectionBilinear
        hcoupling hle left right) := by
  exact CReal.Equiv.trans
    (strictJointCylinderReflectionBilinearSequenceLimit_equiv
      hcoupling hle
      (strictJointCylinderStagePairingLeft left right)
      (strictJointCylinderStagePairingRight left right))
    (strictJointCylinderStageReflectionBilinear_at_common
      hcoupling hle left right
      (Nat.le_max_left left.base right.base)
      (Nat.le_max_right left.base right.base))

/-! ## 3. The canonical pairing sequence of two Cauchy representatives -/

variable {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
  (hle : coupling <= anchorCoupling)

private abbrev StageSeminorm : SquaredSeminorm :=
  strictJointCylinderStageSquaredSeminorm hcoupling hle

/-- The rational family underlying the canonical staged pairing terms. -/
def strictJointCylinderCanonicalPairingRationalFamily
    (X Y : (StageSeminorm hcoupling hle).Cauchy)
    (n : Nat) : Nat -> Q' :=
  strictJointCylinderStageReflectionBilinearRationalSequence
    hcoupling (X.seq n) (Y.seq n)

/-- Memberwise rational Cauchy data for the canonical pairing family. -/
def strictJointCylinderCanonicalPairingQCauchyFamily
    (X Y : (StageSeminorm hcoupling hle).Cauchy)
    (n : Nat) :
    CReal.QCauchy
      (strictJointCylinderCanonicalPairingRationalFamily
        hcoupling hle X Y n) :=
  strictJointCylinderStageReflectionBilinearRationalQCauchy
    hcoupling hle (X.seq n) (Y.seq n)

/-- Canonical representative pairing sequence.  Unlike the raw polarized
sequence, every term records the direct rational approximation provenance
needed for a uniform Type-level inner regularity modulus. -/
def strictJointCylinderCanonicalPairingSequence
    (X Y : (StageSeminorm hcoupling hle).Cauchy)
    (n : Nat) : CReal :=
  CReal.ofQ'CauchySeq
    (strictJointCylinderCanonicalPairingRationalFamily
      hcoupling hle X Y n)
    (strictJointCylinderCanonicalPairingQCauchyFamily
      hcoupling hle X Y n)

/-- Pointwise bridge from canonical rational-sequence terms to the raw
polarized staged-pairing terms. -/
theorem strictJointCylinderCanonicalPairingSequence_equiv_raw
    (X Y : (StageSeminorm hcoupling hle).Cauchy)
    (n : Nat) :
    CReal.Equiv
      (strictJointCylinderCanonicalPairingSequence
        hcoupling hle X Y n)
      (strictJointCylinderPairingSequence hcoupling hle X Y n) := by
  exact strictJointCylinderStageReflectionBilinearSequenceLimit_equiv
    hcoupling hle (X.seq n) (Y.seq n)

/-! ## 4. Raw and canonically closed outer rates -/

/-- The raw outer pairing estimate transfers pointwise to the canonical
rational-sequence terms. -/
theorem strictJointCylinderCanonicalPairingSequence_raw_leRatBound
    (X Y : (StageSeminorm hcoupling hle).Cauchy) :
    CReal.LeRatBound
      (strictJointCylinderCanonicalPairingSequence hcoupling hle X Y)
      (strictJointCylinderPairingRawRate hcoupling hle X Y) :=
  CReal.LeRatBound.of_pointwise_equiv
    (strictJointCylinderCanonicalPairingSequence_equiv_raw
      hcoupling hle X Y)
    (strictJointCylinderPairingSequence_raw_leRatBound
      hcoupling hle X Y)

/-- Executable antitone/cofinal closure of the arbitrary raw pairing rate. -/
def strictJointCylinderCanonicalPairingRate
    (X Y : (StageSeminorm hcoupling hle).Cauchy) (epsilon : Q') : Nat :=
  CReal.closedRate CReal.canonicalReciprocalIndexData
    (strictJointCylinderPairingRawRate hcoupling hle X Y) epsilon

/-- The closed rate is antitone in the tolerance, as required by the
`ConvergesTo` half of `completeLimitFromRate`. -/
theorem strictJointCylinderCanonicalPairingRate_mmonoPred
    (X Y : (StageSeminorm hcoupling hle).Cauchy) :
    CReal.MmonoPred
      (strictJointCylinderCanonicalPairingRate hcoupling hle X Y) :=
  CReal.closedRate_mmonoPred CReal.canonicalReciprocalIndexData
    (strictJointCylinderPairingRawRate hcoupling hle X Y)

/-- The canonical pairing sequence satisfies its two-sided outer bound at the
closed antitone rate. -/
theorem strictJointCylinderCanonicalPairingSequence_leRatBound
    (X Y : (StageSeminorm hcoupling hle).Cauchy) :
    CReal.LeRatBound
      (strictJointCylinderCanonicalPairingSequence hcoupling hle X Y)
      (strictJointCylinderCanonicalPairingRate hcoupling hle X Y) :=
  CReal.LeRatBound.closed CReal.canonicalReciprocalIndexData
    (strictJointCylinderCanonicalPairingSequence_raw_leRatBound
      hcoupling hle X Y)

/-! ## 5. Inner regularity and the completed representative pairing -/

/-- Uniform Type-level inner regularity modulus of every canonical term. -/
def strictJointCylinderCanonicalPairingReg
    (_ : Nat) (epsilon : Q') : Nat :=
  epsilon.den

theorem strictJointCylinderCanonicalPairing_regPred
    (X Y : (StageSeminorm hcoupling hle).Cauchy) :
    CReal.RegPred
      (strictJointCylinderCanonicalPairingSequence hcoupling hle X Y)
      strictJointCylinderCanonicalPairingReg := by
  exact CReal.ofQ'CauchySeq_family_regPred
    (strictJointCylinderCanonicalPairingRationalFamily
      hcoupling hle X Y)
    (strictJointCylinderCanonicalPairingQCauchyFamily
      hcoupling hle X Y)

/-- Genuine pre-quotient completed pairing value of two explicit Cauchy
representatives. -/
def strictJointCylinderRepresentativePairingLimit
    (X Y : (StageSeminorm hcoupling hle).Cauchy) : CReal :=
  CReal.completeLimitFromRate
    (strictJointCylinderCanonicalPairingSequence hcoupling hle X Y)
    (strictJointCylinderCanonicalPairingRate hcoupling hle X Y)
    strictJointCylinderCanonicalPairingReg
    (strictJointCylinderCanonicalPairing_regPred hcoupling hle X Y)
    (strictJointCylinderCanonicalPairingSequence_leRatBound
      hcoupling hle X Y)

/-- The canonical staged pairings converge to the pre-quotient completed
pairing value. -/
theorem strictJointCylinderRepresentativePairingLimit_converges
    (X Y : (StageSeminorm hcoupling hle).Cauchy) :
    CReal.ConvergesTo
      (strictJointCylinderCanonicalPairingSequence hcoupling hle X Y)
      (strictJointCylinderRepresentativePairingLimit
        hcoupling hle X Y) :=
  CReal.convergesTo_completeLimitFromRate
    (strictJointCylinderCanonicalPairingSequence hcoupling hle X Y)
    (strictJointCylinderCanonicalPairingRate hcoupling hle X Y)
    strictJointCylinderCanonicalPairingReg
    (strictJointCylinderCanonicalPairing_regPred hcoupling hle X Y)
    (strictJointCylinderCanonicalPairingSequence_leRatBound
      hcoupling hle X Y)
    (strictJointCylinderCanonicalPairingRate_mmonoPred
      hcoupling hle X Y)

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Constructive.CReal.ofQ'CauchySeq_family_regPred
#print axioms YMGap.Constructive.CReal.LeRatBound.of_pointwise_equiv
#print axioms strictJointCylinderStageReflectionBilinearSequenceLimit_equiv
#print axioms strictJointCylinderCanonicalPairingSequence_raw_leRatBound
#print axioms strictJointCylinderCanonicalPairingRate_mmonoPred
#print axioms strictJointCylinderCanonicalPairingSequence_leRatBound
#print axioms strictJointCylinderCanonicalPairing_regPred
#print axioms strictJointCylinderRepresentativePairingLimit
#print axioms strictJointCylinderRepresentativePairingLimit_converges

end YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCanonicalPairingCompletion
