/-
# Quotient descent of the completed strict reflection pairing

For two explicit staged-seminorm Cauchy representatives, the preceding leaf
constructs a genuine constructive-real limit of their strict pairings.  This
module proves that the limit is independent of both representatives and
therefore descends, in both arguments at once, to an RC-valued pairing on the
actual seminorm completion.

The proof remains intuitionistic.  CompletionRel witnesses are eliminated
only into CReal.Equiv, and the approximation threshold obtained from leRat is
kept inside the Prop-valued limit-closeness statement.  No representative,
modulus, or approximation cutoff is selected while constructing the quotient
pairing.
-/

import YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCanonicalPairingCompletion
import YMGap.Constructive.CRealLimitClose

namespace YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedPairingDescent

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

open YMGap.Constructive
open YMGap.Continuum.CRealSeminormCompletion
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCanonicalPairingCompletion
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealDirectLimitSeminorm
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealPairingAnchorBound
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealPairingRawOuterRate
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealStagePairingContinuity
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDirectLimitBilinear
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

variable {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
  (hle : coupling <= anchorCoupling)

private abbrev StageSeminorm : SquaredSeminorm :=
  strictJointCylinderStageSquaredSeminorm hcoupling hle

/-- Actual `Close` data in both arguments make the two canonical completed
pairing sequences asymptotically close in the exact two-cutoff form used by
`CReal.Equiv_of_limit_of_close`. -/
theorem strictJointCylinderCanonicalPairingSequence_close_of_close
    (X X' Y Y' : (StageSeminorm hcoupling hle).Cauchy)
    (hX : (StageSeminorm hcoupling hle).Close X X')
    (hY : (StageSeminorm hcoupling hle).Close Y Y') :
    forall epsilon : Q', (0 : Q') < epsilon ->
      exists Nstage : Nat, forall N : Nat, Nstage <= N ->
        exists Napx : Nat, forall n : Nat, Napx <= n ->
          (strictJointCylinderCanonicalPairingSequence
              hcoupling hle X Y N).approx n <=
            (strictJointCylinderCanonicalPairingSequence
              hcoupling hle X' Y' N).approx n + epsilon /\
          (strictJointCylinderCanonicalPairingSequence
              hcoupling hle X' Y' N).approx n <=
            (strictJointCylinderCanonicalPairingSequence
              hcoupling hle X Y N).approx n + epsilon := by
  intro epsilon hepsilon
  let rho : Q' := HalfPow.half * epsilon
  let C : Nat :=
    max (strictJointCylinderCauchyNormCeil hcoupling hle Y)
      (strictJointCylinderCauchyNormCeil hcoupling hle X')
  let delta : Q' := strictJointCylinderPairingContinuityScale C rho
  let Nstage : Nat :=
    max
      (max (strictJointCylinderCauchyNormBase hcoupling hle Y)
        (strictJointCylinderCauchyNormBase hcoupling hle X'))
      (max (hX.modulus delta) (hY.modulus delta))
  have hrho : (0 : Q') < rho := by
    dsimp [rho]
    exact ExpNeg.half_mul_pos epsilon hepsilon
  have hdelta : (0 : Q') < delta := by
    dsimp [delta]
    exact strictJointCylinderPairingContinuityScale_pos C hrho
  refine ⟨Nstage, fun N hN => ?_⟩
  have hN' :
      max
        (max (strictJointCylinderCauchyNormBase hcoupling hle Y)
          (strictJointCylinderCauchyNormBase hcoupling hle X'))
        (max (hX.modulus delta) (hY.modulus delta)) <= N := by
    simpa [Nstage] using hN
  have hYBase :
      strictJointCylinderCauchyNormBase hcoupling hle Y <= N :=
    Nat.le_trans
      (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)) hN'
  have hX'Base :
      strictJointCylinderCauchyNormBase hcoupling hle X' <= N :=
    Nat.le_trans
      (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)) hN'
  have hXMod : hX.modulus delta <= N :=
    Nat.le_trans
      (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) hN'
  have hYMod : hY.modulus delta <= N :=
    Nat.le_trans
      (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) hN'
  have hleftDist : CReal.leRat
      (strictJointCylinderStageReflectionDistSq
        hcoupling hle (X.seq N) (X'.seq N)) delta := by
    exact hX.close delta hdelta N hXMod
  have hrightDist : CReal.leRat
      (strictJointCylinderStageReflectionDistSq
        hcoupling hle (Y.seq N) (Y'.seq N)) delta := by
    exact hY.close delta hdelta N hYMod
  have hrightBound : CReal.leRat
      (strictJointCylinderStageReflectionBilinear
        hcoupling hle (Y.seq N) (Y.seq N))
      (Q'.ofNat C) := by
    refine CReal.leRat_mono
      (strictJointCylinderCauchy_self_leRat_normCeil
        hcoupling hle Y N hYBase) ?_
    dsimp [C]
    exact Q'.ofNat_le_ofNat (Nat.le_max_left _ _)
  have hleft'Bound : CReal.leRat
      (strictJointCylinderStageReflectionBilinear
        hcoupling hle (X'.seq N) (X'.seq N))
      (Q'.ofNat C) := by
    refine CReal.leRat_mono
      (strictJointCylinderCauchy_self_leRat_normCeil
        hcoupling hle X' N hX'Base) ?_
    dsimp [C]
    exact Q'.ofNat_le_ofNat (Nat.le_max_right _ _)
  have hbudget :
      (delta + delta) * (Q'.ofNat C + delta) <=
        (HalfPow.half * rho) * (HalfPow.half * rho) := by
    dsimp [delta]
    exact strictJointCylinderPairingContinuityScale_budget C hrho
  obtain ⟨hrawForward, hrawBackward⟩ :=
    strictJointCylinderStageReflectionBilinear_difference_leRat
      hcoupling hle
      (X.seq N) (X'.seq N) (Y.seq N) (Y'.seq N)
      rho delta (Q'.ofNat C) delta
      hrho hdelta hdelta hleftDist hrightDist
      hrightBound hleft'Bound hbudget
  have hcanonicalForward : CReal.leRat
      (CReal.add
        (strictJointCylinderCanonicalPairingSequence
          hcoupling hle X Y N)
        (CReal.neg
          (strictJointCylinderCanonicalPairingSequence
            hcoupling hle X' Y' N))) rho := by
    exact CReal.leRat_of_equiv
      (CReal.Equiv_add
        (strictJointCylinderCanonicalPairingSequence_equiv_raw
          hcoupling hle X Y N)
        (CReal.neg_congr
          (strictJointCylinderCanonicalPairingSequence_equiv_raw
            hcoupling hle X' Y' N)))
      hrawForward
  have hcanonicalBackward : CReal.leRat
      (CReal.add
        (strictJointCylinderCanonicalPairingSequence
          hcoupling hle X' Y' N)
        (CReal.neg
          (strictJointCylinderCanonicalPairingSequence
            hcoupling hle X Y N))) rho := by
    exact CReal.leRat_of_equiv
      (CReal.Equiv_add
        (strictJointCylinderCanonicalPairingSequence_equiv_raw
          hcoupling hle X' Y' N)
        (CReal.neg_congr
          (strictJointCylinderCanonicalPairingSequence_equiv_raw
            hcoupling hle X Y N)))
      hrawBackward
  obtain ⟨Napx, hNapx⟩ :=
    CReal.evTwoSided_of_leRat
      hcanonicalForward hcanonicalBackward hrho
  refine ⟨Napx, fun n hn => ?_⟩
  obtain ⟨hforward, hbackward⟩ := hNapx n hn
  have htwo : rho + rho <= epsilon := by
    dsimp [rho]
    exact Q'.le_of_eqv (ExpNeg.two_halves epsilon)
  exact
    ⟨Q'.le_trans' _ _ _ hforward
        (Q'.add_le_add_left
          ((strictJointCylinderCanonicalPairingSequence
            hcoupling hle X' Y' N).approx n)
          (rho + rho) epsilon htwo),
      Q'.le_trans' _ _ _ hbackward
        (Q'.add_le_add_left
          ((strictJointCylinderCanonicalPairingSequence
            hcoupling hle X Y N).approx n)
          (rho + rho) epsilon htwo)⟩

/-- Actual `Close` data in both arguments do not change the completed
representative pairing. -/
theorem strictJointCylinderRepresentativePairingLimit_equiv_of_close
    (X X' Y Y' : (StageSeminorm hcoupling hle).Cauchy)
    (hX : (StageSeminorm hcoupling hle).Close X X')
    (hY : (StageSeminorm hcoupling hle).Close Y Y') :
    CReal.Equiv
      (strictJointCylinderRepresentativePairingLimit
        hcoupling hle X Y)
      (strictJointCylinderRepresentativePairingLimit
        hcoupling hle X' Y') :=
  CReal.Equiv_of_limit_of_close
    (strictJointCylinderRepresentativePairingLimit_converges
      hcoupling hle X Y)
    (strictJointCylinderRepresentativePairingLimit_converges
      hcoupling hle X' Y')
    (strictJointCylinderCanonicalPairingSequence_close_of_close
      hcoupling hle X X' Y Y' hX hY)

/-- The completed representative pairing is independent of both Cauchy
representatives modulo the relation used by the completion quotient. -/
theorem strictJointCylinderRepresentativePairingLimit_welldef
    (X X' Y Y' : (StageSeminorm hcoupling hle).Cauchy)
    (hX : (StageSeminorm hcoupling hle).CompletionRel X X')
    (hY : (StageSeminorm hcoupling hle).CompletionRel Y Y') :
    CReal.Equiv
      (strictJointCylinderRepresentativePairingLimit
        hcoupling hle X Y)
      (strictJointCylinderRepresentativePairingLimit
        hcoupling hle X' Y') := by
  rcases hX with ⟨hXdata⟩
  rcases hY with ⟨hYdata⟩
  exact strictJointCylinderRepresentativePairingLimit_equiv_of_close
    hcoupling hle X X' Y Y' hXdata hYdata

/-- The representative-level completed pairing packaged in the genuine real
quotient. -/
def strictJointCylinderRepresentativePairingR
    (X Y : (StageSeminorm hcoupling hle).Cauchy) : CReal.RC :=
  Quotient.mk CReal.crealSetoid
    (strictJointCylinderRepresentativePairingLimit hcoupling hle X Y)

/-- The strict reflection pairing descended to both completed arguments. -/
def strictJointCylinderCompletedPairing :
    (StageSeminorm hcoupling hle).Completion ->
      (StageSeminorm hcoupling hle).Completion -> CReal.RC :=
  Quotient.lift₂
    (fun X Y => strictJointCylinderRepresentativePairingR
      hcoupling hle X Y)
    (fun X Y X' Y' hX hY => Quotient.sound
      (strictJointCylinderRepresentativePairingLimit_welldef
        hcoupling hle X X' Y Y' hX hY))

@[simp] theorem strictJointCylinderCompletedPairing_mk
    (X Y : (StageSeminorm hcoupling hle).Cauchy) :
    strictJointCylinderCompletedPairing hcoupling hle
        (Quotient.mk (StageSeminorm hcoupling hle).completionSetoid X)
        (Quotient.mk (StageSeminorm hcoupling hle).completionSetoid Y) =
      Quotient.mk CReal.crealSetoid
        (strictJointCylinderRepresentativePairingLimit
          hcoupling hle X Y) := rfl

#print axioms strictJointCylinderCanonicalPairingSequence_close_of_close
#print axioms strictJointCylinderRepresentativePairingLimit_equiv_of_close
#print axioms strictJointCylinderRepresentativePairingLimit_welldef
#print axioms strictJointCylinderRepresentativePairingR
#print axioms strictJointCylinderCompletedPairing
#print axioms strictJointCylinderCompletedPairing_mk

end YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedPairingDescent
