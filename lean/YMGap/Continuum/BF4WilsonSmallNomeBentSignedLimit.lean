/-
# Actual bent-loop signed gain on the SAME completed carrier

At nome 1/16 and width two, the proved original all-depth gain G>=S/4
is divided by its SAME positive even partition. The literal bent source
and its original odd OWN center coincide with the existing finite-gain
stream. The existing cutoff/time/representative thresholds construct its
diagonal convergence to the already defined gainLimit. Consequently the
existing completed centered vector satisfies C2-w^18*C1>=C2/4>=2^(-130).

The reference w^18 is not a centered eigenvalue. There is no source,
center, state or normalization substitution, and no changing-width/nome,
growing-square, continuum-survival or physical mass-gap assertion.
-/

import YMGap.Continuum.BF4WilsonSmallNomeBentCompletedGain
import YMGap.Continuum.BF4WilsonAllNomeFilteredFiniteGainLimit

namespace YMGap.Continuum.BF4WilsonSmallNomeBentSignedLimit

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser (qpow)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTransfer (bentObservable)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeSmallFundamentalCap
  (smallNome smallNome_pos)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTerminalOwnMean (originalOddMean)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTerminalGain
  (relativeSquareFloor originalSquare originalOwn_gain_relative_lower
    originalOwn_normalized_gain_floor)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredCommutatorGain (commutatorGain)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredNoiseDrift
  (evenPartition evenPartition_positive)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredOwnYoung (ownMean)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe (sourceCharacter)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow (WindowExpression)
open YMGap.Continuum.BF4ExactSlabFixedSpatialMiddlePairing (middleRatio)
open YMGap.Continuum.BF4ExactSlabFixedSpatialMovingCenterLagDifference (centeredPair)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonOwnCenterLimit
  (own_centeredPair_converges)
open YMGap.Continuum.BF4ExactSlabThermodynamicScalarRows (limit_le_of_eventual)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4WilsonSmallNomeBentCompletedGain
  (bentLoop bentLoop_source_pin originalOwn_square_chronological_pin)
open YMGap.Continuum.BF4WilsonAllNomeFilteredFiniteGainApproximation (normalizedFiniteGain)
open YMGap.Continuum.BF4WilsonAllNomeFilteredFiniteGainLimit
  (gainCutoffThreshold gainTimeThreshold gainRepresentativeThreshold
    normalizedFiniteGain_approx)
open YMGap.Continuum.BF4WilsonAllNomeFilteredGainLimit
  (gainLimit gainLimit_centered_pin gainLimit_completed_pin)
open YMGap.Continuum.BF4WilsonAllNomeZeroRadiusIncrement (state)
open YMGap.Continuum.BF4WilsonAllNomeLoopTimePin (loopState)
open YMGap.Continuum.BF4WilsonAllNomeCenteredMoments (centeredTimeMoment)
open YMGap.Continuum.BF4WilsonAllNomeCenteredVector
  (centeredVector centeredVector_time_pairing)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner (completedInner)
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime (completedTime)
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz.CReal
  (convergesTo_mul_general)

local infix:50 " ≈ " => Q'.eqv
local notation "hw0" => smallNome_pos
local notation "hw1" => (by decide : smallNome < (1 : Q'))
local notation "a" => qpow smallNome 18
local notation "quarter" => Q'.mkPos 1 4 (by decide)
local notation "e" => WindowExpression.loop 0 bentLoop 1
local notation "he" => Nat.le_refl (0 : Nat)
local notation "C2" => centeredTimeMoment hw0 hw1 2 (loopState bentLoop) (loopState bentLoop)
local notation "C1" => centeredTimeMoment hw0 hw1 1 (loopState bentLoop) (loopState bentLoop)
local notation "G" => gainLimit hw0 hw1 e he a

attribute [local irreducible] gainLimit normalizedFiniteGain originalSquare
  originalOddMean commutatorGain evenPartition centeredPair middleRatio

private theorem finite_gain_original_pin (stage n : Nat)
    (hK : 1 ≤ headCutoff smallNome+stage) :
    normalizedFiniteGain hw0 hw1 2 stage n bentLoop a ≈
      Q'.divPos
        (commutatorGain smallNome (headCutoff smallNome+stage) 2 n bentObservable
          (originalOddMean (headCutoff smallNome+stage) hK (Nat.le_add_right _ _) n) a)
        (evenPartition smallNome (headCutoff smallNome+stage) 2 n)
        (evenPartition_positive hw0 hw1 (headCutoff smallNome+stage) 2
          (Nat.le_add_right _ _) n) := by
  unfold normalizedFiniteGain ownMean originalOddMean Q'.divPos
  rw [bentLoop_source_pin]
  exact Q'.eqv_refl _

private theorem finite_relative_lower (stage n : Nat)
    (hK : 1 ≤ headCutoff smallNome+stage) :
    quarter*centeredPair hw0 hw1 (headCutoff smallNome+stage) 2
      (Nat.le_add_right _ _) n 2 (sourceCharacter 2 bentLoop.edges 1)
      (middleRatio hw0 hw1 (headCutoff smallNome+stage) 2
        (Nat.le_add_right _ _) (n+1) n (sourceCharacter 2 bentLoop.edges 1)) ≤
    normalizedFiniteGain hw0 hw1 2 stage n bentLoop a := by
  let K := headCutoff smallNome+stage
  let c := originalOddMean K hK (Nat.le_add_right _ _) n
  let S := originalSquare K n c
  let g := commutatorGain smallNome K 2 n bentObservable c a
  let E := evenPartition smallNome K 2 n
  let hE := evenPartition_positive hw0 hw1 K 2 (Nat.le_add_right _ _) n
  let z := Q'.recipPos E hE
  have hraw : quarter*S ≤ g := originalOwn_gain_relative_lower K hK (Nat.le_add_right _ _) n
  have hm : (quarter*S)*z ≤ g*z := Q'.mul_le_mul_of_nonneg_right _ _ z hraw
    (Q'.le_of_lt (Q'.recipPos_pos E hE))
  have hs := originalOwn_square_chronological_pin K hK (Nat.le_add_right _ _) n
  have hleft : quarter*centeredPair hw0 hw1 K 2 (Nat.le_add_right _ _) n 2
      bentObservable (middleRatio hw0 hw1 K 2 (Nat.le_add_right _ _) (n+1) n bentObservable) ≈
      (quarter*S)*z := Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left quarter _ _ (Q'.eqv_symm hs))
    (Q'.eqv_symm (Q'.mul_assoc_eqv quarter S z))
  rw [bentLoop_source_pin]
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
    (Q'.le_trans' _ _ _ hm (Q'.ge_of_eqv (finite_gain_original_pin stage n hK)))

/-- The actual existing gain thresholds, with no new convergence input. -/
def bentGainDiagonalModulus (epsilon : Q') : Nat :=
  max (gainCutoffThreshold hw0 hw1 2 bentLoop epsilon)
    (gainTimeThreshold hw0 hw1 2 bentLoop epsilon)

/-- Original OWN finite gains converge to the EXISTING pinned gainLimit.
The representative threshold remains independent of cutoff and time. -/
theorem bent_gain_diagonal_converges :
    ConvergesTo (fun k => ofQ' (normalizedFiniteGain hw0 hw1 2 k k bentLoop a)) G := by
  intro epsilon hepsilon
  refine ⟨bentGainDiagonalModulus epsilon, fun k hk =>
    ⟨gainRepresentativeThreshold hw0 hw1 2 bentLoop epsilon, fun p hp => ?_⟩⟩
  exact normalizedFiniteGain_approx hw0 hw1 2 bentLoop epsilon hepsilon a
    (by decide) (by decide) k k p
    (Nat.le_trans (Nat.le_max_left _ _) hk)
    (Nat.le_trans (Nat.le_max_right _ _) hk) hp

/-- The relative finite gain survives on the same completed centered
moments. w^18 is a reference coefficient, not a source eigenpin. -/
theorem bent_signed_limit_relative_lower :
    leEv (mul (ofQ' quarter) C2)
      (sub C2 (mul (ofQ' a) C1)) := by
  have hpair := own_centeredPair_converges hw0 hw1 bentLoop 2
  have hscaled : ConvergesTo (fun k => ofQ' (quarter*centeredPair hw0 hw1
      (headCutoff smallNome+k) 2 (Nat.le_add_right _ _) k 2
      (sourceCharacter 2 bentLoop.edges 1)
      (middleRatio hw0 hw1 (headCutoff smallNome+k) 2 (Nat.le_add_right _ _)
        (k+1) k (sourceCharacter 2 bentLoop.edges 1)))) (mul (ofQ' quarter) C2) :=
    TrigAddCReal.convergesTo_congr_seq
      (fun k => (CRealAlg.ofQ'_mul quarter _).symm)
      (convergesTo_mul_general (convergesTo_const (ofQ' quarter)) hpair)
  have hgain : leEv (mul (ofQ' quarter) C2) G :=
    limit_le_of_eventual hscaled bent_gain_diagonal_converges 1 (fun k hk =>
      leEv_of_le (ofQ'_le_ofQ' (finite_relative_lower k k (by omega))))
  have hp : Equiv G (sub C2 (mul (ofQ' a) C1)) :=
    gainLimit_centered_pin hw0 hw1 e he a
  exact leEv_trans hgain (leEv_of_equiv hp)

/-- A positive rational floor for the actual signed completed gain. -/
theorem bent_signed_limit_floor :
    leEv (ofQ' (quarter*relativeSquareFloor)) G := by
  apply limit_le_of_eventual (convergesTo_const (ofQ' (quarter*relativeSquareFloor)))
    bent_gain_diagonal_converges 1
  intro k hk
  have hK : 1 ≤ headCutoff smallNome+k := by omega
  have hf := originalOwn_normalized_gain_floor
    (headCutoff smallNome+k) hK (Nat.le_add_right _ _) k
  exact leEv_of_le (ofQ'_le_ofQ' (Q'.le_trans' _ _ _ hf
    (Q'.ge_of_eqv (finite_gain_original_pin k k hK))))

local notation "v" => centeredVector hw0 hw1 (loopState bentLoop)
local notation "B" => completedInner hw0 hw1
local notation "T" => completedTime hw0 hw1

/-- SAME vector, original T and signed quadratic: C2-a*C1>=C2/4. -/
theorem bent_completed_signed_gain_relative_lower :
    RCle (RCscale quarter (B v (T 2 v)))
      (RCsub (B v (T 2 v)) (RCscale a (B v (T 1 v)))) := by
  rw [centeredVector_time_pairing, centeredVector_time_pairing]
  exact bent_signed_limit_relative_lower

theorem bent_completed_signed_gain_floor :
    RCle (Quotient.mk crealSetoid (ofQ' (quarter*relativeSquareFloor)))
      (RCsub (B v (T 2 v)) (RCscale a (B v (T 1 v)))) := by
  have hp := gainLimit_completed_pin hw0 hw1 e he a
  change Quotient.mk crealSetoid G =
    RCsub (B v (T 2 v)) (RCscale a (B v (T 1 v))) at hp
  rw [← hp]
  exact bent_signed_limit_floor

#print axioms bentGainDiagonalModulus
#print axioms bent_gain_diagonal_converges
#print axioms bent_signed_limit_relative_lower
#print axioms bent_signed_limit_floor
#print axioms bent_completed_signed_gain_relative_lower
#print axioms bent_completed_signed_gain_floor

end YMGap.Continuum.BF4WilsonSmallNomeBentSignedLimit
