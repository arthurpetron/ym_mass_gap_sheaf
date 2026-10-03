/-
# The original antisymmetric current reaches the SAME response drop

The literal current retains both spatial weights and the actual terminal
and centered message. Its normalization is (half*current)*recip(E), with
the SAME even partition and the finite odd OWN mean. At reference one the
mean residue vanishes exactly, so no separate residue depth onset is needed.

Nome, width and loop are fixed. This identifies the signed analytic source
of C1-C2; it does not produce a relative upper bound, a changing family,
survival, physical calibration or a continuum result.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialJumpCurrent
import YMGap.Continuum.BF4WilsonAllNomeDyadicSteinGainLimit

namespace YMGap.Continuum.BF4WilsonAllNomeJumpCurrentLimit

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe
  (SourceLoop sourceCharacter sourceCharacter_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow (WindowExpression)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket (terminalMessage)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredOwnYoung (ownMean)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredCommutatorGain
  (centeredMessage commutatorGain)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredNoiseDrift
  (evenPartition evenPartition_positive)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredGainSourcePair
  (fullSourceDefectPair commutatorGain_source_pair)
open YMGap.Continuum.BF4ExactSlabFixedSpatialJumpCurrent
  (signedCurrent original_centered_current_source_pin)
open YMGap.Continuum.BF4WilsonAllNomeDyadicSteinGainLimit (normalizedSourcePair)
open YMGap.Continuum.BF4WilsonAllNomeFilteredFiniteGainApproximation (normalizedFiniteGain)
open YMGap.Continuum.BF4WilsonAllNomeFilteredFiniteGainLimit
  (gainCutoffThreshold gainTimeThreshold gainRepresentativeThreshold normalizedFiniteGain_approx)
open YMGap.Continuum.BF4WilsonAllNomeFilteredGainLimit (gainLimit gainLimit_centered_pin)
open YMGap.Continuum.BF4WilsonAllNomeZeroRadiusIncrement (state)
open YMGap.Continuum.BF4WilsonAllNomeCenteredMoments (centeredTimeMoment)
open YMGap.Continuum.BF4WilsonAllNomeCenteredVector
  (centeredVector centeredVector_time_pairing)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner (completedInner)
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime (completedTime)

local infix:50 " ≈ " => Q'.eqv
attribute [local irreducible] ownMean evenPartition signedCurrent fullSourceDefectPair
  commutatorGain centeredMessage terminalMessage normalizedFiniteGain gainLimit

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (width : Nat) (loop : SourceLoop width)

/-- Half the literal signed current, divided by its original EVEN mass. -/
def normalizedOwnCurrent (stage n : Nat) : Q' :=
  let K := headCutoff w+stage
  let hK := Nat.le_add_right (headCutoff w) stage
  let f := sourceCharacter width loop.edges 1
  let c := ownMean hw0 hw1 K width hK n loop
  (HalfPow.half*signedCurrent w K width (terminalMessage w K width n)
    (centeredMessage w K width n f c) f)*
    Q'.recipPos (evenPartition w K width n) (evenPartition_positive hw0 hw1 K width hK n)

private theorem half_current (P z : Q') :
    (HalfPow.half*((-2)*P))*z ≈ -(P*z) :=
  Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ z (Q'.mul_assoc_eqv HalfPow.half (-2) P).symm)
    (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ z (Q'.mul_eqv_congr_right _ _ P
        (by decide : HalfPow.half*(-2) ≈ (-1 : Q'))))
      (poly_identity_of_normal_eq
        (.mul (.mul (.const (-1)) (.var 0)) (.var 1))
        (.neg (.mul (.var 0) (.var 1))) (by decide) (fun | 0 => P | _ => z)))

/-- The antisymmetric normalization is exactly the negative full-source pair.
No mean or partition replacement is made. -/
theorem normalizedOwnCurrent_source_pin (stage n : Nat) :
    normalizedOwnCurrent hw0 hw1 width loop stage n ≈
      -normalizedSourcePair hw0 hw1 width stage n loop 1 := by
  let K := headCutoff w+stage
  let hK := Nat.le_add_right (headCutoff w) stage
  let f := sourceCharacter width loop.edges 1
  let c := ownMean hw0 hw1 K width hK n loop
  let z := Q'.recipPos (evenPartition w K width n)
    (evenPartition_positive hw0 hw1 K width hK n)
  have h := original_centered_current_source_pin w K width n f c
    (sourceCharacter_supported width loop.edges 1)
  change (HalfPow.half*signedCurrent w K width (terminalMessage w K width n)
    (centeredMessage w K width n f c) f)*z ≈ -(fullSourceDefectPair w K width n f c 1*z)
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ z (Q'.mul_eqv_congr_left HalfPow.half _ _ h))
    (half_current _ z)

/-- Reference one cancels the finite mean residue EXACTLY. -/
theorem normalizedOwnCurrent_gain_pin (stage n : Nat) :
    normalizedOwnCurrent hw0 hw1 width loop stage n ≈
      -normalizedFiniteGain hw0 hw1 width stage n loop 1 := by
  let K := headCutoff w+stage
  let hK := Nat.le_add_right (headCutoff w) stage
  let f := sourceCharacter width loop.edges 1
  let c := ownMean hw0 hw1 K width hK n loop
  have hg : commutatorGain w K width n f c 1 ≈ fullSourceDefectPair w K width n f c 1 :=
    Q'.eqv_trans _ _ _ (commutatorGain_source_pair w K width n f c 1)
      (poly_identity_of_normal_eq
        (.add (.var 0) (.mul (.mul (.add (.const 1) (.neg (.const 1))) (.var 1)) (.var 2)))
        (.var 0) (by decide) (fun
          | 0 => fullSourceDefectPair w K width n f c 1
          | 1 => c
          | _ => BF4ExactSlabFixedSpatialFilteredGainSourcePair.centeredMeanPair w K width n f c))
  have hn : normalizedFiniteGain hw0 hw1 width stage n loop 1 ≈
      normalizedSourcePair hw0 hw1 width stage n loop 1 := by
    unfold normalizedFiniteGain normalizedSourcePair
    exact Q'.mul_eqv_congr_right _ _ _ hg
  exact Q'.eqv_trans _ _ _ (normalizedOwnCurrent_source_pin hw0 hw1 width loop stage n)
    (Q'.neg_eqv_congr _ _ hn.symm)

/-- Computed diagonal onset; the independent representative threshold is
gainRepresentativeThreshold epsilon. There is NO mean-residue onset. -/
def currentDiagonalModulus (epsilon : Q') : Nat :=
  max (gainCutoffThreshold hw0 hw1 width loop epsilon)
    (gainTimeThreshold hw0 hw1 width loop epsilon)

/-- The actual current diagonal converges to the negative EXISTING gain.
Both approximation directions use the original finite OWN center. -/
theorem own_current_diagonal_converges :
    ConvergesTo (fun k => ofQ' (normalizedOwnCurrent hw0 hw1 width loop k k))
      (neg (gainLimit hw0 hw1 (WindowExpression.loop 0 loop 1) (Nat.le_refl 0) 1)) := by
  intro epsilon he
  refine ⟨currentDiagonalModulus hw0 hw1 width loop epsilon, fun k hk => ?_⟩
  refine ⟨gainRepresentativeThreshold hw0 hw1 width loop epsilon, fun p hp => ?_⟩
  have h := normalizedFiniteGain_approx hw0 hw1 width loop epsilon he 1
    (by decide) (by decide) k k p
    (Nat.le_trans (Nat.le_max_left _ _) hk)
    (Nat.le_trans (Nat.le_max_right _ _) hk) hp
  have hpin := normalizedOwnCurrent_gain_pin hw0 hw1 width loop k k
  exact ⟨Q'.le_trans' _ _ _ (Q'.le_of_eqv hpin) (Q'.neg_le_neg_add h.2),
    Q'.le_trans' _ _ _ (Q'.neg_le_neg_add h.1)
      (Q'.le_of_eqv (Q'.add_eqv_congr_right _ _ _ hpin.symm))⟩

/-- Exact centered C1-C2 on the existing state; no new limit is defined. -/
theorem current_limit_centered_pin :
    Equiv (neg (gainLimit hw0 hw1 (WindowExpression.loop 0 loop 1) (Nat.le_refl 0) 1))
      (sub (centeredTimeMoment hw0 hw1 1
        (state (WindowExpression.loop 0 loop 1) (Nat.le_refl 0))
        (state (WindowExpression.loop 0 loop 1) (Nat.le_refl 0)))
        (centeredTimeMoment hw0 hw1 2
          (state (WindowExpression.loop 0 loop 1) (Nat.le_refl 0))
          (state (WindowExpression.loop 0 loop 1) (Nat.le_refl 0)))) := by
  apply (neg_congr (gainLimit_centered_pin hw0 hw1
    (WindowExpression.loop 0 loop 1) (Nat.le_refl 0) 1)).trans
  exact SumOfSquares.Equiv_of_approx_eqv (fun p => poly_identity_of_normal_eq
    (.neg (.add (.var 1) (.neg (.mul (.const 1) (.var 0)))))
    (.add (.var 0) (.neg (.var 1))) (by decide) (fun
      | 0 => (centeredTimeMoment hw0 hw1 1
          (state (WindowExpression.loop 0 loop 1) (Nat.le_refl 0))
          (state (WindowExpression.loop 0 loop 1) (Nat.le_refl 0))).approx p
      | _ => (centeredTimeMoment hw0 hw1 2
          (state (WindowExpression.loop 0 loop 1) (Nat.le_refl 0))
          (state (WindowExpression.loop 0 loop 1) (Nat.le_refl 0))).approx p))

/-- Convergence to the existing centered response DROP, not a new limit. -/
theorem own_current_centered_converges :
    ConvergesTo (fun k => ofQ' (normalizedOwnCurrent hw0 hw1 width loop k k))
      (sub (centeredTimeMoment hw0 hw1 1
        (state (WindowExpression.loop 0 loop 1) (Nat.le_refl 0))
        (state (WindowExpression.loop 0 loop 1) (Nat.le_refl 0)))
        (centeredTimeMoment hw0 hw1 2
          (state (WindowExpression.loop 0 loop 1) (Nat.le_refl 0))
          (state (WindowExpression.loop 0 loop 1) (Nat.le_refl 0)))) :=
  ArctanTrigConvergesProof.convergesTo_of_equiv
    (own_current_diagonal_converges hw0 hw1 width loop)
    (current_limit_centered_pin hw0 hw1 width loop)

/-- The SAME completed vector and original time map, at literal lags one/two. -/
theorem current_limit_completed_pin :
    let v := centeredVector hw0 hw1 (state (WindowExpression.loop 0 loop 1) (Nat.le_refl 0))
    Quotient.mk crealSetoid
      (neg (gainLimit hw0 hw1 (WindowExpression.loop 0 loop 1) (Nat.le_refl 0) 1)) =
      RCsub (completedInner hw0 hw1 v (completedTime hw0 hw1 1 v))
        (completedInner hw0 hw1 v (completedTime hw0 hw1 2 v)) := by
  dsimp only
  rw [centeredVector_time_pairing, centeredVector_time_pairing]
  exact Quotient.sound (current_limit_centered_pin hw0 hw1 width loop)

end YMGap.Continuum.BF4WilsonAllNomeJumpCurrentLimit

#print axioms YMGap.Continuum.BF4WilsonAllNomeJumpCurrentLimit.normalizedOwnCurrent
#print axioms YMGap.Continuum.BF4WilsonAllNomeJumpCurrentLimit.normalizedOwnCurrent_source_pin
#print axioms YMGap.Continuum.BF4WilsonAllNomeJumpCurrentLimit.normalizedOwnCurrent_gain_pin
#print axioms YMGap.Continuum.BF4WilsonAllNomeJumpCurrentLimit.currentDiagonalModulus
#print axioms YMGap.Continuum.BF4WilsonAllNomeJumpCurrentLimit.own_current_diagonal_converges
#print axioms YMGap.Continuum.BF4WilsonAllNomeJumpCurrentLimit.current_limit_centered_pin
#print axioms YMGap.Continuum.BF4WilsonAllNomeJumpCurrentLimit.own_current_centered_converges
#print axioms YMGap.Continuum.BF4WilsonAllNomeJumpCurrentLimit.current_limit_completed_pin
