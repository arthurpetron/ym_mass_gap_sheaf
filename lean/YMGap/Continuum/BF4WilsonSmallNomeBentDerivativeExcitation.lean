/-
# A literal bent-loop excitation in the original derivative graph

The EXISTING centered bent state at nome 1/16 and width two supplies the
actual domain point `fromTime v`. Its input is T1 v and its action is the
constructed range derivative of v. The original lag-two norm floor and
sharp graph-form gap give a positive rational energy floor. The original
centered-stream ceiling bounds both norms and the energy from above.

No new state, postulated domain, eigenmode or variance premise is used.
This is a fixed-parameter excitation of the witnessed derivative graph,
not a self-adjoint Hamiltonian, physical calibration or continuum result.
-/

import YMGap.Continuum.BF4WilsonSmallNomeBentCompletedGain
import YMGap.Continuum.BF4WilsonAllNomeDerivativeGraphGap
import YMGap.Continuum.BF4WilsonAllNomeDerivativeGraphReal

namespace YMGap.Continuum.BF4WilsonSmallNomeBentDerivativeExcitation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeSmallFundamentalCap
  (smallNome smallNome_pos)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTerminalGain (relativeSquareFloor)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferMixingRate
  (mixFraction mixFraction_positive)
open YMGap.Continuum.BF4WilsonSmallNomeBentCompletedGain
  (bentLoop bent_completed_T1_norm_floor bent_completed_T1_ne_zero)
open YMGap.Continuum.BF4WilsonAllNomeLoopTimePin (loopState)
open YMGap.Continuum.BF4WilsonAllNomeCenteredVector
  (centeredVector centeredStream centeredExcitation centeredNormCeiling centeredVector_norm_ceiling)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4WilsonAllNomeBilinearTime
open YMGap.Continuum.BF4WilsonAllNomeLinear (completedZero completedSub)
open YMGap.Continuum.BF4WilsonAllNomeCompletedPairingContinuity
  (completedInner_sub_left completedInner_sub_right)
open YMGap.Continuum.BF4WilsonAllNomeDyadicDerivative (derivativeAction derivativeCertificate)
open YMGap.Continuum.BF4WilsonAllNomeDyadicDerivativeLaws (derivativeAction_norm_bound)
open YMGap.Continuum.BF4WilsonAllNomeDerivativeGraph
open YMGap.Continuum.BF4WilsonAllNomeDerivativeGraphGap (action_form_sharp_gap)
open YMGap.Continuum.BF4WilsonAllNomeDerivativeGraphReal
  (realRemainder realTaylorCertificate)
open YMGap.Continuum.PositiveRealDyadicTimeData (PositiveTime)
open YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimePins (timeValue realValue)

local notation "hw0" => smallNome_pos
local notation "hw1" => (by decide : smallNome < (1 : Q'))
local notation "v" => centeredVector hw0 hw1 (loopState bentLoop)
local notation "B" => completedInner hw0 hw1
local notation "T" => completedTime hw0 hw1
local notation "U" => unitState hw0 hw1 2
local notation "Z" => completedZero hw0 hw1 2
local notation "rat" q:arg => Quotient.mk crealSetoid (ofQ' q)

/-- The actual original range-domain witness, with its original centered preimage. -/
def bentDerivativePoint : Domain hw0 hw1 (width := 2) := fromTime hw0 hw1 v

/-- The computed ceiling of the SAME centered Cauchy stream. -/
def bentDerivativeNormCeiling : Q' :=
  centeredNormCeiling hw0 hw1 (loopState bentLoop)

/-- The original kinetic fraction times the checked 2^(-128) image floor. -/
def bentDerivativeEnergyFloor : Q' :=
  mixFraction hw0 hw1 2 * relativeSquareFloor

/-- Energy pairing of the actual domain input and its witnessed action. -/
def bentDerivativeEnergy : RC :=
  B (input hw0 hw1 bentDerivativePoint) (action hw0 hw1 bentDerivativePoint)

attribute [local irreducible] bentDerivativePoint

theorem bentDerivativePoint_pins :
    input hw0 hw1 bentDerivativePoint = T 1 v ∧
      action hw0 hw1 bentDerivativePoint = derivativeAction hw0 hw1 v := by
  constructor
  · unfold bentDerivativePoint
    exact input_fromTime hw0 hw1 v
  · unfold bentDerivativePoint
    exact action_fromTime hw0 hw1 v

/-- Orthogonality uses the unchanged unit of the original completion. -/
theorem bentDerivativePoint_orthogonal :
    B U (input hw0 hw1 bentDerivativePoint) = RCzero := by
  rw [bentDerivativePoint_pins.1]
  exact completedTime_preserves_vacuumComplement hw0 hw1 1 v
    (centeredExcitation hw0 hw1 (loopState bentLoop)).property

/-- Neither image nor action needs a supplied norm cap. -/
theorem bentDerivativePoint_norm_bounds :
    RCle (B (input hw0 hw1 bentDerivativePoint) (input hw0 hw1 bentDerivativePoint))
      (rat bentDerivativeNormCeiling) ∧
    RCle (B (action hw0 hw1 bentDerivativePoint) (action hw0 hw1 bentDerivativePoint))
      (rat bentDerivativeNormCeiling) := by
  have hc : RCle (B v v) (rat bentDerivativeNormCeiling) :=
    centeredVector_norm_ceiling hw0 hw1 (loopState bentLoop)
  constructor
  · rw [bentDerivativePoint_pins.1]
    exact RCle_trans (completedInner_time_contraction hw0 hw1 1 v) hc
  · rw [bentDerivativePoint_pins.2]
    exact RCle_trans (derivativeAction_norm_bound hw0 hw1 v) hc

theorem bentDerivativePoint_norm_floor :
    RCle (rat relativeSquareFloor)
      (B (input hw0 hw1 bentDerivativePoint) (input hw0 hw1 bentDerivativePoint)) := by
  rw [bentDerivativePoint_pins.1]
  exact bent_completed_T1_norm_floor

theorem bentDerivativePoint_input_ne_zero : input hw0 hw1 bentDerivativePoint ≠ Z := by
  rw [bentDerivativePoint_pins.1]
  exact bent_completed_T1_ne_zero

private theorem rc_add_zero (a : RC) : RCadd a RCzero = a := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.eqv_of_eq (Q'.add_zero' (A.approx n))))

private theorem pair_balance (a b c : RC) :
    RCadd (RCadd b b) (RCsub (RCsub a b) (RCsub b c)) = RCadd a c := by
  refine Quotient.inductionOn₃ a b c ?_
  intro A B' C
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.add (.add (.var 1) (.var 1))
        (.add (.add (.var 0) (.neg (.var 1)))
          (.neg (.add (.var 1) (.neg (.var 2))))))
      (.add (.var 0) (.var 2)) (by decide)
      (fun | 0 => A.approx n | 1 => B'.approx n | _ => C.approx n)))

private theorem half_double (a : RC) :
    RCscale HalfPow.half (RCadd a a) = a := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    Q'.eqv_trans _ _ _ (Q'.mul_add_eqv HalfPow.half (A.approx n) (A.approx n))
      (ExpNeg.two_halves (A.approx n))))

private theorem energy_upper : RCle bentDerivativeEnergy (rat bentDerivativeNormCeiling) := by
  let x := input hw0 hw1 bentDerivativePoint
  let y := action hw0 hw1 bentDerivativePoint
  have hp := completedInner_nonnegative hw0 hw1 (completedSub hw0 hw1 x y)
  rw [completedInner_sub_left, completedInner_sub_right, completedInner_sub_right,
    completedInner_symm hw0 hw1 y x] at hp
  have hdouble := RCadd_le_add (RCle_refl (RCadd (B x y) (B x y))) hp
  rw [rc_add_zero, pair_balance] at hdouble
  have hn := RCadd_le_add bentDerivativePoint_norm_bounds.1 bentDerivativePoint_norm_bounds.2
  have hh := RCscale_mono HalfPow.half_nonneg (RCle_trans hdouble hn)
  simpa only [half_double] using hh

private theorem scaled_floor_pin :
    RCscale (mixFraction hw0 hw1 2) (rat relativeSquareFloor) =
      rat bentDerivativeEnergyFloor :=
  Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.eqv_refl _))

/-- Positive rational lower energy and computed upper energy, with no
Hamiltonian or spectral interpretation asserted. -/
theorem bentDerivativeEnergy_bounds :
    (0 : Q') < bentDerivativeEnergyFloor ∧
      RCle (rat bentDerivativeEnergyFloor) bentDerivativeEnergy ∧
      RCle bentDerivativeEnergy (rat bentDerivativeNormCeiling) := by
  have hpos : (0 : Q') < bentDerivativeEnergyFloor :=
    Q'.mul_pos (mixFraction_positive hw0 hw1 2)
      (by decide : (0 : Q') < relativeSquareFloor)
  have hf := RCscale_mono (Q'.le_of_lt (mixFraction_positive hw0 hw1 2))
    bentDerivativePoint_norm_floor
  rw [scaled_floor_pin] at hf
  exact ⟨hpos, RCle_trans hf
    (action_form_sharp_gap hw0 hw1 bentDerivativePoint bentDerivativePoint_orthogonal),
    energy_upper⟩

theorem bentDerivativeEnergy_ne_zero : bentDerivativeEnergy ≠ RCzero := by
  intro hz
  have h := bentDerivativeEnergy_bounds.2.1
  rw [hz] at h
  have hbad : bentDerivativeEnergyFloor ≤ (0 : Q') := by
    apply Q'.le_of_forall_pos_add
    intro epsilon he
    obtain ⟨M, hM⟩ := h epsilon he
    exact hM M (Nat.le_refl M)
  exact (by decide : ¬ ((0 : Q') < 0))
    (Q'.pos_of_lt_of_le bentDerivativeEnergy_bounds.1 hbad)

theorem bentDerivativePoint_action_ne_zero : action hw0 hw1 bentDerivativePoint ≠ Z := by
  intro hz
  apply bentDerivativeEnergy_ne_zero
  unfold bentDerivativeEnergy
  rw [hz, completedInner_zero_right]

/-- The literal centered preimage and constructed derivative representative
produce an explicit small-positive-real-time Taylor witness for THIS domain
point. No graph hypothesis or representative choice is supplied by the caller. -/
def bentDerivativeTaylorCertificate (epsilon : Q') (he : (0 : Q') < epsilon) :
    Σ' radius : Q', ((0 : Q') < radius) ×'
      (∀ D : PositiveTime,
        RCle (realValue (timeValue D)) (rat radius) →
          RCle (B (realRemainder hw0 hw1 D
              (input hw0 hw1 bentDerivativePoint) (action hw0 hw1 bentDerivativePoint))
            (realRemainder hw0 hw1 D
              (input hw0 hw1 bentDerivativePoint) (action hw0 hw1 bentDerivativePoint)))
            (RCmul (RCmul (realValue (timeValue D)) (realValue (timeValue D)))
              (rat epsilon))) := by
  let C := centeredStream hw0 hw1 (loopState bentLoop)
  let X := (timeNonexpansive hw0 hw1 1).mapCauchy C
  let Y := (derivativeCertificate hw0 hw1 C).1
  let G : GraphLimit hw0 hw1
      (Quotient.mk (CRealSeminormCompletion.SquaredSeminorm.completionSetoid
        (BF4WilsonAllNomeSeminorm.seminorm hw0 hw1 (width := 2))) X)
      (Quotient.mk (CRealSeminormCompletion.SquaredSeminorm.completionSetoid
        (BF4WilsonAllNomeSeminorm.seminorm hw0 hw1 (width := 2))) Y) :=
    core hw0 hw1 v
  let certificate := realTaylorCertificate hw0 hw1 G (fun _ => C)
    (fun _ => rfl) epsilon he
  refine ⟨certificate.1, certificate.2.1, ?_⟩
  intro D ht
  have h := certificate.2.2 D ht
  rw [bentDerivativePoint_pins.1, bentDerivativePoint_pins.2]
  exact h

#print axioms bentDerivativePoint
#print axioms bentDerivativeNormCeiling
#print axioms bentDerivativeEnergyFloor
#print axioms bentDerivativeEnergy
#print axioms bentDerivativePoint_pins
#print axioms bentDerivativePoint_orthogonal
#print axioms bentDerivativePoint_norm_bounds
#print axioms bentDerivativePoint_norm_floor
#print axioms bentDerivativePoint_input_ne_zero
#print axioms bentDerivativeEnergy_bounds
#print axioms bentDerivativeEnergy_ne_zero
#print axioms bentDerivativePoint_action_ne_zero
#print axioms bentDerivativeTaylorCertificate

end YMGap.Continuum.BF4WilsonSmallNomeBentDerivativeExcitation
