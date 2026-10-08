/-
# The actual spatial swap on the SAME original Wilson completion

The original source map is nonexpansive by its proved reflected-form pin,
not by an assumed operator bound. It transports each supplied Cauchy row
with the SAME modulus. Its literal involution, signed linearity and temporal
commutation descend through the existing null/Cauchy quotient. The existing
completed pairing and distance are preserved; the actual unit is fixed.

This is one finite spatial permutation at fixed width and nome, not spatial
translations, continuous Euclidean covariance or a continuum QFT. No new
carrier, measure, norm, range witness or mass-gap estimate is postulated.
-/

import YMGap.Continuum.BF4WilsonAllNomeSpatialAxisSwapAlgebra
import YMGap.Continuum.BF4WilsonAllNomeDistance
import YMGap.Continuum.BF4WilsonAllNomeCompletedPairingContinuity
import YMGap.Continuum.RingNormaliser

namespace YMGap.Continuum.BF4WilsonAllNomeSpatialAxisSwapCompletion

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm
  (IntrinsicExpression unit)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicSeminorm (sum)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicAlgebra (smul)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPhysicalTime (advance)
open YMGap.Continuum.BF4WilsonAllNomeSeminorm (seminorm distSq distSq_refl)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4WilsonAllNomeLinear
open YMGap.Continuum.BF4WilsonAllNomeBilinearTime
open YMGap.Continuum.BF4WilsonAllNomeCompletedPairingContinuity
open YMGap.Continuum.BF4WilsonAllNomeDistance (completedDist)
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4WilsonAllNomeSpatialAxisSwapForm
open YMGap.Continuum.BF4WilsonAllNomeSpatialAxisSwapAlgebra
open YMGap.Continuum.CRealSeminormCompletion.SquaredSeminorm.NonexpansiveSemigroup
  (closeOfPointwiseNull)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "D" => seminorm hw0 hw1 (width := width)
local notation "PD" => pairingData hw0 hw1 (width := width)
local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "S" => swapNonexpansive hw0 hw1 (width := width)
local notation "T" => completedTime hw0 hw1
local notation "R" => CRealSeminormPairingCompletion.representativeInner PD

/-- The already constructed source nonexpansiveness supplies the quotient map. -/
def completedSwap : V → V := (S).completionMap

local notation "U" => completedSwap hw0 hw1

theorem completedSwap_embed (x : IntrinsicExpression width) :
    U (embed hw0 hw1 x) = embed hw0 hw1 (swapIntrinsic x) := rfl

/-- No new tolerance or index selection: retain the supplied modulus verbatim. -/
theorem swap_cauchy_modulus (X : (D).Cauchy) :
    ((S).mapCauchy X).modulus = X.modulus := rfl

theorem completedSwap_involutive (x : V) : U (U x) = x := by
  refine Quotient.inductionOn x ?_
  intro X
  apply Quotient.sound
  exact ⟨closeOfPointwiseNull (fun k => by
    change Equiv (distSq hw0 hw1 (swapIntrinsic (swapIntrinsic (X.seq k))) (X.seq k)) czero
    rw [swapIntrinsic_involutive]
    exact distSq_refl hw0 hw1 _)⟩

theorem completedSwap_time (n : Nat) (x : V) : U (T n x) = T n (U x) := by
  refine Quotient.inductionOn x ?_
  intro X
  apply Quotient.sound
  exact ⟨closeOfPointwiseNull (fun k => by
    change Equiv (distSq hw0 hw1 (swapIntrinsic (advance n (X.seq k)))
      (advance n (swapIntrinsic (X.seq k)))) czero
    rw [swap_advance]
    exact distSq_refl hw0 hw1 _)⟩

theorem completedSwap_add (x y : V) :
    U (completedAdd hw0 hw1 x y) = completedAdd hw0 hw1 (U x) (U y) := by
  refine Quotient.inductionOn₂ x y ?_
  intro X Y
  apply Quotient.sound
  exact ⟨closeOfPointwiseNull (fun k => by
    change Equiv (distSq hw0 hw1 (swapIntrinsic (sum (X.seq k) (Y.seq k)))
      (sum (swapIntrinsic (X.seq k)) (swapIntrinsic (Y.seq k)))) czero
    rw [swapIntrinsic_sum]
    exact distSq_refl hw0 hw1 _)⟩

theorem completedSwap_smul (c : Q') (x : V) :
    U (completedSmul hw0 hw1 c x) = completedSmul hw0 hw1 c (U x) := by
  refine Quotient.inductionOn x ?_
  intro X
  apply Quotient.sound
  exact ⟨closeOfPointwiseNull (fun k => by
    change Equiv (distSq hw0 hw1 (swapIntrinsic (smul c (X.seq k)))
      (smul c (swapIntrinsic (X.seq k)))) czero
    rw [swapIntrinsic_smul]
    exact distSq_refl hw0 hw1 _)⟩

theorem completedSwap_sub (x y : V) :
    U (completedSub hw0 hw1 x y) = completedSub hw0 hw1 (U x) (U y) := by
  unfold completedSub completedNeg
  rw [completedSwap_add, completedSwap_smul]

theorem completedSwap_unit : U (unitState hw0 hw1 width) = unitState hw0 hw1 width := by
  unfold unitState
  rw [completedSwap_embed, swapIntrinsic_unit]

theorem completedSwap_zero :
    U (completedZero hw0 hw1 width) = completedZero hw0 hw1 width := by
  unfold completedZero
  rw [completedSwap_embed, swapIntrinsic_zero]

/-- The existing mixed pairing limit; its inner and outer moduli are not replaced. -/
theorem representativeInner_swap (X Y : (D).Cauchy) :
    Equiv (R ((S).mapCauchy X) ((S).mapCauchy Y)) (R X Y) :=
  Equiv_of_limit_of_equal
    (fun k => intrinsicForm_swap hw0 hw1 (X.seq k) (Y.seq k))
    (CRealSeminormPairingCompletion.pairSequence_converges PD
      ((S).mapCauchy X) ((S).mapCauchy Y))
    (CRealSeminormPairingCompletion.pairSequence_converges PD X Y)

theorem completedInner_swap (x y : V) : B (U x) (U y) = B x y := by
  refine Quotient.inductionOn₂ x y ?_
  intro X Y
  exact Quotient.sound (representativeInner_swap hw0 hw1 X Y)

/-- The involutive spatial map is self-adjoint for the SAME pairing. -/
theorem completedInner_swap_balance (x y : V) : B (U x) y = B x (U y) := by
  have h := completedInner_swap hw0 hw1 x (U y)
  rw [completedSwap_involutive] at h
  exact h

theorem completedDist_swap (x y : V) :
    completedDist hw0 hw1 (U x) (U y) = completedDist hw0 hw1 x y := by
  unfold completedDist
  rw [← completedSwap_sub, completedInner_swap]

/-- Actual orthogonality to the original unit is preserved, not assumed. -/
theorem completedSwap_preserves_vacuumComplement (x : V)
    (hx : B (unitState hw0 hw1 width) x = RCzero) :
    B (unitState hw0 hw1 width) (U x) = RCzero := by
  rw [← completedInner_swap_balance, completedSwap_unit]
  exact hx

/-! The following averages remain on the literal original completion. A
detector is unchanged only when its source has an *actual* swap-sector pin. -/

local notation "A" => completedAdd hw0 hw1
local notation "M" => completedSmul hw0 hw1
local notation "Sub" => completedSub hw0 hw1

/-- The even average under the actual spatial involution. -/
def evenPart (v : V) : V := M HalfPow.half (A v (U v))

/-- The odd average under the actual spatial involution. -/
def oddPart (v : V) : V := M HalfPow.half (Sub v (U v))

private theorem rc_half_double (a : RC) :
    RCscale HalfPow.half (RCadd a a) = a := by
  refine Quotient.inductionOn a ?_
  intro x
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    Q'.eqv_trans _ _ _
      (Q'.mul_add_eqv HalfPow.half (x.approx n) (x.approx n))
      (ExpNeg.two_halves (x.approx n))))

private theorem rc_half_sub_neg (a : RC) :
    RCscale HalfPow.half (RCsub a (RCscale (-1) a)) = a := by
  refine Quotient.inductionOn a ?_
  intro x
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    Q'.eqv_trans _ _ _
      (poly_identity_of_normal_eq
        (.mul (.var 1)
          (.add (.var 0) (.neg (.mul (.const (-1)) (.var 0)))))
        (.mul (.var 1) (.add (.var 0) (.var 0))) (by decide)
        (fun | 0 => x.approx n | _ => HalfPow.half))
      (Q'.eqv_trans _ _ _
        (Q'.mul_add_eqv HalfPow.half (x.approx n) (x.approx n))
        (ExpNeg.two_halves (x.approx n)))))

private theorem rc_parity_pyth (a b : RC) :
    RCadd
      (RCscale HalfPow.half
        (RCadd (RCscale HalfPow.half (RCadd a b))
          (RCscale HalfPow.half (RCadd b a))))
      (RCscale HalfPow.half
        (RCsub (RCscale HalfPow.half (RCsub a b))
          (RCscale HalfPow.half (RCsub b a)))) = a := by
  refine Quotient.inductionOn₂ a b ?_
  intro x y
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq
      (.add
        (.mul (.var 2)
          (.add
            (.mul (.var 2) (.add (.var 0) (.var 1)))
            (.mul (.var 2) (.add (.var 1) (.var 0)))))
        (.mul (.var 2)
          (.add
            (.mul (.var 2) (.add (.var 0) (.neg (.var 1))))
            (.neg (.mul (.var 2)
              (.add (.var 1) (.neg (.var 0))))))))
      (.mul (.mul (.const 4) (.mul (.var 2) (.var 2))) (.var 0))
      (by decide)
      (fun | 0 => x.approx n | 1 => y.approx n | _ => HalfPow.half))
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right
          (Q'.ofInt 4 * (HalfPow.half * HalfPow.half)) 1
          (x.approx n) (by decide))
        (Q'.one_mul_eqv (x.approx n)))))

private theorem rc_add_zero (a : RC) : RCadd a RCzero = a := by
  refine Quotient.inductionOn a ?_
  intro x
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.eqv_of_eq (Q'.add_zero' (x.approx n))))

private theorem rc_zero_add (a : RC) : RCadd RCzero a = a := by
  refine Quotient.inductionOn a ?_
  intro x
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.eqv_of_eq (Q'.zero_add' (x.approx n))))

/-- Exact Pythagoras for the two rational averages, with no source change. -/
theorem sector_norm_split (v : V) :
    RCadd (B (evenPart hw0 hw1 v) (evenPart hw0 hw1 v))
      (B (oddPart hw0 hw1 v) (oddPart hw0 hw1 v)) = B v v := by
  have heven : B (evenPart hw0 hw1 v) (evenPart hw0 hw1 v) =
      RCscale HalfPow.half
        (RCadd (RCscale HalfPow.half (RCadd (B v v) (B v (U v))))
          (RCscale HalfPow.half (RCadd (B v (U v)) (B v v)))) := by
    unfold evenPart
    rw [completedInner_smul_left, completedInner_add_left,
      completedInner_smul_right, completedInner_smul_right,
      completedInner_add_right, completedInner_add_right,
      completedInner_swap_balance hw0 hw1 v v,
      completedInner_swap hw0 hw1 v v]
  have hodd : B (oddPart hw0 hw1 v) (oddPart hw0 hw1 v) =
      RCscale HalfPow.half
        (RCsub (RCscale HalfPow.half (RCsub (B v v) (B v (U v))))
          (RCscale HalfPow.half (RCsub (B v (U v)) (B v v)))) := by
    unfold oddPart
    rw [completedInner_smul_left, completedInner_sub_left,
      completedInner_smul_right, completedInner_smul_right,
      completedInner_sub_right, completedInner_sub_right,
      completedInner_swap_balance hw0 hw1 v v,
      completedInner_swap hw0 hw1 v v]
  rw [heven, hodd]
  exact rc_parity_pyth (B v v) (B v (U v))

theorem evenPart_norm_le (v : V) :
    RCle (B (evenPart hw0 hw1 v) (evenPart hw0 hw1 v)) (B v v) := by
  have h := RCadd_le_add
    (RCle_refl (B (evenPart hw0 hw1 v) (evenPart hw0 hw1 v)))
    (completedInner_nonnegative hw0 hw1 (oddPart hw0 hw1 v))
  rw [rc_add_zero, sector_norm_split hw0 hw1 v] at h
  exact h

theorem oddPart_norm_le (v : V) :
    RCle (B (oddPart hw0 hw1 v) (oddPart hw0 hw1 v)) (B v v) := by
  have h := RCadd_le_add
    (completedInner_nonnegative hw0 hw1 (evenPart hw0 hw1 v))
    (RCle_refl (B (oddPart hw0 hw1 v) (oddPart hw0 hw1 v)))
  rw [rc_zero_add, sector_norm_split hw0 hw1 v] at h
  exact h

theorem evenPart_time (n : Nat) (v : V) :
    evenPart hw0 hw1 (T n v) = T n (evenPart hw0 hw1 v) := by
  unfold evenPart
  rw [completedTime_smul, completedTime_additive, completedSwap_time]

theorem oddPart_time (n : Nat) (v : V) :
    oddPart hw0 hw1 (T n v) = T n (oddPart hw0 hw1 v) := by
  unfold oddPart
  rw [completedTime_smul, completedTime_sub, completedSwap_time]

/-- For an actual even source, averaging the test preserves its detector. -/
theorem evenPart_detector (x v : V) (hx : U x = x) :
    B x (evenPart hw0 hw1 v) = B x v := by
  have hpair : B x (U v) = B x v := by
    rw [← completedInner_swap_balance hw0 hw1 x v, hx]
  unfold evenPart
  rw [completedInner_smul_right, completedInner_add_right, hpair]
  exact rc_half_double (B x v)

/-- For an actual odd source, averaging the test preserves its detector. -/
theorem oddPart_detector (x v : V)
    (hx : U x = completedNeg hw0 hw1 x) :
    B x (oddPart hw0 hw1 v) = B x v := by
  have hpair : B x (U v) = RCscale (-1) (B x v) := by
    rw [← completedInner_swap_balance hw0 hw1 x v, hx]
    exact completedInner_smul_left hw0 hw1 (-1) x v
  unfold oddPart
  rw [completedInner_smul_right, completedInner_sub_right, hpair]
  exact rc_half_sub_neg (B x v)

/-- Odd averaging of any test is orthogonal to the actual fixed unit. -/
theorem oddPart_vacuumComplement (v : V) :
    B (unitState hw0 hw1 width) (oddPart hw0 hw1 v) = RCzero := by
  have hpair : B (unitState hw0 hw1 width) (U v) =
      B (unitState hw0 hw1 width) v := by
    rw [← completedInner_swap_balance hw0 hw1 (unitState hw0 hw1 width) v,
      completedSwap_unit]
  unfold oddPart
  rw [completedInner_smul_right, completedInner_sub_right, hpair]
  refine Quotient.inductionOn (B (unitState hw0 hw1 width) v) ?_
  intro x
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.mul (.var 1)
        (.add (.var 0) (.neg (.var 0))))
      (.const 0) (by decide)
      (fun | 0 => x.approx n | _ => HalfPow.half)))

/-- The even average does not spoil an already centered test. -/
theorem evenPart_preserves_vacuumComplement (v : V)
    (hv : B (unitState hw0 hw1 width) v = RCzero) :
    B (unitState hw0 hw1 width) (evenPart hw0 hw1 v) = RCzero := by
  unfold evenPart
  rw [completedInner_smul_right, completedInner_add_right, hv,
    completedSwap_preserves_vacuumComplement hw0 hw1 v hv]
  rw [rc_zero_add]
  exact RCscale_RCzero HalfPow.half

end YMGap.Continuum.BF4WilsonAllNomeSpatialAxisSwapCompletion

#print axioms YMGap.Continuum.BF4WilsonAllNomeSpatialAxisSwapCompletion.completedSwap
#print axioms YMGap.Continuum.BF4WilsonAllNomeSpatialAxisSwapCompletion.completedSwap_embed
#print axioms YMGap.Continuum.BF4WilsonAllNomeSpatialAxisSwapCompletion.swap_cauchy_modulus
#print axioms YMGap.Continuum.BF4WilsonAllNomeSpatialAxisSwapCompletion.completedSwap_involutive
#print axioms YMGap.Continuum.BF4WilsonAllNomeSpatialAxisSwapCompletion.completedSwap_time
#print axioms YMGap.Continuum.BF4WilsonAllNomeSpatialAxisSwapCompletion.completedSwap_add
#print axioms YMGap.Continuum.BF4WilsonAllNomeSpatialAxisSwapCompletion.completedSwap_smul
#print axioms YMGap.Continuum.BF4WilsonAllNomeSpatialAxisSwapCompletion.completedSwap_sub
#print axioms YMGap.Continuum.BF4WilsonAllNomeSpatialAxisSwapCompletion.completedSwap_unit
#print axioms YMGap.Continuum.BF4WilsonAllNomeSpatialAxisSwapCompletion.completedSwap_zero
#print axioms YMGap.Continuum.BF4WilsonAllNomeSpatialAxisSwapCompletion.representativeInner_swap
#print axioms YMGap.Continuum.BF4WilsonAllNomeSpatialAxisSwapCompletion.completedInner_swap
#print axioms YMGap.Continuum.BF4WilsonAllNomeSpatialAxisSwapCompletion.completedInner_swap_balance
#print axioms YMGap.Continuum.BF4WilsonAllNomeSpatialAxisSwapCompletion.completedDist_swap
#print axioms YMGap.Continuum.BF4WilsonAllNomeSpatialAxisSwapCompletion.completedSwap_preserves_vacuumComplement
#print axioms YMGap.Continuum.BF4WilsonAllNomeSpatialAxisSwapCompletion.evenPart
#print axioms YMGap.Continuum.BF4WilsonAllNomeSpatialAxisSwapCompletion.oddPart
#print axioms YMGap.Continuum.BF4WilsonAllNomeSpatialAxisSwapCompletion.sector_norm_split
#print axioms YMGap.Continuum.BF4WilsonAllNomeSpatialAxisSwapCompletion.evenPart_norm_le
#print axioms YMGap.Continuum.BF4WilsonAllNomeSpatialAxisSwapCompletion.oddPart_norm_le
#print axioms YMGap.Continuum.BF4WilsonAllNomeSpatialAxisSwapCompletion.evenPart_time
#print axioms YMGap.Continuum.BF4WilsonAllNomeSpatialAxisSwapCompletion.oddPart_time
#print axioms YMGap.Continuum.BF4WilsonAllNomeSpatialAxisSwapCompletion.evenPart_detector
#print axioms YMGap.Continuum.BF4WilsonAllNomeSpatialAxisSwapCompletion.oddPart_detector
#print axioms YMGap.Continuum.BF4WilsonAllNomeSpatialAxisSwapCompletion.oddPart_vacuumComplement
#print axioms YMGap.Continuum.BF4WilsonAllNomeSpatialAxisSwapCompletion.evenPart_preserves_vacuumComplement
