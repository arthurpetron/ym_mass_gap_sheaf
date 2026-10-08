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
open YMGap.Continuum.BF4WilsonAllNomeDistance (completedDist)
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
