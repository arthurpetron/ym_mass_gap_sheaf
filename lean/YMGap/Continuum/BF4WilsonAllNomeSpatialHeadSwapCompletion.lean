/-
# The second spatial transposition on the SAME original Wilson completion

The concrete x0/x1 source swap preserves the actual intrinsic reflected form
and time advance. Its exact signed algebra therefore supplies a nonexpansive
map on the existing seminorm, with each supplied Cauchy modulus retained.
The descended operator is involutive, preserves the existing pairing and
distance, fixes the original unit, and commutes with the actual completed
physical time. No symmetry premise, new carrier or pairing is introduced.

This is a fixed-width, fixed-nome finite spatial symmetry. Completed cubic
composition, continuous Euclidean covariance, changing-family control and
the physical continuum Hamiltonian gap remain separate obligations.
-/

import YMGap.Continuum.BF4WilsonAllNomeSpatialHeadSwapForm
import YMGap.Continuum.BF4WilsonAllNomeDistance

namespace YMGap.Continuum.BF4WilsonAllNomeSpatialHeadSwapCompletion

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabSpatialHeadSwapGeometry
open YMGap.Continuum.BF4ExactSlabSpatialHeadSwapWilsonLoop
open YMGap.Continuum.BF4ExactSlabSpatialHeadSwapWilsonWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe (SourceLoop)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow (WindowExpression)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm
  (IntrinsicExpression chart unit)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicSeminorm
  (sum difference)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicAlgebra
  (smul zero)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPhysicalTime (advance)
open YMGap.Continuum.BF4WilsonAllNomeSeminorm (seminorm distSq distSq_refl)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4WilsonAllNomeLinear
open YMGap.Continuum.BF4WilsonAllNomeDistance (completedDist)
open YMGap.Continuum.BF4WilsonAllNomeSpatialHeadSwapForm
open YMGap.Continuum.CRealSeminormCompletion.SquaredSeminorm.NonexpansiveSemigroup
  (closeOfPointwiseNull)

private theorem sourceLoop_ext {width : Nat} (x y : SourceLoop width)
    (hs : x.start = y.start) (he : x.edges = y.edges) : x = y := by
  cases x
  cases y
  cases hs
  cases he
  rfl

theorem swapSourceLoop_involutive {width : Nat} (loop : SourceLoop width) :
    swapSourceLoop (swapSourceLoop loop) = loop := by
  apply sourceLoop_ext
  · exact swapVertex_involutive loop.start
  · change (loop.edges.map swapEntry).map swapEntry = loop.edges
    simp only [List.map_map, Function.comp_def, swapEntry_involutive]
    exact List.map_id _

theorem swapExpression_involutive {width : Nat} :
    ∀ e : WindowExpression width, swapExpression (swapExpression e) = e
  | .one => rfl
  | .loop offset value spin => by
      change WindowExpression.loop offset (swapSourceLoop (swapSourceLoop value)) spin =
        WindowExpression.loop offset value spin
      rw [swapSourceLoop_involutive]
  | .add e f => by
      change WindowExpression.add (swapExpression (swapExpression e))
        (swapExpression (swapExpression f)) = WindowExpression.add e f
      rw [swapExpression_involutive e, swapExpression_involutive f]
  | .mul e f => by
      change WindowExpression.mul (swapExpression (swapExpression e))
        (swapExpression (swapExpression f)) = WindowExpression.mul e f
      rw [swapExpression_involutive e, swapExpression_involutive f]
  | .smul c e => by
      change WindowExpression.smul c (swapExpression (swapExpression e)) =
        WindowExpression.smul c e
      rw [swapExpression_involutive e]

private theorem intrinsic_ext {width : Nat} (x y : IntrinsicExpression width)
    (hr : x.radius = y.radius) (he : x.expression = y.expression) : x = y := by
  cases x
  cases y
  cases hr
  cases he
  rfl

theorem swapIntrinsic_involutive {width : Nat} (x : IntrinsicExpression width) :
    swapIntrinsic (swapIntrinsic x) = x := by
  apply intrinsic_ext
  · rfl
  · exact swapExpression_involutive x.expression

theorem swapIntrinsic_unit (width : Nat) :
    swapIntrinsic (unit width) = unit width := rfl

/-- Both operands retain their actual common-radius temporal charts. -/
theorem swapIntrinsic_sum {width : Nat} (x y : IntrinsicExpression width) :
    swapIntrinsic (sum x y) = sum (swapIntrinsic x) (swapIntrinsic y) := by
  apply intrinsic_ext
  · rfl
  · change WindowExpression.add
      (swapExpression (chart (max x.radius y.radius) x))
      (swapExpression (chart (max x.radius y.radius) y)) =
      WindowExpression.add (chart (max x.radius y.radius) (swapIntrinsic x))
        (chart (max x.radius y.radius) (swapIntrinsic y))
    rw [swap_chart, swap_chart]

theorem swapIntrinsic_difference {width : Nat} (x y : IntrinsicExpression width) :
    swapIntrinsic (difference x y) =
      difference (swapIntrinsic x) (swapIntrinsic y) := by
  apply intrinsic_ext
  · rfl
  · change WindowExpression.add
      (swapExpression (chart (max x.radius y.radius) x))
      (WindowExpression.smul (-1) (swapExpression (chart (max x.radius y.radius) y))) =
      WindowExpression.add (chart (max x.radius y.radius) (swapIntrinsic x))
        (WindowExpression.smul (-1) (chart (max x.radius y.radius) (swapIntrinsic y)))
    rw [swap_chart, swap_chart]

theorem swapIntrinsic_smul {width : Nat} (c : Q') (x : IntrinsicExpression width) :
    swapIntrinsic (smul c x) = smul c (swapIntrinsic x) := rfl

theorem swapIntrinsic_zero (width : Nat) :
    swapIntrinsic (zero width) = zero width := rfl

/-- Equality in the existing all-nome source seminorm. -/
theorem distSq_swap {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width : Nat} (x y : IntrinsicExpression width) :
    Equiv (distSq hw0 hw1 (swapIntrinsic x) (swapIntrinsic y))
      (distSq hw0 hw1 x y) := by
  unfold distSq
  simpa only [swapIntrinsic_difference] using
    intrinsicForm_swap hw0 hw1 (difference x y) (difference x y)

/-- The proved SAME-form identity supplies contraction data. -/
def swapNonexpansive {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width : Nat} : (seminorm hw0 hw1 (width := width)).Nonexpansive where
  toFun := swapIntrinsic
  contraction := fun x y => leEv_of_equiv (distSq_swap hw0 hw1 x y)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "D" => seminorm hw0 hw1 (width := width)
local notation "PD" => pairingData hw0 hw1 (width := width)
local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "S" => swapNonexpansive hw0 hw1 (width := width)
local notation "T" => completedTime hw0 hw1
local notation "R" => CRealSeminormPairingCompletion.representativeInner PD

/-- The existing null/Cauchy quotient descent, on the ORIGINAL carrier. -/
def completedSwap : V → V := (S).completionMap

local notation "U" => completedSwap hw0 hw1

theorem completedSwap_embed (x : IntrinsicExpression width) :
    U (embed hw0 hw1 x) = embed hw0 hw1 (swapIntrinsic x) := rfl

/-- The supplied modulus is retained verbatim. -/
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

/-- Physical time is the existing x3 advance and completed semigroup. -/
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

/-- Preserve the already selected mixed pairing limit and its convergence pins. -/
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

theorem completedInner_swap_balance (x y : V) : B (U x) y = B x (U y) := by
  have h := completedInner_swap hw0 hw1 x (U y)
  rw [completedSwap_involutive] at h
  exact h

theorem completedDist_swap (x y : V) :
    completedDist hw0 hw1 (U x) (U y) = completedDist hw0 hw1 x y := by
  unfold completedDist
  rw [← completedSwap_sub, completedInner_swap]

theorem completedSwap_preserves_vacuumComplement (x : V)
    (hx : B (unitState hw0 hw1 width) x = RCzero) :
    B (unitState hw0 hw1 width) (U x) = RCzero := by
  rw [← completedInner_swap_balance, completedSwap_unit]
  exact hx

end YMGap.Continuum.BF4WilsonAllNomeSpatialHeadSwapCompletion

#print axioms YMGap.Continuum.BF4WilsonAllNomeSpatialHeadSwapCompletion.swapSourceLoop_involutive
#print axioms YMGap.Continuum.BF4WilsonAllNomeSpatialHeadSwapCompletion.swapExpression_involutive
#print axioms YMGap.Continuum.BF4WilsonAllNomeSpatialHeadSwapCompletion.swapIntrinsic_involutive
#print axioms YMGap.Continuum.BF4WilsonAllNomeSpatialHeadSwapCompletion.swapIntrinsic_unit
#print axioms YMGap.Continuum.BF4WilsonAllNomeSpatialHeadSwapCompletion.swapIntrinsic_sum
#print axioms YMGap.Continuum.BF4WilsonAllNomeSpatialHeadSwapCompletion.swapIntrinsic_difference
#print axioms YMGap.Continuum.BF4WilsonAllNomeSpatialHeadSwapCompletion.swapIntrinsic_smul
#print axioms YMGap.Continuum.BF4WilsonAllNomeSpatialHeadSwapCompletion.swapIntrinsic_zero
#print axioms YMGap.Continuum.BF4WilsonAllNomeSpatialHeadSwapCompletion.distSq_swap
#print axioms YMGap.Continuum.BF4WilsonAllNomeSpatialHeadSwapCompletion.swapNonexpansive
#print axioms YMGap.Continuum.BF4WilsonAllNomeSpatialHeadSwapCompletion.completedSwap
#print axioms YMGap.Continuum.BF4WilsonAllNomeSpatialHeadSwapCompletion.completedSwap_embed
#print axioms YMGap.Continuum.BF4WilsonAllNomeSpatialHeadSwapCompletion.swap_cauchy_modulus
#print axioms YMGap.Continuum.BF4WilsonAllNomeSpatialHeadSwapCompletion.completedSwap_involutive
#print axioms YMGap.Continuum.BF4WilsonAllNomeSpatialHeadSwapCompletion.completedSwap_time
#print axioms YMGap.Continuum.BF4WilsonAllNomeSpatialHeadSwapCompletion.completedSwap_add
#print axioms YMGap.Continuum.BF4WilsonAllNomeSpatialHeadSwapCompletion.completedSwap_smul
#print axioms YMGap.Continuum.BF4WilsonAllNomeSpatialHeadSwapCompletion.completedSwap_sub
#print axioms YMGap.Continuum.BF4WilsonAllNomeSpatialHeadSwapCompletion.completedSwap_unit
#print axioms YMGap.Continuum.BF4WilsonAllNomeSpatialHeadSwapCompletion.completedSwap_zero
#print axioms YMGap.Continuum.BF4WilsonAllNomeSpatialHeadSwapCompletion.representativeInner_swap
#print axioms YMGap.Continuum.BF4WilsonAllNomeSpatialHeadSwapCompletion.completedInner_swap
#print axioms YMGap.Continuum.BF4WilsonAllNomeSpatialHeadSwapCompletion.completedInner_swap_balance
#print axioms YMGap.Continuum.BF4WilsonAllNomeSpatialHeadSwapCompletion.completedDist_swap
#print axioms YMGap.Continuum.BF4WilsonAllNomeSpatialHeadSwapCompletion.completedSwap_preserves_vacuumComplement
