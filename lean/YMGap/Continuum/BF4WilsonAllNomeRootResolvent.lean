/-
# Actual normalized root resolvents on the original Wilson completion

For every fixed constructed root R and explicit 0 <= r < 1, construct
C_r=(1-r) sum_{n>=0} r^n R^n with represented geometric convergence.
The original norm bounds C_r, and its fixed-point equation is exact.
All representatives and moduli are computed, not selected from a quotient.

This is a bounded inverse prerequisite for a generator resolvent. Passing
through shrinking dyadic time, range-sector membership and the generator
equation are separate steps; no physical OS or scaling result is asserted.
-/

import YMGap.Continuum.BF4WilsonAllNomeRootResolventPartial
import YMGap.Continuum.BF4WilsonAllNomeLogOperator
import YMGap.Continuum.BF4WilsonAllNomeTimeAverages
import YMGap.Continuum.PositiveContractionResidual

namespace YMGap.Continuum.BF4WilsonAllNomeRootResolvent

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4WilsonAllNomeSeminorm (seminorm)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeLinear
open YMGap.Continuum.BF4WilsonAllNomeLinearLaws
open YMGap.Continuum.BF4WilsonAllNomeBilinearTime
open YMGap.Continuum.BF4WilsonAllNomeCompletedPairingContinuity
  (completedInner_sub_left completedInner_sub_right)
open YMGap.Continuum.BF4WilsonAllNomeCompletedRealScalar
open YMGap.Continuum.BF4WilsonAllNomeDistance
open YMGap.Continuum.BF4WilsonAllNomeCauchyRows
open YMGap.Continuum.BF4WilsonAllNomeRowPairingLimit
open YMGap.Continuum.BF4WilsonAllNomeLogOperator (pairing_limits_eq)
open YMGap.Continuum.BF4WilsonAllNomeNestedRootBasics
open YMGap.Continuum.BF4WilsonAllNomeNestedRootCompatibility
open YMGap.Continuum.BF4WilsonAllNomeDyadicRepresentatives
  (rootRepresentative rootRepresentative_pin)
open YMGap.Continuum.BF4WilsonAllNomeRootResolventPartial
open YMGap.Continuum.CRealSeminormPairingCompletion
  (normCeiling normCeiling_nonnegative completedInner_diagonal_le_normCeiling)
open YMGap.Continuum.PositiveContractionResidual (geometricCutoff geometric_bound)
open YMGap.Continuum.BF4ExactSlabPlaquetteCompletedApproximation (quarter quarter_pos)
open YMGap.Continuum.RCSignedPairBudget (scale_congr)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "D" => seminorm hw0 hw1 (width := width)
local notation "P" => distanceData hw0 hw1 (width := width)
local notation "PD" => pairingData hw0 hw1 (width := width)
local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "S" => completedSmul hw0 hw1
local notation "A" => completedAdd hw0 hw1
local notation "Sub" => completedSub hw0 hw1
local notation "dist" => completedDist hw0 hw1
local notation "R" => root hw0 hw1
local notation "Class" => Quotient.mk
  (CRealSeminormCompletion.SquaredSeminorm.completionSetoid
    (seminorm hw0 hw1 (width := width)))
local notation "Rq" q:arg => Quotient.mk crealSetoid (ofQ' q)

private theorem partial_symmetric (depth : Nat) (r : Q') (n : Nat) (x y : V) :
    B (rootPartial hw0 hw1 depth r n x) y =
      B x (rootPartial hw0 hw1 depth r n y) := by
  induction n generalizing x y with
  | zero =>
      exact (completedInner_zero_left hw0 hw1 y).trans
        (completedInner_zero_right hw0 hw1 x).symm
  | succ n ih =>
      change B (A (S (1-r) x) (S r (R depth (rootPartial hw0 hw1 depth r n x)))) y =
        B x (A (S (1-r) y) (S r (R depth (rootPartial hw0 hw1 depth r n y))))
      rw [completedInner_add_left, completedInner_add_right,
        completedInner_smul_left, completedInner_smul_left,
        completedInner_smul_right, completedInner_smul_right,
        root_symmetric, ih, partial_root_commute]

/-- The norm ceiling comes from the supplied original representative. -/
def seriesModulus (r : Q') (X : (D).Cauchy) (epsilon : Q') : Nat :=
  geometricCutoff r (normCeiling PD X) epsilon

private theorem ordered_small (depth : Nat) (r : Q')
    (hr0 : (0 : Q') ≤ r) (hr1 : r < (1 : Q'))
    (X : (D).Cauchy) (epsilon : Q') (he : (0 : Q') < epsilon)
    (m n : Nat) (hmn : m ≤ n) (hm : seriesModulus hw0 hw1 r X epsilon ≤ m) :
    RCle (dist (rootPartial hw0 hw1 depth r n (Class X))
      (rootPartial hw0 hw1 depth r m (Class X))) (Rq epsilon) := by
  have h := partial_tail_bound hw0 hw1 depth r hr0 hr1 m (n-m) (Class X)
  rw [Nat.add_sub_of_le hmn] at h
  have hp0 := Q'.pow_nonneg r hr0 m
  have hp1 := HKPos.pow_le_one hr0 (Q'.le_of_lt hr1) m
  have hsq : r^m*r^m ≤ r^m := Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ _ hp1 hp0)
    (Q'.le_of_eqv (Q'.one_mul_eqv _))
  have hcap := RCle_trans h (RCscale_mono
    (Q'.mul_nonneg _ _ hp0 hp0) (completedInner_diagonal_le_normCeiling PD X))
  have hs : RCscale (r^m*r^m) (Rq (normCeiling PD X)) =
      Rq ((r^m*r^m)*normCeiling PD X) :=
    Quotient.sound (CRealAlg.ofQ'_mul _ _).symm
  rw [hs] at hcap
  apply RCle_trans hcap
  exact leEv_le_ofQ'_of_approx_le (fun _ => Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ _ hsq (normCeiling_nonnegative PD X))
    (geometric_bound hr0 hr1 (normCeiling_nonnegative PD X) he m hm))

def seriesRows (depth : Nat) (r : Q')
    (hr0 : (0 : Q') ≤ r) (hr1 : r < (1 : Q')) (X : (D).Cauchy) :
    RepresentedCauchy hw0 hw1 (width := width) where
  row := fun n => partialRepresentative hw0 hw1 depth r n X
  modulus := seriesModulus hw0 hw1 r X
  isCauchy := by
    intro epsilon he m n hm hn
    change RCle (dist (Class (partialRepresentative hw0 hw1 depth r m X))
      (Class (partialRepresentative hw0 hw1 depth r n X))) _
    rw [partialRepresentative_pin, partialRepresentative_pin]
    rcases Nat.le_total m n with hmn | hnm
    · rw [completedDist_symm]
      exact ordered_small hw0 hw1 depth r hr0 hr1 X epsilon he m n hmn hm
    · exact ordered_small hw0 hw1 depth r hr0 hr1 X epsilon he n m hnm hn

theorem seriesRows_point (depth : Nat) (r : Q')
    (hr0 : (0 : Q') ≤ r) (hr1 : r < (1 : Q')) (X : (D).Cauchy) (n : Nat) :
    rowPoint hw0 hw1 (seriesRows hw0 hw1 depth r hr0 hr1 X) n =
      rootPartial hw0 hw1 depth r n (Class X) :=
  partialRepresentative_pin hw0 hw1 depth r n X

/-- The actual normalized Neumann limit on EVERY original completion class. -/
def resolvent (depth : Nat) (r : Q')
    (hr0 : (0 : Q') ≤ r) (hr1 : r < (1 : Q')) : V → V :=
  Quotient.lift (fun X => limit hw0 hw1 (seriesRows hw0 hw1 depth r hr0 hr1 X))
    (fun X Y h => by
      apply limit_independent hw0 hw1
      intro n
      rw [seriesRows_point, seriesRows_point, Quotient.sound h])

def convergenceModulus (depth : Nat) (r : Q')
    (hr0 : (0 : Q') ≤ r) (hr1 : r < (1 : Q')) (X : (D).Cauchy) (epsilon : Q') : Nat :=
  limitRate hw0 hw1 (seriesRows hw0 hw1 depth r hr0 hr1 X) epsilon

theorem resolvent_approximation (depth : Nat) (r : Q')
    (hr0 : (0 : Q') ≤ r) (hr1 : r < (1 : Q')) (X : (D).Cauchy)
    (epsilon : Q') (he : (0 : Q') < epsilon) (n : Nat)
    (hn : convergenceModulus hw0 hw1 depth r hr0 hr1 X epsilon ≤ n) :
    RCle (dist (rootPartial hw0 hw1 depth r n (Class X))
      (resolvent hw0 hw1 depth r hr0 hr1 (Class X))) (Rq epsilon) := by
  exact (seriesRows_point hw0 hw1 depth r hr0 hr1 X n) ▸
    limit_bound hw0 hw1 (seriesRows hw0 hw1 depth r hr0 hr1 X) epsilon he n hn

/-- A computed representative for subsequent dyadic diagonalization. -/
def outputRepresentative (depth : Nat) (r : Q')
    (hr0 : (0 : Q') ≤ r) (hr1 : r < (1 : Q')) (X : (D).Cauchy) : (D).Cauchy :=
  CRealSeminormCauchyRows.diagonalCauchy P (seriesRows hw0 hw1 depth r hr0 hr1 X)

theorem outputRepresentative_pin (depth : Nat) (r : Q')
    (hr0 : (0 : Q') ≤ r) (hr1 : r < (1 : Q')) (X : (D).Cauchy) :
    Class (outputRepresentative hw0 hw1 depth r hr0 hr1 X) =
      resolvent hw0 hw1 depth r hr0 hr1 (Class X) := rfl

theorem resolvent_norm_bound (depth : Nat) (r : Q')
    (hr0 : (0 : Q') ≤ r) (hr1 : r < (1 : Q')) (x : V) :
    RCle (B (resolvent hw0 hw1 depth r hr0 hr1 x)
      (resolvent hw0 hw1 depth r hr0 hr1 x)) (B x x) := by
  refine Quotient.inductionOn x ?_
  intro X
  apply rowLimit_norm_bound hw0 hw1
  intro n
  rw [seriesRows_point]
  exact partial_norm_bound hw0 hw1 depth r hr0 hr1 n (Class X)

theorem resolvent_symmetric (depth : Nat) (r : Q')
    (hr0 : (0 : Q') ≤ r) (hr1 : r < (1 : Q')) (x y : V) :
    B (resolvent hw0 hw1 depth r hr0 hr1 x) y =
      B x (resolvent hw0 hw1 depth r hr0 hr1 y) := by
  refine Quotient.inductionOn₂ x y ?_
  intro X Y
  have h := pairing_limits_eq hw0 hw1
    (seriesRows hw0 hw1 depth r hr0 hr1 X) (constantRows hw0 hw1 Y)
    (constantRows hw0 hw1 X) (seriesRows hw0 hw1 depth r hr0 hr1 Y) (fun n => by
      rw [seriesRows_point, constantRows_point, constantRows_point, seriesRows_point]
      exact partial_symmetric hw0 hw1 depth r n (Class X) (Class Y))
  rw [limit_constantRows, limit_constantRows] at h
  exact h

theorem resolvent_add (depth : Nat) (r : Q')
    (hr0 : (0 : Q') ≤ r) (hr1 : r < (1 : Q')) (x y : V) :
    resolvent hw0 hw1 depth r hr0 hr1 (A x y) =
      A (resolvent hw0 hw1 depth r hr0 hr1 x) (resolvent hw0 hw1 depth r hr0 hr1 y) := by
  apply completed_eq_of_pairings hw0 hw1
  intro z
  rw [resolvent_symmetric, completedInner_add_left, completedInner_add_left,
    resolvent_symmetric, resolvent_symmetric]

theorem resolvent_smul (depth : Nat) (r : Q')
    (hr0 : (0 : Q') ≤ r) (hr1 : r < (1 : Q')) (c : Q') (x : V) :
    resolvent hw0 hw1 depth r hr0 hr1 (S c x) =
      S c (resolvent hw0 hw1 depth r hr0 hr1 x) := by
  apply completed_eq_of_pairings hw0 hw1
  intro z
  rw [resolvent_symmetric, completedInner_smul_left, completedInner_smul_left,
    resolvent_symmetric]

theorem resolvent_sub (depth : Nat) (r : Q')
    (hr0 : (0 : Q') ≤ r) (hr1 : r < (1 : Q')) (x y : V) :
    resolvent hw0 hw1 depth r hr0 hr1 (Sub x y) =
      Sub (resolvent hw0 hw1 depth r hr0 hr1 x) (resolvent hw0 hw1 depth r hr0 hr1 y) := by
  unfold completedSub completedNeg
  rw [resolvent_add, resolvent_smul]

theorem resolvent_root_commute (depth : Nat) (r : Q')
    (hr0 : (0 : Q') ≤ r) (hr1 : r < (1 : Q')) (x : V) :
    resolvent hw0 hw1 depth r hr0 hr1 (R depth x) =
      R depth (resolvent hw0 hw1 depth r hr0 hr1 x) := by
  refine Quotient.inductionOn x ?_
  intro X
  apply completed_eq_of_pairings hw0 hw1
  intro y
  refine Quotient.inductionOn y ?_
  intro Y
  have h := pairing_limits_eq hw0 hw1
    (seriesRows hw0 hw1 depth r hr0 hr1 (rootRepresentative hw0 hw1 depth X))
    (constantRows hw0 hw1 Y)
    (seriesRows hw0 hw1 depth r hr0 hr1 X)
    (constantRows hw0 hw1 (rootRepresentative hw0 hw1 depth Y)) (fun n => by
      rw [seriesRows_point, constantRows_point, seriesRows_point, constantRows_point,
        rootRepresentative_pin, rootRepresentative_pin, partial_root_commute, root_symmetric])
  rw [limit_constantRows, limit_constantRows] at h
  change B (resolvent hw0 hw1 depth r hr0 hr1
      (Class (rootRepresentative hw0 hw1 depth X))) (Class Y) =
    B (resolvent hw0 hw1 depth r hr0 hr1 (Class X))
      (Class (rootRepresentative hw0 hw1 depth Y)) at h
  rw [rootRepresentative_pin, rootRepresentative_pin] at h
  exact h.trans (root_symmetric hw0 hw1 depth _ _).symm

private theorem affine_sub (depth : Nat) (r : Q') (a x y : V) :
    Sub (A a (S r (R depth x))) (A a (S r (R depth y))) =
      S r (R depth (Sub x y)) := by
  apply completed_eq_of_pairings hw0 hw1
  intro z
  rw [root_sub, completedInner_sub_left, completedInner_add_left,
    completedInner_add_left, completedInner_smul_left, completedInner_smul_left,
    completedInner_smul_left, completedInner_sub_left]
  generalize B a z = b, B (R depth x) z = c, B (R depth y) z = d
  refine Quotient.inductionOn₃ b c d ?_
  intro b c d
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    RingNormaliser.poly_identity_of_normal_eq
      (.add (.add (.var 0) (.mul (.var 3) (.var 1)))
        (.neg (.add (.var 0) (.mul (.var 3) (.var 2)))))
      (.mul (.var 3) (.add (.var 1) (.neg (.var 2)))) (by decide)
      (fun | 0 => b.approx n | 1 => c.approx n | 2 => d.approx n | _ => r)))

private theorem affine_distance (depth : Nat) (r : Q')
    (hr0 : (0 : Q') ≤ r) (hr1 : r < (1 : Q')) (a x y : V) :
    RCle (dist (A a (S r (R depth x))) (A a (S r (R depth y)))) (dist x y) := by
  unfold completedDist
  rw [affine_sub, completedInner_smul_left, completedInner_smul_right, RCscale_RCscale]
  have hsq : r*r ≤ 1 := Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg (Q'.le_of_lt hr1) (Q'.le_of_lt hr1) Q'.zero_le_one hr0)
    (by decide)
  have h := RCle_trans (RCscale_mono (Q'.mul_nonneg _ _ hr0 hr0)
    (root_norm_bound hw0 hw1 depth (Sub x y)))
    (RCscale_scalar_mono hsq (completedInner_nonnegative hw0 hw1 (Sub x y)))
  rwa [RCscale_one] at h

/-- Exact fixed-point equation for the constructed limit, not an assumed inverse. -/
theorem resolvent_equation (depth : Nat) (r : Q')
    (hr0 : (0 : Q') ≤ r) (hr1 : r < (1 : Q')) (x : V) :
    resolvent hw0 hw1 depth r hr0 hr1 x =
      A (S (1-r) x) (S r (R depth (resolvent hw0 hw1 depth r hr0 hr1 x))) := by
  refine Quotient.inductionOn x ?_
  intro X
  apply CRealSeminormCauchyRows.completed_eq_of_small P
  intro epsilon he
  let delta := quarter epsilon
  have hd : (0 : Q') < delta := quarter_pos he
  let n := convergenceModulus hw0 hw1 depth r hr0 hr1 X delta
  apply CRealSeminormCompletedApproximation.completedDist_two_segment P
    _ (rootPartial hw0 hw1 depth r (n+1) (Class X)) _ epsilon
  · change RCle (dist (resolvent hw0 hw1 depth r hr0 hr1 (Class X))
      (rootPartial hw0 hw1 depth r (n+1) (Class X))) (Rq delta)
    rw [completedDist_symm]
    exact resolvent_approximation hw0 hw1 depth r hr0 hr1 X delta hd (n+1) (Nat.le_succ n)
  · exact RCle_trans (affine_distance hw0 hw1 depth r hr0 hr1 _ _ _)
      (resolvent_approximation hw0 hw1 depth r hr0 hr1 X delta hd n (Nat.le_refl n))

/-- The bounded operator whose inverse is being constructed. -/
def defect (depth : Nat) (r : Q') (x : V) : V := Sub x (S r (R depth x))

theorem defect_smul (depth : Nat) (r c : Q') (x : V) :
    defect hw0 hw1 depth r (S c x) = S c (defect hw0 hw1 depth r x) := by
  unfold defect
  rw [root_smul, BF4WilsonAllNomeTimeAverages.smul_sub,
    completedSmul_mul, completedSmul_mul,
    completedSmul_congr hw0 hw1 (Q'.mul_comm_eqv r c)]

private theorem add_sub_cancel (x y : V) : Sub (A x y) y = x := by
  unfold completedSub
  rw [completedAdd_assoc, completedAdd_comm hw0 hw1 y (completedNeg hw0 hw1 y),
    completedNeg_add, completedAdd_zero]

theorem resolvent_right_normalized (depth : Nat) (r : Q')
    (hr0 : (0 : Q') ≤ r) (hr1 : r < (1 : Q')) (x : V) :
    defect hw0 hw1 depth r (resolvent hw0 hw1 depth r hr0 hr1 x) = S (1-r) x := by
  exact (congrArg (fun z => Sub z
      (S r (R depth (resolvent hw0 hw1 depth r hr0 hr1 x))))
    (resolvent_equation hw0 hw1 depth r hr0 hr1 x)).trans (add_sub_cancel hw0 hw1 _ _)

theorem resolvent_left_normalized (depth : Nat) (r : Q')
    (hr0 : (0 : Q') ≤ r) (hr1 : r < (1 : Q')) (x : V) :
    resolvent hw0 hw1 depth r hr0 hr1 (defect hw0 hw1 depth r x) = S (1-r) x := by
  unfold defect
  rw [resolvent_sub, resolvent_smul, resolvent_root_commute]
  exact resolvent_right_normalized hw0 hw1 depth r hr0 hr1 x

/-- Explicit operator-norm ceiling for the unnormalized inverse. -/
def inverseBound (r : Q') (hr1 : r < (1 : Q')) : Q' :=
  Q'.recipPos (1-r) (HKPos.one_sub_pos hr1)

theorem inverseBound_positive (r : Q') (hr1 : r < (1 : Q')) :
    (0 : Q') < inverseBound r hr1 := Q'.recipPos_pos _ _

private theorem inverseBound_cancel (r : Q') (hr1 : r < (1 : Q')) :
    Q'.eqv (inverseBound r hr1 * (1-r)) 1 :=
  Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _)
    (Q'.mul_recipPos_eqv (1-r) (HKPos.one_sub_pos hr1))

/-- The actual two-sided inverse of I-rR, retaining the original carrier. -/
def inverse (depth : Nat) (r : Q')
    (hr0 : (0 : Q') ≤ r) (hr1 : r < (1 : Q')) (x : V) : V :=
  S (inverseBound r hr1) (resolvent hw0 hw1 depth r hr0 hr1 x)

def inverseRepresentative (depth : Nat) (r : Q')
    (hr0 : (0 : Q') ≤ r) (hr1 : r < (1 : Q')) (X : (D).Cauchy) : (D).Cauchy :=
  (scalarContinuous hw0 hw1 (inverseBound r hr1)).mapCauchy
    (outputRepresentative hw0 hw1 depth r hr0 hr1 X)

theorem inverseRepresentative_pin (depth : Nat) (r : Q')
    (hr0 : (0 : Q') ≤ r) (hr1 : r < (1 : Q')) (X : (D).Cauchy) :
    Class (inverseRepresentative hw0 hw1 depth r hr0 hr1 X) =
      inverse hw0 hw1 depth r hr0 hr1 (Class X) := by
  change S (inverseBound r hr1) (Class (outputRepresentative hw0 hw1 depth r hr0 hr1 X)) = _
  rw [outputRepresentative_pin]
  rfl

theorem inverse_right (depth : Nat) (r : Q')
    (hr0 : (0 : Q') ≤ r) (hr1 : r < (1 : Q')) (x : V) :
    defect hw0 hw1 depth r (inverse hw0 hw1 depth r hr0 hr1 x) = x := by
  unfold inverse
  rw [defect_smul, resolvent_right_normalized, completedSmul_mul,
    completedSmul_congr hw0 hw1 (inverseBound_cancel r hr1), completedSmul_one]

theorem inverse_left (depth : Nat) (r : Q')
    (hr0 : (0 : Q') ≤ r) (hr1 : r < (1 : Q')) (x : V) :
    inverse hw0 hw1 depth r hr0 hr1 (defect hw0 hw1 depth r x) = x := by
  unfold inverse
  rw [resolvent_left_normalized, completedSmul_mul,
    completedSmul_congr hw0 hw1 (inverseBound_cancel r hr1), completedSmul_one]

theorem inverse_norm_bound (depth : Nat) (r : Q')
    (hr0 : (0 : Q') ≤ r) (hr1 : r < (1 : Q')) (x : V) :
    RCle (B (inverse hw0 hw1 depth r hr0 hr1 x)
      (inverse hw0 hw1 depth r hr0 hr1 x))
      (RCscale (inverseBound r hr1 * inverseBound r hr1) (B x x)) := by
  unfold inverse
  rw [completedInner_smul_left, completedInner_smul_right, RCscale_RCscale]
  exact RCscale_mono (Q'.mul_nonneg _ _ (Q'.le_of_lt (inverseBound_positive r hr1))
    (Q'.le_of_lt (inverseBound_positive r hr1)))
    (resolvent_norm_bound hw0 hw1 depth r hr0 hr1 x)

theorem inverse_unique (depth : Nat) (r : Q')
    (hr0 : (0 : Q') ≤ r) (hr1 : r < (1 : Q')) (x y : V)
    (hy : defect hw0 hw1 depth r y = x) :
    y = inverse hw0 hw1 depth r hr0 hr1 x := by
  rw [← hy, inverse_left]

/-- A commuting original map commutes with the constructed inverse. This
will compare adjacent root depths without assuming a functional calculus. -/
theorem inverse_commutes_of_defect_commutes (depth : Nat) (r : Q')
    (hr0 : (0 : Q') ≤ r) (hr1 : r < (1 : Q')) (L : V → V)
    (hL : ∀ x, defect hw0 hw1 depth r (L x) = L (defect hw0 hw1 depth r x))
    (x : V) :
    inverse hw0 hw1 depth r hr0 hr1 (L x) =
      L (inverse hw0 hw1 depth r hr0 hr1 x) := by
  apply Eq.symm
  apply inverse_unique hw0 hw1 depth r hr0 hr1
  rw [hL, inverse_right]

#print axioms seriesRows
#print axioms seriesRows_point
#print axioms resolvent
#print axioms convergenceModulus
#print axioms resolvent_approximation
#print axioms outputRepresentative
#print axioms outputRepresentative_pin
#print axioms resolvent_norm_bound
#print axioms resolvent_symmetric
#print axioms resolvent_add
#print axioms resolvent_smul
#print axioms resolvent_sub
#print axioms resolvent_root_commute
#print axioms resolvent_equation
#print axioms resolvent_right_normalized
#print axioms resolvent_left_normalized
#print axioms defect_smul
#print axioms inverseBound_positive
#print axioms inverse
#print axioms inverseRepresentative
#print axioms inverseRepresentative_pin
#print axioms inverse_right
#print axioms inverse_left
#print axioms inverse_norm_bound
#print axioms inverse_unique
#print axioms inverse_commutes_of_defect_commutes

end YMGap.Continuum.BF4WilsonAllNomeRootResolvent
