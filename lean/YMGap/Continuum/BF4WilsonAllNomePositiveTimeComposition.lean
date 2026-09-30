/-
Positive-time addition on the original all-nome Wilson completion. The summed
dyadic samples have an explicit original-carrier Cauchy modulus. Their limit
is the already constructed action at the summed time, and the finite dyadic
pairing law passes to that limit. No legacy completion is used.
-/

import YMGap.Continuum.PositiveRealDyadicTimeAddition
import YMGap.Continuum.BF4WilsonAllNomePositiveTimeLaws
import YMGap.Continuum.BF4WilsonAllNomeLogOperator
import YMGap.Continuum.BF4WilsonAllNomeCompletedRealScalar

namespace YMGap.Continuum.BF4WilsonAllNomePositiveTimeComposition

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Constructive.DyadicTimeRationals (value upper upper_error)
open YMGap.Continuum.PositiveRealDyadicTimeData
open YMGap.Continuum.PositiveRealDyadicTimeAddition
open YMGap.Continuum.BF4WilsonAllNomeSeminorm (seminorm)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeDistance
open YMGap.Continuum.BF4WilsonAllNomeCauchyRows
open YMGap.Continuum.BF4WilsonAllNomeRowPairingLimit
  (constantRows constantRows_point limit_constantRows)
open YMGap.Continuum.BF4WilsonAllNomeLogOperator (pairing_limits_eq)
open YMGap.Continuum.BF4WilsonAllNomePositiveTimeAction
open YMGap.Continuum.BF4WilsonAllNomePositiveTimeLaws (positiveAction_symmetric)
open YMGap.Continuum.BF4WilsonAllNomeDyadicContinuity (rangeModulus scaled_norm_small)
open YMGap.Continuum.BF4WilsonAllNomeDyadicRepresentatives (meshRepresentative meshRepresentative_pin)
open YMGap.Continuum.BF4ExactSlabPlaquetteCompletedApproximation (quarter quarter_pos)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "PD" => seminorm hw0 hw1 (width := width)
local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "d" => completedDist hw0 hw1
local notation "Class" => Quotient.mk
  (CRealSeminormCompletion.SquaredSeminorm.completionSetoid
    (seminorm hw0 hw1 (width := width)))
local notation "rat" q:arg => Quotient.mk crealSetoid (ofQ' q)

def sumRowModulus (D E : PositiveTime) (X : (PD).Cauchy) (epsilon : Q') : Nat :=
  sumModulus D E (timeTolerance hw0 hw1 (sumTime D E) X epsilon)

theorem sum_action_cauchy (D E : PositiveTime) (X : (PD).Cauchy) (epsilon : Q')
    (he : (0 : Q') < epsilon) (m n : Nat)
    (hm : sumRowModulus hw0 hw1 D E X epsilon ≤ m)
    (hn : sumRowModulus hw0 hw1 D E X epsilon ≤ n) :
    RCle (d (BF4WilsonAllNomeDyadicSemigroup.action hw0 hw1
      (NonnegativeDyadicTime.embed (sumMesh D E m)) (Class X))
      (BF4WilsonAllNomeDyadicSemigroup.action hw0 hw1
        (NonnegativeDyadicTime.embed (sumMesh D E n)) (Class X))) (rat epsilon) := by
  have h := sumMesh_cauchy D E _
    (timeTolerance_positive hw0 hw1 (sumTime D E) X epsilon) m n hm hn
  exact RCle_trans (mesh_close_bound hw0 hw1 _ _
    (rangeModulus hw0 hw1 X epsilon) (D.floor+E.floor)
    (sumMesh_lower D E m) (sumMesh_lower D E n) h.1 h.2 (Class X))
    (scaled_norm_small hw0 hw1 X epsilon he _ (Nat.le_refl _))

def sumRows (D E : PositiveTime) (X : (PD).Cauchy) :
    RepresentedCauchy hw0 hw1 (width := width) where
  row := fun n => meshRepresentative hw0 hw1 (sumMesh D E n).depth (sumMesh D E n).steps X
  modulus := sumRowModulus hw0 hw1 D E X
  isCauchy := by
    intro epsilon he m n hm hn
    change RCle (d
      (Class (meshRepresentative hw0 hw1 (sumMesh D E m).depth (sumMesh D E m).steps X))
      (Class (meshRepresentative hw0 hw1 (sumMesh D E n).depth (sumMesh D E n).steps X))) _
    rw [meshRepresentative_pin, meshRepresentative_pin]
    exact sum_action_cauchy hw0 hw1 D E X epsilon he m n hm hn

theorem sumRows_pin (D E : PositiveTime) (X : (PD).Cauchy) (n : Nat) :
    rowPoint hw0 hw1 (sumRows hw0 hw1 D E X) n =
      BF4WilsonAllNomeDyadicSemigroup.action hw0 hw1
        (NonnegativeDyadicTime.embed (sumMesh D E n)) (Class X) :=
  meshRepresentative_pin hw0 hw1 (sumMesh D E n).depth (sumMesh D E n).steps X

def sumComparisonModulus (D E : PositiveTime) (X : (PD).Cauchy) (epsilon : Q') : Nat :=
  (timeTolerance hw0 hw1 (sumTime D E) X epsilon).den

theorem sum_rows_close (D E : PositiveTime) (X : (PD).Cauchy) (epsilon : Q')
    (he : (0 : Q') < epsilon) (n : Nat)
    (hn : sumComparisonModulus hw0 hw1 D E X epsilon ≤ n) :
    RCle (d (rowPoint hw0 hw1 (timeRows hw0 hw1 (sumTime D E) X) n)
      (rowPoint hw0 hw1 (sumRows hw0 hw1 D E X) n)) (rat epsilon) := by
  let k := rangeModulus hw0 hw1 X epsilon
  let delta := timeTolerance hw0 hw1 (sumTime D E) X epsilon
  have hd : (0 : Q') < delta := timeTolerance_positive hw0 hw1 (sumTime D E) X epsilon
  have herr : HalfPow.half^n ≤ delta :=
    Q'.le_trans' _ _ _ (HalfPow.pow_half_le_invSucc n)
      (Q'.le_trans' _ _ _ (ExpNeg.invSucc_le_of_le hn)
        (HalfPow.invSucc_den_le delta hd))
  have hsample := Q'.le_trans' _ _ _
    (Q'.le_of_lt (sum_floor_positive D E)) (sum_lower D E n)
  have hu := upper_error (sumSample D E n) hsample n
  have hleft : value (upper (sumSample D E n) n) ≤ value (sumMesh D E n) + delta :=
    Q'.le_trans' _ _ _ hu.2 (Q'.le_trans' _ _ _
      (Q'.add_le_add_left _ _ _ herr)
      (Q'.add_le_add_right _ _ _ (Q'.ge_of_eqv (sumMesh_value D E n))))
  have hright : value (sumMesh D E n) ≤ value (upper (sumSample D E n) n) + delta :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (sumMesh_value D E n))
      (Q'.le_trans' _ _ _ hu.1
        (Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt hd)))
  have hp : D.floor+E.floor ≤ value (upper (sumSample D E n) n) :=
    Q'.le_trans' _ _ _ (sum_lower D E n) hu.1
  have h := RCle_trans (mesh_close_bound hw0 hw1
      (upper (sumSample D E n) n) (sumMesh D E n) k
      (D.floor+E.floor) hp (sumMesh_lower D E n) hleft hright (Class X))
    (scaled_norm_small hw0 hw1 X epsilon he k (Nat.le_refl _))
  rw [timeRows_pin, sumRows_pin]
  unfold approximation
  rw [sumTime_sample]
  exact h

private theorem rowLimits_eq_of_close
    (R S : RepresentedCauchy hw0 hw1 (width := width)) (rate : Q' → Nat)
    (h : ∀ epsilon : Q', (0 : Q') < epsilon → ∀ n, rate epsilon ≤ n →
      RCle (d (rowPoint hw0 hw1 R n) (rowPoint hw0 hw1 S n)) (rat epsilon)) :
    limit hw0 hw1 R = limit hw0 hw1 S := by
  apply CRealSeminormCauchyRows.completed_eq_of_small
    (distanceData hw0 hw1 (width := width))
  intro epsilon he
  let delta := quarter (quarter epsilon)
  have hd : (0 : Q') < delta := quarter_pos (quarter_pos he)
  let n := max (max (limitRate hw0 hw1 R delta) (limitRate hw0 hw1 S delta)) (rate delta)
  have hR := limit_bound hw0 hw1 R delta hd n
    (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _))
  have hS := limit_bound hw0 hw1 S delta hd n
    (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _))
  rw [completedDist_symm] at hR
  exact CRealSeminormCompletedApproximation.completedDist_three_segment
    (distanceData hw0 hw1 (width := width))
    (limit hw0 hw1 R) (rowPoint hw0 hw1 R n)
    (rowPoint hw0 hw1 S n) (limit hw0 hw1 S) epsilon he
    hR (h delta hd n (Nat.le_max_right _ _)) hS

theorem sumRows_limit (D E : PositiveTime) (X : (PD).Cauchy) :
    limit hw0 hw1 (sumRows hw0 hw1 D E X) =
      positiveAction hw0 hw1 (sumTime D E) (Class X) := by
  rw [positiveAction_pin hw0 hw1 (sumTime D E) X]
  exact (rowLimits_eq_of_close hw0 hw1
    (timeRows hw0 hw1 (sumTime D E) X) (sumRows hw0 hw1 D E X)
    (sumComparisonModulus hw0 hw1 D E X) (sum_rows_close hw0 hw1 D E X)).symm

theorem sumRows_pairing (D E : PositiveTime) (X Y : (PD).Cauchy) (n : Nat) :
    B (rowPoint hw0 hw1 (sumRows hw0 hw1 D E X) n) (Class Y) =
      B (rowPoint hw0 hw1 (timeRows hw0 hw1 E X) n)
        (rowPoint hw0 hw1 (timeRows hw0 hw1 D Y) n) := by
  rw [sumRows_pin, timeRows_pin, timeRows_pin]
  change B (BF4WilsonAllNomeDyadicSemigroup.action hw0 hw1
    (NonnegativeDyadicTime.embed (NonnegativeDyadicTime.addMesh
      (approximation D n) (approximation E n))) (Class X)) (Class Y) = _
  rw [← NonnegativeDyadicTime.add_embed]
  rw [BF4WilsonAllNomeDyadicSemigroup.action_add hw0 hw1]
  exact BF4WilsonAllNomeDyadicSemigroup.action_symmetric hw0 hw1
    (NonnegativeDyadicTime.embed (approximation D n))
    (BF4WilsonAllNomeDyadicSemigroup.action hw0 hw1
      (NonnegativeDyadicTime.embed (approximation E n)) (Class X)) (Class Y)

theorem positiveAction_sum_pairing (D E : PositiveTime) (x y : V) :
    B (positiveAction hw0 hw1 (sumTime D E) x) y =
      B (positiveAction hw0 hw1 E x) (positiveAction hw0 hw1 D y) := by
  refine Quotient.inductionOn₂ x y ?_
  intro X Y
  have h := pairing_limits_eq hw0 hw1
    (sumRows hw0 hw1 D E X) (constantRows hw0 hw1 Y)
    (timeRows hw0 hw1 E X) (timeRows hw0 hw1 D Y)
    (fun n => by rw [constantRows_point]; exact sumRows_pairing hw0 hw1 D E X Y n)
  rw [sumRows_limit, limit_constantRows] at h
  rw [positiveAction_pin hw0 hw1 E X, positiveAction_pin hw0 hw1 D Y]
  exact h

theorem positiveAction_sum (D E : PositiveTime) (x : V) :
    positiveAction hw0 hw1 (sumTime D E) x =
      positiveAction hw0 hw1 D (positiveAction hw0 hw1 E x) := by
  apply BF4WilsonAllNomeCompletedRealScalar.completed_eq_of_pairings hw0 hw1
  intro y
  exact (positiveAction_sum_pairing hw0 hw1 D E x y).trans
    (positiveAction_symmetric hw0 hw1 D (positiveAction hw0 hw1 E x) y).symm

def sumActionCertificate (D E : PositiveTime) (X : (PD).Cauchy) :
    Σ' Y : (PD).Cauchy, Σ' rate : Q' → Nat,
      (Class Y = positiveAction hw0 hw1 D (positiveAction hw0 hw1 E (Class X))) ×'
      (∀ epsilon : Q', (0 : Q') < epsilon → ∀ n, rate epsilon ≤ n →
        RCle (d (BF4WilsonAllNomeDyadicSemigroup.action hw0 hw1
          (NonnegativeDyadicTime.embed (sumMesh D E n)) (Class X)) (Class Y))
          (rat epsilon)) :=
  ⟨CRealSeminormCauchyRows.diagonalCauchy (distanceData hw0 hw1 (width := width))
      (sumRows hw0 hw1 D E X),
    limitRate hw0 hw1 (sumRows hw0 hw1 D E X),
    (sumRows_limit hw0 hw1 D E X).trans (positiveAction_sum hw0 hw1 D E (Class X)),
    fun epsilon he n hn => by
      have h := limit_bound hw0 hw1 (sumRows hw0 hw1 D E X) epsilon he n hn
      rw [sumRows_pin] at h
      exact h⟩

#print axioms sumRowModulus
#print axioms sum_action_cauchy
#print axioms sumRows
#print axioms sumRows_pin
#print axioms sumComparisonModulus
#print axioms sum_rows_close
#print axioms sumRows_limit
#print axioms sumRows_pairing
#print axioms positiveAction_sum_pairing
#print axioms positiveAction_sum
#print axioms sumActionCertificate

end YMGap.Continuum.BF4WilsonAllNomePositiveTimeComposition
