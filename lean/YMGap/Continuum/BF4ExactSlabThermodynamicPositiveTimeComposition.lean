/-
# Positive real-time addition gives ORIGINAL operator composition

The two numerical dyadic streams are added on common meshes. Their
computed Cauchy rate constructs original state rows. Upward rounding
changes the summed time by at most half^n, so the energy estimate pins
their limit to the PREVIOUS positiveAction at the actual sum of times.
The existing mixed dyadic pairing identity then passes to row limits;
original positive definiteness gives the composition law.

No product-limit hypothesis, new state carrier, inverse, spectral model
or selected quotient representative is used. Full-space continuity at
zero, geometric T1/Hamiltonian identification, physical-scale control,
continuum and Clay remain open. SU(2) nome and spacing remain fixed.
-/

import YMGap.Continuum.PositiveRealDyadicTimeAddition
import YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimePins
import YMGap.Continuum.BF4ExactSlabThermodynamicSymbolCompatibility

namespace YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimeComposition

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Constructive.DyadicTimeRationals (value upper upper_error)
open YMGap.Continuum.PositiveRealDyadicTimeData
open YMGap.Continuum.PositiveRealDyadicTimeAddition
open YMGap.Continuum.RegularLinearGeometricModulus (halfCutoff halfCutoff_spec)
open YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedInner
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedGeometry
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedRealScalar (completed_eq_of_pairings)
open YMGap.Continuum.BF4ExactSlabThermodynamicCauchyRows
open YMGap.Continuum.BF4ExactSlabThermodynamicRowPairingOrder
open YMGap.Continuum.BF4ExactSlabThermodynamicSymbolCompatibility (rowLimits_eq_of_close)
open YMGap.Continuum.BF4ExactSlabThermodynamicDyadicSemigroup
  (action representative representative_pin action_mixed_moments)
open YMGap.Continuum.BF4ExactSlabThermodynamicDyadicEnergy (rangeModulus scaled_norm_small)
open YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimeAction
open YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimePins

local notation "point" X => Quotient.mk seminorm.completionSetoid X
local notation "rat" q => Quotient.mk crealSetoid (ofQ' q)

def sumRowModulus (D E : PositiveTime) (X : seminorm.Cauchy) (epsilon : Q') : Nat :=
  sumModulus D E (timeTolerance (sumTime D E) X epsilon)

theorem sum_action_cauchy (D E : PositiveTime) (X : seminorm.Cauchy) (epsilon : Q')
    (he : (0 : Q') < epsilon) (m n : Nat)
    (hm : sumRowModulus D E X epsilon ≤ m) (hn : sumRowModulus D E X epsilon ≤ n) :
    RCle (completedDist (action (NonnegativeDyadicTime.embed (sumMesh D E m)) (point X))
      (action (NonnegativeDyadicTime.embed (sumMesh D E n)) (point X))) (rat epsilon) := by
  have h := sumMesh_cauchy D E _ (timeTolerance_positive (sumTime D E) X epsilon) m n hm hn
  exact RCle_trans (mesh_close_bound _ _ (rangeModulus X epsilon) (D.floor+E.floor)
    (sumMesh_lower D E m) (sumMesh_lower D E n) h.1 h.2 (point X))
    (scaled_norm_small X epsilon he _ (Nat.le_refl _))

def sumRows (D E : PositiveTime) (X : seminorm.Cauchy) : CauchyRows where
  row := fun n => representative (sumMesh D E n) X
  modulus := sumRowModulus D E X
  isCauchy := by
    intro epsilon he m n hm hn
    rw [representative_pin, representative_pin]
    exact sum_action_cauchy D E X epsilon he m n hm hn

theorem sumRows_pin (D E : PositiveTime) (X : seminorm.Cauchy) (n : Nat) :
    rowPoint (sumRows D E X) n = action (NonnegativeDyadicTime.embed (sumMesh D E n)) (point X) :=
  representative_pin _ X

def sumComparisonModulus (D E : PositiveTime) (X : seminorm.Cauchy) (epsilon : Q') : Nat :=
  halfCutoff (timeTolerance (sumTime D E) X epsilon)

theorem sum_rows_close (D E : PositiveTime) (X : seminorm.Cauchy) (epsilon : Q')
    (he : (0 : Q') < epsilon) (n : Nat) (hn : sumComparisonModulus D E X epsilon ≤ n) :
    RCle (completedDist (rowPoint (timeRows (sumTime D E) X) n) (rowPoint (sumRows D E X) n)) (rat epsilon) := by
  let k := rangeModulus X epsilon
  let delta := timeTolerance (sumTime D E) X epsilon
  have hd : (0 : Q') < delta := timeTolerance_positive (sumTime D E) X epsilon
  have herr : HalfPow.half^n ≤ delta :=
    Q'.le_trans' _ _ _ (half_pow_antitone _ n hn) (halfCutoff_spec _ hd)
  have hsample := Q'.le_trans' _ _ _ (Q'.le_of_lt (sum_floor_positive D E)) (sum_lower D E n)
  have hu := upper_error (sumSample D E n) hsample n
  have hleft : value (upper (sumSample D E n) n) ≤ value (sumMesh D E n) + delta :=
    Q'.le_trans' _ _ _ hu.2 (Q'.le_trans' _ _ _ (Q'.add_le_add_left _ _ _ herr)
      (Q'.add_le_add_right _ _ _ (Q'.ge_of_eqv (sumMesh_value D E n))))
  have hright : value (sumMesh D E n) ≤ value (upper (sumSample D E n) n) + delta :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (sumMesh_value D E n))
      (Q'.le_trans' _ _ _ hu.1 (Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt hd)))
  have hp : D.floor+E.floor ≤ value (upper (sumSample D E n) n) :=
    Q'.le_trans' _ _ _ (sum_lower D E n) hu.1
  have h := RCle_trans (mesh_close_bound (upper (sumSample D E n) n) (sumMesh D E n) k
    (D.floor+E.floor) hp (sumMesh_lower D E n) hleft hright (point X))
    (scaled_norm_small X epsilon he k (Nat.le_refl _))
  rw [timeRows_pin, sumRows_pin]
  unfold approximation
  rw [sumTime_sample]
  exact h

/-- The independently constructed summed-mesh rows converge to the PREVIOUS action. -/
theorem sumRows_limit (D E : PositiveTime) (X : seminorm.Cauchy) :
    rowLimit (sumRows D E X) = positiveAction (sumTime D E) (point X) :=
  (rowLimits_eq_of_close (timeRows (sumTime D E) X) (sumRows D E X)
    (sumComparisonModulus D E X) (sum_rows_close D E X)).symm

theorem sumRows_pairing (D E : PositiveTime) (X Y : seminorm.Cauchy) (n : Nat) :
    completedInner (rowPoint (sumRows D E X) n) (point Y) =
      completedInner (rowPoint (timeRows E X) n) (rowPoint (timeRows D Y) n) := by
  rw [sumRows_pin, timeRows_pin, timeRows_pin]
  exact action_mixed_moments (NonnegativeDyadicTime.embed (approximation D n))
    (NonnegativeDyadicTime.embed (approximation E n)) (point X) (point Y)

theorem positiveAction_sum_pairing (D E : PositiveTime) (x y : Completion) :
    completedInner (positiveAction (sumTime D E) x) y =
      completedInner (positiveAction E x) (positiveAction D y) := by
  refine Quotient.inductionOn₂ x y ?_
  intro X Y
  have h := rowLimit_pairing_eq (sumRows D E X) (constantRows Y) (timeRows E X) (timeRows D Y)
    (fun n => by rw [constantRows_pin]; exact sumRows_pairing D E X Y n)
  rw [sumRows_limit, rowLimit_constant] at h
  exact h

/-- Actual positive real-time addition gives composition of the SAME original operators. -/
theorem positiveAction_sum (D E : PositiveTime) (x : Completion) :
    positiveAction (sumTime D E) x = positiveAction D (positiveAction E x) := by
  apply completed_eq_of_pairings
  intro y
  exact (positiveAction_sum_pairing D E x y).trans
    (positiveAction_symmetric D (positiveAction E x) y).symm

def sumActionCertificate (D E : PositiveTime) (X : seminorm.Cauchy) :
    Σ' Y : seminorm.Cauchy, Σ' rate : Q' → Nat,
      ((point Y) = positiveAction D (positiveAction E (point X))) ×'
      (∀ epsilon : Q', (0 : Q') < epsilon → ∀ n, rate epsilon ≤ n →
        RCle (completedDist (action (NonnegativeDyadicTime.embed (sumMesh D E n)) (point X)) (point Y)) (rat epsilon)) :=
  ⟨diagonalCauchy (sumRows D E X), rowLimitRate (sumRows D E X),
    (sumRows_limit D E X).trans (positiveAction_sum D E (point X)),
    fun epsilon he n hn => by
      have h := rowLimit_bound (sumRows D E X) epsilon he n hn
      rw [sumRows_pin] at h
      exact h⟩

end YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimeComposition

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimeComposition.sumRowModulus
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimeComposition.sum_action_cauchy
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimeComposition.sumRows
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimeComposition.sumRows_pin
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimeComposition.sumComparisonModulus
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimeComposition.sum_rows_close
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimeComposition.sumRows_limit
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimeComposition.sumRows_pairing
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimeComposition.positiveAction_sum_pairing
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimeComposition.positiveAction_sum
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimeComposition.sumActionCertificate
