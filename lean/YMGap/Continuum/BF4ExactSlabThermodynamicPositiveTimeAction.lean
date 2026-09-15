/-
# Constructed positive real-time action on the ORIGINAL completion

Explicit positive real-time data produce rationally Cauchy dyadic times.
The energy estimate turns their rational modulus and positive floor into
an original squared-distance Cauchy modulus. Original row completion then
constructs the action and its output representative, without choosing
representatives from either a state or a time quotient.

The original state carrier, unit and norm are retained. The positive-time
addition law and continuity/identification at time zero are separate
obligations; no geometric T1, Hamiltonian, physical-scale or continuum/Clay
closure is claimed. The SU(2) nome and lattice spacing remain fixed.
-/

import YMGap.Continuum.BF4ExactSlabThermodynamicDyadicEnergy
import YMGap.Continuum.PositiveRealDyadicTimeData

namespace YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimeAction

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Constructive.HalfPow (half half_nonneg)
open YMGap.Constructive.NonnegativeDyadicTime (MeshPoint refine)
open YMGap.Constructive.DyadicTimeRationals
  (value value_refine relative_step_budget half_power_num)
open YMGap.Continuum.PositiveRealDyadicTimeData
open YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletionLinear
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedInner
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedBilinear
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedGeometry
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedRealScalar (completed_eq_of_pairings)
open YMGap.Continuum.BF4ExactSlabThermodynamicCauchyRows
open YMGap.Continuum.BF4ExactSlabThermodynamicRowPairingOrder
open YMGap.Continuum.BF4ExactSlabThermodynamicDyadicTimeMeshes
open YMGap.Continuum.BF4ExactSlabThermodynamicDyadicSemigroup
  (action action_embed time_refinement_power representative representative_pin)
open YMGap.Continuum.BF4ExactSlabThermodynamicDyadicEnergy
  (time_smallTime_bound rangeModulus scaled_norm_small)

local notation "point" X => Quotient.mk seminorm.completionSetoid X
local notation "rat" q => Quotient.mk crealSetoid (ofQ' q)
local notation "B" => completedInner

theorem same_mesh_close_bound (depth a b k : Nat) (floor : Q')
    (ha : floor ≤ value ⟨depth,a⟩) (hb : floor ≤ value ⟨depth,b⟩)
    (hab : value ⟨depth,a⟩ ≤ value ⟨depth,b⟩ + floor*half^k)
    (hba : value ⟨depth,b⟩ ≤ value ⟨depth,a⟩ + floor*half^k) (x : Completion) :
    RCle (completedDist (time depth a x) (time depth b x)) (RCscale (half^k) (B x x)) := by
  have hh := Q'.pow_nonneg half half_nonneg k
  by_cases h : a ≤ b
  · have hr := Q'.le_trans' _ _ _ hba
      (Q'.add_le_add_left _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ ha hh))
    have he := time_smallTime_bound depth (b-a) a k (relative_step_budget depth a b k h hr) x
    rw [← time_add, Nat.sub_add_cancel h, completedDist_symm] at he
    exact he
  · have h' : b ≤ a := by omega
    have hr := Q'.le_trans' _ _ _ hab
      (Q'.add_le_add_left _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ hb hh))
    have he := time_smallTime_bound depth (a-b) b k (relative_step_budget depth b a k h' hr) x
    rw [← time_add, Nat.sub_add_cancel h'] at he
    exact he

/-- Rational time control on arbitrary meshes, on every original vector. -/
theorem mesh_close_bound (p q : MeshPoint) (k : Nat) (floor : Q')
    (hp : floor ≤ value p) (hq : floor ≤ value q)
    (hpq : value p ≤ value q + floor*half^k)
    (hqp : value q ≤ value p + floor*half^k) (x : Completion) :
    RCle (completedDist (action (NonnegativeDyadicTime.embed p) x)
      (action (NonnegativeDyadicTime.embed q) x)) (RCscale (half^k) (B x x)) := by
  let d := p.depth+q.depth
  let a := p.steps*2^q.depth
  let b := q.steps*2^p.depth
  have ep : Q'.eqv (value ⟨d,a⟩) (value p) := value_refine p q.depth
  have eq : Q'.eqv (value ⟨d,b⟩) (value q) := by
    have h := value_refine q p.depth
    simpa only [refine, Nat.add_comm q.depth p.depth] using h
  have hpa := Q'.le_trans' _ _ _ hp (Q'.ge_of_eqv ep)
  have hqb := Q'.le_trans' _ _ _ hq (Q'.ge_of_eqv eq)
  have hab := Q'.le_trans' _ _ _ (Q'.le_of_eqv ep)
    (Q'.le_trans' _ _ _ hpq (Q'.add_le_add_right _ _ _ (Q'.ge_of_eqv eq)))
  have hba := Q'.le_trans' _ _ _ (Q'.le_of_eqv eq)
    (Q'.le_trans' _ _ _ hqp (Q'.add_le_add_right _ _ _ (Q'.ge_of_eqv ep)))
  have h := same_mesh_close_bound d a b k floor hpa hqb hab hba x
  have htq : time d b x = time q.depth q.steps x := by
    change time (p.depth+q.depth) (q.steps*2^p.depth) x = _
    rw [Nat.add_comm p.depth q.depth]
    exact time_refinement_power q.depth p.depth q.steps x
  have htp : time d a x = time p.depth p.steps x := time_refinement_power p.depth q.depth p.steps x
  rw [htp, htq] at h
  exact h

theorem half_power_positive (k : Nat) : (0 : Q') < HalfPow.half^k := by
  apply CReal.pos_of_num_pos
  rw [half_power_num]
  decide

def timeTolerance (D : PositiveTime) (X : seminorm.Cauchy) (epsilon : Q') : Q' :=
  D.floor * half^(rangeModulus X epsilon)

theorem timeTolerance_positive (D : PositiveTime) (X : seminorm.Cauchy) (epsilon : Q') :
    (0 : Q') < timeTolerance D X epsilon := Q'.mul_pos D.floor_positive (half_power_positive _)

def timeModulus (D : PositiveTime) (X : seminorm.Cauchy) (epsilon : Q') : Nat :=
  approximationModulus D (timeTolerance D X epsilon)

theorem time_approximations_cauchy (D : PositiveTime) (X : seminorm.Cauchy)
    (epsilon : Q') (he : (0 : Q') < epsilon) (m n : Nat)
    (hm : timeModulus D X epsilon ≤ m) (hn : timeModulus D X epsilon ≤ n) :
    RCle (completedDist (action (NonnegativeDyadicTime.embed (approximation D m)) (point X))
      (action (NonnegativeDyadicTime.embed (approximation D n)) (point X))) (rat epsilon) := by
  have h := approximation_cauchy D (timeTolerance D X epsilon) (timeTolerance_positive D X epsilon) m n hm hn
  exact RCle_trans (mesh_close_bound _ _ (rangeModulus X epsilon) D.floor
    (approximation_lower D m) (approximation_lower D n) h.1 h.2 (point X))
    (scaled_norm_small X epsilon he _ (Nat.le_refl _))

def timeRows (D : PositiveTime) (X : seminorm.Cauchy) : CauchyRows where
  row := fun n => representative (approximation D n) X
  modulus := timeModulus D X
  isCauchy := by
    intro epsilon he m n hm hn
    rw [representative_pin, representative_pin]
    exact time_approximations_cauchy D X epsilon he m n hm hn

theorem timeRows_pin (D : PositiveTime) (X : seminorm.Cauchy) (n : Nat) :
    rowPoint (timeRows D X) n = action (NonnegativeDyadicTime.embed (approximation D n)) (point X) :=
  representative_pin _ X

def representedAction (D : PositiveTime) (X : seminorm.Cauchy) : Completion := rowLimit (timeRows D X)

theorem representedAction_congr (D : PositiveTime) (X Y : seminorm.Cauchy)
    (h : (point X) = (point Y)) : representedAction D X = representedAction D Y := by
  apply rowLimit_independent
  intro n
  rw [timeRows_pin, timeRows_pin, h]

def positiveAction (D : PositiveTime) : Completion → Completion :=
  Quotient.lift (representedAction D) (fun X Y h => representedAction_congr D X Y (Quotient.sound h))

theorem positiveAction_pin (D : PositiveTime) (X : seminorm.Cauchy) :
    positiveAction D (point X) = representedAction D X := rfl

def outputRepresentative (D : PositiveTime) (X : seminorm.Cauchy) : seminorm.Cauchy := diagonalCauchy (timeRows D X)

theorem outputRepresentative_pin (D : PositiveTime) (X : seminorm.Cauchy) :
    (point (outputRepresentative D X)) = positiveAction D (point X) := rfl

def convergenceModulus (D : PositiveTime) (X : seminorm.Cauchy) : Q' → Nat := rowLimitRate (timeRows D X)

theorem approximation_bound (D : PositiveTime) (X : seminorm.Cauchy) (epsilon : Q')
    (he : (0 : Q') < epsilon) (n : Nat) (hn : convergenceModulus D X epsilon ≤ n) :
    RCle (completedDist (action (NonnegativeDyadicTime.embed (approximation D n)) (point X))
      (positiveAction D (point X))) (rat epsilon) := by
  have h := rowLimit_bound (timeRows D X) epsilon he n hn
  rw [timeRows_pin] at h
  exact h

def actionCertificate (D : PositiveTime) (X : seminorm.Cauchy) :
    Σ' Y : seminorm.Cauchy, Σ' rate : Q' → Nat,
      ((point Y) = positiveAction D (point X)) ×'
      (∀ epsilon : Q', (0 : Q') < epsilon → ∀ n, rate epsilon ≤ n →
        RCle (completedDist (action (NonnegativeDyadicTime.embed (approximation D n)) (point X)) (point Y)) (rat epsilon)) :=
  ⟨outputRepresentative D X, convergenceModulus D X, outputRepresentative_pin D X,
    fun e he n hn => approximation_bound D X e he n hn⟩

theorem positiveAction_symmetric (D : PositiveTime) (x y : Completion) :
    B (positiveAction D x) y = B x (positiveAction D y) := by
  refine Quotient.inductionOn₂ x y ?_
  intro X Y
  have h := rowLimit_pairing_eq (timeRows D X) (constantRows Y) (constantRows X) (timeRows D Y)
    (fun n => by
      rw [timeRows_pin, timeRows_pin, constantRows_pin, constantRows_pin]
      exact BF4ExactSlabThermodynamicDyadicSemigroup.action_symmetric _ _ _)
  rw [rowLimit_constant, rowLimit_constant] at h
  exact h

theorem positiveAction_nonnegative (D : PositiveTime) (x : Completion) : RCnonneg (B (positiveAction D x) x) := by
  refine Quotient.inductionOn x ?_
  intro X
  have h := rowLimit_pairing_nonnegative (timeRows D X) (constantRows X)
    (fun n => by rw [timeRows_pin, constantRows_pin]; exact BF4ExactSlabThermodynamicDyadicSemigroup.action_nonnegative _ _)
  rw [rowLimit_constant] at h
  exact h

theorem positiveAction_contraction (D : PositiveTime) (x : Completion) :
    RCle (B (positiveAction D x) (positiveAction D x)) (B x x) := by
  refine Quotient.inductionOn x ?_
  intro X
  have h := rowLimit_pairing_le (timeRows D X) (timeRows D X) (constantRows X) (constantRows X)
    (fun n => by rw [timeRows_pin, constantRows_pin]; exact BF4ExactSlabThermodynamicDyadicSemigroup.action_contraction _ _)
  rw [rowLimit_constant] at h
  exact h

theorem positiveAction_add (D : PositiveTime) (x y : Completion) :
    positiveAction D (completedAdd x y) = completedAdd (positiveAction D x) (positiveAction D y) := by
  apply completed_eq_of_pairings
  intro z
  rw [positiveAction_symmetric, completedInner_add_left, completedInner_add_left,
    positiveAction_symmetric, positiveAction_symmetric]

theorem positiveAction_smul (D : PositiveTime) (c : Q') (x : Completion) :
    positiveAction D (completedSmul c x) = completedSmul c (positiveAction D x) := by
  apply completed_eq_of_pairings
  intro z
  rw [positiveAction_symmetric, completedInner_smul_left, completedInner_smul_left, positiveAction_symmetric]

end YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimeAction

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimeAction.same_mesh_close_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimeAction.mesh_close_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimeAction.half_power_positive
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimeAction.timeTolerance
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimeAction.timeTolerance_positive
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimeAction.timeModulus
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimeAction.time_approximations_cauchy
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimeAction.timeRows
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimeAction.timeRows_pin
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimeAction.representedAction
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimeAction.representedAction_congr
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimeAction.positiveAction
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimeAction.positiveAction_pin
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimeAction.outputRepresentative
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimeAction.outputRepresentative_pin
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimeAction.convergenceModulus
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimeAction.approximation_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimeAction.actionCertificate
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimeAction.positiveAction_symmetric
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimeAction.positiveAction_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimeAction.positiveAction_contraction
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimeAction.positiveAction_add
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimeAction.positiveAction_smul
