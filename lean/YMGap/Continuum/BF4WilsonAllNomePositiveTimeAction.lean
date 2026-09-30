/-
# Constructed positive real-time images on the SAME original Wilson carrier

Explicit positive real-time data have a rational floor and computed dyadic
approximations. The original energy estimate converts their time modulus
to an original squared-distance modulus. Supplied dyadic output streams
then construct an actual original limit and its output representative.

This construction works on EVERY original state at strictly positive times.
It does not assert continuity at zero on the whole carrier, remove its
boundary kernel, or identify a generator or physical time calibration.
Time-presentation independence and the addition law are separate joins.
-/

import YMGap.Continuum.BF4WilsonAllNomeDyadicContinuity
import YMGap.Continuum.BF4WilsonAllNomeDyadicRepresentatives
import YMGap.Continuum.PositiveRealDyadicTimeData

namespace YMGap.Continuum.BF4WilsonAllNomePositiveTimeAction

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Constructive.HalfPow (half half_nonneg)
open YMGap.Constructive.NonnegativeDyadicTime (MeshPoint refine embed)
open YMGap.Constructive.DyadicTimeRationals (value value_refine relative_step_budget half_power_num)
open YMGap.Continuum.PositiveRealDyadicTimeData
open YMGap.Continuum.BF4WilsonAllNomeSeminorm (seminorm)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeDistance
open YMGap.Continuum.BF4WilsonAllNomeCauchyRows
open YMGap.Continuum.BF4WilsonAllNomeDyadicSemigroup
open YMGap.Continuum.BF4WilsonAllNomeDyadicEnergy (time_small_bound)
open YMGap.Continuum.BF4WilsonAllNomeDyadicContinuity (rangeModulus scaled_norm_small)
open YMGap.Continuum.BF4WilsonAllNomeDyadicRepresentatives (meshRepresentative meshRepresentative_pin)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "D" => seminorm hw0 hw1 (width := width)
local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "d" => completedDist hw0 hw1
local notation "S" => meshAction hw0 hw1
local notation "Class" => Quotient.mk
  (CRealSeminormCompletion.SquaredSeminorm.completionSetoid
    (seminorm hw0 hw1 (width := width)))
local notation "rat" q:arg => Quotient.mk crealSetoid (ofQ' q)

theorem same_mesh_close_bound (depth a b k : Nat) (floor : Q')
    (ha : floor ≤ value ⟨depth,a⟩) (hb : floor ≤ value ⟨depth,b⟩)
    (hab : value ⟨depth,a⟩ ≤ value ⟨depth,b⟩+floor*half^k)
    (hba : value ⟨depth,b⟩ ≤ value ⟨depth,a⟩+floor*half^k) (x : V) :
    RCle (d (S depth a x) (S depth b x)) (RCscale (half^k) (B x x)) := by
  have hh := Q'.pow_nonneg half half_nonneg k
  by_cases h : a ≤ b
  · have hr := Q'.le_trans' _ _ _ hba
      (Q'.add_le_add_left _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ ha hh))
    have he := time_small_bound hw0 hw1 depth (b-a) a k (relative_step_budget depth a b k h hr) x
    rw [← mesh_add,Nat.sub_add_cancel h,completedDist_symm] at he
    exact he
  · have h' : b ≤ a := by omega
    have hr := Q'.le_trans' _ _ _ hab
      (Q'.add_le_add_left _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ hb hh))
    have he := time_small_bound hw0 hw1 depth (a-b) b k (relative_step_budget depth b a k h' hr) x
    rw [← mesh_add,Nat.sub_add_cancel h'] at he
    exact he

/-- A common positive time floor controls arbitrary dyadic meshes on every state. -/
theorem mesh_close_bound (p q : MeshPoint) (k : Nat) (floor : Q')
    (hp : floor ≤ value p) (hq : floor ≤ value q)
    (hpq : value p ≤ value q+floor*half^k)
    (hqp : value q ≤ value p+floor*half^k) (x : V) :
    RCle (d (action hw0 hw1 (embed p) x) (action hw0 hw1 (embed q) x))
      (RCscale (half^k) (B x x)) := by
  let depth := p.depth+q.depth
  let a := p.steps*2^q.depth
  let b := q.steps*2^p.depth
  have ep : Q'.eqv (value ⟨depth,a⟩) (value p) := value_refine p q.depth
  have eq : Q'.eqv (value ⟨depth,b⟩) (value q) := by
    have h := value_refine q p.depth
    simpa only [refine,Nat.add_comm q.depth p.depth] using h
  have hpa := Q'.le_trans' _ _ _ hp (Q'.ge_of_eqv ep)
  have hqb := Q'.le_trans' _ _ _ hq (Q'.ge_of_eqv eq)
  have hab := Q'.le_trans' _ _ _ (Q'.le_of_eqv ep)
    (Q'.le_trans' _ _ _ hpq (Q'.add_le_add_right _ _ _ (Q'.ge_of_eqv eq)))
  have hba := Q'.le_trans' _ _ _ (Q'.le_of_eqv eq)
    (Q'.le_trans' _ _ _ hqp (Q'.add_le_add_right _ _ _ (Q'.ge_of_eqv ep)))
  have h := same_mesh_close_bound hw0 hw1 depth a b k floor hpa hqb hab hba x
  have htq : S depth b x = S q.depth q.steps x := by
    change S (p.depth+q.depth) (q.steps*2^p.depth) x = _
    rw [Nat.add_comm p.depth q.depth]
    exact mesh_refinement hw0 hw1 q.depth p.depth q.steps x
  have htp : S depth a x = S p.depth p.steps x := mesh_refinement hw0 hw1 p.depth q.depth p.steps x
  rw [htp,htq] at h
  exact h

theorem half_power_positive (k : Nat) : (0 : Q') < half^k := by
  induction k with
  | zero => decide
  | succ k ih => exact Q'.mul_pos (by decide : (0 : Q') < half) ih

def timeTolerance (time : PositiveTime) (X : (D).Cauchy) (epsilon : Q') : Q' :=
  time.floor*half^(rangeModulus hw0 hw1 X epsilon)

theorem timeTolerance_positive (time : PositiveTime) (X : (D).Cauchy) (epsilon : Q') :
    (0 : Q') < timeTolerance hw0 hw1 time X epsilon :=
  Q'.mul_pos time.floor_positive (half_power_positive _)

def timeModulus (time : PositiveTime) (X : (D).Cauchy) (epsilon : Q') : Nat :=
  approximationModulus time (timeTolerance hw0 hw1 time X epsilon)

theorem time_approximations_cauchy (time : PositiveTime) (X : (D).Cauchy)
    (epsilon : Q') (he : (0 : Q') < epsilon) (m n : Nat)
    (hm : timeModulus hw0 hw1 time X epsilon ≤ m) (hn : timeModulus hw0 hw1 time X epsilon ≤ n) :
    RCle (d (action hw0 hw1 (embed (approximation time m)) (Class X))
      (action hw0 hw1 (embed (approximation time n)) (Class X))) (rat epsilon) := by
  have h := approximation_cauchy time (timeTolerance hw0 hw1 time X epsilon)
    (timeTolerance_positive hw0 hw1 time X epsilon) m n hm hn
  exact RCle_trans (mesh_close_bound hw0 hw1 _ _ (rangeModulus hw0 hw1 X epsilon) time.floor
    (approximation_lower time m) (approximation_lower time n) h.1 h.2 (Class X))
    (scaled_norm_small hw0 hw1 X epsilon he _ (Nat.le_refl _))

/-- Both the original output streams and the outer time modulus are computed. -/
def timeRows (time : PositiveTime) (X : (D).Cauchy) : RepresentedCauchy hw0 hw1 (width := width) where
  row := fun n => meshRepresentative hw0 hw1 (approximation time n).depth (approximation time n).steps X
  modulus := timeModulus hw0 hw1 time X
  isCauchy := by
    intro epsilon he m n hm hn
    change RCle (d
      (Class (meshRepresentative hw0 hw1 (approximation time m).depth (approximation time m).steps X))
      (Class (meshRepresentative hw0 hw1 (approximation time n).depth (approximation time n).steps X))) _
    rw [meshRepresentative_pin,meshRepresentative_pin]
    exact time_approximations_cauchy hw0 hw1 time X epsilon he m n hm hn

theorem timeRows_pin (time : PositiveTime) (X : (D).Cauchy) (n : Nat) :
    rowPoint hw0 hw1 (timeRows hw0 hw1 time X) n = action hw0 hw1 (embed (approximation time n)) (Class X) :=
  meshRepresentative_pin hw0 hw1 (approximation time n).depth (approximation time n).steps X

def representedAction (time : PositiveTime) (X : (D).Cauchy) : V := limit hw0 hw1 (timeRows hw0 hw1 time X)

theorem representedAction_congr (time : PositiveTime) (X Y : (D).Cauchy)
    (h : Class X = Class Y) : representedAction hw0 hw1 time X = representedAction hw0 hw1 time Y := by
  apply limit_independent hw0 hw1
  intro n
  rw [timeRows_pin,timeRows_pin,h]

/-- Positive real-time images on the ORIGINAL completion, without representative choice. -/
def positiveAction (time : PositiveTime) : V → V :=
  Quotient.lift (representedAction hw0 hw1 time)
    (fun X Y h => representedAction_congr hw0 hw1 time X Y (Quotient.sound h))

theorem positiveAction_pin (time : PositiveTime) (X : (D).Cauchy) :
    positiveAction hw0 hw1 time (Class X) = limit hw0 hw1 (timeRows hw0 hw1 time X) := rfl

def outputRepresentative (time : PositiveTime) (X : (D).Cauchy) : (D).Cauchy :=
  CRealSeminormCauchyRows.diagonalCauchy (distanceData hw0 hw1 (width := width)) (timeRows hw0 hw1 time X)

theorem outputRepresentative_pin (time : PositiveTime) (X : (D).Cauchy) :
    Class (outputRepresentative hw0 hw1 time X) = positiveAction hw0 hw1 time (Class X) := rfl

def convergenceModulus (time : PositiveTime) (X : (D).Cauchy) : Q' → Nat :=
  limitRate hw0 hw1 (timeRows hw0 hw1 time X)

theorem approximation_bound (time : PositiveTime) (X : (D).Cauchy) (epsilon : Q')
    (he : (0 : Q') < epsilon) (n : Nat) (hn : convergenceModulus hw0 hw1 time X epsilon ≤ n) :
    RCle (d (action hw0 hw1 (embed (approximation time n)) (Class X))
      (positiveAction hw0 hw1 time (Class X))) (rat epsilon) := by
  have h := limit_bound hw0 hw1 (timeRows hw0 hw1 time X) epsilon he n hn
  rw [timeRows_pin] at h
  exact h

/-- Actual output stream, convergence rate, and SAME-action pin remain Type data. -/
def actionCertificate (time : PositiveTime) (X : (D).Cauchy) :
    Σ' Y : (D).Cauchy, Σ' rate : Q' → Nat,
      (Class Y = positiveAction hw0 hw1 time (Class X)) ×'
      (∀ epsilon : Q', (0 : Q') < epsilon → ∀ n, rate epsilon ≤ n →
        RCle (d (action hw0 hw1 (embed (approximation time n)) (Class X)) (Class Y)) (rat epsilon)) :=
  ⟨outputRepresentative hw0 hw1 time X,convergenceModulus hw0 hw1 time X,outputRepresentative_pin hw0 hw1 time X,
    fun e he n hn => approximation_bound hw0 hw1 time X e he n hn⟩

#print axioms mesh_close_bound
#print axioms timeModulus
#print axioms time_approximations_cauchy
#print axioms timeRows
#print axioms timeRows_pin
#print axioms representedAction_congr
#print axioms positiveAction
#print axioms outputRepresentative
#print axioms outputRepresentative_pin
#print axioms convergenceModulus
#print axioms approximation_bound
#print axioms actionCertificate

end YMGap.Continuum.BF4WilsonAllNomePositiveTimeAction
