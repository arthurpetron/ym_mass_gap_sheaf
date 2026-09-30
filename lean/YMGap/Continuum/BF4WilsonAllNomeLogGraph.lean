/-
# A single-valued witnessed graph limit of the original time series

Let T be original one-step time and F=sum_{k>=1}(I-T)^k T/k.
The core graph consists of (T x,F x). Its graph limits carry their source
sequence and a simultaneous squared-distance modulus as data. If the input
limit is zero then the output limit is zero: commutation first gives T z=0,
the proved kernel law gives F z=0, and symmetry makes z orthogonal to every
approximating F x. This proves closability without any source-norm bound.

The original carrier and its boundary kernel are unchanged. This is not a
full-carrier densely defined operator, a scalar-log identification, a
continuous-time generator, or a physical Hamiltonian/mass-gap theorem.
-/

import YMGap.Continuum.BF4WilsonAllNomeLogOperator
import YMGap.Continuum.BF4WilsonAllNomeGraphDistance
import YMGap.Continuum.BF4WilsonAllNomeLogRangePositive

namespace YMGap.Continuum.BF4WilsonAllNomeLogGraph

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4WilsonAllNomeLinear
open YMGap.Continuum.BF4WilsonAllNomeLinearLaws
open YMGap.Continuum.BF4WilsonAllNomeBilinearTime
open YMGap.Continuum.BF4WilsonAllNomeDistance
open YMGap.Continuum.BF4WilsonAllNomeCauchyRows
open YMGap.Continuum.BF4WilsonAllNomeLogSeries
open YMGap.Continuum.BF4WilsonAllNomeLogOperator
open YMGap.Continuum.BF4WilsonAllNomeGraphDistance
open YMGap.Continuum.BF4WilsonAllNomeLogRangePositive

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "T" => completedTime hw0 hw1
local notation "F" => regularizedLog hw0 hw1
local notation "S" => completedSub hw0 hw1
local notation "Z" => completedZero hw0 hw1 width
local notation "dist" => completedDist hw0 hw1
local notation "rat" q => Quotient.mk crealSetoid (ofQ' q)

private def quarter (e : Q') : Q' := HalfPow.half * (HalfPow.half * e)

private theorem quarter_positive {e : Q'} (he : (0 : Q') < e) :
    (0 : Q') < quarter e := ExpNeg.half_mul_pos _ (ExpNeg.half_mul_pos _ he)

private theorem four_quarters (e : Q') :
    RCadd (RCadd (rat (quarter e)) (rat (quarter e)))
      (RCadd (rat (quarter e)) (rat (quarter e))) = rat e :=
  Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun _ =>
    Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (ExpNeg.two_halves (HalfPow.half*e))
        (ExpNeg.two_halves (HalfPow.half*e))) (ExpNeg.two_halves e)))

private theorem zero_add_rat (e : Q') : RCadd RCzero (rat e) = rat e :=
  Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun _ => by change Q'.eqv (0+e) e; rw [Q'.zero_add']; exact Q'.eqv_refl _))

private theorem eq_of_dist_small (x y : V)
    (h : ∀ e : Q', (0 : Q') < e → RCle (dist x y) (rat e)) : x = y := by
  apply (completedDist_zero_iff hw0 hw1 x y).mp
  apply RCle_antisymm ?_ (completedDist_nonnegative hw0 hw1 x y)
  apply RationalScalarTwoSidedError.le_of_all_errors
  intro e he
  rw [zero_add_rat]
  exact h e he

/-- Graph convergence data, with no chosen inverse or erased modulus. -/
structure GraphLimit (input output : V) where
  source : Nat → V
  modulus : Q' → Nat
  bound : ∀ e : Q', (0 : Q') < e → ∀ n, modulus e ≤ n →
    RCle (dist (T 1 (source n)) input) (rat e) ∧
    RCle (dist (F (source n)) output) (rat e)

/-- Every actual positive-time image has its literal series graph witness. -/
def core (x : V) : GraphLimit hw0 hw1 (T 1 x) (F x) where
  source := fun _ => x
  modulus := fun _ => 0
  bound := by
    intro e he n _
    rw [(completedDist_zero_iff hw0 hw1 _ _).mpr rfl,
      (completedDist_zero_iff hw0 hw1 _ _).mpr rfl]
    have h : RCle RCzero (rat e) := leEv_le_ofQ'_of_approx_le (fun _ => Q'.le_of_lt he)
    exact ⟨h,h⟩

/-- Continuity and exact commutation survive a witnessed graph limit. -/
theorem graph_time_pin {input output : V} (G : GraphLimit hw0 hw1 input output) :
    T 1 output = F input := by
  apply eq_of_dist_small hw0 hw1
  intro e he
  let d := quarter e
  let n := G.modulus d
  have h := G.bound d (quarter_positive he) n (Nat.le_refl _)
  have hleft := RCle_trans (completedDist_time hw0 hw1 1 output (F (G.source n)))
    (by rw [completedDist_symm]; exact h.2)
  have hright := RCle_trans (regularizedLog_dist_bound hw0 hw1 (T 1 (G.source n)) input) h.1
  rw [regularizedLog_commutes_time] at hright
  have htriangle := RCle_trans
    (completedDist_triangle hw0 hw1 (T 1 output) (T 1 (F (G.source n))) (F input))
    (RCadd_le_add (RCadd_le_add hleft hleft) (RCadd_le_add hright hright))
  rwa [four_quarters] at htriangle

/-- The core graph is closable, even when preimage norms diverge. -/
theorem graph_zero_input {output : V} (G : GraphLimit hw0 hw1 Z output) : output = Z := by
  have hF0 : F Z = Z := regularizedLog_kernel_zero hw0 hw1 Z (completedTime_zero_element hw0 hw1 1)
  have hT : T 1 output = Z := (graph_time_pin hw0 hw1 G).trans hF0
  have hF : F output = Z := regularizedLog_kernel_zero hw0 hw1 output hT
  apply eq_of_dist_small hw0 hw1
  intro e he
  let n := G.modulus e
  have hp : B output (F (G.source n)) = RCzero := by
    rw [← regularizedLog_symmetric, hF, completedInner_zero_left]
  rw [dist_zero_right]
  exact RCle_trans (norm_le_dist_of_orthogonal hw0 hw1 output (F (G.source n)) hp)
    (by rw [completedDist_symm]; exact (G.bound e he n (Nat.le_refl _)).2)

/-- Subtract graph witnesses with an explicit synchronized quarter modulus. -/
def subtract {x y u v : V} (G : GraphLimit hw0 hw1 x u) (H : GraphLimit hw0 hw1 y v) :
    GraphLimit hw0 hw1 (S x y) (S u v) where
  source := fun n => S (G.source n) (H.source n)
  modulus := fun e => max (G.modulus (quarter e)) (H.modulus (quarter e))
  bound := by
    intro e he n hn
    have hG := G.bound (quarter e) (quarter_positive he) n (Nat.le_trans (Nat.le_max_left _ _) hn)
    have hH := H.bound (quarter e) (quarter_positive he) n (Nat.le_trans (Nat.le_max_right _ _) hn)
    constructor
    · rw [completedTime_sub]
      have h := RCle_trans (completedDist_sub_le hw0 hw1 _ _ _ _)
        (RCadd_le_add (RCadd_le_add hG.1 hG.1) (RCadd_le_add hH.1 hH.1))
      rwa [four_quarters] at h
    · rw [regularizedLog_sub]
      have h := RCle_trans (completedDist_sub_le hw0 hw1 _ _ _ _)
        (RCadd_le_add (RCadd_le_add hG.2 hG.2) (RCadd_le_add hH.2 hH.2))
      rwa [four_quarters] at h

/-- Every witnessed graph limit has a unique output on the original carrier. -/
theorem graph_single_valued {input y z : V}
    (G : GraphLimit hw0 hw1 input y) (H : GraphLimit hw0 hw1 input z) : y = z := by
  have W := subtract hw0 hw1 G H
  rw [completedSub_self] at W
  have h := graph_zero_input hw0 hw1 W
  apply (completedDist_zero_iff hw0 hw1 y z).mp
  unfold completedDist
  rw [h, completedInner_zero_left]

/-- Source nonuniqueness in the actual time kernel does not make the graph multivalued. -/
theorem core_single_valued {x y : V} (h : T 1 x = T 1 y) : F x = F y := by
  have G := core hw0 hw1 x
  rw [h] at G
  exact graph_single_valued hw0 hw1 G (core hw0 hw1 y)

/-- Positivity on the actual core graph, not merely positivity of F alone. -/
theorem core_nonnegative (x : V) : RCnonneg (B (T 1 x) (F x)) :=
  regularizedLog_time_nonnegative hw0 hw1 x

/-- Symmetry uses both the original time and the same constructed series. -/
theorem core_symmetric (x y : V) : B (F x) (T 1 y) = B (T 1 x) (F y) := by
  rw [regularizedLog_symmetric, regularizedLog_commutes_time,
    ← completedInner_time_balance]

/-- A second supplied graph limit is flattened by an explicit diagonal.
This is closedness for witnessed limits, with no countable choice. -/
def diagonal {input output : V} (xs ys : Nat → V)
    (G : ∀ n, GraphLimit hw0 hw1 (xs n) (ys n))
    (modulus : Q' → Nat)
    (bound : ∀ e : Q', (0 : Q') < e → ∀ n, modulus e ≤ n →
      RCle (dist (xs n) input) (rat e) ∧ RCle (dist (ys n) output) (rat e)) :
    GraphLimit hw0 hw1 input output where
  source := fun n => (G n).source ((G n).modulus (Q'.invSucc n))
  modulus := fun e => max (modulus (quarter e)) (quarter e).den
  bound := by
    intro e he n hn
    have hd := quarter_positive he
    have ho := bound (quarter e) hd n (Nat.le_trans (Nat.le_max_left _ _) hn)
    have hi := (G n).bound (Q'.invSucc n) (Q'.invSucc_pos n)
      ((G n).modulus (Q'.invSucc n)) (Nat.le_refl _)
    have hq : RCle (rat (Q'.invSucc n)) (rat (quarter e)) :=
      leEv_le_ofQ'_of_approx_le (fun _ => Q'.le_trans' _ _ _
        (ExpNeg.invSucc_le_of_le (Nat.le_trans (Nat.le_max_right _ _) hn))
        (HalfPow.invSucc_den_le _ hd))
    have h1 := RCle_trans hi.1 hq
    have h2 := RCle_trans hi.2 hq
    constructor
    · have h := RCle_trans (completedDist_triangle hw0 hw1 _ (xs n) input)
        (RCadd_le_add (RCadd_le_add h1 h1) (RCadd_le_add ho.1 ho.1))
      rwa [four_quarters] at h
    · have h := RCle_trans (completedDist_triangle hw0 hw1 _ (ys n) output)
        (RCadd_le_add (RCadd_le_add h2 h2) (RCadd_le_add ho.2 ho.2))
      rwa [four_quarters] at h

/-- A presentation contains its input, output and actual simultaneous limit
certificate. This is a local operator domain, not a new frontier bundle. -/
def Presentation := Σ' input : V, Σ' output : V, GraphLimit hw0 hw1 input output

/-- Presentations are identified by their ORIGINAL carrier input alone. -/
def inputSetoid : Setoid (Presentation hw0 hw1 (width := width)) where
  r p q := p.1 = q.1
  iseqv := ⟨fun _ => rfl, fun h => h.symm, fun h k => h.trans k⟩

def Domain := Quotient (inputSetoid hw0 hw1 (width := width))

/-- The domain embeds in the unchanged completed carrier. -/
def input : Domain hw0 hw1 (width := width) → V :=
  Quotient.lift (fun p => p.1) (fun _ _ h => h)

/-- Actual operator value, descending by the proved graph uniqueness.
No inverse of T or representative choice is used. -/
def action : Domain hw0 hw1 (width := width) → V :=
  Quotient.lift (fun p => p.2.1) (fun p q h => by
    apply graph_single_valued hw0 hw1 p.2.2
    exact h.symm ▸ q.2.2)

theorem input_injective (p q : Domain hw0 hw1 (width := width))
    (h : input hw0 hw1 p = input hw0 hw1 q) : p = q := by
  revert h
  refine Quotient.inductionOn₂ p q ?_
  intro P Q h
  exact Quotient.sound h

/-- Every supplied original positive-time image is in this domain. -/
def fromTime (x : V) : Domain hw0 hw1 (width := width) :=
  Quotient.mk (inputSetoid hw0 hw1) ⟨T 1 x, F x, core hw0 hw1 x⟩

theorem input_fromTime (x : V) : input hw0 hw1 (fromTime hw0 hw1 x) = T 1 x := rfl

theorem action_fromTime (x : V) : action hw0 hw1 (fromTime hw0 hw1 x) = F x := rfl

/-- The original vacuum is an actual domain input, with zero value. -/
theorem vacuum_input : input hw0 hw1 (fromTime hw0 hw1 (unitState hw0 hw1 width)) =
    unitState hw0 hw1 width := completedUnit_fixed hw0 hw1 1

theorem vacuum_action : action hw0 hw1 (fromTime hw0 hw1 (unitState hw0 hw1 width)) = Z :=
  regularizedLog_unit_zero hw0 hw1

#print axioms GraphLimit
#print axioms core
#print axioms graph_time_pin
#print axioms graph_zero_input
#print axioms subtract
#print axioms graph_single_valued
#print axioms core_single_valued
#print axioms core_nonnegative
#print axioms core_symmetric
#print axioms diagonal
#print axioms Presentation
#print axioms inputSetoid
#print axioms Domain
#print axioms input
#print axioms action
#print axioms input_injective
#print axioms fromTime
#print axioms input_fromTime
#print axioms action_fromTime
#print axioms vacuum_input
#print axioms vacuum_action

end YMGap.Continuum.BF4WilsonAllNomeLogGraph
