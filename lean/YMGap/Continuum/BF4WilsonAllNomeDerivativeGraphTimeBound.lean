/-
# Original increments controlled by the witnessed derivative graph output

The core increment estimate passes through simultaneous graph convergence.
Its time-squared coefficient is retained. The only continuity bounds used
in this passage concern the two graph coordinates, never their preimages.
This is the uniform-in-small-time estimate needed to transfer the actual
Taylor theorem to graph limits. It is not physical-time calibration.
-/

import YMGap.Continuum.BF4WilsonAllNomeDerivativeIncrement
import YMGap.Continuum.BF4WilsonAllNomeDerivativeGraphLinear
import YMGap.Continuum.BF4WilsonAllNomeNormLimitOrder

namespace YMGap.Continuum.BF4WilsonAllNomeDerivativeGraphTimeBound

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Constructive.DyadicTimeRationals (value)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4WilsonAllNomeLinear
open YMGap.Continuum.BF4WilsonAllNomeBilinearTime
open YMGap.Continuum.BF4WilsonAllNomeDistance
open YMGap.Continuum.BF4WilsonAllNomeGraphDistance
open YMGap.Continuum.BF4WilsonAllNomeDyadicEnergy (mesh_distance_bound)
open YMGap.Continuum.BF4WilsonAllNomeDyadicSemigroup (meshAction)
open YMGap.Continuum.BF4WilsonAllNomeDyadicDerivative (derivativeAction)
open YMGap.Continuum.BF4WilsonAllNomeDerivativeGraph
open YMGap.Continuum.BF4WilsonAllNomeDerivativeGraphLinear (completedDist_smul)
open YMGap.Continuum.BF4WilsonAllNomeDerivativeIncrement (mesh_increment_bound)
open YMGap.Continuum.BF4WilsonAllNomeNormLimitOrder (norm_limit_order)
open YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialContinuity
  (linearTolerance linearTolerance_pos linearTolerance_budget)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "T" => completedTime hw0 hw1
local notation "M" => meshAction hw0 hw1
local notation "A" => derivativeAction hw0 hw1
local notation "Sub" => completedSub hw0 hw1
local notation "Smul" => completedSmul hw0 hw1
local notation "d" => completedDist hw0 hw1
local notation "rat" q:arg => Quotient.mk crealSetoid (ofQ' q)

theorem four_copies (r : RC) :
    RCadd (RCadd r r) (RCadd r r) = RCscale 4 r := by
  refine Quotient.inductionOn r ?_
  intro R
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    RingNormaliser.poly_identity_of_normal_eq
      (.add (.add (.var 0) (.var 0)) (.add (.var 0) (.var 0)))
      (.mul (.const 4) (.var 0)) (by decide) (fun _ => R.approx n)))

theorem scaled_tolerance {c e : Q'} (hc : (0 : Q') ≤ c) (he : (0 : Q') < e) :
    RCle (RCscale c (rat (linearTolerance c hc e))) (rat e) :=
  leEv_le_ofQ'_of_approx_le (fun _ => linearTolerance_budget c hc he)

/-- Fixed-mesh convergence of the input increment uses only the graph input. -/
def incrementModulus {u v : V} (G : GraphLimit hw0 hw1 u v) (e : Q') : Nat :=
  G.modulus (linearTolerance 4 (by decide) e)

theorem increment_close {u v : V} (G : GraphLimit hw0 hw1 u v)
    (depth steps : Nat) (e : Q') (he : (0 : Q') < e)
    (n : Nat) (hn : incrementModulus hw0 hw1 G e ≤ n) :
    RCle (d (Sub (T 1 (G.source n)) (M depth steps (T 1 (G.source n))))
      (Sub u (M depth steps u))) (rat e) := by
  have h := (G.bound _ (linearTolerance_pos 4 (by decide) he) n hn).1
  have hm := RCle_trans (mesh_distance_bound hw0 hw1 depth steps _ _) h
  have hb := RCle_trans (completedDist_sub_le hw0 hw1 _ _ _ _)
    (RCadd_le_add (RCadd_le_add h h) (RCadd_le_add hm hm))
  rw [four_copies] at hb
  exact RCle_trans hb (scaled_tolerance (by decide) he)

/-- The whole witnessed graph retains the original time-squared bound. -/
theorem graph_mesh_increment_bound {u v : V} (G : GraphLimit hw0 hw1 u v)
    (depth steps : Nat) :
    RCle (d u (M depth steps u))
      (RCscale (value ⟨depth,steps⟩*value ⟨depth,steps⟩) (B v v)) := by
  let t := value ⟨depth,steps⟩
  let c := t*t
  have hc : (0 : Q') ≤ c := SumOfSquares.q_mul_self_nonneg t
  let xs := fun n => Sub (T 1 (G.source n)) (M depth steps (T 1 (G.source n)))
  let ys := fun n => Smul t (A (G.source n))
  let mx := incrementModulus hw0 hw1 G
  let my := fun e => G.modulus (linearTolerance c hc e)
  have bx : ∀ e, (0 : Q') < e → ∀ n, mx e ≤ n →
      RCle (d (xs n) (Sub u (M depth steps u))) (rat e) :=
    increment_close hw0 hw1 G depth steps
  have by' : ∀ e, (0 : Q') < e → ∀ n, my e ≤ n →
      RCle (d (ys n) (Smul t v)) (rat e) := by
    intro e he n hn
    have h := (G.bound _ (linearTolerance_pos c hc he) n hn).2
    change RCle (d (Smul t (A (G.source n))) (Smul t v)) (rat e)
    rw [completedDist_smul]
    exact RCle_trans (RCscale_mono hc h) (scaled_tolerance hc he)
  have h := norm_limit_order hw0 hw1 xs ys (Sub u (M depth steps u)) (Smul t v)
    mx my bx by' (by
      intro n
      dsimp only [xs,ys]
      rw [completedInner_smul_left,completedInner_smul_right,RCscale_RCscale]
      exact mesh_increment_bound hw0 hw1 depth steps (G.source n))
  rw [completedInner_smul_left,completedInner_smul_right,RCscale_RCscale] at h
  exact h

#print axioms four_copies
#print axioms scaled_tolerance
#print axioms incrementModulus
#print axioms increment_close
#print axioms graph_mesh_increment_bound

end YMGap.Continuum.BF4WilsonAllNomeDerivativeGraphTimeBound
