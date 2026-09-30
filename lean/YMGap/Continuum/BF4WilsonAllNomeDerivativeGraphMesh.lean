/-
# Actual dyadic Taylor derivative on the original witnessed graph

Choose ONE graph approximant at an output-error tolerance depending only
on epsilon. The graph increment estimate controls the remainder difference
by 4*t^2 times this output error. That approximant's own core Taylor radius
then works for the graph point. No common radius or bounded preimages.

Source representatives are supplied, never selected from the quotient.
Time is the original T(1) unit. This does not identify the maximal generator
domain, self-adjointness, physical calibration or a continuum theory.
-/

import YMGap.Continuum.BF4WilsonAllNomeDerivativeGraphTimeBound

namespace YMGap.Continuum.BF4WilsonAllNomeDerivativeGraphMesh

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Constructive.NonnegativeDyadicTime (embed)
open YMGap.Constructive.DyadicTimeRationals (value)
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4WilsonAllNomeSeminorm (seminorm)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4WilsonAllNomeLinear
open YMGap.Continuum.BF4WilsonAllNomeBilinearTime
open YMGap.Continuum.BF4WilsonAllNomeDistance
open YMGap.Continuum.BF4WilsonAllNomeGraphDistance (dist_zero_right)
open YMGap.Continuum.BF4WilsonAllNomeCompletedPairingContinuity (completedInner_sub_left)
open YMGap.Continuum.BF4WilsonAllNomeCompletedRealScalar (completed_eq_of_pairings)
open YMGap.Continuum.BF4WilsonAllNomeDyadicSemigroup (meshAction action_sub)
open YMGap.Continuum.BF4WilsonAllNomeTimeAverages (smul_sub)
open YMGap.Continuum.BF4WilsonAllNomeDyadicDerivative (derivativeAction)
open YMGap.Continuum.BF4WilsonAllNomeDerivativeGraph
open YMGap.Continuum.BF4WilsonAllNomeDerivativeGraphTimeBound
open YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialContinuity
  (linearTolerance linearTolerance_pos linearTolerance_budget)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "D" => seminorm hw0 hw1 (width := width)
local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "T" => completedTime hw0 hw1
local notation "M" => meshAction hw0 hw1
local notation "A" => derivativeAction hw0 hw1
local notation "Sub" => completedSub hw0 hw1
local notation "Smul" => completedSmul hw0 hw1
local notation "Z" => completedZero hw0 hw1 width
local notation "dist" => completedDist hw0 hw1
local notation "Class" => Quotient.mk
  (CRealSeminormCompletion.SquaredSeminorm.completionSetoid
    (seminorm hw0 hw1 (width := width)))
local notation "rat" q:arg => Quotient.mk crealSetoid (ofQ' q)

theorem sub_sub_exchange (a b c d : V) :
    Sub (Sub a b) (Sub c d) = Sub (Sub a c) (Sub b d) := by
  apply completed_eq_of_pairings hw0 hw1
  intro z
  simp only [completedInner_sub_left]
  refine Quotient.inductionOn₂ (B a z) (B b z) ?_
  intro P Q
  refine Quotient.inductionOn₂ (B c z) (B d z) ?_
  intro R S
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.add (.add (.var 0) (.neg (.var 1))) (.neg (.add (.var 2) (.neg (.var 3)))))
      (.add (.add (.var 0) (.neg (.var 2))) (.neg (.add (.var 1) (.neg (.var 3)))))
      (by decide) (fun | 0 => P.approx n | 1 => Q.approx n | 2 => R.approx n | _ => S.approx n)))

def remainder (depth steps : Nat) (u v : V) : V :=
  Sub (Sub u (M depth steps u)) (Smul (value ⟨depth,steps⟩) v)

theorem remainder_sub (depth steps : Nat) (u v u' v' : V) :
    remainder hw0 hw1 depth steps (Sub u u') (Sub v v') =
      Sub (remainder hw0 hw1 depth steps u v) (remainder hw0 hw1 depth steps u' v') := by
  have ht (x y : V) : M depth steps (Sub x y) = Sub (M depth steps x) (M depth steps y) :=
    action_sub hw0 hw1 (embed ⟨depth,steps⟩) x y
  unfold remainder
  rw [ht,smul_sub,sub_sub_exchange hw0 hw1 u u' (M depth steps u) (M depth steps u'),
    sub_sub_exchange hw0 hw1 (Sub u (M depth steps u)) (Sub u' (M depth steps u'))
      (Smul (value ⟨depth,steps⟩) v) (Smul (value ⟨depth,steps⟩) v')]

/-- Uniform as t tends to zero, in the graph OUTPUT norm. -/
theorem remainder_graph_bound {u v : V} (G : GraphLimit hw0 hw1 u v)
    (depth steps : Nat) :
    RCle (B (remainder hw0 hw1 depth steps u v) (remainder hw0 hw1 depth steps u v))
      (RCscale 4 (RCscale (value ⟨depth,steps⟩*value ⟨depth,steps⟩) (B v v))) := by
  have hb := completedDist_triangle hw0 hw1 (Sub u (M depth steps u)) Z
    (Smul (value ⟨depth,steps⟩) v)
  rw [dist_zero_right,completedDist_symm hw0 hw1 Z,dist_zero_right,
    completedInner_smul_left,completedInner_smul_right,RCscale_RCscale] at hb
  have hi := graph_mesh_increment_bound hw0 hw1 G depth steps
  have h := RCle_trans hb (RCadd_le_add (RCadd_le_add hi hi)
    (RCadd_le_add (RCle_refl _) (RCle_refl _)))
  rw [four_copies] at h
  exact h

def tolerance (epsilon : Q') : Q' := linearTolerance 10 (by decide) epsilon

theorem tolerance_positive {epsilon : Q'} (he : (0 : Q') < epsilon) :
    (0 : Q') < tolerance epsilon := linearTolerance_pos 10 (by decide) he

private theorem ten_copies (r : RC) :
    RCadd (RCadd (RCscale 4 r) (RCscale 4 r)) (RCadd r r) = RCscale 10 r := by
  refine Quotient.inductionOn r ?_
  intro R
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.add (.add (.mul (.const 4) (.var 0)) (.mul (.const 4) (.var 0))) (.add (.var 0) (.var 0)))
      (.mul (.const 10) (.var 0)) (by decide) (fun _ => R.approx n)))

private theorem tolerance_budget (t epsilon : Q') (he : (0 : Q') < epsilon) :
    RCle (RCscale 10 (RCscale (t*t) (rat (tolerance epsilon))))
      (rat ((t*t)*epsilon)) := by
  apply leEv_le_ofQ'_of_approx_le
  intro _
  have h : Q'.eqv (10*((t*t)*tolerance epsilon)) ((t*t)*(10*tolerance epsilon)) :=
    poly_identity_of_normal_eq
      (.mul (.const 10) (.mul (.var 0) (.var 1)))
      (.mul (.var 0) (.mul (.const 10) (.var 1))) (by decide)
      (fun | 0 => t*t | _ => tolerance epsilon)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv h)
    (Q'.mul_le_mul_of_nonneg_left _ _ _ (linearTolerance_budget 10 (by decide) he)
      (SumOfSquares.q_mul_self_nonneg t))

/-- A single supplied graph approximant's actual core radius. -/
def radius {u v : V} (G : GraphLimit hw0 hw1 u v)
    (preimages : Nat → (D).Cauchy) (epsilon : Q') : Q' :=
  BF4WilsonAllNomeMeshDerivative.meshRadius hw0 hw1
    (preimages (G.modulus (tolerance epsilon))) (tolerance epsilon)

theorem radius_positive {u v : V} (G : GraphLimit hw0 hw1 u v)
    (preimages : Nat → (D).Cauchy) (epsilon : Q') :
    (0 : Q') < radius hw0 hw1 G preimages epsilon :=
  BF4WilsonAllNomeMeshDerivative.meshRadius_positive hw0 hw1 _ _

/-- Every dyadic increment below one computed radius differentiates at the
actual graph point, with no uniformity assumption on the source sequence. -/
theorem mesh_taylor_bound {u v : V} (G : GraphLimit hw0 hw1 u v)
    (preimages : Nat → (D).Cauchy) (hpin : ∀ n, Class (preimages n) = G.source n)
    (epsilon : Q') (he : (0 : Q') < epsilon) (depth steps : Nat)
    (ht : value ⟨depth,steps⟩ ≤ radius hw0 hw1 G preimages epsilon) :
    RCle (B (remainder hw0 hw1 depth steps u v) (remainder hw0 hw1 depth steps u v))
      (rat ((value ⟨depth,steps⟩*value ⟨depth,steps⟩)*epsilon)) := by
  let delta := tolerance epsilon
  let n := G.modulus delta
  let x : V := Class (preimages n)
  let c := RCscale (value ⟨depth,steps⟩*value ⟨depth,steps⟩) (rat delta)
  have hi : RCle (dist v (A x)) (rat delta) := by
    rw [completedDist_symm]
    dsimp only [x]
    rw [hpin n]
    exact (G.bound delta (tolerance_positive he) n (Nat.le_refl _)).2
  have H := subtract hw0 hw1 G (core hw0 hw1 x)
  have hd := remainder_graph_bound hw0 hw1 H depth steps
  rw [remainder_sub] at hd
  have hd' : RCle (dist (remainder hw0 hw1 depth steps u v)
      (remainder hw0 hw1 depth steps (T 1 x) (A x))) (RCscale 4 c) :=
    RCle_trans hd (RCscale_mono (by decide : (0 : Q') ≤ 4)
      (RCscale_mono (SumOfSquares.q_mul_self_nonneg _) hi))
  have hc : RCle (B (remainder hw0 hw1 depth steps (T 1 x) (A x))
      (remainder hw0 hw1 depth steps (T 1 x) (A x))) c :=
    BF4WilsonAllNomeMeshDerivative.mesh_taylor_bound hw0 hw1 (preimages n)
      delta (tolerance_positive he) depth steps ht
  have hb := completedDist_triangle hw0 hw1 (remainder hw0 hw1 depth steps u v)
    (remainder hw0 hw1 depth steps (T 1 x) (A x)) Z
  rw [dist_zero_right,dist_zero_right] at hb
  have hb' := RCle_trans hb (RCadd_le_add (RCadd_le_add hd' hd') (RCadd_le_add hc hc))
  rw [ten_copies] at hb'
  exact RCle_trans hb' (tolerance_budget (value ⟨depth,steps⟩) epsilon he)

def meshTaylorCertificate {u v : V} (G : GraphLimit hw0 hw1 u v)
    (preimages : Nat → (D).Cauchy) (hpin : ∀ n, Class (preimages n) = G.source n)
    (epsilon : Q') (he : (0 : Q') < epsilon) :
    Σ' r : Q', ((0 : Q') < r) ×'
      (∀ depth steps, value ⟨depth,steps⟩ ≤ r →
        RCle (B (remainder hw0 hw1 depth steps u v) (remainder hw0 hw1 depth steps u v))
          (rat ((value ⟨depth,steps⟩*value ⟨depth,steps⟩)*epsilon))) :=
  ⟨radius hw0 hw1 G preimages epsilon,radius_positive hw0 hw1 G preimages epsilon,
    mesh_taylor_bound hw0 hw1 G preimages hpin epsilon he⟩

#print axioms sub_sub_exchange
#print axioms remainder
#print axioms remainder_sub
#print axioms remainder_graph_bound
#print axioms tolerance
#print axioms tolerance_positive
#print axioms radius
#print axioms radius_positive
#print axioms mesh_taylor_bound
#print axioms meshTaylorCertificate

end YMGap.Continuum.BF4WilsonAllNomeDerivativeGraphMesh
