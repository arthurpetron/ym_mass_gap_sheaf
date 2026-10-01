/-
# Coercivity below the original sector form margin

For a rational shift strictly below the fixed-nome, fixed-width core margin,
the original derivative graph remains coercive on its witnessed vacuum
complement. The norm estimate and uniqueness concern the existing domain and
its original squared norm; no physical OS or uniform scaling claim is made.
-/

import YMGap.Continuum.BF4WilsonAllNomeSectorResolventGap
import YMGap.Continuum.BF4WilsonAllNomeDerivativeGraphLinear
import YMGap.Continuum.ClusteringImpliesGap

namespace YMGap.Continuum.BF4WilsonAllNomeSectorSubgapInjective

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeLinear
open YMGap.Continuum.BF4WilsonAllNomeLinearLaws
open YMGap.Continuum.BF4WilsonAllNomeBilinearTime
open YMGap.Continuum.BF4WilsonAllNomeCompletedPairingContinuity
open YMGap.Continuum.BF4WilsonAllNomeDistance
open YMGap.Continuum.BF4WilsonAllNomeDerivativeGraph
open YMGap.Continuum.BF4WilsonAllNomeDerivativeGraphGap (graph_form_gap)
open YMGap.Continuum.BF4WilsonAllNomeLogCoreGap (coreMargin)
open YMGap.Continuum.BF4WilsonAllNomeSectorDerivative (DomainPoint graph)
open YMGap.Continuum.BF4WilsonAllNomeSectorResolvent (shifted)
open YMGap.Continuum.BF4WilsonAllNomeSectorResolventGap (norm_from_coercivity)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "U" => unitState hw0 hw1 width
local notation "A" => completedAdd hw0 hw1
local notation "S" => completedSmul hw0 hw1
local notation "N" => completedNeg hw0 hw1
local notation "Sub" => completedSub hw0 hw1
local notation "Z" => completedZero hw0 hw1 width
local notation "Point" => DomainPoint hw0 hw1 (width := width)

private theorem neg_smul (c : Q') (x : V) : N (S c x) = S c (N x) := by
  unfold completedNeg
  rw [completedSmul_mul, completedSmul_mul]
  exact completedSmul_congr hw0 hw1 (Q'.mul_comm_eqv (-1) c) x

private theorem neg_add (x y : V) : N (A x y) = A (N x) (N y) :=
  completedSmul_add hw0 hw1 (-1) x y

private theorem add_swap_middle (a b c e : V) :
    A (A a b) (A c e) = A (A a c) (A b e) := by
  rw [completedAdd_assoc hw0 hw1 a b (A c e)]
  have h : A b (A c e) = A c (A b e) := by
    calc
      A b (A c e) = A (A b c) e := (completedAdd_assoc hw0 hw1 b c e).symm
      _ = A (A c b) e := congrArg (fun t => A t e) (completedAdd_comm hw0 hw1 b c)
      _ = A c (A b e) := completedAdd_assoc hw0 hw1 c b e
  rw [h]
  exact (completedAdd_assoc hw0 hw1 a c (A b e)).symm

private theorem shift_sub (c : Q') (x y u v : V) :
    Sub (A (S c x) u) (A (S c y) v) =
      A (S c (Sub x y)) (Sub u v) := by
  change A (A (S c x) u) (N (A (S c y) v)) =
    A (S c (A x (N y))) (A u (N v))
  rw [neg_add]
  rw [add_swap_middle hw0 hw1 (S c x) u (N (S c y)) (N v)]
  rw [neg_smul, completedSmul_add]

private theorem shifted_graph_coercivity (a : Q')
    (x y : V) (G : GraphLimit hw0 hw1 x y)
    (hx : B U x = RCzero) :
    RCle (RCscale (coreMargin hw0 hw1 width-a) (B x x))
      (B x (A (S (-a) x) y)) := by
  let delta := coreMargin hw0 hw1 width
  have hsum : RCscale (delta-a) (B x x) =
      RCadd (RCscale (-a) (B x x)) (RCscale delta (B x x)) := by
    refine Quotient.inductionOn (B x x) ?_
    intro X
    exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
      poly_identity_of_normal_eq
        (.mul (.add (.var 0) (.neg (.var 1))) (.var 2))
        (.add (.mul (.neg (.var 1)) (.var 2)) (.mul (.var 0) (.var 2)))
        (by decide) (fun | 0 => delta | 1 => a | _ => X.approx n)))
  change RCle (RCscale (delta-a) (B x x))
    (B x (A (S (-a) x) y))
  rw [hsum, completedInner_add_right, completedInner_smul_right]
  exact RCadd_le_add (RCle_refl _) (graph_form_gap hw0 hw1 G hx)

/-- The original negative-shifted domain form remains coercive whenever the
shift lies strictly below the existing core margin. -/
theorem coercivity (a : Q') (_ha : a < coreMargin hw0 hw1 width)
    (p : Point) (hp : B U p.input.val = RCzero) :
    RCle (RCscale (coreMargin hw0 hw1 width-a)
      (B p.input.val p.input.val))
      (B p.input.val (shifted hw0 hw1 (-a) p).val) := by
  exact shifted_graph_coercivity hw0 hw1 a p.input.val p.output.val
    (graph hw0 hw1 p) hp

/-- Square-completion gives the sharp inverse squared-norm coefficient on
the original centered domain, without dividing by an unknown norm. -/
theorem norm_bound (a : Q') (ha : a < coreMargin hw0 hw1 width)
    (p : Point) (hp : B U p.input.val = RCzero) :
    let d := coreMargin hw0 hw1 width-a
    RCle (B p.input.val p.input.val)
      (RCscale
        (Q'.recipPos d (ClusteringImpliesGap.sub_pos_of_lt ha) *
          Q'.recipPos d (ClusteringImpliesGap.sub_pos_of_lt ha))
        (B (shifted hw0 hw1 (-a) p).val
          (shifted hw0 hw1 (-a) p).val)) := by
  dsimp only
  exact norm_from_coercivity hw0 hw1 _
    (ClusteringImpliesGap.sub_pos_of_lt ha) _ _
    (coercivity hw0 hw1 a ha p hp)

/-- Equal negative-shifted values determine equal centered domain inputs,
but do not identify their presentation witnesses. -/
theorem input_injective (a : Q') (ha : a < coreMargin hw0 hw1 width)
    (p q : Point)
    (hp : B U p.input.val = RCzero) (hq : B U q.input.val = RCzero)
    (hshift : (shifted hw0 hw1 (-a) p).val =
      (shifted hw0 hw1 (-a) q).val) :
    p.input.val = q.input.val := by
  let du := Sub p.input.val q.input.val
  let dv := Sub p.output.val q.output.val
  have G : GraphLimit hw0 hw1 du dv :=
    subtract hw0 hw1 (graph hw0 hw1 p) (graph hw0 hw1 q)
  have hu : B U du = RCzero := by
    change B U (Sub p.input.val q.input.val) = RCzero
    rw [completedInner_sub_right, hp, hq]
    exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
      (fun _ => (by decide : Q'.eqv ((0 : Q') + -0) 0)))
  have hz : A (S (-a) du) dv = Z := by
    rw [← shift_sub hw0 hw1 (-a) p.input.val q.input.val p.output.val q.output.val]
    change Sub (shifted hw0 hw1 (-a) p).val
      (shifted hw0 hw1 (-a) q).val = Z
    rw [hshift, completedSub_self]
  have hc := shifted_graph_coercivity hw0 hw1 a du dv G hu
  rw [hz] at hc
  have hd : (0 : Q') < coreMargin hw0 hw1 width-a :=
    ClusteringImpliesGap.sub_pos_of_lt ha
  have hn := norm_from_coercivity hw0 hw1 _ hd du Z hc
  rw [completedInner_zero_right, RCscale_RCzero] at hn
  have hdist : completedDist hw0 hw1 p.input.val q.input.val = RCzero :=
    RCle_antisymm hn (completedDist_nonnegative hw0 hw1 p.input.val q.input.val)
  exact (completedDist_zero_iff hw0 hw1 p.input.val q.input.val).mp hdist

#print axioms coercivity
#print axioms norm_bound
#print axioms input_injective

end YMGap.Continuum.BF4WilsonAllNomeSectorSubgapInjective
