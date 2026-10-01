/-
# Positive shifts are injective on the witnessed original time sector

The positivity of the existing derivative graph makes every strictly
positive rational shift injective on its sector domain. This is a statement
about the original fixed-nome, fixed-width completed carrier; it does not
construct a resolvent or identify a physical Hamiltonian.
-/

import YMGap.Continuum.BF4WilsonAllNomeSectorDerivative
import YMGap.Continuum.BF4WilsonAllNomeDerivativeGraphLinear

namespace YMGap.Continuum.BF4WilsonAllNomeSectorShiftInjective

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeLinear
open YMGap.Continuum.BF4WilsonAllNomeLinearLaws
open YMGap.Continuum.BF4WilsonAllNomeBilinearTime
open YMGap.Continuum.BF4WilsonAllNomeDistance
open YMGap.Continuum.BF4WilsonAllNomeDerivativeGraph
open YMGap.Continuum.BF4WilsonAllNomeDerivativeGraphForm (graph_nonnegative)
open YMGap.Continuum.BF4WilsonAllNomeSectorDerivative (DomainPoint graph output_congr)
open YMGap.Continuum.RCSignedPairBudget (scale_congr)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "A" => completedAdd hw0 hw1
local notation "S" => completedSmul hw0 hw1
local notation "N" => completedNeg hw0 hw1
local notation "Sub" => completedSub hw0 hw1
local notation "d" => completedDist hw0 hw1
local notation "Z" => completedZero hw0 hw1 width

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

private theorem add_zero (a : RC) : RCadd a RCzero = a := by
  refine Quotient.inductionOn a ?_
  intro X
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.eqv_of_eq (Q'.add_zero' (X.approx n))))

private theorem add_le_of_nonnegative {a b : RC} (hb : RCnonneg b) :
    RCle a (RCadd a b) := by
  have h := RCadd_le_add (RCle_refl a) hb
  rw [add_zero] at h
  exact h

/-- A positive rational shift of the actual witnessed derivative graph has
at most one sector input for each value. -/
theorem input_injective (lambda : Q') (hl : (0 : Q') < lambda)
    (p q : DomainPoint hw0 hw1 (width := width))
    (h : A (S lambda p.input.val) p.output.val =
      A (S lambda q.input.val) q.output.val) :
    p.input.val = q.input.val := by
  let du := Sub p.input.val q.input.val
  let dv := Sub p.output.val q.output.val
  have G : GraphLimit hw0 hw1 du dv :=
    subtract hw0 hw1 (graph hw0 hw1 p) (graph hw0 hw1 q)
  have hshift : A (S lambda du) dv = Z := by
    rw [← shift_sub hw0 hw1 lambda p.input.val q.input.val p.output.val q.output.val]
    rw [h, completedSub_self]
  have hform : RCnonneg (B du dv) := graph_nonnegative hw0 hw1 G
  have hpair : RCadd (RCscale lambda (B du du)) (B du dv) = RCzero := by
    have hh := congrArg (B du) hshift
    rw [completedInner_add_right, completedInner_smul_right,
      completedInner_zero_right] at hh
    exact hh
  have hscaled : RCle (RCscale lambda (B du du)) RCzero := by
    rw [← hpair]
    exact add_le_of_nonnegative hform
  have hcancel := RCscale_mono (Q'.le_of_lt (Q'.recipPos_pos lambda hl)) hscaled
  have hrecip : Q'.eqv ((Q'.recipPos lambda hl) * lambda) 1 :=
    Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) (Q'.mul_recipPos_eqv lambda hl)
  rw [RCscale_RCscale, RCscale_RCzero,
    scale_congr hrecip, RCscale_one] at hcancel
  have hdist : d p.input.val q.input.val = RCzero :=
    RCle_antisymm hcancel (completedDist_nonnegative hw0 hw1 p.input.val q.input.val)
  exact (completedDist_zero_iff hw0 hw1 p.input.val q.input.val).mp hdist

/-- Equality of a positive shifted value also fixes the derivative output. -/
theorem output_injective (lambda : Q') (hl : (0 : Q') < lambda)
    (p q : DomainPoint hw0 hw1 (width := width))
    (h : A (S lambda p.input.val) p.output.val =
      A (S lambda q.input.val) q.output.val) :
    p.output.val = q.output.val :=
  output_congr hw0 hw1 p q (input_injective hw0 hw1 lambda hl p q h)

#print axioms input_injective
#print axioms output_injective

end YMGap.Continuum.BF4WilsonAllNomeSectorShiftInjective
