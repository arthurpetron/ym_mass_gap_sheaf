/-
# Positive symmetric form on the witnessed original derivative graph

Pairing continuity passes through the supplied graph convergence moduli.
Only limiting inputs, outputs and nearby images require norm bounds;
no representative or uniform norm bound for preimages is selected.
This concerns the actual A-range derivative graph, not the log-series
graph. It does not assert self-adjointness or physical calibration.
-/

import YMGap.Continuum.BF4WilsonAllNomeDerivativeGraph
import YMGap.Continuum.BF4WilsonAllNomeCompletedPairingContinuity

namespace YMGap.Continuum.BF4WilsonAllNomeDerivativeGraphForm

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4WilsonAllNomeSeminorm (seminorm)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4WilsonAllNomeLinear
open YMGap.Continuum.BF4WilsonAllNomeLinearLaws
open YMGap.Continuum.BF4WilsonAllNomeDistance
open YMGap.Continuum.BF4WilsonAllNomeGraphDistance (dist_zero_right)
open YMGap.Continuum.BF4WilsonAllNomeDyadicDerivative
open YMGap.Continuum.BF4WilsonAllNomeDerivativeGraph
open YMGap.Continuum.BF4WilsonAllNomeCompletedPairingContinuity (pairing_close)
open YMGap.Continuum.BF4ExactSlabPlaquettePairingContinuity
  (pairingTolerance pairingTolerance_pos)
open YMGap.Continuum.CRealSeminormPairingCompletion
  (normCeiling normCeiling_nonnegative completedInner_diagonal_le_normCeiling)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "D" => seminorm hw0 hw1 (width := width)
local notation "P" => pairingData hw0 hw1 (width := width)
local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "T" => completedTime hw0 hw1
local notation "A" => derivativeAction hw0 hw1
local notation "dist" => completedDist hw0 hw1
local notation "Z" => completedZero hw0 hw1 width
local notation "rat" q => Quotient.mk crealSetoid (ofQ' q)

private theorem norm_ceiling (x : V) :
    ∃ c : Q', (0 : Q') ≤ c ∧ RCle (B x x) (rat c) := by
  refine Quotient.inductionOn x ?_
  intro X
  exact ⟨normCeiling P X, normCeiling_nonnegative P X,
    completedInner_diagonal_le_normCeiling P X⟩

private theorem rat_four_sum (a b : Q') :
    RCadd (RCadd (rat a) (rat a)) (RCadd (rat b) (rat b)) =
      rat ((a+a)+(b+b)) :=
  Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.eqv_refl _))

private theorem rat_zero_add (a : Q') : RCadd RCzero (rat a) = rat a :=
  Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun _ =>
    Q'.eqv_of_eq (Q'.zero_add' a)))

private theorem rat_two_halves (a : RC) (e : Q') :
    RCadd (RCadd a (rat (HalfPow.half*e))) (rat (HalfPow.half*e)) =
      RCadd a (rat e) := by
  refine Quotient.inductionOn a ?_
  intro X
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun _ =>
    Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv _ _ _)
      (Q'.add_eqv_congr_left _ _ _ (ExpNeg.two_halves e))))

/-- Explicit rational cap for one graph-pairing comparison. -/
def graphPairingCap (cx cv : Q') : Q' := Q'.max' cx ((1+1)+(cv+cv))

theorem graphPairingCap_nonnegative (cx cv : Q') (hcx : (0 : Q') ≤ cx) :
    (0 : Q') ≤ graphPairingCap cx cv :=
  Q'.le_trans' _ _ _ hcx (Q'.le_max'_left _ _)

/-- A computed all-tail pairing cutoff from supplied image-norm caps and
the two graph moduli; no existential modulus is erased. -/
def graphPairingModulus {x u y v : V}
    (G : GraphLimit hw0 hw1 x u) (H : GraphLimit hw0 hw1 y v)
    (cx cv : Q') (hcx : (0 : Q') ≤ cx) (epsilon : Q') : Nat :=
  let cap := graphPairingCap cx cv
  let delta := pairingTolerance cap (graphPairingCap_nonnegative cx cv hcx) epsilon
  max (G.modulus delta) (max (H.modulus delta) (H.modulus 1))

/-- Pairing continuity along two witnessed graph sequences. The cap comes
from supplied norm bounds for the limiting input and output, plus the
output's distance-one tail. -/
theorem graph_pairing_close {x u y v : V}
    (G : GraphLimit hw0 hw1 x u) (H : GraphLimit hw0 hw1 y v)
    (cx cv : Q') (hcx0 : (0 : Q') ≤ cx)
    (hcx : RCle (B x x) (rat cx)) (hcv : RCle (B v v) (rat cv))
    (epsilon : Q') (he : (0 : Q') < epsilon)
    (n : Nat) (hn : graphPairingModulus hw0 hw1 G H cx cv hcx0 epsilon ≤ n) :
      RCle (B (T 1 (G.source n)) (A (H.source n)))
        (RCadd (B x v) (rat epsilon)) ∧
      RCle (B x v)
        (RCadd (B (T 1 (G.source n)) (A (H.source n))) (rat epsilon)) := by
  let cap := graphPairingCap cx cv
  have hcap : (0 : Q') ≤ cap := graphPairingCap_nonnegative cx cv hcx0
  let delta := pairingTolerance cap hcap epsilon
  have hd : (0 : Q') < delta := pairingTolerance_pos cap hcap he
  change max (G.modulus delta) (max (H.modulus delta) (H.modulus 1)) ≤ n at hn
  have hG := (G.bound delta hd n
    (Nat.le_trans (Nat.le_max_left _ _) hn)).1
  have hH := (H.bound delta hd n
    (Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) hn)).2
  have hH1 := (H.bound 1 (by decide) n
    (Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) hn)).2
  have hxn : RCle (B x x) (rat cap) :=
    RCle_trans hcx (leEv_le_ofQ'_of_approx_le (fun _ => Q'.le_max'_left _ _))
  have htri := completedDist_triangle hw0 hw1 (A (H.source n)) v Z
  rw [dist_zero_right, dist_zero_right] at htri
  have hnear : RCle (B (A (H.source n)) (A (H.source n)))
      (rat ((1+1)+(cv+cv))) := by
    have h := RCle_trans htri
      (RCadd_le_add (RCadd_le_add hH1 hH1) (RCadd_le_add hcv hcv))
    rwa [rat_four_sum] at h
  have hyn : RCle (B (A (H.source n)) (A (H.source n))) (rat cap) :=
    RCle_trans hnear (leEv_le_ofQ'_of_approx_le (fun _ => Q'.le_max'_right _ _))
  exact pairing_close hw0 hw1 _ _ _ _ cap hcap epsilon he hG hH hyn hxn

/-- The closure of the actual positive-time graph has nonnegative form.
This uses no bound on its source sequence and makes no self-adjointness or
continuous-time claim. -/
theorem graph_nonnegative {input output : V}
    (G : GraphLimit hw0 hw1 input output) :
    RCnonneg (B input output) := by
  obtain ⟨cx, hcx0, hcx⟩ := norm_ceiling hw0 hw1 input
  obtain ⟨cv, _, hcv⟩ := norm_ceiling hw0 hw1 output
  apply RationalScalarTwoSidedError.le_of_all_errors
  intro epsilon he
  let n := graphPairingModulus hw0 hw1 G G cx cv hcx0 epsilon
  have h := (graph_pairing_close hw0 hw1 G G cx cv hcx0 hcx hcv
    epsilon he n (Nat.le_refl n)).1
  have hp := core_nonnegative hw0 hw1 (G.source n)
  exact RCle_trans hp h

/-- Symmetry passes to two witnessed graph limits using one common tail
index for the two pairing comparisons. -/
theorem graph_symmetric {x u y v : V}
    (G : GraphLimit hw0 hw1 x u) (H : GraphLimit hw0 hw1 y v) :
    B u y = B x v := by
  obtain ⟨cx, hcx0, hcx⟩ := norm_ceiling hw0 hw1 x
  obtain ⟨cv, _, hcv⟩ := norm_ceiling hw0 hw1 v
  obtain ⟨cy, hcy0, hcy⟩ := norm_ceiling hw0 hw1 y
  obtain ⟨cu, _, hcu⟩ := norm_ceiling hw0 hw1 u
  have hxy : RCle (B x v) (B y u) := by
    apply RationalScalarTwoSidedError.le_of_all_errors
    intro epsilon he
    let d := HalfPow.half*epsilon
    have hd : (0 : Q') < d := ExpNeg.half_mul_pos epsilon he
    let N := graphPairingModulus hw0 hw1 G H cx cv hcx0 d
    let M := graphPairingModulus hw0 hw1 H G cy cu hcy0 d
    let n := max N M
    have h1 := (graph_pairing_close hw0 hw1 G H cx cv hcx0 hcx hcv
      d hd n (Nat.le_max_left _ _)).2
    have h2 := (graph_pairing_close hw0 hw1 H G cy cu hcy0 hcy hcu
      d hd n (Nat.le_max_right _ _)).1
    have hfinite : B (T 1 (G.source n)) (A (H.source n)) =
        B (T 1 (H.source n)) (A (G.source n)) := by
      rw [← core_symmetric hw0 hw1 (G.source n) (H.source n),
        completedInner_symm hw0 hw1 (A (G.source n)) (T 1 (H.source n))]
    rw [hfinite] at h1
    have hsum := RCle_trans h1
      (RCadd_le_add h2 (RCle_refl (rat d)))
    rwa [rat_two_halves] at hsum
  have hyx : RCle (B y u) (B x v) := by
    apply RationalScalarTwoSidedError.le_of_all_errors
    intro epsilon he
    let d := HalfPow.half*epsilon
    have hd : (0 : Q') < d := ExpNeg.half_mul_pos epsilon he
    let N := graphPairingModulus hw0 hw1 G H cx cv hcx0 d
    let M := graphPairingModulus hw0 hw1 H G cy cu hcy0 d
    let n := max N M
    have h1 := (graph_pairing_close hw0 hw1 H G cy cu hcy0 hcy hcu
      d hd n (Nat.le_max_right _ _)).2
    have h2 := (graph_pairing_close hw0 hw1 G H cx cv hcx0 hcx hcv
      d hd n (Nat.le_max_left _ _)).1
    have hfinite : B (T 1 (H.source n)) (A (G.source n)) =
        B (T 1 (G.source n)) (A (H.source n)) := by
      rw [← core_symmetric hw0 hw1 (G.source n) (H.source n),
        completedInner_symm hw0 hw1 (A (G.source n)) (T 1 (H.source n))]
    rw [hfinite] at h1
    have hsum := RCle_trans h1
      (RCadd_le_add h2 (RCle_refl (rat d)))
    rwa [rat_two_halves] at hsum
  exact (completedInner_symm hw0 hw1 u y).trans
    (RCle_antisymm hyx hxy)

/-- Positivity on the actual quotient domain's original carrier input. -/
theorem action_nonnegative (p : Domain hw0 hw1 (width := width)) :
    RCnonneg (B (input hw0 hw1 p) (action hw0 hw1 p)) := by
  refine Quotient.inductionOn p ?_
  intro U
  exact graph_nonnegative hw0 hw1 U.2.2

/-- Symmetry of the closed witnessed graph on its quotient domain. -/
theorem action_symmetric (p q : Domain hw0 hw1 (width := width)) :
    B (action hw0 hw1 p) (input hw0 hw1 q) =
      B (input hw0 hw1 p) (action hw0 hw1 q) := by
  refine Quotient.inductionOn₂ p q ?_
  intro U W
  exact graph_symmetric hw0 hw1 U.2.2 W.2.2

#print axioms graphPairingCap
#print axioms graphPairingCap_nonnegative
#print axioms graphPairingModulus
#print axioms graph_pairing_close
#print axioms graph_nonnegative
#print axioms graph_symmetric
#print axioms action_nonnegative
#print axioms action_symmetric

end YMGap.Continuum.BF4WilsonAllNomeDerivativeGraphForm
