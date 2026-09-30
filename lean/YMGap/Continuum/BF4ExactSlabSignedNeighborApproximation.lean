/-
# Energy-relative polynomial approximation of the original signed neighbor sum

The existing kernel polynomials give a finite rational approximation to
the ACTUAL signed neighboring residual Gram sum. For residual relative
error delta, the total error is at most 50*(delta+delta^2/2)*E(p), using
both original incidence bounds of 25. No volume multiplier is introduced.
The cutoff depends on nome and delta, not polynomial degree or extent.

The signed finite value is retained; it is not asserted positive. This
proves approximation error control, not a useful collective lower margin,
an efficient evaluation algorithm, scaling uniformity or an OS mass gap.
-/

import YMGap.Continuum.BF4ExactSlabStarEnergyRelativeApproximation
import YMGap.Continuum.BF4ExactSlabFullActionScalar
import YMGap.Continuum.BF4ExactSlabSignedNeighborEnergy
import YMGap.Continuum.GNSPairApproximationError
import YMGap.Continuum.RCDirectedPairError

namespace YMGap.Continuum.BF4ExactSlabSignedNeighborApproximation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.GNSProjectionSweep
open YMGap.Continuum.GNSProjectionSweep.Family
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabStarFullActionProbe
open YMGap.Continuum.BF4ExactSlabConditionalSweep
open YMGap.Continuum.BF4ExactSlabConditionalSweepEnergy
open YMGap.Continuum.BF4ExactSlabEightLayerCone
open YMGap.Continuum.BF4ExactSlabSignedNeighborEnergy
open YMGap.Continuum.BF4ExactSlabFullActionScalar
open YMGap.Continuum.BF4ExactSlabStarPolynomialResidual
open YMGap.Continuum.BF4ExactSlabStarResidualApproximation
open YMGap.Continuum.BF4ExactSlabStarEnergyRelativeApproximation
open YMGap.Continuum.GNSPairApproximationError
open YMGap.Continuum.RCDirectedPairError

private instance (extent : Nat) : DecidableEq (PhysicalLink extent) :=
  inferInstanceAs (DecidableEq {link : Z4Link //
    link ∈ Z4HalfTimeReflectionGeometry.boundaryCompleteSlabLinks extent})

private def rat (q : Q') : RC := Quotient.mk crealSetoid (ofQ' q)

private theorem neg_neg (a : RC) : RCneg (RCneg a) = a := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun k => Q'.neg_neg_eqv (A.approx k)))

private def qsum {A : Type} : List A → (A → Q') → Q'
  | [], _ => 0
  | i :: rest, f => f i + qsum rest f

private theorem rat_add (a b : Q') : rat (a+b) = RCadd (rat a) (rat b) :=
  Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.eqv_refl _))

private theorem qsum_pin {A : Type} (xs : List A) (f : A → Q') :
    rat (qsum xs f) = sumOn xs (fun i => rat (f i)) := by
  induction xs with
  | nil => rfl
  | cons i rest ih => simp only [qsum, sumOn, rat_add, ih]

/-- Exactly the ordered distinct neighboring pairs in the original sum. -/
def offNeighbor {extent : Nat} (i j : PhysicalLink extent) : Bool :=
  if i = j then false else adjacent i j

private theorem filter_mask_length_le {A : Type} (p : A → Prop) [DecidablePred p]
    (q : A → Bool) (xs : List A) :
    (xs.filter (fun i => if p i then false else q i)).length ≤ (xs.filter q).length := by
  induction xs with
  | nil => exact Nat.le_refl 0
  | cons i rest ih =>
      by_cases hp : p i <;> cases hq : q i <;>
        simp only [List.filter_cons, hp, hq,
          Bool.false_eq_true, if_false, if_true, List.length_cons] <;> omega

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K extent : Nat) (hK : headCutoff w ≤ K)

local notation "F" => fullData hw0 hw1 K extent hK
local notation "P" => projections hw0 hw1 K extent hK

/-- Existing polynomial conditional-kernel approximation on the original
full-action carrier, without truncating its input polynomial degree. -/
def residualPolynomial (i : PhysicalLink extent) (p : (F).V) (n : Nat) : (F).V :=
  polynomialResidual hw0 hw1 K extent hK i
    (approximationSeed hw0 hw1 K extent hK i p n)

/-- A finite rational signed Gram sum with the SAME full-action pairing.
The definition makes no claim that direct evaluation is computationally cheap. -/
def neighborValue (p : (F).V) (n : Nat) : Q' :=
  qsum (schedule extent) (fun i => qsum (schedule extent) (fun j =>
    if offNeighbor i j then
      (F).B (residualPolynomial hw0 hw1 K extent hK i p n)
        (residualPolynomial hw0 hw1 K extent hK j p n) else 0))

theorem neighborValue_pin (p : (F).V) (n : Nat) :
    rat (neighborValue hw0 hw1 K extent hK p n) =
      pairSum (schedule extent) offNeighbor (fun i j =>
        (F).cinnerCompl (embedV F (residualPolynomial hw0 hw1 K extent hK i p n))
          (embedV F (residualPolynomial hw0 hw1 K extent hK j p n))) := by
  unfold neighborValue pairSum
  rw [qsum_pin]
  apply congrArg (sumOn (schedule extent))
  funext i
  rw [qsum_pin]
  apply congrArg (sumOn (schedule extent))
  funext j
  cases h : offNeighbor i j with
  | false => simp only [h, Bool.false_eq_true, if_false]; rfl
  | true =>
      simp only [h, if_true]
      exact ((F).cinnerCompl_embed _ _).symm

private theorem actual_pairSum (p : (F).V) :
    pairSum (schedule extent) offNeighbor (fun i j =>
      (F).cinnerCompl ((P).residual i (embedV F p)) ((P).residual j (embedV F p))) =
      signedNeighborEnergy hw0 hw1 K extent hK (embedV F p) := by
  unfold pairSum signedNeighborEnergy neighboringCross
  apply congrArg (sumOn (schedule extent))
  funext i
  apply congrArg (sumOn (schedule extent))
  funext j
  by_cases h : i = j <;> simp only [offNeighbor, h, if_true, if_false, Bool.false_eq_true]

/-- The proved error coefficient retains the ordered row AND column cost. -/
def neighborErrorCoefficient (delta : Q') : Q' := 50 * pairErrorCoefficient delta

/-- Two-sided energy-relative approximation of the original signed sum.
The displayed cutoff is computed, not an unsupplied analytic premise. -/
theorem signedNeighbor_error_bounds (p : (F).V) (delta : Q')
    (hd : (0 : Q') < delta) (n : Nat)
    (hn : BF4ExactSlabStarResidualApproximation.relativeCutoff w (delta*delta) ≤ n) :
    let err := RCsub (signedNeighborEnergy hw0 hw1 K extent hK (embedV F p))
      (rat (neighborValue hw0 hw1 K extent hK p n))
    let budget := RCscale (neighborErrorCoefficient delta)
      ((P).finalEnergy (schedule extent) (embedV F p))
    RCle (RCneg budget) err ∧ RCle err budget := by
  let r := fun i : PhysicalLink extent => (P).residual i (embedV F p)
  let t := fun i : PhysicalLink extent =>
    embedV F (residualPolynomial hw0 hw1 K extent hK i p n)
  have he (i : PhysicalLink extent) :
      RCle (normSq ((F).cSub (r i) (t i))) (RCscale (delta*delta) (normSq (r i))) :=
    residual_energy_relative_error_le hw0 hw1 K extent hK i p (delta*delta)
      (Q'.mul_pos hd hd) n hn
  have hp (i j : PhysicalLink extent) :=
    pair_error_bounds (fullScalarData hw0 hw1 K extent hK) delta hd
      (r i) (r j) (t i) (t j) (he i) (he j)
  have hrow (i : PhysicalLink extent) (_hi : i ∈ schedule extent) :
      ((schedule extent).filter (offNeighbor i)).length ≤ 25 :=
    Nat.le_trans (filter_mask_length_le _ _ _)
      (neighborhood_row_count extent i)
  have hcol (j : PhysicalLink extent) (_hj : j ∈ schedule extent) :
      ((schedule extent).filter (fun i => offNeighbor i j)).length ≤ 25 :=
    Nat.le_trans (filter_mask_length_le _ _ _)
      (column_count j (schedule extent) (schedule_nodup extent))
  have h := pairSum_error_bounds (schedule extent) offNeighbor
    (fun i => normSq (r i))
    (fun i j => (F).cinnerCompl (r i) (r j))
    (fun i j => (F).cinnerCompl (t i) (t j))
    25 (pairErrorCoefficient delta) (pairErrorCoefficient_nonnegative delta (Q'.le_of_lt hd))
    (fun i _ => (F).cinner_self_nonneg (r i)) hrow hcol
    (fun i j _ _ _ => by
      have hlo := RCSignedPairBudget.neg_mono (hp i j).2
      rw [neg_neg] at hlo
      exact ⟨hlo, (hp i j).1⟩)
  change RCle (RCneg (RCscale (2*Q'.ofNat 25*pairErrorCoefficient delta)
    ((P).finalEnergy (schedule extent) (embedV F p)))) _ ∧
    RCle _ (RCscale (2*Q'.ofNat 25*pairErrorCoefficient delta)
      ((P).finalEnergy (schedule extent) (embedV F p))) at h
  have hc : Q'.eqv (2*Q'.ofNat 25*pairErrorCoefficient delta)
      (neighborErrorCoefficient delta) :=
    Q'.mul_eqv_congr_right _ _ _ (by decide : Q'.eqv (2*Q'.ofNat 25) 50)
  rw [RCSignedPairBudget.scale_congr hc] at h
  dsimp only [r, t] at h
  rw [actual_pairSum, ← neighborValue_pin] at h
  exact h

/-- An unconditional computable signed contribution to the original H^2
lower bound, with its proved energy-relative approximation loss. Positivity
of the displayed lower bound is NOT asserted. Remote squares are retained
through their original proved nonnegativity. -/
theorem conditionalGenerator_square_polynomial_lower (p : (F).V) (delta : Q')
    (hd : (0 : Q') < delta) (n : Nat)
    (hn : BF4ExactSlabStarResidualApproximation.relativeCutoff w (delta*delta) ≤ n) :
    RCle (RCsub
      (RCadd ((P).finalEnergy (schedule extent) (embedV F p))
        (rat (neighborValue hw0 hw1 K extent hK p n)))
      (RCscale (neighborErrorCoefficient delta)
        ((P).finalEnergy (schedule extent) (embedV F p))))
      (normSq (conditionalGenerator hw0 hw1 K extent hK (embedV F p))) := by
  let energy := (P).finalEnergy (schedule extent) (embedV F p)
  let value := rat (neighborValue hw0 hw1 K extent hK p n)
  have h := (signedNeighbor_error_bounds hw0 hw1 K extent hK p delta hd n hn).1
  have hs := RCadd_le_add (RCle_refl value) h
  have hcancel (a b : RC) : RCadd b (RCsub a b) = a := by
    refine Quotient.inductionOn₂ a b ?_
    intro A B
    exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun k =>
      Q'.eqv_trans _ _ _ (Q'.add_comm_eqv _ _)
        (Q'.sub_add_cancel_eqv (A.approx k) (B.approx k))))
  change RCle (RCsub value (RCscale (neighborErrorCoefficient delta) energy))
    (RCadd value (RCsub _ value)) at hs
  rw [hcancel] at hs
  have ha := RCadd_le_add (RCle_refl energy) hs
  have hassoc (a b c : RC) : RCadd a (RCsub b c) = RCsub (RCadd a b) c := by
    refine Quotient.inductionOn₃ a b c ?_
    intro A B C
    exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun k =>
      Q'.eqv_symm (Q'.add_assoc_eqv (A.approx k) (B.approx k) (-(C.approx k)))))
  rw [hassoc] at ha
  exact RCle_trans ha (signed_energy_le_generator_square hw0 hw1 K extent hK (embedV F p))

#print axioms offNeighbor
#print axioms residualPolynomial
#print axioms neighborValue
#print axioms neighborValue_pin
#print axioms neighborErrorCoefficient
#print axioms signedNeighbor_error_bounds
#print axioms conditionalGenerator_square_polynomial_lower

end YMGap.Continuum.BF4ExactSlabSignedNeighborApproximation
