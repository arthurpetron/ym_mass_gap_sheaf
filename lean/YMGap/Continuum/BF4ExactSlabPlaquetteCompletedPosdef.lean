/-
# Positive definiteness of the ORIGINAL completed plaquette pairing

The outer Cauchy rate bounds each late pairing's difference from its actual
limit. If the completed diagonal is zero, that same computed rate witnesses
closeness to the constant-zero representative. Thus no new null states
remain in the completed pairing, not merely on the embedded quotient.

All closeness moduli are Type-level data. The proof introduces neither a
selected representative nor a new analytic premise.
-/

import YMGap.Continuum.BF4ExactSlabPlaquetteCompletedBilinear

namespace YMGap.Continuum.BF4ExactSlabPlaquetteCompletedPosdef

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabPlaquetteFiniteGNS
open YMGap.Continuum.BF4ExactSlabPlaquetteReflectedForm
open YMGap.Continuum.BF4ExactSlabPlaquetteNullQuotient
open YMGap.Continuum.BF4ExactSlabPlaquetteSeminormCompletion
open YMGap.Continuum.BF4ExactSlabPlaquettePairingLimit
open YMGap.Continuum.BF4ExactSlabPlaquetteCompletedInner
open YMGap.Continuum.BF4ExactSlabPlaquetteCompletedBilinear

private theorem convergesTo_max {s : Nat → CReal} {L : CReal} (h : ConvergesTo s L) (base : Nat) :
    ConvergesTo (fun n => s (max n base)) L := by
  intro epsilon he
  obtain ⟨N, hN⟩ := h epsilon he
  exact ⟨N, fun n hn => hN (max n base) (Nat.le_trans hn (Nat.le_max_left _ _))⟩

private theorem late_limit_bound {s : Nat → CReal} {L : CReal} {M : Q' → Nat}
    (hs : ConvergesTo s L) (hb : LeRatBound s M) (epsilon : Q') (he : (0 : Q') < epsilon)
    (n : Nat) (hn : M epsilon ≤ n) :
    leRat (CReal.sub (s n) L) epsilon ∧ leRat (CReal.sub L (s n)) epsilon := by
  have ht := convergesTo_max hs (M epsilon)
  constructor
  · exact leEv_of_convergesTo_le
      (TrigAddCReal.convergesTo_add (convergesTo_const (s n)) (convergesTo_neg ht))
      (convergesTo_const (ofQ' epsilon))
      (fun m => (hb epsilon he n (max m (M epsilon)) hn (Nat.le_max_right _ _)).1)
  · exact leEv_of_convergesTo_le
      (TrigAddCReal.convergesTo_add ht (convergesTo_const (CReal.neg (s n))))
      (convergesTo_const (ofQ' epsilon))
      (fun m => (hb epsilon he n (max m (M epsilon)) hn (Nat.le_max_right _ _)).2)

variable (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {half : Nat}

local notation "D" => seminorm w hw0 hw1 half

/-- The SAME Type-level outer rate controls distance from the constructed limit. -/
theorem pairSequence_limit_close (X Y : (D).Cauchy) (epsilon : Q') (he : (0 : Q') < epsilon)
    (n : Nat) (hn : pairRate w hw0 hw1 X Y epsilon ≤ n) :
    leRat (CReal.sub (pairSequence w hw0 hw1 X Y n) (representativeInner w hw0 hw1 X Y)) epsilon ∧
    leRat (CReal.sub (representativeInner w hw0 hw1 X Y) (pairSequence w hw0 hw1 X Y n)) epsilon :=
  late_limit_bound (pairSequence_converges w hw0 hw1 X Y) (pairSequence_bound w hw0 hw1 X Y) epsilon he n hn

theorem distSq_zero (e : PlaquetteExpression half) :
    Equiv (distSq w hw0 hw1 e (zeroExpression half)) (form w hw0 hw1 e e) := by
  let G := finiteGNSData w (Q'.le_of_lt hw0) 0 half
  have he : expressionEqv (subtract e (zeroExpression half)) e :=
    G.veq_trans (G.add_congr (G.veq_refl e) G.neg_zero) (G.add_zero e)
  exact form_congr w hw0 hw1 he he

/-- Zero completed norm supplies an actual closeness witness, not an erased modulus. -/
def closeZeroOfInnerZero (X : (D).Cauchy) (h : Equiv (representativeInner w hw0 hw1 X X) czero) :
    (D).Close X ((D).constant (zeroExpression half)) where
  modulus := pairRate w hw0 hw1 X X
  close := by
    intro epsilon he n hn
    have hbound := (pairSequence_limit_close w hw0 hw1 X X epsilon he n hn).1
    have hsub : Equiv (CReal.sub (pairSequence w hw0 hw1 X X n) (representativeInner w hw0 hw1 X X))
        (pairSequence w hw0 hw1 X X n) :=
      (CReal.sub_congr_right h).trans (SumOfSquares.Equiv_of_approx_eqv (fun k =>
        Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ (by decide : Q'.eqv (-0) 0))
          (QPoly.q_add_zero_eqv ((pairSequence w hw0 hw1 X X n).approx k))))
    exact leEv_trans (leEv_of_equiv (distSq_zero w hw0 hw1 (X.seq n)))
      (CReal.leRat_of_equiv hsub.symm hbound)

theorem completedInner_posdef (x : Completion w hw0 hw1 half) :
    completedInner w hw0 hw1 x x = RCzero ↔ x = completedZero w hw0 hw1 half := by
  constructor
  · refine Quotient.inductionOn x ?_
    intro X h
    exact Quotient.sound ⟨closeZeroOfInnerZero w hw0 hw1 X (Quotient.exact h)⟩
  · intro h
    rw [h, completedInner_zero_left]

end YMGap.Continuum.BF4ExactSlabPlaquetteCompletedPosdef

#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCompletedPosdef.pairSequence_limit_close
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCompletedPosdef.distSq_zero
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCompletedPosdef.closeZeroOfInnerZero
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCompletedPosdef.completedInner_posdef
