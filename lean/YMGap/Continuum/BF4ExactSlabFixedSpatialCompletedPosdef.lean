/-
# No new null elements in the SAME completed reflected pairing

The computed outer pairing rate also bounds each late term's distance from
the constructed scalar limit. A zero limiting diagonal therefore supplies
an explicit closeness witness to the constant-zero sequence. This proves
positive definiteness on the actual Cauchy quotient before requiring any
completed vector-space laws.

No representative is selected and no modulus is erased to construct data.
This does not prove metric completeness, Hilbert laws or a strict gap.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedInner

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedPosdef

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialReflectedForm
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicReflectedForm
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicDifference
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicSeminorm
open YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedPhysicalTime
open YMGap.Continuum.BF4ExactSlabFixedSpatialPairingLimit
open YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedInner

private theorem convergesTo_max {s : Nat → CReal} {L : CReal}
    (h : ConvergesTo s L) (base : Nat) : ConvergesTo (fun n => s (max n base)) L := by
  intro epsilon he
  obtain ⟨N, hN⟩ := h epsilon he
  exact ⟨N, fun n hn => hN (max n base) (Nat.le_trans hn (Nat.le_max_left _ _))⟩

private theorem late_limit_bound {s : Nat → CReal} {L : CReal} {M : Q' → Nat}
    (hs : ConvergesTo s L) (hb : LeRatBound s M) (epsilon : Q') (he : (0 : Q') < epsilon)
    (n : Nat) (hn : M epsilon ≤ n) :
    leRat (sub (s n) L) epsilon ∧ leRat (sub L (s n)) epsilon := by
  have ht := convergesTo_max hs (M epsilon)
  constructor
  · exact leEv_of_convergesTo_le
      (TrigAddCReal.convergesTo_add (convergesTo_const (s n)) (convergesTo_neg ht))
      (convergesTo_const (ofQ' epsilon))
      (fun m => (hb epsilon he n (max m (M epsilon)) hn (Nat.le_max_right _ _)).1)
  · exact leEv_of_convergesTo_le
      (TrigAddCReal.convergesTo_add ht (convergesTo_const (neg (s n))))
      (convergesTo_const (ofQ' epsilon))
      (fun m => (hb epsilon he n (max m (M epsilon)) hn (Nat.le_max_right _ _)).2)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (width stage : Nat)

local notation "D" => seminorm hw0 hw1 width stage

def completedZero : Completion hw0 hw1 width stage :=
  embedSpan hw0 hw1 width stage (zero width)

/-- The SAME named outer rate bounds late terms against their actual limit. -/
theorem pairSequence_limit_close (X Y : (D).Cauchy) (epsilon : Q') (he : (0 : Q') < epsilon)
    (n : Nat) (hn : pairRate hw0 hw1 width stage X Y epsilon ≤ n) :
    leRat (sub (pairSequence hw0 hw1 width stage X Y n)
      (representativeInner hw0 hw1 width stage X Y)) epsilon ∧
    leRat (sub (representativeInner hw0 hw1 width stage X Y)
      (pairSequence hw0 hw1 width stage X Y n)) epsilon :=
  late_limit_bound (pairSequence_converges hw0 hw1 width stage X Y)
    (pairSequence_bound hw0 hw1 width stage X Y) epsilon he n hn

theorem distSq_zero (x : PhysicalSpan width) :
    Equiv (distSq hw0 hw1 width stage x (zero width))
      (pairing hw0 hw1 width x.val x.val stage) := by
  simp only [distSq, zero, difference, scaleSpan, List.map_nil, List.append_nil]
  exact Equiv.refl _

/-- Zero norm constructs an actual closeness datum with the existing rate. -/
def closeZeroOfInnerZero (X : (D).Cauchy)
    (h : Equiv (representativeInner hw0 hw1 width stage X X) czero) :
    (D).Close X ((D).constant (zero width)) where
  modulus := pairRate hw0 hw1 width stage X X
  close := by
    intro epsilon he n hn
    have hbound := (pairSequence_limit_close hw0 hw1 width stage X X epsilon he n hn).1
    have hsub : Equiv
        (sub (pairSequence hw0 hw1 width stage X X n) (representativeInner hw0 hw1 width stage X X))
        (pairSequence hw0 hw1 width stage X X n) :=
      (CReal.sub_congr_right h).trans (SumOfSquares.Equiv_of_approx_eqv (fun k =>
        Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ (by decide : Q'.eqv (-0) 0))
          (QPoly.q_add_zero_eqv ((pairSequence hw0 hw1 width stage X X n).approx k))))
    exact leEv_trans (leEv_of_equiv (distSq_zero hw0 hw1 width stage (X.seq n)))
      (CReal.leRat_of_equiv hsub.symm hbound)

theorem completedZero_inner_zero :
    completedInner hw0 hw1 width stage (completedZero hw0 hw1 width stage)
      (completedZero hw0 hw1 width stage) = RCzero := by
  unfold completedZero
  rw [completedInner_embedSpan]
  exact Quotient.sound (pairing_difference_self_left hw0 hw1 width [] [] stage)

/-- Positive definiteness on this actual carrier, without completed linearity. -/
theorem completedInner_posdef (x : Completion hw0 hw1 width stage) :
    completedInner hw0 hw1 width stage x x = RCzero ↔ x = completedZero hw0 hw1 width stage := by
  constructor
  · refine Quotient.inductionOn x ?_
    intro X h
    exact Quotient.sound ⟨closeZeroOfInnerZero hw0 hw1 width stage X (Quotient.exact h)⟩
  · intro h
    rw [h]
    exact completedZero_inner_zero hw0 hw1 width stage

end YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedPosdef

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedPosdef.completedZero
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedPosdef.pairSequence_limit_close
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedPosdef.distSq_zero
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedPosdef.closeZeroOfInnerZero
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedPosdef.completedZero_inner_zero
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedPosdef.completedInner_posdef
