/-
# Positive definiteness of the ORIGINAL thermodynamic completed pairing

The SAME constructed outer pairing rate bounds the distance from each
late diagonal to its own limit. Zero completed norm therefore supplies a
Type-level closeness witness to the constant-zero presentation. No new
zero-norm states survive on arbitrary Cauchy classes.

This result neither assumes nor constructs completed linear operations or
full quotient-level completeness, physical time, a stationary vacuum,
nonzero excitation, uniform gap or continuum theory.
-/

import YMGap.Continuum.BF4ExactSlabThermodynamicCompletedInner

namespace YMGap.Continuum.BF4ExactSlabThermodynamicCompletedPosdef

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabThermodynamicPresentation
open YMGap.Continuum.BF4ExactSlabThermodynamicLowerFunctional
open YMGap.Continuum.BF4ExactSlabThermodynamicReflectedObservable
open YMGap.Continuum.BF4ExactSlabThermodynamicReflectedBilinear
open YMGap.Continuum.BF4ExactSlabThermodynamicNullQuotient
open YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion
open YMGap.Continuum.BF4ExactSlabThermodynamicPairingLimit
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedInner

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

local notation "D" => seminorm

/-- The SAME Type-level outer rate controls distance from the constructed limit. -/
theorem pairSequence_limit_close (X Y : (D).Cauchy) (epsilon : Q') (he : (0 : Q') < epsilon)
    (n : Nat) (hn : pairRate X Y epsilon ≤ n) :
    leRat (CReal.sub (pairSequence X Y n) (representativeInner X Y)) epsilon ∧
    leRat (CReal.sub (representativeInner X Y) (pairSequence X Y n)) epsilon :=
  late_limit_bound (pairSequence_converges X Y) (pairSequence_bound X Y) epsilon he n hn

def zeroPresentation : Presentation :=
  smul 0 BF4ExactSlabThermodynamicPresentation.one

theorem embed_zeroPresentation : embed zeroPresentation = zero := rfl

theorem completedZero_pin : completedZero = embedPresentation zeroPresentation := rfl

private theorem rc_sub_zero (a : RC) : RCsub a RCzero = a := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ (by decide : Q'.eqv (-0) 0))
      (QPoly.q_add_zero_eqv (A.approx n))))

theorem distSq_zero (p : Presentation) :
    Equiv (distSq p zeroPresentation) (presentedForm p p) := by
  apply Quotient.exact (s := crealSetoid)
  rw [distSq_pin, embed_zeroPresentation, pairing_sub_left, pairing_zero_left, rc_sub_zero,
    pairing_sub_right, pairing_zero_right, rc_sub_zero]
  rfl

private theorem sub_equiv_self {a b : CReal} (h : Equiv b czero) : Equiv (CReal.sub a b) a :=
  (CReal.sub_congr_right h).trans (SumOfSquares.Equiv_of_approx_eqv (fun k =>
    Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ (by decide : Q'.eqv (-0) 0))
      (QPoly.q_add_zero_eqv (a.approx k))))

/-- Zero completed norm supplies an actual closeness witness, not an erased modulus. -/
def closeZeroOfInnerZero (X : (D).Cauchy) (h : Equiv (representativeInner X X) czero) :
    (D).Close X ((D).constant zeroPresentation) where
  modulus := pairRate X X
  close := by
    intro epsilon he n hn
    have hbound := (pairSequence_limit_close X X epsilon he n hn).1
    have hsub : Equiv (CReal.sub (pairSequence X X n) (representativeInner X X))
        (pairSequence X X n) := sub_equiv_self h
    exact leEv_trans (leEv_of_equiv (distSq_zero (X.seq n)))
      (CReal.leRat_of_equiv hsub.symm hbound)

theorem completedInner_zero_zero : completedInner completedZero completedZero = RCzero := by
  change completedInner (embedObservable zero) (embedObservable zero) = RCzero
  rw [completedInner_embedObservable]
  exact pairing_zero_left zero

theorem completedInner_posdef (x : Completion) :
    completedInner x x = RCzero ↔ x = completedZero := by
  constructor
  · refine Quotient.inductionOn x ?_
    intro X h
    exact Quotient.sound ⟨closeZeroOfInnerZero X (Quotient.exact h)⟩
  · intro h
    rw [h, completedInner_zero_zero]

end YMGap.Continuum.BF4ExactSlabThermodynamicCompletedPosdef

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletedPosdef.pairSequence_limit_close
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletedPosdef.zeroPresentation
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletedPosdef.embed_zeroPresentation
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletedPosdef.completedZero_pin
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletedPosdef.distSq_zero
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletedPosdef.closeZeroOfInnerZero
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletedPosdef.completedInner_zero_zero
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletedPosdef.completedInner_posdef
