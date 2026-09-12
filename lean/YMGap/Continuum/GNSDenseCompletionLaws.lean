/-
# Full-space laws for the constructive dense-map extension

Joint pairing continuity passes the sharp dense distance bound to the entire
completion. Constant representatives of the original input sequence give a
second explicit outer Cauchy family; its limit is the original input class.
Mixed pairing limits therefore also pass dense symmetry and positivity to
the SAME constructed completion map. No new analytic certificate is required.
-/

import YMGap.Continuum.GNSDenseCompletionExtension
import YMGap.Continuum.GNSJointPairingContinuity
import YMGap.Continuum.FCNormBoundLimit

namespace YMGap.Continuum.GNSDenseCompletionLaws

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.GNSJointPairingContinuity
open YMGap.Continuum.GNSDenseCompletionExtension

variable {D : GNSData}

/-- Nondegeneracy follows from the original rational distance representatives. -/
theorem eq_of_distance_le_zero (x y : GNSCompletionSpace D)
    (h : CReal.RCle (D.cinnerCompl (D.cSub x y) (D.cSub x y)) CReal.RCzero) : x = y := by
  revert h
  refine Quotient.inductionOn₂ x y ?_
  intro X Y h
  apply Quotient.sound
  intro epsilon hepsilon
  obtain ⟨N, hN⟩ := distance_eventually_le D X Y 0 h epsilon hepsilon
  exact ⟨N, fun n hn => Q'.le_trans' _ _ _ (hN n hn)
    (Q'.le_of_eqv (Q'.eqv_of_eq (Q'.zero_add' epsilon)))⟩

theorem eq_of_pairings_equal (x y : GNSCompletionSpace D)
    (h : ∀ z, D.cinnerCompl x z = D.cinnerCompl y z) : x = y := by
  apply eq_of_distance_le_zero x y
  rw [D.cinnerCompl_cSub_left, h]
  have hz (a : CReal.RC) : CReal.RCsub a a = CReal.RCzero := by
    refine Quotient.inductionOn a ?_
    intro A
    exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
      (fun n => Q'.add_neg_self_eqv (A.approx n)))
  rw [hz]
  exact CReal.RCle_refl _

/-- The supplied input modulus is retained as data. -/
def inputOuter (X : CauchyGNS D) : GeneralCompletionCauchy D where
  pt n := constCauchy D (X.seq n)
  mod := X.modulus
  cauchy := fun epsilon hepsilon p q hp hq =>
    ⟨0, fun _ _ => X.isCauchy epsilon hepsilon p q hp hq⟩

theorem inputOuter_lim_null (X : CauchyGNS D) :
    CauchyNull D (inputOuter X).lim X := by
  intro epsilon hepsilon
  let tiny := HalfPow.half * (HalfPow.half * epsilon)
  have htiny : (0 : Q') < tiny := ExpNeg.half_mul_pos _ (ExpNeg.half_mul_pos epsilon hepsilon)
  let p := max (limitRate (inputOuter X) tiny) (X.modulus tiny)
  obtain ⟨N, hN⟩ := limit_close_at (inputOuter X) tiny htiny p (Nat.le_max_left _ _)
  refine ⟨max N (X.modulus tiny), fun n hn => ?_⟩
  have ha := Q'.le_trans' _ _ _ (Q'.le_of_eqv (D.distSqQ_comm _ _))
    (hN n (Nat.le_trans (Nat.le_max_left _ _) hn))
  have hb := X.isCauchy tiny htiny p n (Nat.le_max_right _ _)
    (Nat.le_trans (Nat.le_max_right _ _) hn)
  have htri := D.distSqQ_triangle ((inputOuter X).lim.seq n) (X.seq p) (X.seq n)
  exact Q'.le_trans' _ _ _ (Q'.le_trans' _ _ _ htri
    (Q'.add_le_add (Q'.add_le_add ha ha) (Q'.add_le_add hb hb)))
    (Q'.le_of_eqv (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr'
      (ExpNeg.two_halves (HalfPow.half * epsilon))
      (ExpNeg.two_halves (HalfPow.half * epsilon))) (ExpNeg.two_halves epsilon)))

theorem inputOuter_lim_class (X : CauchyGNS D) :
    Quotient.mk (cauchySetoid D) (inputOuter X).lim = Quotient.mk (cauchySetoid D) X :=
  Quotient.sound (inputOuter_lim_null X)

theorem fixed_input_converges (X Y : CauchyGNS D) :
    CReal.ConvergesTo (fun n => D.cinnerRep X (constCauchy D (Y.seq n))) (D.cinnerRep X Y) := by
  apply CReal.convergesTo_limit_congr (D.cinnerRep_continuous_right (inputOuter Y) X)
  exact Quotient.exact (s := CReal.crealSetoid)
    (congrArg (D.cinnerCompl (Quotient.mk (cauchySetoid D) X)) (inputOuter_lim_class Y))

/-- Equality can be tested on the literal dense vectors, not arbitrary
quotient representatives selected by choice. -/
theorem eq_of_dense_pairings (x y : GNSCompletionSpace D)
    (h : ∀ v : D.V, D.cinnerCompl x (embedV D v) = D.cinnerCompl y (embedV D v)) : x = y := by
  apply eq_of_pairings_equal
  intro z
  revert h
  refine Quotient.inductionOn₃ x y z ?_
  intro X Y Z h
  apply Quotient.sound
  exact CReal.Equiv_of_limit_of_equal
    (fun n => Quotient.exact (s := CReal.crealSetoid) (h (Z.seq n)))
    (fixed_input_converges X Z) (fixed_input_converges Y Z)

variable (T : DenseMap D)

/-- Nonexpansiveness on ALL completion vectors, with no constant loss. -/
theorem completionMap_nonexpansive (x y : GNSCompletionSpace D) :
    CReal.RCle
      (D.cinnerCompl (D.cSub (T.completionMap x) (T.completionMap y))
        (D.cSub (T.completionMap x) (T.completionMap y)))
      (D.cinnerCompl (D.cSub x y) (D.cSub x y)) := by
  refine Quotient.inductionOn₂ x y ?_
  intro X Y
  exact CReal.leEv_of_convergesTo_le
    (difference_converges (T.mapOuter X) (T.mapOuter Y))
    (CReal.convergesTo_ofQ'CauchySeq _ (D.distSqSeqCauchy X Y))
    (fun n => T.nonexpansive (X.seq n) (Y.seq n))

theorem mixed_left_converges (X Y : CauchyGNS D) :
    CReal.ConvergesTo (fun n => D.cinnerRep (T.toRep (X.seq n)) (constCauchy D (Y.seq n)))
      (D.cinnerRep (T.mapRep X) Y) := by
  apply CReal.convergesTo_limit_congr (pairing_converges (T.mapOuter X) (inputOuter Y))
  exact Quotient.exact (s := CReal.crealSetoid)
    (congrArg (D.cinnerCompl (Quotient.mk (cauchySetoid D) (T.mapRep X))) (inputOuter_lim_class Y))

theorem mixed_right_converges (X Y : CauchyGNS D) :
    CReal.ConvergesTo (fun n => D.cinnerRep (constCauchy D (X.seq n)) (T.toRep (Y.seq n)))
      (D.cinnerRep X (T.mapRep Y)) := by
  apply CReal.convergesTo_limit_congr (pairing_converges (inputOuter X) (T.mapOuter Y))
  exact Quotient.exact (s := CReal.crealSetoid)
    (congrArg (fun z => D.cinnerCompl z (Quotient.mk (cauchySetoid D) (T.mapRep Y)))
      (inputOuter_lim_class X))

/-- Dense symmetry is only a hypothesis of this generic theorem; the physical
application proves it for its already constructed output representatives. -/
theorem completionMap_selfAdjoint
    (h : ∀ x y, D.cinnerCompl (Quotient.mk (cauchySetoid D) (T.toRep x))
        (Quotient.mk (cauchySetoid D) (constCauchy D y)) =
      D.cinnerCompl (Quotient.mk (cauchySetoid D) (constCauchy D x))
        (Quotient.mk (cauchySetoid D) (T.toRep y)))
    (x y : GNSCompletionSpace D) :
    D.cinnerCompl (T.completionMap x) y = D.cinnerCompl x (T.completionMap y) := by
  refine Quotient.inductionOn₂ x y ?_
  intro X Y
  apply Quotient.sound
  exact CReal.Equiv_of_limit_of_equal
    (fun n => Quotient.exact (s := CReal.crealSetoid) (h (X.seq n) (Y.seq n)))
    (mixed_left_converges T X Y) (mixed_right_converges T X Y)

theorem completionMap_positive
    (h : ∀ x, CReal.RCnonneg (D.cinnerCompl (Quotient.mk (cauchySetoid D) (T.toRep x))
      (Quotient.mk (cauchySetoid D) (constCauchy D x))))
    (x : GNSCompletionSpace D) : CReal.RCnonneg (D.cinnerCompl (T.completionMap x) x) := by
  refine Quotient.inductionOn x ?_
  intro X
  exact CReal.leEv_of_convergesTo_le (CReal.convergesTo_const CReal.czero)
    (mixed_left_converges T X X) (fun n => h (X.seq n))

end YMGap.Continuum.GNSDenseCompletionLaws

#print axioms YMGap.Continuum.GNSDenseCompletionLaws.inputOuter
#print axioms YMGap.Continuum.GNSDenseCompletionLaws.eq_of_distance_le_zero
#print axioms YMGap.Continuum.GNSDenseCompletionLaws.eq_of_pairings_equal
#print axioms YMGap.Continuum.GNSDenseCompletionLaws.inputOuter_lim_null
#print axioms YMGap.Continuum.GNSDenseCompletionLaws.inputOuter_lim_class
#print axioms YMGap.Continuum.GNSDenseCompletionLaws.fixed_input_converges
#print axioms YMGap.Continuum.GNSDenseCompletionLaws.eq_of_dense_pairings
#print axioms YMGap.Continuum.GNSDenseCompletionLaws.completionMap_nonexpansive
#print axioms YMGap.Continuum.GNSDenseCompletionLaws.mixed_left_converges
#print axioms YMGap.Continuum.GNSDenseCompletionLaws.mixed_right_converges
#print axioms YMGap.Continuum.GNSDenseCompletionLaws.completionMap_selfAdjoint
#print axioms YMGap.Continuum.GNSDenseCompletionLaws.completionMap_positive
