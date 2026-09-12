/-
# Pairing limits from a represented approximation to a specified vector

A family of supplied Cauchy representatives with an explicit squared-error
rate gives an outer Cauchy family whose limit is the SPECIFIED original
vector. Joint pairing continuity therefore has no extra limit-identification
premise and needs no choice of representatives from quotient-valued families.
-/

import YMGap.Continuum.GNSDenseCompletionLaws

namespace YMGap.Continuum.GNSRepresentedApproximation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.GNSDenseCompletionExtension
open YMGap.Continuum.GNSJointPairingContinuity

variable (D : GNSData)

abbrev classOf (X : CauchyGNS D) : GNSCompletionSpace D := Quotient.mk (cauchySetoid D) X

def errorSq (X Y : CauchyGNS D) : CReal.RC :=
  D.cinnerCompl (D.cSub (classOf D X) (classOf D Y)) (D.cSub (classOf D X) (classOf D Y))

variable (X : CauchyGNS D) (U : Nat → CauchyGNS D) (M : Q' → Nat)
  (h : ∀ epsilon, (0 : Q') < epsilon → ∀ n, M epsilon ≤ n →
    CReal.RCle (errorSq D (U n) X) (Quotient.mk CReal.crealSetoid (CReal.ofQ' epsilon)))

include h

theorem pointwise_close (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (p : Nat) (hp : M (HalfPow.half * epsilon) ≤ p) :
    ∃ N, ∀ n, N ≤ n → D.distSqQ ((U p).seq n) (X.seq n) ≤ epsilon := by
  have htiny := ExpNeg.half_mul_pos epsilon hepsilon
  obtain ⟨N, hN⟩ := distance_eventually_le D (U p) X _ (h _ htiny p hp) _ htiny
  exact ⟨N, fun n hn => Q'.le_trans' _ _ _ (hN n hn) (Q'.le_of_eqv (ExpNeg.two_halves epsilon))⟩

/-- Explicit outer rate M(epsilon/8); no rate is selected from a Prop. -/
def outer : GeneralCompletionCauchy D where
  pt := U
  mod epsilon := M (HalfPow.half * (HalfPow.half * (HalfPow.half * epsilon)))
  cauchy := by
    intro epsilon hepsilon p q hp hq
    let quarter := HalfPow.half * (HalfPow.half * epsilon)
    have hquarter : (0 : Q') < quarter :=
      ExpNeg.half_mul_pos _ (ExpNeg.half_mul_pos _ hepsilon)
    obtain ⟨NP, hNP⟩ := pointwise_close D X U M h quarter hquarter p hp
    obtain ⟨NQ, hNQ⟩ := pointwise_close D X U M h quarter hquarter q hq
    refine ⟨max NP NQ, fun n hn => ?_⟩
    have ha := hNP n (Nat.le_trans (Nat.le_max_left _ _) hn)
    have hb := Q'.le_trans' _ _ _ (Q'.le_of_eqv (D.distSqQ_comm _ _))
      (hNQ n (Nat.le_trans (Nat.le_max_right _ _) hn))
    exact Q'.le_trans' _ _ _ (D.distSqQ_triangle ((U p).seq n) (X.seq n) ((U q).seq n))
      (Q'.le_trans' _ _ _ (Q'.add_le_add (Q'.add_le_add ha ha) (Q'.add_le_add hb hb))
        (Q'.le_of_eqv (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr'
          (ExpNeg.two_halves (HalfPow.half * epsilon))
          (ExpNeg.two_halves (HalfPow.half * epsilon))) (ExpNeg.two_halves epsilon))))

theorem outer_lim_null : CauchyNull D (outer D X U M h).lim X := by
  intro epsilon hepsilon
  let quarter := HalfPow.half * (HalfPow.half * epsilon)
  have hquarter : (0 : Q') < quarter := ExpNeg.half_mul_pos _ (ExpNeg.half_mul_pos _ hepsilon)
  let p := max (limitRate (outer D X U M h) quarter) (M (HalfPow.half * quarter))
  obtain ⟨NL, hNL⟩ := limit_close_at (outer D X U M h) quarter hquarter p (Nat.le_max_left _ _)
  obtain ⟨NX, hNX⟩ := pointwise_close D X U M h quarter hquarter p (Nat.le_max_right _ _)
  refine ⟨max NL NX, fun n hn => ?_⟩
  have ha := Q'.le_trans' _ _ _ (Q'.le_of_eqv (D.distSqQ_comm _ _))
    (hNL n (Nat.le_trans (Nat.le_max_left _ _) hn))
  have hb := hNX n (Nat.le_trans (Nat.le_max_right _ _) hn)
  exact Q'.le_trans' _ _ _ (D.distSqQ_triangle ((outer D X U M h).lim.seq n) ((U p).seq n) (X.seq n))
    (Q'.le_trans' _ _ _ (Q'.add_le_add (Q'.add_le_add ha ha) (Q'.add_le_add hb hb))
      (Q'.le_of_eqv (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr'
        (ExpNeg.two_halves (HalfPow.half * epsilon))
        (ExpNeg.two_halves (HalfPow.half * epsilon))) (ExpNeg.two_halves epsilon))))

theorem outer_lim_class : classOf D (outer D X U M h).lim = classOf D X :=
  Quotient.sound (outer_lim_null D X U M h)

/-- Joint continuity with both actual target representatives already pinned. -/
theorem pairing_converges_to (Y : CauchyGNS D) (V : Nat → CauchyGNS D) (N : Q' → Nat)
    (k : ∀ epsilon, (0 : Q') < epsilon → ∀ n, N epsilon ≤ n →
      CReal.RCle (errorSq D (V n) Y) (Quotient.mk CReal.crealSetoid (CReal.ofQ' epsilon))) :
    CReal.ConvergesTo (fun n => D.cinnerRep (U n) (V n)) (D.cinnerRep X Y) := by
  apply CReal.convergesTo_limit_congr
    (pairing_converges (outer D X U M h) (outer D Y V N k))
  apply Quotient.exact (s := CReal.crealSetoid)
  change D.cinnerCompl (classOf D (outer D X U M h).lim) (classOf D (outer D Y V N k).lim) =
    D.cinnerCompl (classOf D X) (classOf D Y)
  rw [outer_lim_class, outer_lim_class]

end YMGap.Continuum.GNSRepresentedApproximation

#print axioms YMGap.Continuum.GNSRepresentedApproximation.errorSq
#print axioms YMGap.Continuum.GNSRepresentedApproximation.pointwise_close
#print axioms YMGap.Continuum.GNSRepresentedApproximation.outer
#print axioms YMGap.Continuum.GNSRepresentedApproximation.outer_lim_null
#print axioms YMGap.Continuum.GNSRepresentedApproximation.outer_lim_class
#print axioms YMGap.Continuum.GNSRepresentedApproximation.pairing_converges_to
