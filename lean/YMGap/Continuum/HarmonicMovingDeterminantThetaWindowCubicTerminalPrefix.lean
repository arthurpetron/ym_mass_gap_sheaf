/-
Constructive finite-sequence combinator: a nonnegative total together with
forward propagation of strict negativity forces every prefix nonnegative.
-/

import YMGap.Continuum.HarmonicMovingDeterminantThetaWindowCubicFullPhysicalClosure

namespace YMGap.Continuum.HarmonicMovingDeterminantThetaWindowCubicTerminalPrefix

set_option maxHeartbeats 2400000
set_option maxRecDepth 30000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep

private theorem nonnegative_of_not_negative {a : Q'}
    (h : ¬ a < (0 : Q')) : (0 : Q') ≤ a := by
  show (0 : Int) * (a.den : Int) ≤ a.num * (((0 : Q').den) : Int)
  exact Int.le_of_not_gt h

private theorem negative_add (f : Nat → Q') {L : Nat}
    (hstep : ∀ i, i + 1 < L → f i < (0 : Q') → f (i + 1) < (0 : Q'))
    (i : Nat) : ∀ d, i + d < L → f i < (0 : Q') →
      f (i + d) < (0 : Q')
  | 0, _, hi => by simpa using hi
  | d + 1, hid, hi => by
      have hprev : i + d < L := by omega
      have ih := negative_add f hstep i d hprev hi
      have hs := hstep (i + d) (by omega) ih
      simpa [Nat.add_assoc] using hs

private theorem fsum_nonnegative_bounded (f : Nat → Q') : ∀ n,
    (∀ i, i < n → (0 : Q') ≤ f i) → (0 : Q') ≤ fsum f n
  | 0, _ => Q'.le_refl' 0
  | n + 1, h =>
      Q'.zero_le_add _ _
        (fsum_nonnegative_bounded f n (fun i hi => h i (by omega)))
        (h n (by omega))

/-- Terminal strict negativity plus a nonnegative total closes all prefixes. -/
theorem fsum_prefix_nonnegative_of_terminal_negative
    (f : Nat → Q') : ∀ L,
    (0 : Q') ≤ fsum f L →
    (∀ i, i + 1 < L → f i < (0 : Q') → f (i + 1) < (0 : Q')) →
    ∀ p, p ≤ L → (0 : Q') ≤ fsum f p
  | 0, _, _, p, hp => by
      have hp0 : p = 0 := by omega
      subst p
      exact Q'.le_refl' 0
  | L + 1, htotal, hstep, p, hp => by
      by_cases hlast : f L < (0 : Q')
      · have hfull : (0 : Q') ≤ fsum f L + f L := by
          simpa only [fsum_succ] using htotal
        have hdrop : fsum f L + f L ≤ fsum f L := by
          have hle : f L ≤ (0 : Q') := Q'.le_of_lt hlast
          have hadd := Q'.add_le_add_left (fsum f L) (f L) 0 hle
          exact Q'.le_trans' _ _ _ hadd
            (Q'.le_of_eqv (YMGap.Constructive.QPoly.q_add_zero_eqv _))
        have hprev : (0 : Q') ≤ fsum f L :=
          Q'.le_trans' _ _ _ hfull hdrop
        rcases Nat.lt_or_eq_of_le hp with hlt | heq
        · exact fsum_prefix_nonnegative_of_terminal_negative f L hprev
            (fun i hi => hstep i (by omega)) p (by omega)
        · subst p
          exact htotal
      · apply fsum_nonnegative_bounded
        intro i hi
        by_cases hneg : f i < (0 : Q')
        · have hiL : i ≤ L := by omega
          have hto := negative_add f hstep i (L - i) (by omega) hneg
          have htoLast : f L < (0 : Q') := by
            simpa [Nat.add_sub_of_le hiL] using hto
          exact False.elim (hlast htoLast)
        · exact nonnegative_of_not_negative hneg

#print axioms fsum_prefix_nonnegative_of_terminal_negative

end YMGap.Continuum.HarmonicMovingDeterminantThetaWindowCubicTerminalPrefix
