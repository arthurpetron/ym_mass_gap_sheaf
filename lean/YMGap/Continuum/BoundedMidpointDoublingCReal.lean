/-
# Bounded midpoint doubling for constructive reals

The eventual order cannot be sampled at one universal rational stage over an
infinite family of indices.  For a fixed Archimedean contradiction, however,
only a finite dyadic orbit is needed.  This module synchronizes precisely
those finitely many eventual cutoffs, performs the rational growth argument,
and returns the contraction in `CReal.leEv`.
-/

import YMGap.Continuum.BoundedMidpointDoublingError
import YMGap.Continuum.GNSDynamics

namespace YMGap.Continuum.BoundedMidpointDoublingCReal

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum.BoundedMidpointDoubling
open YMGap.Continuum.BoundedMidpointDoublingError
open YMGap.Continuum.ClusteringImpliesGap

local infix:50 " ≈ " => Q'.eqv

private theorem q_lt_of_not_le_local {a b : Q'}
    (h : ¬ a ≤ b) : b < a := by
  have hnum : ¬ (a.num * (b.den : Int) ≤
      b.num * (a.den : Int)) := h
  show b.num * (a.den : Int) < a.num * (b.den : Int)
  exact Int.not_le.mp hnum

private theorem lt_of_sub_pos_local {a b : Q'}
    (h : (0 : Q') < b + (-a)) : a < b := by
  have hnum : (0 : Int) < (b + (-a)).num := Q'.num_pos_of_pos h
  have hdiff : (0 : Int) <
      b.num * (a.den : Int) + (-a.num) * (b.den : Int) := hnum
  rw [Int.neg_mul] at hdiff
  show a.num * (b.den : Int) < b.num * (a.den : Int)
  omega

private theorem ofNat_mul_eqv_local (a b : Nat) :
    Q'.ofNat (a * b) ≈ Q'.ofNat a * Q'.ofNat b := by
  show _ * (_ : Int) = _ * (_ : Int)
  simp only [Q'.mul_num_cast, Q'.mul_den_cast,
    Q'.ofNat_num_cast, Q'.ofNat_den_cast,
    Int.natCast_mul, Int.mul_one]

private theorem successor_factor_le_double
    (t : Nat) {d : Q'} (hd : (0 : Q') ≤ d) :
    Q'.ofNat (t + 2) * d ≤
      (2 : Q') * (Q'.ofNat (t + 1) * d) := by
  have hnat : t + 2 ≤ 2 * (t + 1) := by omega
  have hq : Q'.ofNat (t + 2) ≤ Q'.ofNat (2 * (t + 1)) :=
    CReal.ofNat_le_ofNat hnat
  have hmul := Q'.mul_le_mul_of_nonneg_right _ _ d hq hd
  have hfactor :
      Q'.ofNat (2 * (t + 1)) * d ≈
        (2 : Q') * (Q'.ofNat (t + 1) * d) := by
    refine Q'.eqv_trans _
      ((Q'.ofNat 2 * Q'.ofNat (t + 1)) * d) _ ?_ ?_
    · exact Q'.mul_eqv_congr_right _ _ d
        (ofNat_mul_eqv_local 2 (t + 1))
    · exact Q'.mul_assoc_eqv _ _ _
  exact Q'.le_trans' _ _ _ hmul (Q'.le_of_eqv hfactor)

private def errorDifferenceOnceLeft : RingNormaliser.PolyExpr :=
  .add (.add (.var 0) (.neg (.var 1))) (.neg (.var 2))

private def errorDifferenceOnceRight : RingNormaliser.PolyExpr :=
  .add (.var 0) (.neg (.add (.var 1) (.var 2)))

private theorem errorDifferenceOnce_normal :
    RingNormaliser.normalize errorDifferenceOnceLeft =
      RingNormaliser.normalize errorDifferenceOnceRight := by decide

private theorem error_difference_once
    (current anchor error : Q') :
    current + -anchor + -error ≈ current + -(anchor + error) := by
  simpa [errorDifferenceOnceLeft, errorDifferenceOnceRight,
    RingNormaliser.eval] using
    (RingNormaliser.poly_identity_of_normal_eq
      errorDifferenceOnceLeft errorDifferenceOnceRight
      errorDifferenceOnce_normal
      (fun | 0 => current | 1 => anchor | _ => error))

private def errorDifferenceTwiceLeft : RingNormaliser.PolyExpr :=
  .add
    (.add (.add (.var 0) (.neg (.var 1))) (.neg (.var 2)))
    (.neg (.var 2))

private def errorDifferenceTwiceRight : RingNormaliser.PolyExpr :=
  .add (.var 0)
    (.neg (.add (.add (.var 1) (.var 2)) (.var 2)))

private theorem errorDifferenceTwice_normal :
    RingNormaliser.normalize errorDifferenceTwiceLeft =
      RingNormaliser.normalize errorDifferenceTwiceRight := by decide

private theorem error_difference_twice
    (current anchor error : Q') :
    current + -anchor + -error + -error ≈
      current + -((anchor + error) + error) := by
  simpa [errorDifferenceTwiceLeft, errorDifferenceTwiceRight,
    RingNormaliser.eval] using
    (RingNormaliser.poly_identity_of_normal_eq
      errorDifferenceTwiceLeft errorDifferenceTwiceRight
      errorDifferenceTwice_normal
      (fun | 0 => current | 1 => anchor | _ => error))

/-! ## 1. Finite-orbit synchronization and growth -/

/-- Synchronize the eventual midpoint inequalities on exactly a finite
prefix of one dyadic orbit. -/
theorem midpointDoubling_prefix_eventually
    (a : Nat → CReal)
    (hmid : ∀ n,
      CReal.leEv
        (CReal.mul (CReal.ofQ' 2) (a n))
        (CReal.add (a 0) (a (2 * n))))
    (error : Q') (herror : (0 : Q') < error)
    (n length : Nat) :
    ∃ cutoff : Nat, ∀ stage : Nat, cutoff ≤ stage →
      ∀ t : Nat, t < length →
        (2 : Q') * (a (doubledIndex n t)).approx stage ≤
          (a 0).approx stage +
            (a (doubledIndex n (t + 1))).approx stage + error := by
  induction length with
  | zero =>
      exact ⟨0, fun _ _ t ht => False.elim (Nat.not_lt_zero t ht)⟩
  | succ length ih =>
      obtain ⟨previousCutoff, hprevious⟩ := ih
      obtain ⟨currentCutoff, hcurrent⟩ :=
        hmid (doubledIndex n length) error herror
      refine ⟨max previousCutoff currentCutoff, fun stage hstage t ht => ?_⟩
      have hpreviousStage : previousCutoff ≤ stage :=
        Nat.le_trans (Nat.le_max_left _ _) hstage
      have hcurrentStage : currentCutoff ≤ stage :=
        Nat.le_trans (Nat.le_max_right _ _) hstage
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ ht) with hlt | heq
      · exact hprevious stage hpreviousStage t hlt
      · subst t
        have hpoint := hcurrent stage hcurrentStage
        change
          (2 : Q') * (a (doubledIndex n length)).approx stage ≤
            ((a 0).approx stage +
              (a (2 * doubledIndex n length)).approx stage) + error
          at hpoint
        simpa only [doubledIndex_succ] using hpoint

/-- A homogeneous doubling inequality on a finite dyadic prefix gives the
same arbitrary-integer growth factor used in the unbounded-orbit proof. -/
theorem homogeneousDoubling_prefix_growth
    (a : Nat → Q') (n length : Nat)
    (hdouble : ∀ t, t < length →
      (2 : Q') * a (doubledIndex n t) ≤
        a (doubledIndex n (t + 1)))
    (hnonnegative : (0 : Q') ≤ a n) :
    Q'.ofNat (length + 1) * a n ≤
      a (doubledIndex n length) := by
  induction length with
  | zero =>
      exact Q'.le_of_eqv (Q'.one_mul_eqv (a n))
  | succ length ih =>
      have hfactor := successor_factor_le_double length hnonnegative
      have hprefix : ∀ t, t < length →
          (2 : Q') * a (doubledIndex n t) ≤
            a (doubledIndex n (t + 1)) :=
        fun t ht => hdouble t (Nat.lt_succ_of_lt ht)
      have hgrowth := ih hprefix
      have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ (2 : Q')
        hgrowth (by decide)
      exact Q'.le_trans' _ _ _ hfactor
        (Q'.le_trans' _ _ _ hscaled (by
          simpa only [doubledIndex_succ] using
            hdouble length (Nat.lt_succ_self length)))

/-! ## 2. Constructive-real Archimedean consumer -/

/-- A pointwise rational cap and a nonnegative anchor turn the eventual
midpoint recurrence into contraction toward the anchor. -/
theorem bounded_midpointDoubling_leEv_anchor
    (a : Nat → CReal) (bound : Q')
    (hbound : ∀ n stage, (a n).approx stage ≤ bound)
    (hanchor : ∀ stage, (0 : Q') ≤ (a 0).approx stage)
    (hmid : ∀ n,
      CReal.leEv
        (CReal.mul (CReal.ofQ' 2) (a n))
        (CReal.add (a 0) (a (2 * n))))
    (n : Nat) :
    CReal.leEv (a n) (a 0) := by
  intro epsilon hepsilon
  let error := HalfPow.half * epsilon
  have herrorPositive : (0 : Q') < error :=
    ExpNeg.half_mul_pos epsilon hepsilon
  have herrorNonnegative : (0 : Q') ≤ error :=
    Q'.le_of_lt herrorPositive
  have herrorLe : error ≤ epsilon := by
    have hfirst : error ≤ error + error :=
      Q'.add_le_self_of_nonneg error error herrorNonnegative
    exact Q'.le_trans' _ _ _ hfirst
      (Q'.le_of_eqv (ExpNeg.two_halves epsilon))
  obtain ⟨length, hlength⟩ := exists_succ_mul_gt
    bound error herrorPositive
  obtain ⟨cutoff, hprefix⟩ := midpointDoubling_prefix_eventually
    a hmid error herrorPositive n length
  refine ⟨cutoff, fun stage hstage => ?_⟩
  by_cases hle : (a n).approx stage ≤ (a 0).approx stage + epsilon
  · exact hle
  · have hstrict : (a 0).approx stage + epsilon <
        (a n).approx stage := q_lt_of_not_le_local hle
    let shifted : Nat → Q' := fun k =>
      (a k).approx stage + -(a 0).approx stage + -error
    have hshiftDouble : ∀ t, t < length →
        (2 : Q') * shifted (doubledIndex n t) ≤
          shifted (doubledIndex n (t + 1)) := by
      intro t ht
      dsimp only [shifted]
      exact midpointError_to_homogeneous
        (hprefix stage hstage t ht)
    have htwoAnchor :
        ((a 0).approx stage + error) + error ≈
          (a 0).approx stage + epsilon := by
      refine Q'.eqv_trans _ _ _
        (Q'.add_assoc_eqv ((a 0).approx stage) error error) ?_
      exact Q'.add_eqv_congr_left ((a 0).approx stage)
        (error + error) epsilon (ExpNeg.two_halves epsilon)
    have htwoAnchorStrict :
        ((a 0).approx stage + error) + error <
          (a n).approx stage :=
      Q'.lt_of_le_of_lt (Q'.le_of_eqv htwoAnchor) hstrict
    have hremainingPositive : (0 : Q') <
        (a n).approx stage +
          -(((a 0).approx stage + error) + error) :=
      sub_pos_of_lt htwoAnchorStrict
    have hshiftMinusErrorPositive : (0 : Q') < shifted n + -error := by
      exact lt_of_lt_of_le hremainingPositive
        (Q'.ge_of_eqv (by
          dsimp only [shifted]
          exact error_difference_twice
            ((a n).approx stage) ((a 0).approx stage) error))
    have herrorLtShifted : error < shifted n :=
      lt_of_sub_pos_local hshiftMinusErrorPositive
    have hshiftNonnegative : (0 : Q') ≤ shifted n :=
      Q'.le_trans' _ _ _ (Q'.le_of_lt herrorPositive)
        (Q'.le_of_lt herrorLtShifted)
    have hgrowth := homogeneousDoubling_prefix_growth
      shifted n length hshiftDouble hshiftNonnegative
    have hnegAnchor : -(a 0).approx stage ≤ (0 : Q') := by
      exact Q'.le_trans' _ _ _
        (Q'.neg_le_neg (hanchor stage))
        (Q'.le_of_eqv (by decide : (-(0 : Q')) ≈ 0))
    have hnegError : -error ≤ (0 : Q') := by
      exact Q'.le_trans' _ _ _
        (Q'.neg_le_neg herrorNonnegative)
        (Q'.le_of_eqv (by decide : (-(0 : Q')) ≈ 0))
    have horbitBound : shifted (doubledIndex n length) ≤ bound := by
      have hfirst := Q'.add_le_add
        (hbound (doubledIndex n length) stage) hnegAnchor
      have hsecond := Q'.add_le_add hfirst hnegError
      dsimp only [shifted]
      simpa only [Q'.add_zero'] using hsecond
    have hcap : Q'.ofNat (length + 1) * shifted n ≤ bound :=
      Q'.le_trans' _ _ _ hgrowth horbitBound
    have hscaledStrict :
        Q'.ofNat (length + 1) * error <
          Q'.ofNat (length + 1) * shifted n :=
      Q'.mul_lt_mul_of_pos_left (Q'.ofNat_succ_pos length)
        herrorLtShifted
    have himpossible : bound < bound :=
      lt_of_lt_of_le
        (lt_of_lt_of_le hlength (Q'.le_of_lt hscaledStrict)) hcap
    exact False.elim (lt_irrefl' bound himpossible)

#print axioms midpointDoubling_prefix_eventually
#print axioms homogeneousDoubling_prefix_growth
#print axioms bounded_midpointDoubling_leEv_anchor

end YMGap.Continuum.BoundedMidpointDoublingCReal
