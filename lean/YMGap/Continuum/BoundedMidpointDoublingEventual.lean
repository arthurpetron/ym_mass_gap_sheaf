/-
# Bounded midpoint doubling with EVENTUAL original-real bounds

A uniform eventual upper cap and an eventually nonnegative anchor suffice:
2 a(n) <= a(0)+a(2n) implies a(n) <= a(0). Only a finite dyadic orbit
is synchronized at each tolerance. Its terminal bound and the anchor bound
are synchronized separately; no universal approximation index is assumed.

This is a scalar order theorem, not an assumed contraction for a physical
model. The caller must supply its actual recurrence and uniform orbit cap.
All threshold eliminations stay in the proposition being proved.
-/

import YMGap.Continuum.BoundedMidpointDoublingCReal

namespace YMGap.Continuum.BoundedMidpointDoublingEventual

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BoundedMidpointDoubling
open YMGap.Continuum.BoundedMidpointDoublingError (midpointError_to_homogeneous)
open YMGap.Continuum.BoundedMidpointDoublingCReal
  (midpointDoubling_prefix_eventually homogeneousDoubling_prefix_growth)
open YMGap.Continuum.ClusteringImpliesGap

local infix:50 " ≈ " => Q'.eqv

private theorem q_lt_of_not_le {a b : Q'} (h : ¬ a ≤ b) : b < a := by
  have hn : ¬ (a.num * (b.den : Int) ≤ b.num * (a.den : Int)) := h
  exact Int.not_le.mp hn

private theorem lt_of_sub_pos {a b : Q'} (h : (0 : Q') < b + (-a)) : a < b := by
  have hn : (0 : Int) < b.num * (a.den : Int) + (-a.num) * (b.den : Int) := Q'.num_pos_of_pos h
  rw [Int.neg_mul] at hn
  show a.num * (b.den : Int) < b.num * (a.den : Int)
  omega

private theorem error_difference_once (current anchor error : Q') :
    current + -anchor + -error ≈ current + -(anchor + error) :=
  RingNormaliser.poly_identity_of_normal_eq
    (.add (.add (.var 0) (.neg (.var 1))) (.neg (.var 2)))
    (.add (.var 0) (.neg (.add (.var 1) (.var 2)))) (by decide)
    (fun | 0 => current | 1 => anchor | _ => error)

private theorem error_difference_twice (current anchor error : Q') :
    current + -anchor + -error + -error ≈ current + -((anchor + error) + error) :=
  RingNormaliser.poly_identity_of_normal_eq
    (.add (.add (.add (.var 0) (.neg (.var 1))) (.neg (.var 2))) (.neg (.var 2)))
    (.add (.var 0) (.neg (.add (.add (.var 1) (.var 2)) (.var 2)))) (by decide)
    (fun | 0 => current | 1 => anchor | _ => error)

/-- Eventual caps are sufficient; their representative thresholds may depend on n. -/
theorem bounded_midpointDoubling_leEv_anchor (a : Nat → CReal) (bound : Q')
    (hbound : ∀ n, leEv (a n) (ofQ' bound)) (hanchor : leEv czero (a 0))
    (hmid : ∀ n, leEv (CReal.mul (ofQ' 2) (a n)) (CReal.add (a 0) (a (2*n)))) (n : Nat) :
    leEv (a n) (a 0) := by
  intro epsilon hepsilon
  let error := HalfPow.half * epsilon
  have he : (0 : Q') < error := ExpNeg.half_mul_pos epsilon hepsilon
  obtain ⟨length, hlength⟩ := exists_succ_mul_gt (bound+1) error he
  obtain ⟨midCutoff, hmidCutoff⟩ := midpointDoubling_prefix_eventually a hmid error he n length
  obtain ⟨boundCutoff, hboundCutoff⟩ := hbound (doubledIndex n length) 1 (by decide)
  obtain ⟨anchorCutoff, hanchorCutoff⟩ := hanchor error he
  refine ⟨max (max midCutoff boundCutoff) anchorCutoff, fun stage hstage => ?_⟩
  have hm : midCutoff ≤ stage := Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)) hstage
  have hb : boundCutoff ≤ stage := Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)) hstage
  have ha : anchorCutoff ≤ stage := Nat.le_trans (Nat.le_max_right _ _) hstage
  by_cases hle : (a n).approx stage ≤ (a 0).approx stage + epsilon
  · exact hle
  · have hstrict := q_lt_of_not_le hle
    let shifted : Nat → Q' := fun k => (a k).approx stage + -(a 0).approx stage + -error
    have hdouble : ∀ t, t < length → (2 : Q') * shifted (doubledIndex n t) ≤ shifted (doubledIndex n (t+1)) := by
      intro t ht
      exact midpointError_to_homogeneous (hmidCutoff stage hm t ht)
    have htwo : ((a 0).approx stage + error) + error ≈ (a 0).approx stage + epsilon :=
      Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv _ _ _)
        (Q'.add_eqv_congr_left _ _ _ (ExpNeg.two_halves epsilon))
    have htwoStrict := Q'.lt_of_le_of_lt (Q'.le_of_eqv htwo) hstrict
    have hremaining : (0 : Q') < shifted n + -error :=
      lt_of_lt_of_le (sub_pos_of_lt htwoStrict) (Q'.ge_of_eqv (error_difference_twice _ _ _))
    have herrorLt : error < shifted n := lt_of_sub_pos hremaining
    have hshiftNonnegative : (0 : Q') ≤ shifted n := Q'.le_trans' _ _ _ (Q'.le_of_lt he) (Q'.le_of_lt herrorLt)
    have hgrowth := homogeneousDoubling_prefix_growth shifted n length hdouble hshiftNonnegative
    have hneg : -((a 0).approx stage + error) ≤ (0 : Q') :=
      Q'.le_trans' _ _ _ (Q'.neg_le_neg (hanchorCutoff stage ha))
        (Q'.le_of_eqv (by decide : (-(0 : Q')) ≈ 0))
    have horbitBound : shifted (doubledIndex n length) ≤ bound+1 :=
      Q'.le_trans' _ _ _ (Q'.le_of_eqv (error_difference_once _ _ _))
        (Q'.le_trans' _ _ _ (Q'.add_le_add (hboundCutoff stage hb) hneg)
          (Q'.le_of_eqv (Q'.eqv_of_eq (Q'.add_zero' (bound+1)))))
    have hcap : Q'.ofNat (length+1) * shifted n ≤ bound+1 := Q'.le_trans' _ _ _ hgrowth horbitBound
    have hscaled := Q'.mul_lt_mul_of_pos_left (Q'.ofNat_succ_pos length) herrorLt
    have himpossible : bound+1 < bound+1 :=
      lt_of_lt_of_le (lt_of_lt_of_le hlength (Q'.le_of_lt hscaled)) hcap
    exact False.elim (lt_irrefl' (bound+1) himpossible)

end YMGap.Continuum.BoundedMidpointDoublingEventual

#print axioms YMGap.Continuum.BoundedMidpointDoublingEventual.bounded_midpointDoubling_leEv_anchor
