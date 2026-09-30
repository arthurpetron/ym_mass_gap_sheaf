/-
# Order is preserved by same-carrier completed norm limits

This is the elementary order-closure step for the original completed
pairing. The two approximating streams carry explicit distance moduli; no
boundedness hypothesis is imposed on any preimage or representative.
-/

import YMGap.Continuum.BF4WilsonAllNomeGraphDistance
import YMGap.Continuum.BF4WilsonAllNomeCompletedPairingContinuity
import YMGap.Continuum.CRealSeminormPairingCompletion

namespace YMGap.Continuum.BF4WilsonAllNomeNormLimitOrder

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeDistance
open YMGap.Continuum.BF4WilsonAllNomeLinear
open YMGap.Continuum.BF4WilsonAllNomeGraphDistance (dist_zero_right)
open YMGap.Continuum.BF4WilsonAllNomeCompletedPairingContinuity
  (pairing_close)
open YMGap.Continuum.BF4ExactSlabPlaquettePairingContinuity
  (pairingTolerance pairingTolerance_pos)
open YMGap.Continuum.CRealSeminormPairingCompletion
  (normCeiling normCeiling_nonnegative completedInner_diagonal_le_normCeiling)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "P" => pairingData hw0 hw1 (width := width)
local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "d" => completedDist hw0 hw1
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

private theorem rat_two_halves (a : RC) (e : Q') :
    RCadd (RCadd a (rat (HalfPow.half*e))) (rat (HalfPow.half*e)) =
      RCadd a (rat e) := by
  refine Quotient.inductionOn a ?_
  intro X
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun _ =>
    Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv _ _ _)
      (Q'.add_eqv_congr_left _ _ _ (ExpNeg.two_halves e))))

private def limitPairingCap (cx cy : Q') : Q' :=
  Q'.max' (Q'.max' cx cy)
    (Q'.max' ((1+1)+(cx+cx)) ((1+1)+(cy+cy)))

private theorem limitPairingCap_nonnegative (cx cy : Q')
    (hcx : (0 : Q') ≤ cx) (_hcy : (0 : Q') ≤ cy) :
    (0 : Q') ≤ limitPairingCap cx cy := by
  unfold limitPairingCap
  exact Q'.le_trans' _ _ _ (Q'.le_trans' _ _ _ hcx (Q'.le_max'_left _ _))
    (Q'.le_max'_left _ _)

private theorem limitPairingCap_bounds (cx cy : Q') :
    cx ≤ limitPairingCap cx cy ∧ cy ≤ limitPairingCap cx cy ∧
    (1+1)+(cx+cx) ≤ limitPairingCap cx cy ∧
    (1+1)+(cy+cy) ≤ limitPairingCap cx cy := by
  constructor
  · exact Q'.le_trans' _ _ _ (Q'.le_max'_left _ _) (Q'.le_max'_left _ _)
  constructor
  · exact Q'.le_trans' _ _ _ (Q'.le_max'_right _ _) (Q'.le_max'_left _ _)
  constructor
  · exact Q'.le_trans' _ _ _ (Q'.le_max'_left _ _) (Q'.le_max'_right _ _)
  · exact Q'.le_trans' _ _ _ (Q'.le_max'_right _ _) (Q'.le_max'_right _ _)

private theorem nearby_diagonal_cap (s x : V) (c : Q')
    (hc : RCle (B x x) (rat c))
    (hd : RCle (d s x) (rat 1)) :
    RCle (B s s) (rat ((1+1)+(c+c))) := by
  have htri := completedDist_triangle hw0 hw1 s x Z
  rw [dist_zero_right, dist_zero_right] at htri
  have htwice := RCadd_le_add (RCadd_le_add hd hd) (RCadd_le_add hc hc)
  have h := RCle_trans htri htwice
  rwa [rat_four_sum] at h

/-- If two streams converge in the supplied completed squared-distance
moduli and their diagonal pairings are ordered at every stage, then the same
order holds for their limits on the original carrier. -/
theorem norm_limit_order
    (xs ys : Nat → V) (x y : V)
    (mx my : Q' → Nat)
    (bx : ∀ (epsilon : Q'), (0 : Q') < epsilon → ∀ n, mx epsilon ≤ n →
      RCle (d (xs n) x) (rat epsilon))
    (byy : ∀ (epsilon : Q'), (0 : Q') < epsilon → ∀ n, my epsilon ≤ n →
      RCle (d (ys n) y) (rat epsilon))
    (hstage : ∀ n, RCle (B (xs n) (xs n)) (B (ys n) (ys n))) :
    RCle (B x x) (B y y) := by
  obtain ⟨cx, hcx0, hcx⟩ := norm_ceiling hw0 hw1 x
  obtain ⟨cy, hcy0, hcy⟩ := norm_ceiling hw0 hw1 y
  let cap := limitPairingCap cx cy
  have hcap : (0 : Q') ≤ cap := limitPairingCap_nonnegative cx cy hcx0 hcy0
  have hcaps := limitPairingCap_bounds cx cy
  apply RationalScalarTwoSidedError.le_of_all_errors
  intro epsilon hepsilon
  let q := HalfPow.half * epsilon
  have hq : (0 : Q') < q := ExpNeg.half_mul_pos epsilon hepsilon
  let delta := pairingTolerance cap hcap q
  have hdelta : (0 : Q') < delta := pairingTolerance_pos cap hcap hq
  let n := max (max (mx delta) (my delta)) (max (mx 1) (my 1))
  have hbx := bx delta hdelta n
    (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _))
  have hby := byy delta hdelta n
    (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _))
  have hbx1 := bx 1 (by decide) n
    (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _))
  have hby1 := byy 1 (by decide) n
    (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))
  have hxs : RCle (B (xs n) (xs n)) (rat ((1+1)+(cx+cx))) :=
    nearby_diagonal_cap hw0 hw1 (xs n) x cx hcx hbx1
  have hys : RCle (B (ys n) (ys n)) (rat ((1+1)+(cy+cy))) :=
    nearby_diagonal_cap hw0 hw1 (ys n) y cy hcy hby1
  have hxsCap : RCle (B (xs n) (xs n)) (rat cap) :=
    RCle_trans hxs (leEv_le_ofQ'_of_approx_le (fun _ => hcaps.2.2.1))
  have hysCap : RCle (B (ys n) (ys n)) (rat cap) :=
    RCle_trans hys (leEv_le_ofQ'_of_approx_le (fun _ => hcaps.2.2.2))
  have hxc : RCle (B x x) (rat cap) :=
    RCle_trans hcx (leEv_le_ofQ'_of_approx_le (fun _ => hcaps.1))
  have hyc : RCle (B y y) (rat cap) :=
    RCle_trans hcy (leEv_le_ofQ'_of_approx_le (fun _ => hcaps.2.1))
  have hcloseX := pairing_close hw0 hw1 (xs n) x (xs n) x
    cap hcap q hq hbx hbx hxsCap hxc
  have hcloseY := pairing_close hw0 hw1 (ys n) y (ys n) y
    cap hcap q hq hby hby hysCap hyc
  have hfinite := hstage n
  have hleft := hcloseX.2
  have hright := hcloseY.1
  have hmid : RCle (B x x) (RCadd (B (ys n) (ys n)) (rat q)) :=
    RCle_trans hleft
      (RCadd_le_add hfinite (RCle_refl (rat q)))
  have hfinal : RCle (B x x)
      (RCadd (RCadd (B y y) (rat q)) (rat q)) :=
    RCle_trans hmid (RCadd_le_add hright (RCle_refl (rat q)))
  rw [rat_two_halves (B y y) epsilon] at hfinal
  exact hfinal

#print axioms norm_limit_order

end YMGap.Continuum.BF4WilsonAllNomeNormLimitOrder
