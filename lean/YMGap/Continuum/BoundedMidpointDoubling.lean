/-
# Bounded midpoint doubling forces contraction

If a rational sequence is uniformly bounded above and satisfies

    2 * a(n) <= a(0) + a(2*n),

then every term is at most `a(0)`.  Indeed, any positive excess above the
anchor grows by an arbitrary integer factor along the dyadic orbit and
eventually violates the uniform bound.  This is the constructive algebraic
core needed by reflection-positive transfer arguments; no spectral or
translation-invariance premise is hidden in it.
-/

import YMGap.Constructive.CRealMul
import YMGap.Constructive.RegularCReal
import YMGap.Continuum.ClusteringImpliesGap
import YMGap.Continuum.RingNormaliser

namespace YMGap.Continuum.BoundedMidpointDoubling

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Continuum.ClusteringImpliesGap

local infix:50 " ≈ " => Q'.eqv

/-- The orbit obtained by repeatedly doubling an index. -/
def doubledIndex (n : Nat) : Nat → Nat
  | 0 => n
  | t + 1 => 2 * doubledIndex n t

@[simp] theorem doubledIndex_zero (n : Nat) :
    doubledIndex n 0 = n := rfl

@[simp] theorem doubledIndex_succ (n t : Nat) :
    doubledIndex n (t + 1) = 2 * doubledIndex n t := rfl

private theorem ofNat_mul_eqv_local (a b : Nat) :
    Q'.ofNat (a * b) ≈ Q'.ofNat a * Q'.ofNat b := by
  show _ * (_ : Int) = _ * (_ : Int)
  simp only [Q'.mul_num_cast, Q'.mul_den_cast,
    Q'.ofNat_num_cast, Q'.ofNat_den_cast,
    Int.natCast_mul, Int.mul_one]

private theorem q_lt_of_not_le_local {a b : Q'}
    (h : ¬ a ≤ b) : b < a := by
  have hnum : ¬ (a.num * (b.den : Int) ≤
      b.num * (a.den : Int)) := h
  show b.num * (a.den : Int) < a.num * (b.den : Int)
  exact Int.not_le.mp hnum

private theorem q_not_lt_of_le_local {a b : Q'}
    (h : a ≤ b) : ¬ b < a := by
  intro hlt
  exact Int.not_lt_of_ge h hlt

private def doubleDifferenceL : RingNormaliser.PolyExpr :=
  .mul (.const 2) (.add (.var 0) (.neg (.var 1)))

private def doubleDifferenceR : RingNormaliser.PolyExpr :=
  .add (.mul (.const 2) (.var 0))
    (.neg (.mul (.const 2) (.var 1)))

private theorem doubleDifference_normal :
    RingNormaliser.normalize doubleDifferenceL =
      RingNormaliser.normalize doubleDifferenceR := by decide

private theorem double_difference_regroup (current anchor : Q') :
    (2 : Q') * (current + -anchor) ≈
      (2 : Q') * current + -((2 : Q') * anchor) := by
  simpa [doubleDifferenceL, doubleDifferenceR, RingNormaliser.eval] using
    (RingNormaliser.poly_identity_of_normal_eq
      doubleDifferenceL doubleDifferenceR doubleDifference_normal
      (fun | 0 => current | _ => anchor))

private def shiftedMidpointL : RingNormaliser.PolyExpr :=
  .add (.add (.var 0) (.var 1))
    (.neg (.mul (.const 2) (.var 0)))

private def shiftedMidpointR : RingNormaliser.PolyExpr :=
  .add (.var 1) (.neg (.var 0))

private theorem shiftedMidpoint_normal :
    RingNormaliser.normalize shiftedMidpointL =
      RingNormaliser.normalize shiftedMidpointR := by decide

private theorem shifted_midpoint_regroup (anchor next : Q') :
    (anchor + next) + -((2 : Q') * anchor) ≈ next + -anchor := by
  simpa [shiftedMidpointL, shiftedMidpointR, RingNormaliser.eval] using
    (RingNormaliser.poly_identity_of_normal_eq
      shiftedMidpointL shiftedMidpointR shiftedMidpoint_normal
      (fun | 0 => anchor | _ => next))

/-- Midpoint growth written in anchor-difference coordinates. -/
theorem two_mul_anchorDifference_le_next
    {anchor current next : Q'}
    (hmid : (2 : Q') * current ≤ anchor + next) :
    (2 : Q') * (current + -anchor) ≤ next + -anchor := by
  have hshift := Q'.add_le_add_right
    ((2 : Q') * current) (anchor + next)
    (-((2 : Q') * anchor)) hmid
  have hleft :
      (2 : Q') * (current + -anchor) ≈
        (2 : Q') * current + -((2 : Q') * anchor) := by
    exact double_difference_regroup current anchor
  have hright :
      (anchor + next) + -((2 : Q') * anchor) ≈
        next + -anchor := by
    exact shifted_midpoint_regroup anchor next
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
    (Q'.le_trans' _ _ _ hshift (Q'.le_of_eqv hright))

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
    exact Q'.mul_assoc_eqv _ _ _
  exact Q'.le_trans' _ _ _ hmul (Q'.le_of_eqv hfactor)

/-- Along the dyadic orbit, an initial nonnegative excess grows by at least
the arbitrary integer factor `t+1`. -/
theorem midpointDoubling_excess_growth
    (a : Nat → Q')
    (hmid : ∀ n,
      (2 : Q') * a n ≤ a 0 + a (2 * n))
    (n : Nat)
    (hexcess : (0 : Q') ≤ a n + -a 0) :
    ∀ t,
      Q'.ofNat (t + 1) * (a n + -a 0) ≤
        a (doubledIndex n t) + -a 0
  | 0 => by
      apply Q'.le_of_eqv
      exact Q'.eqv_trans _ _ _
        (Q'.one_mul_eqv (a n + -a 0))
        (Q'.eqv_refl _)
  | t + 1 => by
      have hfactor := successor_factor_le_double t hexcess
      have hind := midpointDoubling_excess_growth a hmid n hexcess t
      have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ (2 : Q')
        hind (by decide)
      have hnext := two_mul_anchorDifference_le_next
        (hmid (doubledIndex n t))
      exact Q'.le_trans' _ _ _ hfactor
        (Q'.le_trans' _ _ _ hscaled (by
          simpa only [doubledIndex_succ] using hnext))

/-- A uniformly upper-bounded midpoint-doubling sequence cannot rise above
its anchor.  This is a fully constructive rational theorem. -/
theorem bounded_midpointDoubling_le_anchor
    (a : Nat → Q') (bound : Q')
    (hbound : ∀ n, a n ≤ bound)
    (hmid : ∀ n,
      (2 : Q') * a n ≤ a 0 + a (2 * n))
    (n : Nat) :
    a n ≤ a 0 := by
  by_cases hle : a n ≤ a 0
  · exact hle
  · have hlt : a 0 < a n := q_lt_of_not_le_local hle
    let excess := a n + -a 0
    have hexcessPos : (0 : Q') < excess := by
      dsimp only [excess]
      exact sub_pos_of_lt hlt
    have hexcess : (0 : Q') ≤ excess := Q'.le_of_lt hexcessPos
    obtain ⟨t, ht⟩ := exists_succ_mul_gt
      (bound + -a 0) excess hexcessPos
    have hgrowth := midpointDoubling_excess_growth
      a hmid n (by simpa only [excess] using hexcess) t
    have hcap : a (doubledIndex n t) + -a 0 ≤ bound + -a 0 :=
      Q'.add_le_add_right _ _ (-a 0)
        (hbound (doubledIndex n t))
    have hleCap : Q'.ofNat (t + 1) * excess ≤ bound + -a 0 := by
      dsimp only [excess]
      exact Q'.le_trans' _ _ _ hgrowth hcap
    exact False.elim ((q_not_lt_of_le_local hleCap) ht)

#print axioms doubledIndex
#print axioms two_mul_anchorDifference_le_next
#print axioms midpointDoubling_excess_growth
#print axioms bounded_midpointDoubling_le_anchor

end YMGap.Continuum.BoundedMidpointDoubling
