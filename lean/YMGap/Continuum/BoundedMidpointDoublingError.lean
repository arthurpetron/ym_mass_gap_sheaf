/-
# Bounded midpoint doubling with a uniform additive defect

The exact midpoint theorem has a stable error form.  If a uniformly
upper-bounded rational sequence satisfies

    2 * a(n) <= a(0) + a(2*n) + eta

with `eta >= 0`, then `a(n) <= a(0) + eta`.  Subtracting both the anchor and
the error turns the recurrence into homogeneous doubling.  Any remaining
positive excess then grows without bound on the dyadic orbit.

This is only an algebraic consumer.  It does not manufacture the uniform cap
or the model-specific recurrence.
-/

import YMGap.Continuum.BoundedMidpointDoubling

namespace YMGap.Continuum.BoundedMidpointDoublingError

set_option maxRecDepth 100000
set_option maxHeartbeats 1500000

open YMGap.Constructive
open YMGap.Continuum.BoundedMidpointDoubling
open YMGap.Continuum.ClusteringImpliesGap

local infix:50 " ≈ " => Q'.eqv

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

/-- Homogeneous doubling grows a nonnegative value by every integer factor
along the dyadic orbit. -/
theorem homogeneousDoubling_growth
    (a : Nat → Q')
    (hdouble : ∀ n, (2 : Q') * a n ≤ a (2 * n))
    (n : Nat) (hnonneg : (0 : Q') ≤ a n) :
    ∀ t, Q'.ofNat (t + 1) * a n ≤ a (doubledIndex n t)
  | 0 => by
      apply Q'.le_of_eqv
      exact Q'.one_mul_eqv (a n)
  | t + 1 => by
      have hfactor := successor_factor_le_double t hnonneg
      have hind := homogeneousDoubling_growth a hdouble n hnonneg t
      have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ (2 : Q')
        hind (by decide)
      exact Q'.le_trans' _ _ _ hfactor
        (Q'.le_trans' _ _ _ hscaled (by
          simpa only [doubledIndex_succ] using
            hdouble (doubledIndex n t)))

/-- A uniformly upper-bounded homogeneous-doubling sequence is nonpositive. -/
theorem bounded_homogeneousDoubling_le_zero
    (a : Nat → Q') (bound : Q')
    (hbound : ∀ n, a n ≤ bound)
    (hdouble : ∀ n, (2 : Q') * a n ≤ a (2 * n))
    (n : Nat) : a n ≤ 0 := by
  by_cases hle : a n ≤ 0
  · exact hle
  · have hpos : (0 : Q') < a n := q_lt_of_not_le_local hle
    have hnonneg : (0 : Q') ≤ a n := Q'.le_of_lt hpos
    obtain ⟨t, ht⟩ := exists_succ_mul_gt bound (a n) hpos
    have hgrowth := homogeneousDoubling_growth a hdouble n hnonneg t
    have hcap := hbound (doubledIndex n t)
    have hleCap : Q'.ofNat (t + 1) * a n ≤ bound :=
      Q'.le_trans' _ _ _ hgrowth hcap
    exact False.elim ((q_not_lt_of_le_local hleCap) ht)

private def errorShiftLeftTarget : RingNormaliser.PolyExpr :=
  .mul (.const 2)
    (.add (.add (.var 0) (.neg (.var 1))) (.neg (.var 3)))

private def errorShiftLeftRaw : RingNormaliser.PolyExpr :=
  .add (.mul (.const 2) (.var 0))
    (.neg (.add (.mul (.const 2) (.var 1))
      (.mul (.const 2) (.var 3))))

private theorem errorShiftLeft_normal :
    RingNormaliser.normalize errorShiftLeftTarget =
      RingNormaliser.normalize errorShiftLeftRaw := by decide

private def errorShiftRightRaw : RingNormaliser.PolyExpr :=
  .add (.add (.add (.var 1) (.var 2)) (.var 3))
    (.neg (.add (.mul (.const 2) (.var 1))
      (.mul (.const 2) (.var 3))))

private def errorShiftRightTarget : RingNormaliser.PolyExpr :=
  .add (.add (.var 2) (.neg (.var 1))) (.neg (.var 3))

private theorem errorShiftRight_normal :
    RingNormaliser.normalize errorShiftRightRaw =
      RingNormaliser.normalize errorShiftRightTarget := by decide

/-- Subtracting the anchor and the uniform error makes the defective midpoint
recurrence homogeneous. -/
theorem midpointError_to_homogeneous
    {anchor current next error : Q'}
    (hmid : (2 : Q') * current ≤ anchor + next + error) :
    (2 : Q') * (current + -anchor + -error) ≤
      next + -anchor + -error := by
  let value : Nat → Q'
    | 0 => current
    | 1 => anchor
    | 2 => next
    | _ => error
  have hleft :
      (2 : Q') * (current + -anchor + -error) ≈
        (2 : Q') * current +
          -((2 : Q') * anchor + (2 : Q') * error) := by
    simpa [errorShiftLeftTarget, errorShiftLeftRaw,
      RingNormaliser.eval, value] using
      (RingNormaliser.poly_identity_of_normal_eq
        errorShiftLeftTarget errorShiftLeftRaw errorShiftLeft_normal value)
  have hright :
      (anchor + next + error) +
          -((2 : Q') * anchor + (2 : Q') * error) ≈
        next + -anchor + -error := by
    simpa [errorShiftRightRaw, errorShiftRightTarget,
      RingNormaliser.eval, value] using
      (RingNormaliser.poly_identity_of_normal_eq
        errorShiftRightRaw errorShiftRightTarget errorShiftRight_normal value)
  have hshift := Q'.add_le_add_right
    ((2 : Q') * current) (anchor + next + error)
    (-((2 : Q') * anchor + (2 : Q') * error)) hmid
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
    (Q'.le_trans' _ _ _ hshift (Q'.le_of_eqv hright))

private def errorDifferenceRaw : RingNormaliser.PolyExpr :=
  .add (.add (.var 0) (.neg (.var 1))) (.neg (.var 2))

private def errorDifferenceTarget : RingNormaliser.PolyExpr :=
  .add (.var 0) (.neg (.add (.var 1) (.var 2)))

private theorem errorDifference_normal :
    RingNormaliser.normalize errorDifferenceRaw =
      RingNormaliser.normalize errorDifferenceTarget := by decide

private theorem error_difference_regroup (current anchor error : Q') :
    current + -anchor + -error ≈ current + -(anchor + error) := by
  simpa [errorDifferenceRaw, errorDifferenceTarget,
    RingNormaliser.eval] using
    (RingNormaliser.poly_identity_of_normal_eq
      errorDifferenceRaw errorDifferenceTarget errorDifference_normal
      (fun | 0 => current | 1 => anchor | _ => error))

private theorem le_add_of_sub_le_local {a b c : Q'}
    (h : a + -b ≤ c) : a ≤ b + c := by
  have hstep := Q'.add_le_add_right (a + -b) c b h
  have hleft : (a + -b) + b ≈ a := by
    refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv a (-b) b) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left a (-b + b) 0
        (Q'.neg_add_self_eqv b)) ?_
    exact Q'.eqv_of_eq (Q'.add_zero' a)
  have hright : c + b ≈ b + c := Q'.add_comm_eqv c b
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hleft)
    (Q'.le_trans' _ _ _ hstep (Q'.le_of_eqv hright))

/-- Uniform additive-error form of bounded midpoint doubling. -/
theorem bounded_midpointDoubling_le_anchor_add_error
    (a : Nat → Q') (bound error : Q')
    (herror : (0 : Q') ≤ error)
    (hbound : ∀ n, a n ≤ bound)
    (hmid : ∀ n,
      (2 : Q') * a n ≤ a 0 + a (2 * n) + error)
    (n : Nat) :
    a n ≤ a 0 + error := by
  by_cases hn : n = 0
  · subst n
    exact Q'.add_le_self_of_nonneg (a 0) error herror
  let shifted : Nat → Q' := fun k => a k + -a 0 + -error
  have hshiftBound : ∀ k, shifted k ≤ bound + -a 0 + -error := by
    intro k
    dsimp only [shifted]
    have hfirst := Q'.add_le_add_right (a k) bound (-a 0) (hbound k)
    exact Q'.add_le_add_right _ _ (-error) hfirst
  have hshiftDouble : ∀ k,
      (2 : Q') * shifted k ≤ shifted (2 * k) := by
    intro k
    dsimp only [shifted]
    exact midpointError_to_homogeneous (hmid k)
  have hzero := bounded_homogeneousDoubling_le_zero shifted
    (bound + -a 0 + -error) hshiftBound hshiftDouble n
  have hsub : a n + -(a 0 + error) ≤ 0 :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.eqv_symm
        (error_difference_regroup (a n) (a 0) error))) hzero
  have hrearranged := le_add_of_sub_le_local hsub
  exact Q'.le_trans' _ _ _ hrearranged
    (Q'.le_of_eqv (Q'.eqv_of_eq (Q'.add_zero' (a 0 + error))))

#print axioms homogeneousDoubling_growth
#print axioms bounded_homogeneousDoubling_le_zero
#print axioms midpointError_to_homogeneous
#print axioms bounded_midpointDoubling_le_anchor_add_error

end YMGap.Continuum.BoundedMidpointDoublingError
