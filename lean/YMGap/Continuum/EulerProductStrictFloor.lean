/-
# A computable strictly positive Euler-product floor

Keep the first K factors, with K computed from the geometric tail budget.
Every remaining finite segment loses at most one half. Consequently
E_Q(N) >= E_Q(K)/2 > 0 at EVERY N, for each supplied rational 0<Q<1.
The floor and cutoff depend on Q; no uniformity as Q approaches one is claimed.
-/

import YMGap.Continuum.FiniteJacobiWeightConvergence

namespace YMGap.Continuum.EulerProductStrictFloor

open YMGap.Constructive
open YMGap.Constructive.Q'
open YMGap.Continuum.GaussQBinomEulerNormalization
open YMGap.Continuum.GaussQBinomEulerQuotient
open YMGap.Continuum.FiniteEulerSegment
open YMGap.Continuum.FiniteJacobiWeightConvergence

local infix:50 " ≈ " => Q'.eqv

/-- Computed prefix length at the named base Q. -/
def cutoff (Q : Q') : Nat := lossCutoff Q HalfPow.half

/-- The retained finite prefix, halved to pay for its entire tail. -/
def floor (Q : Q') : Q' := euler Q (cutoff Q) * HalfPow.half

theorem floor_pos {Q : Q'} (hQ0 : (0 : Q') < Q) (hQ1 : Q < (1 : Q')) :
    (0 : Q') < floor Q :=
  HKPos.q_mul_pos (euler_pos hQ0 hQ1 _) (by decide)

/-- The actual Euler product decreases when more factors are included. -/
theorem euler_antitone {Q : Q'} (hQ0 : (0 : Q') < Q) (hQ1 : Q < (1 : Q'))
    {m n : Nat} (hmn : m ≤ n) : euler Q n ≤ euler Q m := by
  have he := euler_split Q m (n - m)
  rw [Nat.add_sub_of_le hmn] at he
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv he)
    (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ _ (segment_le_one hQ0 hQ1 m (n - m))
        (Q'.le_of_lt (euler_pos hQ0 hQ1 m)))
      (Q'.le_of_eqv (Q'.mul_one_eqv _)))

/-- All finite tails after the computed prefix are bounded below by half. -/
theorem segment_ge_half {Q : Q'} (hQ0 : (0 : Q') < Q) (hQ1 : Q < (1 : Q'))
    (len : Nat) : HalfPow.half ≤ segment Q (cutoff Q) len := by
  have htail : HKConvGen.geoTailBase 1 Q (cutoff Q + 1) ≤ HalfPow.half := by
    have hdom : HKConvGen.geoTailBase 1 Q (cutoff Q + 1)
        ≤ FiniteJacobiWeightBounds.lossBound Q (cutoff Q + 1) := by
      exact Q'.mul_le_mul_of_nonneg_right _ _ _
        (Q'.mul_le_mul_of_nonneg_right 1 2 _ (by decide)
          (Q'.pow_nonneg Q (Q'.le_of_lt hQ0) _))
        (HKConv.divPos_nonneg Q'.zero_le_one)
    exact Q'.le_trans' _ _ _ hdom
      (lossBound_le hQ0 hQ1 (by decide) _ (by unfold cutoff; omega))
  have hhalf : HalfPow.half ≤ 1 - HKConvGen.geoTailBase 1 Q (cutoff Q + 1) :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv (by decide : HalfPow.half ≈ 1 - HalfPow.half))
      (Q'.add_le_add_left 1 _ _ (Q'.neg_le_neg htail))
  exact Q'.le_trans' _ _ _ hhalf (segment_ge_one_sub_tail hQ0 hQ1 _ len)

/-- Uniform in the named truncation N, with a strictly positive Q-dependent
floor returned by the definition above. No limiting denominator is assumed. -/
theorem floor_le_euler {Q : Q'} (hQ0 : (0 : Q') < Q) (hQ1 : Q < (1 : Q'))
    (N : Nat) : floor Q ≤ euler Q N := by
  by_cases hN : cutoff Q ≤ N
  · have he := euler_split Q (cutoff Q) (N - cutoff Q)
    rw [Nat.add_sub_of_le hN] at he
    exact Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ _ (segment_ge_half hQ0 hQ1 _)
        (Q'.le_of_lt (euler_pos hQ0 hQ1 _)))
      (Q'.ge_of_eqv he)
  · exact Q'.le_trans' _ _ _
      (Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_left HalfPow.half 1 _ (by decide)
          (Q'.le_of_lt (euler_pos hQ0 hQ1 _)))
        (Q'.le_of_eqv (Q'.mul_one_eqv _)))
      (euler_antitone hQ0 hQ1 (by omega))

end YMGap.Continuum.EulerProductStrictFloor

#print axioms YMGap.Continuum.EulerProductStrictFloor.cutoff
#print axioms YMGap.Continuum.EulerProductStrictFloor.floor
#print axioms YMGap.Continuum.EulerProductStrictFloor.floor_pos
#print axioms YMGap.Continuum.EulerProductStrictFloor.euler_antitone
#print axioms YMGap.Continuum.EulerProductStrictFloor.segment_ge_half
#print axioms YMGap.Continuum.EulerProductStrictFloor.floor_le_euler
