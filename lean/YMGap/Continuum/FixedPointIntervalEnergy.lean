/-
Track 11.7-fusion / R3w -- certified fixed-point intervals for path energies.

The fine even/odd reserve is most stable in the positive Dirichlet form.  Its
terms are squares of differences between two nearby heat-kernel coefficients,
so independently rounding the expanded subtraction would lose the physical
margin.  This module instead proves a small interval-arithmetic kernel:

* endpoint intervals give a certified lower distance when they are disjoint;
* the larger of the two outward endpoint gaps gives a certified upper distance;
* floor/ceiling multiplication turns those distance bounds into square bounds.

The checker therefore manipulates natural numerators and binary power tables,
while the proof below establishes once and for all that the checked numerators
bound the exact rational Dirichlet energy.

No `Classical`, `native_decide`, `sorry`, custom axiom, or noncomputable
declaration.
-/

import YMGap.Continuum.FixedPointPowerInterval

namespace YMGap.Continuum.FixedPointIntervalEnergy

set_option maxHeartbeats 4000000
set_option maxRecDepth 30000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.FixedPointPowerInterval

local infix:50 " ≈ " => Q'.eqv

/-- Lower distance between two closed natural-numerator intervals. -/
def intervalLowerGap (loA hiA loB hiB : Nat) : Nat :=
  if hiA <= loB then loB - hiA
  else if hiB <= loA then loA - hiB
  else 0

/-- Upper distance between two closed natural-numerator intervals. -/
def intervalUpperGap (loA hiA loB hiB : Nat) : Nat :=
  Nat.max (hiA - loB) (hiB - loA)

private def subSquareL : RingNormaliser.PolyExpr :=
  .mul (.add (.var 0) (.neg (.var 1)))
    (.add (.var 0) (.neg (.var 1)))

private def subSquareR : RingNormaliser.PolyExpr :=
  .mul (.add (.var 1) (.neg (.var 0)))
    (.add (.var 1) (.neg (.var 0)))

private theorem subSquare_normal :
    RingNormaliser.normalize subSquareL =
      RingNormaliser.normalize subSquareR := by decide

theorem sub_square_comm_eqv (a b : Q') :
    (a + -b) * (a + -b) ≈ (b + -a) * (b + -a) := by
  simpa [subSquareL, subSquareR, RingNormaliser.eval] using
    (RingNormaliser.poly_identity_of_normal_eq
      subSquareL subSquareR subSquare_normal
      (fun | 0 => a | _ => b))

/-- A signed common-denominator difference is below its truncated natural
difference.  When the signed difference is negative the truncation is zero. -/
theorem fixedPointVal_sub_le_truncated
    (scale : Nat) (hScale : 0 < scale) (a b : Nat) :
    fixedPointVal scale hScale a +
        -(fixedPointVal scale hScale b) <=
      fixedPointVal scale hScale (a - b) := by
  rcases Nat.le_total b a with hba | hab
  · exact Q'.le_of_eqv
      (Q'.eqv_symm (fixedPointVal_sub_eqv scale hScale a b hba))
  · have hsigned : fixedPointVal scale hScale a +
        -(fixedPointVal scale hScale b) <= (0 : Q') := by
      have h := fixedPointVal_mono scale hScale hab
      have hadd := Q'.add_le_add_right _ _
        (-(fixedPointVal scale hScale b)) h
      exact Q'.le_trans' _ _ _ hadd
        (Q'.le_of_eqv
          (Q'.add_neg_self_eqv (fixedPointVal scale hScale b)))
    have hsub : a - b = 0 := Nat.sub_eq_zero_of_le hab
    rw [hsub]
    exact Q'.le_trans' _ _ _ hsigned
      (fixedPointVal_nonneg scale hScale 0)

private theorem lowerGap_right_le
    (scale : Nat) (hScale : 0 < scale)
    {a b : Q'} {hiA loB : Nat}
    (haHi : a <= fixedPointVal scale hScale hiA)
    (hbLo : fixedPointVal scale hScale loB <= b)
    (hsep : hiA <= loB) :
    fixedPointVal scale hScale (loB - hiA) <= b + -a := by
  have hgap := fixedPointVal_sub_eqv scale hScale loB hiA hsep
  have hneg := Q'.neg_le_neg haHi
  have hadd := Q'.add_le_add hbLo hneg
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hgap) hadd

private theorem lowerGap_left_le
    (scale : Nat) (hScale : 0 < scale)
    {a b : Q'} {loA hiB : Nat}
    (haLo : fixedPointVal scale hScale loA <= a)
    (hbHi : b <= fixedPointVal scale hScale hiB)
    (hsep : hiB <= loA) :
    fixedPointVal scale hScale (loA - hiB) <= a + -b := by
  have hgap := fixedPointVal_sub_eqv scale hScale loA hiB hsep
  have hneg := Q'.neg_le_neg hbHi
  have hadd := Q'.add_le_add haLo hneg
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hgap) hadd

/-- Downward-rounded squared interval distance is below the exact squared
difference.  Overlapping intervals deliberately return the safe lower bound
zero. -/
theorem intervalLowerSquare_sound
    (scale : Nat) (hScale : 0 < scale)
    (loA hiA loB hiB : Nat) (a b : Q')
    (haLo : fixedPointVal scale hScale loA <= a)
    (haHi : a <= fixedPointVal scale hScale hiA)
    (hbLo : fixedPointVal scale hScale loB <= b)
    (hbHi : b <= fixedPointVal scale hScale hiB) :
    fixedPointVal scale hScale
        (floorMul scale
          (intervalLowerGap loA hiA loB hiB)
          (intervalLowerGap loA hiA loB hiB)) <=
      (a + -b) * (a + -b) := by
  let gap := intervalLowerGap loA hiA loB hiB
  have hfloor := floorMul_sound scale hScale gap gap
  change fixedPointVal scale hScale (floorMul scale gap gap) <=
    (a + -b) * (a + -b)
  by_cases hright : hiA <= loB
  · have hgapDef : gap = loB - hiA := by
      simp only [gap, intervalLowerGap, if_pos hright]
    have hgap := lowerGap_right_le scale hScale haHi hbLo hright
    have hgap' : fixedPointVal scale hScale gap <= b + -a := by
      simpa only [hgapDef] using hgap
    have hgap0 : (0 : Q') <= fixedPointVal scale hScale gap :=
      fixedPointVal_nonneg _ _ _
    have hdiff0 : (0 : Q') <= b + -a := by
      have hab : a <= b := Q'.le_trans' _ _ _ haHi
        (Q'.le_trans' _ _ _
          (fixedPointVal_mono scale hScale hright) hbLo)
      exact Q'.sub_nonneg_of_le hab
    have hsquare : fixedPointVal scale hScale gap *
        fixedPointVal scale hScale gap <= (b + -a) * (b + -a) :=
      Q'.mul_le_mul_of_nonneg hgap' hgap' hdiff0 hgap0
    exact Q'.le_trans' _ _ _ hfloor
      (Q'.le_trans' _ _ _ hsquare
        (Q'.ge_of_eqv (sub_square_comm_eqv a b)))
  · by_cases hleft : hiB <= loA
    · have hgapDef : gap = loA - hiB := by
        simp only [gap, intervalLowerGap, if_neg hright, if_pos hleft]
      have hgap := lowerGap_left_le scale hScale haLo hbHi hleft
      have hgap' : fixedPointVal scale hScale gap <= a + -b := by
        simpa only [hgapDef] using hgap
      have hgap0 : (0 : Q') <= fixedPointVal scale hScale gap :=
        fixedPointVal_nonneg _ _ _
      have hdiff0 : (0 : Q') <= a + -b := by
        have hba : b <= a := Q'.le_trans' _ _ _ hbHi
          (Q'.le_trans' _ _ _
            (fixedPointVal_mono scale hScale hleft) haLo)
        exact Q'.sub_nonneg_of_le hba
      have hsquare : fixedPointVal scale hScale gap *
          fixedPointVal scale hScale gap <= (a + -b) * (a + -b) :=
        Q'.mul_le_mul_of_nonneg hgap' hgap' hdiff0 hgap0
      exact Q'.le_trans' _ _ _ hfloor hsquare
    · have hgapDef : gap = 0 := by
        simp only [gap, intervalLowerGap, if_neg hright, if_neg hleft]
      have hzero : fixedPointVal scale hScale gap *
          fixedPointVal scale hScale gap ≈ (0 : Q') := by
        rw [hgapDef]
        refine Q'.eqv_trans _
          ((0 : Q') * fixedPointVal scale hScale 0) _ ?_ ?_
        · exact Q'.mul_eqv_congr_right _ _ _
            (fixedPointVal_zero_eqv scale hScale)
        refine Q'.eqv_trans _ ((0 : Q') * (0 : Q')) _ ?_ ?_
        · exact Q'.mul_eqv_congr_left 0 _ _
            (fixedPointVal_zero_eqv scale hScale)
        · exact Q'.zero_mul_eqv 0
      exact Q'.le_trans' _ _ _ hfloor
        (Q'.le_trans' _ _ _ (Q'.le_of_eqv hzero)
          (SumOfSquares.q_mul_self_nonneg (a + -b)))

private theorem exact_difference_le_upperGap
    (scale : Nat) (hScale : 0 < scale)
    {a b : Q'} {loA hiA loB hiB : Nat}
    (haHi : a <= fixedPointVal scale hScale hiA)
    (hbLo : fixedPointVal scale hScale loB <= b) :
    a + -b <= fixedPointVal scale hScale
      (intervalUpperGap loA hiA loB hiB) := by
  have hneg := Q'.neg_le_neg hbLo
  have hadd := Q'.add_le_add haHi hneg
  have htrunc := fixedPointVal_sub_le_truncated
    scale hScale hiA loB
  have hmax : hiA - loB <= intervalUpperGap loA hiA loB hiB := by
    unfold intervalUpperGap
    exact Nat.le_max_left _ _
  exact Q'.le_trans' _ _ _ hadd
    (Q'.le_trans' _ _ _ htrunc
      (fixedPointVal_mono scale hScale hmax))

/-- Upward-rounded squared outward interval gap bounds the exact squared
difference. -/
theorem intervalUpperSquare_sound
    (scale : Nat) (hScale : 0 < scale)
    (loA hiA loB hiB : Nat) (a b : Q')
    (haLo : fixedPointVal scale hScale loA <= a)
    (haHi : a <= fixedPointVal scale hScale hiA)
    (hbLo : fixedPointVal scale hScale loB <= b)
    (hbHi : b <= fixedPointVal scale hScale hiB) :
    (a + -b) * (a + -b) <=
      fixedPointVal scale hScale
        (ceilMul scale
          (intervalUpperGap loA hiA loB hiB)
          (intervalUpperGap loA hiA loB hiB)) := by
  let gap := intervalUpperGap loA hiA loB hiB
  have hupper : a + -b <= fixedPointVal scale hScale gap := by
    simpa only [gap] using
      exact_difference_le_upperGap scale hScale haHi hbLo
  have hreverse : b + -a <= fixedPointVal scale hScale gap := by
    have h := exact_difference_le_upperGap
      (loA := loB) (hiA := hiB) (loB := loA) (hiB := hiA)
      scale hScale hbHi haLo
    have hgapSymm : intervalUpperGap loB hiB loA hiA = gap := by
      unfold intervalUpperGap gap
      exact Nat.max_comm _ _
    rw [hgapSymm] at h
    exact h
  have hlower : -(fixedPointVal scale hScale gap) <= a + -b := by
    have hneg := Q'.neg_le_neg hreverse
    have hswap : -(b + -a) ≈ a + -b := by
      refine Q'.eqv_trans _ _ _ (Q'.neg_add_eqv b (-a)) ?_
      refine Q'.eqv_trans _
        (-b + a) _
        (Q'.add_eqv_congr_left (-b) _ _ (Q'.neg_neg_eqv a)) ?_
      exact Q'.add_comm_eqv (-b) a
    exact Q'.le_trans' _ _ _ hneg (Q'.le_of_eqv hswap)
  have hgap0 : (0 : Q') <= fixedPointVal scale hScale gap :=
    fixedPointVal_nonneg _ _ _
  have hsquare : (a + -b) * (a + -b) <=
      fixedPointVal scale hScale gap *
        fixedPointVal scale hScale gap :=
    Q'.mul_le_of_bounds hgap0 hgap0 hlower hupper hlower hupper
  exact Q'.le_trans' _ _ _ hsquare
    (ceilMul_sound scale hScale gap gap)

#print axioms fixedPointVal_sub_le_truncated
#print axioms intervalLowerSquare_sound
#print axioms intervalUpperSquare_sound

end YMGap.Continuum.FixedPointIntervalEnergy
