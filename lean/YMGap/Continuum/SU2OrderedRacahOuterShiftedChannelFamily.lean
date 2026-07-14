/-
# Physical channel transports for the coupled outer-height recurrence

The label-lowering term in the factorial Hahn adjacent-difference law is
again a physical fixed-output right channel.  Lowering height through the
third source coordinate reduces `(a,c,r)`; lowering through the second
reduces `(a,b,r)`.  These are two distinct shifted families, and the four-term
Omega correction uses both source directions.  This file constructs both
proof-carrying transports and proves their strict height-one base cases.
-/

import YMGap.Continuum.SU2OrderedRacahHigherHeightRecurrenceFence

namespace YMGap.Continuum.SU2OrderedRacahOuterShiftedChannelFamily

open YMGap.Continuum.SU2DirectRightFixedOutputSections
open YMGap.Continuum.SU2OrderedRacahOmegaCorrectionThreeCarrier
open YMGap.Continuum.SU2OrderedRacahHeightOneNormalizedCancellation

/-- Lower the first and third external labels and the outer contraction order
by one.  The final output degree and inner contraction order are unchanged. -/
def reduceFirstThirdRightChannel {a b c d : Nat}
    (q : FixedRightCGChannel a b c d)
    (ha : 0 < a) (hc : 0 < c) (hpc : q.p < c) (hr : 0 < q.r) :
    FixedRightCGChannel (a - 1) b (c - 1) d where
  p := q.p
  p_le := by
    have hp := Nat.le_min.mp q.p_le
    apply Nat.le_min.mpr
    constructor <;> omega
  r := q.r - 1
  r_le := by
    have hp := Nat.le_min.mp q.p_le
    have hq := Nat.le_min.mp q.r_le
    apply Nat.le_min.mpr
    constructor <;> omega
  degree_eq := by
    have hp := Nat.le_min.mp q.p_le
    have hq := Nat.le_min.mp q.r_le
    have hd := q.degree_eq
    unfold FixedRightCGChannel.intermediate at hq
    omega

/-- The first/third shift lowers the intermediate degree by exactly one. -/
theorem reduceFirstThirdRightChannel_intermediate
    {a b c d : Nat} (q : FixedRightCGChannel a b c d)
    (ha : 0 < a) (hc : 0 < c) (hpc : q.p < c) (hr : 0 < q.r) :
    (reduceFirstThirdRightChannel q ha hc hpc hr).intermediate =
      q.intermediate - 1 := by
  have hp := Nat.le_min.mp q.p_le
  change b + (c - 1) - 2 * q.p =
    (b + c - 2 * q.p) - 1
  omega

/-- The first/third shift keeps `p` and lowers `r` by exactly one. -/
theorem reduceFirstThirdRightChannel_orders
    {a b c d : Nat} (q : FixedRightCGChannel a b c d)
    (ha : 0 < a) (hc : 0 < c) (hpc : q.p < c) (hr : 0 < q.r) :
    (reduceFirstThirdRightChannel q ha hc hpc hr).p = q.p ∧
    (reduceFirstThirdRightChannel q ha hc hpc hr).r = q.r - 1 :=
  ⟨rfl, rfl⟩

/-- Symmetric transport obtained by lowering the first and second external
labels and the outer contraction order by one. -/
def reduceFirstSecondRightChannel {a b c d : Nat}
    (q : FixedRightCGChannel a b c d)
    (ha : 0 < a) (hb : 0 < b) (hpb : q.p < b) (hr : 0 < q.r) :
    FixedRightCGChannel (a - 1) (b - 1) c d where
  p := q.p
  p_le := by
    have hp := Nat.le_min.mp q.p_le
    apply Nat.le_min.mpr
    constructor <;> omega
  r := q.r - 1
  r_le := by
    have hp := Nat.le_min.mp q.p_le
    have hq := Nat.le_min.mp q.r_le
    apply Nat.le_min.mpr
    constructor <;> omega
  degree_eq := by
    have hp := Nat.le_min.mp q.p_le
    have hq := Nat.le_min.mp q.r_le
    have hd := q.degree_eq
    unfold FixedRightCGChannel.intermediate at hq
    omega

/-- The first/second shift also lowers the intermediate degree by one. -/
theorem reduceFirstSecondRightChannel_intermediate
    {a b c d : Nat} (q : FixedRightCGChannel a b c d)
    (ha : 0 < a) (hb : 0 < b) (hpb : q.p < b) (hr : 0 < q.r) :
    (reduceFirstSecondRightChannel q ha hb hpb hr).intermediate =
      q.intermediate - 1 := by
  have hp := Nat.le_min.mp q.p_le
  change (b - 1) + c - 2 * q.p =
    (b + c - 2 * q.p) - 1
  omega

/-- The first/second shift keeps `p` and lowers `r` by exactly one. -/
theorem reduceFirstSecondRightChannel_orders
    {a b c d : Nat} (q : FixedRightCGChannel a b c d)
    (ha : 0 < a) (hb : 0 < b) (hpb : q.p < b) (hr : 0 < q.r) :
    (reduceFirstSecondRightChannel q ha hb hpb hr).p = q.p ∧
    (reduceFirstSecondRightChannel q ha hb hpb hr).r = q.r - 1 :=
  ⟨rfl, rfl⟩

/-- Consecutive inner orders force the opposite one-step change in outer
order at fixed output degree. -/
theorem adjacentRightChannel_outer_order
    {a b c d : Nat} (q0 q1 : FixedRightCGChannel a b c d)
    (hp : q1.p = q0.p + 1) : q0.r = q1.r + 1 := by
  have hp1 := Nat.le_min.mp q1.p_le
  have hr0 := Nat.le_min.mp q0.r_le
  have hr1 := Nat.le_min.mp q1.r_le
  have hinter : q1.intermediate = q0.intermediate - 2 := by
    unfold FixedRightCGChannel.intermediate
    omega
  have hinter2 : 2 ≤ q0.intermediate := by
    unfold FixedRightCGChannel.intermediate
    omega
  have hd0 := q0.degree_eq
  have hd1 := q1.degree_eq
  unfold FixedRightCGChannel.intermediate at hd0 hd1
  omega

/-- The two directional label shifts form the minimal one-step family needed
to follow either source-coordinate realization of an outer-height decrease. -/
def OmegaCorrectionOuterShiftPair
    {a b c d : Nat} (qm q qp : FixedRightCGChannel a b c d)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hmb : qm.p < b) (hmc : qm.p < c)
    (hqb : q.p < b) (hqc : q.p < c)
    (hpb : qp.p < b) (hpc : qp.p < c)
    (hrm : 0 < qm.r) (hr : 0 < q.r) (hrp : 0 < qp.r)
    (i j l s : Nat) : Prop :=
  OmegaCorrectionThreeCarrierAt
      (reduceFirstThirdRightChannel qm ha hc hmc hrm)
      (reduceFirstThirdRightChannel q ha hc hqc hr)
      (reduceFirstThirdRightChannel qp ha hc hpc hrp) i j l s ∧
  OmegaCorrectionThreeCarrierAt
      (reduceFirstSecondRightChannel qm ha hb hmb hrm)
      (reduceFirstSecondRightChannel q ha hb hqb hr)
      (reduceFirstSecondRightChannel qp ha hb hpb hrp) i j l s

/-- Both shifted families inherit the already-proved height-one correction
base.  The stronger margins are exactly those consumed by decrementing one
of `b,c`, and by lowering the upper adjacent outer order. -/
theorem omegaCorrectionOuterShiftPair_height_one_strict_bulk
    {a b c d : Nat} (qm q qp : FixedRightCGChannel a b c d)
    (hp : 0 < q.p) (hprev : q.p = qm.p + 1)
    (hnext : qp.p = q.p + 1)
    (i j l s : Nat)
    (hshell : s + (q.r - 1) + q.p = i + j + l)
    (hj : 3 ≤ j) (hl : 3 ≤ l)
    (hheight : j + l = q.p + 1)
    (hpb : q.p + 3 ≤ b) (hpc : q.p + 3 ≤ c)
    (hr : 5 ≤ q.r) (hri : q.r ≤ i)
    (hia : i + 2 ≤ a)
    (hrn : q.r + 2 ≤ q.intermediate) :
    OmegaCorrectionOuterShiftPair qm q qp
      (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by
        have hm := adjacentRightChannel_outer_order qm q (by omega)
        omega)
      (by omega)
      (by
        have hq := adjacentRightChannel_outer_order q qp hnext
        omega)
      i j l s := by
  have hrm : qm.r = q.r + 1 :=
    adjacentRightChannel_outer_order qm q (by omega)
  have hrp : qp.r + 1 = q.r :=
    (adjacentRightChannel_outer_order q qp hnext).symm
  constructor
  · apply omegaCorrectionThreeCarrierAt_height_one_strict_bulk_on_shell
      (reduceFirstThirdRightChannel qm (by omega) (by omega) (by omega) (by omega))
      (reduceFirstThirdRightChannel q (by omega) (by omega) (by omega) (by omega))
      (reduceFirstThirdRightChannel qp (by omega) (by omega) (by omega) (by omega))
      hp hprev hnext i j l s
    · simpa only [reduceFirstThirdRightChannel] using hshell
    · exact hj
    · exact hl
    · exact hheight
    · simpa only [reduceFirstThirdRightChannel] using (show q.p + 2 ≤ b by omega)
    · simpa only [reduceFirstThirdRightChannel] using (show q.p + 2 ≤ c - 1 by omega)
    · simpa only [reduceFirstThirdRightChannel] using (show 4 ≤ q.r - 1 by omega)
    · simpa only [reduceFirstThirdRightChannel] using
        (show q.r - 1 + 1 ≤ i by omega)
    · simpa only [reduceFirstThirdRightChannel] using (show i + 1 ≤ a - 1 by omega)
    · rw [reduceFirstThirdRightChannel_intermediate]
      simp only [reduceFirstThirdRightChannel]
      omega
  · apply omegaCorrectionThreeCarrierAt_height_one_strict_bulk_on_shell
      (reduceFirstSecondRightChannel qm (by omega) (by omega) (by omega) (by omega))
      (reduceFirstSecondRightChannel q (by omega) (by omega) (by omega) (by omega))
      (reduceFirstSecondRightChannel qp (by omega) (by omega) (by omega) (by omega))
      hp hprev hnext i j l s
    · simpa only [reduceFirstSecondRightChannel] using hshell
    · exact hj
    · exact hl
    · exact hheight
    · simpa only [reduceFirstSecondRightChannel] using (show q.p + 2 ≤ b - 1 by omega)
    · simpa only [reduceFirstSecondRightChannel] using (show q.p + 2 ≤ c by omega)
    · simpa only [reduceFirstSecondRightChannel] using (show 4 ≤ q.r - 1 by omega)
    · simpa only [reduceFirstSecondRightChannel] using
        (show q.r - 1 + 1 ≤ i by omega)
    · simpa only [reduceFirstSecondRightChannel] using (show i + 1 ≤ a - 1 by omega)
    · rw [reduceFirstSecondRightChannel_intermediate]
      simp only [reduceFirstSecondRightChannel]
      omega

end YMGap.Continuum.SU2OrderedRacahOuterShiftedChannelFamily

#print axioms YMGap.Continuum.SU2OrderedRacahOuterShiftedChannelFamily.reduceFirstThirdRightChannel_intermediate
#print axioms YMGap.Continuum.SU2OrderedRacahOuterShiftedChannelFamily.reduceFirstSecondRightChannel_intermediate
#print axioms YMGap.Continuum.SU2OrderedRacahOuterShiftedChannelFamily.adjacentRightChannel_outer_order
#print axioms YMGap.Continuum.SU2OrderedRacahOuterShiftedChannelFamily.omegaCorrectionOuterShiftPair_height_one_strict_bulk
