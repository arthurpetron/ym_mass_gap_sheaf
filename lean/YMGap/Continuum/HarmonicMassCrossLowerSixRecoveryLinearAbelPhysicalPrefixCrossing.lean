/-
# Constructive location of the physical carrier-prefix crossing

The three-band payment needs a crossing index but may not obtain it by
classical minimization.  This module implements a bounded recursive search in
the exact cleared numerator coordinate and proves its first-crossing laws.
The only analytic input left to the search is one nonnegative terminal
numerator.
-/

import YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryLinearAbelPhysicalBlockCancellation

namespace YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryLinearAbelPhysicalPrefixCrossing

set_option maxHeartbeats 800000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryDropCarrier
open YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryFiniteDifference
open YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryLinearAbel
open YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryLinearAbelPhysicalCarrier
open YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryLinearAbelPhysicalSplice
open YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryLinearAbelRisingSplice

/-- Bounded constructive search for the first nonnegative value of `f`,
starting at `s`. -/
def firstNonnegativeFrom (f : Nat → Q') : Nat → Nat → Nat
  | s, 0 => s
  | s, fuel + 1 =>
      if (0 : Q') ≤ f s then s
      else firstNonnegativeFrom f (s + 1) fuel

theorem firstNonnegativeFrom_lower (f : Nat → Q') : ∀ s fuel,
    s ≤ firstNonnegativeFrom f s fuel
  | s, 0 => Nat.le_refl s
  | s, fuel + 1 => by
      by_cases h : (0 : Q') ≤ f s
      · simpa only [firstNonnegativeFrom, if_pos h] using Nat.le_refl s
      · simp only [firstNonnegativeFrom, if_neg h]
        exact Nat.le_trans (Nat.le_succ s)
          (firstNonnegativeFrom_lower f (s + 1) fuel)

theorem firstNonnegativeFrom_upper (f : Nat → Q') : ∀ s fuel,
    firstNonnegativeFrom f s fuel ≤ s + fuel
  | s, 0 => Nat.le_refl s
  | s, fuel + 1 => by
      by_cases h : (0 : Q') ≤ f s
      · simp only [firstNonnegativeFrom, if_pos h]
        omega
      · simp only [firstNonnegativeFrom, if_neg h]
        have ih := firstNonnegativeFrom_upper f (s + 1) fuel
        omega

theorem firstNonnegativeFrom_selected_nonnegative
    (f : Nat → Q') : ∀ s fuel,
    (0 : Q') ≤ f (s + fuel) →
      (0 : Q') ≤ f (firstNonnegativeFrom f s fuel)
  | s, 0, hend => hend
  | s, fuel + 1, hend => by
      by_cases h : (0 : Q') ≤ f s
      · simpa only [firstNonnegativeFrom, if_pos h] using h
      · simp only [firstNonnegativeFrom, if_neg h]
        apply firstNonnegativeFrom_selected_nonnegative f (s + 1) fuel
        simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hend

theorem firstNonnegativeFrom_predecessor_nonpositive
    (f : Nat → Q') : ∀ s fuel,
    firstNonnegativeFrom f s fuel = s ∨
      f (firstNonnegativeFrom f s fuel - 1) ≤ (0 : Q')
  | s, 0 => Or.inl rfl
  | s, fuel + 1 => by
      by_cases h : (0 : Q') ≤ f s
      · simp only [firstNonnegativeFrom, if_pos h]
        exact Or.inl True.intro
      · simp only [firstNonnegativeFrom, if_neg h]
        have hneg : f s ≤ (0 : Q') := Q'.le_of_not_le h
        rcases firstNonnegativeFrom_predecessor_nonpositive
            f (s + 1) fuel with hfirst | hbefore
        · right
          rw [hfirst]
          simpa only [Nat.add_sub_cancel] using hneg
        · exact Or.inr hbefore

/-- The canonical physical crossing searches from the proved increment peak
through index `c`. -/
def lowerSixRecoveryPhysicalPrefixCrossing (k c : Nat) : Nat :=
  let r := lowerSixRecoveryPhysicalPeakIndex c
  let f := fun p =>
    lowerSixRecoveryLinearCarrierPrefixNumerator (k + 1) (p + 1)
  firstNonnegativeFrom f r (c - r)

/-- A nonnegative numerator at index `c+1` constructively produces all four
crossing facts required by the exact physical splice. -/
theorem lowerSixRecoveryPhysicalPrefixCrossing_spec
    {k c : Nat} (hc : 4 ≤ c)
    (hterminal : (0 : Q') ≤
      lowerSixRecoveryLinearCarrierPrefixNumerator (k + 1) (c + 1)) :
    lowerSixRecoveryPhysicalPeakIndex c ≤
        lowerSixRecoveryPhysicalPrefixCrossing k c ∧
      lowerSixRecoveryPhysicalPrefixCrossing k c ≤ c ∧
      (lowerSixRecoveryPhysicalPrefixCrossing k c =
          lowerSixRecoveryPhysicalPeakIndex c ∨
        lowerSixRecoveryLinearCarrierPrefixNumerator (k + 1)
            (lowerSixRecoveryPhysicalPrefixCrossing k c) ≤ (0 : Q')) ∧
      (0 : Q') ≤
        lowerSixRecoveryLinearCarrierPrefixNumerator (k + 1)
          (lowerSixRecoveryPhysicalPrefixCrossing k c + 1) := by
  let r := lowerSixRecoveryPhysicalPeakIndex c
  let f := fun p =>
    lowerSixRecoveryLinearCarrierPrefixNumerator (k + 1) (p + 1)
  let s := firstNonnegativeFrom f r (c - r)
  have hrc : r ≤ c := by
    dsimp only [r]
    unfold lowerSixRecoveryPhysicalPeakIndex
    omega
  have hshape : r + (c - r) = c := Nat.add_sub_of_le hrc
  have hsLower : r ≤ s := firstNonnegativeFrom_lower f r (c - r)
  have hsUpperRaw : s ≤ r + (c - r) :=
    firstNonnegativeFrom_upper f r (c - r)
  have hsUpper : s ≤ c := by simpa only [hshape] using hsUpperRaw
  have hend : (0 : Q') ≤ f (r + (c - r)) := by
    dsimp only [f]
    simpa only [hshape] using hterminal
  have hafter : (0 : Q') ≤ f s :=
    firstNonnegativeFrom_selected_nonnegative f r (c - r) hend
  have hbeforeRaw :=
    firstNonnegativeFrom_predecessor_nonpositive f r (c - r)
  have hbefore : s = r ∨
      lowerSixRecoveryLinearCarrierPrefixNumerator (k + 1) s ≤
        (0 : Q') := by
    rcases hbeforeRaw with hfirst | hprev
    · exact Or.inl hfirst
    · right
      have hr1 : 1 ≤ r := by
        dsimp only [r]
        unfold lowerSixRecoveryPhysicalPeakIndex
        omega
      have hs1 : 1 ≤ s := Nat.le_trans hr1 hsLower
      change lowerSixRecoveryLinearCarrierPrefixNumerator (k + 1)
        ((s - 1) + 1) ≤ (0 : Q') at hprev
      simpa only [Nat.sub_add_cancel hs1] using hprev
  dsimp only [lowerSixRecoveryPhysicalPrefixCrossing, r, f, s]
  exact ⟨hsLower, hsUpper, hbefore, hafter⟩

/-- Post-bootstrap form, with the upper range converted to the exact Abel
length `2c-1`. -/
theorem lowerSixRecoveryPhysicalPrefixCrossing_postBootstrap_spec
    {k c : Nat}
    (hcell : LowerSixWithinCenterCell (k + 2) c)
    (hterminal : (0 : Q') ≤
      lowerSixRecoveryLinearCarrierPrefixNumerator (k + 1) (c + 1)) :
    let s := lowerSixRecoveryPhysicalPrefixCrossing k c
    lowerSixRecoveryPhysicalPeakIndex c ≤ s ∧
      s ≤ 2 * c - 1 ∧
      (s = lowerSixRecoveryPhysicalPeakIndex c ∨
        lowerSixRecoveryLinearCarrierPrefixNumerator (k + 1) s ≤
          (0 : Q')) ∧
      (0 : Q') ≤
        lowerSixRecoveryLinearCarrierPrefixNumerator (k + 1) (s + 1) := by
  have hs := lowerSixRecoveryPhysicalPrefixCrossing_spec
    (k := k) (c := c) (Nat.le_trans (by decide) hcell.2.1) hterminal
  dsimp only
  exact ⟨hs.1, Nat.le_trans hs.2.1 (by omega), hs.2.2⟩

/-- Fully constructive consumer at the searched crossing.  Once the terminal
numerator and the literal quantitative payment are proved, no choice of a
crossing index remains in the critical path. -/
theorem lowerSixRecoveryLinearPayment_of_searchedPhysicalCrossing
    {k c : Nat} (hk : 648 ≤ k)
    (hcell : LowerSixWithinCenterCell (k + 2) c)
    (hterminal : (0 : Q') ≤
      lowerSixRecoveryLinearCarrierPrefixNumerator (k + 1) (c + 1))
    (hpay :
      let s := lowerSixRecoveryPhysicalPrefixCrossing k c
      lowerSixRecoveryClearedAbelPhysicalDebt k c s +
            -(lowerSixRecoveryTerminalDrop k (2 * c) *
              lowerSixRecoveryLinearCarrierPrefixDen (k + 1)) ≤
          lowerSixRecoveryLinearScaleReserve k c *
            lowerSixRecoveryLinearCarrierPrefixDen (k + 1)) :
    (-lowerSixRecoveryLinearDriftDebt k c ≤
        lowerSixRecoveryLinearScaleReserve k c) ∧
      lowerSixRecoveryClearedAbelMiddle k
          (lowerSixRecoveryPhysicalPeakIndex c)
          (lowerSixRecoveryPhysicalPrefixCrossing k c) ≤ (0 : Q') ∧
      (0 : Q') ≤
        lowerSixRecoveryClearedAbelTail k
          (lowerSixRecoveryPhysicalPrefixCrossing k c) (2 * c - 1) := by
  have hs := lowerSixRecoveryPhysicalPrefixCrossing_postBootstrap_spec
    hcell hterminal
  dsimp only at hs hpay
  exact lowerSixRecoveryLinearPayment_of_physicalCrossingPayment
    hk hcell hs.1 hs.2.1 hs.2.2.1 hs.2.2.2 hpay

#print axioms firstNonnegativeFrom_lower
#print axioms firstNonnegativeFrom_upper
#print axioms firstNonnegativeFrom_selected_nonnegative
#print axioms firstNonnegativeFrom_predecessor_nonpositive
#print axioms lowerSixRecoveryPhysicalPrefixCrossing_spec
#print axioms lowerSixRecoveryPhysicalPrefixCrossing_postBootstrap_spec
#print axioms lowerSixRecoveryLinearPayment_of_searchedPhysicalCrossing

end YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryLinearAbelPhysicalPrefixCrossing
