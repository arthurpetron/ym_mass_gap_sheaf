/-
# Physical three-band splice for the cleared linear Abel payment

The carrier-prefix numerator is exact at every mode.  This module selects a
uniform, center-dependent start of the falling complement-increment region
and separates the later prefix crossing as a second index.  The resulting
three bands have the true sign pattern: a finite rising head, a favorable
negative middle band, and the certified nonnegative falling suffix.
-/

import YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryLinearAbelRisingSplice

namespace YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryLinearAbelPhysicalSplice

set_option maxHeartbeats 800000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryFiniteDifference
open YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryLinearAbel
open YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryLinearAbelCumulativePayment
open YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryLinearAbelFluxLocation
open YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryLinearAbelFluxUnimodality
open YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryLinearAbelPrefixVariation
open YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryLinearAbelRisingSplice
open YMGap.Continuum.RGTransport

local infix:50 " ≈ " => Q'.eqv

private theorem even_square_local (m : Nat) :
    (2 * m) * (2 * m) = 2 * (2 * m * m) := by ac_rfl

private theorem even_succ_square_local (m : Nat) :
    (2 * m + 1) * (2 * m + 1) =
      2 * (2 * m * m + 2 * m) + 1 := by
  rw [Nat.add_mul, Nat.mul_add, even_square_local]
  omega

private theorem two_m_mul_succ_local (m : Nat) :
    2 * m * (m + 1) = 2 * m * m + 2 * m := by
  rw [Nat.mul_add]
  omega

private theorem odd_succ_square_local (m : Nat) :
    (2 * m + 1 + 1) * (2 * m + 1 + 1) =
      2 * (2 * m * (m + 1) + 2 * m + 1) + 2 := by
  have hform : 2 * m + 1 + 1 = 2 * (m + 1) := by omega
  rw [hform, even_square_local]
  have hexpand : 2 * (m + 1) = 2 * m + 2 := by omega
  rw [hexpand, Nat.add_mul]
  rw [two_m_mul_succ_local]
  omega

private theorem physical_peak_exponent_local (m : Nat) :
    lowerSixRecoveryComplementExponent (m + 2) =
      2 * m * m + 6 * m + 6 := by
  unfold lowerSixRecoveryComplementExponent
  have hsub : m + 2 - 1 = m + 1 := by omega
  have hfactor : 2 * (m + 2) = 2 * m + 4 := by omega
  have hfour : 4 * (m + 1) = 4 * m + 4 := by omega
  rw [hsub, hfactor, Nat.add_mul, two_m_mul_succ_local, hfour]
  omega

/-- A uniform rational start of the falling-increment region. -/
def lowerSixRecoveryPhysicalPeakIndex (c : Nat) : Nat :=
  c / 2 + 2

/-- The physical same-center inequalities put the quadratic complement
exponent beyond the harmonic scale at `floor(c/2)+2`. -/
theorem lowerSixRecoveryPhysicalPeakIndex_threshold
    {k c : Nat} (hcell : LowerSixWithinCenterCell (k + 2) c) :
    k + 2 ≤
      lowerSixRecoveryComplementExponent
        (lowerSixRecoveryPhysicalPeakIndex c) := by
  rcases hcell with ⟨_, hc10, _, hupper⟩
  have hpar : c % 2 = 0 ∨ c % 2 = 1 := by omega
  rcases hpar with heven | hodd
  · let m := c / 2
    have hc : c = 2 * m := by dsimp only [m]; omega
    have hsq :
        2 * ((k + 2) + 1) + 1 <
          2 * (2 * m * m + 2 * m) + 1 := by
      rw [hc, even_succ_square_local] at hupper
      exact hupper
    unfold lowerSixRecoveryPhysicalPeakIndex
    rw [hc]
    have hhalf : 2 * m / 2 = m := by omega
    rw [hhalf]
    rw [physical_peak_exponent_local]
    omega
  · let m := c / 2
    have hc : c = 2 * m + 1 := by dsimp only [m]; omega
    have hsq :
        2 * ((k + 2) + 1) + 1 <
          2 * (2 * m * (m + 1) + 2 * m + 1) + 2 := by
      rw [hc, odd_succ_square_local] at hupper
      exact hupper
    unfold lowerSixRecoveryPhysicalPeakIndex
    rw [hc]
    have hhalf : (2 * m + 1) / 2 = m := by omega
    rw [hhalf]
    rw [physical_peak_exponent_local]
    rw [two_m_mul_succ_local] at hsq
    omega

theorem lowerSixRecoveryPhysicalPeakIndex_pos
    {c : Nat} (hc : 10 ≤ c) :
    1 ≤ lowerSixRecoveryPhysicalPeakIndex c := by
  unfold lowerSixRecoveryPhysicalPeakIndex
  omega

theorem lowerSixRecoveryPhysicalPeakIndex_lt_cutoff
    {c : Nat} (hc : 10 ≤ c) :
    lowerSixRecoveryPhysicalPeakIndex c < 2 * c - 1 := by
  unfold lowerSixRecoveryPhysicalPeakIndex
  omega

/-- Every increment after the physical peak index is antitone. -/
theorem lowerSixRecoveryComplementScaleIncrement_physical_tail_antitone
    {k c : Nat} (hcell : LowerSixWithinCenterCell (k + 2) c) (d : Nat) :
    lowerSixRecoveryComplementScaleIncrement k
        (lowerSixRecoveryPhysicalPeakIndex c + d + 1) ≤
      lowerSixRecoveryComplementScaleIncrement k
        (lowerSixRecoveryPhysicalPeakIndex c + d) := by
  exact lowerSixRecoveryComplementScaleIncrement_tail_antitone_of_exponent_ge_scale
    (lowerSixRecoveryPhysicalPeakIndex_pos hcell.2.1)
    (lowerSixRecoveryPhysicalPeakIndex_threshold hcell) d

/-! ## Prefix signs in the exact numerator coordinate -/

theorem lowerSixRecoveryNextCarrierPrefix_nonpositive_of_numerator
    {k p : Nat}
    (hnum : lowerSixRecoveryLinearCarrierPrefixNumerator (k + 1) (p + 1) ≤
      (0 : Q')) :
    lowerSixRecoveryNextCarrierPrefix k p ≤ (0 : Q') := by
  apply lowerSixRecoveryNextCarrierPrefix_le_of_numerator
  exact Q'.le_trans' _ _ _ hnum
    (Q'.ge_of_eqv
      (Q'.zero_mul_eqv
        (lowerSixRecoveryLinearCarrierPrefixDen (k + 1))))

theorem lowerSixRecoveryNextCarrierPrefix_nonnegative_of_numerator
    {k p : Nat}
    (hnum : (0 : Q') ≤
      lowerSixRecoveryLinearCarrierPrefixNumerator (k + 1) (p + 1)) :
    (0 : Q') ≤ lowerSixRecoveryNextCarrierPrefix k p := by
  let D := lowerSixRecoveryLinearCarrierPrefixDen (k + 1)
  have hrepr :=
    lowerSixRecoveryNextCarrierPrefix_mul_den_eqv_numerator k p
  have hscaled : (0 : Q') * D ≤
      lowerSixRecoveryNextCarrierPrefix k p * D := by
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.zero_mul_eqv D))
      (Q'.le_trans' _ _ _ hnum (Q'.ge_of_eqv hrepr))
  exact BakryEmery.le_of_mul_le_mul_right_pos
    (lowerSixRecoveryLinearCarrierPrefixDen_pos (k + 1)) hscaled

/-! ## Exact three-band split -/

def lowerSixRecoveryClearedAbelHead (k r : Nat) : Q' :=
  finSum (fun p => lowerSixRecoveryClearedAbelVariationTerm k p) r

def lowerSixRecoveryClearedAbelMiddle (k r s : Nat) : Q' :=
  finSum (fun d => lowerSixRecoveryClearedAbelVariationTerm k (r + d))
    (s - r)

def lowerSixRecoveryClearedAbelTail (k s L : Nat) : Q' :=
  finSum (fun d => lowerSixRecoveryClearedAbelVariationTerm k (s + d))
    (L - s)

/-- Exact split of the cleared variation sum at an increment peak `r` and a
later carrier-prefix crossing `s`.  The terminal term remains outside this
identity, so using the split does not normalize the very large closed
carrier numerator. -/
theorem lowerSixRecoveryClearedAbelVariationSum_eqv_threeBand
    {k c r s : Nat} (hrs : r ≤ s) (hsL : s ≤ 2 * c - 1) :
    finSum (fun p => lowerSixRecoveryClearedAbelVariationTerm k p)
        (2 * c - 1) ≈
      lowerSixRecoveryClearedAbelHead k r +
        (lowerSixRecoveryClearedAbelMiddle k r s +
          lowerSixRecoveryClearedAbelTail k s (2 * c - 1)) := by
  let f := fun p => lowerSixRecoveryClearedAbelVariationTerm k p
  let L := 2 * c - 1
  have hrL : r ≤ L := Nat.le_trans hrs hsL
  have hshape1 : r + (L - r) = L := Nat.add_sub_of_le hrL
  have hshape2 : (s - r) + (L - s) = L - r := by omega
  have hsplit1 := YMGap.Constructive.finSum_split f r (L - r)
  rw [hshape1] at hsplit1
  have hsplit2 := YMGap.Constructive.finSum_split (fun d => f (r + d))
    (s - r) (L - s)
  rw [hshape2] at hsplit2
  have hshift : ∀ d,
      f (r + ((s - r) + d)) ≈ f (s + d) := by
    intro d
    have hrsEq : r + (s - r) = s := Nat.add_sub_of_le hrs
    rw [← Nat.add_assoc, hrsEq]
    exact Q'.eqv_refl _
  have htail := RationalTail.finSum_eqv_congr
    (fun d => f (r + ((s - r) + d)))
    (fun d => f (s + d)) hshift (L - s)
  unfold lowerSixRecoveryClearedAbelHead
    lowerSixRecoveryClearedAbelMiddle
    lowerSixRecoveryClearedAbelTail
  dsimp only [f, L] at hsplit1 hsplit2 htail ⊢
  refine Q'.eqv_trans _
    (finSum (fun p => lowerSixRecoveryClearedAbelVariationTerm k p) r +
      finSum (fun d =>
        lowerSixRecoveryClearedAbelVariationTerm k (r + d)) (L - r)) _
    hsplit1 ?_
  refine Q'.add_eqv_congr_left _ _ _ ?_
  refine Q'.eqv_trans _
    (finSum (fun d =>
        lowerSixRecoveryClearedAbelVariationTerm k (r + d)) (s - r) +
      finSum (fun d =>
        lowerSixRecoveryClearedAbelVariationTerm k
          (r + ((s - r) + d))) (L - s)) _
    hsplit2 ?_
  exact Q'.add_eqv_congr_left _ _ _ htail

private theorem signed_finSum_nonpositive (f : Nat → Q') : ∀ N,
    (∀ j, j < N → f j ≤ (0 : Q')) → finSum f N ≤ (0 : Q')
  | 0, _ => Q'.le_refl' 0
  | N + 1, h => by
      rw [finSum_succ]
      exact Q'.le_trans' _ _ _
        (Q'.add_le_add
          (signed_finSum_nonpositive f N
            (fun j hj => h j (Nat.lt_trans hj (Nat.lt_succ_self N))))
          (h N (Nat.lt_succ_self N))) (by decide)

private theorem signed_finSum_nonnegative (f : Nat → Q') : ∀ N,
    (∀ j, j < N → (0 : Q') ≤ f j) →
      (0 : Q') ≤ finSum f N
  | 0, _ => Q'.le_refl' 0
  | N + 1, h => by
      rw [finSum_succ]
      exact Q'.zero_le_add _ _
        (signed_finSum_nonnegative f N
          (fun j hj => h j (Nat.lt_trans hj (Nat.lt_succ_self N))))
        (h N (Nat.lt_succ_self N))

/-- Between the increment peak and the prefix crossing, the cleared middle
band is favorable (nonpositive). -/
theorem lowerSixRecoveryClearedAbelMiddle_nonpositive
    {k r s : Nat} (hrs : r ≤ s)
    (hr1 : 1 ≤ r)
    (hthreshold : k + 2 ≤ lowerSixRecoveryComplementExponent r)
    (hcarrier : (0 : Q') ≤ lowerSixRecoveryLinearCarrier (k + 1) r)
    (hbefore : s = r ∨
      lowerSixRecoveryNextCarrierPrefix k (s - 1) ≤ (0 : Q')) :
    lowerSixRecoveryClearedAbelMiddle k r s ≤ (0 : Q') := by
  unfold lowerSixRecoveryClearedAbelMiddle
  apply signed_finSum_nonpositive
  intro d hd
  have hdr : r + d < s := by omega
  have hpref : lowerSixRecoveryNextCarrierPrefix k (r + d) ≤ (0 : Q') := by
    rcases hbefore with hEq | hlast
    · omega
    have hmono := lowerSixRecoveryNextCarrierPrefix_tail_mono
      (p := r) (q := r + d) (by omega) hcarrier
    have htoLast := lowerSixRecoveryNextCarrierPrefix_tail_mono
      (p := r + d) (q := s - 1) (by omega)
      (lowerSixRecoveryLinearCarrier_nonnegative_mono (by omega) hcarrier)
    exact Q'.le_trans' _ _ _ htoLast hlast
  have hnum : lowerSixRecoveryLinearCarrierPrefixNumerator
      (k + 1) (r + d + 1) ≤ (0 : Q') := by
    have hrepr :=
      lowerSixRecoveryNextCarrierPrefix_mul_den_eqv_numerator k (r + d)
    have hD0 : (0 : Q') ≤
        lowerSixRecoveryLinearCarrierPrefixDen (k + 1) :=
      Q'.le_of_lt (lowerSixRecoveryLinearCarrierPrefixDen_pos (k + 1))
    have hm : lowerSixRecoveryNextCarrierPrefix k (r + d) *
        lowerSixRecoveryLinearCarrierPrefixDen (k + 1) ≤ (0 : Q') := by
      have hs := Q'.mul_le_mul_of_nonneg_right _ _ _ hpref hD0
      exact Q'.le_trans' _ _ _ hs
        (Q'.le_of_eqv (Q'.zero_mul_eqv _))
    exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hrepr) hm
  have hfall :=
    lowerSixRecoveryComplementScaleIncrement_tail_antitone_of_exponent_ge_scale
      hr1 hthreshold d
  have hvar := lowerSixRecoveryComplementVariation_nonnegative_of_descent
    (by simpa only [Nat.add_assoc] using hfall)
  unfold lowerSixRecoveryClearedAbelVariationTerm
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_comm_eqv _ _))
    (Q'.mul_nonpos_of_nonneg_nonpos hvar hnum)

/-- Once the prefix has crossed after the physical peak, the entire cleared
tail band is nonnegative. -/
theorem lowerSixRecoveryClearedAbelTail_nonnegative
    {k r s L : Nat} (hrs : r ≤ s)
    (hr1 : 1 ≤ r)
    (hthreshold : k + 2 ≤ lowerSixRecoveryComplementExponent r)
    (hcarrier : (0 : Q') ≤ lowerSixRecoveryLinearCarrier (k + 1) r)
    (hprefix : (0 : Q') ≤ lowerSixRecoveryNextCarrierPrefix k s) :
    (0 : Q') ≤ lowerSixRecoveryClearedAbelTail k s L := by
  unfold lowerSixRecoveryClearedAbelTail
  apply signed_finSum_nonnegative
  intro d hd
  have hsCarrier : (0 : Q') ≤
      lowerSixRecoveryLinearCarrier (k + 1) s :=
    lowerSixRecoveryLinearCarrier_nonnegative_mono hrs hcarrier
  have hp : (0 : Q') ≤ lowerSixRecoveryNextCarrierPrefix k (s + d) :=
    lowerSixRecoveryNextCarrierPrefix_nonnegative_mono (by omega)
      hsCarrier hprefix
  have hnum := lowerSixRecoveryLinearCarrierPrefixNumerator_nonnegative hp
  have hfall :=
    lowerSixRecoveryComplementScaleIncrement_tail_antitone_of_exponent_ge_scale
      hr1 hthreshold (s - r + d)
  have hindex : r + (s - r + d) = s + d := by omega
  rw [hindex] at hfall
  have hvar := lowerSixRecoveryComplementVariation_nonnegative_of_descent
    (by simpa only [Nat.add_assoc] using hfall)
  unfold lowerSixRecoveryClearedAbelVariationTerm
  exact Q'.mul_nonneg _ _ hnum hvar

#print axioms lowerSixRecoveryPhysicalPeakIndex_threshold
#print axioms lowerSixRecoveryComplementScaleIncrement_physical_tail_antitone
#print axioms lowerSixRecoveryNextCarrierPrefix_nonpositive_of_numerator
#print axioms lowerSixRecoveryNextCarrierPrefix_nonnegative_of_numerator
#print axioms lowerSixRecoveryClearedAbelVariationSum_eqv_threeBand
#print axioms lowerSixRecoveryClearedAbelMiddle_nonpositive
#print axioms lowerSixRecoveryClearedAbelTail_nonnegative

end YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryLinearAbelPhysicalSplice
