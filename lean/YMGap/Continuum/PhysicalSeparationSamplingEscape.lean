/-
# An explicit scale at which fixed-physical-time sampling exceeds N steps

The existing spacing modulus at t/(N+1) supplies the threshold. Positive
rational cross multiplication then gives N <= floor(t/a_j). This retains
the original sampler and returns the modulus as data; no rate of spacing
decay beyond the supplied SpacingToZero witness is assumed.
-/

import YMGap.Continuum.PhysicalSeparationSamplingOfSpacingToZero

namespace YMGap.Continuum.PhysicalSeparationSamplingEscape

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.PhysicalSeparationSamplingOfSpacingToZero
open YMGap.Continuum.PhysicalSeparatorLinearTail
open YMGap.Continuum.PhysicalSeparatorLogRate (PhysicalSpacing)

private theorem ofNat_pos_of_pos {n : Nat} (hn : 0 < n) :
    (0 : Q') < Q'.ofNat n := by
  change (0 : Int) * 1 < (n : Int) * 1
  simpa only [Int.mul_one] using (Int.ofNat_lt.mpr hn)

private theorem escapeDenominator_pos (N : Nat) :
    (0 : Q') < Q'.ofNat (N + 1) :=
  ofNat_pos_of_pos (by omega)

def stepEscapeModulus (A : PhysicalSpacing) (Z : SpacingToZero A)
    (t N : Nat) : Nat :=
  Z.modulus
    (Q'.divPos (Q'.ofNat t) (Q'.ofNat (N + 1))
      (escapeDenominator_pos N))

private theorem spacing_mul_succ_le_target
    (A : PhysicalSpacing) (Z : SpacingToZero A)
    {t N j : Nat} (ht : 0 < t)
    (hj : stepEscapeModulus A Z t N ≤ j) :
    A.spacing j * Q'.ofNat (N + 1) ≤ Q'.ofNat t := by
  let epsilon := Q'.divPos (Q'.ofNat t) (Q'.ofNat (N + 1))
    (escapeDenominator_pos N)
  have hepsilon : (0 : Q') < epsilon := by
    unfold epsilon
    exact Q'.divPos_pos _ _ (escapeDenominator_pos N)
      (ofNat_pos_of_pos ht)
  have hspacing : A.spacing j ≤ epsilon := by
    exact Z.spacing_le epsilon hepsilon j hj
  have hmul : A.spacing j * Q'.ofNat (N + 1) ≤
      epsilon * Q'.ofNat (N + 1) :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hspacing
      (Q'.le_of_lt (escapeDenominator_pos N))
  exact Q'.le_trans' _ _ _ hmul
    (Q'.le_of_eqv (Q'.divPos_mul_eqv (Q'.ofNat t)
      (Q'.ofNat (N + 1)) (escapeDenominator_pos N)))

theorem floorLatticeSteps_ge_of_spacing_mul_le
    (A : PhysicalSpacing) {t N j : Nat}
    (hspacing : A.spacing j * Q'.ofNat (N + 1) ≤ Q'.ofNat t) :
    N ≤ floorLatticeSteps A j t := by
  let a := A.spacing j
  let p : Nat := a.num.toNat
  let d : Nat := a.den
  have hp : 0 < p := by
    dsimp [p, a]
    exact spacingNumToNat_pos A j
  have hcross : (N + 1) * p ≤ t * d := by
    have h := hspacing
    change (a * Q'.ofNat (N + 1)).num *
        ((Q'.ofNat t).den : Int) ≤
      (Q'.ofNat t).num * ((a * Q'.ofNat (N + 1)).den : Int) at h
    simp only [Q'.mul_num_cast, Q'.mul_den_cast,
      Q'.ofNat_num_cast, Q'.ofNat_den_cast, Int.mul_one] at h
    have hpCast : (p : Int) = a.num := by
      dsimp [p]
      exact Int.toNat_of_nonneg
        (Int.le_of_lt (Q'.num_pos_of_pos (A.spacing_pos j)))
    rw [← hpCast] at h
    have hraw : p * (N+1) ≤ t*d := by exact_mod_cast h
    simpa only [Nat.mul_comm p] using hraw
  have hcross' : N * p ≤ t * d :=
    Nat.le_trans (Nat.mul_le_mul_right p (Nat.le_succ N)) hcross
  dsimp [floorLatticeSteps, p, d]
  exact (Nat.le_div_iff_mul_le hp).mpr hcross'

theorem floorLatticeSteps_ge_stepEscapeModulus
    (A : PhysicalSpacing) (Z : SpacingToZero A)
    {t N j : Nat} (ht : 0 < t)
    (hj : stepEscapeModulus A Z t N ≤ j) :
    N ≤ floorLatticeSteps A j t := by
  exact floorLatticeSteps_ge_of_spacing_mul_le A
    (spacing_mul_succ_le_target A Z ht hj)

#print axioms stepEscapeModulus
#print axioms floorLatticeSteps_ge_of_spacing_mul_le
#print axioms floorLatticeSteps_ge_stepEscapeModulus

end YMGap.Continuum.PhysicalSeparationSamplingEscape
