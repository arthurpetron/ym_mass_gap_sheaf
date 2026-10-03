/-
# The existing absolute spectator certificate cannot give a uniform reserve

The original `squareResponseFraction` is strictly positive at each finite
scale. Nevertheless it is at most `(1/2)^(side scale)`, uniformly over EVERY
nome `0 < w < 1`. The explicit modulus below rules out any positive lower
bound on this particular certificate along an arbitrary changing-nome family.

The proof uses the already defined local band, not a replacement action or
operator. This is NOT an upper bound on the actual interacting response.
It leaves the pointwise floor usable for constructing the anchor normalizer;
it only excludes promoting that floor to a family-wide survival reserve.
-/

import YMGap.Continuum.BF4DyadicWilsonSquareSpectatorResponse

namespace YMGap.Continuum.BF4DyadicWilsonSquareSpectatorResponseObstruction

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.HalfPow
open YMGap.Continuum.BF4DyadicWilsonSquare
open YMGap.Continuum.BF4DyadicWilsonSquareSpectatorResponse
open YMGap.Continuum.BF4ExactSlabFixedSpatialUniformLocalBand
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headFloor headFloor_positive)
open YMGap.Continuum.BF4ExactSlabAllNomeTailInterval (prefixCap)
open YMGap.Continuum.BF4ExactSlabStarRateObstruction (prefixCap_ge_one)
open YMGap.Continuum.BF4ExactSlabSharedWindowFloorBound (headFloor_le_oneThirtySecond)

private theorem pow_mono {x y : Q'} (hx : (0 : Q') ≤ x) (hxy : x ≤ y) :
    ∀ n : Nat, x ^ n ≤ y ^ n
  | 0 => Q'.le_refl' 1
  | n+1 => Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ _ hxy (Q'.pow_nonneg x hx n))
      (Q'.mul_le_mul_of_nonneg_left _ _ _ (pow_mono hx hxy n)
        (Q'.le_trans' _ _ _ hx hxy))

private theorem one_le_pow {r : Q'} (hr : (1 : Q') ≤ r) :
    ∀ n : Nat, (1 : Q') ≤ r ^ n
  | 0 => Q'.le_refl' 1
  | n+1 => by
      rw [Q'.pow_succ]
      have hr0 := Q'.le_trans' _ _ _ Q'.zero_le_one hr
      exact Q'.le_trans' _ _ _ (one_le_pow hr n)
        (Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.one_mul_eqv _))
          (Q'.mul_le_mul_of_nonneg_right _ _ _ hr (Q'.pow_nonneg r hr0 n)))

private theorem wordPower_le_one {w : Q'} (hw0 : (0 : Q') ≤ w)
    (hw1 : w ≤ (1 : Q')) :
    ∀ n : Nat, RingNormaliser.qpow w n ≤ (1 : Q')
  | 0 => Q'.le_refl' 1
  | n+1 => Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ _ (wordPower_le_one hw0 hw1 n) hw0)
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.one_mul_eqv w)) hw1)

private theorem scale_le_side : ∀ k : Nat, k ≤ side k
  | 0 => Nat.zero_le _
  | k+1 => by
      have hp := side_positive k
      have h := scale_le_side k
      change k+1 ≤ 2^(k+1)
      rw [Nat.pow_succ]
      change k+1 ≤ side k*2
      omega

/-- The explicit response certificate never exceeds even one copy of its
already defined absolute local lower factor. -/
theorem squareResponseFraction_le_localLower {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (scale : Nat) :
    squareResponseFraction hw0 hw1 scale ≤ localLower w (4*side scale) := by
  let l := localLower w (4*side scale)
  let u := localUpper w (4*side scale)
  have hl0 : (0 : Q') ≤ l := Q'.le_of_lt (localLower_positive hw0 hw1 _)
  have hl1 : l ≤ (1 : Q') :=
    HKConvGen.pow_base_antitone (Q'.le_of_lt (headFloor_positive hw0 hw1))
      (Q'.le_trans' _ _ _ (headFloor_le_oneThirtySecond hw0 hw1) (by decide))
      (m := 0) (Nat.zero_le _)
  have hu1 : (1 : Q') ≤ u := one_le_pow (prefixCap_ge_one hw0 hw1) _
  have hu0 := Q'.le_trans' _ _ _ Q'.zero_le_one hu1
  have huu1 : (1 : Q') ≤ u*u := Q'.le_trans' _ _ _ hu1
    (Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.mul_one_eqv u))
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hu1 hu0))
  let hu := Q'.mul_pos (localUpper_positive hw0 hw1 (4*side scale))
    (localUpper_positive hw0 hw1 (4*side scale))
  let r := Q'.recipPos (u*u) hu
  have hr0 : (0 : Q') ≤ r := Q'.le_of_lt (Q'.recipPos_pos _ _)
  have hr1 : r ≤ (1 : Q') := by
    apply Q'.le_of_mul_le_mul_left (c := u*u) _ hu
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_recipPos_eqv _ hu))
      (Q'.le_trans' _ _ _ huu1 (Q'.ge_of_eqv (Q'.mul_one_eqv _)))
  have hll : l*l ≤ l := Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ _ hl1 hl0)
    (Q'.le_of_eqv (Q'.mul_one_eqv l))
  have hnum : RingNormaliser.qpow w (12*side scale)*(l*l) ≤ l :=
    Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ _
        (wordPower_le_one (Q'.le_of_lt hw0) (Q'.le_of_lt hw1) _)
        (Q'.mul_nonneg _ _ hl0 hl0))
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.one_mul_eqv _)) hll)
  change (RingNormaliser.qpow w (12*side scale)*(l*l))*r ≤ l
  exact Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ hnum hr0)
    (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ hr1 hl0)
      (Q'.le_of_eqv (Q'.mul_one_eqv l)))

/-- A deliberately coarse, but nome-uniform, geometric upper bound on the
particular spectator certificate. No actual response upper bound is asserted. -/
theorem squareResponseFraction_le_half_side {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (scale : Nat) :
    squareResponseFraction hw0 hw1 scale ≤ half ^ side scale := by
  have hfloor : headFloor w ≤ half := Q'.le_trans' _ _ _
    (headFloor_le_oneThirtySecond hw0 hw1) (by decide)
  exact Q'.le_trans' _ _ _ (squareResponseFraction_le_localLower hw0 hw1 scale)
    (Q'.le_trans' _ _ _
      (pow_mono (Q'.le_of_lt (headFloor_positive hw0 hw1)) hfloor (7*(4*side scale)))
      (HKConvGen.pow_base_antitone half_nonneg (by decide)
        (by omega : side scale ≤ 7*(4*side scale))))

/-- `epsilon.den` is an explicit scale cutoff valid simultaneously for all
strict nomes. The upper bound concerns the certificate, not the theory. -/
theorem squareResponseFraction_small {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (epsilon : Q') (he : (0 : Q') < epsilon)
    (scale : Nat) (hscale : epsilon.den ≤ scale) :
    squareResponseFraction hw0 hw1 scale ≤ epsilon :=
  Q'.le_trans' _ _ _ (squareResponseFraction_le_half_side hw0 hw1 scale)
    (Q'.le_trans' _ _ _
      (HKConvGen.pow_base_antitone half_nonneg (by decide) (scale_le_side scale))
      (spacing_small epsilon he scale hscale))

/-- No choice of nome family can give this explicit spectator certificate a
fixed positive lower bound at all dyadic scales. -/
theorem no_uniform_positive_fraction (nome : Nat → Q')
    (hw0 : ∀ k, (0 : Q') < nome k) (hw1 : ∀ k, nome k < (1 : Q'))
    (gamma : Q') (hgamma : (0 : Q') < gamma) :
    ¬ ∀ k, gamma ≤ squareResponseFraction (hw0 k) (hw1 k) k := by
  intro h
  let epsilon := gamma*half
  have he : (0 : Q') < epsilon := Q'.mul_pos hgamma (by decide)
  have hsmall := squareResponseFraction_small (hw0 epsilon.den) (hw1 epsilon.den)
    epsilon he epsilon.den (Nat.le_refl _)
  have hle : gamma ≤ gamma*half := Q'.le_trans' _ _ _ (h epsilon.den) hsmall
  have hone : (1 : Q') ≤ half := Q'.le_of_mul_le_mul_left
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_one_eqv gamma)) hle) hgamma
  exact (by decide : ¬ ((1 : Q') ≤ half)) hone

end YMGap.Continuum.BF4DyadicWilsonSquareSpectatorResponseObstruction

#print axioms YMGap.Continuum.BF4DyadicWilsonSquareSpectatorResponseObstruction.squareResponseFraction_le_localLower
#print axioms YMGap.Continuum.BF4DyadicWilsonSquareSpectatorResponseObstruction.squareResponseFraction_le_half_side
#print axioms YMGap.Continuum.BF4DyadicWilsonSquareSpectatorResponseObstruction.squareResponseFraction_small
#print axioms YMGap.Continuum.BF4DyadicWilsonSquareSpectatorResponseObstruction.no_uniform_positive_fraction
