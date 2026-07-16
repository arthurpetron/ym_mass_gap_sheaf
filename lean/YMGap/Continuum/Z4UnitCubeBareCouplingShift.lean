/-
# The exact bare coupling shift for the dyadic unit cube

The elementary six-face cube at coupling `2 * w^4` has exactly the same
single-polymer activity as its 24-face dyadic refinement at coupling `w`.
This is a genuine coupling shift, derived from the fundamental SU(2)
coefficient `coeffW w 1 = 2 * w^3`; no fitted or measured constant enters.

The theorem is deliberately about bare activities.  Equality of normalized
finite-volume occurrence probabilities requires a further control of all
other polymers and is the next RG estimate, not a consequence of this exact
identity.
-/

import YMGap.Continuum.Z4CoarseUnitCubeActivity

namespace YMGap.Continuum.Z4UnitCubeBareCouplingShift

set_option maxRecDepth 10000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.ClusteringImpliesGap
open YMGap.Continuum.RGTransport
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CoarseUnitCubeActivity
open YMGap.Continuum.Z4CoarseUnitCubeBlockGeometry
open YMGap.Continuum.Z4DyadicUnitCubeActivity
open YMGap.Continuum.Z4DyadicUnitCubeBlockGeometry
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

/-- The exact rational coupling assigned to the coarse six-face block. -/
def unitCubeBlockCoupling (fineCoupling : Q') : Q' :=
  Q'.ofNat 2 * fineCoupling ^ 4

theorem unitCubeBlockCoupling_nonnegative
    {fineCoupling : Q'} (hfine : (0 : Q') ≤ fineCoupling) :
    (0 : Q') ≤ unitCubeBlockCoupling fineCoupling := by
  unfold unitCubeBlockCoupling
  exact Q'.mul_nonneg _ _ (by decide)
    (Q'.pow_nonneg fineCoupling hfine 4)

private theorem qpow_pos_local {value : Q'}
    (hvalue : (0 : Q') < value) :
    ∀ exponent : Nat, (0 : Q') < value ^ exponent
  | 0 => by
      change (0 : Q') < 1
      decide
  | exponent + 1 => Q'.mul_pos hvalue
      (qpow_pos_local hvalue exponent)

theorem unitCubeBlockCoupling_pos
    {fineCoupling : Q'} (hfine : (0 : Q') < fineCoupling) :
    (0 : Q') < unitCubeBlockCoupling fineCoupling := by
  unfold unitCubeBlockCoupling
  exact Q'.mul_pos (by decide) (qpow_pos_local hfine 4)

/-- At the checked strong-coupling anchor the activity-matched coarse
coupling lies deeper in the strong-coupling regime. -/
theorem anchor_unitCubeBlockCoupling_le :
    unitCubeBlockCoupling anchorCoupling ≤ anchorCoupling := by
  unfold unitCubeBlockCoupling anchorCoupling
  decide

private theorem neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.ofNat_num_cast, Q'.ofNat_den_cast,
               Q'.neg_den, neg_num_cast,
               show (1 : Q').num = 1 from rfl,
               show ((1 : Q').den : Int) = 1 from rfl,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one]; ac_rfl))

/-- The fundamental character coefficient transforms by the fourth power. -/
theorem unitCubeBlockCoupling_coeffW_one
    (fineCoupling : Q') :
    coeffW (unitCubeBlockCoupling fineCoupling) 1 ≈
      (coeffW fineCoupling 1) ^ 4 := by
  unfold unitCubeBlockCoupling coeffW dimQ c4
  simp only [qpow, Q'.pow_succ, Q'.pow_zero]
  ring_qeqv

private theorem pow_pow_eqv_local (value : Q') (outer : Nat) :
    ∀ inner : Nat,
      ((value ^ outer) ^ inner) ≈ value ^ (outer * inner)
  | 0 => by
      simp only [Nat.mul_zero, Q'.pow_zero]
      exact Q'.eqv_refl 1
  | inner + 1 => by
      rw [Q'.pow_succ]
      refine Q'.eqv_trans _
        (value ^ outer * value ^ (outer * inner)) _
        (Q'.mul_eqv_congr_left _ _ _
          (pow_pow_eqv_local value outer inner)) ?_
      have hsum := Q'.eqv_symm
        (Q'.pow_add_eqv value outer (outer * inner))
      have hexponent : outer * (inner + 1) =
          outer + outer * inner := by
        rw [Nat.mul_succ]
        exact Nat.add_comm _ _
      rw [hexponent]
      exact hsum

/-- The coefficient-level block identity in the exponents used by the two
cube boundaries. -/
theorem unitCubeBlockCoupling_coeffW_six_eqv_twentyFour
    (fineCoupling : Q') :
    (coeffW (unitCubeBlockCoupling fineCoupling) 1) ^ 6 ≈
      (coeffW fineCoupling 1) ^ 24 := by
  have hcongr := pow_eqv_congr
    (coeffW (unitCubeBlockCoupling fineCoupling) 1)
    ((coeffW fineCoupling 1) ^ 4)
    (unitCubeBlockCoupling_coeffW_one fineCoupling) 6
  have hnested := pow_pow_eqv_local
    (coeffW fineCoupling 1) 4 6
  have hexponent : 4 * 6 = 24 := by omega
  rw [hexponent] at hnested
  exact Q'.eqv_trans _ _ _ hcongr hnested

/-- **Exact bare RG normalization.**  The coarse cube at `2*w^4` and the
dyadically refined cube at `w` have identical derived activities. -/
theorem coarse_shifted_activity_eqv_dyadic_activity
    (fineCoupling : Q') :
    canonicalSurfaceActivity (unitCubeBlockCoupling fineCoupling) 2
        coarseUnitCubeSupportIds ≈
      canonicalSurfaceActivity fineCoupling 4
        dyadicUnitCubeSupportIds := by
  exact Q'.eqv_trans _ _ _
    (coarseUnitCube_canonicalSurfaceActivity_eqv
      (unitCubeBlockCoupling fineCoupling))
    (Q'.eqv_trans _ _ _
      (unitCubeBlockCoupling_coeffW_six_eqv_twentyFour fineCoupling)
      (Q'.eqv_symm
        (dyadicUnitCube_canonicalSurfaceActivity_eqv fineCoupling)))

theorem coarse_shifted_activity_pos
    {fineCoupling : Q'} (hfine : (0 : Q') < fineCoupling) :
    (0 : Q') <
      canonicalSurfaceActivity (unitCubeBlockCoupling fineCoupling) 2
        coarseUnitCubeSupportIds :=
  coarseUnitCube_canonicalSurfaceActivity_pos
    (unitCubeBlockCoupling_pos hfine)

#print axioms unitCubeBlockCoupling_nonnegative
#print axioms anchor_unitCubeBlockCoupling_le
#print axioms unitCubeBlockCoupling_coeffW_one
#print axioms unitCubeBlockCoupling_coeffW_six_eqv_twentyFour
#print axioms coarse_shifted_activity_eqv_dyadic_activity
#print axioms coarse_shifted_activity_pos

end YMGap.Continuum.Z4UnitCubeBareCouplingShift
