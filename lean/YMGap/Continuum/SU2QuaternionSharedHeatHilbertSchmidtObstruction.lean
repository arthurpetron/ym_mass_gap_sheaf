/-
The centered, isolated two-link heat packet already has ordinary-Haar
Hilbert--Schmidt mass greater than one at an explicit positive late cutoff.
This concerns the unweighted two-link kernel, not the normalized full-slab
operator, its gauge-sector compression, or a signed collective estimate.
-/

import YMGap.Continuum.SU2QuaternionSharedHeatLoopMoments
import YMGap.Continuum.SU2QuaternionFiniteHaarGNSCarrier

namespace YMGap.Continuum.SU2QuaternionSharedHeatHilbertSchmidtObstruction

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionRelativeCharacterSelection
open YMGap.Continuum.SU2QuaternionRelativeHeatTransmission
open YMGap.Continuum.SU2QuaternionRelativeHeatMarkovData
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry
open YMGap.Continuum.SU2QuaternionSharedHeatLoopMoments
open YMGap.Continuum.SU2QuaternionSharedHeatCorrelationObstruction
open YMGap.Continuum.SU2QuaternionFiniteHaarGNSCarrier
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity

local infix:50 " ≈ " => Q'.eqv

/-- The centered actual packet, including every spin through `K`. -/
def centeredHeat (w : Q') (K : Nat) : RatPoly :=
  polyAdd (relativeHeat w K) (polySmul (-1) polyOne)

/-- Four equal-weight fundamental coordinate channels. -/
def fourChannels : RatPoly := polySmul 4 relativeScalar

private def coordinateProduct (i : Fin 4) : RatPoly :=
  polyMul (polyVar i.val) (liftHead (polyVar i.val))

theorem fourChannels_coordinates : RatPolyCoeffEqv fourChannels
    (polySmul 4 (polyAdd (coordinateProduct 0) (polyAdd (coordinateProduct 1)
      (polyAdd (coordinateProduct 2) (coordinateProduct 3))))) := by
  apply RatPolyCoeffEqv.of_canon_termwise
  decide +kernel

private theorem supported_smul {p : RatPoly} (hp : SupportedQuaternionBlocks 2 p)
    (c : Q') : SupportedQuaternionBlocks 2 (polySmul c p) := by
  intro t ht
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
  exact hp u hu

private theorem scalar_support : SupportedQuaternionBlocks 2 relativeScalar := by
  change SupportedQuaternionBlocks 2 (scalarAt 0 1)
  exact SU2QuaternionRelativeHeatPairGeometry.scalar_supported (by decide) (by decide)

private theorem channels_supported : SupportedQuaternionBlocks 2 fourChannels :=
  supported_smul scalar_support 4

private theorem centered_supported (w : Q') (K : Nat) :
    SupportedQuaternionBlocks 2 (centeredHeat w K) :=
  supported_add (relativeHeat_supported w K) (supported_smul (supported_one 2) (-1))

/-- The four coordinate products have zero ordinary-Haar mean. -/
theorem fourChannels_mean : finiteHaarPair 2 polyOne fourChannels ≈ 0 := by
  decide +kernel

/-- Their ordinary-Haar squared norm is exactly four. -/
theorem fourChannels_square : finiteHaarPair 2 fourChannels fourChannels ≈ 4 := by
  decide +kernel

/-- All four channels transmit by the same exact spin-one coefficient. -/
theorem heat_channels_pair (w : Q') (K : Nat) (hK : 1 ≤ K) :
    finiteHaarPair 2 (relativeHeat w K) fourChannels ≈ 4 * qpow w 3 := by
  unfold finiteHaarPair fourChannels
  refine Q'.eqv_trans _ _ _
    (quaternionHaar_polyMul_smul_right 2 4 (relativeHeat w K) relativeScalar) ?_
  exact Q'.mul_eqv_congr_left _ _ _
    (Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _))
      (relative_scalar_moment w K hK))

/-- Centering removes no part of the fundamental transmission. -/
theorem centered_channels_pair (w : Q') (K : Nat) (hK : 1 ≤ K) :
    finiteHaarPair 2 (centeredHeat w K) fourChannels ≈ 4 * qpow w 3 := by
  change finiteHaarPair 2 (polyAdd (relativeHeat w K) (polySmul (-1) polyOne))
    fourChannels ≈ 4 * qpow w 3
  refine Q'.eqv_trans _ _ _
    (finiteHaarPair_add_left 2 _ _ _) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' (heat_channels_pair w K hK)
      (Q'.eqv_trans _ _ _ (finiteHaarPair_smul_left 2 (-1) polyOne fourChannels)
        (Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left _ _ _ fourChannels_mean)
          (Q'.mul_zero_eqv _)))) ?_
  exact Q'.eqv_of_eq (Q'.add_zero' _)

private theorem mul_eqv_congr {a a' b b' : Q'} (ha : a ≈ a') (hb : b ≈ b') :
    a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right a a' b ha)
    (Q'.mul_eqv_congr_left a' b b' hb)

/-- The ordinary-Haar squared Hilbert--Schmidt mass of `relativeHeat-1`
contains four independent fundamental coordinate contributions. -/
theorem centeredHeat_square_lower (w : Q') (K : Nat) (hK : 1 ≤ K) :
    (4 : Q') * (qpow w 3 * qpow w 3) ≤
      quaternionHaar 2 (polyMul (centeredHeat w K) (centeredHeat w K)) := by
  let a := qpow w 3
  let H := finiteHaarPair 2 (centeredHeat w K) (centeredHeat w K)
  let P := finiteHaarPair 2 (centeredHeat w K) fourChannels
  let S := finiteHaarPair 2 fourChannels fourChannels
  have hcs : P * P ≤ H * S := by
    exact (finiteHaarGNSData 2).cauchy_schwarz
      ⟨centeredHeat w K, centered_supported w K⟩
      ⟨fourChannels, channels_supported⟩
  have hp : P ≈ 4 * a := centered_channels_pair w K hK
  have hs : S ≈ 4 := fourChannels_square
  have hcs' : (4 * a) * (4 * a) ≤ H * 4 :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv (mul_eqv_congr hp hp))
      (Q'.le_trans' _ _ _ hcs
        (Q'.le_of_eqv (Q'.mul_eqv_congr_left H S 4 hs)))
  have hfactor : (4 * a) * (4 * a) ≈ (4 : Q') * (4 * (a * a)) :=
    poly_identity_of_normal_eq
      (.mul (.mul (.const 4) (.var 0)) (.mul (.const 4) (.var 0)))
      (.mul (.const 4) (.mul (.const 4) (.mul (.var 0) (.var 0))))
      (by decide) (fun _ => a)
  have hscaled : (4 : Q') * (4 * (a * a)) ≤ (4 : Q') * H :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv hfactor)
      (Q'.le_trans' _ _ _ hcs' (Q'.le_of_eqv (Q'.mul_comm_eqv H 4)))
  exact Q'.le_of_mul_le_mul_left hscaled (by decide : (0 : Q') < 4)

private theorem lt_of_lt_of_le {a b c : Q'} (hab : a < b) (hbc : b ≤ c) : a < c := by
  have e1 : a.num * (b.den : Int) < b.num * (a.den : Int) := hab
  have e2 : b.num * (c.den : Int) ≤ c.num * (b.den : Int) := hbc
  have hbden : (0 : Int) < (b.den : Int) := by exact_mod_cast b.den_pos
  have hcden : (0 : Int) < (c.den : Int) := by exact_mod_cast c.den_pos
  have haden : (0 : Int) < (a.den : Int) := by exact_mod_cast a.den_pos
  have h1 := Int.mul_lt_mul_of_pos_right e1 hcden
  have h2 := Int.mul_le_mul_of_nonneg_left e2 (Int.le_of_lt haden)
  have hchain : (a.num * (c.den : Int)) * (b.den : Int) <
      (c.num * (a.den : Int)) * (b.den : Int) := by
    have hleft : (a.num * (b.den : Int)) * (c.den : Int) =
        (a.num * (c.den : Int)) * (b.den : Int) := by
      rw [Int.mul_assoc, Int.mul_assoc, Int.mul_comm (b.den : Int) (c.den : Int)]
    have hmiddle : (b.num * (a.den : Int)) * (c.den : Int) =
        (a.den : Int) * (b.num * (c.den : Int)) := by
      rw [Int.mul_comm b.num (a.den : Int), Int.mul_assoc]
    have hright : (a.den : Int) * (c.num * (b.den : Int)) =
        (c.num * (a.den : Int)) * (b.den : Int) := by
      rw [Int.mul_comm c.num (a.den : Int), Int.mul_assoc]
    rw [hleft, hmiddle] at h1
    rw [hright] at h2
    exact Int.lt_of_lt_of_le h1 h2
  exact Int.lt_of_mul_lt_mul_right hchain (Int.le_of_lt hbden)

/-- A concrete positive late-cutoff heat packet has centered ordinary-Haar
Hilbert--Schmidt squared mass strictly above one. -/
theorem test_centeredHeat_square_gt_one :
    (1 : Q') < quaternionHaar 2
      (polyMul (centeredHeat testNome testCutoff) (centeredHeat testNome testCutoff)) :=
  lt_of_lt_of_le
    (by decide : (1 : Q') < 4 * (qpow testNome 3 * qpow testNome 3))
    (centeredHeat_square_lower testNome testCutoff (by unfold testCutoff; omega))

#print axioms centeredHeat
#print axioms fourChannels
#print axioms fourChannels_coordinates
#print axioms fourChannels_mean
#print axioms fourChannels_square
#print axioms heat_channels_pair
#print axioms centered_channels_pair
#print axioms centeredHeat_square_lower
#print axioms test_centeredHeat_square_gt_one

end YMGap.Continuum.SU2QuaternionSharedHeatHilbertSchmidtObstruction
