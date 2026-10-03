/-
# The original normalized anchor from one macroscopic response ratio

For s=side(scale), the single SAME-state estimate kappa*R(s)<=R(2s)
controls both the existing half-anchor preimage and later block responses.
The original anchor norm may collapse: its already constructed inverse square
root is used only to normalize the SAME physical bond and vacuum-complement
state. No adjacent-response budget, microscopic start or raw reserve is needed.

The radius below is uniform in nome, width and scale when kappa is fixed and
the displayed ratio is proved for the actual family. It concerns the assigned
geometric spacing, not a physical-time calibration. The ratio producer,
cross-scale convergence and the continuum Yang--Mills identification remain
open. No sign of the finite source gain or eigenpin of a centered loop is used.
-/

import YMGap.Continuum.BF4WilsonAllNomeDyadicNormalizedAnchorContinuity
import YMGap.Continuum.BF4WilsonAllNomeBlockResponseLower

namespace YMGap.Continuum.BF4WilsonAllNomeDyadicNormalizedMacroRatio

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Constructive.CRealAlg
open YMGap.Constructive.HalfPow (half_nonneg)
open YMGap.Constructive.NonnegativeDyadicTime (MeshPoint)
open YMGap.Constructive.DyadicTimeRationals
  (value value_num value_den value_le_iff half_power_num half_power_den)
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4DyadicWilsonSquare (side spacing unit_side)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4WilsonAllNomeCompletedRealScalar
open YMGap.Continuum.BF4WilsonAllNomeRealScalarLaws
open YMGap.Continuum.BF4WilsonAllNomeDistance (completedDist)
open YMGap.Continuum.BF4WilsonAllNomeDyadicSemigroup (meshAction mesh_original)
open YMGap.Continuum.BF4WilsonAllNomeDyadicEnergy (anchored_small_bound)
open YMGap.Continuum.BF4WilsonAllNomeDyadicUnitExcitation
open YMGap.Continuum.BF4WilsonAllNomeDyadicNormalizedBondAnchor
open YMGap.Continuum.BF4WilsonAllNomeDyadicNormalizedAnchorContinuity
  (halfAnchorPreimage halfAnchorPreimage_pin)
open YMGap.Continuum.BF4WilsonAllNomeBlockResponseLower
  (response_shifted_block_step_lower response_shifted_block_geometric_lower)
open YMGap.Continuum.RationalBlockedSurvival (quarter quarter_positive)
open YMGap.Continuum.BF4WilsonAllNomeDyadicBondAnchorContinuity (half_den_small)
open YMGap.Continuum.BF4WilsonAllNomeBondOSCompletion (bondCompletedDistance)
open YMGap.Continuum.BF4WilsonAllNomeBondOSTime (bondValue_distance)
open YMGap.Continuum.BF4WilsonAllNomeBondOSRealTime
  (action action_value action_addTime action_distance_bound)
open YMGap.Continuum.BF4WilsonAllNomePositiveTimePins (realTimeAction)
open YMGap.Continuum.BF4WilsonAllNomeTimeRangeRealContinuity
  (incrementRows incrementRows_pin incrementRows_limit)
open YMGap.Continuum.BF4WilsonAllNomeCauchyRows (rowPoint limit)
open YMGap.Continuum.BF4WilsonAllNomeRowPairingLimit (pairingModulus row_pairing_bound)
open YMGap.Continuum.PositiveRealDyadicTimeData
  (PositiveTime approximation approximationReal approximationReal_equiv)
open YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimePins
  (PositiveTimeValue timeValue realValue)
open YMGap.Continuum.BF4ExactSlabThermodynamicPositiveRealSemigroup (addTime)

local notation "Rq" a:arg => Quotient.mk crealSetoid (ofQ' a)
local notation "half" => YMGap.Constructive.HalfPow.half
local infix:50 " ≈ " => Q'.eqv

private theorem scale_rational (c q : Q') : RCscale c (Rq q) = Rq (c*q) := by
  rw [RCscale_mk]
  exact Quotient.sound (ofQ'_mul c q).symm

private theorem scale_rational_one (c : Q') : RCscale c (Rq 1) = Rq c :=
  Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.mul_one_eqv c))

private theorem scalar_permutation (alpha : CReal) (c : Q') (x : CReal) :
    Equiv (mul alpha (mul alpha (mul (ofQ' c) x)))
      (mul (ofQ' c) (mul alpha (mul alpha x))) :=
  SumOfSquares.Equiv_of_approx_eqv (fun n => poly_identity_of_normal_eq
    (.mul (.var 0) (.mul (.var 0) (.mul (.var 1) (.var 2))))
    (.mul (.var 1) (.mul (.var 0) (.mul (.var 0) (.var 2)))) (by decide)
    (fun
      | 0 => alpha.approx n
      | 1 => c
      | _ => x.approx n))

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (scale width : Nat) (hwidth : side scale < width)

local notation "B" => completedInner hw0 hw1
local notation "T" => completedTime hw0 hw1
local notation "u" => Subtype.val (dyadicUnitExcitation hw0 hw1 scale width hwidth)
local notation "R" j:arg => dyadicUnitResponse hw0 hw1 scale width hwidth j
local notation "alpha" => anchorNormalizer hw0 hw1 scale width hwidth
local notation "z" => Subtype.val (normalizedVacuumExcitation hw0 hw1 scale width hwidth)

attribute [local irreducible] dyadicUnitExcitation dyadicUnitResponse anchorNormalizer

private theorem normalizer_nonnegative : leEv czero alpha := by
  simpa only [anchorNormalizer] using PositiveCRealNormalizationScalar.scalar_nonnegative
    (anchorNorm hw0 hw1 scale width hwidth)
    (anchorNormCauchy hw0 hw1 scale width hwidth)
    (anchorNormFloor hw0 hw1 scale) (anchorNormFloor_positive hw0 hw1 scale)

private theorem side_halves (hs : 2 ≤ side scale) :
    side scale/2+side scale/2=side scale := by
  cases scale with
  | zero =>
      have hzero : ¬ (2 ≤ side 0) := by decide
      exact False.elim (hzero hs)
  | succ k =>
      simp only [side, Nat.pow_succ] at hs ⊢
      omega

/-- The existing half-anchor preimage has a cleared norm bound directly from
the SAME macroscopic ratio. Positivity of kappa is not needed for this identity. -/
theorem halfAnchorPreimage_norm_cleared (kappa : Q') (hs2 : 2 ≤ side scale)
    (hratio : leEv (mul (ofQ' kappa) (R (side scale))) (R (2*side scale))) :
    RCle (RCscale kappa
      (B (halfAnchorPreimage hw0 hw1 scale width hwidth)
        (halfAnchorPreimage hw0 hw1 scale width hwidth))) (Rq 1) := by
  have ha := normalizer_nonnegative hw0 hw1 scale width hwidth
  have hscaled := leEv_mul_nonneg_left ha (leEv_mul_nonneg_left ha hratio)
  have hperm := scalar_permutation alpha kappa (R (side scale))
  unfold halfAnchorPreimage
  rw [completedInner_realSmul_diagonal, completedInner_time_sum,
    side_halves scale hs2, dyadicUnitResponse_pin]
  exact leEv_trans (leEv_of_equiv hperm.symm)
    (leEv_trans hscaled (leEv_of_equiv
      (anchorNormalizer_normalizes hw0 hw1 scale width hwidth)))

/-- Every integer block of size side has a positive normalized response floor.
In particular j=2 gives R(4*side)/R(2*side)>=kappa^2. -/
theorem normalizedAnchorResponse_block_floor (kappa : Q') (hkappa : (0 : Q') < kappa)
    (hratio : leEv (mul (ofQ' kappa) (R (side scale))) (R (2*side scale)))
    (j : Nat) :
    leEv (ofQ' (kappa^j))
      (normalizedAnchorResponse hw0 hw1 scale width hwidth (j*side scale)) := by
  have hfirst : RCle (RCscale kappa (B u (T (side scale) u)))
      (B u (T (side scale+side scale) u)) := by
    rw [dyadicUnitResponse_pin, dyadicUnitResponse_pin,
      show side scale+side scale=2*side scale by omega]
    exact hratio
  have hstep := response_shifted_block_step_lower hw0 hw1 u kappa
    (Q'.le_of_lt hkappa) (side scale) (side scale) hfirst 1
  have hsecond : RCle (RCscale kappa (B u (T (2*side scale) u)))
      (B u (T (2*side scale+side scale) u)) := by
    simpa only [Nat.one_mul, show side scale+side scale=2*side scale by omega] using hstep
  have hgeom := response_shifted_block_geometric_lower hw0 hw1 u kappa
    (Q'.le_of_lt hkappa) (side scale) (2*side scale) hsecond j
  rw [dyadicUnitResponse_pin, dyadicUnitResponse_pin] at hgeom
  have hscaled := leEv_mul_nonneg_left (normalizer_nonnegative hw0 hw1 scale width hwidth)
    (leEv_mul_nonneg_left (normalizer_nonnegative hw0 hw1 scale width hwidth) hgeom)
  have hleft : Equiv (mul alpha (mul alpha (mul (ofQ' (kappa^j)) (R (2*side scale)))))
      (ofQ' (kappa^j)) :=
    (scalar_permutation alpha (kappa^j) (R (2*side scale))).trans
      ((Pivot2.mul_congr_right
        (anchorNormalizer_normalizes hw0 hw1 scale width hwidth)).trans
        (cmul_cone (ofQ' (kappa^j))))
  exact leEv_trans (leEv_of_equiv hleft.symm) hscaled

private theorem halfAnchorPreimage_norm_bound (kappa : Q') (hkappa : (0 : Q') < kappa)
    (hs2 : 2 ≤ side scale)
    (hratio : leEv (mul (ofQ' kappa) (R (side scale))) (R (2*side scale))) :
    RCle (B (halfAnchorPreimage hw0 hw1 scale width hwidth)
        (halfAnchorPreimage hw0 hw1 scale width hwidth))
      (Rq (Q'.recipPos kappa hkappa)) := by
  have h := RCscale_mono (Q'.le_of_lt (Q'.recipPos_pos _ hkappa))
    (halfAnchorPreimage_norm_cleared hw0 hw1 scale width hwidth kappa hs2 hratio)
  have hi : Q'.recipPos kappa hkappa*kappa ≈ 1 :=
    Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) (Q'.mul_recipPos_eqv _ hkappa)
  rwa [RCscale_RCscale, RCSignedPairBudget.scale_congr hi, RCscale_one,
    scale_rational_one] at h

private theorem scaled_mesh_pin (count k : Nat) :
    value ⟨k,count⟩ ≈ Q'.ofNat count*half^k := by
  change (value ⟨k,count⟩).num*((Q'.ofNat count*half^k).den : Int) =
    (Q'.ofNat count*half^k).num*((value ⟨k,count⟩).den : Int)
  rw [value_num, value_den, Q'.mul_den_cast, Q'.mul_num_cast]
  change (count : Int)*(1*((half^k).den : Int)) =
    ((count : Int)*(half^k).num)*(2^k : Nat)
  rw [half_power_num k, half_power_den k, Int.one_mul, Int.mul_one]

/-- All actual dyadic increments of the existing normalized state, with a
constant depending only on the positive macroscopic ratio. -/
theorem normalizedMesh_increment_bound (kappa : Q') (hkappa : (0 : Q') < kappa)
    (hs2 : 2 ≤ side scale)
    (hratio : leEv (mul (ofQ' kappa) (R (side scale))) (R (2*side scale)))
    (p : MeshPoint) (k : Nat) (ht : value p ≤ Q'.ofNat (side scale/2)*half^k) :
    RCle (completedDist hw0 hw1 (meshAction hw0 hw1 p.depth p.steps z) z)
      (Rq (half^k*Q'.recipPos kappa hkappa)) := by
  have htime : value p ≤ value ⟨k,side scale/2⟩ :=
    Q'.le_trans' _ _ _ ht (Q'.ge_of_eqv (scaled_mesh_pin _ _))
  have hsteps := (value_le_iff p ⟨k,side scale/2⟩).mp htime
  have hsmall : (p.steps*2^0)*2^k ≤ (side scale/2)*2^p.depth := by
    simpa only [Nat.pow_zero, Nat.mul_one] using hsteps
  have h := anchored_small_bound hw0 hw1 0 (side scale/2) p.depth p.steps k hsmall
    (halfAnchorPreimage hw0 hw1 scale width hwidth)
  rw [mesh_original, halfAnchorPreimage_pin hw0 hw1 scale width hwidth hs2] at h
  exact RCle_trans h (by
    have hb := RCscale_mono (Q'.pow_nonneg half half_nonneg k)
      (halfAnchorPreimage_norm_bound hw0 hw1 scale width hwidth kappa hkappa hs2 hratio)
    rwa [scale_rational] at hb)

/-- Geometric radius with the factor-two slack used by real-time approximants. -/
def macroGeometricRadius (kappa epsilon : Q') : Q' :=
  quarter*half^(epsilon*kappa).den

theorem macroGeometricRadius_positive (kappa epsilon : Q') :
    (0 : Q') < macroGeometricRadius kappa epsilon :=
  Q'.mul_pos quarter_positive (HKPos.pow_pos (by decide : (0 : Q') < half) _)

private theorem side_half_scalar (hs2 : 2 ≤ side scale) :
    Q'.ofNat (side scale/2) ≈ Q'.ofNat (side scale)*half := by
  have h := side_halves scale hs2
  change (Q'.ofNat (side scale/2)).num*((Q'.ofNat (side scale)*half).den : Int) =
    (Q'.ofNat (side scale)*half).num*((Q'.ofNat (side scale/2)).den : Int)
  rw [Q'.mul_num_cast, Q'.mul_den_cast]
  change ((side scale/2 : Nat) : Int)*(1*2) = ((side scale : Int)*1)*1
  simp only [Int.one_mul, Int.mul_one]
  exact_mod_cast (show (side scale/2)*2=side scale by omega)

private theorem radius_double (kappa epsilon : Q') (hs2 : 2 ≤ side scale) :
    Q'.ofNat (side scale)*macroGeometricRadius kappa epsilon +
        Q'.ofNat (side scale)*macroGeometricRadius kappa epsilon ≈
      Q'.ofNat (side scale/2)*half^(epsilon*kappa).den := by
  have hr : Q'.ofNat (side scale)*macroGeometricRadius kappa epsilon +
      Q'.ofNat (side scale)*macroGeometricRadius kappa epsilon ≈
      (Q'.ofNat (side scale)*half)*half^(epsilon*kappa).den :=
    Q'.eqv_trans _ _ _
      (poly_identity_of_normal_eq
        (.add (.mul (.var 0) (.mul (.var 2) (.var 1)))
          (.mul (.var 0) (.mul (.var 2) (.var 1))))
        (.mul (.mul (.var 0) (.add (.var 2) (.var 2))) (.var 1)) (by decide)
        (fun
          | 0 => Q'.ofNat (side scale)
          | 1 => half^(epsilon*kappa).den
          | _ => quarter))
      (Q'.mul_eqv_congr_right _ _ _
        (Q'.mul_eqv_congr_left _ _ _ (by decide : quarter+quarter ≈ half)))
  exact Q'.eqv_trans _ _ _ hr
    (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm (side_half_scalar scale hs2)))

private theorem radius_error (kappa : Q') (hkappa : (0 : Q') < kappa)
    (epsilon : Q') (he : (0 : Q') < epsilon) :
    half^(epsilon*kappa).den*Q'.recipPos kappa hkappa ≤ epsilon := by
  have h := Q'.mul_le_mul_of_nonneg_right _ _ _
    (half_den_small (epsilon*kappa) (Q'.mul_pos he hkappa))
    (Q'.le_of_lt (Q'.recipPos_pos _ hkappa))
  have heq : (epsilon*kappa)*Q'.recipPos kappa hkappa ≈ epsilon :=
    Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv _ _ _)
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _
        (Q'.mul_recipPos_eqv _ hkappa)) (Q'.mul_one_eqv _))
  exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv heq)

private theorem lattice_radius_positive (kappa epsilon : Q') :
    (0 : Q') < Q'.ofNat (side scale)*macroGeometricRadius kappa epsilon := by
  have hs : (0 : Q') < Q'.ofNat (side scale) := by
    change (0 : Int)*1 < (side scale : Int)*1
    simp only [Int.mul_one]
    exact_mod_cast BF4DyadicWilsonSquare.side_positive scale
  exact Q'.mul_pos hs (macroGeometricRadius_positive kappa epsilon)

private theorem normalized_real_increment (kappa : Q') (hkappa : (0 : Q') < kappa)
    (hs2 : 2 ≤ side scale)
    (hratio : leEv (mul (ofQ' kappa) (R (side scale))) (R (2*side scale)))
    (epsilon : Q') (he : (0 : Q') < epsilon) (time : PositiveTime)
    (ht : RCle (realValue (timeValue time))
      (Rq (Q'.ofNat (side scale)*macroGeometricRadius kappa epsilon))) :
    RCle (completedDist hw0 hw1 (realTimeAction hw0 hw1 (timeValue time) z) z)
      (Rq epsilon) := by
  have hap : leEv (approximationReal time)
      (ofQ' (Q'.ofNat (side scale)*macroGeometricRadius kappa epsilon)) := by
    have hp : Quotient.mk crealSetoid (approximationReal time) = realValue (timeValue time) :=
      Quotient.sound (approximationReal_equiv time)
    rwa [← hp] at ht
  obtain ⟨N,hN⟩ := hap _ (lattice_radius_positive scale kappa epsilon)
  have hsmall (j : Nat) (hj : N ≤ j) :
      value (approximation time j) ≤ Q'.ofNat (side scale/2)*half^(epsilon*kappa).den :=
    Q'.le_trans' _ _ _ (hN j hj) (Q'.le_of_eqv (radius_double scale kappa epsilon hs2))
  let state := normalizedSector hw0 hw1 scale width hwidth
  let rows := incrementRows hw0 hw1 state.range time
  have hlimit : RCle (B (limit hw0 hw1 rows) (limit hw0 hw1 rows)) (Rq epsilon) := by
    apply RationalScalarTwoSidedError.le_of_all_errors
    intro delta hd
    let j := max (pairingModulus hw0 hw1 rows rows delta) N
    have hp := (row_pairing_bound hw0 hw1 rows rows delta hd j (Nat.le_max_left _ _)).2
    have hpoint : RCle (B (rowPoint hw0 hw1 rows j) (rowPoint hw0 hw1 rows j)) (Rq epsilon) := by
      rw [show rows = incrementRows hw0 hw1 state.range time from rfl, incrementRows_pin]
      rw [show state = normalizedSector hw0 hw1 scale width hwidth from rfl, normalizedSector_pin]
      exact RCle_trans (normalizedMesh_increment_bound hw0 hw1 scale width hwidth
        kappa hkappa hs2 hratio (approximation time j) (epsilon*kappa).den
        (hsmall j (Nat.le_max_right _ _)))
        (leEv_of_le (ofQ'_le_ofQ' (radius_error kappa hkappa epsilon he)))
    exact RCle_trans hp (RCadd_le_add hpoint (RCle_refl _))
  rw [show rows = incrementRows hw0 hw1 state.range time from rfl, incrementRows_limit,
    show state = normalizedSector hw0 hw1 scale width hwidth from rfl, normalizedSector_pin] at hlimit
  exact hlimit

/-- ALL represented positive real increments on the existing physical bond
state. The radius depends only on kappa and epsilon, not the raw norm. -/
theorem normalizedBond_geometric_real_increment (kappa : Q') (hkappa : (0 : Q') < kappa)
    (hs2 : 2 ≤ side scale)
    (hratio : leEv (mul (ofQ' kappa) (R (side scale))) (R (2*side scale)))
    (epsilon : Q') (he : (0 : Q') < epsilon) (time : PositiveTimeValue)
    (ht : RCle (RCscale (spacing scale) (realValue time))
      (Rq (macroGeometricRadius kappa epsilon))) :
    RCle (bondCompletedDistance hw0 hw1
      (action hw0 hw1 time (normalizedBondExcitation hw0 hw1 scale width hwidth))
      (normalizedBondExcitation hw0 hw1 scale width hwidth)) (Rq epsilon) := by
  have ht' := RCscale_mono (Q'.ofNat_nonneg (side scale)) ht
  have hi : Q'.ofNat (side scale)*spacing scale ≈ 1 :=
    Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) (unit_side scale)
  rw [RCscale_RCscale, RCSignedPairBudget.scale_congr hi, RCscale_one, scale_rational] at ht'
  rw [bondValue_distance, action_value, normalizedBond_value]
  revert ht'
  refine Quotient.inductionOn time ?_
  intro t ht'
  exact normalized_real_increment hw0 hw1 scale width hwidth kappa hkappa hs2 hratio
    epsilon he t ht'

/-- The same modulus controls every forward orbit point under the existing
real-time action; no new carrier or extra physical half-step is introduced. -/
theorem normalizedBond_geometric_real_forward_increment
    (kappa : Q') (hkappa : (0 : Q') < kappa) (hs2 : 2 ≤ side scale)
    (hratio : leEv (mul (ofQ' kappa) (R (side scale))) (R (2*side scale)))
    (epsilon : Q') (he : (0 : Q') < epsilon) (s t : PositiveTimeValue)
    (ht : RCle (RCscale (spacing scale) (realValue t))
      (Rq (macroGeometricRadius kappa epsilon))) :
    RCle (bondCompletedDistance hw0 hw1
      (action hw0 hw1 (addTime s t) (normalizedBondExcitation hw0 hw1 scale width hwidth))
      (action hw0 hw1 s (normalizedBondExcitation hw0 hw1 scale width hwidth)))
      (Rq epsilon) := by
  rw [action_addTime]
  exact RCle_trans (action_distance_bound hw0 hw1 s _ _)
    (normalizedBond_geometric_real_increment hw0 hw1 scale width hwidth
      kappa hkappa hs2 hratio epsilon he t ht)

#print axioms halfAnchorPreimage_norm_cleared
#print axioms normalizedAnchorResponse_block_floor
#print axioms normalizedMesh_increment_bound
#print axioms macroGeometricRadius
#print axioms macroGeometricRadius_positive
#print axioms normalizedBond_geometric_real_increment
#print axioms normalizedBond_geometric_real_forward_increment

end YMGap.Continuum.BF4WilsonAllNomeDyadicNormalizedMacroRatio
