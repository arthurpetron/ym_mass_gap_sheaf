/-
# Uniform continuity of the SAME normalized positive-time bond anchor

A supplied ORIGINAL relative response budget, starting no later than side,
controls the norm of an explicit half-anchor preimage by the fixed rational
1/kappa, kappa=(3/4)*(1/4)^(2*C). Neither the collapsing original anchor norm
nor a uniform raw lag-one reserve occurs in the resulting continuity radius.

The state, physical bond completion, represented real-time action and range
witness are the existing ones. The radius is uniform at the ASSIGNED geometric
spacing, conditional on a family-wide finite C and the displayed SAME response
budget. That analytic family input, cross-scale convergence, physical time
calibration and the full continuum Yang--Mills identification remain open.
-/

import YMGap.Continuum.BF4WilsonAllNomeDyadicNormalizedBondAnchor
import YMGap.Continuum.BF4WilsonAllNomeRealBondAnchorContinuity

namespace YMGap.Continuum.BF4WilsonAllNomeDyadicNormalizedAnchorContinuity

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Constructive.CRealAlg
open YMGap.Constructive.HalfPow (half half_nonneg)
open YMGap.Constructive.NonnegativeDyadicTime (MeshPoint)
open YMGap.Constructive.DyadicTimeRationals
  (value value_num value_den value_le_iff half_power_num half_power_den)
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.RationalBlockedSurvival
open YMGap.Continuum.BF4DyadicWilsonSquare (side spacing unit_side)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4WilsonAllNomeTimeDefectMoments (mixedMoment_nonnegative)
open YMGap.Continuum.BF4WilsonAllNomeCompletedRealScalar
open YMGap.Continuum.BF4WilsonAllNomeRealScalarLaws
open YMGap.Continuum.BF4WilsonAllNomeDistance (completedDist)
open YMGap.Continuum.BF4WilsonAllNomeDyadicSemigroup (meshAction mesh_original)
open YMGap.Continuum.BF4WilsonAllNomeDyadicEnergy (anchored_small_bound)
open YMGap.Continuum.BF4WilsonAllNomeDyadicUnitExcitation
open YMGap.Continuum.BF4WilsonAllNomeDyadicFilteredGeometricSurvival
  (response_shifted_step_lower response_shifted_geometric_lower)
open YMGap.Continuum.BF4WilsonAllNomeDyadicNormalizedBondAnchor
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

/-- Fixed preimage reserve, not a lower bound on the original anchor norm. -/
def preimageReserve (C : Nat) : Q' := Q'.mkPos 3 4 (by decide)*quarter^(2*C)

theorem preimageReserve_positive (C : Nat) : (0 : Q') < preimageReserve C :=
  Q'.mul_pos (by decide) (HKPos.pow_pos quarter_positive _)

private theorem rate_ge_threeQuarters (C m : Nat) (hC : 1 ≤ C) (hm : 4*C ≤ m) :
    Q'.mkPos 3 4 (by decide) ≤ blocked_rate C m := by
  have hm1 : 1 ≤ m := by omega
  have hl : Q'.ofNat C*Q'.invSucc (m-1) ≤ quarter := by
    change (Q'.ofNat C*Q'.invSucc (m-1)).num*4 ≤
      1*((Q'.ofNat C*Q'.invSucc (m-1)).den : Int)
    rw [Q'.mul_num_cast, Q'.mul_den_cast, Q'.invSucc_num, Q'.invSucc_den]
    change (C : Int)*1*4 ≤ 1*(1*((m-1+1 : Nat) : Int))
    simp only [Int.mul_one, Int.one_mul, Nat.sub_add_cancel hm1]
    exact_mod_cast (show C*4 ≤ m by omega)
  exact Q'.le_trans' _ _ _ (by decide : Q'.mkPos 3 4 (by decide) ≤ 1-quarter)
    (Q'.add_le_add_left 1 _ _ (Q'.neg_le_neg hl))

private theorem reserve_le_rate_power (C m s : Nat) (hC : 1 ≤ C)
    (hm : 4*C ≤ m) (hs : s ≤ m) : preimageReserve C ≤ (blocked_rate C m)^s := by
  have hm1 : 1 ≤ m := by omega
  have hprod := Q'.mul_le_mul_of_nonneg_right _ _ _
    (rate_ge_threeQuarters C m hC hm)
    (Q'.pow_nonneg quarter (Q'.le_of_lt quarter_positive) (2*C))
  have hprod' := Q'.mul_le_mul_of_nonneg_left _ _ _
    (blocked_rate_floor C m hC hm) (blocked_rate_nonnegative C m hC hm)
  have he : (blocked_rate C m)*(blocked_rate C m)^(m-1) ≈ (blocked_rate C m)^m := by
    rw [← Q'.pow_succ, Nat.sub_add_cancel hm1]
    exact Q'.eqv_refl _
  exact Q'.le_trans' _ _ _ hprod
    (Q'.le_trans' _ _ _ hprod' (Q'.le_trans' _ _ _ (Q'.le_of_eqv he)
      (HKConvGen.pow_base_antitone (blocked_rate_nonnegative C m hC hm)
        (blocked_rate_le_one C m hC hm) hs)))

private theorem sub_add (a b : RC) : RCadd (RCsub a b) b = a := by
  refine Quotient.inductionOn₂ a b ?_
  exact fun A B => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.sub_add_cancel_eqv (A.approx n) (B.approx n)))

private theorem add_sub_first (a b : RC) : RCsub (RCadd a b) a = b := by
  refine Quotient.inductionOn₂ a b ?_
  exact fun A B => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq (.add (.add (.var 0) (.var 1)) (.neg (.var 0)))
      (.var 1) (by decide) (fun | 0 => A.approx n | _ => B.approx n)))

private theorem budget_floor (A E : RC) (C m : Nat) (hm : 1 ≤ m)
    (hbudget : RCle (RCscale (Q'.ofNat m) (RCsub A E)) (RCscale (Q'.ofNat C) A)) :
    RCle (RCscale (blocked_rate C m) A) E := by
  let r := Q'.invSucc (m-1)
  have hi : r*Q'.ofNat m ≈ 1 := by
    have hi' := Q'.ofNat_succ_mul_invSucc (m-1)
    change Q'.ofNat (m-1+1)*Q'.invSucc (m-1) ≈ 1 at hi'
    rw [Nat.sub_add_cancel hm] at hi'
    exact Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) hi'
  have h := RCscale_mono (Q'.invSucc_nonneg (m-1)) hbudget
  rw [RCscale_RCscale, RCscale_RCscale, RCSignedPairBudget.scale_congr hi, RCscale_one] at h
  have h' := RCadd_le_add h (RCle_refl E)
  rw [sub_add] at h'
  have h'' := RCadd_le_add h' (RCle_refl (RCneg (RCscale (r*Q'.ofNat C) A)))
  change RCle (RCsub A (RCscale (r*Q'.ofNat C) A))
    (RCsub (RCadd (RCscale (r*Q'.ofNat C) A) E) (RCscale (r*Q'.ofNat C) A)) at h''
  rw [add_sub_first] at h''
  have hp : RCsub A (RCscale (r*Q'.ofNat C) A) = RCscale (blocked_rate C m) A := by
    refine Quotient.inductionOn A ?_
    exact fun X => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
      poly_identity_of_normal_eq
        (.add (.var 0) (.neg (.mul (.mul (.var 1) (.var 2)) (.var 0))))
        (.mul (.add (.const 1) (.neg (.mul (.var 2) (.var 1)))) (.var 0))
        (by decide) (fun | 0 => X.approx n | 1 => r | _ => Q'.ofNat C)))
  rwa [hp] at h''

private theorem scale_rational (c q : Q') : RCscale c (Rq q) = Rq (c*q) := by
  rw [RCscale_mk]
  exact Quotient.sound (ofQ'_mul c q).symm

private theorem scale_rational_one (c : Q') : RCscale c (Rq 1) = Rq c :=
  Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.mul_one_eqv c))

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (scale width : Nat) (hwidth : side scale < width)

local notation "B" => completedInner hw0 hw1
local notation "T" => completedTime hw0 hw1
local notation "u" => Subtype.val (dyadicUnitExcitation hw0 hw1 scale width hwidth)
local notation "R" j:arg => dyadicUnitResponse hw0 hw1 scale width hwidth j
local notation "alpha" => anchorNormalizer hw0 hw1 scale width hwidth
local notation "alphaCauchy" => anchorNormalizerCauchy hw0 hw1 scale width hwidth
local notation "z" => Subtype.val (normalizedVacuumExcitation hw0 hw1 scale width hwidth)

attribute [local irreducible] dyadicUnitExcitation dyadicUnitResponse
  anchorNormalizer

private theorem side_halves (hs : 2 ≤ side scale) : side scale/2+side scale/2=side scale := by
  cases scale with
  | zero =>
      have hzero : ¬ (2 ≤ side 0) := by decide
      exact False.elim (hzero hs)
  | succ k =>
      simp only [side, Nat.pow_succ] at hs ⊢
      omega

/-- Computed ORIGINAL integer-time preimage; no inverse transfer is chosen. -/
def halfAnchorPreimage : Completion hw0 hw1 width :=
  completedRealSmul hw0 hw1 alpha alphaCauchy (T (side scale/2) u)

theorem halfAnchorPreimage_pin (hs : 2 ≤ side scale) :
    T (side scale/2) (halfAnchorPreimage hw0 hw1 scale width hwidth) = z := by
  unfold halfAnchorPreimage
  rw [completedTime_realSmul, ← completedTime_add, side_halves scale hs]
  rfl

private theorem response_anchor_bridge (C m start : Nat) (hC : 1 ≤ C)
    (hm : 4*C ≤ m) (hstart : start ≤ side scale) (hs : side scale ≤ m)
    (hbudget : leEv (mul (ofQ' (Q'.ofNat m)) (sub (R start) (R (start+1))))
      (mul (ofQ' (Q'.ofNat C)) (R start))) :
    leEv (mul (ofQ' (preimageReserve C)) (R (side scale))) (R (2*side scale)) := by
  let rho := blocked_rate C m
  have hb : RCle (RCscale (Q'.ofNat m)
      (RCsub (B u (T start u)) (B u (T (start+1) u))))
      (RCscale (Q'.ofNat C) (B u (T start u))) := by
    rw [dyadicUnitResponse_pin, dyadicUnitResponse_pin]
    exact hbudget
  have hfirst := budget_floor _ _ C m (by omega) hb
  have hstep := response_shifted_step_lower hw0 hw1 u rho
    (blocked_rate_nonnegative C m hC hm) start hfirst (side scale-start)
  rw [Nat.add_sub_of_le hstart] at hstep
  have hgeom := response_shifted_geometric_lower hw0 hw1 u rho
    (blocked_rate_nonnegative C m hC hm) (side scale) hstep (side scale)
  have hpos := mixedMoment_nonnegative hw0 hw1 u (side scale) 0
  change RCnonneg (B u (T (side scale) u)) at hpos
  have hc := RCscale_mono_scalar (reserve_le_rate_power C m (side scale) hC hm hs) hpos
  have h := RCle_trans hc hgeom
  rw [dyadicUnitResponse_pin, dyadicUnitResponse_pin,
    show side scale+side scale=2*side scale by omega] at h
  exact h

/-- Uniform cleared preimage norm. Only the SAME relative budget is supplied;
the original anchor norm is allowed to collapse arbitrarily. -/
theorem halfAnchorPreimage_norm_cleared (C m start : Nat) (hC : 1 ≤ C)
    (hm : 4*C ≤ m) (hstart : start ≤ side scale) (hs : side scale ≤ m)
    (hs2 : 2 ≤ side scale)
    (hbudget : leEv (mul (ofQ' (Q'.ofNat m)) (sub (R start) (R (start+1))))
      (mul (ofQ' (Q'.ofNat C)) (R start))) :
    RCle (RCscale (preimageReserve C)
      (B (halfAnchorPreimage hw0 hw1 scale width hwidth)
        (halfAnchorPreimage hw0 hw1 scale width hwidth))) (Rq 1) := by
  have ha : leEv czero alpha := by
    simpa only [anchorNormalizer] using PositiveCRealNormalizationScalar.scalar_nonnegative
      (anchorNorm hw0 hw1 scale width hwidth)
      (anchorNormCauchy hw0 hw1 scale width hwidth)
      (anchorNormFloor hw0 hw1 scale) (anchorNormFloor_positive hw0 hw1 scale)
  have hbridge := response_anchor_bridge hw0 hw1 scale width hwidth C m start hC hm hstart hs hbudget
  have hscaled := leEv_mul_nonneg_left ha (leEv_mul_nonneg_left ha hbridge)
  have hperm : Equiv
      (mul alpha (mul alpha (mul (ofQ' (preimageReserve C)) (R (side scale)))))
      (mul (ofQ' (preimageReserve C)) (mul alpha (mul alpha (R (side scale))))) :=
    SumOfSquares.Equiv_of_approx_eqv (fun n => poly_identity_of_normal_eq
      (.mul (.var 0) (.mul (.var 0) (.mul (.var 1) (.var 2))))
      (.mul (.var 1) (.mul (.var 0) (.mul (.var 0) (.var 2)))) (by decide)
      (fun | 0 => (alpha).approx n | 1 => preimageReserve C | _ => (R (side scale)).approx n))
  unfold halfAnchorPreimage
  rw [completedInner_realSmul_diagonal, completedInner_time_sum, side_halves scale hs2,
    dyadicUnitResponse_pin]
  exact leEv_trans (leEv_of_equiv hperm.symm)
    (leEv_trans hscaled (leEv_of_equiv (anchorNormalizer_normalizes hw0 hw1 scale width hwidth)))

private theorem halfAnchorPreimage_norm_bound (C m start : Nat) (hC : 1 ≤ C)
    (hm : 4*C ≤ m) (hstart : start ≤ side scale) (hs : side scale ≤ m)
    (hs2 : 2 ≤ side scale)
    (hbudget : leEv (mul (ofQ' (Q'.ofNat m)) (sub (R start) (R (start+1))))
      (mul (ofQ' (Q'.ofNat C)) (R start))) :
    RCle (B (halfAnchorPreimage hw0 hw1 scale width hwidth)
        (halfAnchorPreimage hw0 hw1 scale width hwidth))
      (Rq (Q'.recipPos (preimageReserve C) (preimageReserve_positive C))) := by
  have h := RCscale_mono (Q'.le_of_lt (Q'.recipPos_pos _ (preimageReserve_positive C)))
    (halfAnchorPreimage_norm_cleared hw0 hw1 scale width hwidth C m start hC hm hstart hs hs2 hbudget)
  have hi : Q'.recipPos (preimageReserve C) (preimageReserve_positive C)*preimageReserve C ≈ 1 :=
    Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) (Q'.mul_recipPos_eqv _ (preimageReserve_positive C))
  rwa [RCscale_RCscale, RCSignedPairBudget.scale_congr hi, RCscale_one, scale_rational_one] at h

private theorem scaled_mesh_pin (count k : Nat) :
    value ⟨k,count⟩ ≈ Q'.ofNat count*half^k := by
  change (value ⟨k,count⟩).num*((Q'.ofNat count*half^k).den : Int) =
    (Q'.ofNat count*half^k).num*((value ⟨k,count⟩).den : Int)
  rw [value_num, value_den, Q'.mul_den_cast, Q'.mul_num_cast]
  change (count : Int)*(1*((half^k).den : Int)) =
    ((count : Int)*(half^k).num)*(2^k : Nat)
  rw [half_power_num k, half_power_den k, Int.one_mul, Int.mul_one]

/-- Every actual dyadic increment, on the EXISTING normalized state. Its
constant depends only on C, not nome, width, scale or the original norm. -/
theorem normalizedMesh_increment_bound (C m start : Nat) (hC : 1 ≤ C)
    (hm : 4*C ≤ m) (hstart : start ≤ side scale) (hs : side scale ≤ m)
    (hs2 : 2 ≤ side scale)
    (hbudget : leEv (mul (ofQ' (Q'.ofNat m)) (sub (R start) (R (start+1))))
      (mul (ofQ' (Q'.ofNat C)) (R start))) (p : MeshPoint) (k : Nat)
    (ht : value p ≤ Q'.ofNat (side scale/2)*half^k) :
    RCle (completedDist hw0 hw1 (meshAction hw0 hw1 p.depth p.steps z) z)
      (Rq (half^k*Q'.recipPos (preimageReserve C) (preimageReserve_positive C))) := by
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
      (halfAnchorPreimage_norm_bound hw0 hw1 scale width hwidth C m start hC hm hstart hs hs2 hbudget)
    rwa [scale_rational] at hb)

/-- Uniform geometric radius, with factor-two approximation slack. -/
def normalizedGeometricRadius (C : Nat) (epsilon : Q') : Q' :=
  quarter*half^(epsilon*preimageReserve C).den

theorem normalizedGeometricRadius_positive (C : Nat) (epsilon : Q') :
    (0 : Q') < normalizedGeometricRadius C epsilon :=
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

private theorem radius_double (C : Nat) (epsilon : Q') (hs2 : 2 ≤ side scale) :
    Q'.ofNat (side scale)*normalizedGeometricRadius C epsilon +
        Q'.ofNat (side scale)*normalizedGeometricRadius C epsilon ≈
      Q'.ofNat (side scale/2)*half^(epsilon*preimageReserve C).den := by
  have hr : Q'.ofNat (side scale)*normalizedGeometricRadius C epsilon +
      Q'.ofNat (side scale)*normalizedGeometricRadius C epsilon ≈
      (Q'.ofNat (side scale)*half)*half^(epsilon*preimageReserve C).den :=
    Q'.eqv_trans _ _ _
      (poly_identity_of_normal_eq
        (.add (.mul (.var 0) (.mul (.var 2) (.var 1)))
          (.mul (.var 0) (.mul (.var 2) (.var 1))))
        (.mul (.mul (.var 0) (.add (.var 2) (.var 2))) (.var 1)) (by decide)
        (fun
          | 0 => Q'.ofNat (side scale)
          | 1 => half^(epsilon*preimageReserve C).den
          | _ => quarter))
      (Q'.mul_eqv_congr_right _ _ _
        (Q'.mul_eqv_congr_left _ _ _ (by decide : quarter+quarter ≈ half)))
  exact Q'.eqv_trans _ _ _ hr
    (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm (side_half_scalar scale hs2)))

private theorem radius_error (C : Nat) (epsilon : Q') (he : (0 : Q') < epsilon) :
    half^(epsilon*preimageReserve C).den *
      Q'.recipPos (preimageReserve C) (preimageReserve_positive C) ≤ epsilon := by
  have h := Q'.mul_le_mul_of_nonneg_right _ _ _
    (half_den_small (epsilon*preimageReserve C) (Q'.mul_pos he (preimageReserve_positive C)))
    (Q'.le_of_lt (Q'.recipPos_pos _ (preimageReserve_positive C)))
  have heq : (epsilon*preimageReserve C)*Q'.recipPos (preimageReserve C)
      (preimageReserve_positive C) ≈ epsilon :=
    Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv _ _ _)
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _
        (Q'.mul_recipPos_eqv _ (preimageReserve_positive C))) (Q'.mul_one_eqv _))
  exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv heq)

private theorem lattice_radius_positive (C : Nat) (epsilon : Q') :
    (0 : Q') < Q'.ofNat (side scale)*normalizedGeometricRadius C epsilon := by
  have hs : (0 : Q') < Q'.ofNat (side scale) := by
    change (0 : Int)*1 < (side scale : Int)*1
    simp only [Int.mul_one]
    exact_mod_cast BF4DyadicWilsonSquare.side_positive scale
  exact Q'.mul_pos hs (normalizedGeometricRadius_positive C epsilon)

private theorem normalized_real_increment (C m start : Nat) (hC : 1 ≤ C)
    (hm : 4*C ≤ m) (hstart : start ≤ side scale) (hs : side scale ≤ m)
    (hs2 : 2 ≤ side scale)
    (hbudget : leEv (mul (ofQ' (Q'.ofNat m)) (sub (R start) (R (start+1))))
      (mul (ofQ' (Q'.ofNat C)) (R start))) (epsilon : Q') (he : (0 : Q') < epsilon)
    (time : PositiveTime)
    (ht : RCle (realValue (timeValue time))
      (Rq (Q'.ofNat (side scale)*normalizedGeometricRadius C epsilon))) :
    RCle (completedDist hw0 hw1 (realTimeAction hw0 hw1 (timeValue time) z) z) (Rq epsilon) := by
  have hap : leEv (approximationReal time)
      (ofQ' (Q'.ofNat (side scale)*normalizedGeometricRadius C epsilon)) := by
    have hp : Quotient.mk crealSetoid (approximationReal time) = realValue (timeValue time) :=
      Quotient.sound (approximationReal_equiv time)
    rwa [← hp] at ht
  obtain ⟨N,hN⟩ := hap _ (lattice_radius_positive scale C epsilon)
  have hsmall (j : Nat) (hj : N ≤ j) :
      value (approximation time j) ≤ Q'.ofNat (side scale/2)*half^(epsilon*preimageReserve C).den :=
    Q'.le_trans' _ _ _ (hN j hj) (Q'.le_of_eqv (radius_double scale C epsilon hs2))
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
        C m start hC hm hstart hs hs2 hbudget (approximation time j)
        (epsilon*preimageReserve C).den (hsmall j (Nat.le_max_right _ _)))
        (leEv_of_le (ofQ'_le_ofQ' (radius_error C epsilon he)))
    exact RCle_trans hp (RCadd_le_add hpoint (RCle_refl _))
  rw [show rows = incrementRows hw0 hw1 state.range time from rfl, incrementRows_limit,
    show state = normalizedSector hw0 hw1 scale width hwidth from rfl, normalizedSector_pin] at hlimit
  exact hlimit

/-- ALL represented positive real increments on the SAME physical bond state.
The displayed geometric radius depends only on C and epsilon. -/
theorem normalizedBond_geometric_real_increment (C m start : Nat) (hC : 1 ≤ C)
    (hm : 4*C ≤ m) (hstart : start ≤ side scale) (hs : side scale ≤ m)
    (hs2 : 2 ≤ side scale)
    (hbudget : leEv (mul (ofQ' (Q'.ofNat m)) (sub (R start) (R (start+1))))
      (mul (ofQ' (Q'.ofNat C)) (R start))) (epsilon : Q') (he : (0 : Q') < epsilon)
    (time : PositiveTimeValue)
    (ht : RCle (RCscale (spacing scale) (realValue time)) (Rq (normalizedGeometricRadius C epsilon))) :
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
  exact normalized_real_increment hw0 hw1 scale width hwidth C m start hC hm hstart hs hs2
    hbudget epsilon he t ht'

/-- The same modulus propagates to every forward real-time orbit point. -/
theorem normalizedBond_geometric_real_forward_increment (C m start : Nat) (hC : 1 ≤ C)
    (hm : 4*C ≤ m) (hstart : start ≤ side scale) (hs : side scale ≤ m)
    (hs2 : 2 ≤ side scale)
    (hbudget : leEv (mul (ofQ' (Q'.ofNat m)) (sub (R start) (R (start+1))))
      (mul (ofQ' (Q'.ofNat C)) (R start))) (epsilon : Q') (he : (0 : Q') < epsilon)
    (s t : PositiveTimeValue)
    (ht : RCle (RCscale (spacing scale) (realValue t)) (Rq (normalizedGeometricRadius C epsilon))) :
    RCle (bondCompletedDistance hw0 hw1
      (action hw0 hw1 (addTime s t) (normalizedBondExcitation hw0 hw1 scale width hwidth))
      (action hw0 hw1 s (normalizedBondExcitation hw0 hw1 scale width hwidth))) (Rq epsilon) := by
  rw [action_addTime]
  exact RCle_trans (action_distance_bound hw0 hw1 s _ _)
    (normalizedBond_geometric_real_increment hw0 hw1 scale width hwidth C m start hC hm
      hstart hs hs2 hbudget epsilon he t ht)

#print axioms preimageReserve
#print axioms preimageReserve_positive
#print axioms halfAnchorPreimage
#print axioms halfAnchorPreimage_pin
#print axioms halfAnchorPreimage_norm_cleared
#print axioms normalizedMesh_increment_bound
#print axioms normalizedGeometricRadius
#print axioms normalizedGeometricRadius_positive
#print axioms normalizedBond_geometric_real_increment
#print axioms normalizedBond_geometric_real_forward_increment

end YMGap.Continuum.BF4WilsonAllNomeDyadicNormalizedAnchorContinuity
