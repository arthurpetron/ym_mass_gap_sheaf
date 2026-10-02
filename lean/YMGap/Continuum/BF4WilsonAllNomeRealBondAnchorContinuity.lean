/-
# Uniform represented-real increments on ORIGINAL positive-time bond anchors

The SAME finite dyadic dissipation estimate passes through the already
constructed original real-time action. The computed geometric radius
2^(-epsilon.den-1) is independent of nome, width, scale and anchor lag.
Original lattice-time radius is side(scale) times that radius.

The actual original anchored bond rows supply every represented limit and
range witness. No state is normalized again, carrier replaced or continuum
limit assumed. This is uniform within-family time continuity at assigned
geometric spacing, not changing-family convergence, surviving norm, physical
YM calibration, a full canonical OS root or a Yang--Mills mass gap.
-/

import YMGap.Continuum.BF4WilsonAllNomeDyadicBondAnchorContinuity
import YMGap.Continuum.BF4WilsonAllNomeBondOSRealTime

namespace YMGap.Continuum.BF4WilsonAllNomeRealBondAnchorContinuity

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Constructive.HalfPow (half)
open YMGap.Constructive.DyadicTimeRationals (value)
open YMGap.Continuum.PositiveRealDyadicTimeData
  (PositiveTime approximation approximationReal approximationReal_equiv rational)
open YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimePins
  (PositiveTimeValue timeValue realValue)
open YMGap.Continuum.BF4ExactSlabThermodynamicPositiveRealSemigroup (addTime)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4WilsonAllNomeDistance (completedDist)
open YMGap.Continuum.BF4WilsonAllNomeLinear (completedSub)
open YMGap.Continuum.BF4WilsonAllNomeCauchyRows (rowPoint limit)
open YMGap.Continuum.BF4WilsonAllNomeRowPairingLimit (pairingModulus row_pairing_bound)
open YMGap.Continuum.BF4WilsonAllNomeTimeRangeRealContinuity
  (incrementRows incrementRows_pin incrementRows_limit)
open YMGap.Continuum.BF4WilsonAllNomePositiveTimePins (realTimeAction)
open YMGap.Continuum.BF4WilsonAllNomeBondOSCompletion (bondCompletedDistance)
open YMGap.Continuum.BF4WilsonAllNomeBondOSTime (bondValue_distance)
open YMGap.Continuum.BF4WilsonAllNomeBondOSRealTime
  (action action_value action_addTime action_distance_bound)
open YMGap.Continuum.BF4DyadicWilsonSquare
open YMGap.Continuum.BF4WilsonAllNomeDyadicUnitExcitation
open YMGap.Continuum.BF4WilsonAllNomeDyadicBondAnchor
open YMGap.Continuum.BF4WilsonAllNomeDyadicBondAnchorContinuity

local notation "Rq" q:arg => Quotient.mk crealSetoid (ofQ' q)
local notation "half" => YMGap.Constructive.HalfPow.half

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (scale width : Nat) (hwidth : side scale < width)

local notation "B" => completedInner hw0 hw1
local notation "T" => completedTime hw0 hw1
local notation "u" => Subtype.val (dyadicUnitExcitation hw0 hw1 scale width hwidth)
local notation "x" j:arg => anchoredBondExcitation hw0 hw1 scale width hwidth j

/-- Computed lattice-time radius; its assigned geometric value is anchoredRadius. -/
def latticeRadius (epsilon : Q') : Q' := Q'.ofNat (side scale)*anchoredRadius epsilon

private theorem side_rational_positive : (0 : Q') < Q'.ofNat (side scale) := by
  change (0 : Int)*1 < (side scale : Int)*1
  simp only [Int.mul_one]
  exact_mod_cast side_positive scale

theorem latticeRadius_positive (epsilon : Q') :
    (0 : Q') < latticeRadius scale epsilon :=
  Q'.mul_pos (side_rational_positive scale) (anchoredRadius_positive epsilon)

/-- Pass the uniform dyadic bound through the original represented increment
rows, retaining their SAME actual positive-real-time limit. -/
theorem anchored_real_increment (lag : Nat) (epsilon : Q')
    (he : (0 : Q') < epsilon) (time : PositiveTime)
    (ht : RCle (realValue (timeValue time)) (Rq (latticeRadius scale epsilon))) :
    RCle (completedDist hw0 hw1
      (realTimeAction hw0 hw1 (timeValue time) (T (side scale+lag) u))
      (T (side scale+lag) u)) (Rq epsilon) := by
  have htime : Quotient.mk crealSetoid (approximationReal time) =
      realValue (timeValue time) := Quotient.sound (approximationReal_equiv time)
  have hap : RCle (Quotient.mk crealSetoid (approximationReal time))
      (Rq (latticeRadius scale epsilon)) := by
    rw [htime]
    exact ht
  change leEv (approximationReal time) (ofQ' (latticeRadius scale epsilon)) at hap
  obtain ⟨N,hN⟩ := hap (latticeRadius scale epsilon) (latticeRadius_positive scale epsilon)
  have hsmall (n : Nat) (hn : N ≤ n) :
      value (approximation time n) ≤ Q'.ofNat (side scale)*half^epsilon.den :=
    Q'.le_trans' _ _ _ (hN n hn) (Q'.le_of_eqv (radius_double scale epsilon))
  let state := anchoredSector hw0 hw1 scale width hwidth lag
  let rows := incrementRows hw0 hw1 state.range time
  have hlimit : RCle (B (limit hw0 hw1 rows) (limit hw0 hw1 rows)) (Rq epsilon) := by
    apply RationalScalarTwoSidedError.le_of_all_errors
    intro delta hd
    let n := max (pairingModulus hw0 hw1 rows rows delta) N
    have hp := (row_pairing_bound hw0 hw1 rows rows delta hd n (Nat.le_max_left _ _)).2
    have hs : RCle (B (rowPoint hw0 hw1 rows n) (rowPoint hw0 hw1 rows n))
        (Rq epsilon) := by
      rw [show rows = incrementRows hw0 hw1 state.range time from rfl, incrementRows_pin]
      rw [show state = anchoredSector hw0 hw1 scale width hwidth lag from rfl,
        anchoredSector_pin]
      exact RCle_trans (anchoredMesh_increment_bound hw0 hw1 scale width hwidth
        lag (approximation time n) epsilon.den (hsmall n (Nat.le_max_right _ _)))
        (leEv_of_le (ofQ'_le_ofQ' (half_den_small epsilon he)))
    exact RCle_trans hp (RCadd_le_add hs (RCle_refl _))
  rw [show rows = incrementRows hw0 hw1 state.range time from rfl, incrementRows_limit,
    show state = anchoredSector hw0 hw1 scale width hwidth lag from rfl,
    anchoredSector_pin] at hlimit
  exact hlimit

/-- ALL represented positive numerical real times, on the EXISTING physical
bond action. Radius is explicit and geometric-uniform, not physical calibration. -/
theorem anchoredBond_real_increment (lag : Nat) (epsilon : Q')
    (he : (0 : Q') < epsilon) (time : PositiveTimeValue)
    (ht : RCle (realValue time) (Rq (latticeRadius scale epsilon))) :
    RCle (bondCompletedDistance hw0 hw1 (action hw0 hw1 time (x lag)) (x lag))
      (Rq epsilon) := by
  rw [bondValue_distance, action_value, anchoredBond_value]
  revert ht
  refine Quotient.inductionOn time ?_
  intro t ht
  exact anchored_real_increment hw0 hw1 scale width hwidth lag epsilon he t ht

private theorem scale_rational (c q : Q') : RCscale c (Rq q) = Rq (c*q) := by
  rw [RCscale_mk]
  exact Quotient.sound (CRealAlg.ofQ'_mul c q).symm

/-- The explicit SAME original numerical time is measured with the assigned
geometric spacing, not replaced by a legacy rescaled carrier/action. -/
theorem rescaled_time_bound (epsilon : Q') (time : PositiveTimeValue)
    (ht : RCle (RCscale (spacing scale) (realValue time)) (Rq (anchoredRadius epsilon))) :
    RCle (realValue time) (Rq (latticeRadius scale epsilon)) := by
  have h := RCscale_mono (Q'.ofNat_nonneg (side scale)) ht
  have hc : Q'.eqv (Q'.ofNat (side scale)*spacing scale) 1 :=
    Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) (unit_side scale)
  rw [RCscale_RCscale, RCSignedPairBudget.scale_congr hc, RCscale_one,
    scale_rational] at h
  exact h

/-- Uniform over every strict nome, width, scale and nonnegative anchor lag,
for EVERY positive represented real increment with small assigned geometric time. -/
theorem anchoredBond_geometric_real_increment (lag : Nat) (epsilon : Q')
    (he : (0 : Q') < epsilon) (time : PositiveTimeValue)
    (ht : RCle (RCscale (spacing scale) (realValue time)) (Rq (anchoredRadius epsilon))) :
    RCle (bondCompletedDistance hw0 hw1 (action hw0 hw1 time (x lag)) (x lag))
      (Rq epsilon) :=
  anchoredBond_real_increment hw0 hw1 scale width hwidth lag epsilon he time
    (rescaled_time_bound scale epsilon time ht)

/-- The SAME uniform radius propagates to every forward real-time orbit point. -/
theorem anchoredBond_geometric_real_forward_increment (lag : Nat) (epsilon : Q')
    (he : (0 : Q') < epsilon) (s t : PositiveTimeValue)
    (ht : RCle (RCscale (spacing scale) (realValue t)) (Rq (anchoredRadius epsilon))) :
    RCle (bondCompletedDistance hw0 hw1
      (action hw0 hw1 (addTime s t) (x lag)) (action hw0 hw1 s (x lag)))
      (Rq epsilon) := by
  rw [action_addTime]
  exact RCle_trans (action_distance_bound hw0 hw1 s _ _)
    (anchoredBond_geometric_real_increment hw0 hw1 scale width hwidth lag epsilon he t ht)

#print axioms latticeRadius
#print axioms latticeRadius_positive
#print axioms anchored_real_increment
#print axioms anchoredBond_real_increment
#print axioms rescaled_time_bound
#print axioms anchoredBond_geometric_real_increment
#print axioms anchoredBond_geometric_real_forward_increment

end YMGap.Continuum.BF4WilsonAllNomeRealBondAnchorContinuity
