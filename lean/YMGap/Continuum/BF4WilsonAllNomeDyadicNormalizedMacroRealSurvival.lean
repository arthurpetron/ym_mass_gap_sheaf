/-
# All represented real-time survival of the SAME normalized bond anchor

The original dyadic response decreases with its mesh time: at the finer
square-root mesh it is a squared norm, and the remaining evolution contracts.
The existing witnessed time-row limit passes this order to a strictly later
integer endpoint. A positive integer slack absorbs upper-rounded time
approximants, so no real-time antitonicity or endpoint identity is assumed.

For the existing normalized anchor, kappa*R(side)<=R(2*side) therefore gives
response >=kappa^(j+1) at EVERY represented positive real geometric time <=j.
The ONE-block slack is explicit. No uniform raw norm floor, microscopic
budget, new carrier or inverse transfer is introduced. Geometric spacing is
not a physical calibration; the family ratio estimate, cross-scale limit and
continuum Yang--Mills identification remain open.
-/

import YMGap.Continuum.BF4WilsonAllNomeDyadicNormalizedMacroRatio

namespace YMGap.Continuum.BF4WilsonAllNomeDyadicNormalizedMacroRealSurvival

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Constructive.NonnegativeDyadicTime (embed)
open YMGap.Constructive.DyadicTimeRationals (value value_num value_den)
open YMGap.Continuum.BF4WilsonAllNomeSeminorm (seminorm)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4WilsonAllNomeDyadicSemigroup
  (meshAction mesh_add mesh_symmetric mesh_norm_bound mesh_double
   mesh_refinement mesh_original action_embed)
open YMGap.Continuum.BF4WilsonAllNomePositiveTimeAction
  (positiveAction positiveAction_pin timeRows timeRows_pin)
open YMGap.Continuum.BF4WilsonAllNomePositiveTimePins
  (realTimeAction realTimeAction_pin)
open YMGap.Continuum.BF4WilsonAllNomeCauchyRows (limit rowPoint)
open YMGap.Continuum.BF4WilsonAllNomeRowPairingLimit
  (constantRows constantRows_point limit_constantRows pairingModulus row_pairing_bound)
open YMGap.Continuum.PositiveRealDyadicTimeData
  (PositiveTime approximation approximationReal approximationReal_equiv)
open YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimePins
  (PositiveTimeValue timeValue realValue)
open YMGap.Continuum.BF4DyadicWilsonSquare (side spacing unit_side)
open YMGap.Continuum.BF4WilsonAllNomeDyadicUnitExcitation (dyadicUnitResponse)
open YMGap.Continuum.BF4WilsonAllNomeDyadicNormalizedBondAnchor
open YMGap.Continuum.BF4WilsonAllNomeDyadicNormalizedMacroRatio
  (normalizedAnchorResponse_block_floor)
open YMGap.Continuum.BF4WilsonAllNomeBondOSCompletion (bondCompletedInner)
open YMGap.Continuum.BF4WilsonAllNomeBondOSTime (bondValue_inner)
open YMGap.Continuum.BF4WilsonAllNomeBondOSRealTime (action action_value)

local notation "Rq" q:arg => Quotient.mk crealSetoid (ofQ' q)
local infix:50 " ≈ " => Q'.eqv

section Generic

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "D" => seminorm hw0 hw1 (width := width)
local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "T" => completedTime hw0 hw1
local notation "S" => meshAction hw0 hw1
local notation "Class" => Quotient.mk
  (CRealSeminormCompletion.SquaredSeminorm.completionSetoid
    (seminorm hw0 hw1 (width := width)))

/-- Actual dyadic response order on the original carrier. No source sign,
spectral measure or normalized-state premise is used. -/
theorem mesh_response_antitone (x : V) (depth a b : Nat) (hab : a ≤ b) :
    RCle (B x (S depth b x)) (B x (S depth a x)) := by
  have h := mesh_norm_bound hw0 hw1 (depth+1) (b-a) (S (depth+1) a x)
  rw [← mesh_add, Nat.sub_add_cancel hab] at h
  have hp (n : Nat) : B x (S depth n x) =
      B (S (depth+1) n x) (S (depth+1) n x) := by
    rw [← mesh_double hw0 hw1 depth n x,
      mesh_add hw0 hw1 (depth+1) n n x,
      ← mesh_symmetric hw0 hw1 (depth+1) n x (S (depth+1) n x)]
  rwa [← hp b, ← hp a] at h

private theorem mesh_integer_pin (depth L : Nat) (x : V) :
    S depth (L*2^depth) x = T L x := by
  simpa only [Nat.zero_add, mesh_original] using
    mesh_refinement hw0 hw1 0 depth L x

private theorem ofNat_positive (n : Nat) (hn : 0 < n) : (0 : Q') < Q'.ofNat n := by
  change (0 : Int)*1 < (n : Int)*1
  simp only [Int.mul_one]
  exact_mod_cast hn

/-- A positive integer slack makes the actual upper-rounded approximants
eventually earlier than the comparison endpoint. The SAME existing pairing
limit, not an assumed real-time order law, supplies the final inequality. -/
theorem positiveAction_response_integer_slack (x : V) (time : PositiveTime)
    (L gap : Nat) (hgap : 0 < gap)
    (ht : leEv time.real (ofQ' (Q'.ofNat L))) :
    RCle (B x (T (L+gap) x)) (B x (positiveAction hw0 hw1 time x)) := by
  have hap : leEv (approximationReal time) (ofQ' (Q'.ofNat L)) :=
    leEv_trans (leEv_of_equiv (approximationReal_equiv time)) ht
  obtain ⟨N,hN⟩ := hap _ (ofNat_positive gap hgap)
  refine Quotient.inductionOn x ?_
  intro X
  rw [positiveAction_pin]
  apply RationalScalarTwoSidedError.le_of_all_errors
  intro epsilon he
  let R := constantRows hw0 hw1 X
  let Q := timeRows hw0 hw1 time X
  let n := max (pairingModulus hw0 hw1 R Q epsilon) N
  have hpoint : value (approximation time n) ≤ Q'.ofNat (L+gap) :=
    Q'.le_trans' _ _ _ (hN n (Nat.le_max_right _ _))
      (Q'.le_of_eqv (Q'.eqv_symm (Q'.ofNat_add_eqv L gap)))
  have hsteps : (approximation time n).steps ≤
      (L+gap)*2^(approximation time n).depth := by
    change (value (approximation time n)).num*1 ≤
      ((L+gap : Nat) : Int)*((value (approximation time n)).den : Int) at hpoint
    rw [value_num, value_den, Int.mul_one] at hpoint
    exact_mod_cast hpoint
  have hm := mesh_response_antitone hw0 hw1 (Class X)
    (approximation time n).depth (approximation time n).steps
    ((L+gap)*2^(approximation time n).depth) hsteps
  rw [mesh_integer_pin] at hm
  have hrow := (row_pairing_bound hw0 hw1 R Q epsilon he n (Nat.le_max_left _ _)).1
  dsimp only [R, Q] at hrow
  rw [constantRows_point, timeRows_pin, limit_constantRows, action_embed] at hrow
  exact RCle_trans hm hrow

private theorem scale_rational (c q : Q') : RCscale c (Rq q) = Rq (c*q) := by
  rw [RCscale_mk]
  exact Quotient.sound (CRealAlg.ofQ'_mul c q).symm

end Generic

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (scale width : Nat) (hwidth : side scale < width)

local notation "B" => completedInner hw0 hw1
local notation "T" => completedTime hw0 hw1
local notation "z" => Subtype.val (normalizedVacuumExcitation hw0 hw1 scale width hwidth)
local notation "R" j:arg => dyadicUnitResponse hw0 hw1 scale width hwidth j

attribute [local irreducible] normalizedVacuumExcitation dyadicUnitResponse

/-- All represented positive real times up to geometric horizon j. The
proved floor has ONE explicit block of slack, kappa^(j+1). In particular this
applies to every j>=1; no extra adjacent budget or half-time state is needed. -/
theorem normalizedBond_geometric_real_floor (kappa : Q') (hkappa : (0 : Q') < kappa)
    (hratio : leEv (mul (ofQ' kappa) (R (side scale))) (R (2*side scale)))
    (j : Nat) (time : PositiveTimeValue)
    (ht : RCle (RCscale (spacing scale) (realValue time)) (Rq (Q'.ofNat j))) :
    RCle (Rq (kappa^(j+1)))
      (bondCompletedInner hw0 hw1
        (normalizedBondExcitation hw0 hw1 scale width hwidth)
        (action hw0 hw1 time (normalizedBondExcitation hw0 hw1 scale width hwidth))) := by
  have ht' := RCscale_mono (Q'.ofNat_nonneg (side scale)) ht
  have hi : Q'.ofNat (side scale)*spacing scale ≈ 1 :=
    Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) (unit_side scale)
  rw [RCscale_RCscale, RCSignedPairBudget.scale_congr hi, RCscale_one, scale_rational] at ht'
  have he : Rq (Q'.ofNat (side scale)*Q'.ofNat j) = Rq (Q'.ofNat (j*side scale)) :=
    Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun _ =>
      Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _)
        (Q'.eqv_symm (SU3CharFactor.ofNat_mul_eqv j (side scale)))))
  rw [he] at ht'
  have hfloor : RCle (Rq (kappa^(j+1))) (B z (T ((j+1)*side scale) z)) := by
    rw [normalizedAnchorResponse_pin]
    exact normalizedAnchorResponse_block_floor hw0 hw1 scale width hwidth kappa hkappa hratio (j+1)
  rw [bondValue_inner, action_value, normalizedBond_value]
  revert ht'
  refine Quotient.inductionOn time ?_
  intro t ht'
  change RCle (Rq (kappa^(j+1))) (B z (realTimeAction hw0 hw1 (timeValue t) z))
  rw [realTimeAction_pin]
  have hreal := positiveAction_response_integer_slack hw0 hw1 z t
    (j*side scale) (side scale) (BF4DyadicWilsonSquare.side_positive scale) ht'
  rw [show j*side scale+side scale=(j+1)*side scale by
    rw [Nat.add_mul, Nat.one_mul]] at hreal
  exact RCle_trans hfloor hreal

#print axioms mesh_response_antitone
#print axioms positiveAction_response_integer_slack
#print axioms normalizedBond_geometric_real_floor

end YMGap.Continuum.BF4WilsonAllNomeDyadicNormalizedMacroRealSurvival
