/-
# Shifted geometric survival from the SAME filtered response

The actual completed time-map second difference propagates a Rayleigh
floor starting at ANY integer response, without a half-time state.
For the EXISTING dyadic unit state, a bounded relative filtered budget
  m*(R(1)-R(2)) <= C*R(1),   1<=C, 4*C<=m,
and a lag-one reserve gamma0 give
  R(m) >= gamma0*(1/4)^(2*C).
The positive rational coefficient is computed, but neither the relative
budget nor a useful reserve is proved along a changing family. No original
source estimate, cross-scale limit or continuum survival is asserted.
-/

import YMGap.Continuum.BF4WilsonAllNomeDyadicFilteredSurvival
import YMGap.Continuum.BF4WilsonAllNomeResponseLower
import YMGap.Continuum.RationalBlockedSurvival
import YMGap.Continuum.ReconstructionCapstone

namespace YMGap.Continuum.BF4WilsonAllNomeDyadicFilteredGeometricSurvival

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4WilsonAllNomeTimeDefectMoments
open YMGap.Continuum.BF4WilsonAllNomeResponseLower (response_second_difference)
open YMGap.Continuum.BF4WilsonAllNomeDyadicUnitExcitation
open YMGap.Continuum.BF4DyadicWilsonSquare (side)
open YMGap.Continuum.RationalBlockedSurvival

local infix:50 " ≈ " => Q'.eqv
local notation "Rq" a:arg => Quotient.mk crealSetoid (ofQ' a)

private theorem zero_add (a : RC) : RCadd RCzero a = a := by
  refine Quotient.inductionOn a ?_
  exact fun A => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.eqv_of_eq (Q'.zero_add' (A.approx n))))

private theorem sub_self (a : RC) : RCsub a a = RCzero := by
  refine Quotient.inductionOn a ?_
  exact fun A => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.add_neg_self_eqv (A.approx n)))

private theorem sub_add (a b : RC) : RCadd (RCsub a b) b = a := by
  refine Quotient.inductionOn₂ a b ?_
  exact fun A B => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.sub_add_cancel_eqv (A.approx n) (B.approx n)))

private theorem add_sub_first (a b : RC) : RCsub (RCadd a b) a = b := by
  refine Quotient.inductionOn₂ a b ?_
  exact fun A B => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq (.add (.add (.var 0) (.var 1)) (.neg (.var 0)))
      (.var 1) (by decide) (fun | 0 => A.approx n | _ => B.approx n)))

private theorem sub_nonnegative {a b : RC} (h : RCle b a) :
    RCnonneg (RCsub a b) := by
  have h' := RCadd_le_add h (RCle_refl (RCneg b))
  change RCle (RCsub b b) (RCsub a b) at h'
  rwa [sub_self] at h'

private theorem le_of_sub_nonnegative {a b : RC}
    (h : RCnonneg (RCsub a b)) : RCle b a := by
  have h' := RCadd_le_add h (RCle_refl b)
  rwa [zero_add, sub_add] at h'

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "T" => completedTime hw0 hw1

/-- Propagate an initial adjacent-response floor at the literal integer
start, using positivity of powers of the SAME completed time map. -/
theorem response_shifted_step_lower (x : V) (rho : Q') (hrho : (0 : Q') ≤ rho)
    (start : Nat) (hfloor : RCle (RCscale rho (B x (T start x)))
      (B x (T (start+1) x))) : ∀ lag : Nat,
    RCle (RCscale rho (B x (T (start+lag) x))) (B x (T (start+lag+1) x))
  | 0 => by simpa only [Nat.add_zero] using hfloor
  | lag+1 => by
      have h := RCscale_mono hrho
        (sub_nonnegative (response_shifted_step_lower x rho hrho start hfloor lag))
      rw [RCscale_RCzero] at h
      have hd := response_second_difference hw0 hw1 x rho (start+lag)
      have hnext := le_of_sub_nonnegative (RCle_trans h hd)
      simpa only [Nat.add_assoc] using hnext

/-- The shifted geometric bound uses the original state and operator; no
fractional-time image is introduced. -/
theorem response_shifted_geometric_lower (x : V) (rho : Q') (hrho : (0 : Q') ≤ rho)
    (start : Nat) (hfloor : RCle (RCscale rho (B x (T start x)))
      (B x (T (start+1) x))) : ∀ lag : Nat,
    RCle (RCscale (rho^lag) (B x (T start x))) (B x (T (start+lag) x))
  | 0 => by rw [Q'.pow_zero, RCscale_one, Nat.add_zero]; exact RCle_refl _
  | lag+1 => by
      have h := RCle_trans
        (RCscale_mono hrho (response_shifted_geometric_lower x rho hrho start hfloor lag))
        (response_shifted_step_lower hw0 hw1 x rho hrho start hfloor lag)
      rw [RCscale_RCscale] at h
      simpa only [Q'.pow_succ, Nat.add_assoc] using h

private theorem budget_floor (A E : RC) (C m : Nat) (hm : 1 ≤ m)
    (hbudget : RCle (RCscale (Q'.ofNat m) (RCsub A E))
      (RCscale (Q'.ofNat C) A)) : RCle (RCscale (blocked_rate C m) A) E := by
  let r := Q'.invSucc (m-1)
  have hi : r*Q'.ofNat m ≈ 1 := by
    dsimp only [r]
    have hi' := Q'.ofNat_succ_mul_invSucc (m-1)
    change Q'.ofNat (m-1+1)*Q'.invSucc (m-1) ≈ 1 at hi'
    rw [Nat.sub_add_cancel hm] at hi'
    exact Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) hi'
  have h := RCscale_mono (Q'.invSucc_nonneg (m-1)) hbudget
  rw [RCscale_RCscale, RCscale_RCscale,
    RCSignedPairBudget.scale_congr hi, RCscale_one] at h
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

variable (scale : Nat) (hwidth : side scale < width)

attribute [local irreducible] dyadicUnitExcitation dyadicUnitResponse

local notation "u" => Subtype.val (dyadicUnitExcitation hw0 hw1 scale width hwidth)
local notation "R" lag:arg => dyadicUnitResponse hw0 hw1 scale width hwidth lag

/-- Literal lag-one starting point on the EXISTING original dyadic unit state. -/
theorem dyadicUnitResponse_shifted_geometric_lower (rho : Q')
    (hrho : (0 : Q') ≤ rho) (hfloor : leEv (mul (ofQ' rho) (R 1)) (R 2))
    (lag : Nat) : leEv (mul (ofQ' (rho^lag)) (R 1)) (R (1+lag)) := by
  have hstart : RCle (RCscale rho (B u (T 1 u))) (B u (T 2 u)) := by
    rw [dyadicUnitResponse_pin, dyadicUnitResponse_pin]
    exact hfloor
  have h := response_shifted_geometric_lower hw0 hw1 u rho hrho 1 hstart lag
  rw [dyadicUnitResponse_pin, dyadicUnitResponse_pin] at h
  exact h

/-- A bounded RELATIVE filtered budget permits arbitrary fixed C, rather
than requiring its total cost to fit the linear reserve. Both quantitative
inputs are explicit assumptions, not estimates produced by this module. -/
theorem dyadicUnitResponse_filtered_block_floor (C m : Nat) (hC : 1 ≤ C)
    (hm : 4*C ≤ m) (gamma0 : Q') (hreserve : leEv (ofQ' gamma0) (R 1))
    (hbudget : leEv (mul (ofQ' (Q'.ofNat m)) (sub (R 1) (R 2)))
      (mul (ofQ' (Q'.ofNat C)) (R 1))) :
    leEv (ofQ' (gamma0*quarter^(2*C))) (R m) := by
  have hm1 : 1 ≤ m := by omega
  let rho := blocked_rate C m
  let p := quarter^(2*C)
  have hbudget' : RCle (RCscale (Q'.ofNat m) (RCsub (B u (T 1 u)) (B u (T 2 u))))
      (RCscale (Q'.ofNat C) (B u (T 1 u))) := by
    rw [dyadicUnitResponse_pin, dyadicUnitResponse_pin]
    exact hbudget
  have hstart := budget_floor (B u (T 1 u)) (B u (T 2 u)) C m hm1 hbudget'
  have hgeom := response_shifted_geometric_lower hw0 hw1 u rho
    (blocked_rate_nonnegative C m hC hm) 1 hstart (m-1)
  rw [show 1+(m-1)=m by omega] at hgeom
  have hpos : RCnonneg (B u (T 1 u)) := completedInner_oneStep_nonnegative hw0 hw1 u
  have hscalar := RCscale_mono_scalar (blocked_rate_floor C m hC hm) hpos
  have hreserve' : RCle (Rq gamma0) (B u (T 1 u)) := by
    rw [dyadicUnitResponse_pin]
    exact hreserve
  have hscaled := RCscale_mono (Q'.pow_nonneg quarter (Q'.le_of_lt quarter_positive) (2*C)) hreserve'
  have hp : RCscale p (Rq gamma0) = Rq (gamma0*p) :=
    Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.mul_comm_eqv p gamma0))
  have h := RCle_trans hscaled (RCle_trans hscalar hgeom)
  rw [hp, dyadicUnitResponse_pin] at h
  exact h

/-- The computed rational floor is strictly positive whenever the supplied
lag-one reserve is. No uniform reserve or original-source budget is derived. -/
theorem dyadicUnitResponse_filtered_block_ne_zero (C m : Nat) (hC : 1 ≤ C)
    (hm : 4*C ≤ m) (gamma0 : Q') (hgamma0 : (0 : Q') < gamma0)
    (hreserve : leEv (ofQ' gamma0) (R 1))
    (hbudget : leEv (mul (ofQ' (Q'.ofNat m)) (sub (R 1) (R 2)))
      (mul (ofQ' (Q'.ofNat C)) (R 1))) : ¬ Equiv (R m) czero := by
  intro hz
  have h := leEv_trans
    (dyadicUnitResponse_filtered_block_floor hw0 hw1 scale hwidth C m hC hm gamma0 hreserve hbudget)
    (leEv_of_equiv hz)
  have hbad : gamma0*quarter^(2*C) ≤ (0 : Q') := by
    apply Q'.le_of_forall_pos_add
    intro epsilon hepsilon
    obtain ⟨N,hN⟩ := h epsilon hepsilon
    exact hN N (Nat.le_refl N)
  have hfloor : (0 : Q') < gamma0*quarter^(2*C) := Q'.mul_pos hgamma0
    (HKPos.pow_pos quarter_positive (2*C))
  exact (by decide : ¬ (0 : Q') < 0) (Q'.pos_of_lt_of_le hfloor hbad)

#print axioms response_shifted_step_lower
#print axioms response_shifted_geometric_lower
#print axioms dyadicUnitResponse_shifted_geometric_lower
#print axioms dyadicUnitResponse_filtered_block_floor
#print axioms dyadicUnitResponse_filtered_block_ne_zero

end YMGap.Continuum.BF4WilsonAllNomeDyadicFilteredGeometricSurvival
