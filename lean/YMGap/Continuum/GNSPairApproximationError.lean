/-
# Energy-relative error in a completed signed Gram entry

This is a scalar and completed-GNS estimate.  It compares pairings of
supplied vectors on the same carrier; it does not assert a useful lower
bound for any Gram sum.
-/

import YMGap.Continuum.ContinuousFunctionalCalculusForm
import YMGap.Continuum.RCSignedPairBudget
import YMGap.Continuum.GNSFiniteSumEnergy

namespace YMGap.Continuum.GNSPairApproximationError

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.GNSProjectionSweep
open YMGap.Continuum.HamiltonianScalar
open YMGap.Continuum.RingNormaliser

local infix:50 " ≈ " => Q'.eqv

/-- The endpoint coefficient for one signed Gram-entry approximation. -/
def pairErrorCoefficient (delta : Q') : Q' :=
  delta + HalfPow.half * (delta * delta)

theorem pairErrorCoefficient_nonnegative (delta : Q')
    (hdelta : (0 : Q') ≤ delta) :
    (0 : Q') ≤ pairErrorCoefficient delta := by
  unfold pairErrorCoefficient
  exact Q'.zero_le_add _ _ hdelta
    (Q'.mul_nonneg _ _ HalfPow.half_nonneg
      (Q'.mul_nonneg _ _ hdelta hdelta))

private theorem rc_zero_add (a : RC) : RCadd RCzero a = a := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.eqv_of_eq (Q'.zero_add' (A.approx n))))

private theorem rc_sub_add_cancel (a b : RC) : RCadd (RCsub a b) b = a := by
  refine Quotient.inductionOn₂ a b ?_
  intro A B
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.sub_add_cancel_eqv (A.approx n) (B.approx n)))

private theorem rc_add_neg_cancel (a b : RC) :
    RCadd (RCadd a b) (RCneg b) = a := by
  refine Quotient.inductionOn₂ a b ?_
  intro A B
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.add (.add (.var 0) (.var 1)) (.neg (.var 1))) (.var 0)
      (by decide) (fun | 0 => A.approx n | _ => B.approx n)))

private theorem rc_scale_neg (q : Q') (a : RC) :
    RCscale q (RCneg a) = RCneg (RCscale q a) := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    Q'.mul_neg_eqv q (A.approx n)))

private theorem rc_half_double (a : RC) :
    RCscale HalfPow.half (RCscale 2 a) = a := by
  rw [RCscale_RCscale,
    RCSignedPairBudget.scale_congr (by decide : Q'.eqv (HalfPow.half * 2) 1) a,
    RCscale_one]

variable (S : SmulGNSData)
local notation "D" => S.toGNSData

private theorem norm_add (x y : GNSCompletionSpace D) :
    normSq ((D).cAdd x y) =
      RCadd (RCadd (normSq x) ((D).cinnerCompl x y))
        (RCadd ((D).cinnerCompl x y) (normSq y)) := by
  unfold normSq
  rw [(D).cinnerCompl_cAdd_left, (D).cinnerCompl_cAdd_right,
    (D).cinnerCompl_cAdd_right, (D).cinnerCompl_comm y x]

private theorem norm_sub (x y : GNSCompletionSpace D) :
    normSq ((D).cSub x y) =
      RCsub (RCsub (normSq x) ((D).cinnerCompl x y))
        (RCsub ((D).cinnerCompl x y) (normSq y)) := by
  unfold normSq
  rw [(D).cinnerCompl_cSub_left, (D).cinnerCompl_comm x ((D).cSub x y),
    (D).cinnerCompl_cSub_left, (D).cinnerCompl_comm y ((D).cSub x y),
    (D).cinnerCompl_cSub_left, (D).cinnerCompl_comm y x]

private theorem norm_add_as (x y : GNSCompletionSpace D) :
    normSq ((D).cAdd x y) =
      RCadd (RCadd (normSq x) (normSq y))
        (RCscale 2 ((D).cinnerCompl x y)) := by
  rw [norm_add]
  refine Quotient.inductionOn₃ (normSq x) (normSq y) ((D).cinnerCompl x y) ?_
  intro A B C
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.add (.add (.var 0) (.var 2)) (.add (.var 2) (.var 1)))
      (.add (.add (.var 0) (.var 1)) (.mul (.const 2) (.var 2)))
      (by decide) (fun | 0 => A.approx n | 1 => B.approx n | _ => C.approx n)))

private theorem norm_sub_as (x y : GNSCompletionSpace D) :
    normSq ((D).cSub x y) =
      RCsub (RCadd (normSq x) (normSq y))
        (RCscale 2 ((D).cinnerCompl x y)) := by
  rw [norm_sub]
  refine Quotient.inductionOn₃ (normSq x) (normSq y) ((D).cinnerCompl x y) ?_
  intro A B C
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.add (.add (.var 0) (.neg (.var 2)))
        (.neg (.add (.var 2) (.neg (.var 1)))))
      (.add (.add (.var 0) (.var 1)) (.neg (.mul (.const 2) (.var 2))))
      (by decide) (fun | 0 => A.approx n | 1 => B.approx n | _ => C.approx n)))

/-- Two-sided completed Young inequality with supplied squared-energy caps. -/
theorem pairing_young (x y : GNSCompletionSpace D) (A B : RC)
    (hx : RCle (normSq x) A) (hy : RCle (normSq y) B) :
    RCle ((D).cinnerCompl x y) (RCscale HalfPow.half (RCadd A B)) ∧
    RCle (RCneg ((D).cinnerCompl x y))
      (RCscale HalfPow.half (RCadd A B)) := by
  let c := (D).cinnerCompl x y
  have hupper : RCle (RCscale 2 c) (RCadd (normSq x) (normSq y)) := by
    have h := RCadd_le_add ((D).cinner_self_nonneg ((D).cSub x y))
      (RCle_refl (RCscale 2 c))
    change RCle (RCadd RCzero (RCscale 2 c))
      (RCadd (normSq ((D).cSub x y)) (RCscale 2 c)) at h
    rw [rc_zero_add, norm_sub_as S x y, rc_sub_add_cancel] at h
    exact h
  have hlower : RCle (RCneg (RCscale 2 c))
      (RCadd (normSq x) (normSq y)) := by
    have h := RCadd_le_add ((D).cinner_self_nonneg ((D).cAdd x y))
      (RCle_refl (RCneg (RCscale 2 c)))
    change RCle (RCadd RCzero (RCneg (RCscale 2 c)))
      (RCadd (normSq ((D).cAdd x y)) (RCneg (RCscale 2 c))) at h
    rw [rc_zero_add, norm_add_as S x y, rc_add_neg_cancel] at h
    exact h
  have hcap := RCadd_le_add hx hy
  constructor
  · have h := RCscale_mono HalfPow.half_nonneg (RCle_trans hupper hcap)
    rw [rc_half_double] at h
    exact h
  · have h := RCscale_mono HalfPow.half_nonneg (RCle_trans hlower hcap)
    rw [rc_scale_neg, rc_half_double] at h
    exact h

private theorem norm_smul (q : Q') (x : GNSCompletionSpace D) :
    normSq (S.cSmul q x) = RCscale (q*q) (normSq x) := by
  unfold normSq
  rw [S.cinnerCompl_cSmul_left, S.cinnerCompl_cSmul_right, RCscale_RCscale]

private theorem reciprocal_square (delta : Q') (hdelta : (0 : Q') < delta) :
    (Q'.recipPos delta hdelta * Q'.recipPos delta hdelta) *
      (delta*delta) ≈ 1 := by
  let q := Q'.recipPos delta hdelta
  have hq : q*delta ≈ 1 :=
    Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv q delta)
      (Q'.mul_recipPos_eqv delta hdelta)
  have hfactor : (q*q)*(delta*delta) ≈ (q*delta)*(q*delta) :=
    poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1)))
      (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1)))
      (by decide) (fun | 0 => q | _ => delta)
  exact Q'.eqv_trans _ _ _ hfactor
    (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right (q*delta) 1 (q*delta) hq)
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left 1 (q*delta) 1 hq)
        (Q'.one_mul_eqv 1)))

private theorem reciprocal_scaled_error (delta : Q') (hdelta : (0 : Q') < delta)
    (x r : GNSCompletionSpace D)
    (hx : RCle (normSq x) (RCscale (delta*delta) (normSq r))) :
    RCle (normSq (S.cSmul (Q'.recipPos delta hdelta) x)) (normSq r) := by
  let q := Q'.recipPos delta hdelta
  rw [norm_smul]
  have hq : (0 : Q') ≤ q*q :=
    Q'.mul_nonneg _ _ (Q'.le_of_lt (Q'.recipPos_pos delta hdelta))
      (Q'.le_of_lt (Q'.recipPos_pos delta hdelta))
  have h := RCscale_mono hq hx
  rw [RCscale_RCscale,
    RCSignedPairBudget.scale_congr (reciprocal_square delta hdelta)] at h
  rw [RCscale_one] at h
  exact h

private theorem reciprocal_pair (delta : Q') (hdelta : (0 : Q') < delta)
    (x y : GNSCompletionSpace D) :
    RCscale delta ((D).cinnerCompl (S.cSmul (Q'.recipPos delta hdelta) x) y) =
      (D).cinnerCompl x y := by
  rw [S.cinnerCompl_cSmul_left, RCscale_RCscale]
  have h : delta * Q'.recipPos delta hdelta ≈ 1 :=
    Q'.mul_recipPos_eqv delta hdelta
  rw [RCSignedPairBudget.scale_congr h, RCscale_one]

/-- A first-order signed pairing error costs half a delta at each endpoint. -/
theorem relative_pairing_error (delta : Q') (hdelta : (0 : Q') < delta)
    (e r s : GNSCompletionSpace D)
    (he : RCle (normSq e) (RCscale (delta*delta) (normSq r))) :
    RCle ((D).cinnerCompl e s)
      (RCscale (HalfPow.half*delta) (RCadd (normSq r) (normSq s))) ∧
    RCle (RCneg ((D).cinnerCompl e s))
      (RCscale (HalfPow.half*delta) (RCadd (normSq r) (normSq s))) := by
  let q := Q'.recipPos delta hdelta
  have hpair := pairing_young S (S.cSmul q e) s (normSq r) (normSq s)
    (reciprocal_scaled_error S delta hdelta e r he) (RCle_refl _)
  have hpos : (0 : Q') ≤ delta := Q'.le_of_lt hdelta
  constructor
  · have h := RCscale_mono hpos hpair.1
    rw [reciprocal_pair S delta hdelta, RCscale_RCscale] at h
    rw [RCSignedPairBudget.scale_congr
      (Q'.mul_comm_eqv delta HalfPow.half)] at h
    exact h
  · have h := RCscale_mono hpos hpair.2
    rw [rc_scale_neg, reciprocal_pair S delta hdelta, RCscale_RCscale] at h
    rw [RCSignedPairBudget.scale_congr
      (Q'.mul_comm_eqv delta HalfPow.half)] at h
    exact h

/-- A product of two relative errors costs a half delta squared per endpoint. -/
theorem relative_error_pair (delta : Q') (_hdelta : (0 : Q') < delta)
    (e f r s : GNSCompletionSpace D)
    (he : RCle (normSq e) (RCscale (delta*delta) (normSq r)))
    (hf : RCle (normSq f) (RCscale (delta*delta) (normSq s))) :
    RCle ((D).cinnerCompl e f)
      (RCscale (HalfPow.half*(delta*delta))
        (RCadd (normSq r) (normSq s))) ∧
    RCle (RCneg ((D).cinnerCompl e f))
      (RCscale (HalfPow.half*(delta*delta))
        (RCadd (normSq r) (normSq s))) := by
  have hpair := pairing_young S e f
    (RCscale (delta*delta) (normSq r))
    (RCscale (delta*delta) (normSq s)) he hf
  have hscale : RCscale HalfPow.half
      (RCadd (RCscale (delta*delta) (normSq r))
        (RCscale (delta*delta) (normSq s))) =
      RCscale (HalfPow.half*(delta*delta))
        (RCadd (normSq r) (normSq s)) := by
    rw [← RCscale_RCadd, RCscale_RCscale]
  exact ⟨hscale ▸ hpair.1, hscale ▸ hpair.2⟩

private theorem pair_difference_scalar (a b c d : RC) :
    RCsub a d =
      RCsub (RCadd (RCsub a b) (RCsub a c))
        (RCsub (RCsub a c) (RCsub b d)) := by
  refine Quotient.inductionOn₃ a b c ?_
  intro A B C
  refine Quotient.inductionOn d ?_
  intro E
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.add (.var 0) (.neg (.var 3)))
      (.add
        (.add (.add (.var 0) (.neg (.var 1)))
          (.add (.var 0) (.neg (.var 2))))
        (.neg (.add (.add (.var 0) (.neg (.var 2)))
          (.neg (.add (.var 1) (.neg (.var 3)))))))
      (by decide)
      (fun | 0 => A.approx n | 1 => B.approx n
           | 2 => C.approx n | _ => E.approx n)))

private theorem pair_difference (r s t u : GNSCompletionSpace D) :
    RCsub ((D).cinnerCompl r s) ((D).cinnerCompl t u) =
      RCsub
        (RCadd ((D).cinnerCompl ((D).cSub r t) s)
          ((D).cinnerCompl r ((D).cSub s u)))
        ((D).cinnerCompl ((D).cSub r t) ((D).cSub s u)) := by
  have hright (a b c : GNSCompletionSpace D) :
      (D).cinnerCompl a ((D).cSub b c) =
        RCsub ((D).cinnerCompl a b) ((D).cinnerCompl a c) := by
    rw [(D).cinnerCompl_comm a ((D).cSub b c), (D).cinnerCompl_cSub_left,
      (D).cinnerCompl_comm b a, (D).cinnerCompl_comm c a]
  have hlast : (D).cinnerCompl ((D).cSub r t) ((D).cSub s u) =
      RCsub (RCsub ((D).cinnerCompl r s) ((D).cinnerCompl r u))
        (RCsub ((D).cinnerCompl t s) ((D).cinnerCompl t u)) := by
    rw [(D).cinnerCompl_cSub_left, hright, hright]
  rw [(D).cinnerCompl_cSub_left, hright r s u, hlast]
  exact pair_difference_scalar _ _ _ _

private theorem signed_three_budget (a b c E : RC) (p q : Q')
    (ha : RCle a (RCscale p E))
    (ha' : RCle (RCneg a) (RCscale p E))
    (hb : RCle b (RCscale p E))
    (hb' : RCle (RCneg b) (RCscale p E))
    (hc : RCle c (RCscale q E))
    (hc' : RCle (RCneg c) (RCscale q E)) :
    RCle (RCsub (RCadd a b) c) (RCscale (p+p+q) E) ∧
    RCle (RCneg (RCsub (RCadd a b) c)) (RCscale (p+p+q) E) := by
  have hsum : RCadd (RCadd (RCscale p E) (RCscale p E)) (RCscale q E) =
      RCscale (p+p+q) E := by
    refine Quotient.inductionOn E ?_
    intro X
    exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
      poly_identity_of_normal_eq
        (.add (.add (.mul (.var 0) (.var 2)) (.mul (.var 0) (.var 2)))
          (.mul (.var 1) (.var 2)))
        (.mul (.add (.add (.var 0) (.var 0)) (.var 1)) (.var 2))
        (by decide) (fun | 0 => p | 1 => q | _ => X.approx n)))
  constructor
  · have h := RCadd_le_add (RCadd_le_add ha hb) hc'
    change RCle (RCsub (RCadd a b) c)
      (RCadd (RCadd (RCscale p E) (RCscale p E)) (RCscale q E)) at h
    rwa [hsum] at h
  · have h := RCadd_le_add (RCadd_le_add ha' hb') hc
    have hneg : RCneg (RCsub (RCadd a b) c) =
        RCadd (RCadd (RCneg a) (RCneg b)) c := by
      refine Quotient.inductionOn₃ a b c ?_
      intro A B C
      exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
        poly_identity_of_normal_eq
          (.neg (.add (.add (.var 0) (.var 1)) (.neg (.var 2))))
          (.add (.add (.neg (.var 0)) (.neg (.var 1))) (.var 2))
          (by decide)
          (fun | 0 => A.approx n | 1 => B.approx n | _ => C.approx n)))
    rw [hneg]
    rwa [hsum] at h

/-- Both signed order errors for one completed Gram entry.  The same
reference endpoint energies control each polynomial approximation error. -/
theorem pair_error_bounds (delta : Q') (hdelta : (0 : Q') < delta)
    (r s t u : GNSCompletionSpace D)
    (hr : RCle (normSq ((D).cSub r t))
      (RCscale (delta*delta) (normSq r)))
    (hs : RCle (normSq ((D).cSub s u))
      (RCscale (delta*delta) (normSq s))) :
    RCle (RCsub ((D).cinnerCompl r s) ((D).cinnerCompl t u))
      (RCscale (pairErrorCoefficient delta)
        (RCadd (normSq r) (normSq s))) ∧
    RCle (RCneg (RCsub ((D).cinnerCompl r s) ((D).cinnerCompl t u)))
      (RCscale (pairErrorCoefficient delta)
        (RCadd (normSq r) (normSq s))) := by
  let e := (D).cSub r t
  let f := (D).cSub s u
  let E := RCadd (normSq r) (normSq s)
  have ha := relative_pairing_error S delta hdelta e r s hr
  have hb0 := relative_pairing_error S delta hdelta f s r hs
  have hb : RCle ((D).cinnerCompl r f) (RCscale (HalfPow.half*delta) E) ∧
      RCle (RCneg ((D).cinnerCompl r f)) (RCscale (HalfPow.half*delta) E) := by
    rw [(D).cinnerCompl_comm r f]
    have hcomm : RCadd (normSq s) (normSq r) = E := by
      change RCadd (normSq s) (normSq r) =
        RCadd (normSq r) (normSq s)
      refine Quotient.inductionOn₂ (normSq r) (normSq s) ?_
      intro R T
      exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
        (fun n => Q'.add_comm_eqv (T.approx n) (R.approx n)))
    rw [hcomm] at hb0
    exact hb0
  have hc := relative_error_pair S delta hdelta e f r s hr hs
  rw [pair_difference S r s t u]
  have h := signed_three_budget ((D).cinnerCompl e s) ((D).cinnerCompl r f)
    ((D).cinnerCompl e f) E (HalfPow.half*delta)
    (HalfPow.half*(delta*delta)) ha.1 ha.2 hb.1 hb.2 hc.1 hc.2
  have hcoeff : (HalfPow.half*delta)+(HalfPow.half*delta)+
      HalfPow.half*(delta*delta) ≈ pairErrorCoefficient delta := by
    unfold pairErrorCoefficient
    exact Q'.add_eqv_congr_right _ _ _ (ExpNeg.two_halves delta)
  rw [RCSignedPairBudget.scale_congr hcoeff] at h
  exact h

#print axioms pairErrorCoefficient
#print axioms pairErrorCoefficient_nonnegative
#print axioms pairing_young
#print axioms relative_pairing_error
#print axioms relative_error_pair
#print axioms pair_error_bounds

end YMGap.Continuum.GNSPairApproximationError
