/-
# From complement coercivity to a completed square-generator bound

This is a generic same-carrier Hilbert-form implication. An exact pairing
with a supplied complement vector and a lower energy bound imply a square
bound by completed Young and rational scalar cancellation. No spectral
theorem, inverse, or asserted Yang--Mills coercivity enters here.
-/

import YMGap.Continuum.GNSPairApproximationError

namespace YMGap.Continuum.GNSProjectionKernelCoercivity

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.GNSProjectionSweep
open YMGap.Continuum.HamiltonianScalar
open YMGap.Continuum.RingNormaliser

local infix:50 " ≈ " => Q'.eqv

private theorem double_sub_self (a : RC) :
    RCsub (RCscale 2 a) a = a := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.add (.mul (.const 2) (.var 0)) (.neg (.var 0)))
      (.var 0) (by decide) (fun _ => A.approx n)))

private theorem add_sub_cancel (a b : RC) :
    RCsub (RCadd a b) b = a := by
  refine Quotient.inductionOn₂ a b ?_
  intro A B
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.add (.add (.var 0) (.var 1)) (.neg (.var 1)))
      (.var 0) (by decide)
      (fun | 0 => A.approx n | _ => B.approx n)))

/-- Scalar cancellation of a coercive square: if 2a≤b+c and c≤a,
then a≤b. This does not divide by a possibly zero energy. -/
private theorem le_of_double_le_add {a b c : RC}
    (hdouble : RCle (RCscale 2 a) (RCadd b c))
    (hcap : RCle c a) : RCle a b := by
  have hleft := RCadd_le_add (RCle_refl (RCscale 2 a))
    (RCSignedPairBudget.neg_mono hcap)
  change RCle (RCsub (RCscale 2 a) a)
    (RCsub (RCscale 2 a) c) at hleft
  rw [double_sub_self] at hleft
  have hright := RCadd_le_add hdouble (RCle_refl (RCneg c))
  change RCle (RCsub (RCscale 2 a) c)
    (RCsub (RCadd b c) c) at hright
  rw [add_sub_cancel] at hright
  exact RCle_trans hleft hright

private theorem norm_smul (S : SmulGNSData) (q : Q')
    (x : GNSCompletionSpace S.toGNSData) :
    normSq (S.cSmul q x) = RCscale (q*q) (normSq x) := by
  unfold normSq
  rw [S.cinnerCompl_cSmul_left, S.cinnerCompl_cSmul_right, RCscale_RCscale]

private theorem double_half (a : RC) :
    RCscale 2 (RCscale HalfPow.half a) = a := by
  rw [RCscale_RCscale,
    RCSignedPairBudget.scale_congr (by decide : (2 : Q') * HalfPow.half ≈ 1) a,
    RCscale_one]

/-- A coercive complement pairing supplies the generator square bound on
the SAME completed GNS carrier. The supplied lower bound is genuine input;
the theorem itself asserts no positive margin for an arbitrary projection. -/
theorem square_lower_of_coercive_pair (S : SmulGNSData)
    (gamma : Q') (hgamma : (0 : Q') ≤ gamma)
    (v y : GNSCompletionSpace S.toGNSData) (E : RC)
    (hpair : (S.toGNSData).cinnerCompl v y = E)
    (hcoerc : RCle (RCscale gamma (normSq y)) E) :
    RCle (RCscale gamma E) (normSq v) := by
  let D := S.toGNSData
  have hnorm := norm_smul S gamma y
  have hyoung := (GNSPairApproximationError.pairing_young S v
    (S.cSmul gamma y) (normSq v) (normSq (S.cSmul gamma y))
    (RCle_refl _) (RCle_refl _)).1
  rw [S.cinnerCompl_cSmul_right, hpair, hnorm] at hyoung
  have htwice := RCscale_mono (by decide : (0 : Q') ≤ 2) hyoung
  rw [double_half] at htwice
  have hcap := RCscale_mono hgamma hcoerc
  rw [RCscale_RCscale] at hcap
  exact le_of_double_le_add htwice hcap

#print axioms square_lower_of_coercive_pair

end YMGap.Continuum.GNSProjectionKernelCoercivity
