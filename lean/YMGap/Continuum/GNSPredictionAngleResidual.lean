/-
# A sharp signed residual bound from the prediction covariance at ONE state

The positive square is retained until the exact scalar combination is made.
For y,u,v with <y,u>=||u||^2 and <y,v>=||v||^2, set
z=(1+rho)y-u-v. Then

  2(1+rho)<y-u,y-v> + rho(1+rho)(||y-u||^2+||y-v||^2)
    = 2||z||^2 + (1-rho)(rho(||u||^2+||v||^2)-2<u,v>).

Thus a one-sided prediction covariance bound with 0<=rho<=1 gives a
residual lower bound with coefficient rho/2, without a 1/(1-rho) loss.
Only this state's bound is needed; no global range-angle premise is used.
This algebra does not produce a useful original-action covariance bound.
-/

import YMGap.Continuum.GNSProjectionPredictionCovariance
import YMGap.Continuum.ContinuousFunctionalCalculusForm
import YMGap.Continuum.RCPredictionAngleBudget

namespace YMGap.Continuum.GNSPredictionAngleResidual

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.GNSProjectionSweep
open YMGap.Continuum.HamiltonianScalar
open YMGap.Continuum.RingNormaliser

private def crossExpansion (Y U V C : RC) : RC :=
  RCsub (RCsub Y V) (RCsub U C)

private def squareExpansion (rho : Q') (Y U V C : RC) : RC :=
  RCsub
    (RCsub (RCscale (1+rho) (RCscale (1+rho) Y))
      (RCscale (1+rho) (RCadd U V)))
    (RCsub (RCscale (1+rho) (RCadd U V))
      (RCadd (RCadd U C) (RCadd C V)))

private theorem scalar_identity (rho : Q') (Y U V C : RC) :
    RCadd (RCscale (2*(1+rho)) (crossExpansion Y U V C))
      (RCscale (rho*(1+rho)) (RCadd (RCsub Y U) (RCsub Y V))) =
    RCadd (RCscale 2 (squareExpansion rho Y U V C))
      (RCscale (1 + (-rho)) (RCsub (RCscale rho (RCadd U V)) (RCscale 2 C))) := by
  refine Quotient.inductionOn₃ Y U V ?_
  intro y u v
  refine Quotient.inductionOn C ?_
  intro c
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.add
        (.mul (.mul (.const 2) (.add (.const 1) (.var 0)))
          (.add (.add (.var 1) (.neg (.var 3)))
            (.neg (.add (.var 2) (.neg (.var 4))))))
        (.mul (.mul (.var 0) (.add (.const 1) (.var 0)))
          (.add (.add (.var 1) (.neg (.var 2)))
            (.add (.var 1) (.neg (.var 3))))))
      (.add
        (.mul (.const 2)
          (.add
            (.add (.mul (.add (.const 1) (.var 0))
                (.mul (.add (.const 1) (.var 0)) (.var 1)))
              (.neg (.mul (.add (.const 1) (.var 0)) (.add (.var 2) (.var 3)))))
            (.neg (.add (.mul (.add (.const 1) (.var 0)) (.add (.var 2) (.var 3)))
              (.neg (.add (.add (.var 2) (.var 4)) (.add (.var 4) (.var 3))))))))
        (.mul (.add (.const 1) (.neg (.var 0)))
          (.add (.mul (.var 0) (.add (.var 2) (.var 3)))
            (.neg (.mul (.const 2) (.var 4))))))
      (by decide)
      (fun | 0 => rho | 1 => y.approx n | 2 => u.approx n
           | 3 => v.approx n | _ => c.approx n)))

variable (S : SmulGNSData)
local notation "D" => S.toGNSData

private theorem inner_sub_right (x y z : GNSCompletionSpace D) :
    (D).cinnerCompl x ((D).cSub y z) =
      RCsub ((D).cinnerCompl x y) ((D).cinnerCompl x z) := by
  rw [(D).cinnerCompl_comm x, (D).cinnerCompl_cSub_left,
    (D).cinnerCompl_comm y, (D).cinnerCompl_comm z]

private theorem norm_sub (x y : GNSCompletionSpace D) :
    normSq ((D).cSub x y) =
      RCsub (RCsub (normSq x) ((D).cinnerCompl x y))
        (RCsub ((D).cinnerCompl x y) (normSq y)) := by
  unfold normSq
  rw [(D).cinnerCompl_cSub_left, inner_sub_right, inner_sub_right,
    (D).cinnerCompl_comm y x]

/-- The square identity is unconditional in rho and uses only the two
orthogonality identities at the supplied vectors. -/
theorem weighted_square_identity (rho : Q') (y u v : GNSCompletionSpace D)
    (hu : (D).cinnerCompl y u = normSq u)
    (hv : (D).cinnerCompl y v = normSq v) :
    RCadd (RCscale (2*(1+rho)) ((D).cinnerCompl ((D).cSub y u) ((D).cSub y v)))
      (RCscale (rho*(1+rho)) (RCadd (normSq ((D).cSub y u)) (normSq ((D).cSub y v)))) =
    RCadd (RCscale 2 (normSq ((D).cSub (S.cSmul (1+rho) y) ((D).cAdd u v))))
      (RCscale (1 + (-rho))
        (RCsub (RCscale rho (RCadd (normSq u) (normSq v)))
          (RCscale 2 ((D).cinnerCompl u v)))) := by
  have hyu : (D).cinnerCompl u u = (D).cinnerCompl u y := by
    rw [(D).cinnerCompl_comm u y, hu]
    rfl
  have hyv : (D).cinnerCompl v v = (D).cinnerCompl v y := by
    rw [(D).cinnerCompl_comm v y, hv]
    rfl
  have hcross : (D).cinnerCompl ((D).cSub y u) ((D).cSub y v) =
      crossExpansion (normSq y) (normSq u) (normSq v) ((D).cinnerCompl u v) := by
    rw [(D).cinnerCompl_cSub_left, inner_sub_right, inner_sub_right,
      (D).cinnerCompl_comm u y, hu, hv]
    rfl
  have hsum : (D).cinnerCompl y ((D).cAdd u v) = RCadd (normSq u) (normSq v) := by
    rw [(D).cinnerCompl_cAdd_right, hu, hv]
  have hsumSq : normSq ((D).cAdd u v) =
      RCadd (RCadd (normSq u) ((D).cinnerCompl u v))
        (RCadd ((D).cinnerCompl u v) (normSq v)) := by
    unfold normSq
    rw [(D).cinnerCompl_cAdd_left, (D).cinnerCompl_cAdd_right,
      (D).cinnerCompl_cAdd_right, (D).cinnerCompl_comm v u]
  have hsq : normSq ((D).cSub (S.cSmul (1+rho) y) ((D).cAdd u v)) =
      squareExpansion rho (normSq y) (normSq u) (normSq v) ((D).cinnerCompl u v) := by
    rw [norm_sub]
    change RCsub (RCsub ((D).cinnerCompl (S.cSmul (1+rho) y) (S.cSmul (1+rho) y)) _)
      (RCsub _ (normSq ((D).cAdd u v))) = _
    rw [S.cinnerCompl_cSmul_left, S.cinnerCompl_cSmul_right,
      S.cinnerCompl_cSmul_left, hsum, hsumSq]
    rfl
  have hnu : normSq ((D).cSub y u) = RCsub (normSq y) (normSq u) :=
    GNSPairingNormBound.residual_norm_identity D u y hyu
  have hnv : normSq ((D).cSub y v) = RCsub (normSq y) (normSq v) :=
    GNSPairingNormBound.residual_norm_identity D v y hyv
  rw [hcross, hnu, hnv, hsq]
  exact scalar_identity rho _ _ _ _

/-- A one-sided prediction bound at this state suffices. No absolute
covariance, all-state angle, inverse or spectral theorem is assumed. -/
theorem residual_lower (rho : Q') (hrho0 : (0 : Q') ≤ rho) (hrho1 : rho ≤ 1)
    (y u v : GNSCompletionSpace D)
    (hu : (D).cinnerCompl y u = normSq u)
    (hv : (D).cinnerCompl y v = normSq v)
    (hcov : RCle (RCscale 2 ((D).cinnerCompl u v))
      (RCscale rho (RCadd (normSq u) (normSq v)))) :
    RCle (RCneg (RCscale (HalfPow.half*rho)
      (RCadd (normSq ((D).cSub y u)) (normSq ((D).cSub y v)))))
      ((D).cinnerCompl ((D).cSub y u) ((D).cSub y v)) :=
  RCPredictionAngleBudget.residual_lower rho hrho0 hrho1 _ _ _ _ _
    ((D).cinner_self_nonneg _) hcov (weighted_square_identity S rho y u v hu hv)

private theorem sub_sub_common (x u c : GNSCompletionSpace D) :
    (D).cSub ((D).cSub x c) ((D).cSub u c) = (D).cSub x u := by
  apply GNSDenseCompletionLaws.eq_of_pairings_equal
  intro z
  simp only [(D).cinnerCompl_cSub_left]
  generalize (D).cinnerCompl x z = A, (D).cinnerCompl u z = B,
    (D).cinnerCompl c z = C
  refine Quotient.inductionOn₃ A B C ?_
  intro a b c
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.add (.add (.var 0) (.neg (.var 2)))
        (.neg (.add (.var 1) (.neg (.var 2)))))
      (.add (.var 0) (.neg (.var 1))) (by decide)
      (fun | 0 => a.approx n | 1 => b.approx n | _ => c.approx n)))

variable {Index : Type} (P : Family S.toGNSData Index)

theorem centered_projection_self_pairing (i k : Index)
    (hki : ∀ z, P.op k (P.op i z) = P.op k z) (x : GNSCompletionSpace D) :
    (D).cinnerCompl (P.residual k x) ((D).cSub (P.op i x) (P.op k x)) =
      normSq ((D).cSub (P.op i x) (P.op k x)) := by
  have hp := P.residual_pairing_covariance k x (P.op i x)
  have hn := P.single_loss k (P.op i x)
  unfold Family.residual at hp hn ⊢
  rw [hki] at hp hn
  rw [hp, hn, (D).cinnerCompl_comm x (P.op i x), ← P.self_pairing]
  rfl

/-- Sharp conversion for two actual projections and a common subprojection.
Only the displayed prediction covariance at x is an analytic input. -/
theorem projection_residual_lower (i j k : Index)
    (hki : ∀ z, P.op k (P.op i z) = P.op k z)
    (hkj : ∀ z, P.op k (P.op j z) = P.op k z)
    (rho : Q') (hrho0 : (0 : Q') ≤ rho) (hrho1 : rho ≤ 1)
    (x : GNSCompletionSpace D)
    (hcov : RCle
      (RCscale 2 ((D).cinnerCompl ((D).cSub (P.op i x) (P.op k x))
        ((D).cSub (P.op j x) (P.op k x))))
      (RCscale rho (RCadd (normSq ((D).cSub (P.op i x) (P.op k x)))
        (normSq ((D).cSub (P.op j x) (P.op k x)))))) :
    RCle (RCneg (RCscale (HalfPow.half*rho)
      (RCadd (normSq (P.residual i x)) (normSq (P.residual j x)))))
      ((D).cinnerCompl (P.residual i x) (P.residual j x)) := by
  have h := residual_lower S rho hrho0 hrho1 (P.residual k x)
    ((D).cSub (P.op i x) (P.op k x)) ((D).cSub (P.op j x) (P.op k x))
    (centered_projection_self_pairing S P i k hki x)
    (centered_projection_self_pairing S P j k hkj x) hcov
  unfold Family.residual at h ⊢
  rwa [sub_sub_common, sub_sub_common] at h

#print axioms weighted_square_identity
#print axioms residual_lower
#print axioms centered_projection_self_pairing
#print axioms projection_residual_lower

end YMGap.Continuum.GNSPredictionAngleResidual
