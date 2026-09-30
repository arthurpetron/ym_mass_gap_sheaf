/-
# Original finite covariance from an explicit Chebyshev norm budget

The rational budget is checked on the actual centered source polynomial.
It need not assert a nonnegative reverse margin at each recurrence step.
The covariance, reciprocal partition, and both diagonal variances remain
those of the same original finite full action. No strict or scaling-uniform
budget is constructed by this implication.
-/

import YMGap.Continuum.BF4ExactSlabChebyshevNormBudget
import YMGap.Continuum.BF4ExactSlabChebyshevCovariance
import YMGap.Continuum.RCCauchySchwarz

namespace YMGap.Continuum.BF4ExactSlabChebyshevBudgetCovariance

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.GNSProjectionSweep
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabStarFullActionProbe
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabEightLayerCone
open YMGap.Continuum.BF4ExactSlabConditionalCovariance
open YMGap.Continuum.BF4ExactSlabChebyshevPairing
open YMGap.Continuum.BF4ExactSlabChebyshevCovariance
open YMGap.Continuum.BF4ExactSlabChebyshevNormBudget
open YMGap.Continuum.BF4ExactSlabConnectedFaceResponse (finiteCovariance)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

private def rat (q : Q') : RC := Quotient.mk crealSetoid (ofQ' q)

private theorem RCmul_mono_nonneg_left {factor a b : RC}
    (hf : RCnonneg factor) (hab : RCle a b) :
    RCle (RCmul factor a) (RCmul factor b) := by
  revert hf hab
  refine Quotient.inductionOn₃ factor a b ?_
  intro F A B hF hAB
  exact leEv_mul_nonneg_left hF hAB

private theorem scale_square (r : Q') (a : RC) :
    RCmul (RCscale r a) (RCscale r a) =
      RCscale (r*r) (RCmul a a) := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n => by
    change ((r * A.approx n) * (r * A.approx n)).eqv
      ((r*r) * (A.approx n * A.approx n))
    exact poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1)))
      (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1)))
      (by decide) (fun | 0 => r | _ => A.approx n)))

private theorem scale_variance_reorder (r eta : Q') (a b : RC) :
    RCscale (r*r) (RCmul (RCscale eta a) b) =
      RCscale eta (RCmul (RCscale r a) (RCscale r b)) := by
  refine Quotient.inductionOn₂ a b ?_
  intro A B
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n => by
    change ((r*r) * ((eta*A.approx n) * B.approx n)).eqv
      (eta * ((r*A.approx n) * (r*B.approx n)))
    exact poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.var 0))
        (.mul (.mul (.var 1) (.var 2)) (.var 3)))
      (.mul (.var 1)
        (.mul (.mul (.var 0) (.var 2)) (.mul (.var 0) (.var 3))))
      (by decide)
      (fun | 0 => r | 1 => eta | 2 => A.approx n | _ => B.approx n)))

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (extent stage : Nat)

local notation "K" => headCutoff w + stage
local notation "hK" => Nat.le_add_right (headCutoff w) stage
local notation "F" => fullData hw0 hw1 K extent hK
local notation "r" => inversePartition hw0 hw1 extent stage
local notation "ids" => slabPhysicalFaceEdges extent
local notation "physical" => (fun (id : Nat) (h : id ∈ ids) => h)

private theorem inversePartition_nonnegative : (0 : Q') ≤ r := by
  have hp : (0 : Q') < r := by
    unfold inversePartition BF4ExactSlabAllNomeFaceSetReciprocal.reciprocalTerm
    exact Q'.recipPos_pos _ _
  exact Q'.le_of_lt hp

/-- An explicit finite rational Chebyshev budget for the actual centered
source controls the squared SAME original finite covariance. No sign is
required of the intermediate reverse-energy margin. -/
theorem finiteCovariance_sq_bound_of_finite_budget (c : Q') (n : Nat)
    (ht : (0 : Q') < Cheb.T n (c + (-(1 : Q'))))
    (eta epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (support testSupport : List Z4Link) (p q : (F).V)
    (hp : LinkLocal extent support p.val)
    (hq : LinkLocal extent testSupport q.val)
    (hsep : LinksDisjoint (grow extent (16*n) support) testSupport)
    (htest : epsilon ≤ budgetValue hw0 hw1 K extent hK c
      (constCauchy F (centered hw0 hw1 extent stage p)) n eta epsilon) :
    RCle
      (RCmul
        (rat (finiteCovariance w hw0 hw1 extent ids physical p.val q.val stage))
        (rat (finiteCovariance w hw0 hw1 extent ids physical p.val q.val stage)))
      (RCscale eta
        (RCmul
          (rat (finiteCovariance w hw0 hw1 extent ids physical p.val p.val stage))
          (rat (finiteCovariance w hw0 hw1 extent ids physical q.val q.val stage)))) := by
  let x := embedV F (centered hw0 hw1 extent stage p)
  let y := embedV F (centered hw0 hw1 extent stage q)
  let z := normalizedFirst hw0 hw1 K extent hK c n ht x
  have hcs := (F).RC_cauchy_schwarz z y
  have hnorm := normalizedFirst_norm_of_finite_budget
    hw0 hw1 K extent hK c
    (constCauchy F (centered hw0 hw1 extent stage p)) n ht
    eta epsilon hepsilon htest
  change RCle (normSq z) (RCscale eta (normSq x)) at hnorm
  have hy : RCnonneg (normSq y) := (F).cinner_self_nonneg y
  have hm := RCmul_mono_nonneg_left hy hnorm
  rw [RCmul_comm (normSq y) (normSq z),
    RCmul_comm (normSq y) (RCscale eta (normSq x))] at hm
  have hpair : RCle
      (RCmul ((F).cinnerCompl z y) ((F).cinnerCompl z y))
      (RCmul (RCscale eta (normSq x)) (normSq y)) :=
    RCle_trans hcs hm
  have hr : (0 : Q') ≤ r := inversePartition_nonnegative hw0 hw1 extent stage
  have hrr : (0 : Q') ≤ r*r := Q'.mul_nonneg _ _ hr hr
  have hscaled := RCscale_mono hrr hpair
  rw [← scale_square r ((F).cinnerCompl z y),
    scale_variance_reorder r eta (normSq x) (normSq y)] at hscaled
  have hcov := covariance_as_chebyshev_pairing hw0 hw1 extent stage
    c n ht support testSupport p q hp hq hsep
  have hpdiag := completed_covariance hw0 hw1 extent stage p p
  have hqdiag := completed_covariance hw0 hw1 extent stage q q
  dsimp only [x, y, z, normSq] at hscaled
  rw [← hcov, ← hpdiag, ← hqdiag] at hscaled
  exact hscaled

#print axioms finiteCovariance_sq_bound_of_finite_budget

end YMGap.Continuum.BF4ExactSlabChebyshevBudgetCovariance
