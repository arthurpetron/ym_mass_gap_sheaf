/-
# Conditional squared covariance bound for the original finite action

The existing finite covariance, its own partition reciprocal, and both
original diagonal variances are compared through completed Cauchy--Schwarz.
The only dynamical hypothesis is reverse energy at the actual Chebyshev
auxiliary vector.  This does not produce that estimate, a strict gap, or a
scaling-uniform rate.
-/

import YMGap.Continuum.BF4ExactSlabChebyshevCovariance
import YMGap.Continuum.BF4ExactSlabChebyshevRescale
import YMGap.Continuum.RCCauchySchwarz

namespace YMGap.Continuum.BF4ExactSlabChebyshevCovarianceBound

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
open YMGap.Continuum.BF4ExactSlabConditionalSweep
open YMGap.Continuum.BF4ExactSlabConditionalCovariance
open YMGap.Continuum.BF4ExactSlabSweepChebyshev
open YMGap.Continuum.BF4ExactSlabChebyshevPairing
open YMGap.Continuum.BF4ExactSlabChebyshevCovariance
open YMGap.Continuum.BF4ExactSlabChebyshevRescale
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

private theorem scale_variance_reorder (r s : Q') (a b : RC) :
    RCscale (r*r)
      (RCmul (RCscale s (RCscale s a)) b) =
    RCscale (s*s) (RCmul (RCscale r a) (RCscale r b)) := by
  refine Quotient.inductionOn₂ a b ?_
  intro A B
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n => by
    change ((r*r) * (((s*(s*A.approx n)) * B.approx n))).eqv
      ((s*s) * ((r*A.approx n) * (r*B.approx n)))
    exact poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.var 0))
        (.mul (.mul (.var 1) (.mul (.var 1) (.var 2))) (.var 3)))
      (.mul (.mul (.var 1) (.var 1))
        (.mul (.mul (.var 0) (.var 2)) (.mul (.var 0) (.var 3))))
      (by decide)
      (fun | 0 => r | 1 => s | 2 => A.approx n | _ => B.approx n)))

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (extent stage : Nat)

local notation "K" => headCutoff w + stage
local notation "hK" => Nat.le_add_right (headCutoff w) stage
local notation "F" => fullData hw0 hw1 K extent hK
local notation "P" => projections hw0 hw1 K extent hK
local notation "B" => Family.balanced (P) (schedule extent)
local notation "W" => Family.sweep (P) (schedule extent)
local notation "r" => inversePartition hw0 hw1 extent stage
local notation "ids" => slabPhysicalFaceEdges extent
local notation "physical" => (fun (id : Nat) (h : id ∈ ids) => h)

private theorem inversePartition_nonnegative : (0 : Q') ≤ r := by
  have hp : (0 : Q') < r := by
    unfold inversePartition BF4ExactSlabAllNomeFaceSetReciprocal.reciprocalTerm
    exact Q'.recipPos_pos _ _
  exact Q'.le_of_lt hp

/-- The squared SAME finite normalized covariance is controlled by its
original diagonal finite variances, conditional only on the displayed
auxiliary-vector reverse-energy inequality. -/
theorem finiteCovariance_sq_bound (c : Q') (hc : (0 : Q') ≤ c) (n : Nat)
    (ht : (0 : Q') < Cheb.T n (c + (-(1 : Q'))))
    (support testSupport : List Z4Link) (p q : (F).V)
    (hp : LinkLocal extent support p.val)
    (hq : LinkLocal extent testSupport q.val)
    (hsep : LinksDisjoint (grow extent (16*n) support) testSupport)
    (hrev : let x := embedV F (centered hw0 hw1 extent stage p)
      let u := (coupled hw0 hw1 K extent hK c x n).2
      RCle (RCscale c (normSq (B u))) (RCscale 2 (normSq (W u)))) :
    RCle
      (RCmul
        (rat (finiteCovariance w hw0 hw1 extent ids physical p.val q.val stage))
        (rat (finiteCovariance w hw0 hw1 extent ids physical p.val q.val stage)))
      (RCscale
        ((Q'.recipPos (Cheb.T n (c + (-(1 : Q')))) ht) *
          (Q'.recipPos (Cheb.T n (c + (-(1 : Q')))) ht))
        (RCmul
          (rat (finiteCovariance w hw0 hw1 extent ids physical p.val p.val stage))
          (rat (finiteCovariance w hw0 hw1 extent ids physical q.val q.val stage)))) := by
  let x := embedV F (centered hw0 hw1 extent stage p)
  let y := embedV F (centered hw0 hw1 extent stage q)
  let s := Q'.recipPos (Cheb.T n (c + (-(1 : Q')))) ht
  let z := normalizedFirst hw0 hw1 K extent hK c n ht x
  have hcs := (F).RC_cauchy_schwarz z y
  have hnorm := normalizedFirst_norm_from_reverse_energy
    hw0 hw1 K extent hK c hc x n ht hrev
  have hy : RCnonneg (normSq y) := (F).cinner_self_nonneg y
  have hm := RCmul_mono_nonneg_left hy hnorm
  rw [RCmul_comm (normSq y) (normSq z),
    RCmul_comm (normSq y) (RCscale s (RCscale s (normSq x)))] at hm
  have hpair : RCle
      (RCmul ((F).cinnerCompl z y) ((F).cinnerCompl z y))
      (RCmul (RCscale s (RCscale s (normSq x))) (normSq y)) :=
    RCle_trans hcs hm
  have hr : (0 : Q') ≤ r := inversePartition_nonnegative hw0 hw1 extent stage
  have hrr : (0 : Q') ≤ r*r := Q'.mul_nonneg _ _ hr hr
  have hscaled := RCscale_mono hrr hpair
  rw [← scale_square r ((F).cinnerCompl z y),
    scale_variance_reorder r s (normSq x) (normSq y)] at hscaled
  have hcov := covariance_as_chebyshev_pairing hw0 hw1 extent stage
    c n ht support testSupport p q hp hq hsep
  have hpdiag := completed_covariance hw0 hw1 extent stage p p
  have hqdiag := completed_covariance hw0 hw1 extent stage q q
  dsimp only [x, y, z, normSq] at hscaled
  rw [← hcov, ← hpdiag, ← hqdiag] at hscaled
  exact hscaled

#print axioms finiteCovariance_sq_bound

end YMGap.Continuum.BF4ExactSlabChebyshevCovarianceBound
