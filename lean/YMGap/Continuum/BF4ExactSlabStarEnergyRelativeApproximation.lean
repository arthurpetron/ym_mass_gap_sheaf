/-
# Energy-relative approximation of the original conditional residual

The existing polynomial kernel tests have error at most q^(2n) times the
SAME residual energy, not merely the input norm. Subtracting a finite
exterior probe leaves the error unchanged. The constructed conditional
approximants then converge to the minimizing exterior prediction, giving
the sharper bound without a gap assumption or division by the energy.

The iteration count depends on nome and tolerance, not volume, late heat
cutoff, link, or input. This removes an additive state-norm error in local
residual certificates; it does not estimate the signed collective energy,
control omitted modes of a finite matrix, or prove a scaling/OS gap.
-/

import YMGap.Continuum.BF4ExactSlabStarVariationalApproximation
import YMGap.Continuum.EffMassConvergence
import YMGap.Continuum.GNSProjectionSignedEnergy

namespace YMGap.Continuum.BF4ExactSlabStarEnergyRelativeApproximation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.GNSDenseCompletionLaws
open YMGap.Continuum.GNSProjectionSweep
open YMGap.Continuum.GNSProjectionSweep.Family
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabStarInverseApproximation
open YMGap.Continuum.BF4ExactSlabStarFullActionProbe
open YMGap.Continuum.BF4ExactSlabStarConditionalProjection
open YMGap.Continuum.BF4ExactSlabConditionalSweep
open YMGap.Continuum.BF4ExactSlabStarPolynomialResidual
open YMGap.Continuum.BF4ExactSlabStarExteriorResidual
open YMGap.Continuum.BF4ExactSlabStarResidualApproximation
open YMGap.Continuum.BF4ExactSlabStarVariationalApproximation
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.SU2QuaternionHaarHeadProbeTransport

private def rat (q : Q') : RC := Quotient.mk crealSetoid (ofQ' q)

private theorem embed_pair (D : GNSData) (a b : D.V) :
    D.cinnerCompl (embedV D a) (embedV D b) = rat (D.B a b) :=
  D.cinnerCompl_embed a b

private theorem embed_congr (D : GNSData) {a b : D.V} (h : D.veq a b) :
    embedV D a = embedV D b := by
  apply eq_of_dense_pairings
  intro c
  rw [embed_pair, embed_pair]
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun _ => D.B_congr_left c h))

private theorem embed_sub (D : GNSData) (a b : D.V) :
    embedV D (D.sub a b) = D.cSub (embedV D a) (embedV D b) := by
  apply eq_of_dense_pairings
  intro c
  rw [D.cinnerCompl_cSub_left, embed_pair, embed_pair, embed_pair]
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun _ =>
    Q'.eqv_trans _ _ _ (D.B_add_left a (D.neg b) c)
      (Q'.add_eqv_congr_left _ _ _ (D.B_neg_left b c))))

private theorem cSub_zero (D : GNSData) (x : GNSCompletionSpace D) :
    D.cSub x (embedV D D.zero) = x := by
  apply eq_of_pairings_equal
  intro z
  rw [D.cinnerCompl_cSub_left, D.cinnerCompl_embedZero_left]
  generalize D.cinnerCompl x z = b
  refine Quotient.inductionOn b ?_
  intro B
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ (by decide : Q'.eqv (-0) 0))
      (Q'.eqv_of_eq (Q'.add_zero' (B.approx n)))))

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K extent : Nat) (hK : headCutoff w ≤ K) (i : PhysicalLink extent)

local notation "F" => fullData hw0 hw1 K extent hK
local notation "G" => exteriorData hw0 hw1 K extent hK i.val i.property
local notation "J" => probeMap hw0 hw1 K extent hK i.val i.property
local notation "M" => normalizerMap hw0 hw1 K extent hK i.val i.property
local notation "P" => projections hw0 hw1 K extent hK
local notation "E" => exteriorSeed hw0 hw1 K extent hK i
local notation "t" => polynomialResidual hw0 hw1 K extent hK i

private theorem exterior_sub_right (e : (G).V) (p q : (F).V) :
    embedV F (E e ((F).sub p q)) =
      (F).cSub (embedV F (E e p)) (embedV F (E e q)) := by
  apply Eq.trans (embed_congr F (b := (F).sub (E e p) (E e q)) ?_) (embed_sub F _ _)
  change RatPolyCoeffEqv
    (polyMul (J e).val (polyAdd p.val (polySmul (-1) q.val)))
    (polyAdd (polyMul (J e).val p.val) (polySmul (-1) (polyMul (J e).val q.val)))
  exact (RatPolyCoeffEqv.mul_add_right _ _ _).trans
    ((RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.polyMul_smul_right (-1) _ _))

private theorem exterior_product_residual_zero (e b : (G).V) :
    (P).residual i (embedV F (E e (J b))) = embedV F (F).zero := by
  let eb : (G).V := ⟨polyMul e.val b.val, supported_polyMul e.property b.property⟩
  have he : E e (J b) = J eb := by
    apply Subtype.ext
    exact (headProbe_mul _ e.val b.val).symm
  rw [he, ← probeCompletion_embed]
  have hf : (P).op i (probeCompletion hw0 hw1 K extent hK i.val i.property
      (embedV G eb)) = probeCompletion hw0 hw1 K extent hK i.val i.property
      (embedV G eb) := by
    change conditionalProjection hw0 hw1 K extent hK i.val i.property
      (probeCompletion hw0 hw1 K extent hK i.val i.property (embedV G eb)) = _
    exact conditionalProjection_fix_exterior hw0 hw1 K extent hK
      i.val i.property (embedV G eb)
  rw [← hf]
  exact (P).residual_after_own i _

/-- Subtracting any finite exterior prediction leaves the ACTUAL completed
approximation error exactly unchanged. -/
theorem residual_error_sub_probe (a b : (G).V) (p : (F).V) :
    (F).cSub ((P).residual i (embedV F ((F).sub p (J b))))
      (embedV F (t (E a ((F).sub p (J b))))) =
    (F).cSub ((P).residual i (embedV F p)) (embedV F (t (E a p))) := by
  rw [residual_error_identity, residual_error_identity,
    exterior_sub_right, (P).residual_sub, exterior_product_residual_zero, cSub_zero]

private theorem le_scale_distance_limit (D : GNSData) (X Y : CauchyGNS D)
    (r : Q') (a : RC)
    (h : ∀ n, RCle a (rat (r * D.distSqQ (X.seq n) (Y.seq n)))) :
    RCle a (RCscale r (normSq (D.cSub (Quotient.mk (cauchySetoid D) X)
      (Quotient.mk (cauchySetoid D) Y)))) := by
  revert h
  refine Quotient.inductionOn a ?_
  intro A h
  exact CReal.leEv_of_convergesTo_le (CReal.convergesTo_const A)
    (EffMassConvergence.convergesTo_scale r
      (CReal.convergesTo_ofQ'CauchySeq _ (D.distSqSeqCauchy X Y))) h

/-- The geometric squared-error prefactor is the SAME local residual
energy. No positivity of that energy or spectral-gap hypothesis is needed. -/
theorem residual_approximation_energy (p : (F).V) (n : Nat) :
    RCle (normSq ((F).cSub ((P).residual i (embedV F p))
      (embedV F (t (approximationSeed hw0 hw1 K extent hK i p n)))))
      (RCscale ((inverseRate w * inverseRate w)^n)
        (normSq ((P).residual i (embedV F p)))) := by
  let C := conditionalDenseMap hw0 hw1 K extent hK i.val i.property
  have h := le_scale_distance_limit F (constCauchy F p) (C.toRep p)
    ((inverseRate w * inverseRate w)^n)
    (normSq ((F).cSub ((P).residual i (embedV F p))
      (embedV F (t (approximationSeed hw0 hw1 K extent hK i p n))))) (fun k => ?_)
  · have hc : Quotient.mk (cauchySetoid F) (C.toRep p) = (P).op i (embedV F p) :=
      (conditionalProjection_embed hw0 hw1 K extent hK i.val i.property p).symm
    rw [hc] at h
    exact h
  · have hb := residual_approximation_norm hw0 hw1 K extent hK i
      ((F).sub p ((C.toRep p).seq k)) n
    change RCle
      (normSq ((F).cSub
        ((P).residual i (embedV F ((F).sub p (J _))))
        (embedV F (t (E _ ((F).sub p (J _))))))) _ at hb
    rw [residual_error_sub_probe] at hb
    exact hb

/-- The EXISTING explicit relative cutoff now gives an energy-relative
error, uniformly in volume, late heat cutoff, link and input at fixed nome. -/
theorem residual_energy_relative_error_le (p : (F).V) (epsilon : Q')
    (hepsilon : (0 : Q') < epsilon) (n : Nat)
    (hn : BF4ExactSlabStarResidualApproximation.relativeCutoff w epsilon ≤ n) :
    RCle (normSq ((F).cSub ((P).residual i (embedV F p))
      (embedV F (t (approximationSeed hw0 hw1 K extent hK i p n)))))
      (RCscale epsilon (normSq ((P).residual i (embedV F p)))) := by
  have hq := inverseRate_bounds hw0 hw1
  have hq2 : inverseRate w * inverseRate w < (1 : Q') :=
    Q'.lt_of_le_of_lt (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ _ (Q'.le_of_lt hq.2) hq.1)
      (Q'.le_of_eqv (Q'.one_mul_eqv _))) hq.2
  have hp : (inverseRate w * inverseRate w)^n ≤ epsilon :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.mul_one_eqv _))
      (PositiveContractionResidual.geometric_bound
        (Q'.mul_nonneg _ _ hq.1 hq.1) hq2 (by decide : (0 : Q') ≤ 1) hepsilon n hn)
  exact RCle_trans (residual_approximation_energy hw0 hw1 K extent hK i p n)
    (RCscale_scalar_mono hp ((F).cinner_self_nonneg _))

/-- The existing finite rational dual value brackets the SAME local energy
with relative, not additive state-norm, error. In particular no positive
floor for the residual is an input. -/
theorem residual_energy_relative_bracket (p : (F).V) (epsilon : Q')
    (hepsilon : (0 : Q') < epsilon) :
    RCle (rat (relativeValue hw0 hw1 K extent hK i p epsilon))
      (normSq ((P).residual i (embedV F p))) ∧
    RCle (normSq ((P).residual i (embedV F p)))
      (RCadd (rat (relativeValue hw0 hw1 K extent hK i p epsilon))
        (RCscale epsilon (normSq ((P).residual i (embedV F p))))) := by
  refine ⟨(residual_relative_bracket hw0 hw1 K extent hK i p epsilon hepsilon).1, ?_⟩
  have he := residual_dual_error_identity hw0 hw1 K extent hK i
    (approximationSeed hw0 hw1 K extent hK i p
      (BF4ExactSlabStarResidualApproximation.relativeCutoff w epsilon)) p
  have hb := residual_energy_relative_error_le hw0 hw1 K extent hK i p epsilon
    hepsilon _ (Nat.le_refl _)
  rw [he] at hb
  have hs := RCadd_le_add (RCle_refl
    (rat (relativeValue hw0 hw1 K extent hK i p epsilon))) hb
  have hadd (a b : RC) : RCadd b (RCsub a b) = a := by
    refine Quotient.inductionOn₂ a b ?_
    intro A B
    exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun k =>
      Q'.eqv_trans _ _ _ (Q'.add_comm_eqv _ _)
        (Q'.sub_add_cancel_eqv (A.approx k) (B.approx k))))
  change RCle (RCadd _ (RCsub _ (rat (relativeValue hw0 hw1 K extent hK i p epsilon)))) _ at hs
  rwa [hadd] at hs

/-- Sum of local squared approximation errors, with NO number-of-links
factor. This is not a bound on the squared norm of the SUM of error vectors. -/
theorem summed_residual_energy_relative_error_le (tests : List (PhysicalLink extent))
    (p : (F).V) (epsilon : Q') (hepsilon : (0 : Q') < epsilon) (n : Nat)
    (hn : BF4ExactSlabStarResidualApproximation.relativeCutoff w epsilon ≤ n) :
    RCle (sumOn tests (fun j => normSq ((F).cSub
      ((P).residual j (embedV F p))
      (embedV F (polynomialResidual hw0 hw1 K extent hK j
        (approximationSeed hw0 hw1 K extent hK j p n))))))
      (RCscale epsilon ((P).finalEnergy tests (embedV F p))) := by
  have h := sumOn_mono tests _ _ (fun j _ =>
    residual_energy_relative_error_le hw0 hw1 K extent hK j p epsilon hepsilon n hn)
  rw [sumOn_scale] at h
  exact h

#print axioms residual_error_sub_probe
#print axioms residual_approximation_energy
#print axioms residual_energy_relative_error_le
#print axioms residual_energy_relative_bracket
#print axioms summed_residual_energy_relative_error_le

end YMGap.Continuum.BF4ExactSlabStarEnergyRelativeApproximation
