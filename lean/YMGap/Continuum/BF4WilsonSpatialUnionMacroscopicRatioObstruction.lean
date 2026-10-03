/-
# A fixed-small-nome obstruction to a macroscopic response ratio

The EXISTING original Wilson spatial-union transfer has a strict squared
norm rate theta. Applying its norm decay to the actual smoothed vector,
rather than to the initial vector, gives a relative even-response bound.
At the computed cutoff, a positive macroscopic lower ratio forces that
smoothed vector to be zero. This applies to every centered vector, including
any scalar renormalization on this SAME carrier.

The positive rational margin is cancelled constructively. No one-step
positivity, spectral theorem, inverse of an arbitrary real, or choice of
completion representatives is used. This is fixed-small-nome, fixed-spacing
original Wilson structure, NOT an all-nome or continuum counterexample.

The guarded-ceiling refinement also lets the nome, completed carrier and
vector vary arbitrarily: the onset depends only on one guarded ceiling W
and kappa. It needs NO initial norm bound, including for diverging scalar
renormalizations. It excludes a nonzero macroscopic response ratio below
W, not all responses or all weak-coupling families. No statement identifies
the entropy boundary with a physical critical point or proves w tends to one.
-/

import YMGap.Continuum.BF4WilsonSpatialUnionRelaxation
import YMGap.Continuum.BF4WilsonSpatialUnionPosdef
import YMGap.Continuum.BF4ExactSlabCouplingRateMonotonicity

namespace YMGap.Continuum.BF4WilsonSpatialUnionMacroscopicRatioObstruction

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4WilsonSpatialUnionSeminorm
open YMGap.Continuum.BF4WilsonSpatialUnionPairingData
open YMGap.Continuum.BF4WilsonSpatialUnionTimeForm
open YMGap.Continuum.BF4WilsonSpatialUnionPosdef
open YMGap.Continuum.BF4WilsonSpatialUnionRelaxation (norm_decay)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialDenseGap
  (twoStepRate twoStepRate_positive twoStepRate_lt_one)
open YMGap.Continuum.PositiveContractionResidual (geometricCutoff geometric_bound)
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval

private theorem positive_margin (kappa decay : Q')
    (hk : (0 : Q') < kappa) (hdecay : decay ≤ HalfPow.half*kappa) :
    (0 : Q') < kappa + -decay := by
  have hh := ExpNeg.half_mul_pos kappa hk
  have hs := Q'.sub_nonneg_of_le hdecay
  have hp : (0 : Q') <
      HalfPow.half*kappa + (HalfPow.half*kappa + -decay) :=
    Q'.pos_of_lt_of_le hh (Q'.add_le_self_of_nonneg _ _ hs)
  have he : Q'.eqv
      (HalfPow.half*kappa + (HalfPow.half*kappa + -decay))
      (kappa + -decay) :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.add_assoc_eqv _ _ _))
      (Q'.add_eqv_congr_right _ _ _ (ExpNeg.two_halves kappa))
  exact Q'.pos_of_lt_of_le hp (Q'.le_of_eqv he)

/-- Cancellation concerns a strictly positive RATIONAL margin, not the
possibly zero response. The actual inverse is not needed by the existing
constructive positive-factor cancellation theorem. -/
private theorem scalar_ratio_zero (kappa decay : Q')
    (hm : (0 : Q') < kappa + -decay) (v : RC) (hv : RCnonneg v)
    (h : RCle (RCscale kappa v) (RCscale decay v)) : v = RCzero := by
  revert hv h
  refine Quotient.inductionOn v ?_
  intro X hv h
  have hmargin : leEv (mul X (ofQ' (kappa + -decay)))
      (mul czero (ofQ' (kappa + -decay))) := by
    intro epsilon hepsilon
    obtain ⟨N, hN⟩ := h epsilon hepsilon
    refine ⟨N, fun n hn => ?_⟩
    have hs := Q'.sub_le_of_le_add (hN n hn)
    have he : Q'.eqv (X.approx n*(kappa + -decay))
        (kappa*X.approx n + -(decay*X.approx n)) :=
      RingNormaliser.poly_identity_of_normal_eq
        (.mul (.var 0) (.add (.var 1) (.neg (.var 2))))
        (.add (.mul (.var 1) (.var 0))
          (.neg (.mul (.var 2) (.var 0)))) (by decide)
        (fun
          | 0 => X.approx n
          | 1 => kappa
          | _ => decay)
    have hz : Q'.eqv ((0 : Q')*(kappa + -decay) + epsilon) epsilon :=
      Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ _ (Q'.zero_mul_eqv _))
        (Q'.eqv_of_eq (Q'.zero_add' epsilon))
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv he)
      (Q'.le_trans' _ _ _ hs (Q'.ge_of_eqv hz))
  have hzero : leEv X czero :=
    RCBilinearDifference.cancel_positive_factor (kappa + -decay) hm
      (fun _ => Q'.le_refl' _) hmargin
  exact Quotient.sound (equiv_of_leEv_leEv hzero hv)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)

local notation "V" => UnionCompletion hw0 hw1 hsmall hd hs
local notation "B" => completedInner hw0 hw1 hsmall hd hs
local notation "T" => completedTime hw0 hw1 hsmall hd hs
local notation "U" => completedUnit hw0 hw1 hsmall hd hs
local notation "Z" => completedZero hw0 hw1 hsmall hd hs
local notation "theta" => twoStepRate w hd

/-- Literal SAME completed original autocorrelation, with no normalization. -/
def response (x : V) (lag : Nat) : RC := B x (T lag x)

/-- The rate costs only the additional smoothing n, relative to the
actual response at 2*start. No positive floor for the initial norm is used. -/
theorem relative_even_response_bound (x : V) (hx : B x U = RCzero)
    (start n : Nat) :
    RCle (response hw0 hw1 hsmall hd hs x (2*(start+n)))
      (RCscale (theta^n) (response hw0 hw1 hsmall hd hs x (2*start))) := by
  have h := norm_decay hw0 hw1 hsmall hd hs (T start x)
    (completedTime_preserves_orthogonal hw0 hw1 hsmall hd hs start x hx) n
  rw [← completedTime_add, Nat.add_comm n start] at h
  simpa only [response, completedInner_even_diagonal] using h

/-- Computed threshold independent of the vector and of its normalization. -/
def ratioCutoff (kappa : Q') : Nat := geometricCutoff theta 1 (HalfPow.half*kappa)

include hw0 hw1 hs in
theorem rate_at_ratioCutoff (kappa : Q') (hk : (0 : Q') < kappa)
    (n : Nat) (hn : ratioCutoff hd kappa ≤ n) : theta^n ≤ HalfPow.half*kappa := by
  have h := geometric_bound (Q'.le_of_lt (twoStepRate_positive hw0 hd))
    (twoStepRate_lt_one hw0 hd hs) Q'.zero_le_one
    (ExpNeg.half_mul_pos kappa hk) n hn
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.mul_one_eqv _)) h

/-- A positive macroscopic lower ratio beyond the computed onset forces
the ACTUAL smoothed vector to vanish. x may depend arbitrarily on n. -/
theorem macroscopic_ratio_image_zero (x : V) (hx : B x U = RCzero)
    (kappa : Q') (hk : (0 : Q') < kappa) (n : Nat)
    (hn : ratioCutoff hd kappa ≤ n)
    (hratio : RCle (RCscale kappa (response hw0 hw1 hsmall hd hs x (2*n)))
      (response hw0 hw1 hsmall hd hs x (4*n))) : T n x = Z := by
  have hupper := relative_even_response_bound hw0 hw1 hsmall hd hs x hx n n
  rw [show 2*(n+n)=4*n by omega] at hupper
  have hnon : RCnonneg (response hw0 hw1 hsmall hd hs x (2*n)) := by
    unfold response
    rw [completedInner_even_diagonal]
    exact completedInner_nonnegative hw0 hw1 hsmall hd hs (T n x)
  have hzero := scalar_ratio_zero kappa (theta^n)
    (positive_margin kappa (theta^n) hk (rate_at_ratioCutoff hw0 hw1 hd hs kappa hk n hn))
    (response hw0 hw1 hsmall hd hs x (2*n)) hnon (RCle_trans hratio hupper)
  apply (completedInner_posdef hw0 hw1 hsmall hd hs (T n x)).mp
  simpa only [response, completedInner_even_diagonal] using hzero

theorem macroscopic_ratio_response_zero (x : V) (hx : B x U = RCzero)
    (kappa : Q') (hk : (0 : Q') < kappa) (n : Nat)
    (hn : ratioCutoff hd kappa ≤ n)
    (hratio : RCle (RCscale kappa (response hw0 hw1 hsmall hd hs x (2*n)))
      (response hw0 hw1 hsmall hd hs x (4*n))) :
    response hw0 hw1 hsmall hd hs x (2*n) = RCzero := by
  unfold response
  rw [completedInner_even_diagonal,
    macroscopic_ratio_image_zero hw0 hw1 hsmall hd hs x hx kappa hk n hn hratio,
    completedInner_zero_left]

/-- A single guarded coupling ceiling computes a vector- and nome-independent
onset for the relative obstruction. There is no initial norm cap. -/
def ceilingRatioCutoff (W : Q') (hdW : heatRemainderBound W < 1)
    (kappa : Q') : Nat :=
  geometricCutoff (twoStepRate W hdW) 1 (HalfPow.half*kappa)

/-- The original relative even-response bound is uniform below the named
guarded ceiling. The response and its own smoothed norm are unchanged. -/
theorem relative_even_response_ceiling (x : V) (hx : B x U = RCzero)
    (W : Q') (hdW : heatRemainderBound W < 1) (hwW : w ≤ W)
    (start n : Nat) :
    RCle (response hw0 hw1 hsmall hd hs x (2*(start+n)))
      (RCscale ((twoStepRate W hdW)^n)
        (response hw0 hw1 hsmall hd hs x (2*start))) := by
  have hpow := CRealLog.pow_le_pow_base _ _
    (Q'.le_of_lt (twoStepRate_positive hw0 hd))
    (BF4ExactSlabCouplingRateMonotonicity.twoStepRate_mono
      (Q'.le_of_lt hw0) hwW hd hdW) n
  have hnorm : RCnonneg (response hw0 hw1 hsmall hd hs x (2*start)) := by
    unfold response
    rw [completedInner_even_diagonal]
    exact completedInner_nonnegative hw0 hw1 hsmall hd hs (T start x)
  exact RCle_trans (relative_even_response_bound hw0 hw1 hsmall hd hs x hx start n)
    (RCscale_scalar_mono hpow hnorm)

/-- Arbitrary normalization cannot preserve a positive macroscopic ratio
with nonzero smoothed source below any fixed guarded ceiling, even if the
nome and vector are chosen separately at every scale. -/
theorem macroscopic_ratio_image_zero_of_nome_le (x : V) (hx : B x U = RCzero)
    (W : Q') (hW0 : (0 : Q') < W) (hdW : heatRemainderBound W < 1)
    (hsW : entropyRate 625 (adjustedCoreRate W hdW) < 1) (hwW : w ≤ W)
    (kappa : Q') (hk : (0 : Q') < kappa) (n : Nat)
    (hn : ceilingRatioCutoff W hdW kappa ≤ n)
    (hratio : RCle (RCscale kappa (response hw0 hw1 hsmall hd hs x (2*n)))
      (response hw0 hw1 hsmall hd hs x (4*n))) : T n x = Z := by
  have hgeo := geometric_bound (Q'.le_of_lt (twoStepRate_positive hW0 hdW))
    (twoStepRate_lt_one hW0 hdW hsW) Q'.zero_le_one
    (ExpNeg.half_mul_pos kappa hk) n hn
  have hdecay : (twoStepRate W hdW)^n ≤ HalfPow.half*kappa :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.mul_one_eqv _)) hgeo
  have hupper := relative_even_response_ceiling hw0 hw1 hsmall hd hs x hx W hdW hwW n n
  rw [show 2*(n+n)=4*n by omega] at hupper
  have hnon : RCnonneg (response hw0 hw1 hsmall hd hs x (2*n)) := by
    unfold response
    rw [completedInner_even_diagonal]
    exact completedInner_nonnegative hw0 hw1 hsmall hd hs (T n x)
  have hzero := scalar_ratio_zero kappa ((twoStepRate W hdW)^n)
    (positive_margin kappa _ hk hdecay)
    (response hw0 hw1 hsmall hd hs x (2*n)) hnon (RCle_trans hratio hupper)
  apply (completedInner_posdef hw0 hw1 hsmall hd hs (T n x)).mp
  simpa only [response, completedInner_even_diagonal] using hzero

/-- A nonzero actual smoothed source with the macroscopic ratio must leave
W at the computed onset. No source norm, support or renormalization bound
is a hypothesis. This is NOT a proof of escape from the whole guard region. -/
theorem nome_gt_of_nonzero_macroscopic_ratio (x : V) (hx : B x U = RCzero)
    (W : Q') (hW0 : (0 : Q') < W) (hdW : heatRemainderBound W < 1)
    (hsW : entropyRate 625 (adjustedCoreRate W hdW) < 1)
    (kappa : Q') (hk : (0 : Q') < kappa) (n : Nat)
    (hn : ceilingRatioCutoff W hdW kappa ≤ n) (himage : T n x ≠ Z)
    (hratio : RCle (RCscale kappa (response hw0 hw1 hsmall hd hs x (2*n)))
      (response hw0 hw1 hsmall hd hs x (4*n))) : W < w := by
  apply Int.lt_of_not_ge
  intro hwW
  exact himage (macroscopic_ratio_image_zero_of_nome_le hw0 hw1 hsmall hd hs x hx
    W hW0 hdW hsW hwW kappa hk n hn hratio)

/-- A single computed cutoff controls ALL centered vectors of squared norm
at most one on the existing thermodynamic carrier. In particular the bound
is independent of support and of how a normalized vector was constructed. -/
theorem unit_bounded_response_small (x : V) (hx : B x U = RCzero)
    (hunit : RCle (B x x) (Quotient.mk crealSetoid (ofQ' 1)))
    (epsilon : Q') (he : (0 : Q') < epsilon) (n : Nat)
    (hn : geometricCutoff theta 1 epsilon ≤ n) :
    RCle (response hw0 hw1 hsmall hd hs x (2*n))
      (Quotient.mk crealSetoid (ofQ' epsilon)) := by
  have hdecay := norm_decay hw0 hw1 hsmall hd hs x hx n
  have hscaled := RCscale_mono
    (Q'.pow_nonneg theta (Q'.le_of_lt (twoStepRate_positive hw0 hd)) n) hunit
  have hgeo := geometric_bound (Q'.le_of_lt (twoStepRate_positive hw0 hd))
    (twoStepRate_lt_one hw0 hd hs) Q'.zero_le_one he n hn
  unfold response
  rw [completedInner_even_diagonal]
  exact RCle_trans hdecay (RCle_trans hscaled
    (leEv_le_ofQ'_of_approx_le (fun _ => hgeo)))

end YMGap.Continuum.BF4WilsonSpatialUnionMacroscopicRatioObstruction

#print axioms YMGap.Continuum.BF4WilsonSpatialUnionMacroscopicRatioObstruction.response
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionMacroscopicRatioObstruction.relative_even_response_bound
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionMacroscopicRatioObstruction.ratioCutoff
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionMacroscopicRatioObstruction.rate_at_ratioCutoff
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionMacroscopicRatioObstruction.macroscopic_ratio_image_zero
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionMacroscopicRatioObstruction.macroscopic_ratio_response_zero
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionMacroscopicRatioObstruction.ceilingRatioCutoff
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionMacroscopicRatioObstruction.relative_even_response_ceiling
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionMacroscopicRatioObstruction.macroscopic_ratio_image_zero_of_nome_le
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionMacroscopicRatioObstruction.nome_gt_of_nonzero_macroscopic_ratio
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionMacroscopicRatioObstruction.unit_bounded_response_small
