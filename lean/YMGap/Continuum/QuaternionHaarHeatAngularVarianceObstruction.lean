/-
# A SAME-law obstruction to nome-uniform angular/variance comparison

For the fundamental character of an exposed four-link holonomy, the actual
heat prefix has mass one, variance 1+3*w^8-4*w^6, and selected-link angular
energy 3*(1-w^8). The variance is quadratic in 1-w; angular energy is linear.
The explicit small-deficit guard therefore refutes a bounded comparison.

This is a bare four-link heat law, not the interacting odd marginal
(V*g_n)*g_(n+1). It does not rule out source-specific estimates, nome-dependent
constants, a different observable family, or a continuum Yang--Mills gap.
All normalized quantities use the SAME original Haar mass. At the computed
head cutoff, ExposedHeatPositive supplies an actual density certificate.
-/

import YMGap.Continuum.QuaternionHaarExposedHeatMoments
import YMGap.Continuum.QuaternionHaarExposedFundamentalEnergy
import YMGap.Continuum.QuaternionHaarExposedHeatPositive
import YMGap.Continuum.QuaternionHaarNormalizedMomentCongruence
import YMGap.Continuum.SU2QuaternionHeatCovarianceRates

namespace YMGap.Continuum.QuaternionHaarHeatAngularVarianceObstruction

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionSpinTwoConditionalHaar
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarHeatCertificate
open YMGap.Continuum.QuaternionHaarDensityVariance
open YMGap.Continuum.QuaternionHaarLinearAngularEnergy
open YMGap.Continuum.QuaternionHaarExposedHeatMoments
open YMGap.Continuum.QuaternionHaarExposedFundamentalEnergy
open YMGap.Continuum.QuaternionHaarExposedHeatPositive
open YMGap.Continuum.SU2QuaternionHeatCovarianceRates
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)

local infix:50 " ≈ " => Q'.eqv

private theorem qmul {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h)
    (Q'.mul_eqv_congr_left _ _ _ k)

private theorem normalized_of_mass_one {blocks : Nat} {W : RatPoly}
    (hZ : (0 : Q') < quaternionHaar blocks W)
    (hmass : quaternionHaar blocks W ≈ 1) (p : RatPoly) :
    normalizedMoment blocks W p hZ ≈ quaternionHaar blocks (polyMul W p) := by
  have hr : Q'.recipPos (quaternionHaar blocks W) hZ ≈ 1 :=
    Q'.eqv_trans _ _ _ (Q'.recipPos_eqv_congr _ 1 hZ (by decide) hmass) (by decide)
  exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hr) (Q'.mul_one_eqv _)

variable {blocks : Nat} (hb : 3 < blocks) (r0 r1 r2 r3 : Bool)
include hb

local notation "x" => PolyQuaternion.scalar (exposedFourWord r0 r1 r2 r3)
local notation "f" => characterPolynomial x 1

/-- The denominator is the actual heat mass, not a supplied surrogate. -/
theorem heatMass_positive (w : Q') (K : Nat) :
    (0 : Q') < quaternionHaar blocks (heatPrefix w K x) :=
  HeatKernelRGStep.lt_of_lt_of_le (by decide : (0 : Q') < 1)
    (Q'.ge_of_eqv (heat_mass hb r0 r1 r2 r3 w K))

/-- Exact normalized fundamental mean in this SAME law. -/
theorem normalized_mean (w : Q') (K : Nat) (hK : 1 ≤ K)
    (hZ : (0 : Q') < quaternionHaar blocks (heatPrefix w K x)) :
    normalizedMoment blocks (heatPrefix w K x) f hZ ≈ 2*RGTransport.qpow w 3 :=
  Q'.eqv_trans _ _ _
    (normalized_of_mass_one hZ (heat_mass hb r0 r1 r2 r3 w K) f)
    (heat_fundamental_moment hb r0 r1 r2 r3 w K hK)

/-- Centering uses the actual normalized mean, including its square. -/
theorem normalized_variance (w : Q') (K : Nat) (hK : 2 ≤ K)
    (hZ : (0 : Q') < quaternionHaar blocks (heatPrefix w K x)) :
    normalizedVariance blocks (heatPrefix w K x) f hZ ≈ radialRate w := by
  have hm := normalized_mean hb r0 r1 r2 r3 w K (by omega) hZ
  have hs := Q'.eqv_trans _ _ _
    (normalized_of_mass_one hZ (heat_mass hb r0 r1 r2 r3 w K) (polyMul f f))
    (heat_fundamental_square_moment hb r0 r1 r2 r3 w K hK)
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' hs (Q'.neg_eqv_congr _ _ (qmul hm hm))) ?_
  exact poly_identity_of_normal_eq
    (.add (.add (.const 1) (.mul (.const 3) (.pow (.var 0) 8)))
      (.neg (.mul (.mul (.const 2) (.pow (.var 0) 3))
        (.mul (.const 2) (.pow (.var 0) 3)))))
    (.add (.add (.const 1) (.mul (.const 3) (.pow (.var 0) 8)))
      (.neg (.mul (.const 4) (.pow (.var 0) 6))))
    (by decide) (fun _ => w)

/-- The six-plane angular energy is at one selected link, not summed over
the four links. Its moment is normalized by exactly the same heat mass. -/
theorem normalized_angular (w : Q') (K : Nat) (hK : 2 ≤ K)
    (hZ : (0 : Q') < quaternionHaar blocks (heatPrefix w K x)) :
    normalizedMoment blocks (heatPrefix w K x) (angularSquare f) hZ ≈
      3 * transverseRate w := by
  let W := heatPrefix w K x
  let F := polyMul f f
  have hp : RatPolyCoeffEqv (polyMul W (polyAdd (cap 4) (polyNeg F)))
      (polyAdd (polySmul 4 W) (polySmul (-1) (polyMul W F))) :=
    (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.var 0) (.add (.const 4) (.neg (.var 1))))
      (.add (.mul (.const 4) (.var 0))
        (.mul (.const (-1)) (.mul (.var 0) (.var 1))))
      (by decide) (fun | 0 => W | _ => F)).trans
      ((cap_mul_left 4 W).add (cap_mul_left (-1) (polyMul W F)))
  have hraw := Q'.eqv_trans _ _ _
    (exposedFundamental_angularSquare hb r0 r1 r2 r3 W)
    (Q'.eqv_trans _ _ _ (haar_of_coeff hp)
      (Q'.eqv_trans _ _ _ (quaternionHaar_append blocks _ _)
        (Q'.add_eqv_congr' (quaternionHaar_polySmul blocks 4 W)
          (quaternionHaar_polySmul blocks (-1) (polyMul W F)))))
  have hpin := Q'.add_eqv_congr'
    (Q'.mul_eqv_congr_left 4 _ _ (heat_mass hb r0 r1 r2 r3 w K))
    (Q'.mul_eqv_congr_left (-1) _ _
      (heat_fundamental_square_moment hb r0 r1 r2 r3 w K hK))
  refine Q'.eqv_trans _ _ _
    (normalized_of_mass_one hZ (heat_mass hb r0 r1 r2 r3 w K) (angularSquare f))
    (Q'.eqv_trans _ _ _ hraw (Q'.eqv_trans _ _ _ hpin ?_))
  exact poly_identity_of_normal_eq
    (.add (.mul (.const 4) (.const 1))
      (.mul (.const (-1)) (.add (.const 1) (.mul (.const 3) (.pow (.var 0) 8)))))
    (.mul (.const 3) (.add (.const 1) (.neg (.pow (.var 0) 8))))
    (by decide) (fun _ => w)

/-- Even the first-order angular BUDGET `(1-w)*E[Gamma(f)]` retains at least
one eighth of this variance. This is NOT a lower bound on temporal energy:
an upper-bound budget cannot be reversed into such a conclusion. -/
theorem variance_le_eight_scaled_angular {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K : Nat) (hK : 2 ≤ K)
    (hZ : (0 : Q') < quaternionHaar blocks (heatPrefix w K x)) :
    normalizedVariance blocks (heatPrefix w K x) f hZ ≤
      (8 : Q') * ((1 : Q') + -w) *
        normalizedMoment blocks (heatPrefix w K x) (angularSquare f) hZ :=
  Q'.le_trans' _ _ _
    (Q'.le_of_eqv (normalized_variance hb r0 r1 r2 r3 w K hK hZ))
    (Q'.le_trans' _ _ _ (radialRate_le_eight_scaled_angular hw0 hw1)
      (Q'.ge_of_eqv (Q'.mul_eqv_congr_left _ _ _
        (normalized_angular hb r0 r1 r2 r3 w K hK hZ))))

/-- Quantitative obstruction for the actual normalized angular energy and
centered variance. Positivity at late cutoff is independently constructed
by `exposedHeatPrefixCertificate`, with no restriction to small nomes. -/
theorem angular_not_le_variance_multiple {w C : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (hC : (0 : Q') ≤ C)
    (hsmall : (24 : Q') * C * ((1 : Q') + -w) < 3)
    (K : Nat) (hK : 2 ≤ K)
    (hZ : (0 : Q') < quaternionHaar blocks (heatPrefix w K x)) :
    ¬ normalizedMoment blocks (heatPrefix w K x) (angularSquare f) hZ ≤
      C * normalizedVariance blocks (heatPrefix w K x) f hZ := by
  intro h
  apply angularRate_not_le_multiple_radial hw0 hw1 hC hsmall
  exact Q'.le_trans' _ _ _
    (Q'.ge_of_eqv (normalized_angular hb r0 r1 r2 r3 w K hK hZ))
    (Q'.le_trans' _ _ _ h (Q'.le_of_eqv (Q'.mul_eqv_congr_left C _ _
      (normalized_variance hb r0 r1 r2 r3 w K hK hZ))))

/-- An explicit positive, unit-mass heat-law counterexample for EVERY proposed
nonnegative constant, beyond ANY requested cutoff. The nome is computed by
`obstructionNome`; the returned data include the actual positivity certificate.
This is not the interacting Yang--Mills odd marginal. -/
def positiveCounterexample (C : Q') (hC : (0 : Q') ≤ C) (onset : Nat) :
    Σ K : Nat, { _density : Certificate blocks
      (heatPrefix (obstructionNome C hC) K x) //
      onset ≤ K ∧
      ¬ normalizedMoment blocks (heatPrefix (obstructionNome C hC) K x)
          (angularSquare f) (heatMass_positive hb r0 r1 r2 r3 _ K) ≤
        C * normalizedVariance blocks (heatPrefix (obstructionNome C hC) K x)
          f (heatMass_positive hb r0 r1 r2 r3 _ K) } := by
  let w := obstructionNome C hC
  let K := max onset (max 2 (headCutoff w))
  have hK2 : 2 ≤ K := Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)
  have hKh : headCutoff w ≤ K :=
    Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)
  refine ⟨K, exposedHeatPrefixCertificate hb r0 r1 r2 r3
    (obstructionNome_pos hC) (obstructionNome_lt_one hC) K hKh,
    Nat.le_max_left _ _, ?_⟩
  exact angular_not_le_variance_multiple hb r0 r1 r2 r3
    (obstructionNome_pos hC) (obstructionNome_lt_one hC) hC
    (obstructionNome_smallness hC) K hK2 (heatMass_positive hb r0 r1 r2 r3 w K)

#print axioms heatMass_positive
#print axioms normalized_mean
#print axioms normalized_variance
#print axioms normalized_angular
#print axioms variance_le_eight_scaled_angular
#print axioms angular_not_le_variance_multiple
#print axioms positiveCounterexample

end YMGap.Continuum.QuaternionHaarHeatAngularVarianceObstruction
