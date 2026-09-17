/-
# A norm-controlled full-fringe projection in the original marginal

The spatial residual R=(P_F V)f-P_F(Vf) and numerator M=P_F(Vf) are
orthogonal in the SAME odd marginal after multiplication by any polynomial
J independent of the fringe. Their squared norms add to the norm of
((P_F V)*J)*f. For the constructed reciprocal polynomial J_k, this sum
is at most the original squared norm of f, with coefficient one.

The two pieces also approximate f with squared error at most
rate^(2*k) times its original squared norm. J_k and its rate do not depend
on terminal depth. Cutoff, nome and spatial-width dependence remains;
the rate concerns polynomial approximation, not physical time or a gap.
No active-sector estimate, completed projection or continuum claim is made.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialFringeProjectionWindow
import YMGap.Continuum.QuaternionHaarPolynomialIntervalProduct
import YMGap.Continuum.QuaternionHaarFamilySquare

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialFringeProjectionNorm

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFlow (fringeBlocks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalDual
  (marginalWeight marginalPair marginalCertificate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFringeProjection
open YMGap.Continuum.BF4ExactSlabFixedSpatialFringeProjectionWindow
  (reciprocal reciprocal_supported reciprocal_independent rate rate_nonnegative rate_lt_one
    multiplierSquareCertificate multiplierErrorInterval)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
  (QuaternionBlockIndependent quaternionBlockIndependent_polyMul)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarFamilySquare (haar_weighted_add)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] baseLinks

private theorem square_add (p q : RatPoly) :
    RatPolyCoeffEqv (polyMul (polyAdd p q) (polyAdd p q))
      (polyAdd (polyAdd (polyMul p p) (polyMul q q))
        (polyAdd (polyMul p q) (polyMul p q))) :=
  coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.add (.var 0) (.var 1)) (.add (.var 0) (.var 1)))
    (.add (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1)))
      (.add (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1))))
    (by decide) (fun | 0 => p | _ => q)

private theorem norm_add (w : Q') (K width n : Nat) (p q : RatPoly) :
    marginalPair w K width n (polyAdd p q) (polyAdd p q) ≈
      (marginalPair w K width n p p + marginalPair w K width n q q) +
      (marginalPair w K width n p q + marginalPair w K width n p q) :=
  Q'.eqv_trans _ _ _ (haar_of_coeff ((square_add p q).mul_left (marginalWeight w K width n)))
    (Q'.eqv_trans _ _ _ (haar_weighted_add (N width) (marginalWeight w K width n) _ _)
      (Q'.add_eqv_congr'
        (haar_weighted_add (N width) (marginalWeight w K width n) _ _)
        (haar_weighted_add (N width) (marginalWeight w K width n) _ _)))

/-- Exact finite polynomial splitting, without an independence premise. -/
theorem scaled_split (w : Q') (K width : Nat) (f J : RatPoly) :
    RatPolyCoeffEqv
      (polyAdd (polyMul J (spatialFringeResidual w K width f))
        (polyMul J (spatialFringeMean w K width f)))
      (polyMul (polyMul (spatialFringeMass w K width) J) f) :=
  (RatPolyCoeffEqv.mul_add_right J _ _).symm.trans
    (((spatialFringeResidual_split w K width f).mul_left J).trans
      ((RatPolyCoeffEqv.mul_assoc J (spatialFringeMass w K width) f).symm.trans
        ((RatPolyCoeffEqv.mul_comm J (spatialFringeMass w K width)).mul_right f)))

/-- Both scaled pieces are orthogonal on the ORIGINAL weighted carrier. -/
theorem scaled_pieces_orthogonal (w : Q') (K width n : Nat) (f J : RatPoly)
    (hJ : ∀ i, i ∈ fringeBlocks width → QuaternionBlockIndependent i J) :
    marginalPair w K width n (polyMul J (spatialFringeResidual w K width f))
      (polyMul J (spatialFringeMean w K width f)) ≈ 0 := by
  let R := spatialFringeResidual w K width f
  let M := spatialFringeMean w K width f
  have hb : ∀ i, i ∈ fringeBlocks width → QuaternionBlockIndependent i (polyMul J (polyMul J M)) :=
    fun i hi => quaternionBlockIndependent_polyMul (hJ i hi)
      (quaternionBlockIndependent_polyMul (hJ i hi) (spatialFringeMean_independent w K width f i hi))
  exact Q'.eqv_trans _ _ _
    (haar_of_coeff ((coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 2)))
      (.mul (.var 1) (.mul (.var 0) (.mul (.var 0) (.var 2))))
      (by decide) (fun | 0 => J | 1 => R | _ => M)).mul_left (marginalWeight w K width n)))
    (spatialFringeResidual_orthogonal w K width n f (polyMul J (polyMul J M)) hb)

/-- Exact Pythagoras; no signed cross term is estimated separately. -/
theorem scaled_pieces_pythagoras (w : Q') (K width n : Nat) (f J : RatPoly)
    (hJ : ∀ i, i ∈ fringeBlocks width → QuaternionBlockIndependent i J) :
    marginalPair w K width n (polyMul J (spatialFringeResidual w K width f))
        (polyMul J (spatialFringeResidual w K width f)) +
      marginalPair w K width n (polyMul J (spatialFringeMean w K width f))
        (polyMul J (spatialFringeMean w K width f)) ≈
      marginalPair w K width n (polyMul (polyMul (spatialFringeMass w K width) J) f)
        (polyMul (polyMul (spatialFringeMass w K width) J) f) := by
  let r := polyMul J (spatialFringeResidual w K width f)
  let m := polyMul J (spatialFringeMean w K width f)
  have hz := scaled_pieces_orthogonal w K width n f J hJ
  have hsum : marginalPair w K width n (polyAdd r m) (polyAdd r m) ≈
      marginalPair w K width n r r + marginalPair w K width n m m :=
    Q'.eqv_trans _ _ _ (norm_add w K width n r m)
      (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (Q'.eqv_refl _) (Q'.add_eqv_congr' hz hz))
        (Q'.eqv_of_eq (Q'.add_zero' _)))
  have hs := scaled_split w K width f J
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm hsum)
    (haar_of_coeff ((hs.mul hs).mul_left (marginalWeight w K width n)))

private theorem weighted_multiplier_square_bound {blocks : Nat} {nu p f : RatPoly} {c : Q'}
    (M : Certificate blocks nu) (P : SquareBound blocks p c)
    (hf : SupportedQuaternionBlocks blocks f) :
    quaternionHaar blocks (polyMul nu (polyMul (polyMul p f) (polyMul p f))) ≤
      c*quaternionHaar blocks (polyMul nu (polyMul f f)) := by
  let I : Interval blocks (polyMul p p) c :=
    ⟨supported_polyMul P.support P.support, P.nonnegative, P.certificate,
      (Certificate.constant blocks c P.nonnegative).add (Certificate.square p P.support)⟩
  have h := I.weighted_haar_bound (M.mul (Certificate.square f hf))
  have he : quaternionHaar blocks (polyMul nu (polyMul (polyMul p f) (polyMul p f))) ≈
      quaternionHaar blocks (polyMul (polyMul nu (polyMul f f)) (polyMul p p)) :=
    haar_of_coeff (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.var 0) (.mul (.mul (.var 1) (.var 2)) (.mul (.var 1) (.var 2))))
      (.mul (.mul (.var 0) (.mul (.var 2) (.var 2))) (.mul (.var 1) (.var 1)))
      (by decide) (fun | 0 => nu | 1 => p | _ => f))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv he) (Q'.le_trans' _ _ _ (Q'.le_abs_self _) h)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K width : Nat) (hK : headCutoff w ≤ K) (n k : Nat)

/-- Coefficient-one norm control for BOTH actual polynomial pieces together. -/
theorem reciprocal_pieces_norm_le {f : RatPoly} (hf : SupportedQuaternionBlocks (N width) f) :
    let J := reciprocal hw0 hw1 K width hK k
    marginalPair w K width n (polyMul J (spatialFringeResidual w K width f))
        (polyMul J (spatialFringeResidual w K width f)) +
      marginalPair w K width n (polyMul J (spatialFringeMean w K width f))
        (polyMul J (spatialFringeMean w K width f)) ≤ marginalPair w K width n f f := by
  let J := reciprocal hw0 hw1 K width hK k
  let p := polyMul (spatialFringeMass w K width) J
  let P : SquareBound (N width) p 1 :=
    ⟨supported_polyMul (spatialFringeMass_supported w K width) (reciprocal_supported hw0 hw1 K width hK k),
      Q'.zero_le_one, .ofCoeff ((RatPolyCoeffEqv.one_smul polyOne).add (RatPolyCoeffEqv.refl _))
        (multiplierSquareCertificate hw0 hw1 K width hK k)⟩
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (scaled_pieces_pythagoras w K width n f J (reciprocal_independent hw0 hw1 K width hK k)))
    (Q'.le_trans' _ _ _ (weighted_multiplier_square_bound (marginalCertificate hw0 hw1 K width hK n) P hf)
      (Q'.le_of_eqv (Q'.one_mul_eqv _)))

private theorem multiplier_difference (p f : RatPoly) :
    RatPolyCoeffEqv (polyMul (polyAdd p (polyNeg polyOne)) f)
      (polyAdd (polyMul p f) (polyNeg f)) :=
  (coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.add (.var 0) (.neg (.var 2))) (.var 1))
    (.add (.mul (.var 0) (.var 1)) (.neg (.mul (.var 2) (.var 1))))
    (by decide) (fun | 0 => p | 1 => f | _ => polyOne)).trans
    ((RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.neg (RatPolyCoeffEqv.one_mul f)))

private theorem square_difference_swap (p q : RatPoly) :
    RatPolyCoeffEqv (polyMul (polyAdd p (polyNeg q)) (polyAdd p (polyNeg q)))
      (polyMul (polyAdd q (polyNeg p)) (polyAdd q (polyNeg p))) :=
  coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.add (.var 0) (.neg (.var 1))) (.add (.var 0) (.neg (.var 1))))
    (.mul (.add (.var 1) (.neg (.var 0))) (.add (.var 1) (.neg (.var 0))))
    (by decide) (fun | 0 => p | _ => q)

/-- Geometric approximation in the SAME original norm, without a depth-dependent
prefactor or loss of a positive marginal floor. -/
theorem reciprocal_error_norm_le {f : RatPoly} (hf : SupportedQuaternionBlocks (N width) f) :
    let J := reciprocal hw0 hw1 K width hK k
    let e := polyAdd f (polyNeg (polyAdd (polyMul J (spatialFringeResidual w K width f))
      (polyMul J (spatialFringeMean w K width f))))
    marginalPair w K width n e e ≤
      ((rate hw0 hw1 K width hK)^k*(rate hw0 hw1 K width hK)^k)*marginalPair w K width n f f := by
  let J := reciprocal hw0 hw1 K width hK k
  let s := polyAdd (polyMul J (spatialFringeResidual w K width f))
    (polyMul J (spatialFringeMean w K width f))
  let p := polyMul (spatialFringeMass w K width) J
  let u := polyAdd p (polyNeg polyOne)
  let I := multiplierErrorInterval hw0 hw1 K width hK k
  let P : SquareBound (N width) u
      ((rate hw0 hw1 K width hK)^k*(rate hw0 hw1 K width hK)^k) :=
    ⟨I.support, Q'.mul_nonneg _ _ I.nonnegative I.nonnegative, (I.mul I).upper⟩
  have he : RatPolyCoeffEqv (polyAdd s (polyNeg f)) (polyMul u f) :=
    ((scaled_split w K width f J).add (RatPolyCoeffEqv.refl _)).trans
      (multiplier_difference p f).symm
  have hs := (square_difference_swap f s).trans (he.mul he)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (haar_of_coeff (hs.mul_left (marginalWeight w K width n))))
    (weighted_multiplier_square_bound (marginalCertificate hw0 hw1 K width hK n) P hf)

/-- A relative squared-error modulus independent of the observable and
terminal depth. It retains nome, cutoff and spatial width explicitly. -/
def relativeApproximationCutoff (epsilon : Q') : Nat :=
  PositiveContractionResidual.geometricCutoff (rate hw0 hw1 K width hK) 1 epsilon

theorem reciprocal_error_norm_le_tolerance {f : RatPoly}
    (hf : SupportedQuaternionBlocks (N width) f) (epsilon : Q')
    (hepsilon : (0 : Q') < epsilon)
    (hk : relativeApproximationCutoff hw0 hw1 K width hK epsilon ≤ k) :
    let J := reciprocal hw0 hw1 K width hK k
    let e := polyAdd f (polyNeg (polyAdd (polyMul J (spatialFringeResidual w K width f))
      (polyMul J (spatialFringeMean w K width f))))
    marginalPair w K width n e e ≤ epsilon*marginalPair w K width n f f := by
  have h0 := rate_nonnegative hw0 hw1 K width hK
  have h1 := rate_lt_one hw0 hw1 K width hK
  have hp0 := Q'.pow_nonneg _ h0 k
  have hp1 := HKPos.pow_le_one h0 (Q'.le_of_lt h1) k
  have he : (rate hw0 hw1 K width hK)^k*(rate hw0 hw1 K width hK)^k ≤ epsilon :=
    Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ hp1 hp0)
      (PositiveContractionResidual.geometric_bound h0 h1 Q'.zero_le_one hepsilon k hk)
  have hn := ((marginalCertificate hw0 hw1 K width hK n).mul (Certificate.square f hf)).haar_nonnegative
  exact Q'.le_trans' _ _ _ (reciprocal_error_norm_le hw0 hw1 K width hK n k hf)
    (Q'.mul_le_mul_of_nonneg_right _ _ _ he hn)

end YMGap.Continuum.BF4ExactSlabFixedSpatialFringeProjectionNorm

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFringeProjectionNorm.scaled_split
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFringeProjectionNorm.scaled_pieces_orthogonal
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFringeProjectionNorm.scaled_pieces_pythagoras
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFringeProjectionNorm.reciprocal_pieces_norm_le
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFringeProjectionNorm.reciprocal_error_norm_le
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFringeProjectionNorm.relativeApproximationCutoff
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFringeProjectionNorm.reciprocal_error_norm_le_tolerance
