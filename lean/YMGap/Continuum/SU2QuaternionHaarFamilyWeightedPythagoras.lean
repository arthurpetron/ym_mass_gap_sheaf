/-
# SAME-weight Pythagoras for the original finite Haar family projection

Every projected slot is absent from the supplied weight W. The original
familyProject then preserves the weighted mean and is orthogonal to its
literal residual under every independent test. The weighted square splits
exactly, and a Certificate for W constructs the nonnegative residual term,
giving contraction with coefficient ONE. All surviving variables and the
original Haar functional are retained; repeated schedule slots are allowed.

The consumer removes the positive lower-fringe Jensen debt before squaring
the actual source derivative. No interaction-independent norm comparison,
conditional rate assumption or family-uniform estimate is asserted.
-/

import YMGap.Continuum.SU2QuaternionHaarFamilyPythagoras
import YMGap.Continuum.QuaternionHaarFamilySquare

namespace YMGap.Continuum.SU2QuaternionHaarFamilyWeightedPythagoras

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder (quaternionHaar_append)
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionHaarFamilyProjection
open YMGap.Continuum.SU2QuaternionHaarFamilyPythagoras (familyResidual familyResidual_supported)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarFamilySquare (haar_weighted_add)

local infix:50 " ≈ " => Q'.eqv

private theorem haar_neg (blocks : Nat) : ∀ p : RatPoly,
    quaternionHaar blocks (polyNeg p) ≈ -(quaternionHaar blocks p)
  | [] => by change (0 : Q') ≈ -0; decide
  | t::rest =>
      Q'.eqv_trans _ _ _ (Q'.add_eqv_congr'
        (Q'.neg_mul_eqv t.2 (quaternionHaarMono blocks t.1))
        (haar_neg blocks rest)) (Q'.eqv_symm (Q'.neg_add_eqv_split _ _))

/-- Exact weighted mean preservation. Positivity and support are not needed
for this algebraic identity; the actual callers supply them separately. -/
theorem familyProject_weighted_mean (blocks : Nat) (ids : List Nat)
    (hids : ∀ i, i ∈ ids → i < blocks) (W f : RatPoly)
    (hW : ∀ i, i ∈ ids → QuaternionBlockIndependent i W) :
    quaternionHaar blocks (polyMul W (familyProject ids f)) ≈
      quaternionHaar blocks (polyMul W f) :=
  Q'.eqv_trans _ _ _
    (Q'.eqv_symm (haar_of_coeff (familyProject_mul_of_independent ids W f hW)))
    (familyProject_mean blocks ids hids (polyMul W f))

private theorem weighted_project_pairing (blocks : Nat) (ids : List Nat)
    (hids : ∀ i, i ∈ ids → i < blocks) (W f z : RatPoly)
    (hW : ∀ i, i ∈ ids → QuaternionBlockIndependent i W)
    (hz : ∀ i, i ∈ ids → QuaternionBlockIndependent i z) :
    quaternionHaar blocks (polyMul W (polyMul z f)) ≈
      quaternionHaar blocks (polyMul W (polyMul z (familyProject ids f))) := by
  have hmul : RatPolyCoeffEqv (familyProject ids (polyMul W (polyMul z f)))
      (polyMul W (polyMul z (familyProject ids f))) :=
    (familyProject_mul_of_independent ids W (polyMul z f) hW).trans
      ((familyProject_mul_of_independent ids z f hz).mul_left W)
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_symm (familyProject_mean blocks ids hids (polyMul W (polyMul z f))))
    (haar_of_coeff hmul)

/-- Every independent insertion is orthogonal to the literal residual,
with the SAME independent weight retained. No positivity premise is used. -/
theorem familyResidual_weighted_orthogonal (blocks : Nat) (ids : List Nat)
    (hids : ∀ i, i ∈ ids → i < blocks) (W f z : RatPoly)
    (hW : ∀ i, i ∈ ids → QuaternionBlockIndependent i W)
    (hz : ∀ i, i ∈ ids → QuaternionBlockIndependent i z) :
    quaternionHaar blocks (polyMul W (polyMul z (familyResidual ids f))) ≈ 0 := by
  let Q := familyProject ids f
  have hc := weighted_project_pairing blocks ids hids W f z hW hz
  have halg : RatPolyCoeffEqv (polyMul W (polyMul z (familyResidual ids f)))
      (polyAdd (polyMul W (polyMul z f)) (polyNeg (polyMul W (polyMul z Q)))) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.var 0) (.mul (.var 1) (.add (.var 2) (.neg (.var 3)))))
      (.add (.mul (.var 0) (.mul (.var 1) (.var 2)))
        (.neg (.mul (.var 0) (.mul (.var 1) (.var 3)))))
      (by decide) (fun | 0 => W | 1 => z | 2 => f | _ => Q)
  exact Q'.eqv_trans _ _ _ (haar_of_coeff halg)
    (Q'.eqv_trans _ _ _ (quaternionHaar_append blocks _ _)
      (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' hc (haar_neg blocks _))
        (Q'.add_neg_self_eqv _)))

/-- Exact original weighted Pythagoras. This identity holds even for a
signed independent W; positivity is used only in the contraction consumer. -/
theorem family_weighted_square_decomposition (blocks : Nat) (ids : List Nat)
    (hids : ∀ i, i ∈ ids → i < blocks) (W f : RatPoly)
    (hW : ∀ i, i ∈ ids → QuaternionBlockIndependent i W) :
    quaternionHaar blocks (polyMul W (polyMul f f)) ≈
      quaternionHaar blocks (polyMul W
          (polyMul (familyProject ids f) (familyProject ids f))) +
        quaternionHaar blocks (polyMul W
          (polyMul (familyResidual ids f) (familyResidual ids f))) := by
  let Q := familyProject ids f
  let R := familyResidual ids f
  have hc : quaternionHaar blocks (polyMul W (polyMul Q R)) ≈ 0 :=
    familyResidual_weighted_orthogonal blocks ids hids W f Q hW
      (familyProject_independent ids f)
  have halg : RatPolyCoeffEqv (polyMul f f)
      (polyAdd (polyMul Q Q) (polyAdd (polyMul R R)
        (polyAdd (polyMul Q R) (polyMul Q R)))) :=
    coeffEvalExpr_eqv_of_normalize_eq (.mul (.var 0) (.var 0))
      (.add (.mul (.var 1) (.var 1))
        (.add (.mul (.add (.var 0) (.neg (.var 1))) (.add (.var 0) (.neg (.var 1))))
          (.add (.mul (.var 1) (.add (.var 0) (.neg (.var 1))))
            (.mul (.var 1) (.add (.var 0) (.neg (.var 1)))))))
      (by decide) (fun | 0 => f | _ => Q)
  have hz : quaternionHaar blocks (polyMul W (polyAdd (polyMul Q R) (polyMul Q R))) ≈ 0 :=
    Q'.eqv_trans _ _ _ (haar_weighted_add blocks W _ _)
      (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' hc hc) (by decide : (0 : Q') + 0 ≈ 0))
  exact Q'.eqv_trans _ _ _ (haar_of_coeff (halg.mul_left W))
    (Q'.eqv_trans _ _ _ (haar_weighted_add blocks W _ _)
      (Q'.add_eqv_congr_left _ _ _
        (Q'.eqv_trans _ _ _ (haar_weighted_add blocks W _ _)
          (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ hz)
            (Q'.eqv_of_eq (Q'.add_zero' _))))))

/-- The original positive W constructs the actual weighted residual square
certificate. W support is already part of its Certificate. -/
theorem familyResidual_weighted_square_nonnegative {blocks : Nat}
    (ids : List Nat) {W f : RatPoly} (P : Certificate blocks W)
    (hf : SupportedQuaternionBlocks blocks f) :
    0 ≤ quaternionHaar blocks (polyMul W
      (polyMul (familyResidual ids f) (familyResidual ids f))) :=
  (P.mul (Certificate.square (familyResidual ids f) (familyResidual_supported ids hf))).haar_nonnegative

/-- Coefficient-one projection contraction in the SAME positive weight,
with all projected-slot bounds and independence hypotheses explicit. -/
theorem familyProject_weighted_square_le (blocks : Nat) (ids : List Nat)
    (hids : ∀ i, i ∈ ids → i < blocks) {W f : RatPoly}
    (P : Certificate blocks W) (hf : SupportedQuaternionBlocks blocks f)
    (hW : ∀ i, i ∈ ids → QuaternionBlockIndependent i W) :
    quaternionHaar blocks (polyMul W
        (polyMul (familyProject ids f) (familyProject ids f))) ≤
      quaternionHaar blocks (polyMul W (polyMul f f)) :=
  Q'.le_trans' _ _ _
    (Q'.add_le_self_of_nonneg _ _ (familyResidual_weighted_square_nonnegative ids P hf))
    (Q'.ge_of_eqv (family_weighted_square_decomposition blocks ids hids W f hW))

end YMGap.Continuum.SU2QuaternionHaarFamilyWeightedPythagoras

#print axioms YMGap.Continuum.SU2QuaternionHaarFamilyWeightedPythagoras.familyProject_weighted_mean
#print axioms YMGap.Continuum.SU2QuaternionHaarFamilyWeightedPythagoras.familyResidual_weighted_orthogonal
#print axioms YMGap.Continuum.SU2QuaternionHaarFamilyWeightedPythagoras.family_weighted_square_decomposition
#print axioms YMGap.Continuum.SU2QuaternionHaarFamilyWeightedPythagoras.familyResidual_weighted_square_nonnegative
#print axioms YMGap.Continuum.SU2QuaternionHaarFamilyWeightedPythagoras.familyProject_weighted_square_le
