/-
# Pythagoras for a finite family of quaternion Haar projections

The existing `familyProject` is the concrete iterated conditional Haar
projection.  This leaf records that its actual polynomial complement is
orthogonal on the same original Haar carrier.  Thus the full square splits
exactly into projected and residual squares, without a cardinality loss.
-/

import YMGap.Continuum.SU2QuaternionHaarFamilyProjection

namespace YMGap.Continuum.SU2QuaternionHaarFamilyPythagoras

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionOriginalHaarBlockMarginal
open YMGap.Continuum.SU2QuaternionHaarFamilyProjection
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv

/-- The genuine complement of the concrete finite-family Haar projection. -/
def familyResidual (ids : List Nat) (f : RatPoly) : RatPoly :=
  polyAdd f (polyNeg (familyProject ids f))

theorem familyResidual_supported {blocks : Nat} (ids : List Nat) {f : RatPoly}
    (hf : SupportedQuaternionBlocks blocks f) :
    SupportedQuaternionBlocks blocks (familyResidual ids f) := by
  apply supported_add hf
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact familyProject_supported ids hf s hs

private theorem haar_neg (blocks : Nat) : ∀ p : RatPoly,
    quaternionHaar blocks (polyNeg p) ≈ -(quaternionHaar blocks p)
  | [] => by change (0 : Q') ≈ -0; decide
  | t::rest =>
      Q'.eqv_trans _ _ _ (Q'.add_eqv_congr'
        (Q'.neg_mul_eqv t.2 (quaternionHaarMono blocks t.1))
        (haar_neg blocks rest)) (Q'.eqv_symm (Q'.neg_add_eqv_split _ _))

private theorem projected_residual_orthogonal (blocks : Nat) (ids : List Nat)
    (hids : ∀ i, i ∈ ids → i < blocks) (f : RatPoly) :
    quaternionHaar blocks
      (polyMul (familyProject ids f) (familyResidual ids f)) ≈ 0 := by
  let p := familyProject ids f
  have hcross : quaternionHaar blocks (polyMul p f) ≈
      quaternionHaar blocks (polyMul p p) :=
    quaternionHaar_polyMul_eq_after_integratingBlocks blocks ids p f hids
      (familyProject_independent ids f)
  have halg : RatPolyCoeffEqv (polyMul p (familyResidual ids f))
      (polyAdd (polyMul p f) (polyNeg (polyMul p p))) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.var 0) (.add (.var 1) (.neg (.var 0))))
      (.add (.mul (.var 0) (.var 1)) (.neg (.mul (.var 0) (.var 0))))
      (by decide) (fun | 0 => p | _ => f)
  exact Q'.eqv_trans _ _ _ (haar_of_coeff halg)
    (Q'.eqv_trans _ _ _ (quaternionHaar_append blocks _ _)
      (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr' hcross
          (Q'.eqv_trans _ _ _ (haar_neg blocks _)
            (Q'.neg_eqv_congr _ _ (Q'.eqv_refl _))))
        (Q'.add_neg_self_eqv _)))

/-- Exact finite-family Pythagoras on the original Haar carrier. -/
theorem family_square_decomposition (blocks : Nat) (ids : List Nat)
    (hids : ∀ i, i ∈ ids → i < blocks) (f : RatPoly) :
    quaternionHaar blocks (polyMul f f) ≈
      quaternionHaar blocks
          (polyMul (familyProject ids f) (familyProject ids f)) +
        quaternionHaar blocks
          (polyMul (familyResidual ids f) (familyResidual ids f)) := by
  let p := familyProject ids f
  let q := familyResidual ids f
  have hc : quaternionHaar blocks (polyMul p q) ≈ 0 :=
    projected_residual_orthogonal blocks ids hids f
  have halg : RatPolyCoeffEqv (polyMul f f)
      (polyAdd (polyMul p p) (polyAdd (polyMul q q)
        (polyAdd (polyMul p q) (polyMul p q)))) :=
    coeffEvalExpr_eqv_of_normalize_eq (.mul (.var 0) (.var 0))
      (.add (.mul (.var 1) (.var 1))
        (.add
          (.mul (.add (.var 0) (.neg (.var 1))) (.add (.var 0) (.neg (.var 1))))
          (.add
            (.mul (.var 1) (.add (.var 0) (.neg (.var 1))))
            (.mul (.var 1) (.add (.var 0) (.neg (.var 1)))))))
      (by decide) (fun | 0 => f | _ => p)
  have hz : quaternionHaar blocks (polyAdd (polyMul p q) (polyMul p q)) ≈ 0 :=
    Q'.eqv_trans _ _ _ (quaternionHaar_append blocks _ _)
      (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' hc hc) (by decide : (0 : Q') + 0 ≈ 0))
  exact Q'.eqv_trans _ _ _ (haar_of_coeff halg)
    (Q'.eqv_trans _ _ _ (quaternionHaar_append blocks _ _)
      (Q'.add_eqv_congr_left _ _ _
        (Q'.eqv_trans _ _ _ (quaternionHaar_append blocks _ _)
          (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ hz)
            (Q'.eqv_of_eq (Q'.add_zero' _))))))

/-- The residual square is nonnegative for every supported input. -/
theorem familyResidual_square_nonnegative {blocks : Nat} (ids : List Nat) {f : RatPoly}
    (hf : SupportedQuaternionBlocks blocks f) :
    0 ≤ quaternionHaar blocks
      (polyMul (familyResidual ids f) (familyResidual ids f)) :=
  Certificate.haar_nonnegative
    (.square (familyResidual ids f) (familyResidual_supported ids hf))

/-- The projected square is bounded by the original square, with coefficient one. -/
theorem familyProject_square_le (blocks : Nat) (ids : List Nat)
    (hids : ∀ i, i ∈ ids → i < blocks) (f : RatPoly)
    (hf : SupportedQuaternionBlocks blocks f) :
    quaternionHaar blocks
        (polyMul (familyProject ids f) (familyProject ids f)) ≤
      quaternionHaar blocks (polyMul f f) :=
  Q'.le_trans' _ _ _
    (Q'.add_le_self_of_nonneg _ _ (familyResidual_square_nonnegative ids hf))
    (Q'.ge_of_eqv (family_square_decomposition blocks ids hids f))

#print axioms familyResidual
#print axioms familyResidual_supported
#print axioms family_square_decomposition
#print axioms familyResidual_square_nonnegative
#print axioms familyProject_square_le

end YMGap.Continuum.SU2QuaternionHaarFamilyPythagoras
