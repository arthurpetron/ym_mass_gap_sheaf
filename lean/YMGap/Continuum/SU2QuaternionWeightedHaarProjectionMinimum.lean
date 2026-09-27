/-
# Weighted free-coordinate least squares with an independent background

The original polynomial Haar background may contain interactions among every
other coordinate. Independence from the selected block is the only property
used here. The conclusion is a finite weighted square comparison, not an
interacting conditional projection or a spatial rate.
-/

import YMGap.Continuum.SU2QuaternionHaarBlockProjection
import YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz
import YMGap.Continuum.GNSCompletion

namespace YMGap.Continuum.SU2QuaternionWeightedHaarProjectionMinimum

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
open YMGap.Continuum.SU2QuaternionHaarBlockProjection
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz
open YMGap.Continuum.GNSQuotient

local infix:50 " ≈ " => Q'.eqv

private theorem support_neg {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) :
    SupportedQuaternionBlocks blocks (polyNeg p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

private theorem orthogonal_sum_lower (D : GNSData) (u v : D.V)
    (h : D.B u v ≈ 0) : D.B u u ≤ D.B (D.add u v) (D.add u v) := by
  have hsym : D.B v u ≈ 0 :=
    Q'.eqv_trans _ _ _ (D.B_symm v u) h
  have he : D.B (D.add u v) (D.add u v) ≈ D.B u u + D.B v v :=
    Q'.eqv_trans _ _ _ (D.B_add_diag_expand u v)
      (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr'
          (Q'.add_eqv_congr' (Q'.eqv_refl _) h)
          (Q'.add_eqv_congr' hsym (Q'.eqv_refl _)))
        (poly_identity_of_normal_eq
          (.add (.add (.var 0) (.const 0)) (.add (.const 0) (.var 1)))
          (.add (.var 0) (.var 1)) (by decide)
          (fun | 0 => D.B u u | _ => D.B v v)))
  exact Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg _ _ (D.self_nonneg v))
    (Q'.ge_of_eqv he)

/-- The free fluctuation minimizes the retained-background weighted square
among all exterior approximants. The selected-block-independent weight is
not replaced by a product-Haar or pointwise numerical bound. -/
theorem weighted_fluctuation_le_difference (blocks i : Nat) (hi : i < blocks)
    (B p q : RatPoly) (P : Certificate blocks B)
    (hp : SupportedQuaternionBlocks blocks p)
    (hq : SupportedQuaternionBlocks blocks q)
    (hqi : QuaternionBlockIndependent i q)
    (hBi : QuaternionBlockIndependent i B) :
    quaternionHaar blocks
        (polyMul (polyMul (fluctuation i p) (fluctuation i p)) B) ≤
      quaternionHaar blocks
        (polyMul (polyMul (polyAdd p (polyNeg q))
          (polyAdd p (polyNeg q))) B) := by
  let r := fluctuation i p
  let e := polyAdd (project i p) (polyNeg q)
  let f := polyAdd p (polyNeg q)
  let D := weightedGNSData blocks B P
  have heSupport : SupportedQuaternionBlocks blocks e :=
    supported_add (project_supported i hp) (support_neg hq)
  have hfSupport : SupportedQuaternionBlocks blocks f :=
    supported_add hp (support_neg hq)
  let xr : D.V := ⟨r, fluctuation_supported i hp⟩
  let xe : D.V := ⟨e, heSupport⟩
  let xf : D.V := ⟨f, hfSupport⟩
  have heIndependent : QuaternionBlockIndependent i e :=
    quaternionBlockIndependent_polyAdd (project_independent i p)
      (quaternionBlockIndependent_polyNeg hqi)
  have hcross : D.B xr xe ≈ 0 := by
    have h0 := fluctuation_orthogonal blocks i hi p (polyMul B e)
      (quaternionBlockIndependent_polyMul hBi heIndependent)
    have hc : RatPolyCoeffEqv (polyMul (polyMul r e) B) (polyMul (polyMul B e) r) :=
      coeffEvalExpr_eqv_of_normalize_eq
        (.mul (.mul (.var 0) (.var 1)) (.var 2))
        (.mul (.mul (.var 2) (.var 1)) (.var 0))
        (by decide) (fun | 0 => r | 1 => e | _ => B)
    exact Q'.eqv_trans _ _ _ (haar_of_coeff hc) h0
  have hd : D.veq (D.add xr xe) xf := by
    change RatPolyCoeffEqv (polyAdd r e) f
    unfold r e f fluctuation
    exact coeffEvalExpr_eqv_of_normalize_eq
      (.add (.add (.var 0) (.neg (.var 2)))
        (.add (.var 2) (.neg (.var 1))))
      (.add (.var 0) (.neg (.var 1)))
      (by decide) (fun | 0 => p | 1 => q | _ => project i p)
  exact Q'.le_trans' _ _ _ (orthogonal_sum_lower D xr xe hcross)
    (Q'.le_of_eqv (D.B_diag_congr hd))

end YMGap.Continuum.SU2QuaternionWeightedHaarProjectionMinimum

#print axioms YMGap.Continuum.SU2QuaternionWeightedHaarProjectionMinimum.weighted_fluctuation_le_difference
