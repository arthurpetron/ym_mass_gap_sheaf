/-
# Genuine Haar identities survive supported quaternion block embeddings

Supported Haar equality makes the square of the polynomial difference have
zero Haar integral. Conversely, positivity of the actual finite Haar form
makes such a difference pair to zero with every supported insertion. The
original block embedding preserves this square and its integral, so it
transports the EXISTING SupportedHaarEqv relation to the larger carrier.

The insertion may involve every target variable and interact with the
embedded source. No spectator independence or marginal factorization is
assumed. This is transport of observable identities under Haar, not an
identification of the ordinary Haar form with the reflected OS form.
-/

import YMGap.Continuum.SU2QuaternionHaarBlockEmbeddingAlgebra
import YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
import YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz

namespace YMGap.Continuum.SU2QuaternionHaarBlockEmbeddingSupportedEquality

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz
open YMGap.Continuum.GNSQuotient

local infix:50 " ≈ " => Q'.eqv

private theorem support_smul {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) (a : Q') :
    SupportedQuaternionBlocks blocks (polySmul a p) := by
  intro term ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

/-- No positivity is needed for this direction: test by the actual difference. -/
theorem difference_square_zero {blocks : Nat} {p q : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) (hq : SupportedQuaternionBlocks blocks q)
    (h : SupportedHaarEqv blocks p q) :
    quaternionHaar blocks
      (polyMul (polyAdd p (polySmul (-1) q)) (polyAdd p (polySmul (-1) q))) ≈ 0 := by
  let d := polyAdd p (polySmul (-1) q)
  have hd : SupportedQuaternionBlocks blocks d := supported_add hp (support_smul hq (-1))
  have hzero : SupportedHaarEqv blocks d polyZero :=
    (h.add (.refl blocks (polySmul (-1) q))).trans
      (.of_carrier (RatPolyCoeffEqv.haarCarrier (RatPolyCoeffEqv.add_neg_smul q)))
  exact Q'.eqv_trans _ _ _ (hzero d hd)
    (haar_of_coeff (RatPolyCoeffEqv.mul_zero_right d))

/-- The already proved positive Haar form turns square-nullity into every
supported insertion identity; no ordinary-Haar/OS identification is used. -/
theorem supportedHaarEqv_of_difference_square_zero {blocks : Nat} {p q : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) (hq : SupportedQuaternionBlocks blocks q)
    (h : quaternionHaar blocks
      (polyMul (polyAdd p (polySmul (-1) q)) (polyAdd p (polySmul (-1) q))) ≈ 0) :
    SupportedHaarEqv blocks p q := by
  let D := weightedGNSData blocks polyOne (Certificate.one blocks)
  let x : D.V := ⟨p, hp⟩
  let y : D.V := ⟨q, hq⟩
  have hz : D.rad x y :=
    Q'.eqv_trans _ _ _ (quaternionHaar_polyMul_one_right blocks _) h
  intro r hr
  have hpair := D.B_welldef (D.rad_refl (⟨r, hr⟩ : D.V)) hz
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (quaternionHaar_polyMul_one_right blocks _))
    (Q'.eqv_trans _ _ _ hpair (quaternionHaar_polyMul_one_right blocks _))

end YMGap.Continuum.SU2QuaternionHaarBlockEmbeddingSupportedEquality

namespace YMGap.Continuum.SU2QuaternionHaarBlockEmbedding.BlockEmbedding

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.SU2QuaternionHaarBlockEmbeddingSupportedEquality

/-- Source support and Haar equality imply equality against ALL supported
target insertions, including interacting factors outside the embedding image. -/
theorem polynomial_supportedHaar_congr {source target : Nat}
    (E : BlockEmbedding source target) {p q : RatPoly}
    (hp : SupportedQuaternionBlocks source p) (hq : SupportedQuaternionBlocks source q)
    (h : SupportedHaarEqv source p q) :
    SupportedHaarEqv target (E.polynomial p) (E.polynomial q) := by
  let d := polyAdd p (polySmul (-1) q)
  have hd : SupportedQuaternionBlocks source d :=
    supported_add hp (by
      intro term ht
      obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
      exact hq s hs)
  have hmap := E.haar (polyMul d d) (supported_polyMul hd hd)
  dsimp only [d] at hmap
  rw [E.polynomial_mul, E.polynomial_add, E.polynomial_smul] at hmap
  exact supportedHaarEqv_of_difference_square_zero
    (E.polynomial_supported p) (E.polynomial_supported q)
    (Q'.eqv_trans _ _ _ hmap (difference_square_zero hp hq h))

end YMGap.Continuum.SU2QuaternionHaarBlockEmbedding.BlockEmbedding

#print axioms YMGap.Continuum.SU2QuaternionHaarBlockEmbeddingSupportedEquality.difference_square_zero
#print axioms YMGap.Continuum.SU2QuaternionHaarBlockEmbeddingSupportedEquality.supportedHaarEqv_of_difference_square_zero
#print axioms YMGap.Continuum.SU2QuaternionHaarBlockEmbedding.BlockEmbedding.polynomial_supportedHaar_congr
