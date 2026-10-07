/-
# Rational Cauchy–Schwarz for Haar pairings with characters

(YM Group Realizer.)  From `H((tχ ∓ G)²) ≥ 0`:

  `2 t H(χG) ≤ t² H(χ²) + H(G²)`  and  `-(2 t H(χG)) ≤ t² H(χ²) + H(G²)`

for every rational `t` (`haar_cs_pos`, `haar_cs_neg`).  With
`plaq_character_square_le` and `t ≥ 0` this gives, for plaquette characters,
`±2t·h(χ_s G) ≤ t²(s+1)² + h(G²)` (`plaq_character_cs`), i.e. the
rational-friendly form of `|h(χ_s G)| ≤ (s+1) √h(G²)`.
-/

import YMGap.Continuum.SU2PlaqRadius

namespace YMGap.Continuum.SU2CharacterCauchySchwarz

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionGlobalFaceRatPolySupport
open YMGap.Continuum.SU2CharacterSquareIdentity
open YMGap.Continuum.SU2CharacterHaarBound
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SU2TorusMultiLinkPolyGibbs

local infix:50 " ≅ " => RatPolyCoeffEqv
local infix:50 " ≈ " => Q'.eqv

/-- Scalars pull out of the Haar functional. -/
theorem haar_pull (n : Nat) (q : Q') (M : RatPoly) : H n (polyMul (polySmul q polyOne) M) ≈ q * H n M :=
  Q'.eqv_trans _ _ _
    (haar_coeff ((RatPolyCoeffEqv.polyMul_smul_left q polyOne M).trans
      (RatPolyCoeffEqv.smul q (RatPolyCoeffEqv.one_mul M))) n)
    (YMGap.Continuum.BF4CompactActionCPOrder.quaternionHaar_polySmul n q M)

private def env3 (t : Q') (χ G : RatPoly) : Nat → RatPoly := ev [polySmul t polyOne, χ, G]

/-- `t² χ² + G²` with `T = t·1` atom. -/
private def rhsE : PolyExpr :=
  .add (.mul (v 0) (.mul (v 0) (.mul (v 1) (v 1)))) (.mul (v 2) (v 2))
private def crossE : PolyExpr := .mul (c 2) (.mul (v 0) (.mul (v 1) (v 2)))

private theorem core {n : Nat} (t : Q') (χ G : RatPoly)
    (hsq : (0 : Q') ≤ H n (coeffEvalExpr (env3 t χ G) (.add rhsE (.neg crossE)))) :
    Q'.ofInt 2 * (t * H n (polyMul χ G)) ≤ t * (t * H n (polyMul χ χ)) + H n (polyMul G G) := by
  have hX : H n (coeffEvalExpr (env3 t χ G) rhsE) ≈ t * (t * H n (polyMul χ χ)) + H n (polyMul G G) :=
    Q'.eqv_trans _ _ _ (haar_add n _ _)
      (Q'.add_eqv_congr' (Q'.eqv_trans _ _ _ (haar_pull n t _)
        (Q'.mul_eqv_congr_left _ _ _ (haar_pull n t _))) (Q'.eqv_refl _))
  have hY : H n (coeffEvalExpr (env3 t χ G) crossE) ≈ Q'.ofInt 2 * (t * H n (polyMul χ G)) :=
    Q'.eqv_trans _ _ _ (haar_pull n _ _) (Q'.mul_eqv_congr_left _ _ _ (haar_pull n t _))
  have h1 : (0 : Q') ≤ (t * (t * H n (polyMul χ χ)) + H n (polyMul G G)) +
      -(Q'.ofInt 2 * (t * H n (polyMul χ G))) :=
    Q'.le_trans' _ _ _ hsq (Q'.le_of_eqv (Q'.eqv_trans _ _ _ (haar_add n _ _)
      (Q'.add_eqv_congr' hX (Q'.eqv_trans _ _ _ (haar_neg n _) (Q'.neg_eqv_congr _ _ hY)))))
  exact Q'.le_of_sub_nonneg h1

private theorem sq_nonneg_of {n : Nat} (e : RatPoly) (P : RatPoly) (hP : SupportedCoordinates (4 * n) P)
    (he : e ≅ polyMul P P) : (0 : Q') ≤ H n e :=
  Q'.le_trans' _ _ _
    (YMGap.Continuum.SU2QuaternionArbitraryHaarPolynomialPositivity.quaternionHaar_square_nonnegative n P hP)
    (Q'.le_of_eqv (haar_coeff he.symm n))

/-- `2t·H(χG) ≤ t²H(χ²) + H(G²)`. -/
theorem haar_cs_pos {n : Nat} (t : Q') (χ G : RatPoly)
    (hχ : SupportedCoordinates (4 * n) χ) (hG : SupportedCoordinates (4 * n) G) :
    Q'.ofInt 2 * (t * H n (polyMul χ G)) ≤ t * (t * H n (polyMul χ χ)) + H n (polyMul G G) :=
  core t χ G (sq_nonneg_of _ (coeffEvalExpr (env3 t χ G) (.add (.mul (v 0) (v 1)) (.neg (v 2))))
    (supportedCoordinates_polyAdd (supportedCoordinates_polyMul
      (supportedCoordinates_polySmul _ (supportedCoordinates_polyOne _)) hχ)
      (supportedCoordinates_polyNeg hG))
    (norm (env := env3 t χ G) (.add rhsE (.neg crossE))
      (.mul (.add (.mul (v 0) (v 1)) (.neg (v 2))) (.add (.mul (v 0) (v 1)) (.neg (v 2)))) (by decide)))

/-- `-(2t·H(χG)) ≤ t²H(χ²) + H(G²)` (apply `core` to `-G`). -/
theorem haar_cs_neg {n : Nat} (t : Q') (χ G : RatPoly)
    (hχ : SupportedCoordinates (4 * n) χ) (hG : SupportedCoordinates (4 * n) G) :
    -(Q'.ofInt 2 * (t * H n (polyMul χ G))) ≤ t * (t * H n (polyMul χ χ)) + H n (polyMul G G) := by
  have h := core (n := n) t χ (polyNeg G) (sq_nonneg_of _
    (coeffEvalExpr (env3 t χ (polyNeg G)) (.add (.mul (v 0) (v 1)) (.neg (v 2))))
    (supportedCoordinates_polyAdd (supportedCoordinates_polyMul
      (supportedCoordinates_polySmul _ (supportedCoordinates_polyOne _)) hχ)
      (supportedCoordinates_polyNeg (supportedCoordinates_polyNeg hG)))
    (norm (env := env3 t χ (polyNeg G)) (.add rhsE (.neg crossE))
      (.mul (.add (.mul (v 0) (v 1)) (.neg (v 2))) (.add (.mul (v 0) (v 1)) (.neg (v 2)))) (by decide)))
  have eG : H n (polyMul (polyNeg G) (polyNeg G)) ≈ H n (polyMul G G) :=
    haar_coeff (norm (env := ev [G]) (.mul (.neg (v 0)) (.neg (v 0))) (.mul (v 0) (v 0)) (by decide)) n
  have eX : H n (polyMul χ (polyNeg G)) ≈ -(H n (polyMul χ G)) :=
    Q'.eqv_trans _ _ _
      (haar_coeff (norm (env := ev [χ, G]) (.mul (v 0) (.neg (v 1))) (.neg (.mul (v 0) (v 1))) (by decide)) n)
      (haar_neg n _)
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv ?_) (Q'.le_trans' _ _ _ h
    (Q'.le_of_eqv (Q'.add_eqv_congr' (Q'.eqv_refl _) eG)))
  refine Q'.eqv_symm (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_eqv_congr_left _ _ _ eX)) ?_)
  exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_neg_eqv t _)) (Q'.mul_neg_eqv _ _)

/-- **Plaquette form**: for `t ≥ 0`, `±2t·h(χ_s G) ≤ t²(s+1)² + h(G²)`. -/
theorem plaq_character_cs (links : List Z4Link) (N : Nat) (p : Z4Plaq)
    (hc : YMGap.Continuum.SU2PlaqWordHolonomy.LinksCover links N p) (s : Nat)
    (G : RatPoly) (hG : SupportedCoordinates (4 * links.length) G) (t : Q') (ht : (0 : Q') ≤ t) :
    let χ := plaqCharacter links N p s
    let h := (multiLinkHaar links.length).h
    let B := t * (t * Q'.ofInt (((s : Int) + 1) * ((s : Int) + 1))) + h (polyMul G G)
    Q'.ofInt 2 * (t * h (polyMul χ G)) ≤ B ∧ -(Q'.ofInt 2 * (t * h (polyMul χ G))) ≤ B := by
  intro χ h B
  have hs := YMGap.Continuum.SU2PlaqRadius.plaqWord_supp links N p hc
  have hχ : SupportedCoordinates (4 * links.length) χ :=
    supported_U links.length _ hs.1 s
  have hmono : t * (t * H links.length (polyMul χ χ)) + H links.length (polyMul G G) ≤ B :=
    Q'.add_le_add_right _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ _
        (YMGap.Continuum.SU2PlaqRadius.plaq_character_square_le links N p hc s) ht) ht)
  exact ⟨Q'.le_trans' _ _ _ (haar_cs_pos t χ G hχ hG) hmono,
    Q'.le_trans' _ _ _ (haar_cs_neg t χ G hχ hG) hmono⟩

end YMGap.Continuum.SU2CharacterCauchySchwarz

#print axioms YMGap.Continuum.SU2CharacterCauchySchwarz.haar_cs_pos
#print axioms YMGap.Continuum.SU2CharacterCauchySchwarz.haar_cs_neg
#print axioms YMGap.Continuum.SU2CharacterCauchySchwarz.plaq_character_cs
