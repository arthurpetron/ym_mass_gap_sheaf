/-
# Weighted character-square bound: `H((χ_s G)²) ≤ (s+1)² H(G²)`

(YM Group Realizer, R1 activity, part 1.)  For a polynomial quaternion
`(x, y1, y2, y3)` with Haar-trivial radius and ANY supported multiplier `G`,

  `H_n((U_s(x) G)²) ≤ (s+1)² H_n(G²)`     (`char_weighted_le`),

because `((s+1)² - U_s²) G² ≅ 4(1-x²) Σ_{k<s}(s-k)(U_k G)²` and
`4(1-x²)p² ~ Σ_i (2 y_i p)²` (`haar_Q_square_nonneg` with `p = U_k G`).
Plaquette instance `plaq_weighted_le` (only `LinksCover`).
-/

import YMGap.Continuum.SU2CharacterCauchySchwarz

namespace YMGap.Continuum.SU2PlaqWeightedCharacterBound

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction (HaarCarrierEqv)
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.SU2QuaternionGlobalFaceRatPolySupport
open YMGap.Continuum.SU2CharacterSquareIdentity
open YMGap.Continuum.SU2CharacterHaarBound
open YMGap.Continuum.SU2CharacterCauchySchwarz (haar_pull)
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SU2TorusMultiLinkPolyGibbs

local infix:50 " ≅ " => RatPolyCoeffEqv
local infix:50 " ≈ " => Q'.eqv

/-- `f` is `B`-bounded against every supported multiplier. -/
def Bnd (n : Nat) (f : RatPoly) (B : Q') : Prop :=
  ∀ G, SupportedCoordinates (4 * n) G →
    H n (polyMul (polyMul f G) (polyMul f G)) ≤ (B * B) * H n (polyMul G G)

theorem zle_of_eqv' {a b : Q'} (h : a ≈ b) (hb : (0 : Q') ≤ b) : (0 : Q') ≤ a :=
  Q'.le_trans' _ _ _ hb (Q'.le_of_eqv (Q'.eqv_symm h))

theorem add_mul_c (a b M : RatPoly) : polyMul (polyAdd a b) M ≅ polyAdd (polyMul a M) (polyMul b M) :=
  ((RatPolyCoeffEqv.mul_comm _ _).trans (RatPolyCoeffEqv.mul_add_right _ _ _)).trans
    (RatPolyCoeffEqv.add (RatPolyCoeffEqv.mul_comm _ _) (RatPolyCoeffEqv.mul_comm _ _))

theorem haar_add_mul (n : Nat) (a b M : RatPoly) :
    H n (polyMul (polyAdd a b) M) ≈ H n (polyMul a M) + H n (polyMul b M) :=
  Q'.eqv_trans _ _ _ (haar_coeff (add_mul_c a b M) n) (haar_add n _ _)

theorem ofInt_add' (a b : Int) : Q'.ofInt a + Q'.ofInt b ≈ Q'.ofInt (a + b) := by
  show (a * ((0 + 1 : Nat) : Int) + b * ((0 + 1 : Nat) : Int)) * ((0 + 1 : Nat) : Int) =
    (a + b) * (((0 + 1) * (0 + 1) - 1 + 1 : Nat) : Int)
  simp only [Nat.zero_add, Nat.mul_one, Nat.sub_self, Int.natCast_one, Int.mul_one]

theorem haar_K_mul (n : Nat) (M : RatPoly) :
    ∀ s, H n (polyMul (K s) M) ≈ Q'.ofInt (2 * s + 3) * H n M
  | 0 => haar_pull n _ M
  | s + 1 => Q'.eqv_trans _ _ _ (haar_add_mul n _ _ M)
      (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (haar_K_mul n M s) (haar_pull n _ M))
        (Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.add_mul_eqv _ _ _))
          (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_trans _ _ _ (ofInt_add' _ _) (by
            rw [show (2 * (s : Int) + 3 + 2) = 2 * ((s + 1 : Nat) : Int) + 3 by omega]
            exact Q'.eqv_refl _)))))

theorem haar_L_mul (n : Nat) (M : RatPoly) :
    ∀ s, H n (polyMul (L s) M) ≈ Q'.ofInt (((s : Int) + 1) * ((s : Int) + 1)) * H n M
  | 0 => haar_pull n _ M
  | s + 1 => Q'.eqv_trans _ _ _ (haar_add_mul n _ _ M)
      (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (haar_L_mul n M s) (haar_K_mul n M s))
        (Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.add_mul_eqv _ _ _))
          (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_trans _ _ _ (ofInt_add' _ _) (by
            rw [show (((s : Int) + 1) * ((s : Int) + 1) + (2 * (s : Int) + 3)) =
              (((s + 1 : Nat) : Int) + 1) * (((s + 1 : Nat) : Int) + 1) by
                rw [Int.natCast_add, Int.natCast_one]
                simp only [Int.add_mul, Int.mul_add, Int.one_mul, Int.mul_one]; omega]
            exact Q'.eqv_refl _)))))

section
variable {n : Nat} {x y1 y2 y3 : RatPoly}

private def e2 (a b : RatPoly) : Nat → RatPoly := ev [a, b]

/-- `(UU)(GG) ≅ (UG)(UG)`. -/
private theorem sq_regroup (a G : RatPoly) :
    polyMul (polyMul a a) (polyMul G G) ≅ polyMul (polyMul a G) (polyMul a G) :=
  norm (env := e2 a G) (.mul (.mul (v 0) (v 0)) (.mul (v 1) (v 1)))
    (.mul (.mul (v 0) (v 1)) (.mul (v 0) (v 1))) (by decide)

theorem haar_QT_G_nonneg (hr : HaarCarrierEqv n (radius x y1 y2 y3) polyOne)
    (hx : SupportedCoordinates (4 * n) x) (hy1 : SupportedCoordinates (4 * n) y1)
    (hy2 : SupportedCoordinates (4 * n) y2) (hy3 : SupportedCoordinates (4 * n) y3)
    (G : RatPoly) (hG : SupportedCoordinates (4 * n) G) :
    ∀ s, (0 : Q') ≤ H n (polyMul (Qx x) (polyMul (T x s) (polyMul G G)))
  | 0 => zle_of_eqv' (haar_coeff (RatPolyCoeffEqv.mul (RatPolyCoeffEqv.refl _) (sq_regroup _ G)) n)
      (haar_Q_square_nonneg n x y1 y2 y3 hr hy1 hy2 hy3 _
        (supportedCoordinates_polyMul (supported_U n x hx 0) hG))
  | s + 1 => zle_of_eqv'
      (Q'.eqv_trans _ _ _ (haar_coeff ((RatPolyCoeffEqv.mul (RatPolyCoeffEqv.refl _)
        (add_mul_c _ _ _)).trans (RatPolyCoeffEqv.mul_add_right _ _ _)) n) (haar_add n _ _))
      (Q'.zero_le_add _ _ (haar_QT_G_nonneg hr hx hy1 hy2 hy3 G hG s)
        (zle_of_eqv' (haar_coeff (RatPolyCoeffEqv.mul (RatPolyCoeffEqv.refl _) (sq_regroup _ G)) n)
          (haar_Q_square_nonneg n x y1 y2 y3 hr hy1 hy2 hy3 _
            (supportedCoordinates_polyMul (supported_U n x hx (s + 1)) hG))))

theorem haar_QS_G_nonneg (hr : HaarCarrierEqv n (radius x y1 y2 y3) polyOne)
    (hx : SupportedCoordinates (4 * n) x) (hy1 : SupportedCoordinates (4 * n) y1)
    (hy2 : SupportedCoordinates (4 * n) y2) (hy3 : SupportedCoordinates (4 * n) y3)
    (G : RatPoly) (hG : SupportedCoordinates (4 * n) G) :
    ∀ s, (0 : Q') ≤ H n (polyMul (Qx x) (polyMul (S x s) (polyMul G G)))
  | 0 => zle_of_eqv'
      (haar_coeff (norm (env := e2 x G) (.mul qE (.mul (c 0) (.mul (v 1) (v 1)))) (c 0) (by decide)) n)
      (Q'.le_of_eqv (Q'.eqv_symm (Q'.eqv_trans _ _ _ (QPoly.q_add_zero_eqv _)
        (Q'.zero_mul_eqv _))))
  | s + 1 => zle_of_eqv'
      (Q'.eqv_trans _ _ _ (haar_coeff ((RatPolyCoeffEqv.mul (RatPolyCoeffEqv.refl _)
        (add_mul_c _ _ _)).trans (RatPolyCoeffEqv.mul_add_right _ _ _)) n) (haar_add n _ _))
      (Q'.zero_le_add _ _ (haar_QS_G_nonneg hr hx hy1 hy2 hy3 G hG s)
        (haar_QT_G_nonneg hr hx hy1 hy2 hy3 G hG s))

/-- **Weighted bound**: `H((U_s G)²) ≤ (s+1)² H(G²)`. -/
theorem char_weighted_le (hr : HaarCarrierEqv n (radius x y1 y2 y3) polyOne)
    (hx : SupportedCoordinates (4 * n) x) (hy1 : SupportedCoordinates (4 * n) y1)
    (hy2 : SupportedCoordinates (4 * n) y2) (hy3 : SupportedCoordinates (4 * n) y3) (s : Nat) :
    Bnd n (U x s) (Q'.ofInt ((s : Int) + 1)) := by
  intro G hG
  -- H((L - UU) GG) = H(Q S GG) ≥ 0
  have hdef : (0 : Q') ≤ H n (polyMul (polyAdd (L s) (polyNeg (polyMul (U x s) (U x s)))) (polyMul G G)) :=
    zle_of_eqv' (Q'.eqv_trans _ _ _
      (haar_coeff (RatPolyCoeffEqv.mul (character_square_defect x s) (RatPolyCoeffEqv.refl _)) n)
      (haar_coeff (RatPolyCoeffEqv.mul_assoc _ _ _) n))
      (haar_QS_G_nonneg hr hx hy1 hy2 hy3 G hG s)
  have hsplit : H n (polyMul (polyAdd (L s) (polyNeg (polyMul (U x s) (U x s)))) (polyMul G G)) ≈
      Q'.ofInt (((s : Int) + 1) * ((s : Int) + 1)) * H n (polyMul G G) +
        -(H n (polyMul (polyMul (U x s) G) (polyMul (U x s) G))) :=
    Q'.eqv_trans _ _ _ (haar_add_mul n _ _ _)
      (Q'.add_eqv_congr' (haar_L_mul n _ s)
        (Q'.eqv_trans _ _ _
          (haar_coeff (norm (env := e2 (polyMul (U x s) (U x s)) G) (.mul (.neg (v 0)) (.mul (v 1) (v 1)))
            (.neg (.mul (v 0) (.mul (v 1) (v 1)))) (by decide)) n)
          (Q'.eqv_trans _ _ _ (haar_neg n _) (Q'.neg_eqv_congr _ _ (haar_coeff (sq_regroup _ G) n)))))
  have hle := Q'.le_of_sub_nonneg (Q'.le_trans' _ _ _ hdef (Q'.le_of_eqv hsplit))
  refine Q'.le_trans' _ _ _ hle (Q'.le_of_eqv (Q'.mul_eqv_congr_right _ _ _ ?_))
  show (((s : Int) + 1) * ((s : Int) + 1)) * ((0 + 1 : Nat) : Int) =
    (((s : Int) + 1) * ((s : Int) + 1)) * (((0 + 1) * (0 + 1) - 1 + 1 : Nat) : Int)
  rfl

end

/-- **Plaquette weighted bound** (all spins, any supported multiplier). -/
theorem plaq_weighted_le (links : List Z4Link) (N : Nat) (p : Z4Plaq)
    (hc : YMGap.Continuum.SU2PlaqWordHolonomy.LinksCover links N p) (s : Nat) :
    Bnd links.length (plaqCharacter links N p s) (Q'.ofInt ((s : Int) + 1)) :=
  have hs := YMGap.Continuum.SU2PlaqRadius.plaqWord_supp links N p hc
  char_weighted_le (YMGap.Continuum.SU2PlaqRadius.plaqWord_radius_carrier links N p hc)
    hs.1 hs.2.1 hs.2.2.1 hs.2.2.2 s

end YMGap.Continuum.SU2PlaqWeightedCharacterBound

#print axioms YMGap.Continuum.SU2PlaqWeightedCharacterBound.char_weighted_le
#print axioms YMGap.Continuum.SU2PlaqWeightedCharacterBound.plaq_weighted_le
