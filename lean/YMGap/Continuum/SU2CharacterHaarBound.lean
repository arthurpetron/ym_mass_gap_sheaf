/-
# Haar character-square bound `h(χ_s²) ≤ (s+1)²`, all spins

(YM Group Realizer, J04/R1 positivity, part B.)  For a quaternion-valued
polynomial `(x, y1, y2, y3)` whose radius is Haar-trivial,

  `HaarCarrierEqv n (x² + y1² + y2² + y3²) 1`,

every spin satisfies `0 ≤ H_n((s+1)² - χ_s(x)²)`, i.e.
`H_n(χ_s(x)²) ≤ (s+1)²` (`character_square_haar_le`).  Certificate:
`SU2CharacterSquareIdentity.character_square_defect` gives
`(s+1)² - U_s² ≅ 4(1-x²) Σ_{k<s}(s-k)U_k²`; modulo the radius relation
`4(1-x²)p² ~ Σ_i (2 y_i p)²`, a sum of Haar-nonnegative squares.

Instances: a single link `x = u_{4b}` (radius = block sphere,
`singleLink_character_square_le`); s = 1, 2 are the specialisations.
OPEN: for a plaquette word scalar the radius hypothesis needs the
multiplicativity `|q₁q₂q₃*q₄*|² ~ Π|q_i|²` under Haar (not proved here).
-/

import YMGap.Continuum.SU2CharacterSquareIdentity
import YMGap.Continuum.SU2QuaternionGlobalFaceRatPolySupport
import YMGap.Continuum.SU2QuaternionArbitraryHaarPolynomialPositivity
import YMGap.Continuum.SU2QuaternionFiniteProductHaarSphereIdeal
import YMGap.Continuum.SU2QuaternionOriginalHaarBlockMarginal
import YMGap.Continuum.SU2TorusMultiLinkPolyGibbs

namespace YMGap.Continuum.SU2CharacterHaarBound

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction (HaarCarrierEqv HaarCarrierEqv.refl
  HaarCarrierEqv.trans HaarCarrierEqv.symm HaarCarrierEqv.mul_left)
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer (ratWeightedSum)
open YMGap.Continuum.SU2QuaternionGlobalFaceRatPolySupport
open YMGap.Continuum.SU2CharacterSquareIdentity

local infix:50 " ≅ " => RatPolyCoeffEqv
local infix:50 " ≈ " => Q'.eqv

/-- Exact `n`-block Haar functional. -/
abbrev H (n : Nat) (p : RatPoly) : Q' := quaternionHaar n p

theorem haar_coeff {p q : RatPoly} (h : p ≅ q) (n : Nat) : H n p ≈ H n q := by
  have pin : ∀ r : RatPoly, quaternionHaar n r = ratWeightedSum (quaternionHaarMono n) r := by
    intro r
    induction r with
    | nil => rfl
    | cons t ts ih =>
        obtain ⟨m, q⟩ := t
        show q * _ + quaternionHaar n ts = q * _ + ratWeightedSum _ ts
        rw [ih]
  show quaternionHaar n p ≈ quaternionHaar n q
  rw [pin, pin]
  exact h _

theorem haar_carrier_one {n : Nat} {p q : RatPoly} (h : HaarCarrierEqv n p q) : H n p ≈ H n q :=
  Q'.eqv_trans _ _ _ (haar_coeff (RatPolyCoeffEqv.one_mul p).symm n)
    (Q'.eqv_trans _ _ _ (h polyOne) (haar_coeff (RatPolyCoeffEqv.one_mul q) n))

theorem haar_add (n : Nat) (p q : RatPoly) : H n (polyAdd p q) ≈ H n p + H n q :=
  YMGap.Continuum.BF4CompactActionCPOrder.quaternionHaar_append n p q

private theorem zle_of_eqv {a b : Q'} (h : a ≈ b) (hb : (0 : Q') ≤ b) : (0 : Q') ≤ a :=
  Q'.le_trans' _ _ _ hb (Q'.le_of_eqv (Q'.eqv_symm h))

/-- Radius polynomial of `(x, y1, y2, y3)`. -/
def radius (x y1 y2 y3 : RatPoly) : RatPoly :=
  polyAdd (polyAdd (polyAdd (polyMul x x) (polyMul y1 y1)) (polyMul y2 y2)) (polyMul y3 y3)

/-- `Q = 4 - 4x²` (the same polynomial as in the identity file). -/
abbrev Qx (x : RatPoly) : RatPoly := coeffEvalExpr (ev [x]) qE

section
variable (n : Nat) (x y1 y2 y3 : RatPoly)

private def e5 (p : RatPoly) : Nat → RatPoly := ev [x, y1, y2, y3, p]

private def sqE (e : PolyExpr) : PolyExpr := .mul e e
private def radE : PolyExpr :=
  .add (.add (.add (sqE (v 0)) (sqE (v 1))) (sqE (v 2))) (sqE (v 3))
private def holeE (h : PolyExpr) : PolyExpr :=
  .add (.mul (.mul (c 4) (sqE (v 4))) h) (.mul (c (-4)) (.mul (sqE (v 0)) (sqE (v 4))))
private def sosE : PolyExpr :=
  .add (.add (sqE (.mul (.mul (c 2) (v 1)) (v 4))) (sqE (.mul (.mul (c 2) (v 2)) (v 4))))
    (sqE (.mul (.mul (c 2) (v 3)) (v 4)))

private theorem one_bridge : polyOne ≅ polySmul (Q'.ofInt 1) polyOne :=
  (RatPolyCoeffEqv.one_smul polyOne).symm.trans
    (RatPolyCoeffEqv.smul_coefficient (by decide) polyOne)

/-- `H(Q p²) ≥ 0` given the radius relation. -/
theorem haar_Q_square_nonneg
    (hr : HaarCarrierEqv n (radius x y1 y2 y3) polyOne)
    (hy1 : SupportedCoordinates (4 * n) y1) (hy2 : SupportedCoordinates (4 * n) y2)
    (hy3 : SupportedCoordinates (4 * n) y3)
    (p : RatPoly) (hp : SupportedCoordinates (4 * n) p) :
    (0 : Q') ≤ H n (polyMul (Qx x) (polyMul p p)) := by
  have h1 : HaarCarrierEqv n (coeffEvalExpr (e5 x y1 y2 y3 p) (c 1))
      (coeffEvalExpr (e5 x y1 y2 y3 p) radE) :=
    (RatPolyCoeffEqv.haarCarrier one_bridge.symm).trans hr.symm
  have hA : HaarCarrierEqv n (polyMul (Qx x) (polyMul p p))
      (coeffEvalExpr (e5 x y1 y2 y3 p) sosE) :=
    ((RatPolyCoeffEqv.haarCarrier
      (norm (env := e5 x y1 y2 y3 p) (.mul qE (sqE (v 4))) (holeE (c 1)) (by decide))).trans
      (HaarCarrierEqv.add
        (HaarCarrierEqv.mul (HaarCarrierEqv.refl n _) h1) (HaarCarrierEqv.refl n _))).trans
      (RatPolyCoeffEqv.haarCarrier
        (norm (env := e5 x y1 y2 y3 p) (holeE radE) sosE (by decide)))
  have c2s : SupportedCoordinates (4 * n) (polySmul (Q'.ofInt 2) polyOne) :=
    supportedCoordinates_polySmul _ (supportedCoordinates_polyOne _)
  have sq : ∀ y, SupportedCoordinates (4 * n) y →
      (0 : Q') ≤ H n (polyMul (polyMul (polyMul (polySmul (Q'.ofInt 2) polyOne) y) p)
        (polyMul (polyMul (polySmul (Q'.ofInt 2) polyOne) y) p)) := fun y hy =>
    YMGap.Continuum.SU2QuaternionArbitraryHaarPolynomialPositivity.quaternionHaar_square_nonnegative
      n _ (supportedCoordinates_polyMul (supportedCoordinates_polyMul c2s hy) hp)
  refine zle_of_eqv (haar_carrier_one hA) ?_
  refine zle_of_eqv (haar_add n _ _) (Q'.zero_le_add _ _ ?_ (sq y3 hy3))
  exact zle_of_eqv (haar_add n _ _) (Q'.zero_le_add _ _ (sq y1 hy1) (sq y2 hy2))

theorem supported_U (hx : SupportedCoordinates (4 * n) x) :
    ∀ k, SupportedCoordinates (4 * n) (U x k)
  | 0 => supportedCoordinates_polyOne _
  | 1 => supportedCoordinates_polySmul _ hx
  | k + 2 => supportedCoordinates_polyAdd
      (supportedCoordinates_polyMul (supportedCoordinates_polySmul _ hx) (supported_U hx (k + 1)))
      (supportedCoordinates_polySmul _ (supported_U hx k))

variable {n x y1 y2 y3}

theorem haar_Q_T_nonneg (hr : HaarCarrierEqv n (radius x y1 y2 y3) polyOne)
    (hx : SupportedCoordinates (4 * n) x) (hy1 : SupportedCoordinates (4 * n) y1)
    (hy2 : SupportedCoordinates (4 * n) y2) (hy3 : SupportedCoordinates (4 * n) y3) :
    ∀ s, (0 : Q') ≤ H n (polyMul (Qx x) (T x s))
  | 0 => haar_Q_square_nonneg n x y1 y2 y3 hr hy1 hy2 hy3 _ (supported_U n x hx 0)
  | s + 1 => zle_of_eqv
      (Q'.eqv_trans _ _ _ (haar_coeff (RatPolyCoeffEqv.mul_add_right _ _ _) n) (haar_add n _ _))
      (Q'.zero_le_add _ _ (haar_Q_T_nonneg hr hx hy1 hy2 hy3 s)
        (haar_Q_square_nonneg n x y1 y2 y3 hr hy1 hy2 hy3 _ (supported_U n x hx (s + 1))))

theorem haar_Q_S_nonneg (hr : HaarCarrierEqv n (radius x y1 y2 y3) polyOne)
    (hx : SupportedCoordinates (4 * n) x) (hy1 : SupportedCoordinates (4 * n) y1)
    (hy2 : SupportedCoordinates (4 * n) y2) (hy3 : SupportedCoordinates (4 * n) y3) :
    ∀ s, (0 : Q') ≤ H n (polyMul (Qx x) (S x s))
  | 0 => zle_of_eqv
      (haar_coeff (norm (env := ev [x]) (.mul qE (c 0)) (c 0) (by decide)) n)
      (Q'.le_of_eqv (Q'.eqv_symm (Q'.eqv_trans _ _ _ (QPoly.q_add_zero_eqv _)
        (Q'.zero_mul_eqv _))))
  | s + 1 => zle_of_eqv
      (Q'.eqv_trans _ _ _ (haar_coeff (RatPolyCoeffEqv.mul_add_right _ _ _) n) (haar_add n _ _))
      (Q'.zero_le_add _ _ (haar_Q_S_nonneg hr hx hy1 hy2 hy3 s)
        (haar_Q_T_nonneg hr hx hy1 hy2 hy3 s))

/-- **`H((s+1)² - χ_s(x)²) ≥ 0`** for every spin (with `L s ≅ (s+1)²`). -/
theorem character_square_defect_nonneg (hr : HaarCarrierEqv n (radius x y1 y2 y3) polyOne)
    (hx : SupportedCoordinates (4 * n) x) (hy1 : SupportedCoordinates (4 * n) y1)
    (hy2 : SupportedCoordinates (4 * n) y2) (hy3 : SupportedCoordinates (4 * n) y3) (s : Nat) :
    (0 : Q') ≤ H n (polyAdd (L s) (polyNeg (polyMul (U x s) (U x s)))) :=
  zle_of_eqv (haar_coeff (character_square_defect x s) n) (haar_Q_S_nonneg hr hx hy1 hy2 hy3 s)

end

/-! ## Numeric form -/

theorem haar_const (n : Nat) (q : Q') : H n (polySmul q polyOne) ≈ q :=
  Q'.eqv_trans _ _ _ (QPoly.q_add_zero_eqv _)
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (quaternionHaarMono_one n))
      (Q'.eqv_trans _ _ _ (Q'.mul_one_eqv _) (Q'.mul_one_eqv _)))

private theorem ofInt_add (a b : Int) : Q'.ofInt a + Q'.ofInt b ≈ Q'.ofInt (a + b) := by
  show (a * ((0 + 1 : Nat) : Int) + b * ((0 + 1 : Nat) : Int)) * ((0 + 1 : Nat) : Int) =
    (a + b) * (((0 + 1) * (0 + 1) - 1 + 1 : Nat) : Int)
  simp only [Nat.zero_add, Nat.mul_one, Nat.sub_self, Int.natCast_one,
    Int.mul_one]

theorem haar_K (n : Nat) : ∀ s, H n (K s) ≈ Q'.ofInt (2 * s + 3)
  | 0 => haar_const n _
  | s + 1 => Q'.eqv_trans _ _ _ (haar_add n _ _)
      (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (haar_K n s) (haar_const n _))
        (Q'.eqv_trans _ _ _ (ofInt_add _ _) (by
          rw [show (2 * (s : Int) + 3 + 2) = 2 * ((s + 1 : Nat) : Int) + 3 by omega]
          exact Q'.eqv_refl _)))

theorem haar_L (n : Nat) : ∀ s, H n (L s) ≈ Q'.ofInt (((s : Int) + 1) * ((s : Int) + 1))
  | 0 => haar_const n _
  | s + 1 => Q'.eqv_trans _ _ _ (haar_add n _ _)
      (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (haar_L n s) (haar_K n s))
        (Q'.eqv_trans _ _ _ (ofInt_add _ _) (by
          rw [show (((s : Int) + 1) * ((s : Int) + 1) + (2 * (s : Int) + 3)) =
            (((s + 1 : Nat) : Int) + 1) * (((s + 1 : Nat) : Int) + 1) by
              rw [Int.natCast_add, Int.natCast_one]
              simp only [Int.add_mul, Int.mul_add, Int.one_mul, Int.mul_one]; omega]
          exact Q'.eqv_refl _)))

private theorem negOne_smul : ∀ p : RatPoly, polyNeg p ≅ polySmul (-1) p
  | [] => RatPolyCoeffEqv.refl polyZero
  | t :: rest => by
      intro w
      change (-t.2) * w t.1 + ratWeightedSum w (polyNeg rest) ≈
        ((-1) * t.2) * w t.1 + ratWeightedSum w (polySmul (-1) rest)
      have hc : -t.2 ≈ (-1) * t.2 := Q'.eqv_symm
        (Q'.eqv_trans _ (-(1 * t.2)) _ (Q'.neg_mul_eqv 1 t.2)
          (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv t.2)))
      exact Q'.add_eqv_congr' (Q'.mul_eqv_congr_right _ _ _ hc) (negOne_smul rest w)

theorem haar_neg (n : Nat) (p : RatPoly) : H n (polyNeg p) ≈ -(H n p) :=
  Q'.eqv_trans _ _ _ (haar_coeff (negOne_smul p) n)
    (Q'.eqv_trans _ _ _ (YMGap.Continuum.BF4CompactActionCPOrder.quaternionHaar_polySmul n (-1) p)
      (Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv 1 _) (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv _))))

/-- **Character-square bound**: `H_n(χ_s(x)²) ≤ (s+1)²` for every spin `s`. -/
theorem character_square_haar_le {n : Nat} {x y1 y2 y3 : RatPoly}
    (hr : HaarCarrierEqv n (radius x y1 y2 y3) polyOne)
    (hx : SupportedCoordinates (4 * n) x) (hy1 : SupportedCoordinates (4 * n) y1)
    (hy2 : SupportedCoordinates (4 * n) y2) (hy3 : SupportedCoordinates (4 * n) y3) (s : Nat) :
    H n (polyMul (characterPolynomial x s) (characterPolynomial x s)) ≤
      Q'.ofInt (((s : Int) + 1) * ((s : Int) + 1)) := by
  have h0 := character_square_defect_nonneg hr hx hy1 hy2 hy3 s
  have h1 : (0 : Q') ≤ H n (L s) + -(H n (polyMul (U x s) (U x s))) :=
    zle_of_eqv (Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.eqv_refl _) (Q'.eqv_symm (haar_neg n _)))
      (Q'.eqv_symm (haar_add n _ _))) h0
  exact Q'.le_trans' _ _ _ (Q'.le_of_sub_nonneg h1) (Q'.le_of_eqv (haar_L n s))

/-! ## Single link: the block sphere supplies the radius relation -/

private theorem varMono_sq : ∀ i, monoMul (varMono i) (varMono i) =
    YMGap.Continuum.SU2QuaternionFiniteProductHaarSphereIdeal.coordinateSquareMonomial i
  | 0 => rfl
  | i + 1 => by
      show (0 + 0) :: monoMul (varMono i) (varMono i) = _
      rw [varMono_sq i]; rfl

private theorem radius_block (b : Nat) :
    radius (polyVar (4 * b)) (polyVar (4 * b + 1)) (polyVar (4 * b + 2)) (polyVar (4 * b + 3)) ≅
      YMGap.Continuum.SU2QuaternionFiniteProductHaarSphereIdeal.quaternionBlockRadiusPolynomial b := by
  intro w
  show (1 * 1) * w (monoMul (varMono (4 * b)) (varMono (4 * b))) +
      ((1 * 1) * w (monoMul (varMono (4 * b + 1)) (varMono (4 * b + 1))) +
      ((1 * 1) * w (monoMul (varMono (4 * b + 2)) (varMono (4 * b + 2))) +
      ((1 * 1) * w (monoMul (varMono (4 * b + 3)) (varMono (4 * b + 3))) + 0))) ≈
    1 * w (YMGap.Continuum.SU2QuaternionFiniteProductHaarSphereIdeal.coordinateSquareMonomial (4 * b + 0)) +
      (1 * w (YMGap.Continuum.SU2QuaternionFiniteProductHaarSphereIdeal.coordinateSquareMonomial (4 * b + 1)) +
      (1 * w (YMGap.Continuum.SU2QuaternionFiniteProductHaarSphereIdeal.coordinateSquareMonomial (4 * b + 2)) +
      (1 * w (YMGap.Continuum.SU2QuaternionFiniteProductHaarSphereIdeal.coordinateSquareMonomial (4 * b + 3)) + 0)))
  rw [varMono_sq, varMono_sq, varMono_sq, varMono_sq]
  have e : ∀ m : List Nat, (1 * 1 : Q') * w m ≈ 1 * w m := fun m =>
    Q'.mul_eqv_congr_right _ _ _ (by decide)
  exact Q'.add_eqv_congr' (e _) (Q'.add_eqv_congr' (e _) (Q'.add_eqv_congr' (e _)
    (Q'.add_eqv_congr' (e _) (Q'.eqv_refl _))))

theorem block_radius_carrier {n b : Nat} (hb : b < n) :
    HaarCarrierEqv n
      (radius (polyVar (4 * b)) (polyVar (4 * b + 1)) (polyVar (4 * b + 2)) (polyVar (4 * b + 3)))
      polyOne := by
  intro ins
  refine Q'.eqv_trans _ _ _ (haar_coeff (RatPolyCoeffEqv.mul (RatPolyCoeffEqv.refl ins)
    (radius_block b)) n) ?_
  refine Q'.eqv_trans _ _ _
    (YMGap.Continuum.SU2QuaternionOriginalHaarBlockMarginal.quaternionHaar_eq_finiteProductHaar n _) ?_
  refine Q'.eqv_trans _ _ _
    (YMGap.Continuum.SU2QuaternionFiniteProductHaarSphereIdeal.finiteProductHaar_mul_blockRadius
      n b hb ins) ?_
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm
    (YMGap.Continuum.SU2QuaternionOriginalHaarBlockMarginal.quaternionHaar_eq_finiteProductHaar n _)) ?_
  exact haar_coeff (RatPolyCoeffEqv.mul_one ins).symm n

/-- **Single link, all spins**: `h(χ_s(U_b)²) ≤ (s+1)²` under `multiLinkHaar n`. -/
theorem singleLink_character_square_le {n b : Nat} (hb : b < n) (s : Nat) :
    (YMGap.Continuum.SU2TorusMultiLinkPolyGibbs.multiLinkHaar n).h
        (polyMul (characterPolynomial (polyVar (4 * b)) s) (characterPolynomial (polyVar (4 * b)) s)) ≤
      Q'.ofInt (((s : Int) + 1) * ((s : Int) + 1)) :=
  character_square_haar_le (block_radius_carrier hb)
    (supportedCoordinates_polyVar (by omega)) (supportedCoordinates_polyVar (by omega))
    (supportedCoordinates_polyVar (by omega)) (supportedCoordinates_polyVar (by omega)) s

/-- s = 1: `h(χ_1²) ≤ 4`. -/
theorem singleLink_spin1 {n b : Nat} (hb : b < n) :
    (YMGap.Continuum.SU2TorusMultiLinkPolyGibbs.multiLinkHaar n).h
        (polyMul (characterPolynomial (polyVar (4 * b)) 1) (characterPolynomial (polyVar (4 * b)) 1)) ≤
      Q'.ofInt 4 :=
  singleLink_character_square_le hb 1

/-- s = 2: `h(χ_2²) ≤ 9`. -/
theorem singleLink_spin2 {n b : Nat} (hb : b < n) :
    (YMGap.Continuum.SU2TorusMultiLinkPolyGibbs.multiLinkHaar n).h
        (polyMul (characterPolynomial (polyVar (4 * b)) 2) (characterPolynomial (polyVar (4 * b)) 2)) ≤
      Q'.ofInt 9 :=
  singleLink_character_square_le hb 2

end YMGap.Continuum.SU2CharacterHaarBound

#print axioms YMGap.Continuum.SU2CharacterHaarBound.character_square_defect_nonneg
#print axioms YMGap.Continuum.SU2CharacterHaarBound.character_square_haar_le
#print axioms YMGap.Continuum.SU2CharacterHaarBound.singleLink_character_square_le
#print axioms YMGap.Continuum.SU2CharacterHaarBound.singleLink_spin1
#print axioms YMGap.Continuum.SU2CharacterHaarBound.singleLink_spin2
