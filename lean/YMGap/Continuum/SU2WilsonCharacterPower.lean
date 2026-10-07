/-
# Wilson action, commit 1: powers of the trace in characters (Clebsch–Gordan / Catalan triangle)

(YM Group Realizer, J04 Wilson track.)  With `χ_s = characterPolynomial x s` (`χ_0 = 1`,
`χ_1 = 2x`, the trace when `x = u₀`):

* `chi1_mul_succ` : `χ_1 χ_{n+1} ≅ χ_{n+2} + χ_n` (the SU(2) Clebsch–Gordan rule `1 ⊗ s`).
* `mul_cc`        : `χ_1 · Σ_{s≤D} c_s χ_s  +  c_{D+1} χ_D  ≅  Σ_{s≤D+1} (up c)_s χ_s + Σ_{s≤D} (down c)_s χ_s`.
* `chiPow_expand` : `χ_1^k ≅ Σ_{s≤k} mult k s · χ_s`, where `mult (k+1) s = mult k (s-1) + mult k (s+1)`
  is the Catalan-triangle (ballot) multiplicity.
* `wilsonPoly_expand` : the truncated Wilson Taylor polynomial `T_K = Σ_{k≤K} a_k χ_1^k`, with
  `a_k = (β/2)^k/k!` passed as data, is exactly `Σ_{s≤K} wCoeff a K s · χ_s` with rational
  `wCoeff a K s = Σ_{k≤K} a_k · mult k s`.

All identities are `RatPolyCoeffEqv`, so they hold under every Haar functional.
-/

import YMGap.Continuum.SU2CharacterSquareIdentity

namespace YMGap.Continuum.SU2WilsonCharacterPower

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.SU2CharacterSquareIdentity (U envN chebE cheb_step norm v c ev)

local infix:50 " ≈ " => Q'.eqv
local infix:50 " ≅ " => RatPolyCoeffEqv

private theorem two_smul (x : RatPoly) :
    polySmul 2 x ≅ polyMul (polySmul (Q'.ofInt 2) polyOne) x :=
  ((RatPolyCoeffEqv.smul_coefficient (by decide) x).trans
    (RatPolyCoeffEqv.smul _ (RatPolyCoeffEqv.one_mul x).symm)).trans
    (RatPolyCoeffEqv.polyMul_smul_left _ _ _).symm

/-- Clebsch–Gordan `1 ⊗ (n+1) = (n+2) ⊕ n`. -/
theorem chi1_mul_succ (x : RatPoly) (n : Nat) :
    polyMul (U x 1) (U x (n + 1)) ≅ polyAdd (U x (n + 2)) (U x n) := by
  have h1 : polyMul (U x 1) (U x (n + 1)) ≅
      coeffEvalExpr (envN x n) (.mul (.mul (c 2) (v 0)) (v 2)) :=
    RatPolyCoeffEqv.mul (two_smul x) (RatPolyCoeffEqv.refl _)
  have h2 : polyAdd (U x (n + 2)) (U x n) ≅ coeffEvalExpr (envN x n) (.add chebE (v 1)) :=
    RatPolyCoeffEqv.add (cheb_step x n) (RatPolyCoeffEqv.refl _)
  exact (h1.trans (norm _ _ (by decide))).trans h2.symm

theorem add_smul (a b : Q') (p : RatPoly) :
    polySmul (a + b) p ≅ polyAdd (polySmul a p) (polySmul b p) := fun w =>
  Q'.eqv_trans _ _ _ (ratWeightedSum_smul w (a + b) p)
    (Q'.eqv_trans _ _ _ (Q'.add_mul_eqv a b _)
      (Q'.eqv_symm (Q'.eqv_trans _ _ _ (ratWeightedSum_add w _ _)
        (Q'.add_eqv_congr' (ratWeightedSum_smul w a p) (ratWeightedSum_smul w b p)))))

/-! ## Finite character combinations -/

/-- `Σ_{s≤D} c_s χ_s`. -/
def cc (x : RatPoly) (c : Nat → Q') : Nat → RatPoly
  | 0 => polySmul (c 0) (U x 0)
  | D + 1 => polyAdd (cc x c D) (polySmul (c (D + 1)) (U x (D + 1)))

def up (c : Nat → Q') : Nat → Q'
  | 0 => 0
  | s + 1 => c s

def down (c : Nat → Q') (s : Nat) : Q' := c (s + 1)

theorem cc_congr (x : RatPoly) {c c' : Nat → Q'} (h : ∀ s, c s ≈ c' s) : ∀ D, cc x c D ≅ cc x c' D
  | 0 => RatPolyCoeffEqv.smul_coefficient (h 0) _
  | D + 1 => RatPolyCoeffEqv.add (cc_congr x h D) (RatPolyCoeffEqv.smul_coefficient (h _) _)

theorem cc_add (x : RatPoly) (c c' : Nat → Q') :
    ∀ D, polyAdd (cc x c D) (cc x c' D) ≅ cc x (fun s => c s + c' s) D
  | 0 => (add_smul _ _ _).symm
  | D + 1 => (RatPolyCoeffEqv.four_add_swap _ _ _ _).trans
      (RatPolyCoeffEqv.add (cc_add x c c' D) (add_smul _ _ _).symm)

theorem cc_smul (x : RatPoly) (a : Q') (c : Nat → Q') :
    ∀ D, polySmul a (cc x c D) ≅ cc x (fun s => a * c s) D
  | 0 => RatPolyCoeffEqv.smul_assoc _ _ _
  | D + 1 => (RatPolyCoeffEqv.smul_add _ _ _).trans
      (RatPolyCoeffEqv.add (cc_smul x a c D) (RatPolyCoeffEqv.smul_assoc _ _ _))

/-- Zero padding. -/
theorem cc_pad (x : RatPoly) (c : Nat → Q') (D : Nat) (h : c (D + 1) ≈ 0) :
    cc x c D ≅ cc x c (D + 1) :=
  (RatPolyCoeffEqv.add_zero _).symm.trans (RatPolyCoeffEqv.add (RatPolyCoeffEqv.refl _)
    ((RatPolyCoeffEqv.smul_coefficient h _).trans (RatPolyCoeffEqv.zero_smul _)).symm)

/-- Multiplication by `χ_1` on a combination, with the boundary correction `c_{D+1} χ_D`. -/
theorem mul_cc (x : RatPoly) (c : Nat → Q') : ∀ D,
    polyAdd (polyMul (U x 1) (cc x c D)) (polySmul (c (D + 1)) (U x D)) ≅
      polyAdd (cc x (up c) (D + 1)) (cc x (down c) D)
  | 0 => by
    have hm : polyMul (U x 1) (polySmul (c 0) (U x 0)) ≅
        polyAdd (polySmul (up c 0) (U x 0)) (polySmul (c 0) (U x 1)) :=
      ((RatPolyCoeffEqv.polyMul_smul_right _ _ _).trans
        (RatPolyCoeffEqv.smul _ (RatPolyCoeffEqv.mul_one _))).trans
        ((RatPolyCoeffEqv.zero_add _).symm.trans
          (RatPolyCoeffEqv.add (RatPolyCoeffEqv.zero_smul _).symm (RatPolyCoeffEqv.refl _)))
    exact RatPolyCoeffEqv.add hm (RatPolyCoeffEqv.refl _)
  | D + 1 => by
    let A := U x 1
    let C := cc x c D
    let Q := polySmul (c (D + 1)) (U x (D + 2))
    let P := polySmul (c (D + 1)) (U x D)
    let R := polySmul (c (D + 2)) (U x (D + 1))
    let Up := cc x (up c) (D + 1)
    let Dn := cc x (down c) D
    let env : Nat → RatPoly := ev [A, C, Q, P, R, Up, Dn]
    have hX : polyMul A (polySmul (c (D + 1)) (U x (D + 1))) ≅ polyAdd Q P :=
      (RatPolyCoeffEqv.polyMul_smul_right _ _ _).trans
        ((RatPolyCoeffEqv.smul _ (chi1_mul_succ x D)).trans (RatPolyCoeffEqv.smul_add _ _ _))
    have s1 : polyAdd (polyMul A (polyAdd C (polySmul (c (D + 1)) (U x (D + 1))))) R ≅
        coeffEvalExpr env (.add (.add (.mul (v 0) (v 1)) (.add (v 2) (v 3))) (v 4)) :=
      RatPolyCoeffEqv.add ((RatPolyCoeffEqv.mul_add_right _ _ _).trans
        (RatPolyCoeffEqv.add (RatPolyCoeffEqv.refl _) hX)) (RatPolyCoeffEqv.refl _)
    have s2 : coeffEvalExpr env (.add (.add (.mul (v 0) (v 1)) (.add (v 2) (v 3))) (v 4)) ≅
        coeffEvalExpr env (.add (.add (.mul (v 0) (v 1)) (v 3)) (.add (v 2) (v 4))) :=
      norm _ _ (by decide)
    have s3 : coeffEvalExpr env (.add (.add (.mul (v 0) (v 1)) (v 3)) (.add (v 2) (v 4))) ≅
        coeffEvalExpr env (.add (.add (v 5) (v 6)) (.add (v 2) (v 4))) :=
      RatPolyCoeffEqv.add (mul_cc x c D) (RatPolyCoeffEqv.refl _)
    have s4 : coeffEvalExpr env (.add (.add (v 5) (v 6)) (.add (v 2) (v 4))) ≅
        coeffEvalExpr env (.add (.add (v 5) (v 2)) (.add (v 6) (v 4))) :=
      norm _ _ (by decide)
    exact ((s1.trans s2).trans s3).trans s4

/-! ## Powers of the trace -/

/-- Catalan-triangle multiplicity of `χ_s` in `χ_1^k`. -/
def mult : Nat → Nat → Q'
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | k + 1, s => up (mult k) s + down (mult k) s

theorem mult_vanish : ∀ k s, k < s → mult k s ≈ 0
  | 0, _ + 1, _ => Q'.eqv_refl _
  | k + 1, s + 1, h => by
    show mult k s + mult k (s + 2) ≈ 0
    exact Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (mult_vanish k s (by omega))
      (mult_vanish k (s + 2) (by omega))) (by decide)

/-- `χ_1^k`. -/
def chiPow (x : RatPoly) : Nat → RatPoly
  | 0 => polyOne
  | k + 1 => polyMul (U x 1) (chiPow x k)

theorem chiPow_expand (x : RatPoly) : ∀ k, chiPow x k ≅ cc x (mult k) k
  | 0 => (RatPolyCoeffEqv.one_smul _).symm
  | k + 1 => by
    have h1 : chiPow x (k + 1) ≅ polyAdd (polyMul (U x 1) (cc x (mult k) k))
        (polySmul (mult k (k + 1)) (U x k)) :=
      (RatPolyCoeffEqv.mul (RatPolyCoeffEqv.refl _) (chiPow_expand x k)).trans
        ((RatPolyCoeffEqv.add_zero _).symm.trans (RatPolyCoeffEqv.add (RatPolyCoeffEqv.refl _)
          ((RatPolyCoeffEqv.smul_coefficient (mult_vanish k (k + 1) (by omega)) _).trans
            (RatPolyCoeffEqv.zero_smul _)).symm))
    have h2 := mul_cc x (mult k) k
    have h3 : polyAdd (cc x (up (mult k)) (k + 1)) (cc x (down (mult k)) k) ≅ cc x (mult (k + 1)) (k + 1) :=
      (RatPolyCoeffEqv.add (RatPolyCoeffEqv.refl _)
        (cc_pad x _ k (mult_vanish k (k + 2) (by omega)))).trans (cc_add x _ _ (k + 1))
    exact (h1.trans h2).trans h3

/-! ## Truncated Wilson polynomial -/

/-- `T_K = Σ_{k≤K} a_k χ_1^k` (for Wilson, `a_k = (β/2)^k / k!`). -/
def wilsonPoly (x : RatPoly) (a : Nat → Q') : Nat → RatPoly
  | 0 => polySmul (a 0) (chiPow x 0)
  | K + 1 => polyAdd (wilsonPoly x a K) (polySmul (a (K + 1)) (chiPow x (K + 1)))

/-- Exact character coefficients `c_s^{(K)} = Σ_{k≤K} a_k mult k s`. -/
def wCoeff (a : Nat → Q') : Nat → Nat → Q'
  | 0, s => a 0 * mult 0 s
  | K + 1, s => wCoeff a K s + a (K + 1) * mult (K + 1) s

theorem wCoeff_vanish (a : Nat → Q') : ∀ K s, K < s → wCoeff a K s ≈ 0
  | 0, s, h => Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (mult_vanish 0 s h)) (Q'.mul_zero_eqv _)
  | K + 1, s, h => Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (wCoeff_vanish a K s (by omega))
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (mult_vanish (K + 1) s h)) (Q'.mul_zero_eqv _)))
      (by decide)

theorem wilsonPoly_expand (x : RatPoly) (a : Nat → Q') : ∀ K, wilsonPoly x a K ≅ cc x (wCoeff a K) K
  | 0 => (RatPolyCoeffEqv.smul _ (chiPow_expand x 0)).trans (cc_smul x _ _ 0)
  | K + 1 =>
    (RatPolyCoeffEqv.add ((wilsonPoly_expand x a K).trans (cc_pad x _ K (wCoeff_vanish a K (K + 1) (by omega))))
      ((RatPolyCoeffEqv.smul _ (chiPow_expand x (K + 1))).trans (cc_smul x _ _ (K + 1)))).trans
      (cc_add x _ _ (K + 1))

end YMGap.Continuum.SU2WilsonCharacterPower

#print axioms YMGap.Continuum.SU2WilsonCharacterPower.chi1_mul_succ
#print axioms YMGap.Continuum.SU2WilsonCharacterPower.chiPow_expand
#print axioms YMGap.Continuum.SU2WilsonCharacterPower.wilsonPoly_expand
