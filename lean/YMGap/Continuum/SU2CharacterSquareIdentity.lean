/-
# Chebyshev square identity, all spins, as a coefficient identity

(YM Group Realizer, J04/R1 positivity, part A.)  For ANY polynomial `x`
(single-link coordinate or a plaquette-word scalar part), with
`U_s = characterPolynomial x s`, `Q = 4 - 4 x²`,

  `(s+1)² - U_s²  ≅  Q · S_s`,   `S_s = Σ_{k<s} (s-k) U_k²`

as `RatPolyCoeffEqv` (hence under every Haar functional).  Equivalently
`(s+1)² - U_s(x)² = 4(1-x²) Σ_{k<s} (s-k) U_k(x)²`.

Proof: three coupled inductions (the Cassini identity
`U_s² + U_{s+1}² - 2x U_s U_{s+1} = 1`, the partial-sum identity
`Q T_s = (2s+3) - U_{s+1}² + U_s²`, `T_s = Σ_{k≤s} U_k²`, and the target),
each step a fixed ring identity in seven atoms checked by the reflective
normaliser `coeffEvalExpr_eqv_of_normalize_eq` (`decide`), glued by
congruence.  Constants are carried as atoms `K_s = 2s+3`, `L_s = (s+1)²`.
-/

import YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
import YMGap.Continuum.BF4GeometricSpinNetworkMehler

namespace YMGap.Continuum.SU2CharacterSquareIdentity

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer (ratWeightedSum)

local infix:50 " ≈ " => Q'.eqv

local infix:50 " ≅ " => RatPolyCoeffEqv

/-! ## Generic reflective plumbing -/

/-- Substitution of expressions for variables. -/
def substE (σ : Nat → PolyExpr) : PolyExpr → PolyExpr
  | .const c => .const c
  | .var i => σ i
  | .add a b => .add (substE σ a) (substE σ b)
  | .mul a b => .mul (substE σ a) (substE σ b)
  | .neg a => .neg (substE σ a)
  | .pow a k => .pow (substE σ a) k

theorem coeffEvalExpr_subst (env : Nat → RatPoly) (σ : Nat → PolyExpr) :
    ∀ e, coeffEvalExpr env (substE σ e) = coeffEvalExpr (fun i => coeffEvalExpr env (σ i)) e
  | .const _ => rfl
  | .var _ => rfl
  | .add a b => by
      show polyAdd _ _ = polyAdd _ _
      rw [coeffEvalExpr_subst env σ a, coeffEvalExpr_subst env σ b]
  | .mul a b => by
      show polyMul _ _ = polyMul _ _
      rw [coeffEvalExpr_subst env σ a, coeffEvalExpr_subst env σ b]
  | .neg a => by
      show polyNeg _ = polyNeg _
      rw [coeffEvalExpr_subst env σ a]
  | .pow a k => by
      show coeffPolyPow _ k = coeffPolyPow _ k
      rw [coeffEvalExpr_subst env σ a]

theorem coeffEvalExpr_env_congr {env env' : Nat → RatPoly} (h : ∀ i, env i ≅ env' i) :
    ∀ e, coeffEvalExpr env e ≅ coeffEvalExpr env' e
  | .const _ => RatPolyCoeffEqv.refl _
  | .var i => h i
  | .add a b => RatPolyCoeffEqv.add (coeffEvalExpr_env_congr h a) (coeffEvalExpr_env_congr h b)
  | .mul a b => RatPolyCoeffEqv.mul (coeffEvalExpr_env_congr h a) (coeffEvalExpr_env_congr h b)
  | .neg a => RatPolyCoeffEqv.neg (coeffEvalExpr_env_congr h a)
  | .pow a k => coeffPolyPow_congr (coeffEvalExpr_env_congr h a) k

/-- Transport along atom relations, then a normaliser check. -/
theorem transport {env env' : Nat → RatPoly} (σ : Nat → PolyExpr)
    (hσ : ∀ i, env' i ≅ coeffEvalExpr env (σ i)) (e g : PolyExpr)
    (hn : normalize (substE σ e) = normalize g) :
    coeffEvalExpr env' e ≅ coeffEvalExpr env g := by
  refine (coeffEvalExpr_env_congr hσ e).trans ?_
  rw [← coeffEvalExpr_subst]
  exact coeffEvalExpr_eqv_of_normalize_eq _ _ hn env

theorem norm {env : Nat → RatPoly} (e g : PolyExpr) (hn : normalize e = normalize g) :
    coeffEvalExpr env e ≅ coeffEvalExpr env g :=
  coeffEvalExpr_eqv_of_normalize_eq _ _ hn env

/-! ## Data -/

section
variable (x : RatPoly)

abbrev U (k : Nat) : RatPoly := characterPolynomial x k

/-- `T_s = Σ_{k≤s} U_k²`. -/
def T : Nat → RatPoly
  | 0 => polyMul (U x 0) (U x 0)
  | n + 1 => polyAdd (T n) (polyMul (U x (n + 1)) (U x (n + 1)))

/-- `S_s = Σ_{k<s} (s-k) U_k²`. -/
def S : Nat → RatPoly
  | 0 => polySmul (Q'.ofInt 0) polyOne
  | n + 1 => polyAdd (S n) (T x n)

end

/-- `K_s = 2s+3`. -/
def K : Nat → RatPoly
  | 0 => polySmul (Q'.ofInt 3) polyOne
  | n + 1 => polyAdd (K n) (polySmul (Q'.ofInt 2) polyOne)

/-- `L_s = (s+1)²`. -/
def L : Nat → RatPoly
  | 0 => polySmul (Q'.ofInt 1) polyOne
  | n + 1 => polyAdd (L n) (K n)

def ev (l : List RatPoly) (i : Nat) : RatPoly := l.getD i polyZero

/-- Atoms at level `n`: `x, U_n, U_{n+1}, T_n, S_n, K_n, L_n`. -/
def envN (x : RatPoly) (n : Nat) : Nat → RatPoly :=
  ev [x, U x n, U x (n + 1), T x n, S x n, K n, L n]

/-! ## Expressions -/

def v (i : Nat) : PolyExpr := .var i
def c (k : Int) : PolyExpr := .const k
def qE : PolyExpr := .add (c 4) (.mul (c (-4)) (.mul (v 0) (v 0)))
def chebE : PolyExpr := .add (.mul (.mul (c 2) (v 0)) (v 2)) (.neg (v 1))
/-- Cassini: `A² + B² - 2xAB`. -/
def fE : PolyExpr :=
  .add (.add (.mul (v 1) (v 1)) (.mul (v 2) (v 2))) (.mul (c (-2)) (.mul (v 0) (.mul (v 1) (v 2))))
/-- `Q T`. -/
def eL : PolyExpr := .mul qE (v 3)
/-- `K - B² + A²`. -/
def eR : PolyExpr := .add (.add (v 5) (.neg (.mul (v 2) (v 2)))) (.mul (v 1) (v 1))
/-- `L - A²`. -/
def dL : PolyExpr := .add (v 6) (.neg (.mul (v 1) (v 1)))
/-- `Q S`. -/
def dR : PolyExpr := .mul qE (v 4)

/-- Level-step substitution. -/
def σs : Nat → PolyExpr
  | 0 => v 0 | 1 => v 2 | 2 => chebE
  | 3 => .add (v 3) (.mul (v 2) (v 2))
  | 4 => .add (v 4) (v 3)
  | 5 => .add (v 5) (c 2)
  | 6 => .add (v 6) (v 5)
  | i => v i

/-! ## Atom bridges -/

private theorem negOne_smul : ∀ p : RatPoly, polySmul (-1) p ≅ polyNeg p
  | [] => RatPolyCoeffEqv.refl polyZero
  | t :: rest => by
      intro w
      change ((-1) * t.2) * w t.1 + ratWeightedSum w (polySmul (-1) rest) ≈
        (-t.2) * w t.1 + ratWeightedSum w (polyNeg rest)
      have hc : (-1) * t.2 ≈ -t.2 :=
        Q'.eqv_trans _ (-(1 * t.2)) _ (Q'.neg_mul_eqv 1 t.2)
          (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv t.2))
      exact Q'.add_eqv_congr' (Q'.mul_eqv_congr_right _ _ _ hc) (negOne_smul rest w)

private theorem two_smul (x : RatPoly) :
    polySmul 2 x ≅ polyMul (polySmul (Q'.ofInt 2) polyOne) x :=
  ((RatPolyCoeffEqv.smul_coefficient (by decide) x).trans
    (RatPolyCoeffEqv.smul _ (RatPolyCoeffEqv.one_mul x).symm)).trans
    (RatPolyCoeffEqv.polyMul_smul_left _ _ _).symm

theorem cheb_step (x : RatPoly) (n : Nat) :
    U x (n + 2) ≅ coeffEvalExpr (envN x n) chebE :=
  RatPolyCoeffEqv.add (RatPolyCoeffEqv.mul (two_smul x) (RatPolyCoeffEqv.refl _))
    (negOne_smul _)

theorem envN_step (x : RatPoly) (n : Nat) :
    ∀ i, envN x (n + 1) i ≅ coeffEvalExpr (envN x n) (σs i)
  | 0 => RatPolyCoeffEqv.refl _
  | 1 => RatPolyCoeffEqv.refl _
  | 2 => cheb_step x n
  | 3 => RatPolyCoeffEqv.refl _
  | 4 => RatPolyCoeffEqv.refl _
  | 5 => RatPolyCoeffEqv.refl _
  | 6 => RatPolyCoeffEqv.refl _
  | _ + 7 => RatPolyCoeffEqv.refl _

/-- Base atoms in terms of `x` alone. -/
def σ0 : Nat → PolyExpr
  | 0 => v 0 | 1 => c 1 | 2 => .mul (c 2) (v 0)
  | 3 => .mul (c 1) (c 1) | 4 => c 0 | 5 => c 3 | 6 => c 1
  | i => v (i + 100)

private theorem one_bridge : polyOne ≅ polySmul (Q'.ofInt 1) polyOne :=
  (RatPolyCoeffEqv.one_smul polyOne).symm.trans
    (RatPolyCoeffEqv.smul_coefficient (by decide) polyOne)

theorem envN_base (x : RatPoly) : ∀ i, envN x 0 i ≅ coeffEvalExpr (ev [x]) (σ0 i)
  | 0 => RatPolyCoeffEqv.refl _
  | 1 => one_bridge
  | 2 => two_smul x
  | 3 => RatPolyCoeffEqv.mul one_bridge one_bridge
  | 4 => RatPolyCoeffEqv.refl _
  | 5 => RatPolyCoeffEqv.refl _
  | 6 => RatPolyCoeffEqv.refl _
  | _ + 7 => RatPolyCoeffEqv.refl _

/-! ## The three inductions -/

theorem cassini (x : RatPoly) : ∀ n, coeffEvalExpr (envN x n) fE ≅ coeffEvalExpr (envN x n) (c 1)
  | 0 =>
      (transport σ0 (envN_base x) fE (c 1) (by decide)).trans
        (transport σ0 (envN_base x) (c 1) (c 1) (by decide)).symm
  | n + 1 =>
      (transport σs (envN_step x n) fE fE (by decide)).trans
        ((cassini x n).trans (transport σs (envN_step x n) (c 1) (c 1) (by decide)).symm)

/-- `W` with `Q T + Q B² ≅ W + 2·fE` and `W + 2 ≅ eR[σs]`. -/
private def wE : PolyExpr :=
  .add (.add (.add (v 5) (.mul (v 2) (v 2))) (.neg (.mul (v 1) (v 1))))
    (.add (.mul (c (-4)) (.mul (.mul (v 0) (v 0)) (.mul (v 2) (v 2))))
      (.mul (c 4) (.mul (v 0) (.mul (v 1) (v 2)))))

theorem partialSum (x : RatPoly) : ∀ n, coeffEvalExpr (envN x n) eL ≅ coeffEvalExpr (envN x n) eR
  | 0 =>
      (transport σ0 (envN_base x) eL (substE σ0 eR) (by decide)).trans
        (transport σ0 (envN_base x) eR (substE σ0 eR) (by decide)).symm
  | n + 1 => by
      refine (transport σs (envN_step x n) eL (.add eL (.mul qE (.mul (v 2) (v 2)))) (by decide)).trans ?_
      refine (RatPolyCoeffEqv.add (partialSum x n) (RatPolyCoeffEqv.refl _)).trans ?_
      refine (norm (env := envN x n) (.add eR (.mul qE (.mul (v 2) (v 2)))) (.add wE (.mul (c 2) fE))
        (by decide)).trans ?_
      refine (RatPolyCoeffEqv.add (RatPolyCoeffEqv.refl _)
        (RatPolyCoeffEqv.mul (RatPolyCoeffEqv.refl _) (cassini x n))).trans ?_
      exact (transport σs (envN_step x n) eR (.add wE (.mul (c 2) (c 1))) (by decide)).symm

theorem squareDefect (x : RatPoly) : ∀ n, coeffEvalExpr (envN x n) dL ≅ coeffEvalExpr (envN x n) dR
  | 0 =>
      (transport σ0 (envN_base x) dL (substE σ0 dR) (by decide)).trans
        (transport σ0 (envN_base x) dR (substE σ0 dR) (by decide)).symm
  | n + 1 => by
      refine (transport σs (envN_step x n) dL (.add dL eR) (by decide)).trans ?_
      refine (RatPolyCoeffEqv.add (squareDefect x n) (partialSum x n).symm).trans ?_
      exact (transport σs (envN_step x n) dR (.add dR eL) (by decide)).symm

/-- **Main identity**: `L_s - U_s² ≅ (4 - 4x²) · S_s`, i.e.
`(s+1)² - U_s(x)² = 4(1-x²) Σ_{k<s}(s-k) U_k(x)²`. -/
theorem character_square_defect (x : RatPoly) (s : Nat) :
    polyAdd (L s) (polyNeg (polyMul (U x s) (U x s))) ≅
      polyMul (polyAdd (polySmul (Q'.ofInt 4) polyOne)
        (polyMul (polySmul (Q'.ofInt (-4)) polyOne) (polyMul x x))) (S x s) :=
  squareDefect x s

end YMGap.Continuum.SU2CharacterSquareIdentity

#print axioms YMGap.Continuum.SU2CharacterSquareIdentity.cassini
#print axioms YMGap.Continuum.SU2CharacterSquareIdentity.partialSum
#print axioms YMGap.Continuum.SU2CharacterSquareIdentity.character_square_defect
