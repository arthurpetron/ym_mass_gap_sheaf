/-
# Core-B residual simplex / Bernstein certificates

The raw residual and even its square-difference quotient need not have
nonnegative coefficients.  The corrected finite certificate uses the physical
simplex

  a = 4h,  b = 4(w-h),  c = 1-4w,

so `a,b,c >= 0` when `0 <= h <= w` and `4w <= 1`.  For a quotient `q(w,h)`
of maximum degree `M`, every monomial is degree-elevated by
`(a+b+c)^(M-degree)`.  Since `a+b+c = 1`, this does not change its value,
while it can turn the coefficient table nonnegative.

This file implements the transformation reflectively, proves the generic
coefficientwise-positivity consumer, connects an all-index family of simplex
certificates to `SquareAbelCertificate`, and kernel-checks the base certificate
`(s,r) = (0,0)`.  It also checks the square factorization and degree bound for
the next offset `(0,1)`.  Its larger Bernstein table is deliberately not
expanded here; a smaller exact one-negative-monomial proof is supplied in
`CoreBResidualOffsetOne`.
-/

import YMGap.Continuum.CoreBResidualAbel
import YMGap.Constructive.Soundness
import Lean.Elab.Command
import Lean.LibrarySuggestions.SymbolFrequency

namespace YMGap.Continuum.CoreBResidualSimplex

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.AutoconvGershgorin
open YMGap.Continuum.CoreBStructuralRecurrence
open YMGap.Continuum.CoreBResidualPotential
open YMGap.Continuum.CoreBResidualAbel

local infix:50 " ≈ " => Q'.eqv

private theorem mul_eqv_congr₂ {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right a a' b ha)
    (Q'.mul_eqv_congr_left a' b b' hb)

private theorem rnqpow_eqv_qpow (x : Q') : ∀ n,
    RingNormaliser.qpow x n ≈ RGTransport.qpow x n
  | 0 => Q'.eqv_refl 1
  | n + 1 =>
      Q'.mul_eqv_congr_right _ _ x (rnqpow_eqv_qpow x n)

private theorem rnqpow_nonneg (x : Q') (hx : (0 : Q') ≤ x) : ∀ n,
    (0 : Q') ≤ RingNormaliser.qpow x n
  | 0 => by
      change (0 : Q') ≤ (1 : Q')
      decide
  | n + 1 => Q'.mul_nonneg _ _ (rnqpow_nonneg x hx n) hx

private theorem rnqpow_pos (x : Q') (hx : (0 : Q') < x) : ∀ n,
    (0 : Q') < RingNormaliser.qpow x n
  | 0 => by
      change (0 : Q') < (1 : Q')
      decide
  | n + 1 => Q'.mul_pos (rnqpow_pos x hx n) hx

private theorem rnqpow_mul (a b : Q') : ∀ n,
    RingNormaliser.qpow (a * b) n ≈
      RingNormaliser.qpow a n * RingNormaliser.qpow b n
  | 0 => Q'.eqv_symm (Q'.one_mul_eqv 1)
  | n + 1 => by
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ (a * b) (rnqpow_mul a b n)) ?_
      exact RingNormaliser.q_mul4_swap
        (RingNormaliser.qpow a n) (RingNormaliser.qpow b n) a b

private theorem rnqpow_one : ∀ n,
    RingNormaliser.qpow (1 : Q') n ≈ (1 : Q')
  | 0 => Q'.eqv_refl 1
  | n + 1 => Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ 1 (rnqpow_one n)) (Q'.one_mul_eqv 1)

private theorem rnqpow_four_ofNat : ∀ n,
    RingNormaliser.qpow (4 : Q') n ≈ Q'.ofNat (4 ^ n)
  | 0 => Q'.eqv_refl 1
  | n + 1 => by
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ (4 : Q') (rnqpow_four_ofNat n)) ?_
      have hm := Q'.eqv_symm
        (RingNormaliser.ofInt_mul (Int.ofNat (4 ^ n)) (4 : Int))
      simpa [Nat.pow_succ] using hm

/-! ## 1. Reflective syntax for arbitrary residual indices -/

private def sumExpr (f : Nat → RingNormaliser.PolyExpr) : Nat →
    RingNormaliser.PolyExpr
  | 0 => .const 0
  | n + 1 => .add (sumExpr f n) (f n)

private theorem eval_sumExpr (rho : Nat → Q')
    (f : Nat → RingNormaliser.PolyExpr) (g : Nat → Q')
    (hfg : ∀ i, RingNormaliser.eval rho (f i) ≈ g i) : ∀ n,
    RingNormaliser.eval rho (sumExpr f n) ≈ fsum g n
  | 0 => Q'.eqv_refl 0
  | n + 1 => Q'.add_eqv_congr' (eval_sumExpr rho f g hfg n) (hfg n)

private def coeffExpr (v j : Nat) : RingNormaliser.PolyExpr :=
  .mul (.const (Int.ofNat (j + 1))) (.pow (.var v) (c4 j))

private theorem eval_coeffExpr (rho : Nat → Q') (v j : Nat) :
    RingNormaliser.eval rho (coeffExpr v j) ≈ coeffW (rho v) j := by
  unfold coeffExpr coeffW dimQ
  exact Q'.mul_eqv_congr_left _ _ _ (rnqpow_eqv_qpow (rho v) (c4 j))

private def acExpr (v n t : Nat) : RingNormaliser.PolyExpr :=
  sumExpr (fun j => .mul (coeffExpr v j) (coeffExpr v (t - j))) n

private theorem eval_acExpr (rho : Nat → Q') (v n t : Nat) :
    RingNormaliser.eval rho (acExpr v n t) ≈ acN (rho v) n t := by
  unfold acExpr acN
  refine eval_sumExpr rho
    (fun j => .mul (coeffExpr v j) (coeffExpr v (t - j)))
    (fun j => coeffW (rho v) j * coeffW (rho v) (t - j)) ?_ n
  intro i
  exact mul_eqv_congr₂ (eval_coeffExpr rho v i) (eval_coeffExpr rho v (t - i))

private def windowExpr (v s k : Nat) : RingNormaliser.PolyExpr :=
  acExpr v (s + 1) (s + k)

private theorem eval_windowExpr (rho : Nat → Q') (v s k : Nat) :
    RingNormaliser.eval rho (windowExpr v s k) ≈ modeWindow (rho v) s k :=
  eval_acExpr rho v (s + 1) (s + k)

private def offsetAExpr (v s r : Nat) : RingNormaliser.PolyExpr :=
  .mul (windowExpr v s r) (windowExpr v s (r + 2))

private def offsetMExpr (v s r : Nat) : RingNormaliser.PolyExpr :=
  .mul (windowExpr v s (r + 1)) (windowExpr v s (r + 1))

private theorem eval_offsetAExpr (rho : Nat → Q') (v s r : Nat) :
    RingNormaliser.eval rho (offsetAExpr v s r) ≈ offsetA (rho v) s r :=
  mul_eqv_congr₂ (eval_windowExpr rho v s r)
    (eval_windowExpr rho v s (r + 2))

private theorem eval_offsetMExpr (rho : Nat → Q') (v s r : Nat) :
    RingNormaliser.eval rho (offsetMExpr v s r) ≈ offsetM (rho v) s r :=
  mul_eqv_congr₂ (eval_windowExpr rho v s (r + 1))
    (eval_windowExpr rho v s (r + 1))

/-- Reflective syntax for `offsetDelta w h s r`, with `w = var 0` and
`h = var 1`. -/
def offsetDeltaExpr (s r : Nat) : RingNormaliser.PolyExpr :=
  .add
    (.mul (offsetAExpr 0 s r) (offsetMExpr 1 s r))
    (.neg (.mul (offsetMExpr 0 s r) (offsetAExpr 1 s r)))

private theorem eval_offsetDeltaExpr (rho : Nat → Q') (s r : Nat) :
    RingNormaliser.eval rho (offsetDeltaExpr s r) ≈
      offsetDelta (rho 0) (rho 1) s r := by
  unfold offsetDeltaExpr offsetDelta determinant
  exact Q'.add_eqv_congr'
    (mul_eqv_congr₂ (eval_offsetAExpr rho 0 s r)
      (eval_offsetMExpr rho 1 s r))
    (Q'.neg_eqv_congr _ _
      (mul_eqv_congr₂ (eval_offsetMExpr rho 0 s r)
        (eval_offsetAExpr rho 1 s r)))

/-- Reflective syntax for `R_(s,r) = D_(s+1,r)-D_(s,r+1)`. -/
def residualExpr (s r : Nat) : RingNormaliser.PolyExpr :=
  .add (offsetDeltaExpr (s + 1) r) (.neg (offsetDeltaExpr s (r + 1)))

theorem boundaryResidualAt_eq_eval_residualExpr (w h : Q') (s r : Nat) :
    boundaryResidualAt w h s r ≈
      RingNormaliser.eval (fun i => if i = 0 then w else h) (residualExpr s r) := by
  let rho : Nat → Q' := fun i => if i = 0 then w else h
  have h1 := eval_offsetDeltaExpr rho (s + 1) r
  have h0 := eval_offsetDeltaExpr rho s (r + 1)
  have he : RingNormaliser.eval rho (residualExpr s r) ≈
      offsetDelta w h (s + 1) r + -(offsetDelta w h s (r + 1)) := by
    unfold residualExpr
    exact Q'.add_eqv_congr' h1 (Q'.neg_eqv_congr _ _ h0)
  exact Q'.eqv_trans _ _ _
    (boundaryResidualAt_eq_potential_difference w h s r) (Q'.eqv_symm he)

/-! ## 2. Antisymmetric square quotient -/

private def monoExprFrom : Nat → List Nat → RingNormaliser.PolyExpr
  | _, [] => .const 1
  | i, e :: es => .mul (.pow (.var i) e) (monoExprFrom (i + 1) es)

private def monoExpr (m : List Nat) : RingNormaliser.PolyExpr :=
  monoExprFrom 0 m

private def rawExpr : RingNormaliser.RawPoly → RingNormaliser.PolyExpr
  | [] => .const 0
  | (m, c) :: p => .add (.mul (.const c) (monoExpr m)) (rawExpr p)

private def exp0 : List Nat → Nat
  | [] => 0
  | e :: _ => e

private def exp1 : List Nat → Nat
  | [] => 0
  | _ :: [] => 0
  | _ :: e :: _ => e

private def quotientChain (c : Int) : Nat → Nat → Nat →
    RingNormaliser.RawPoly
  | _, _, 0 => []
  | ew, eh, n + 1 => ([ew - 2, eh], c) :: quotientChain c (ew - 2) (eh + 2) n

private def antisymSquareQuotientRaw (e : RingNormaliser.PolyExpr) :
    RingNormaliser.RawPoly :=
  (RingNormaliser.normalize e).flatMap (fun mc =>
    let ew := exp0 mc.1
    let eh := exp1 mc.1
    if eh < ew then quotientChain mc.2 ew eh ((ew - eh) / 2) else [])

/-- Candidate quotient obtained by dividing each upper-triangular
antisymmetric pair by `w^2-h^2`.  Its correctness is kernel-checked in each
certificate, so no unproved generic divisibility assumption is used. -/
def residualQuotientExpr (s r : Nat) : RingNormaliser.PolyExpr :=
  rawExpr (antisymSquareQuotientRaw (residualExpr s r))

private def squareFactorExpr (q : RingNormaliser.PolyExpr) :
    RingNormaliser.PolyExpr :=
  .mul (.add (.pow (.var 0) 2) (.neg (.pow (.var 1) 2))) q

/-! ## 3. Coefficientwise nonnegativity consumer -/

def RawCoefficientsNonnegative : RingNormaliser.RawPoly → Bool
  | [] => true
  | (_, c) :: p => decide ((0 : Int) ≤ c) && RawCoefficientsNonnegative p

theorem rawCoefficientsNonnegative_append : ∀ p q,
    RawCoefficientsNonnegative (p ++ q) =
      (RawCoefficientsNonnegative p && RawCoefficientsNonnegative q)
  | [], q => by simp [RawCoefficientsNonnegative]
  | (_, _) :: p, q => by
      simp [RawCoefficientsNonnegative, rawCoefficientsNonnegative_append,
        Bool.and_assoc]

theorem rawCoefficientsNonnegative_split (p : RingNormaliser.RawPoly) (n : Nat) :
    RawCoefficientsNonnegative p =
      (RawCoefficientsNonnegative (p.take n) &&
        RawCoefficientsNonnegative (p.drop n)) := by
  calc
    RawCoefficientsNonnegative p =
        RawCoefficientsNonnegative (p.take n ++ p.drop n) :=
      congrArg RawCoefficientsNonnegative (List.take_append_drop n p).symm
    _ = _ := rawCoefficientsNonnegative_append _ _

def CoefficientsNonnegative (e : RingNormaliser.PolyExpr) : Prop :=
  RawCoefficientsNonnegative (RingNormaliser.normalize e) = true

private instance (e : RingNormaliser.PolyExpr) :
    Decidable (CoefficientsNonnegative e) := by
  unfold CoefficientsNonnegative
  infer_instance

private theorem ofInt_nonneg {z : Int} (hz : (0 : Int) ≤ z) :
    (0 : Q') ≤ Q'.ofInt z := by
  rw [Q'.zero_le_iff_num_nonneg]
  exact hz

private theorem evalMonoFrom_nonneg (rho : Nat → Q')
    (hrho : ∀ i, (0 : Q') ≤ rho i) : ∀ i m,
    (0 : Q') ≤ RingNormaliser.evalMonoFrom rho i m
  | i, [] => by
      change (0 : Q') ≤ (1 : Q')
      decide
  | i, _ :: es =>
      Q'.mul_nonneg _ _
        (rnqpow_nonneg (rho i) (hrho i) _)
        (evalMonoFrom_nonneg rho hrho (i + 1) es)

private theorem evalRaw_nonneg (rho : Nat → Q')
    (hrho : ∀ i, (0 : Q') ≤ rho i) : ∀ p,
    RawCoefficientsNonnegative p = true →
      (0 : Q') ≤ RingNormaliser.evalRaw rho p
  | [], _ => Q'.le_refl' 0
  | (m, c) :: p, hp => by
      have hb : decide ((0 : Int) ≤ c) = true ∧
          RawCoefficientsNonnegative p = true := by
        simpa [RawCoefficientsNonnegative] using hp
      have hc : (0 : Int) ≤ c := of_decide_eq_true hb.1
      exact Q'.zero_le_add _ _
        (Q'.mul_nonneg _ _ (ofInt_nonneg hc)
          (evalMonoFrom_nonneg rho hrho 0 m))
        (evalRaw_nonneg rho hrho p hb.2)

theorem eval_nonneg_of_coefficients {rho : Nat → Q'}
    (hrho : ∀ i, (0 : Q') ≤ rho i) {e : RingNormaliser.PolyExpr}
    (he : CoefficientsNonnegative e) :
    (0 : Q') ≤ RingNormaliser.eval rho e := by
  have hn := evalRaw_nonneg rho hrho (RingNormaliser.normalize e) he
  exact Q'.le_trans' _ _ _ hn
    (Q'.ge_of_eqv (RingNormaliser.normalize_eval rho e))

/-! The stock normalizer canonicalizes only after fully expanding a power.
For Bernstein powers such as `(a+b)^60`, that creates an exponential
intermediate list.  `fastNormalize` uses the same proved raw operations but
canonicalizes after every multiplication. -/

private def fastPow (p : RingNormaliser.RawPoly) : Nat → RingNormaliser.RawPoly
  | 0 => [([], 1)]
  | n + 1 => RingNormaliser.canon
      (RingNormaliser.rawMul (fastPow p n) p)

private theorem evalRaw_fastPow (rho : Nat → Q')
    (p : RingNormaliser.RawPoly) : ∀ n,
    RingNormaliser.evalRaw rho (fastPow p n) ≈
      RingNormaliser.qpow (RingNormaliser.evalRaw rho p) n
  | 0 => by
      have h := RingNormaliser.eval_rawNormalize rho (.const 1)
      exact Q'.eqv_symm h
  | n + 1 => by
      refine Q'.eqv_trans _ _ _
        (RingNormaliser.evalRaw_canon rho
          (RingNormaliser.rawMul (fastPow p n) p)) ?_
      refine Q'.eqv_trans _ _ _
        (RingNormaliser.evalRaw_rawMul rho (fastPow p n) p) ?_
      exact Q'.mul_eqv_congr_right _ _ (RingNormaliser.evalRaw rho p)
        (evalRaw_fastPow rho p n)

/-- Semantics-preserving normalizer with eager canonicalization. -/
def fastNormalize : RingNormaliser.PolyExpr → RingNormaliser.RawPoly
  | .const c => [([], c)]
  | .var i => [(RingNormaliser.varMono i, 1)]
  | .add a b => RingNormaliser.canon (fastNormalize a ++ fastNormalize b)
  | .mul a b => RingNormaliser.canon
      (RingNormaliser.rawMul (fastNormalize a) (fastNormalize b))
  | .neg a => RingNormaliser.canon (RingNormaliser.rawNeg (fastNormalize a))
  | .pow a n => fastPow (fastNormalize a) n

theorem evalRaw_fastNormalize (rho : Nat → Q') : ∀ e,
    RingNormaliser.evalRaw rho (fastNormalize e) ≈ RingNormaliser.eval rho e
  | .const _ => Q'.eqv_symm (RingNormaliser.eval_rawNormalize rho (.const _))
  | .var _ => Q'.eqv_symm (RingNormaliser.eval_rawNormalize rho (.var _))
  | .add a b => by
      refine Q'.eqv_trans _ _ _
        (RingNormaliser.evalRaw_canon rho (fastNormalize a ++ fastNormalize b)) ?_
      refine Q'.eqv_trans _ _ _
        (RingNormaliser.evalRaw_append rho (fastNormalize a) (fastNormalize b)) ?_
      exact Q'.add_eqv_congr' (evalRaw_fastNormalize rho a)
        (evalRaw_fastNormalize rho b)
  | .mul a b => by
      refine Q'.eqv_trans _ _ _
        (RingNormaliser.evalRaw_canon rho
          (RingNormaliser.rawMul (fastNormalize a) (fastNormalize b))) ?_
      refine Q'.eqv_trans _ _ _
        (RingNormaliser.evalRaw_rawMul rho (fastNormalize a) (fastNormalize b)) ?_
      exact mul_eqv_congr₂ (evalRaw_fastNormalize rho a)
        (evalRaw_fastNormalize rho b)
  | .neg a => by
      refine Q'.eqv_trans _ _ _
        (RingNormaliser.evalRaw_canon rho
          (RingNormaliser.rawNeg (fastNormalize a))) ?_
      refine Q'.eqv_trans _ _ _
        (RingNormaliser.evalRaw_rawNeg rho (fastNormalize a)) ?_
      exact Q'.neg_eqv_congr _ _ (evalRaw_fastNormalize rho a)
  | .pow a n => Q'.eqv_trans _ _ _
      (evalRaw_fastPow rho (fastNormalize a) n)
      (RingNormaliser.qpow_eqv_congr (evalRaw_fastNormalize rho a) n)

theorem eval_nonneg_of_fast_coefficients {rho : Nat → Q'}
    (hrho : ∀ i, (0 : Q') ≤ rho i) {e : RingNormaliser.PolyExpr}
    (he : RawCoefficientsNonnegative (fastNormalize e) = true) :
    (0 : Q') ≤ RingNormaliser.eval rho e := by
  have hn := evalRaw_nonneg rho hrho (fastNormalize e) he
  exact Q'.le_trans' _ _ _ hn
    (Q'.le_of_eqv (evalRaw_fastNormalize rho e))

/-! ## 4. Simplex degree elevation -/

private def simplexTotalDegree (m : List Nat) : Nat := m.foldl Nat.add 0

/-- Every monomial uses at most the two variables `(w,h)` and has degree at
most `M`.  Trailing zero exponents are canonically omitted by the ring
normalizer, so constants and pure `w` powers appear as `[]` and `[ew]` rather
than `[0,0]` and `[ew,0]`.  This structural predicate accepts all three
canonical shapes and is kernel-decidable for a concrete normal form. -/
def TwoVariableDegreeBound (M : Nat) : RingNormaliser.RawPoly → Prop
  | [] => True
  | (([], _)) :: p => TwoVariableDegreeBound M p
  | (([ew], _)) :: p => ew ≤ M ∧ TwoVariableDegreeBound M p
  | (([ew, eh], _)) :: p => ew + eh ≤ M ∧ TwoVariableDegreeBound M p
  | _ :: _ => False

private def twoVariableDegreeBoundDecidable (M : Nat) : ∀ p,
    Decidable (TwoVariableDegreeBound M p)
  | [] => isTrue trivial
  | ([], _) :: p => twoVariableDegreeBoundDecidable M p
  | ([ew], _) :: p =>
      if hd : ew ≤ M then
        match twoVariableDegreeBoundDecidable M p with
        | isTrue hp => isTrue ⟨hd, hp⟩
        | isFalse hp => isFalse (fun h => hp h.2)
      else isFalse (fun h => hd h.1)
  | ([ew, eh], _) :: p =>
      if hd : ew + eh ≤ M then
        match twoVariableDegreeBoundDecidable M p with
        | isTrue hp => isTrue ⟨hd, hp⟩
        | isFalse hp => isFalse (fun h => hp h.2)
      else isFalse (fun h => hd h.1)
  | (_ :: _ :: _ :: _, _) :: _ => isFalse (fun h => h)

private instance (M : Nat) (p : RingNormaliser.RawPoly) :
    Decidable (TwoVariableDegreeBound M p) :=
  twoVariableDegreeBoundDecidable M p

private def simplexTerm (M : Nat) (mc : List Nat × Int) :
    RingNormaliser.PolyExpr :=
  let ew := exp0 mc.1
  let eh := exp1 mc.1
  let slack := M - simplexTotalDegree mc.1
  let ab := RingNormaliser.PolyExpr.add (.var 0) (.var 1)
  let abc := RingNormaliser.PolyExpr.add ab (.var 2)
  .mul (.const (mc.2 * Int.ofNat (4 ^ slack)))
    (.mul (.pow ab ew) (.mul (.pow (.var 0) eh) (.pow abc slack)))

private def plainSimplexTerm (M : Nat) (mc : List Nat × Int) :
    RingNormaliser.PolyExpr :=
  let ew := exp0 mc.1
  let eh := exp1 mc.1
  let slack := M - simplexTotalDegree mc.1
  let ab := RingNormaliser.PolyExpr.add (.var 0) (.var 1)
  .mul (.const (mc.2 * Int.ofNat (4 ^ slack)))
    (.mul (.pow ab ew) (.pow (.var 0) eh))

private def sumTermExpr
    (f : (List Nat × Int) → RingNormaliser.PolyExpr) :
    List (List Nat × Int) → RingNormaliser.PolyExpr
  | [] => .const 0
  | x :: xs => .add (f x) (sumTermExpr f xs)

/-- Homogenized `4^M q((a+b)/4,a/4)`, with every term degree-elevated by a
power of `a+b+c`. -/
def simplexHomogenize (q : RingNormaliser.PolyExpr) (M : Nat) :
    RingNormaliser.PolyExpr :=
  sumTermExpr (simplexTerm M) (RingNormaliser.normalize q)

/-- The tempting transform without `(a+b+c)` degree elevation. -/
def plainSimplexTransform (q : RingNormaliser.PolyExpr) (M : Nat) :
    RingNormaliser.PolyExpr :=
  sumTermExpr (plainSimplexTerm M) (RingNormaliser.normalize q)

private def simplexSubstitution : Nat → RingNormaliser.PolyExpr
  | 0 => .mul (.const 4) (.var 1)
  | 1 => .add (.mul (.const 4) (.var 0))
      (.neg (.mul (.const 4) (.var 1)))
  | 2 => .add (.const 1) (.neg (.mul (.const 4) (.var 0)))
  | _ => .const 0

/-! ## 5. Certificate and its consumers -/

/-- A completely kernel-checkable simplex/Bernstein certificate at one
residual index. -/
structure SimplexSquareCertificate (s r : Nat) : Type where
  degree : Nat
  factor_normal :
    RingNormaliser.normalize (residualExpr s r) =
      RingNormaliser.normalize (squareFactorExpr (residualQuotientExpr s r))
  coefficients_nonnegative :
    RawCoefficientsNonnegative
      (fastNormalize (simplexHomogenize (residualQuotientExpr s r) degree)) = true
  degree_bound :
    TwoVariableDegreeBound degree
      (RingNormaliser.normalize (residualQuotientExpr s r))

private def whEnv (w h : Q') : Nat → Q' :=
  fun i => if i = 0 then w else h

private def simplexPoint (w h : Q') : Nat → Q' :=
  fun i => RingNormaliser.eval (whEnv w h) (simplexSubstitution i)

private def pointAbL : RingNormaliser.PolyExpr :=
  .add (simplexSubstitution 0) (simplexSubstitution 1)

private def pointAbR : RingNormaliser.PolyExpr :=
  .mul (.const 4) (.var 0)

private def pointAbcL : RingNormaliser.PolyExpr :=
  .add pointAbL (simplexSubstitution 2)

private theorem pointAb_normal : RingNormaliser.normalize pointAbL =
    RingNormaliser.normalize pointAbR := by decide

private theorem pointAbc_normal : RingNormaliser.normalize pointAbcL =
    RingNormaliser.normalize (.const 1) := by decide

private theorem simplexPoint_ab (w h : Q') :
    simplexPoint w h 0 + simplexPoint w h 1 ≈ (4 : Q') * w := by
  have hn := RingNormaliser.poly_identity_of_normal_eq pointAbL pointAbR
    pointAb_normal (whEnv w h)
  simpa [pointAbL, pointAbR, simplexPoint] using hn

private theorem simplexPoint_abc (w h : Q') :
    (simplexPoint w h 0 + simplexPoint w h 1) + simplexPoint w h 2 ≈
      (1 : Q') := by
  have hn := RingNormaliser.poly_identity_of_normal_eq pointAbcL (.const 1)
    pointAbc_normal (whEnv w h)
  simpa [pointAbcL, pointAbL, simplexPoint] using hn

private def reorderSixL : RingNormaliser.PolyExpr :=
  .mul (.mul (.var 0) (.var 1))
    (.mul (.mul (.var 2) (.var 3))
      (.mul (.mul (.var 4) (.var 5)) (.const 1)))

private def reorderSixR : RingNormaliser.PolyExpr :=
  .mul (.mul (.mul (.var 1) (.var 2)) (.var 4))
    (.mul (.var 0) (.mul (.var 3) (.mul (.var 5) (.const 1))))

private theorem reorderSix_normal : RingNormaliser.normalize reorderSixL =
    RingNormaliser.normalize reorderSixR := by decide

private theorem reorder_six (c s e w f h : Q') :
    (c * s) * ((e * w) * ((f * h) * 1)) ≈
      ((s * e) * f) * (c * (w * (h * 1))) := by
  have hn := RingNormaliser.poly_identity_of_normal_eq reorderSixL reorderSixR
    reorderSix_normal (fun i => match i with
      | 0 => c | 1 => s | 2 => e | 3 => w | 4 => f | _ => h)
  simpa [reorderSixL, reorderSixR, RingNormaliser.eval] using hn

private theorem eval_simplexTerm_eq_scaled_mono
    (w h : Q') (M ew eh : Nat) (c : Int) (hdeg : ew + eh ≤ M) :
    RingNormaliser.eval (simplexPoint w h) (simplexTerm M ([ew, eh], c)) ≈
      RingNormaliser.qpow (4 : Q') M *
        (Q'.ofInt c * RingNormaliser.evalMono (whEnv w h) [ew, eh]) := by
  let slack := M - (ew + eh)
  have hM : (slack + ew) + eh = M := by
    dsimp [slack]
    omega
  have hc : Q'.ofInt (c * Int.ofNat (4 ^ slack)) ≈
      Q'.ofInt c * RingNormaliser.qpow (4 : Q') slack := by
    refine Q'.eqv_trans _ _ _
      (RingNormaliser.ofInt_mul c (Int.ofNat (4 ^ slack))) ?_
    exact Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm (rnqpow_four_ofNat slack))
  have hab : RingNormaliser.qpow
      (simplexPoint w h 0 + simplexPoint w h 1) ew ≈
      RingNormaliser.qpow (4 : Q') ew * RingNormaliser.qpow w ew :=
    Q'.eqv_trans _ _ _
      (RingNormaliser.qpow_eqv_congr (simplexPoint_ab w h) ew)
      (rnqpow_mul (4 : Q') w ew)
  have ha : RingNormaliser.qpow (simplexPoint w h 0) eh ≈
      RingNormaliser.qpow (4 : Q') eh * RingNormaliser.qpow h eh := by
    simpa [simplexPoint, simplexSubstitution, whEnv, RingNormaliser.eval] using
      (rnqpow_mul (4 : Q') h eh)
  have habc : RingNormaliser.qpow
      ((simplexPoint w h 0 + simplexPoint w h 1) + simplexPoint w h 2) slack ≈
      (1 : Q') :=
    Q'.eqv_trans _ _ _
      (RingNormaliser.qpow_eqv_congr (simplexPoint_abc w h) slack)
      (rnqpow_one slack)
  have hshape :
      RingNormaliser.eval (simplexPoint w h) (simplexTerm M ([ew, eh], c)) ≈
        (Q'.ofInt c * RingNormaliser.qpow (4 : Q') slack) *
          ((RingNormaliser.qpow (4 : Q') ew * RingNormaliser.qpow w ew) *
            ((RingNormaliser.qpow (4 : Q') eh * RingNormaliser.qpow h eh) * 1)) := by
    simpa [simplexTerm, simplexTotalDegree, slack, RingNormaliser.eval] using
      (mul_eqv_congr₂ hc (mul_eqv_congr₂ hab (mul_eqv_congr₂ ha habc)))
  have hscale :
      (RingNormaliser.qpow (4 : Q') slack * RingNormaliser.qpow (4 : Q') ew) *
          RingNormaliser.qpow (4 : Q') eh ≈
        RingNormaliser.qpow (4 : Q') M := by
    have hse : RingNormaliser.qpow (4 : Q') slack *
        RingNormaliser.qpow (4 : Q') ew ≈
          RingNormaliser.qpow (4 : Q') (slack + ew) :=
      Q'.eqv_symm (RingNormaliser.qpow_add (4 : Q') slack ew)
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ (RingNormaliser.qpow (4 : Q') eh) hse) ?_
    rw [← hM]
    exact Q'.eqv_symm (RingNormaliser.qpow_add (4 : Q') (slack + ew) eh)
  refine Q'.eqv_trans _ _ _ hshape ?_
  refine Q'.eqv_trans _ _ _
    (reorder_six (Q'.ofInt c) (RingNormaliser.qpow (4 : Q') slack)
      (RingNormaliser.qpow (4 : Q') ew) (RingNormaliser.qpow w ew)
      (RingNormaliser.qpow (4 : Q') eh) (RingNormaliser.qpow h eh)) ?_
  exact mul_eqv_congr₂ hscale (Q'.eqv_refl _)

private theorem eval_simplexTerm_nil_eq_scaled_mono
    (w h : Q') (M : Nat) (c : Int) :
    RingNormaliser.eval (simplexPoint w h) (simplexTerm M ([], c)) ≈
      RingNormaliser.qpow (4 : Q') M *
        (Q'.ofInt c * RingNormaliser.evalMono (whEnv w h) []) := by
  simpa [simplexTerm, simplexTotalDegree, exp0, exp1,
    RingNormaliser.evalMono, RingNormaliser.evalMonoFrom] using
      (eval_simplexTerm_eq_scaled_mono w h M 0 0 c (by omega))

private theorem eval_simplexTerm_singleton_eq_scaled_mono
    (w h : Q') (M ew : Nat) (c : Int) (hdeg : ew ≤ M) :
    RingNormaliser.eval (simplexPoint w h) (simplexTerm M ([ew], c)) ≈
      RingNormaliser.qpow (4 : Q') M *
        (Q'.ofInt c * RingNormaliser.evalMono (whEnv w h) [ew]) := by
  simpa [simplexTerm, simplexTotalDegree, exp0, exp1,
    RingNormaliser.evalMono, RingNormaliser.evalMonoFrom] using
      (eval_simplexTerm_eq_scaled_mono w h M ew 0 c (by omega))

private theorem eval_simplexSum_eq_scaledRaw (w h : Q') (M : Nat) : ∀ p,
    TwoVariableDegreeBound M p →
    RingNormaliser.eval (simplexPoint w h) (sumTermExpr (simplexTerm M) p) ≈
      RingNormaliser.qpow (4 : Q') M * RingNormaliser.evalRaw (whEnv w h) p
  | [], _ => Q'.eqv_symm (Q'.mul_zero_eqv _)
  | ([], c) :: p, hp => by
      have ht := eval_simplexTerm_nil_eq_scaled_mono w h M c
      have ih := eval_simplexSum_eq_scaledRaw w h M p hp
      refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' ht ih) ?_
      exact Q'.eqv_symm (Q'.mul_add_eqv (RingNormaliser.qpow (4 : Q') M)
        (Q'.ofInt c * RingNormaliser.evalMono (whEnv w h) [])
        (RingNormaliser.evalRaw (whEnv w h) p))
  | ([ew], c) :: p, hp => by
      have ht := eval_simplexTerm_singleton_eq_scaled_mono w h M ew c hp.1
      have ih := eval_simplexSum_eq_scaledRaw w h M p hp.2
      refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' ht ih) ?_
      exact Q'.eqv_symm (Q'.mul_add_eqv (RingNormaliser.qpow (4 : Q') M)
        (Q'.ofInt c * RingNormaliser.evalMono (whEnv w h) [ew])
        (RingNormaliser.evalRaw (whEnv w h) p))
  | ([ew, eh], c) :: p, hp => by
      have ht := eval_simplexTerm_eq_scaled_mono w h M ew eh c hp.1
      have ih := eval_simplexSum_eq_scaledRaw w h M p hp.2
      refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' ht ih) ?_
      exact Q'.eqv_symm (Q'.mul_add_eqv (RingNormaliser.qpow (4 : Q') M)
        (Q'.ofInt c * RingNormaliser.evalMono (whEnv w h) [ew, eh])
        (RingNormaliser.evalRaw (whEnv w h) p))
  | (_ :: _ :: _ :: _, _) :: _, hp => False.elim hp

private theorem simplexPoint_nonneg {w h : Q'}
    (hh0 : (0 : Q') ≤ h) (hhw : h ≤ w)
    (hwcap : (4 : Q') * w ≤ (1 : Q')) : ∀ i,
    (0 : Q') ≤ simplexPoint w h i := by
  have h4 : (0 : Q') ≤ (4 : Q') := by decide
  have h4h : (0 : Q') ≤ (4 : Q') * h := Q'.mul_nonneg _ _ h4 hh0
  have h4mono : (4 : Q') * h ≤ (4 : Q') * w :=
    Q'.mul_le_mul_of_nonneg_left h w 4 hhw h4
  have hgap : (0 : Q') ≤ (4 : Q') * w + -((4 : Q') * h) :=
    Q'.sub_nonneg_of_le h4mono
  have hslack : (0 : Q') ≤ (1 : Q') + -((4 : Q') * w) :=
    Q'.sub_nonneg_of_le hwcap
  intro i
  cases i with
  | zero => exact h4h
  | succ i =>
      cases i with
      | zero => exact hgap
      | succ i =>
          cases i with
          | zero => exact hslack
          | succ _ => exact Q'.le_refl' 0

private theorem scale_pos (M : Nat) :
    (0 : Q') < Q'.ofNat (4 ^ M) := by
  have hp : 0 < 4 ^ M := Nat.pow_pos (by decide)
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hp)
  rw [hk]
  exact Q'.ofNat_succ_pos k

/-- **Reusable reduced-simplex consumer.**  A two-variable polynomial `q`
whose degree-`M` physical-simplex elevation has nonnegative coefficients is
nonnegative at every `0 <= h <= w`, `4w <= 1`.

Unlike `quotient_nonneg_of_simplexCertificate`, this theorem is not tied to a
whole residual quotient.  It is designed for factor-aware certificates: first
remove a manifestly nonnegative common monomial from a large quotient, then
run the reflective simplex check only on the much smaller reduced polynomial.
This avoids the exponential intermediate table that defeated the monolithic
`(0,1)` certificate and is reusable at later offsets. -/
theorem eval_wh_nonneg_of_simplexData {w h : Q'}
    (hh0 : (0 : Q') ≤ h) (hhw : h ≤ w)
    (hwcap : (4 : Q') * w ≤ (1 : Q'))
    {q : RingNormaliser.PolyExpr} {M : Nat}
    (hcoeff : RawCoefficientsNonnegative
      (fastNormalize (simplexHomogenize q M)) = true)
    (hdegree : TwoVariableDegreeBound M (RingNormaliser.normalize q)) :
    (0 : Q') ≤
      RingNormaliser.eval (fun i => if i = 0 then w else h) q := by
  let H := simplexHomogenize q M
  have hH : (0 : Q') ≤ RingNormaliser.eval (simplexPoint w h) H :=
    eval_nonneg_of_fast_coefficients (simplexPoint_nonneg hh0 hhw hwcap) hcoeff
  have hraw := eval_simplexSum_eq_scaledRaw w h M
    (RingNormaliser.normalize q) hdegree
  have hn := RingNormaliser.normalize_eval (whEnv w h) q
  have hscaledEval :
      RingNormaliser.qpow (4 : Q') M * RingNormaliser.eval (whEnv w h) q ≈
        RingNormaliser.qpow (4 : Q') M *
          RingNormaliser.evalRaw (whEnv w h) (RingNormaliser.normalize q) :=
    Q'.mul_eqv_congr_left _ _ _ hn
  have hHscale : RingNormaliser.eval (simplexPoint w h) H ≈
      RingNormaliser.qpow (4 : Q') M * RingNormaliser.eval (whEnv w h) q :=
    Q'.eqv_trans _ _ _ hraw (Q'.eqv_symm hscaledEval)
  have hs0 : (0 : Q') ≤
      RingNormaliser.qpow (4 : Q') M * RingNormaliser.eval (whEnv w h) q :=
    Q'.le_trans' _ _ _ hH (Q'.le_of_eqv hHscale)
  have hmul : RingNormaliser.qpow (4 : Q') M * (0 : Q') ≤
      RingNormaliser.qpow (4 : Q') M * RingNormaliser.eval (whEnv w h) q :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.mul_zero_eqv (RingNormaliser.qpow (4 : Q') M))) hs0
  exact Q'.le_of_mul_le_mul_left hmul
    (rnqpow_pos (4 : Q') (by decide) M)

theorem quotient_nonneg_of_simplexCertificate {w h : Q'} {s r : Nat}
    (hh0 : (0 : Q') ≤ h) (hhw : h ≤ w)
    (hwcap : (4 : Q') * w ≤ (1 : Q'))
    (C : SimplexSquareCertificate s r) :
    (0 : Q') ≤
      RingNormaliser.eval (whEnv w h) (residualQuotientExpr s r) := by
  exact eval_wh_nonneg_of_simplexData hh0 hhw hwcap
    C.coefficients_nonnegative C.degree_bound

theorem residual_factor_of_simplexCertificate (w h : Q') {s r : Nat}
    (C : SimplexSquareCertificate s r) :
    boundaryResidualAt w h s r ≈
      (RingNormaliser.qpow w 2 + -(RingNormaliser.qpow h 2)) *
        RingNormaliser.eval (whEnv w h) (residualQuotientExpr s r) := by
  have hn := RingNormaliser.poly_identity_of_normal_eq _ _ C.factor_normal (whEnv w h)
  exact Q'.eqv_trans _ _ _ (boundaryResidualAt_eq_eval_residualExpr w h s r) hn

theorem residual_nonneg_of_simplexCertificate {w h : Q'} {s r : Nat}
    (hh0 : (0 : Q') ≤ h) (hhw : h ≤ w)
    (hwcap : (4 : Q') * w ≤ (1 : Q'))
    (C : SimplexSquareCertificate s r) :
    (0 : Q') ≤ boundaryResidualAt w h s r := by
  have hsq : (0 : Q') ≤
      RingNormaliser.qpow w 2 + -(RingNormaliser.qpow h 2) :=
    Q'.sub_nonneg_of_le
      (Q'.le_trans' _ _ _
        (Q'.le_of_eqv (rnqpow_eqv_qpow h 2))
        (Q'.le_trans' _ _ _ (HeatKernelGap.qpow_mono hh0 hhw 2)
          (Q'.ge_of_eqv (rnqpow_eqv_qpow w 2))))
  have hp := Q'.mul_nonneg _ _ hsq
    (quotient_nonneg_of_simplexCertificate hh0 hhw hwcap C)
  exact Q'.le_trans' _ _ _ hp
    (Q'.ge_of_eqv (residual_factor_of_simplexCertificate w h C))

/-- An all-index simplex family is exactly strong enough to construct the
previous square-Abel invariant. -/
def squareAbelOfSimplexFamily {w h : Q'}
    (hh0 : (0 : Q') ≤ h) (hhw : h ≤ w)
    (hwcap : (4 : Q') * w ≤ (1 : Q'))
    (F : ∀ s r, SimplexSquareCertificate s r) : SquareAbelCertificate w h where
  quotient := fun s r =>
    RingNormaliser.eval (whEnv w h) (residualQuotientExpr s r)
  quotient_nonneg := fun s r =>
    quotient_nonneg_of_simplexCertificate hh0 hhw hwcap (F s r)
  factor := fun s r => residual_factor_of_simplexCertificate w h (F s r)

theorem offsetDelta_nonneg_of_simplexFamily {w h : Q'}
    (hh0 : (0 : Q') ≤ h) (hhw : h ≤ w)
    (hwcap : (4 : Q') * w ≤ (1 : Q'))
    (F : ∀ s r, SimplexSquareCertificate s r) (s r : Nat) :
    (0 : Q') ≤ offsetDelta w h s r :=
  offsetDelta_nonneg_of_squareAbel hh0 hhw
    (squareAbelOfSimplexFamily hh0 hhw hwcap F) s r

/-! ## 6. Kernel-checked base and first shifted factor -/

theorem factorNormal00 :
    RingNormaliser.normalize (residualExpr 0 0) =
      RingNormaliser.normalize (squareFactorExpr (residualQuotientExpr 0 0)) := by
  decide

theorem coefficientsNonnegative00 :
    RawCoefficientsNonnegative
      (fastNormalize (simplexHomogenize (residualQuotientExpr 0 0) 32)) = true := by
  decide

def simplexCertificate00 : SimplexSquareCertificate 0 0 where
  degree := 32
  factor_normal := factorNormal00
  coefficients_nonnegative := coefficientsNonnegative00
  degree_bound := by decide

theorem factorNormal01 :
    RingNormaliser.normalize (residualExpr 0 1) =
      RingNormaliser.normalize (squareFactorExpr (residualQuotientExpr 0 1)) := by
  decide

theorem degreeBound01 :
    TwoVariableDegreeBound 56
      (RingNormaliser.normalize (residualQuotientExpr 0 1)) := by
  decide

theorem boundaryResidualAt_zero_one_factor (w h : Q') :
    boundaryResidualAt w h 0 1 ≈
      (RingNormaliser.qpow w 2 + -(RingNormaliser.qpow h 2)) *
        RingNormaliser.eval (whEnv w h) (residualQuotientExpr 0 1) := by
  have hn := RingNormaliser.poly_identity_of_normal_eq _ _ factorNormal01 (whEnv w h)
  exact Q'.eqv_trans _ _ _ (boundaryResidualAt_eq_eval_residualExpr w h 0 1) hn

#print axioms boundaryResidualAt_eq_eval_residualExpr
#print axioms rawCoefficientsNonnegative_append
#print axioms rawCoefficientsNonnegative_split
#print axioms eval_nonneg_of_coefficients
#print axioms evalRaw_fastNormalize
#print axioms eval_nonneg_of_fast_coefficients
#print axioms eval_wh_nonneg_of_simplexData
#print axioms quotient_nonneg_of_simplexCertificate
#print axioms residual_factor_of_simplexCertificate
#print axioms residual_nonneg_of_simplexCertificate
#print axioms squareAbelOfSimplexFamily
#print axioms offsetDelta_nonneg_of_simplexFamily
#print axioms simplexCertificate00
#print axioms factorNormal01
#print axioms degreeBound01
#print axioms boundaryResidualAt_zero_one_factor

/- Lean's optional premise-selection metadata traverses every theorem type when
this unusually large module is written.  Its default 200,000-heartbeat export
context can time out after all proofs have succeeded, emit a panic, and still
return a successful compiler status.  Populate the same metadata cache here,
under an unbounded heartbeat scope, so module export only reuses the completed
map.  This changes editor suggestions only; it does not participate in any
definition, theorem, certificate, or axiom. -/
set_option maxHeartbeats 0 in
run_cmd
  Lean.Elab.Command.liftTermElabM do
    let _ ← Lean.LibrarySuggestions.localSymbolFrequency
      ``boundaryResidualAt_zero_one_factor
    pure ()

end YMGap.Continuum.CoreBResidualSimplex
