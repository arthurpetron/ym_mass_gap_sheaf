/-
Heat-kernel pointwise positivity, Part 4 (gap G1, the `ϑ₃`-factor) — building
the Jacobi theta partial PRODUCT

    ϑ₃(x) = ∏_{n≥1} (1 − a^{2n})·(1 + 2·a^{2n-1}·x + a^{4n-2})

as a GENUINE convergent `CReal` with an EXPLICIT Cauchy modulus, and combining it
with the `S`-factor `CReal` of `Continuum/HeatKernelConv.lean` to assemble the
full manifestly-nonnegative object `R(x) = (ϑ₃/2a)·S(x) ≥ 0` UNCONDITIONALLY
(modulo only the separate G2 identity `K_t = R`), removing the last
"`Θ` is hypothetical" caveat from `HKConv.R_geRat_zero_of_theta`.

# What this module closes (the deliverable)

`Continuum/HeatKernelConv.lean` built the `S`-factor as a convergent `CReal`
`sConvCReal` (under `a·a ≤ 1/2`), and `HKConv.R_geRat_zero_of_theta` closed
`Θ·S ≥ 0` GIVEN any `CReal` `Θ` realizing `ϑ₃/2a` with nonneg approximations.
The OTHER factor `ϑ₃` is a partial PRODUCT, not a sum.  This module builds it.

The `k`-th full Jacobi factor (`k = n−1 ≥ 0`) is

    gFac a x k = (1 − a^{2k+2})·factor (a^{2k+1}) x
               = (1 − a^{2k+2})·(1 + 2 a^{2k+1} x + a^{4k+2}),

every factor `> 0` (by `HKPos.factor_pos` and `a^{2k+2} < 1`).  The partial
products `Ppart a x L = ∏_{k<L} gFac a x k` are fed to the KP engine
`Continuum.crealOfGeoIncrement`, which wants a two-sided SINGLE-STEP geometric
increment bound `|Ppart (l+1) − Ppart l| ≤ C·(1/2)^l`.

# The increment bound (the subtlety)

`Ppart (l+1) − Ppart l = Ppart l · (gFac a x l − 1)`.  We bound this in two
independent steps:

  * **Per-factor deviation** `|gFac a x l − 1| ≤ D·(1/2)^l` (two-sided).  Writing
    `c = a^{2l+1}`, `u = a^{2l+2} = a·c`, one has
    `gFac − 1 = 2c·x + c·c − u·factor`, and under `−1 ≤ x ≤ 1`, `a·a ≤ 1/2`,
    each piece is `O((1/2)^l)`; we collect the crude constant `D = 7` and prove
    `−7·(1/2)^l ≤ gFac − 1 ≤ 7·(1/2)^l` from `c ≤ a·(1/2)^l ≤ (1/2)^l`.

  * **Partial-product magnitude bound** `Ppart a x l ≤ B`, an explicit constant.
    Each `gFac` is dominated by `1 + T k`, `T k = 2c + c² ≥ 0`, and the Weierstrass
    product estimate `∏(1+T)·∏(1−T) ≤ 1` together with the lower bound
    `∏(1−T) ≥ 1 − Σ T` gives `∏(1+T) ≤ 2` once `Σ T ≤ 1/2`.  The smallness
    `Σ_{k} T_k ≤ 1/2` is the binding hypothesis on `a`; it holds for `a ≤ 1/16`
    (a clean robust sufficient condition, proved here via geometric series).

Then `C = B·D = 2·7 = 14` and `crealOfGeoIncrement` delivers `thetaConvCReal`.

# What is BUILT here

  * `prodUpBound` — the abstract Weierstrass bound `∏_{k<L}(1+T_k) ≤ 2` from
    `0 ≤ T_k` and `∀ L, finSum T L ≤ 1/2`.
  * `thetaConvCReal a x (…)` — `ϑ₃(x)` as a `CReal` under
    `0 < a`, `a < 1`, `−1 ≤ x`, `x ≤ 1`, `a·a ≤ 1/2`, and the smallness
    `∀ L, finSum (Tcoef a) L ≤ 1/2`, with `approx N = Ppart a x N` and the
    explicit `HalfPow` modulus inherited from `crealOfGeoIncrement`.
  * `thetaConvCReal_approx_nonneg` — every approximation is `≥ 0`.
  * `R_geRat_zero` — the assembled `R = ϑ₃·S ≥ 0`, the `Θ`-hypothesis of
    `HKConv.R_geRat_zero_of_theta` now discharged by `thetaConvCReal`.
  * `Tcoef_sum_small_of_le_sixteenth` — the smallness hypothesis holds for
    `a ≤ 1/16`.

# The precise remaining gap (honest, per AGENTS.md Rule 6)

  (smallness regime) `ϑ₃` is built under `∀ L, finSum (Tcoef a) L ≤ 1/2`
       (sufficient: `a ≤ 1/16`).  The increment ratio uses only `a·a ≤ 1/2`; the
       smallness is needed solely for the product-MAGNITUDE bound `B`.  Lifting
       to all `a ∈ (0,1)` is the same `a`-dependent-cutoff extension named in
       `HeatKernelConv` (mechanical but lengthy) and is not done here.

  (G2) The IDENTITY `K_t(x) = (ϑ₃/2a)·S(x)` (differentiated Jacobi triple
       product) remains the separate analytic gap named in `HeatKernelPos2`.

Everything below is fully proved and axiom-gated (`[propext]` or
`[propext, Quot.sound]`).  No `Classical.*`, no `native_decide`, no `sorry`.
-/

import YMGap.Continuum.HeatKernelConv
import YMGap.Continuum.HeatKernelPos
import YMGap.Continuum.HeatKernelPos2
import YMGap.Continuum.KPLimit
import YMGap.Constructive.Reals
import YMGap.Constructive.CRealMul
import YMGap.Constructive.ExpPos
import YMGap.Constructive.RationalTail
import YMGap.Constructive.HalfPow
import YMGap.Constructive.AbsQ
import YMGap.Constructive.CharacterTail

namespace YMGap.Continuum.ThetaConv

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.HKConv
open YMGap.Continuum.HKPos
open YMGap.Continuum.HKPos2
open YMGap.Constructive.RationalTail
open YMGap.Constructive.HalfPow
open YMGap.Constructive.QPoly (q_add_congr q_zero_add_eqv q_add_zero_eqv)

/-! ## 1. Abstract Weierstrass product-magnitude bound

For a nonnegative sequence `T : Nat → Q'` with all partial sums `≤ 1/2`, the
"upper product" `∏_{k<L}(1+T_k)` is bounded by `2`.  The proof pairs it with the
"lower product" `∏_{k<L}(1−T_k)`:

  * `prodUp · prodLow ≤ 1`            (each step multiplies by `(1−T²) ≤ 1`);
  * `1 − Σ T ≤ prodLow`              (Weierstrass lower bound);
  * `Σ T ≤ 1/2 ⟹ 1/2 ≤ prodLow`,    so `prodUp·(1/2) ≤ prodUp·prodLow ≤ 1`,
    hence `prodUp ≤ 2`.

All three are clean `Q'` inductions; no division is used. -/

/-- The upper product `∏_{k<L}(1 + T_k)`. -/
def prodUp (T : Nat → Q') : Nat → Q'
  | 0 => 1
  | L + 1 => prodUp T L * (1 + T L)

/-- The lower product `∏_{k<L}(1 − T_k)`. -/
def prodLow (T : Nat → Q') : Nat → Q'
  | 0 => 1
  | L + 1 => prodLow T L * (1 + (-(T L)))

@[simp] theorem prodUp_succ (T : Nat → Q') (L : Nat) :
    prodUp T (L + 1) = prodUp T L * (1 + T L) := rfl

@[simp] theorem prodLow_succ (T : Nat → Q') (L : Nat) :
    prodLow T (L + 1) = prodLow T L * (1 + (-(T L))) := rfl

/-- `0 ≤ prodUp` (product of nonnegative factors `1 + T_k ≥ 1 ≥ 0`). -/
theorem prodUp_nonneg {T : Nat → Q'} (hT : ∀ k, (0 : Q') ≤ T k) (L : Nat) :
    (0 : Q') ≤ prodUp T L := by
  induction L with
  | zero =>
      show (0 : Q') ≤ (1 : Q')
      exact Q'.le_of_lt (CReal.pos_of_num_pos (by decide))
  | succ L ih =>
      rw [prodUp_succ]
      refine Q'.mul_nonneg _ _ ih ?_
      -- 0 ≤ 1 + T L
      have h1 : (0 : Q') ≤ (1 : Q') := Q'.le_of_lt (CReal.pos_of_num_pos (by decide))
      exact Q'.le_trans' _ _ _ h1 (Q'.add_le_self_of_nonneg 1 (T L) (hT L))

/-- `0 ≤ prodLow` when every `T_k ≤ 1` (so each factor `1 − T_k ≥ 0`). -/
theorem prodLow_nonneg {T : Nat → Q'} (hT1 : ∀ k, T k ≤ (1 : Q')) (L : Nat) :
    (0 : Q') ≤ prodLow T L := by
  induction L with
  | zero =>
      show (0 : Q') ≤ (1 : Q')
      exact Q'.le_of_lt (CReal.pos_of_num_pos (by decide))
  | succ L ih =>
      rw [prodLow_succ]
      refine Q'.mul_nonneg _ _ ih ?_
      -- 0 ≤ 1 + (-(T L))  ⟺  T L ≤ 1
      exact Q'.sub_nonneg_of_le (c := T L) (d := 1) (hT1 L)

/-- `(1 + t)·(1 + (-t)) ≃ 1 + (-(t·t))` — the difference-of-squares identity. -/
theorem one_plus_mul_one_minus_eqv (t : Q') :
    ((1 + t) * (1 + (-t))).eqv (1 + (-(t * t))) := by
  -- (1+t)(1+(-t)) = 1*(1+(-t)) + t*(1+(-t))
  refine Q'.eqv_trans _ _ _ (Q'.add_mul_eqv 1 t (1 + (-t))) ?_
  -- 1*(1+(-t)) ≃ 1+(-t) ;  t*(1+(-t)) ≃ t*1 + t*(-t) ≃ t + (-(t*t))
  have e1 : ((1 : Q') * (1 + (-t))).eqv (1 + (-t)) := Q'.one_mul_eqv (1 + (-t))
  have e2 : (t * (1 + (-t))).eqv (t + (-(t * t))) := by
    refine Q'.eqv_trans _ _ _ (Q'.mul_add_eqv t 1 (-t)) ?_
    refine q_add_congr (Q'.mul_one_eqv t) ?_
    exact Q'.mul_neg_eqv t t
  refine Q'.eqv_trans _ _ _ (q_add_congr e1 e2) ?_
  -- (1+(-t)) + (t + (-(t*t)))  ≃  1 + (-(t*t))
  -- interchange: = (1 + t) + ((-t) + (-(t*t)))  -- not directly; regroup
  -- (1 + (-t)) + (t + (-(t*t))) = 1 + ((-t) + (t + (-(t*t))))
  refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv 1 (-t) (t + (-(t * t)))) ?_
  refine Q'.add_eqv_congr_left 1 _ (-(t * t)) ?_
  -- (-t) + (t + (-(t*t))) ≃ -(t*t)
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.add_assoc_eqv (-t) t (-(t * t)))) ?_
  -- ((-t) + t) + (-(t*t)) ≃ 0 + (-(t*t)) ≃ -(t*t)
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right ((-t) + t) 0 (-(t * t)) (Q'.neg_add_self_eqv t)) ?_
  exact q_zero_add_eqv (-(t * t))

/-- **`prodUp · prodLow ≤ 1`.**  Each step multiplies the product by
`(1 + T_L)·(1 − T_L) = 1 − T_L² ≤ 1`; the running product stays `≤ 1`
(it starts at `1`).  Needs `0 ≤ prodUp`, `0 ≤ prodLow` and `0 ≤ T_k`. -/
theorem prodUp_mul_prodLow_le_one {T : Nat → Q'}
    (hT : ∀ k, (0 : Q') ≤ T k) (hT1 : ∀ k, T k ≤ (1 : Q')) (L : Nat) :
    prodUp T L * prodLow T L ≤ (1 : Q') := by
  induction L with
  | zero =>
      show (1 : Q') * 1 ≤ (1 : Q')
      exact Q'.le_of_eqv (Q'.mul_one_eqv 1)
  | succ L ih =>
      -- prodUp(L+1)·prodLow(L+1) = (prodUp L · prodLow L)·((1+T_L)(1+(-T_L)))
      rw [prodUp_succ, prodLow_succ]
      -- reassociate to (prodUp L · prodLow L) · ((1+T_L)·(1+(-T_L)))
      have hrearr : ((prodUp T L * (1 + T L)) * (prodLow T L * (1 + (-(T L))))).eqv
          ((prodUp T L * prodLow T L) * ((1 + T L) * (1 + (-(T L))))) := by
        -- (A·b)·(C·d) ≃ (A·C)·(b·d)
        refine Q'.eqv_trans _ _ _
          (Q'.mul_assoc_eqv (prodUp T L) (1 + T L) (prodLow T L * (1 + (-(T L))))) ?_
        refine Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left (prodUp T L) _ _
            (Q'.eqv_symm (Q'.mul_assoc_eqv (1 + T L) (prodLow T L) (1 + (-(T L)))))) ?_
        refine Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left (prodUp T L) _ _
            (Q'.mul_eqv_congr_right _ _ (1 + (-(T L)))
              (Q'.mul_comm_eqv (1 + T L) (prodLow T L)))) ?_
        refine Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left (prodUp T L) _ _
            (Q'.mul_assoc_eqv (prodLow T L) (1 + T L) (1 + (-(T L))))) ?_
        exact Q'.eqv_symm (Q'.mul_assoc_eqv (prodUp T L) (prodLow T L)
          ((1 + T L) * (1 + (-(T L)))))
      refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hrearr) ?_
      -- (P·Q)·((1+T)(1+(-T))) ≤ 1·1 ≤ 1, with P·Q ≤ 1, factor ≤ 1, both ≥ 0
      have hPQ_nn : (0 : Q') ≤ prodUp T L * prodLow T L :=
        Q'.mul_nonneg _ _ (prodUp_nonneg hT L) (prodLow_nonneg hT1 L)
      have hfac_le_one : (1 + T L) * (1 + (-(T L))) ≤ (1 : Q') := by
        refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (one_plus_mul_one_minus_eqv (T L))) ?_
        -- 1 + (-(T_L·T_L)) ≤ 1
        have hsq : (0 : Q') ≤ T L * T L := Q'.mul_nonneg _ _ (hT L) (hT L)
        have hneg : (-(T L * T L)) ≤ (0 : Q') := by
          have := Q'.neg_le_neg hsq
          rwa [show (-(0 : Q')) = 0 from rfl] at this
        refine Q'.le_trans' _ _ _ (Q'.add_le_add_left 1 _ 0 hneg) ?_
        exact Q'.le_of_eqv (q_add_zero_eqv 1)
      -- product ≤ 1·1
      have hprod : (prodUp T L * prodLow T L) * ((1 + T L) * (1 + (-(T L))))
          ≤ (1 : Q') * 1 :=
        mul_le_mul' hPQ_nn (Q'.le_of_lt (CReal.pos_of_num_pos (by decide))) ih hfac_le_one
      exact Q'.le_trans' _ _ _ hprod (Q'.le_of_eqv (Q'.mul_one_eqv 1))

/-- A finite sum of nonnegative terms is nonnegative. -/
theorem finSum_nonneg {T : Nat → Q'} (hT : ∀ k, (0 : Q') ≤ T k) :
    ∀ L, (0 : Q') ≤ finSum T L
  | 0 => Q'.le_refl' 0
  | L + 1 => by
      show (0 : Q') ≤ finSum T L + T L
      exact Q'.zero_le_add _ _ (finSum_nonneg hT L) (hT L)

/-- **Weierstrass lower bound:** `1 − Σ_{k<L} T_k ≤ ∏_{k<L}(1 − T_k)`, for
`0 ≤ T_k ≤ 1`.  Induction on `L`. -/
theorem weierstrass_lower {T : Nat → Q'}
    (hT : ∀ k, (0 : Q') ≤ T k) (hT1 : ∀ k, T k ≤ (1 : Q')) (L : Nat) :
    1 + (-(finSum T L)) ≤ prodLow T L := by
  induction L with
  | zero =>
      show 1 + (-(finSum T 0)) ≤ prodLow T 0
      -- finSum T 0 = 0, prodLow T 0 = 1
      show 1 + (-(0 : Q')) ≤ (1 : Q')
      have e : ((1 : Q') + (-(0 : Q'))).eqv 1 := q_add_zero_eqv 1
      exact Q'.le_of_eqv e
  | succ L ih =>
      -- prodLow(L+1) = prodLow L · (1 + (-(T L)))
      rw [prodLow_succ]
      -- finSum T (L+1) = finSum T L + T L
      show 1 + (-(finSum T L + T L)) ≤ prodLow T L * (1 + (-(T L)))
      have hsnn : (0 : Q') ≤ finSum T L := finSum_nonneg hT L
      generalize hs : finSum T L = s at ih hsnn ⊢
      -- 1 + (-(s + T L)) ≤ (1 + (-s)) · (1 + (-(T L)))  [will dominate]
      have h1mTL_nn : (0 : Q') ≤ 1 + (-(T L)) :=
        Q'.sub_nonneg_of_le (c := T L) (d := 1) (hT1 L)
      -- Step 1: (1 + (-s))·(1 + (-(T L))) ≤ prodLow L · (1 + (-(T L)))
      have step1 : (1 + (-s)) * (1 + (-(T L))) ≤ prodLow T L * (1 + (-(T L))) :=
        Q'.mul_le_mul_of_nonneg_right _ _ (1 + (-(T L))) ih h1mTL_nn
      -- Step 2: 1 + (-(s + T L)) ≤ (1 + (-s))·(1 + (-(T L)))
      have step2 : 1 + (-(s + T L)) ≤ (1 + (-s)) * (1 + (-(T L))) := by
        -- (1+(-s))(1+(-(T L))) ≃ 1 + (-(T L)) + (-s) + s·(T L)
        -- We show RHS ≥ 1 + (-(s + T L)) = 1 + (-s) + (-(T L))
        -- Expand: (1+(-s))*(1+(-(T L))) = 1*(1+(-(T L))) + (-s)*(1+(-(T L)))
        have hexp : ((1 + (-s)) * (1 + (-(T L)))).eqv
            ((1 + (-(T L))) + ((-s) + s * T L)) := by
          refine Q'.eqv_trans _ _ _ (Q'.add_mul_eqv 1 (-s) (1 + (-(T L)))) ?_
          refine q_add_congr (Q'.one_mul_eqv (1 + (-(T L)))) ?_
          -- (-s)*(1+(-(T L))) ≃ (-s)*1 + (-s)*(-(T L)) ≃ (-s) + s·(T L)
          refine Q'.eqv_trans _ _ _ (Q'.mul_add_eqv (-s) 1 (-(T L))) ?_
          refine q_add_congr (Q'.mul_one_eqv (-s)) ?_
          -- (-s)*(-(T L)) ≃ s·(T L)
          refine Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv s (-(T L))) ?_
          refine Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _ (Q'.mul_neg_eqv s (T L))) ?_
          exact Q'.neg_neg_eqv (s * T L)
        refine Q'.le_trans' _ _ _ ?_ (Q'.ge_of_eqv hexp)
        -- Goal now: 1 + (-(s + T L)) ≤ (1 + (-(T L))) + ((-s) + s·(T L))
        -- LHS ≃ 1 + ((-s) + (-(T L)))  ; RHS ≥ 1 + ((-s) + (-(T L))) since s·(T L) ≥ 0
        -- First rewrite LHS via -(s + T L) ≃ (-s) + (-(T L))
        have hLHS : (1 + (-(s + T L))).eqv (1 + ((-s) + (-(T L)))) :=
          Q'.add_eqv_congr_left 1 _ _ (Q'.neg_add_eqv s (T L))
        refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hLHS) ?_
        -- RHS regroup: (1+(-(T L))) + ((-s) + s·T L) ≃ 1 + ((-(T L)) + ((-s) + s·T L))
        have hRHSassoc : ((1 + (-(T L))) + ((-s) + s * T L)).eqv
            (1 + ((-(T L)) + ((-s) + s * T L))) :=
          Q'.add_assoc_eqv 1 (-(T L)) ((-s) + s * T L)
        refine Q'.le_trans' _ _ _ ?_ (Q'.ge_of_eqv hRHSassoc)
        -- Now: 1 + ((-s) + (-(T L))) ≤ 1 + ((-(T L)) + ((-s) + s·T L))
        refine Q'.add_le_add_left 1 _ _ ?_
        -- (-s) + (-(T L)) ≤ (-(T L)) + ((-s) + s·T L)
        -- RHS ≃ ((-(T L)) + (-s)) + s·T L  ≥  (-(T L)) + (-s) ≃ (-s) + (-(T L))
        have hRHS2 : ((-(T L)) + ((-s) + s * T L)).eqv
            (((-(T L)) + (-s)) + s * T L) :=
          Q'.eqv_symm (Q'.add_assoc_eqv (-(T L)) (-s) (s * T L))
        refine Q'.le_trans' _ _ _ ?_ (Q'.ge_of_eqv hRHS2)
        -- (-s) + (-(T L)) ≤ ((-(T L)) + (-s)) + s·T L
        have hcomm : ((-s) + (-(T L))).eqv ((-(T L)) + (-s)) :=
          Q'.add_comm_eqv (-s) (-(T L))
        refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hcomm) ?_
        -- (-(T L)) + (-s) ≤ ((-(T L)) + (-s)) + s·T L  (add nonneg)
        exact Q'.add_le_self_of_nonneg ((-(T L)) + (-s)) (s * T L)
          (Q'.mul_nonneg s (T L) hsnn (hT L))
      exact Q'.le_trans' _ _ _ step2 step1

/-- `T_k ≤ 1/2` from the smallness `finSum T (k+1) ≤ 1/2` (a single term is
dominated by a partial sum of nonnegatives). -/
theorem term_le_half_of_small {T : Nat → Q'} (hT : ∀ k, (0 : Q') ≤ T k)
    (hsmall : ∀ L, finSum T L ≤ half) (k : Nat) : T k ≤ half := by
  -- T k ≤ finSum T k + T k = finSum T (k+1) ≤ half
  have h1 : T k ≤ finSum T k + T k :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm (q_zero_add_eqv (T k))))
      (Q'.add_le_add_right 0 (finSum T k) (T k) (finSum_nonneg hT k))
  exact Q'.le_trans' _ _ _ h1 (hsmall (k + 1))

/-- **The Weierstrass product-magnitude bound:** `∏_{k<L}(1 + T_k) ≤ 2` for a
nonnegative sequence `T` with all partial sums `≤ 1/2`.  Combines
`prodUp_mul_prodLow_le_one` (`prodUp·prodLow ≤ 1`) with `weierstrass_lower`
(`1 − Σ T ≤ prodLow`, hence `1/2 ≤ prodLow`): `prodUp·(1/2) ≤ prodUp·prodLow ≤ 1`,
so `prodUp ≤ 2`.  No division. -/
theorem prodUpBound {T : Nat → Q'} (hT : ∀ k, (0 : Q') ≤ T k)
    (hsmall : ∀ L, finSum T L ≤ half) (L : Nat) :
    prodUp T L ≤ Q'.ofNat 2 := by
  have hT1 : ∀ k, T k ≤ (1 : Q') := fun k =>
    Q'.le_trans' _ _ _ (term_le_half_of_small hT hsmall k) (by decide)
  -- half ≤ prodLow T L
  have hhalf_le_prodLow : half ≤ prodLow T L := by
    -- 1 - finSum T L ≤ prodLow ; and half = 1 - half ≤ 1 - finSum T L
    have hWL : 1 + (-(finSum T L)) ≤ prodLow T L := weierstrass_lower hT hT1 L
    have hmono : half ≤ 1 + (-(finSum T L)) := by
      -- half ≃ 1 + (-half) ≤ 1 + (-(finSum T L))  since finSum T L ≤ half
      have e : (half).eqv (1 + (-half)) := by decide
      refine Q'.le_trans' _ _ _ (Q'.le_of_eqv e) ?_
      exact Q'.add_le_add_left 1 (-half) (-(finSum T L)) (Q'.neg_le_neg (hsmall L))
    exact Q'.le_trans' _ _ _ hmono hWL
  -- prodUp·half ≤ prodUp·prodLow ≤ 1
  have hUp_nn : (0 : Q') ≤ prodUp T L := prodUp_nonneg hT L
  have hstep : prodUp T L * half ≤ prodUp T L * prodLow T L :=
    Q'.mul_le_mul_of_nonneg_left half (prodLow T L) (prodUp T L) hhalf_le_prodLow hUp_nn
  have hUp_half_le_one : prodUp T L * half ≤ (1 : Q') :=
    Q'.le_trans' _ _ _ hstep (prodUp_mul_prodLow_le_one hT hT1 L)
  -- multiply by 2: (prodUp·half)·2 ≤ 1·2 = 2 ; (prodUp·half)·2 ≃ prodUp
  have hmul2 : (prodUp T L * half) * Q'.ofNat 2 ≤ (1 : Q') * Q'.ofNat 2 :=
    Q'.mul_le_mul_of_nonneg_right _ _ (Q'.ofNat 2) hUp_half_le_one (by decide)
  -- (prodUp·half)·2 ≃ prodUp·(half·2) ≃ prodUp·1 ≃ prodUp
  have eUp : ((prodUp T L * half) * Q'.ofNat 2).eqv (prodUp T L) := by
    refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv (prodUp T L) half (Q'.ofNat 2)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (prodUp T L) (half * Q'.ofNat 2) 1 (by decide)) ?_
    exact Q'.mul_one_eqv (prodUp T L)
  -- 1·2 ≃ 2
  have e2 : ((1 : Q') * Q'.ofNat 2).eqv (Q'.ofNat 2) := Q'.one_mul_eqv (Q'.ofNat 2)
  refine Q'.le_trans' _ _ _ (Q'.ge_of_eqv eUp) ?_
  exact Q'.le_trans' _ _ _ hmul2 (Q'.le_of_eqv e2)

/-! ## 2. The full Jacobi factor `gFac` and the coefficient sequence `Tcoef` -/

/-- The `k`-th half-amplitude `u_k = a^{2k+2} = a·a^{2k+1}` (the `(1 − a^{2n})`
prefactor's amplitude, `n = k+1`). -/
def uAmp (a : Q') (k : Nat) : Q' := a ^ (2 * k + 2)

/-- The `k`-th FULL Jacobi factor `(1 − a^{2k+2})·(1 + 2a^{2k+1}x + a^{4k+2})`. -/
def gFac (a x : Q') (k : Nat) : Q' :=
  (1 + (-(uAmp a k))) * HKPos.factor (HKPos.geoAmp a k) x

/-- The dominating coefficient `T_k = 2 a^{2k+1} + a^{4k+2} = two c + c·c`. -/
def Tcoef (a : Q') (k : Nat) : Q' :=
  HKPos.two (HKPos.geoAmp a k) + HKPos.geoAmp a k * HKPos.geoAmp a k

theorem Tcoef_nonneg {a : Q'} (ha0 : (0 : Q') < a) (k : Nat) :
    (0 : Q') ≤ Tcoef a k := by
  have hc0 : (0 : Q') ≤ HKPos.geoAmp a k :=
    Q'.le_of_lt (HKPos.pow_pos ha0 (2 * k + 1))
  exact Q'.zero_le_add _ _ (HKPos.two_nonneg hc0) (Q'.mul_nonneg _ _ hc0 hc0)

/-- `0 < uAmp a k < 1` for `0 < a < 1` (exponent `2k+2 ≥ 1`). -/
theorem uAmp_pos_lt_one {a : Q'} (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (k : Nat) :
    (0 : Q') < uAmp a k ∧ uAmp a k < (1 : Q') := by
  have e : 2 * k + 2 = (2 * k + 1) + 1 := by omega
  show (0 : Q') < a ^ (2 * k + 2) ∧ a ^ (2 * k + 2) < (1 : Q')
  rw [e]
  exact HKPos.pow_succ_pos_lt_one ha0 ha1 (2 * k + 1)

/-- `0 < gFac a x k` (full factor positive: both pieces positive). -/
theorem gFac_pos {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x) (k : Nat) :
    (0 : Q') < gFac a x k := by
  have hu : uAmp a k < (1 : Q') := (uAmp_pos_lt_one ha0 ha1 k).2
  have h1mu : (0 : Q') < 1 + (-(uAmp a k)) := HKPos.one_sub_pos hu
  have hc0 : (0 : Q') ≤ HKPos.geoAmp a k :=
    Q'.le_of_lt ((HKPos.pow_succ_pos_lt_one ha0 ha1 (2 * k)).1)
  have hc1 : HKPos.geoAmp a k < (1 : Q') := (HKPos.pow_succ_pos_lt_one ha0 ha1 (2 * k)).2
  exact HKPos.q_mul_pos h1mu (HKPos.factor_pos hc0 hc1 hx)

theorem gFac_nonneg {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x) (k : Nat) :
    (0 : Q') ≤ gFac a x k :=
  Q'.le_of_lt (gFac_pos ha0 ha1 hx k)

/-! ## 3. The per-factor deviation `gFac − 1` and its two-sided geometric bound

Writing `c = a^{2k+1} = geoAmp a k`, `u = a^{2k+2} = uAmp a k`, `f = factor c x`,
the deviation of the full factor from `1` is

    gFac a x k − 1 = (2c·x + c²) − u·f      (`dev`),

bounded two-sidedly by `±6c` under `−1 ≤ x ≤ 1`, `0 ≤ a ≤ 1`.  Since
`c = a·(a²)^k ≤ (1/2)^k` (under `a² ≤ 1/2`, `a ≤ 1`), `6c ≤ 6·(1/2)^k`. -/

/-- The deviation `dev = (two c·x + c·c) + (−(u·f))`, where `gFac ≃ 1 + dev`. -/
def devFac (a x : Q') (k : Nat) : Q' :=
  (HKPos.two (HKPos.geoAmp a k) * x + HKPos.geoAmp a k * HKPos.geoAmp a k)
    + (-(uAmp a k * HKPos.factor (HKPos.geoAmp a k) x))

/-- `gFac a x k ≃ 1 + devFac a x k`. -/
theorem gFac_eqv_one_add_dev (a x : Q') (k : Nat) :
    (gFac a x k).eqv (1 + devFac a x k) := by
  -- gFac = (1 + (-u))·f = 1·f + (-u)·f = f + (-(u·f))
  show ((1 + (-(uAmp a k))) * HKPos.factor (HKPos.geoAmp a k) x).eqv
      (1 + devFac a x k)
  refine Q'.eqv_trans _ _ _
    (Q'.add_mul_eqv 1 (-(uAmp a k)) (HKPos.factor (HKPos.geoAmp a k) x)) ?_
  -- 1·f + (-u)·f ≃ f + (-(u·f))
  have e1 : ((1 : Q') * HKPos.factor (HKPos.geoAmp a k) x).eqv
      (HKPos.factor (HKPos.geoAmp a k) x) := Q'.one_mul_eqv _
  have e2 : ((-(uAmp a k)) * HKPos.factor (HKPos.geoAmp a k) x).eqv
      (-(uAmp a k * HKPos.factor (HKPos.geoAmp a k) x)) :=
    Q'.neg_mul_eqv (uAmp a k) (HKPos.factor (HKPos.geoAmp a k) x)
  refine Q'.eqv_trans _ _ _ (q_add_congr e1 e2) ?_
  -- f + (-(u·f)) ≃ 1 + devFac, where f = 1 + (two c·x + c·c)
  -- f = 1 + (two c * x + c*c)  (definitional)
  show ((1 + (HKPos.two (HKPos.geoAmp a k) * x + HKPos.geoAmp a k * HKPos.geoAmp a k))
      + (-(uAmp a k * HKPos.factor (HKPos.geoAmp a k) x))).eqv (1 + devFac a x k)
  -- (1 + A) + B ≃ 1 + (A + B) = 1 + devFac
  exact Q'.add_assoc_eqv 1
    (HKPos.two (HKPos.geoAmp a k) * x + HKPos.geoAmp a k * HKPos.geoAmp a k)
    (-(uAmp a k * HKPos.factor (HKPos.geoAmp a k) x))

/-- `uAmp a k ≃ a · geoAmp a k` (i.e. `a^{2k+2} = a·a^{2k+1}`). -/
theorem uAmp_eqv (a : Q') (k : Nat) :
    (uAmp a k).eqv (a * HKPos.geoAmp a k) := by
  show (a ^ (2 * k + 2)).eqv (a * a ^ (2 * k + 1))
  have e : 2 * k + 2 = (2 * k + 1) + 1 := by omega
  rw [e]
  exact Q'.pow_succ a (2 * k + 1) ▸ Q'.eqv_refl _

/-- `uAmp a k ≤ geoAmp a k` for `0 < a ≤ 1` (`a^{2k+2} ≤ a^{2k+1}`). -/
theorem uAmp_le_geoAmp {a : Q'} (ha0 : (0 : Q') < a) (ha1 : a ≤ (1 : Q')) (k : Nat) :
    uAmp a k ≤ HKPos.geoAmp a k := by
  have hc0 : (0 : Q') ≤ HKPos.geoAmp a k := Q'.le_of_lt (HKPos.pow_pos ha0 (2 * k + 1))
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (uAmp_eqv a k)) ?_
  -- a·c ≤ 1·c = c
  refine Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right a 1 (HKPos.geoAmp a k) ha1 hc0) ?_
  exact Q'.le_of_eqv (Q'.one_mul_eqv (HKPos.geoAmp a k))

/-- The constant `four = (1+1)+(1+1)` kept in `+1` form so multiples of `c`
distribute to `two c + two c` without `ofNat`-arithmetic. -/
def four : Q' := (1 + 1) + (1 + 1)

/-- `c · four ≃ two c + two c` (`= 4c`).  Pure distribution. -/
theorem c_mul_four_eqv (c : Q') :
    (c * four).eqv (HKPos.two c + HKPos.two c) := by
  show (c * ((1 + 1) + (1 + 1))).eqv ((c + c) + (c + c))
  -- c·((1+1)+(1+1)) ≃ c·(1+1) + c·(1+1) ≃ (c·1+c·1)+(c·1+c·1) ≃ (c+c)+(c+c)
  refine Q'.eqv_trans _ _ _ (Q'.mul_add_eqv c (1 + 1) (1 + 1)) ?_
  have hone : (c * (1 + 1)).eqv (c + c) := by
    refine Q'.eqv_trans _ _ _ (Q'.mul_add_eqv c 1 1) ?_
    exact q_add_congr (Q'.mul_one_eqv c) (Q'.mul_one_eqv c)
  exact q_add_congr hone hone

/-- `factor c x ≤ four` (`= 4`) for `0 ≤ c < 1`, `x ≤ 1`.  (`1 + 2cx + c² ≤ 1+2+1`.) -/
theorem factor_le_four {c x : Q'}
    (hc0 : (0 : Q') ≤ c) (hc1 : c < (1 : Q')) (hx1 : x ≤ (1 : Q')) :
    HKPos.factor c x ≤ four := by
  -- factor = 1 + (two c * x + c*c)
  show (1 + (HKPos.two c * x + c * c)) ≤ four
  have h2c_nn : (0 : Q') ≤ HKPos.two c := HKPos.two_nonneg hc0
  -- two c * x ≤ two c (x ≤ 1)
  have hcx : HKPos.two c * x ≤ HKPos.two c :=
    Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left x 1 (HKPos.two c) hx1 h2c_nn)
      (Q'.le_of_eqv (Q'.mul_one_eqv (HKPos.two c)))
  -- two c = c + c ≤ 1 + 1
  have h2c_le2 : HKPos.two c ≤ (1 : Q') + 1 := by
    show c + c ≤ (1 : Q') + 1
    have hc1' : c ≤ (1 : Q') := Q'.le_of_lt hc1
    exact Q'.le_trans' _ _ _ (Q'.add_le_add_right c 1 c hc1')
      (Q'.add_le_add_left 1 c 1 hc1')
  -- c*c ≤ 1
  have hcc : c * c ≤ (1 : Q') := by
    refine Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left c 1 c (Q'.le_of_lt hc1) hc0) ?_
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_one_eqv c)) (Q'.le_of_lt hc1)
  -- two c * x + c*c ≤ (1+1) + 1
  have hsum : HKPos.two c * x + c * c ≤ (1 + 1) + 1 := by
    refine Q'.le_trans' _ _ _
      (Q'.add_le_add_right _ _ (c * c) (Q'.le_trans' _ _ _ hcx h2c_le2)) ?_
    exact Q'.add_le_add_left (1 + 1) (c * c) 1 hcc
  -- 1 + (two c * x + c*c) ≤ 1 + ((1+1)+1) ≃ four
  refine Q'.le_trans' _ _ _ (Q'.add_le_add_left 1 _ _ hsum) ?_
  show (1 : Q') + ((1 + 1) + 1) ≤ four
  exact Q'.le_of_eqv (by decide)

/-- The symmetric per-factor deviation bound `dBound = 6c = two c + (two c + two c)`. -/
def dBound (a : Q') (l : Nat) : Q' :=
  HKPos.two (HKPos.geoAmp a l)
    + (HKPos.two (HKPos.geoAmp a l) + HKPos.two (HKPos.geoAmp a l))

theorem dBound_nonneg {a : Q'} (ha0 : (0 : Q') < a) (l : Nat) :
    (0 : Q') ≤ dBound a l := by
  have h2c : (0 : Q') ≤ HKPos.two (HKPos.geoAmp a l) :=
    HKPos.two_nonneg (Q'.le_of_lt (HKPos.pow_pos ha0 (2 * l + 1)))
  exact Q'.zero_le_add _ _ h2c (Q'.zero_le_add _ _ h2c h2c)

/-- `u·f ≤ two c + two c` (`= 4c`): `u ≤ c` and `f ≤ four`, so `u·f ≤ c·four ≃ 4c`. -/
theorem uf_le {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q'))
    (l : Nat) :
    uAmp a l * HKPos.factor (HKPos.geoAmp a l) x
      ≤ HKPos.two (HKPos.geoAmp a l) + HKPos.two (HKPos.geoAmp a l) := by
  have hc0 : (0 : Q') ≤ HKPos.geoAmp a l := Q'.le_of_lt (HKPos.pow_pos ha0 (2 * l + 1))
  have hc1 : HKPos.geoAmp a l < (1 : Q') := (HKPos.pow_succ_pos_lt_one ha0 ha1 (2 * l)).2
  have hu_le : uAmp a l ≤ HKPos.geoAmp a l := uAmp_le_geoAmp ha0 (Q'.le_of_lt ha1) l
  have hu_nn : (0 : Q') ≤ uAmp a l := Q'.le_of_lt (uAmp_pos_lt_one ha0 ha1 l).1
  have hf_nn : (0 : Q') ≤ HKPos.factor (HKPos.geoAmp a l) x :=
    Q'.le_of_lt (HKPos.factor_pos hc0 hc1 hx)
  have hf_le : HKPos.factor (HKPos.geoAmp a l) x ≤ four := factor_le_four hc0 hc1 hx1
  -- u·f ≤ c·four
  have hmul : uAmp a l * HKPos.factor (HKPos.geoAmp a l) x ≤ HKPos.geoAmp a l * four :=
    mul_le_mul' hu_nn (Q'.le_of_lt (by show (0:Q') < four; exact CReal.pos_of_num_pos (by decide)))
      hu_le hf_le
  exact Q'.le_trans' _ _ _ hmul (Q'.le_of_eqv (c_mul_four_eqv (HKPos.geoAmp a l)))

/-- **Upper per-factor bound:** `devFac a x l ≤ dBound a l`. -/
theorem devFac_le {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q'))
    (l : Nat) :
    devFac a x l ≤ dBound a l := by
  have hc0 : (0 : Q') ≤ HKPos.geoAmp a l := Q'.le_of_lt (HKPos.pow_pos ha0 (2 * l + 1))
  have hc1 : HKPos.geoAmp a l ≤ (1 : Q') :=
    Q'.le_of_lt (HKPos.pow_succ_pos_lt_one ha0 ha1 (2 * l)).2
  have h2c_nn : (0 : Q') ≤ HKPos.two (HKPos.geoAmp a l) := HKPos.two_nonneg hc0
  -- devFac = (two c * x + c*c) + (-(u·f)) ≤ (two c * x + c*c)  (drop ≤0 term)
  have hdrop : devFac a x l ≤ HKPos.two (HKPos.geoAmp a l) * x
      + HKPos.geoAmp a l * HKPos.geoAmp a l := by
    show (HKPos.two (HKPos.geoAmp a l) * x + HKPos.geoAmp a l * HKPos.geoAmp a l)
        + (-(uAmp a l * HKPos.factor (HKPos.geoAmp a l) x)) ≤ _
    -- A + (-(u·f)) ≤ A  since u·f ≥ 0
    have huf_nn : (0 : Q') ≤ uAmp a l * HKPos.factor (HKPos.geoAmp a l) x := by
      have hu_nn : (0 : Q') ≤ uAmp a l := Q'.le_of_lt (uAmp_pos_lt_one ha0 ha1 l).1
      have hf_nn : (0 : Q') ≤ HKPos.factor (HKPos.geoAmp a l) x :=
        Q'.le_of_lt (HKPos.factor_pos hc0
          (HKPos.pow_succ_pos_lt_one ha0 ha1 (2 * l)).2 hx)
      exact Q'.mul_nonneg _ _ hu_nn hf_nn
    have hneg : (-(uAmp a l * HKPos.factor (HKPos.geoAmp a l) x)) ≤ (0 : Q') := by
      have := Q'.neg_le_neg huf_nn
      rwa [show (-(0 : Q')) = 0 from rfl] at this
    refine Q'.le_trans' _ _ _ (Q'.add_le_add_left _ _ 0 hneg) ?_
    exact Q'.le_of_eqv (q_add_zero_eqv _)
  -- two c * x ≤ two c  (x ≤ 1) ;  c*c ≤ two c
  have hcx : HKPos.two (HKPos.geoAmp a l) * x ≤ HKPos.two (HKPos.geoAmp a l) :=
    Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left x 1 (HKPos.two (HKPos.geoAmp a l)) hx1 h2c_nn)
      (Q'.le_of_eqv (Q'.mul_one_eqv (HKPos.two (HKPos.geoAmp a l))))
  have hcc : HKPos.geoAmp a l * HKPos.geoAmp a l ≤ HKPos.two (HKPos.geoAmp a l) := by
    -- c*c ≤ c ≤ c + c = two c
    refine Q'.le_trans' _ _ _
      (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ 1 _ hc1 hc0)
        (Q'.le_of_eqv (Q'.mul_one_eqv (HKPos.geoAmp a l)))) ?_
    exact Q'.add_le_self_of_nonneg (HKPos.geoAmp a l) (HKPos.geoAmp a l) hc0
  -- combine: (two c*x + c*c) ≤ two c + two c ≤ two c + (two c + two c) = dBound
  have hsum : HKPos.two (HKPos.geoAmp a l) * x + HKPos.geoAmp a l * HKPos.geoAmp a l
      ≤ HKPos.two (HKPos.geoAmp a l) + HKPos.two (HKPos.geoAmp a l) :=
    Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ _ hcx)
      (Q'.add_le_add_left (HKPos.two (HKPos.geoAmp a l)) _ _ hcc)
  refine Q'.le_trans' _ _ _ hdrop (Q'.le_trans' _ _ _ hsum ?_)
  -- two c + two c ≤ two c + (two c + two c) = dBound
  show HKPos.two (HKPos.geoAmp a l) + HKPos.two (HKPos.geoAmp a l) ≤ dBound a l
  show HKPos.two (HKPos.geoAmp a l) + HKPos.two (HKPos.geoAmp a l)
      ≤ HKPos.two (HKPos.geoAmp a l)
        + (HKPos.two (HKPos.geoAmp a l) + HKPos.two (HKPos.geoAmp a l))
  -- 2c + 2c ≤ 2c + (2c + 2c)  ⟺  2c ≤ 2c + 2c (add nonneg on the right inside)
  -- regroup: (2c + 2c) ≃ 0 + (2c + 2c) ... easier: 2c+2c ≤ 2c+(2c+2c) since second arg grows
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.add_comm_eqv (HKPos.two (HKPos.geoAmp a l))
      (HKPos.two (HKPos.geoAmp a l)))) ?_
  -- 2c + 2c (commuted) ≤ 2c + (2c+2c): add_le_add_left on first 2c, need 2c ≤ 2c+2c
  refine Q'.add_le_add_left (HKPos.two (HKPos.geoAmp a l)) _ _ ?_
  exact Q'.add_le_self_of_nonneg (HKPos.two (HKPos.geoAmp a l))
    (HKPos.two (HKPos.geoAmp a l)) h2c_nn

/-- **Lower per-factor bound:** `−dBound a l ≤ devFac a x l`. -/
theorem neg_dBound_le_devFac {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q'))
    (l : Nat) :
    -(dBound a l) ≤ devFac a x l := by
  have hc0 : (0 : Q') ≤ HKPos.geoAmp a l := Q'.le_of_lt (HKPos.pow_pos ha0 (2 * l + 1))
  have h2c_nn : (0 : Q') ≤ HKPos.two (HKPos.geoAmp a l) := HKPos.two_nonneg hc0
  -- Lower bound the two pieces of devFac.
  -- piece1 = two c * x + c*c ≥ -(two c)
  have hx_lb : -(HKPos.two (HKPos.geoAmp a l)) ≤ HKPos.two (HKPos.geoAmp a l) * x := by
    -- two c * (-1) = -(two c) ≤ two c * x
    have hmul : HKPos.two (HKPos.geoAmp a l) * (-1) ≤ HKPos.two (HKPos.geoAmp a l) * x :=
      Q'.mul_le_mul_of_nonneg_left (-1) x (HKPos.two (HKPos.geoAmp a l)) hx h2c_nn
    have he : (HKPos.two (HKPos.geoAmp a l) * (-1)).eqv (-(HKPos.two (HKPos.geoAmp a l))) := by
      refine Q'.eqv_trans _ _ _ (Q'.mul_neg_eqv (HKPos.two (HKPos.geoAmp a l)) 1) ?_
      exact Q'.neg_eqv_congr _ _ (Q'.mul_one_eqv (HKPos.two (HKPos.geoAmp a l)))
    exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv he) hmul
  have hcc_nn : (0 : Q') ≤ HKPos.geoAmp a l * HKPos.geoAmp a l := Q'.mul_nonneg _ _ hc0 hc0
  have hpiece1 : -(HKPos.two (HKPos.geoAmp a l))
      ≤ HKPos.two (HKPos.geoAmp a l) * x + HKPos.geoAmp a l * HKPos.geoAmp a l := by
    -- -(two c) ≤ two c * x ≤ two c * x + c*c
    exact Q'.le_trans' _ _ _ hx_lb
      (Q'.add_le_self_of_nonneg (HKPos.two (HKPos.geoAmp a l) * x) _ hcc_nn)
  -- piece2 = -(u·f) ≥ -(two c + two c)
  have huf_le : uAmp a l * HKPos.factor (HKPos.geoAmp a l) x
      ≤ HKPos.two (HKPos.geoAmp a l) + HKPos.two (HKPos.geoAmp a l) := uf_le ha0 ha1 hx hx1 l
  have hpiece2 : -(HKPos.two (HKPos.geoAmp a l) + HKPos.two (HKPos.geoAmp a l))
      ≤ -(uAmp a l * HKPos.factor (HKPos.geoAmp a l) x) := Q'.neg_le_neg huf_le
  -- devFac = piece1 + piece2 ≥ -(two c) + (-(two c + two c)) = -dBound
  have hsum : (-(HKPos.two (HKPos.geoAmp a l)))
      + (-(HKPos.two (HKPos.geoAmp a l) + HKPos.two (HKPos.geoAmp a l)))
      ≤ devFac a x l := by
    show _ ≤ (HKPos.two (HKPos.geoAmp a l) * x + HKPos.geoAmp a l * HKPos.geoAmp a l)
        + (-(uAmp a l * HKPos.factor (HKPos.geoAmp a l) x))
    exact Q'.le_trans' _ _ _
      (Q'.add_le_add_right _ _ _ hpiece1)
      (Q'.add_le_add_left _ _ _ hpiece2)
  -- -(dBound) ≃ -(two c) + (-(two c + two c))
  have heq : (-(dBound a l)).eqv
      ((-(HKPos.two (HKPos.geoAmp a l)))
        + (-(HKPos.two (HKPos.geoAmp a l) + HKPos.two (HKPos.geoAmp a l)))) := by
    show (-(HKPos.two (HKPos.geoAmp a l)
        + (HKPos.two (HKPos.geoAmp a l) + HKPos.two (HKPos.geoAmp a l)))).eqv _
    exact Q'.neg_add_eqv (HKPos.two (HKPos.geoAmp a l))
      (HKPos.two (HKPos.geoAmp a l) + HKPos.two (HKPos.geoAmp a l))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv heq) hsum

/-! ## 4. `dBound a l ≤ C·(1/2)^l` and the increment majorant constant

`geoAmp a l = a^{2l+1} ≃ a·(a²)^l ≤ (1/2)^l` under `a·a ≤ 1/2`, `a ≤ 1`.  Hence
`dBound a l = 6·geoAmp ≤ 6·(1/2)^l`.  The engine constant is
`Cinc = two 1 + (two 1 + two 1) = 6`, kept additively so `Cinc·(1/2)^l`
distributes to `two h^l + (two h^l + two h^l)` and the comparison is termwise. -/

/-- `geoAmp a l ≃ a · (a·a)^l` (`a^{2l+1} = a·(a²)^l`). -/
theorem geoAmp_eqv (a : Q') (l : Nat) :
    (HKPos.geoAmp a l).eqv (a * (a * a) ^ l) := by
  show (a ^ (2 * l + 1)).eqv (a * (a * a) ^ l)
  induction l with
  | zero =>
      show (a ^ 1).eqv (a * (a * a) ^ 0)
      refine Q'.eqv_trans _ _ _ ?_ (Q'.eqv_symm (Q'.mul_one_eqv a))
      show (a * a ^ 0).eqv a
      exact Q'.mul_one_eqv a
  | succ l ih =>
      show (a ^ (2 * (l + 1) + 1)).eqv (a * (a * a) ^ (l + 1))
      have he : 2 * (l + 1) + 1 = (2 * l + 1) + 2 := by omega
      rw [he]
      show (a * (a * a ^ (2 * l + 1))).eqv (a * ((a * a) * (a * a) ^ l))
      refine Q'.mul_eqv_congr_left a _ _ ?_
      refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left a _ _ ih) ?_
      exact Q'.eqv_symm (Q'.mul_assoc_eqv a a ((a * a) ^ l))

/-- `geoAmp a l ≤ (1/2)^l` under `0 < a ≤ 1`, `a·a ≤ 1/2`. -/
theorem geoAmp_le_half_pow {a : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a ≤ (1 : Q')) (ha2 : a * a ≤ half) (l : Nat) :
    HKPos.geoAmp a l ≤ half ^ l := by
  -- geoAmp ≃ a·(a²)^l ≤ 1·(a²)^l = (a²)^l ≤ half^l
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (geoAmp_eqv a l)) ?_
  have haa_nn : (0 : Q') ≤ a * a := Q'.mul_nonneg a a (Q'.le_of_lt ha0) (Q'.le_of_lt ha0)
  have hpow : (a * a) ^ l ≤ half ^ l := pow_le_pow_base haa_nn ha2 l
  -- a·(a²)^l ≤ 1·(a²)^l = (a²)^l ≤ half^l
  refine Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right a 1 ((a * a) ^ l) ha1 (Q'.pow_nonneg _ haa_nn l)) ?_
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.one_mul_eqv ((a * a) ^ l))) hpow

/-- The increment majorant constant `Cinc = 6 = two 1 + (two 1 + two 1)`. -/
def Cinc : Q' := HKPos.two 1 + (HKPos.two 1 + HKPos.two 1)

theorem Cinc_num_pos : 0 < Cinc.num := by decide

/-- `two p · q ≃ two (p·q)` (`(p+p)·q = p·q + p·q`). -/
theorem two_mul_eqv (p q : Q') : (HKPos.two p * q).eqv (HKPos.two (p * q)) := by
  show ((p + p) * q).eqv (p * q + p * q)
  exact Q'.add_mul_eqv p p q

/-- `Cinc · q ≃ two q + (two q + two q)` (`6·q` distributed, with `two 1·q ≃ two q`). -/
theorem Cinc_mul_eqv (q : Q') :
    (Cinc * q).eqv (HKPos.two q + (HKPos.two q + HKPos.two q)) := by
  show ((HKPos.two 1 + (HKPos.two 1 + HKPos.two 1)) * q).eqv _
  -- (A + (B + C))·q ≃ A·q + (B·q + C·q)
  refine Q'.eqv_trans _ _ _ (Q'.add_mul_eqv (HKPos.two 1) (HKPos.two 1 + HKPos.two 1) q) ?_
  refine q_add_congr ?_ ?_
  · -- two 1 · q ≃ two q  (since two 1 · q ≃ two (1·q) ≃ two q)
    refine Q'.eqv_trans _ _ _ (two_mul_eqv 1 q) ?_
    show (HKPos.two ((1 : Q') * q)).eqv (HKPos.two q)
    show ((1 : Q') * q + (1 : Q') * q).eqv (q + q)
    exact q_add_congr (Q'.one_mul_eqv q) (Q'.one_mul_eqv q)
  · refine Q'.eqv_trans _ _ _ (Q'.add_mul_eqv (HKPos.two 1) (HKPos.two 1) q) ?_
    refine q_add_congr ?_ ?_ <;>
    · refine Q'.eqv_trans _ _ _ (two_mul_eqv 1 q) ?_
      show ((1 : Q') * q + (1 : Q') * q).eqv (q + q)
      exact q_add_congr (Q'.one_mul_eqv q) (Q'.one_mul_eqv q)

/-- `two p ≤ two r` from `p ≤ r` (`p+p ≤ r+r`). -/
theorem two_le_two {p r : Q'} (h : p ≤ r) : HKPos.two p ≤ HKPos.two r :=
  Q'.le_trans' _ _ _ (Q'.add_le_add_right p r p h) (Q'.add_le_add_left r p r h)

/-- **`dBound a l ≤ Cinc·(1/2)^l`.**  Termwise from `geoAmp ≤ (1/2)^l`. -/
theorem dBound_le {a : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a ≤ (1 : Q')) (ha2 : a * a ≤ half) (l : Nat) :
    dBound a l ≤ Cinc * half ^ l := by
  -- dBound = two c + (two c + two c) ≤ two h^l + (two h^l + two h^l) ≃ Cinc·h^l
  have hc : HKPos.geoAmp a l ≤ half ^ l := geoAmp_le_half_pow ha0 ha1 ha2 l
  have h2c : HKPos.two (HKPos.geoAmp a l) ≤ HKPos.two (half ^ l) := two_le_two hc
  have hstep : dBound a l
      ≤ HKPos.two (half ^ l) + (HKPos.two (half ^ l) + HKPos.two (half ^ l)) := by
    show HKPos.two (HKPos.geoAmp a l)
        + (HKPos.two (HKPos.geoAmp a l) + HKPos.two (HKPos.geoAmp a l)) ≤ _
    exact Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ _ h2c)
      (Q'.add_le_add_left _ _ _
        (Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ _ h2c)
          (Q'.add_le_add_left _ _ _ h2c)))
  exact Q'.le_trans' _ _ _ hstep (Q'.ge_of_eqv (Cinc_mul_eqv (half ^ l)))

/-! ## 5. The partial product `Ppart` and its magnitude bound -/

/-- The Jacobi theta partial product `Ppart a x L = ∏_{k<L} gFac a x k`. -/
def Ppart (a x : Q') : Nat → Q'
  | 0 => 1
  | L + 1 => Ppart a x L * gFac a x L

@[simp] theorem Ppart_succ (a x : Q') (L : Nat) :
    Ppart a x (L + 1) = Ppart a x L * gFac a x L := rfl

/-- Every partial product is `> 0` (finite product of positive factors). -/
theorem Ppart_pos {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x) (L : Nat) :
    (0 : Q') < Ppart a x L := by
  induction L with
  | zero =>
      show (0 : Q') < (1 : Q')
      exact CReal.pos_of_num_pos (by decide)
  | succ L ih =>
      rw [Ppart_succ]
      exact HKPos.q_mul_pos ih (gFac_pos ha0 ha1 hx L)

theorem Ppart_nonneg {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x) (L : Nat) :
    (0 : Q') ≤ Ppart a x L :=
  Q'.le_of_lt (Ppart_pos ha0 ha1 hx L)

/-- `gFac a x k ≤ 1 + Tcoef a k`: the full factor is dominated by `1 + 2c + c²`. -/
theorem gFac_le_one_add_Tcoef {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q'))
    (k : Nat) :
    gFac a x k ≤ 1 + Tcoef a k := by
  have hc0 : (0 : Q') ≤ HKPos.geoAmp a k := Q'.le_of_lt (HKPos.pow_pos ha0 (2 * k + 1))
  have h2c_nn : (0 : Q') ≤ HKPos.two (HKPos.geoAmp a k) := HKPos.two_nonneg hc0
  -- gFac ≃ 1 + dev ;  dev ≤ two c * x + c*c ≤ two c + c*c = Tcoef
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (gFac_eqv_one_add_dev a x k)) ?_
  refine Q'.add_le_add_left 1 _ _ ?_
  -- devFac ≤ Tcoef
  -- dev = (two c*x + c*c) + (-(u·f)) ≤ (two c*x + c*c) ≤ two c + c*c = Tcoef
  have hdrop : devFac a x k ≤ HKPos.two (HKPos.geoAmp a k) * x
      + HKPos.geoAmp a k * HKPos.geoAmp a k := by
    show (HKPos.two (HKPos.geoAmp a k) * x + HKPos.geoAmp a k * HKPos.geoAmp a k)
        + (-(uAmp a k * HKPos.factor (HKPos.geoAmp a k) x)) ≤ _
    have huf_nn : (0 : Q') ≤ uAmp a k * HKPos.factor (HKPos.geoAmp a k) x := by
      have hu_nn : (0 : Q') ≤ uAmp a k := Q'.le_of_lt (uAmp_pos_lt_one ha0 ha1 k).1
      have hf_nn : (0 : Q') ≤ HKPos.factor (HKPos.geoAmp a k) x :=
        Q'.le_of_lt (HKPos.factor_pos hc0
          (HKPos.pow_succ_pos_lt_one ha0 ha1 (2 * k)).2 hx)
      exact Q'.mul_nonneg _ _ hu_nn hf_nn
    have hneg : (-(uAmp a k * HKPos.factor (HKPos.geoAmp a k) x)) ≤ (0 : Q') := by
      have := Q'.neg_le_neg huf_nn
      rwa [show (-(0 : Q')) = 0 from rfl] at this
    refine Q'.le_trans' _ _ _ (Q'.add_le_add_left _ _ 0 hneg) ?_
    exact Q'.le_of_eqv (q_add_zero_eqv _)
  have hcx : HKPos.two (HKPos.geoAmp a k) * x ≤ HKPos.two (HKPos.geoAmp a k) :=
    Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left x 1 (HKPos.two (HKPos.geoAmp a k)) hx1 h2c_nn)
      (Q'.le_of_eqv (Q'.mul_one_eqv (HKPos.two (HKPos.geoAmp a k))))
  -- Tcoef = two c + c*c
  show devFac a x k ≤ HKPos.two (HKPos.geoAmp a k) + HKPos.geoAmp a k * HKPos.geoAmp a k
  exact Q'.le_trans' _ _ _ hdrop (Q'.add_le_add_right _ _ _ hcx)

/-- **`Ppart a x L ≤ prodUp (Tcoef a) L`** (termwise product monotonicity of
nonnegative factors `0 ≤ gFac ≤ 1 + Tcoef`). -/
theorem Ppart_le_prodUp {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q'))
    (L : Nat) :
    Ppart a x L ≤ prodUp (Tcoef a) L := by
  induction L with
  | zero =>
      show (1 : Q') ≤ (1 : Q')
      exact Q'.le_refl' 1
  | succ L ih =>
      rw [Ppart_succ, prodUp_succ]
      -- Ppart L · gFac L ≤ prodUp L · (1 + Tcoef L)
      refine mul_le_mul' (Ppart_nonneg ha0 ha1 hx L) ?_ ih
        (gFac_le_one_add_Tcoef ha0 ha1 hx hx1 L)
      -- 0 ≤ 1 + Tcoef L
      have h1 : (0 : Q') ≤ (1 : Q') := Q'.le_of_lt (CReal.pos_of_num_pos (by decide))
      exact Q'.le_trans' _ _ _ h1
        (Q'.add_le_self_of_nonneg 1 (Tcoef a L) (Tcoef_nonneg ha0 L))

/-- **The partial-product magnitude bound `Ppart a x L ≤ 2`** under the smallness
`∀ L, finSum (Tcoef a) L ≤ 1/2`.  Chains `Ppart ≤ prodUp (Tcoef a) ≤ 2`. -/
theorem Ppart_le_two {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q'))
    (hsmall : ∀ L, finSum (Tcoef a) L ≤ half) (L : Nat) :
    Ppart a x L ≤ Q'.ofNat 2 :=
  Q'.le_trans' _ _ _ (Ppart_le_prodUp ha0 ha1 hx hx1 L)
    (prodUpBound (Tcoef_nonneg ha0) hsmall L)

/-! ## 6. The two-sided single-step increment bound

`Ppart (l+1) = Ppart l · gFac l ≃ Ppart l + Ppart l · dev_l`, and the increment
`Ppart l · dev_l` is bounded two-sidedly by `±(Cinc2·(1/2)^l)`, `Cinc2 = 2·Cinc = 12`:
`|Ppart l| ≤ 2`, `|dev_l| ≤ dBound l ≤ Cinc·(1/2)^l`, so
`|Ppart l · dev_l| ≤ 2·(Cinc·(1/2)^l) = Cinc2·(1/2)^l`. -/

/-- The engine increment constant `Cinc2 = 2·Cinc = 12`. -/
def Cinc2 : Q' := Q'.ofNat 2 * Cinc

theorem Cinc2_num_pos : 0 < Cinc2.num := by decide

/-- `Ppart a x (l+1) ≃ Ppart a x l + Ppart a x l · devFac a x l`. -/
theorem Ppart_succ_eqv (a x : Q') (l : Nat) :
    (Ppart a x (l + 1)).eqv (Ppart a x l + Ppart a x l * devFac a x l) := by
  rw [Ppart_succ]
  -- Ppart l · gFac l ≃ Ppart l · (1 + dev) ≃ Ppart l · 1 + Ppart l · dev ≃ Ppart l + Ppart l·dev
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left (Ppart a x l) _ _ (gFac_eqv_one_add_dev a x l)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.mul_add_eqv (Ppart a x l) 1 (devFac a x l)) ?_
  exact q_add_congr (Q'.mul_one_eqv (Ppart a x l)) (Q'.eqv_refl _)

/-- **Upper increment bound:** `Ppart l · dev_l ≤ Cinc2·(1/2)^l`. -/
theorem incr_le {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q'))
    (ha2 : a * a ≤ half) (hsmall : ∀ L, finSum (Tcoef a) L ≤ half) (l : Nat) :
    Ppart a x l * devFac a x l ≤ Cinc2 * half ^ l := by
  -- bounds: -2 ≤ Ppart ≤ 2 ; -dBound ≤ dev ≤ dBound, dBound ≥ 0
  have hPnn : (0 : Q') ≤ Ppart a x l := Ppart_nonneg ha0 ha1 hx l
  have hPle : Ppart a x l ≤ Q'.ofNat 2 := Ppart_le_two ha0 ha1 hx hx1 hsmall l
  have hPlo : -(Q'.ofNat 2) ≤ Ppart a x l :=
    Q'.le_trans' _ _ _ (by decide : -(Q'.ofNat 2) ≤ (0 : Q')) hPnn
  have hdlo : -(dBound a l) ≤ devFac a x l := neg_dBound_le_devFac ha0 ha1 hx hx1 l
  have hdhi : devFac a x l ≤ dBound a l := devFac_le ha0 ha1 hx hx1 l
  have hdBnn : (0 : Q') ≤ dBound a l := dBound_nonneg ha0 l
  -- Ppart · dev ≤ 2 · dBound
  have hmul : Ppart a x l * devFac a x l ≤ Q'.ofNat 2 * dBound a l :=
    Q'.mul_le_of_bounds (by decide) hdBnn hPlo hPle hdlo hdhi
  -- 2·dBound ≤ 2·(Cinc·half^l) = Cinc2·half^l
  have hdB : dBound a l ≤ Cinc * half ^ l := dBound_le ha0 (Q'.le_of_lt ha1) ha2 l
  have hmono : Q'.ofNat 2 * dBound a l ≤ Q'.ofNat 2 * (Cinc * half ^ l) :=
    Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 2) hdB (by decide)
  have hassoc : (Q'.ofNat 2 * (Cinc * half ^ l)).eqv (Cinc2 * half ^ l) :=
    Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat 2) Cinc (half ^ l))
  exact Q'.le_trans' _ _ _ hmul (Q'.le_trans' _ _ _ hmono (Q'.le_of_eqv hassoc))

/-- **Lower increment bound:** `−(Cinc2·(1/2)^l) ≤ Ppart l · dev_l`. -/
theorem neg_incr_le {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q'))
    (ha2 : a * a ≤ half) (hsmall : ∀ L, finSum (Tcoef a) L ≤ half) (l : Nat) :
    -(Cinc2 * half ^ l) ≤ Ppart a x l * devFac a x l := by
  -- apply incr_le to (-dev): Ppart · (-dev) ≤ Cinc2·half^l, and Ppart·(-dev) ≃ -(Ppart·dev)
  have hPnn : (0 : Q') ≤ Ppart a x l := Ppart_nonneg ha0 ha1 hx l
  have hPle : Ppart a x l ≤ Q'.ofNat 2 := Ppart_le_two ha0 ha1 hx hx1 hsmall l
  have hPlo : -(Q'.ofNat 2) ≤ Ppart a x l :=
    Q'.le_trans' _ _ _ (by decide : -(Q'.ofNat 2) ≤ (0 : Q')) hPnn
  have hdlo : -(dBound a l) ≤ devFac a x l := neg_dBound_le_devFac ha0 ha1 hx hx1 l
  have hdhi : devFac a x l ≤ dBound a l := devFac_le ha0 ha1 hx hx1 l
  have hdBnn : (0 : Q') ≤ dBound a l := dBound_nonneg ha0 l
  -- -dev ∈ [-dBound, dBound]
  have hndlo : -(dBound a l) ≤ -(devFac a x l) := Q'.neg_le_neg hdhi
  have hndhi : -(devFac a x l) ≤ dBound a l :=
    Q'.le_trans' _ _ _ (Q'.neg_le_neg hdlo) (Q'.le_of_eqv (Q'.neg_neg_eqv (dBound a l)))
  have hmul : Ppart a x l * (-(devFac a x l)) ≤ Q'.ofNat 2 * dBound a l :=
    Q'.mul_le_of_bounds (by decide) hdBnn hPlo hPle hndlo hndhi
  have hdB : dBound a l ≤ Cinc * half ^ l := dBound_le ha0 (Q'.le_of_lt ha1) ha2 l
  have hmono : Q'.ofNat 2 * dBound a l ≤ Q'.ofNat 2 * (Cinc * half ^ l) :=
    Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 2) hdB (by decide)
  have hassoc : (Q'.ofNat 2 * (Cinc * half ^ l)).eqv (Cinc2 * half ^ l) :=
    Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat 2) Cinc (half ^ l))
  have hupper : Ppart a x l * (-(devFac a x l)) ≤ Cinc2 * half ^ l :=
    Q'.le_trans' _ _ _ hmul (Q'.le_trans' _ _ _ hmono (Q'.le_of_eqv hassoc))
  -- Ppart·(-dev) ≃ -(Ppart·dev) ;  so -(Ppart·dev) ≤ Cinc2·half^l ⟹ -(Cinc2·half^l) ≤ Ppart·dev
  have heq : (Ppart a x l * (-(devFac a x l))).eqv (-(Ppart a x l * devFac a x l)) :=
    Q'.mul_neg_eqv (Ppart a x l) (devFac a x l)
  have hneg : -(Ppart a x l * devFac a x l) ≤ Cinc2 * half ^ l :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv heq) hupper
  -- from -(A) ≤ B get -B ≤ A
  refine Q'.le_trans' _ _ _ (Q'.neg_le_neg hneg) ?_
  exact Q'.le_of_eqv (Q'.neg_neg_eqv (Ppart a x l * devFac a x l))

/-! ## 7. `ϑ₃(x)` as a convergent `CReal` (the deliverable)

Feed the partial products `Ppart a x` to `Continuum.crealOfGeoIncrement` with the
two-sided geometric increment bound of §6 at the constant `Cinc2`. -/

/-- **THE DELIVERABLE: `ϑ₃(x)` as a convergent `CReal` with explicit modulus,**
in the regime `a·a ≤ 1/2` together with the smallness `∀ L, finSum (Tcoef a) L ≤ 1/2`.
`approx N = Ppart a x N` (the genuine finite truncation `∏_{k<N}(1−a^{2k+2})·factorₖ`);
the Cauchy modulus is the `HalfPow` modulus inherited from `crealOfGeoIncrement`
at the constant `Cinc2 = 12`. -/
def thetaConvCReal {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q'))
    (ha2 : a * a ≤ half) (hsmall : ∀ L, finSum (Tcoef a) L ≤ half) : CReal :=
  crealOfGeoIncrement (Ppart a x) Cinc2
    (Q'.le_of_lt (CReal.pos_of_num_pos Cinc2_num_pos))
    -- hup : Ppart (l+1) ≤ Ppart l + geoIncr Cinc2 l
    (fun l => by
      refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Ppart_succ_eqv a x l)) ?_
      refine Q'.add_le_add_left (Ppart a x l) _ (geoIncr Cinc2 l) ?_
      show Ppart a x l * devFac a x l ≤ Cinc2 * half ^ l
      exact incr_le ha0 ha1 hx hx1 ha2 hsmall l)
    -- hlo : Ppart l ≤ Ppart (l+1) + geoIncr Cinc2 l
    (fun l => by
      -- Ppart (l+1) + geoIncr ≃ (Ppart l + Ppart l·dev) + Cinc2·half^l
      have heq : (Ppart a x (l + 1) + geoIncr Cinc2 l).eqv
          ((Ppart a x l + Ppart a x l * devFac a x l) + Cinc2 * half ^ l) :=
        Q'.add_eqv_congr_right _ _ (Cinc2 * half ^ l) (Ppart_succ_eqv a x l)
      refine Q'.le_trans' _ _ _ ?_ (Q'.ge_of_eqv heq)
      -- Ppart l ≤ (Ppart l + Ppart l·dev) + Cinc2·half^l
      -- ≃ Ppart l + (Ppart l·dev + Cinc2·half^l) ; suffices 0 ≤ Ppart l·dev + Cinc2·half^l
      refine Q'.le_trans' _ _ _
        (Q'.add_le_self_of_nonneg (Ppart a x l)
          (Ppart a x l * devFac a x l + Cinc2 * half ^ l) ?_)
        (Q'.le_of_eqv (Q'.eqv_symm
          (Q'.add_assoc_eqv (Ppart a x l) (Ppart a x l * devFac a x l) (Cinc2 * half ^ l))))
      -- 0 ≤ Ppart l·dev + Cinc2·half^l  ⟺  -(Cinc2·half^l) ≤ Ppart l·dev
      have hlo := neg_incr_le ha0 ha1 hx hx1 ha2 hsmall l
      have h1 : -(Cinc2 * half ^ l) + Cinc2 * half ^ l ≤ Ppart a x l * devFac a x l
          + Cinc2 * half ^ l :=
        Q'.add_le_add_right _ _ (Cinc2 * half ^ l) hlo
      refine Q'.le_trans' _ _ _ ?_ h1
      exact Q'.ge_of_eqv (Q'.neg_add_self_eqv (Cinc2 * half ^ l)))
    -- modulus : ∃ δ>0, (2·Cinc2)·δ ≤ ε,  δ = divPos ε (2·Cinc2)
    (fun ε hε => by
      have h2Cpos : 0 < (Q'.ofNat 2 * Cinc2).num := by
        show 0 < (2 : Int) * Cinc2.num
        exact Int.mul_pos (by decide) Cinc2_num_pos
      refine ⟨divPos ε (Q'.ofNat 2 * Cinc2), divPos_pos (CReal.num_pos_of_pos hε), ?_⟩
      refine Q'.le_of_eqv ?_
      refine Q'.eqv_trans _ _ _
        (Q'.mul_comm_eqv (Q'.ofNat 2 * Cinc2) (divPos ε (Q'.ofNat 2 * Cinc2))) ?_
      exact divPos_mul_eqv h2Cpos)

/-- `ϑ₃`'s `N`-th approximation is exactly the finite-volume partial product. -/
@[simp] theorem thetaConvCReal_approx {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q'))
    (ha2 : a * a ≤ half) (hsmall : ∀ L, finSum (Tcoef a) L ≤ half) (N : Nat) :
    (thetaConvCReal ha0 ha1 hx hx1 ha2 hsmall).approx N = Ppart a x N := rfl

/-- Every approximation of the `ϑ₃` `CReal` is `≥ 0`. -/
theorem thetaConvCReal_approx_nonneg {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q'))
    (ha2 : a * a ≤ half) (hsmall : ∀ L, finSum (Tcoef a) L ≤ half) (N : Nat) :
    (0 : Q') ≤ (thetaConvCReal ha0 ha1 hx hx1 ha2 hsmall).approx N := by
  rw [thetaConvCReal_approx]
  exact Ppart_nonneg ha0 ha1 hx N

/-- **The `ϑ₃` `CReal`'s limit is `≥ 0`** (`ExpPos.geRat … 0`). -/
theorem thetaConvCReal_geRat_zero {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q'))
    (ha2 : a * a ≤ half) (hsmall : ∀ L, finSum (Tcoef a) L ≤ half) :
    ExpPos.geRat (thetaConvCReal ha0 ha1 hx hx1 ha2 hsmall) 0 := by
  apply ExpPos.geRat_of_eventually
  exact ⟨0, fun N _ => thetaConvCReal_approx_nonneg ha0 ha1 hx hx1 ha2 hsmall N⟩

/-! ## 8. The assembled `R = ϑ₃·S ≥ 0` (the `Θ`-hypothesis discharged)

`HKConv.R_geRat_zero_of_theta` closed `Θ·S ≥ 0` given any nonneg-approx `Θ`; we
now supply `Θ = thetaConvCReal`, removing the last hypothetical caveat. -/

/-- **THE FULL `R(x) = ϑ₃(x)·S(x) ≥ 0` as a `CReal`** under `0 < a`, `a < 1`,
`−1 ≤ x ≤ 1`, `a·a ≤ 1/2`, and the smallness `∀ L, finSum (Tcoef a) L ≤ 1/2`.
Both factors are now genuine convergent `CReal`s with explicit moduli
(`thetaConvCReal` and `HKConv.sConvCReal`); their product's limit is `≥ 0` via
`HKConv.R_geRat_zero_of_theta` (which packages `HKPos2.mul_geRat_zero`). -/
theorem R_geRat_zero {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q'))
    (ha2 : a * a ≤ half) (hsmall : ∀ L, finSum (Tcoef a) L ≤ half) :
    ExpPos.geRat
      (CReal.mul (thetaConvCReal ha0 ha1 hx hx1 ha2 hsmall)
        (HKConv.sConvCReal ha0 ha1 hx ha2)) 0 :=
  HKConv.R_geRat_zero_of_theta ha0 ha1 hx ha2
    (thetaConvCReal ha0 ha1 hx hx1 ha2 hsmall)
    (thetaConvCReal_approx_nonneg ha0 ha1 hx hx1 ha2 hsmall)

/-! ## 9. Discharging the smallness hypothesis for `a ≤ 1/16`

`Tcoef a k = 2c_k + c_k² ≤ 3c_k ≤ 3a·(1/2)^k` (under `a² ≤ 1/2`, `c_k ≤ 1`), so
`Σ_{k<L} Tcoef a k ≤ 2·(3a) = 6a ≤ 6/16 = 3/8 ≤ 1/2` once `a ≤ 1/16`.  This gives
a clean concrete regime where the product-magnitude bound (and hence `ϑ₃` and
the full `R ≥ 0`) holds unconditionally. -/

/-- `Tcoef a k ≤ (a + (a + a))·(1/2)^k` (`= 3a·(1/2)^k`) under `0 < a ≤ 1`,
`a·a ≤ 1/2`.  Termwise: `c_k ≤ a·(1/2)^k`, `2c + c² ≤ 3c`. -/
theorem Tcoef_le {a : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a ≤ (1 : Q')) (ha2 : a * a ≤ half) (k : Nat) :
    Tcoef a k ≤ (a + (a + a)) * half ^ k := by
  have hc0 : (0 : Q') ≤ HKPos.geoAmp a k := Q'.le_of_lt (HKPos.pow_pos ha0 (2 * k + 1))
  have hc1 : HKPos.geoAmp a k ≤ (1 : Q') :=
    HKPos.pow_le_one (Q'.le_of_lt ha0) ha1 (2 * k + 1)
  -- c_k ≤ a·half^k :  c_k = a·(a²)^k ≤ a·half^k
  have hc_le : HKPos.geoAmp a k ≤ a * half ^ k := by
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (geoAmp_eqv a k)) ?_
    have haa_nn : (0 : Q') ≤ a * a := Q'.mul_nonneg a a (Q'.le_of_lt ha0) (Q'.le_of_lt ha0)
    have hpow : (a * a) ^ k ≤ half ^ k := pow_le_pow_base haa_nn ha2 k
    exact Q'.mul_le_mul_of_nonneg_left _ _ a hpow (Q'.le_of_lt ha0)
  -- Tcoef = (c + c) + c·c ≤ c + (c + c)  (c·c ≤ c) — collect 3 copies of c
  have hcc : HKPos.geoAmp a k * HKPos.geoAmp a k ≤ HKPos.geoAmp a k :=
    Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ 1 _ hc1 hc0)
      (Q'.le_of_eqv (Q'.mul_one_eqv (HKPos.geoAmp a k)))
  have hT3 : Tcoef a k ≤ HKPos.geoAmp a k + (HKPos.geoAmp a k + HKPos.geoAmp a k) := by
    show (HKPos.geoAmp a k + HKPos.geoAmp a k) + HKPos.geoAmp a k * HKPos.geoAmp a k ≤ _
    -- (c + c) + c·c ≤ (c + c) + c ≃ c + (c + c)
    refine Q'.le_trans' _ _ _
      (Q'.add_le_add_left (HKPos.geoAmp a k + HKPos.geoAmp a k) _ _ hcc) ?_
    -- (c + c) + c ≃ c + (c + c)
    exact Q'.le_of_eqv (Q'.add_assoc_eqv (HKPos.geoAmp a k) (HKPos.geoAmp a k) (HKPos.geoAmp a k))
  -- 3 copies of c ≤ 3 copies of a·half^k ≃ (a+(a+a))·half^k
  have hmono : HKPos.geoAmp a k + (HKPos.geoAmp a k + HKPos.geoAmp a k)
      ≤ a * half ^ k + (a * half ^ k + a * half ^ k) :=
    Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ _ hc_le)
      (Q'.add_le_add_left _ _ _
        (Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ _ hc_le)
          (Q'.add_le_add_left _ _ _ hc_le)))
  have hdist : ((a + (a + a)) * half ^ k).eqv
      (a * half ^ k + (a * half ^ k + a * half ^ k)) := by
    refine Q'.eqv_trans _ _ _ (Q'.add_mul_eqv a (a + a) (half ^ k)) ?_
    exact q_add_congr (Q'.eqv_refl _) (Q'.add_mul_eqv a a (half ^ k))
  exact Q'.le_trans' _ _ _ hT3 (Q'.le_trans' _ _ _ hmono (Q'.ge_of_eqv hdist))

/-- **Smallness discharge:** `∀ L, finSum (Tcoef a) L ≤ 1/2` for `a ≤ 1/16`
(with `0 < a`).  Hence `thetaConvCReal` / `R_geRat_zero` apply unconditionally in
that regime. -/
theorem Tcoef_sum_small_of_le_sixteenth {a : Q'}
    (ha0 : (0 : Q') < a) (haS : a ≤ Q'.mkPos 1 16 (by decide)) (L : Nat) :
    finSum (Tcoef a) L ≤ half := by
  have ha1 : a ≤ (1 : Q') := Q'.le_trans' _ _ _ haS (by decide)
  have ha2 : a * a ≤ half := by
    -- a·a ≤ (1/16)·(1/16) = 1/256 ≤ 1/2
    refine Q'.le_trans' _ _ _
      (mul_le_mul' (Q'.le_of_lt ha0)
        (by decide : (0:Q') ≤ Q'.mkPos 1 16 (by decide)) haS haS) ?_
    decide
  -- finSum Tcoef ≤ finSum (fun k => (a+(a+a))·half^k) ≤ 2·(a+(a+a)) ≤ half
  have hterm : finSum (Tcoef a) L
      ≤ finSum (fun k => (a + (a + a)) * half ^ k) L :=
    CharacterTail.finSum_le_termwise (Tcoef a) (fun k => (a + (a + a)) * half ^ k)
      (fun k => Tcoef_le ha0 ha1 ha2 k) L
  have hgeo : finSum (fun k => (a + (a + a)) * half ^ k) L ≤ Q'.ofNat 2 * (a + (a + a)) := by
    have hKnn : (0 : Q') ≤ a + (a + a) :=
      Q'.zero_le_add _ _ (Q'.le_of_lt ha0) (Q'.zero_le_add _ _ (Q'.le_of_lt ha0) (Q'.le_of_lt ha0))
    exact geom_half_series_le (a + (a + a)) hKnn L
  -- 2·(a+(a+a)) ≤ 2·(1/16+(1/16+1/16)) = 6/16 = 3/8 ≤ 1/2
  have hfinal : Q'.ofNat 2 * (a + (a + a)) ≤ half := by
    have hmono : a + (a + a)
        ≤ Q'.mkPos 1 16 (by decide) + (Q'.mkPos 1 16 (by decide) + Q'.mkPos 1 16 (by decide)) :=
      Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ _ haS)
        (Q'.add_le_add_left _ _ _
          (Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ _ haS)
            (Q'.add_le_add_left _ _ _ haS)))
    refine Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 2) hmono (by decide)) ?_
    decide
  exact Q'.le_trans' _ _ _ hterm (Q'.le_trans' _ _ _ hgeo hfinal)

/-! ## 10. Capstone: unconditional `R ≥ 0` in the regime `a ≤ 1/16`

For `0 < a ≤ 1/16` the strictness `a < 1` and the regime `a·a ≤ 1/2` follow, and
the smallness is discharged, so `ϑ₃` and the full `R ≥ 0` hold with NO residual
side hypotheses beyond `0 < a ≤ 1/16` and `−1 ≤ x ≤ 1`. -/

/-- `a < 1` from `0 < a ≤ 1/16`. -/
theorem lt_one_of_le_sixteenth {a : Q'} (haS : a ≤ Q'.mkPos 1 16 (by decide)) :
    a < (1 : Q') :=
  HKPos.q_lt_of_le_of_lt haS (by decide)

/-- `a·a ≤ 1/2` from `0 < a ≤ 1/16`. -/
theorem mul_self_le_half_of_le_sixteenth {a : Q'}
    (ha0 : (0 : Q') < a) (haS : a ≤ Q'.mkPos 1 16 (by decide)) :
    a * a ≤ half := by
  refine Q'.le_trans' _ _ _
    (mul_le_mul' (Q'.le_of_lt ha0)
      (by decide : (0:Q') ≤ Q'.mkPos 1 16 (by decide)) haS haS) ?_
  decide

/-- **`ϑ₃(x)` as a `CReal`, unconditionally for `0 < a ≤ 1/16`, `−1 ≤ x ≤ 1`.** -/
def thetaConvCReal_sixteenth {a x : Q'}
    (ha0 : (0 : Q') < a) (haS : a ≤ Q'.mkPos 1 16 (by decide))
    (hx : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q')) : CReal :=
  thetaConvCReal ha0 (lt_one_of_le_sixteenth haS) hx hx1
    (mul_self_le_half_of_le_sixteenth ha0 haS)
    (Tcoef_sum_small_of_le_sixteenth ha0 haS)

/-- **THE FULL `R(x) = ϑ₃(x)·S(x) ≥ 0`, unconditionally for `0 < a ≤ 1/16`,
`−1 ≤ x ≤ 1`.**  The smallness hypothesis is discharged; both factors are genuine
convergent `CReal`s with explicit moduli; the `Θ`-hypothesis of
`HKConv.R_geRat_zero_of_theta` is fully discharged.  This is the assembled
manifest nonnegativity of the heat-kernel product object, modulo only the
separate G2 identity `K_t = R`. -/
theorem R_geRat_zero_sixteenth {a x : Q'}
    (ha0 : (0 : Q') < a) (haS : a ≤ Q'.mkPos 1 16 (by decide))
    (hx : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q')) :
    ExpPos.geRat
      (CReal.mul
        (thetaConvCReal ha0 (lt_one_of_le_sixteenth haS) hx hx1
          (mul_self_le_half_of_le_sixteenth ha0 haS)
          (Tcoef_sum_small_of_le_sixteenth ha0 haS))
        (HKConv.sConvCReal ha0 (lt_one_of_le_sixteenth haS) hx
          (mul_self_le_half_of_le_sixteenth ha0 haS))) 0 :=
  R_geRat_zero ha0 (lt_one_of_le_sixteenth haS) hx hx1
    (mul_self_le_half_of_le_sixteenth ha0 haS)
    (Tcoef_sum_small_of_le_sixteenth ha0 haS)

end YMGap.Continuum.ThetaConv

/-! ## Axiom-dependency gates (AGENTS.md Rule 1)

Every load-bearing theorem reports `[propext]` or `[propext, Quot.sound]`
(`Quot.sound` enters only through reused `Nat`/`Int`/`omega`/`finSum`/`decide`
helpers).  No `Classical.*`, no `native_decide`, no `sorry`. -/

#print axioms YMGap.Continuum.ThetaConv.prodUp_nonneg
#print axioms YMGap.Continuum.ThetaConv.prodLow_nonneg
#print axioms YMGap.Continuum.ThetaConv.one_plus_mul_one_minus_eqv
#print axioms YMGap.Continuum.ThetaConv.prodUp_mul_prodLow_le_one
#print axioms YMGap.Continuum.ThetaConv.finSum_nonneg
#print axioms YMGap.Continuum.ThetaConv.weierstrass_lower
#print axioms YMGap.Continuum.ThetaConv.term_le_half_of_small
#print axioms YMGap.Continuum.ThetaConv.prodUpBound
#print axioms YMGap.Continuum.ThetaConv.gFac_pos
#print axioms YMGap.Continuum.ThetaConv.gFac_eqv_one_add_dev
#print axioms YMGap.Continuum.ThetaConv.uAmp_le_geoAmp
#print axioms YMGap.Continuum.ThetaConv.factor_le_four
#print axioms YMGap.Continuum.ThetaConv.uf_le
#print axioms YMGap.Continuum.ThetaConv.devFac_le
#print axioms YMGap.Continuum.ThetaConv.neg_dBound_le_devFac
#print axioms YMGap.Continuum.ThetaConv.geoAmp_le_half_pow
#print axioms YMGap.Continuum.ThetaConv.dBound_le
#print axioms YMGap.Continuum.ThetaConv.Ppart_pos
#print axioms YMGap.Continuum.ThetaConv.gFac_le_one_add_Tcoef
#print axioms YMGap.Continuum.ThetaConv.Ppart_le_prodUp
#print axioms YMGap.Continuum.ThetaConv.Ppart_le_two
#print axioms YMGap.Continuum.ThetaConv.incr_le
#print axioms YMGap.Continuum.ThetaConv.neg_incr_le
#print axioms YMGap.Continuum.ThetaConv.thetaConvCReal
#print axioms YMGap.Continuum.ThetaConv.thetaConvCReal_approx_nonneg
#print axioms YMGap.Continuum.ThetaConv.thetaConvCReal_geRat_zero
#print axioms YMGap.Continuum.ThetaConv.R_geRat_zero
#print axioms YMGap.Continuum.ThetaConv.Tcoef_le
#print axioms YMGap.Continuum.ThetaConv.Tcoef_sum_small_of_le_sixteenth
#print axioms YMGap.Continuum.ThetaConv.thetaConvCReal_sixteenth
#print axioms YMGap.Continuum.ThetaConv.R_geRat_zero_sixteenth
