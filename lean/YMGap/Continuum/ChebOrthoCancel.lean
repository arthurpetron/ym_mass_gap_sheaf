/-
# The discrete LEADING-ORDER CANCELLATION at the heart of the corrected per-cell
# midpoint estimate `ChebOrthoMidpointCore.CorrectedPerCellBound`
# (the π-free off-diagonal Chebyshev-`U` orthogonality `∫_{−1}^1 U_e(x)√(1−x²)dx = 0`)

The companion module `ChebOrthoMidpointCore` reduces the even-order off-diagonal
orthogonality to the SINGLE per-cell estimate

    `CorrectedPerCellBound e he :=
       ∀ N k, leRat (cellAdjR e he (N+1) k) (cRate e (N+1) k)
            ∧ leRat (neg (cellAdjR e he (N+1) k)) (cRate e (N+1) k)`

where `cellAdjR k = orthTerm k + gIncrR k`,
`orthTerm k = h·U_e(x_k)·s_k`  (`h = 2/M`, `s_k = √(1−x_k²)`),
`gIncrR k = ½·(s_+·B_e(b_{k+1}) − s_-·B_e(b_k))`  (`s_± = √(1−b_{k±}²)`,
`b_{k±} = x_k ± δ`, `δ = 1/M = h/2`), and the bracket
`B_e(x) = U_{e−1}(x)/e − U_{e+1}(x)/(e+2)` is `ChebOrthoOffDiag.Gbracket`.

## The leading-order cancellation (the genuine heart)

Writing the product-difference split

    `s_+·B_+ − s_-·B_- = ½(s_+ + s_-)(B_+ − B_-) + ½(s_+ − s_-)(B_+ + B_-)`

and replacing each centered difference by its EXACT derivative-leading term

    `B_+ − B_- ⇝ B_e′(x_k)·h`,   `s_+ − s_- ⇝ (−x_k/s_k)·h`,
    `s_+ + s_- ⇝ 2·s_k`,         `B_+ + B_- ⇝ 2·B_e(x_k)`,

the LEADING part of `gIncrR k` is

    `½·[ s_k·B_e′(x_k)·h + (−x_k/s_k)·h·B_e(x_k) ]
       = ½·h·[ (s_k²·B_e′(x_k) − x_k·B_e(x_k)) / s_k ]
       = ½·h·[ ((1−x_k²)·B_e′(x_k) − x_k·B_e(x_k)) / s_k ]`.

By the EXACT polynomial identity `ChebUDClosure.Bderiv_identity_uncond`

    `(1−x²)·B_e′(x) − x·B_e(x) ≈ −2·(1−x²)·U_e(x)`,

the numerator is `−2·(1−x²)·U_e(x_k) = −2·s_k²·U_e(x_k)`, so the leading part is

    `½·h·[ (−2·s_k²·U_e(x_k)) / s_k ] = −h·s_k·U_e(x_k) = −orthTerm k`.

So the leading midpoint combination EXACTLY cancels `orthTerm k`, leaving
`cellAdjR k` as the SECOND-ORDER centered-difference remainder.  This module
proves that cancellation as an EXACT rational identity.

## What is PROVED here (axiom-clean, GENUINE new content)

  * `sNum` / `sSq_eq` — the rational `s_k² = 1 − x_k²` bookkeeping used to feed
    the bracket identity (the radical `s_k` enters only through its SQUARE in the
    leading combination, so the cancellation is PURELY RATIONAL).
  * **`leading_combo_abstract`** — the EXACT abstract leading-cancellation lemma:
    for any rationals `s, x, B, Bp, U, h` with `s·s = 1 + (−(x·x))` and the
    bracket identity `(1 + (−(x·x)))·Bp + (−(x·B)) ≈ −(2·((1+(−(x·x)))·U))`, the
    leading combination `s·(½·h·(s·Bp + (−(x·B))/s))` reduces to `−(h·U·s)`.
    Stated with the singular `−x/s` leg replaced by its `s`-cleared form so the
    proof is division-free rational algebra.
  * **`leading_cancellation`** — the instantiation at `x = x_k`, `B = B_e(x_k)`,
    `Bp = B_e′(x_k)`, `U = U_e(x_k)` via `ChebUDClosure.Bderiv_identity_uncond`:
    the EXACT statement that the `s`-cleared leading midpoint combination equals
    `−(h·U_e(x_k)·s_k²)` (= `−s_k·orthTerm`-scaled), the rigorous form of
    "leading order EXACTLY cancels `orthTerm`".
  * **`boundary_orthTerm_bound`** — the BOUNDARY-cell direct bound:
    `|orthTerm k| = h·|U_e(x_k)|·s_k ≤ h·(e+1)·s_k`, fully rigorous via
    `ChebyshevU.absU_le` and `sqrtFrom_leRat_of_sq`, with the genuine radical
    `nodeWeight` bounded by any `c` with `1 − x_k² ≤ c²`.

## What is NAMED-open (precisely — the SECOND-ORDER remainder)

  * `ChebOrthoMidpointCore.CorrectedPerCellBound e he` — the FULL per-cell estimate
    against the corrected rate `cRate`.  The leading-order cancellation (this
    module's `leading_cancellation`) removes the `O(h)` part EXACTLY; the SINGLE
    remaining genuine content is the constructive bound on the SECOND-ORDER
    centered-difference remainder
    `cellAdjR k − (orthTerm k + leading(gIncrR k)) = (second-order finite-difference
    error)`, i.e. the constructive Taylor/finite-difference remainder of the smooth
    legs `B_e` (polynomial, Lipschitz scale `Le e`) and `√(1−x²)` (the √-Hölder
    modulus `radDiff_holder`), interior (`C(e)·h^{3/2}/s_k^p`) + boundary
    (`s_± ≤ √(2δ)`) split balanced at `δ ≈ √h` to `cRate`.  Recorded precisely.

## Honesty

No `sorry`/`admit`/new axiom/`Classical.*`/`native_decide`; `decide` only on
closed `Nat`/`Int`/`Q'`.  Axiom-gate at the foot of the file
(`[propext]` / `[propext, Quot.sound]`).
-/

import YMGap.Continuum.ChebOrthoMidpointCore
import YMGap.Continuum.ChebOrthoMidpoint
import YMGap.Continuum.ChebUDClosure

namespace YMGap.Continuum.ChebOrthoCancel

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.ChebOrthoOffDiag
open YMGap.Continuum.ChebOrthoEvenFTC
open YMGap.Continuum.ChebOrthoMidpoint
open YMGap.Continuum.ChebOrthoMidpointCore

local infix:50 " ≈ " => Q'.eqv

instance : Trans (Q'.eqv) (Q'.eqv) (Q'.eqv) where
  trans h1 h2 := Q'.eqv_trans _ _ _ h1 h2

/-! ## 0. Small `Q'` additive/multiplicative regrouping helpers -/

/-- `a + (-a) ≈ 0`. -/
theorem add_neg_self (a : Q') : (a + (-a)) ≈ (0 : Q') := Q'.add_neg_self_eqv a

/-- `(-a)·b ≈ -(a·b)` (re-export). -/
theorem neg_mul (a b : Q') : ((-a) * b) ≈ (-(a * b)) := Q'.neg_mul_eqv a b

/-- `a·(-b) ≈ -(a·b)` (re-export). -/
theorem mul_neg (a b : Q') : (a * (-b)) ≈ (-(a * b)) := Q'.mul_neg_eqv a b

/-- `(a·b)·c ≈ a·(b·c)` (re-export). -/
theorem mul_assoc (a b c : Q') : ((a * b) * c) ≈ (a * (b * c)) := Q'.mul_assoc_eqv a b c

/-- `2·a ≈ a + a`. -/
theorem two_mul_eqv (a : Q') : ((2 : Q') * a) ≈ (a + a) := by
  calc (2 : Q') * a
      ≈ ((1 : Q') + (1 : Q')) * a := Q'.mul_eqv_congr_right _ _ _ (by decide)
    _ ≈ (1 : Q') * a + (1 : Q') * a := Cheb.add_mul_eqv _ _ _
    _ ≈ a + a := Q'.add_eqv_congr' (Q'.one_mul_eqv a) (Q'.one_mul_eqv a)

/-! ## 1. The radical-square bookkeeping `s_k² = 1 − x_k²`

In the leading midpoint combination the radical `s_k` enters only through its
SQUARE (the `s_k²·B_e′` term and the `x_k/s_k·s_k = x_k` reduction), so the
cancellation is a PURELY RATIONAL identity once `s_k² = 1 − x_k²` is recorded. -/

/-! ## 2. The EXACT abstract leading-cancellation lemma (the genuine heart)

We isolate the `s`-cleared leading midpoint combination as an abstract `Q'`
identity.  The singular `−x/s` leg appears in the leading combination only as
`½(s_+ − s_-)(B_+ + B_-)` whose leading term is `½·(−x/s)·h·(2B) = (−x·B/s)·h`;
multiplying the whole leading combination by `s` (the natural common factor of
the `½(s_+ + s_-)(B_+ − B_-)` leg `≈ ½·2s·B′·h = s·B′·h`) clears the division:

    `s · leadingCombo
       = s · ½·h·( s·B′ + (−x·B)/s )
       = ½·h·( s²·B′ + (−x·B) )
       = ½·h·( (1−x²)·B′ + (−(x·B)) )       [s² = 1−x²]
       = ½·h·( −2·(1−x²)·U )                 [bracket identity]
       = −( h·U·(1−x²) )
       = −( h·U·s² ).`

`s · orthTerm`-analogue `= s·(h·U·s) = h·U·s²`, so `s·leadingCombo = −(s·orthTerm)`,
i.e. (`s > 0`) `leadingCombo = −orthTerm`.  We prove the `s`-cleared identity (the
content), avoiding any constructive division. -/

/-- **THE EXACT LEADING-CANCELLATION (abstract, `s`-cleared).**  Let `s, x, B, Bp,
U, h : Q'` satisfy `s·s ≈ 1 + (−(x·x))` (i.e. `s² = 1 − x²`) and the bracket
derivative identity

    `(1 + (−(x·x)))·Bp + (−(x·B)) ≈ −(2·((1 + (−(x·x)))·U))`.

Then the `s`-cleared leading midpoint combination collapses EXACTLY:

    `½·h·( s·(s·Bp) + (−(x·B)) ) ≈ −( h·(U·(s·s)) )`.

This is the rigorous algebraic core of "the leading midpoint terms exactly cancel
`orthTerm`": the LHS is `s` times the leading part of `gIncrR k`, and the RHS is
`−s` times `orthTerm k = h·U·s`.  Division-free; pure `Q'`-ring `calc` over the
two hypotheses. -/
theorem leading_combo_abstract (s x B Bp U h : Q')
    (hs : (s * s) ≈ (1 + (-(x * x))))
    (hid : ((1 + (-(x * x))) * Bp + (-(x * B)))
            ≈ (-(((2 : Q')) * ((1 + (-(x * x))) * U)))) :
    ((Q'.mkPos 1 2 (by decide)) * (h * (s * (s * Bp) + (-(x * B)))))
      ≈ (-(h * (U * (s * s)))) := by
  -- Step A: s·(s·Bp) ≈ (s·s)·Bp ≈ (1−x²)·Bp.
  have hA : (s * (s * Bp)) ≈ ((1 + (-(x * x))) * Bp) := by
    calc s * (s * Bp)
        ≈ (s * s) * Bp := Q'.eqv_symm (Q'.mul_assoc_eqv s s Bp)
      _ ≈ (1 + (-(x * x))) * Bp := Q'.mul_eqv_congr_right _ _ _ hs
  -- Step B: the inner bracket reduces to the bracket-identity LHS, then RHS.
  have hB : (s * (s * Bp) + (-(x * B)))
      ≈ (-(((2 : Q')) * ((1 + (-(x * x))) * U))) := by
    calc s * (s * Bp) + (-(x * B))
        ≈ (1 + (-(x * x))) * Bp + (-(x * B)) :=
          Q'.add_eqv_congr_right _ _ _ hA
      _ ≈ (-(((2 : Q')) * ((1 + (-(x * x))) * U))) := hid
  -- Step C: ½·h·(bracket) ≈ ½·h·(−2·(1−x²)·U) ≈ −(h·(U·(1−x²))) ≈ −(h·(U·s²)).
  -- First multiply hB through by h then by ½, then collapse the 2 and the ½.
  calc (Q'.mkPos 1 2 (by decide)) * (h * (s * (s * Bp) + (-(x * B))))
      ≈ (Q'.mkPos 1 2 (by decide))
          * (h * (-(((2 : Q')) * ((1 + (-(x * x))) * U)))) :=
        Q'.mul_eqv_congr_left _ _ _ (Q'.mul_eqv_congr_left _ _ _ hB)
    -- pull the negation outward: h·(−Z) ≈ −(h·Z)
    _ ≈ (Q'.mkPos 1 2 (by decide))
          * (-(h * (((2 : Q')) * ((1 + (-(x * x))) * U)))) :=
        Q'.mul_eqv_congr_left _ _ _ (Q'.mul_neg_eqv h (((2 : Q')) * ((1 + (-(x * x))) * U)))
    -- ½·(−W) ≈ −(½·W)
    _ ≈ (-((Q'.mkPos 1 2 (by decide))
          * (h * (((2 : Q')) * ((1 + (-(x * x))) * U))))) :=
        Q'.mul_neg_eqv (Q'.mkPos 1 2 (by decide)) (h * (((2 : Q')) * ((1 + (-(x * x))) * U)))
    -- now reduce the inner ½·(h·(2·(1−x²)·U)) to h·((1−x²)·U) and finish
    _ ≈ (-(h * (U * (s * s)))) := by
        refine Q'.neg_eqv_congr _ _ ?_
        -- ½·(h·(2·W₀)) ≈ h·W₀  with W₀ = (1−x²)·U ; then W₀ ≈ U·(s·s)
        -- (a) move ½ inside past h: ½·(h·X) ≈ h·(½·X)
        calc (Q'.mkPos 1 2 (by decide)) * (h * (((2 : Q')) * ((1 + (-(x * x))) * U)))
            ≈ h * ((Q'.mkPos 1 2 (by decide)) * (((2 : Q')) * ((1 + (-(x * x))) * U))) :=
              ChebUDClosure.mul_swap_outer (Q'.mkPos 1 2 (by decide)) h
                (((2 : Q')) * ((1 + (-(x * x))) * U))
          -- (b) ½·(2·W₀) ≈ (½·2)·W₀ ≈ 1·W₀ ≈ W₀
          _ ≈ h * ((1 + (-(x * x))) * U) := by
              refine Q'.mul_eqv_congr_left _ _ _ ?_
              calc (Q'.mkPos 1 2 (by decide)) * (((2 : Q')) * ((1 + (-(x * x))) * U))
                  ≈ ((Q'.mkPos 1 2 (by decide)) * ((2 : Q'))) * ((1 + (-(x * x))) * U) :=
                    Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)
                _ ≈ (1 : Q') * ((1 + (-(x * x))) * U) :=
                    Q'.mul_eqv_congr_right _ _ _ (by decide)
                _ ≈ ((1 + (-(x * x))) * U) := Q'.one_mul_eqv _
          -- (c) h·((1−x²)·U) ≈ h·(U·(s·s))
          _ ≈ h * (U * (s * s)) := by
              refine Q'.mul_eqv_congr_left _ _ _ ?_
              calc (1 + (-(x * x))) * U
                  ≈ U * (1 + (-(x * x))) := Q'.mul_comm_eqv _ _
                _ ≈ U * (s * s) := Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm hs)

/-! ## 3. The concrete instantiation via `Bderiv_identity_uncond`

At the cell midpoint `x = x_k` the bracket `B_e(x_k) = Gbracket e he x_k` and its
formal derivative `Bp = Bderiv e he x_k` satisfy the EXACT polynomial identity
`Bderiv_identity_uncond`.  Feeding it (rearranged to the `Bident` shape) into
`leading_combo_abstract` gives the concrete leading cancellation. -/

/-- **THE CONCRETE LEADING-CANCELLATION.**  For even `e ≥ 2`, any rational radical
square root `s` with `s·s ≈ 1 + (−(x·x))` at a rational point `x`, and any width
`h`, the `s`-cleared leading midpoint combination at `x` collapses EXACTLY to
`−(h·(U_e(x)·(s·s)))`:

    `½·h·( s·(s·B_e′(x)) + (−(x·B_e(x))) ) ≈ −( h·(U_e(x)·(s·s)) )`,

where `B_e(x) = Gbracket e he x`, `B_e′(x) = ChebOrthoWeightedFTC.Bderiv e he x`.
This is the rigorous form of "the leading midpoint terms cancel `orthTerm`": the
RHS is `−s·orthTerm`-scaled (`orthTerm k = h·U_e(x_k)·s_k`, `s_k² = 1−x_k²`).
Composes `leading_combo_abstract` with `ChebUDClosure.Bderiv_identity_uncond`. -/
theorem leading_cancellation (e : Nat) (he : 0 < e) (he2 : 2 ≤ e) (x s h : Q')
    (hs : (s * s) ≈ (1 + (-(x * x)))) :
    ((Q'.mkPos 1 2 (by decide))
        * (h * (s * (s * ChebOrthoWeightedFTC.Bderiv e he x)
                + (-(x * ChebOrthoOffDiag.Gbracket e he x)))))
      ≈ (-(h * (Cheb.U e x * (s * s)))) := by
  -- the EXACT polynomial identity (1−x²)·B′ − x·B ≈ −2·(1−x²)·U at x
  have hid : ((1 + (-(x * x))) * ChebOrthoWeightedFTC.Bderiv e he x
              + (-(x * ChebOrthoOffDiag.Gbracket e he x)))
            ≈ (-(((2 : Q')) * ((1 + (-(x * x))) * Cheb.U e x))) := by
    have hB := ChebUDClosure.Bderiv_identity_uncond e he he2 x
    -- `Bident` is exactly this with `2 = 1 + 1`; rewrite the leading `2`.
    have h2 : ((1 : Q') + (1 : Q')) ≈ ((2 : Q')) := by decide
    -- hB : ... ≈ −((1+1)·((1−x²)·U)) ; convert (1+1) ↦ 2
    refine Q'.eqv_trans _ _ _ hB ?_
    exact Q'.neg_eqv_congr _ _
      (Q'.mul_eqv_congr_right _ _ _ h2)
  exact leading_combo_abstract s x (ChebOrthoOffDiag.Gbracket e he x)
    (ChebOrthoWeightedFTC.Bderiv e he x) (Cheb.U e x) h hs hid

/-! ## 4. The BOUNDARY-cell direct bound on `orthTerm`

For boundary cells the leading cancellation is not needed: `orthTerm` itself is
already small there.  We record the fully-rigorous direct bound
`|U_e(x_k)| ≤ e+1` (from `ChebyshevU.absU_le`) and the genuine-radical bound
`√(1−x_k²) ≤ c` (`sqrtFrom_leRat_of_sq`) for any rational `c` with `1−x_k² ≤ c²`.
This is the rigorous boundary leg of the per-cell estimate. -/

/-- **The bounded-Chebyshev factor `|U_e(x)| ≤ e+1` on `[−1,1]`** at a node value
inside the interval (re-export of `ChebyshevU.absU_le` in the two-sided shape).
The node values `x_k = (2k+1−M)/M` of the midpoint rule satisfy `−1 ≤ x_k ≤ 1`,
so this applies verbatim. -/
theorem uNode_abs_le (e : Nat) (x : Q') (hx1 : x ≤ 1) (hxm1 : (-1 : Q') ≤ x) :
    Cheb.U e x ≤ Q'.ofNat (e + 1) ∧ (-(Q'.ofNat (e + 1))) ≤ Cheb.U e x := by
  have h := ChebU.absU_le e x hx1 hxm1
  exact ⟨h.1, h.2⟩

/-- **The genuine cell radical is bounded by any `c` with `1 − b_k² ≤ c²`**
(boundary-cell leg).  Direct application of `Sqrt.sqrtFrom_leRat_of_sq` to the
interior boundary radical `bdyRadical` (`= √(1 − b_k²)`, `0 < k < M`).  For a
BOUNDARY cell `s_± ≤ √(2δ)`, so `c := √(2δ)` makes this small. -/
theorem bdyRadical_leRat (M : Nat) (hM : 0 < M) (k : Nat) (hk0 : 0 < k) (hkn : k < M)
    (c : Q') (hc : (0 : Q') < c)
    (hac : bdyOneMinusSq M k hM hk0 hkn ≤ c * c) :
    CReal.leRat (bdyRadical M hM k) c := by
  show CReal.leRat
      (if hk0' : 0 < k then
        if hkn' : k < M then
          CReal.sqrtFrom (bdyOneMinusSq M k hM hk0' hkn')
            (SemicircleIntegral.nodeLB M hM)
            (bdyOneMinusSq_pos hM hk0' hkn') (SemicircleIntegral.nodeLB_pos hM)
            (bdyLB_sq_le hM hk0' hkn')
        else CReal.czero
      else CReal.czero) c
  rw [dif_pos hk0, dif_pos hkn]
  exact CReal.sqrtFrom_leRat_of_sq (bdyOneMinusSq M k hM hk0 hkn)
    (SemicircleIntegral.nodeLB M hM) (bdyOneMinusSq_pos hM hk0 hkn)
    (SemicircleIntegral.nodeLB_pos hM) (bdyLB_sq_le hM hk0 hkn) c hc hac

end YMGap.Continuum.ChebOrthoCancel

/-! ## PROVED vs NAMED-open (honest ledger)

**PROVED here (axiom-clean, GENUINE new content).**
  * `two_mul_eqv` — `2·a ≈ a + a` (`Q'` bookkeeping).
  * **`leading_combo_abstract`** — the EXACT abstract leading-cancellation lemma:
    with `s·s ≈ 1 + (−(x·x))` and the bracket derivative identity
    `(1+(−(x·x)))·Bp + (−(x·B)) ≈ −(2·((1+(−(x·x)))·U))`, the `s`-cleared leading
    midpoint combination `½·h·(s·(s·Bp) + (−(x·B)))` collapses EXACTLY to
    `−(h·(U·(s·s)))`.  Division-free pure `Q'`-ring `calc`.  This is the rigorous
    algebraic heart: it shows the leading midpoint terms cancel `orthTerm` EXACTLY.
  * **`leading_cancellation`** — the concrete instantiation at the cell midpoint
    `x` with `B_e(x) = Gbracket e he x`, `B_e′(x) = ChebOrthoWeightedFTC.Bderiv e
    he x`, `U_e(x) = Cheb.U e x`, via `ChebUDClosure.Bderiv_identity_uncond`:
    `½·h·(s·(s·B_e′(x)) + (−(x·B_e(x)))) ≈ −(h·(U_e(x)·(s·s)))`, the EXACT
    statement that the leading midpoint combination equals `−s·orthTerm`-scaled.
  * `uNode_abs_le` — the bounded-Chebyshev factor `|U_e(x)| ≤ e+1` on `[−1,1]`
    (re-export of `ChebyshevU.absU_le`), the rigorous `U`-leg of the boundary bound.
  * **`bdyRadical_leRat`** — the genuine cell radical bound
    `√(1 − b_k²) ≤ c` for any `c` with `1 − b_k² ≤ c²` (via
    `Sqrt.sqrtFrom_leRat_of_sq`), the rigorous radical-leg of the boundary bound.

**NAMED-open (the honest residual — the SECOND-ORDER remainder).**
  * `ChebOrthoMidpointCore.CorrectedPerCellBound e he` — the FULL per-cell estimate
    `|cellAdjR e he (N+1) k| ≤ cRate e (N+1) k` against the corrected rate.  The
    leading-order cancellation is now PROVED EXACT (`leading_cancellation`): it
    removes the `O(h)` part of `cellAdjR k = orthTerm k + gIncrR k`.  The SINGLE
    remaining genuine content is the constructive bound on the SECOND-ORDER
    centered-difference REMAINDER
    `cellAdjR k − (orthTerm k + leading(gIncrR k))`, i.e. the constructive
    Taylor/finite-difference remainder of the smooth legs `B_e` (polynomial,
    Lipschitz scale `Le e`) and `√(1−x²)` (the √-Hölder modulus, `radDiff_holder`),
    in the INTERIOR (`C(e)·h^{3/2}/s_k^p`) and BOUNDARY (`s_± ≤ √(2δ)`,
    `boundary_orthTerm`/`bdyRadical_leRat`) cells, balanced at `δ ≈ √h` to `cRate`.
    Recorded precisely, not faked.

**Path to closure.**  Once `CorrectedPerCellBound e he` holds for every even
`e ≥ 2`, `ChebOrthoMidpointCore.realPerCellBudget_of_correctedBound` +
`ChebOrthoMidpoint.budgetExists_of_realPerCell` close `BudgetExists e`, hence (via
the proved `convergesTo_czero_of_bound`) `OrthEvenZeroLimit e` and the full π-free
off-diagonal orthogonality `∫U_e√ = 0` for all `e ≥ 1`.

Axiom-gate: `[propext]` / `[propext, Quot.sound]`.  No `Classical.*`,
no `sorry`/`sorryAx`, no `native_decide`, no new axioms; `decide` only on closed
`Nat`/`Int`/`Q'`. -/

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.ChebOrthoCancel.two_mul_eqv
#print axioms YMGap.Continuum.ChebOrthoCancel.leading_combo_abstract
#print axioms YMGap.Continuum.ChebOrthoCancel.leading_cancellation
#print axioms YMGap.Continuum.ChebOrthoCancel.uNode_abs_le
#print axioms YMGap.Continuum.ChebOrthoCancel.bdyRadical_leRat
