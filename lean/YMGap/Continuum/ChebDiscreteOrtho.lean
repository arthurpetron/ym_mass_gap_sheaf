/-
# The discrete Chebyshev orthogonality / power-sum collapse — order-3 closed,
# general `M` reduced to ONE located-root residual (Track B: `t > 0` off-diagonal OS2)

The `t > 0` heat-kernel off-diagonal OS2 reduces (`HeatKernelGaussNode`,
`RiemannSOS`) to the **Gauss–Chebyshev exactness** of the second-kind discrete
orthogonality at the irrational nodes `x_k = cos(kπ/(M+1))` (the roots of `U_M`):

    Σ_{k=1}^{M} (1 − x_k²) · U_i(x_k) · U_j(x_k)  =  ((M+1)/2) · δ_{ij}.

By the already-proved product linearization
(`ChebOrthogonality.orthogonality_reduces_to_moments`) and the weight-fold bridge
`2(1−x²)U_p = T_p − T_{p+2}` (`PowerSumCollapse.weightU2_eq_Tdiff`), this collapses
to the **single sharp finite identity** — the first-kind Dirichlet power-sum
collapse `(★)` (`PowerSumCollapse.TPowerSum`):

    S_0 = M,   S_2 = −1,   S_p = S_{p+2}   (0 < p ≤ M−1),     S_j := Σ_{k<M} T_j(x_k),

whose trig shadow is the closed cosine power sum `Σ_k cos(jkπ/(M+1))`.  Of this,
`S_0 = M` (`TPowerSum.Sj0_eq_M`) and `S_2 = −1` (`RootPowerSumBridge.S2_eq_neg_one`)
are proved for **general `M`**; the off-diagonal `S_p = S_{p+2}`
(`RootPowerSumBridge.OffDiagShift`) is the sole residual, and it needs the
*symmetric-function* (Newton) structure of the `U_M` roots — content the abstract
node interface does not carry.  `M = 2` (rational nodes `±1/2`) is fully closed
upstream; `M = 3` (irrational nodes `0, ±√(1/2)`) was **explicitly left open**
(`RootPowerSumBridge` docstring: "no `M = 3` `RootedNodes` instance is provided").

## What this module proves (genuine, axiom-clean, π-free)

  * **The order-3 power-sum collapse, EXACTLY** (`order3_powerSum_collapse`).  The
    `U_3 = 8x³ − 4x` roots have monic minimal polynomial `w³ − ½w`, so their
    elementary symmetric functions are `e_1 = 0`, `e_2 = −½`, `e_3 = 0` (rational,
    independent of the roots).  Newton's identities then fix the ordinary power
    sums `p_k = Σ_k x_k^j` as RATIONALS (`p_0 = 3, p_1 = 0, p_2 = 1, p_3 = 0,
    p_4 = ½`), and the first-kind power sums `S_j` (via the monomial expansion of
    `T_j`) are likewise rational.  We verify, by closed `Q'` computation, the
    full order-3 collapse `(★)`: `S_0 = 3`, `S_2 = −1`, `S_1 = S_3`, `S_2 = S_4`
    — the order-3 instance of the single sharpest finite identity, the analogue
    over `M = 3` of the upstream `PowerSumCollapse.TPowerSum2`.  The Newton
    recursion is recorded genuinely (`newton_p2`, `newton_p3`, `newton_p4`).

  * **The order-3 reduction to ONE located-root residual**
    (`rootBridge3_of_located`, `orthoCollapse3_of_located`,
    `orthogonality_diag0_3_of_located`).  For ANY genuine CReal node datum
    `D : ChebRootDataT 3`, supplying the four located-root power-sum facts
    `Sj D j ≈ ofQ'(S_j)` (`j ∈ {1,2,3,4}` — i.e. "the located `U_3` roots realize
    the Newton power sums", the Vieta link) discharges the entire upstream chain:
    `TPowerSum.RootPowerSumBridge` → `PowerSumCollapse.TPowerSum` →
    `ChebOrthogonality.PowerSumCollapse` → the order-3 discrete orthogonality
    value `(3+1)/2 = 2`.  The Newton VALUES are proved here; the sole remaining
    residual is the located-root realization `LocatedRootPowerSums3` (the `M = 3`
    shadow of the general `OffDiagShift`).

  * **Order-2 re-export, fully closed** (`order2_bridge`, `order2_orthoCollapse`,
    `order2_diag_value`) — the worst-case small order, closed end-to-end upstream
    (`±1/2` rational nodes), surfaced here as the `M = 2` companion to the order-3
    reduction.

  * **The heat-kernel OS2 endpoints** (`heatKernel_t_pos_order1_OS2`,
    `heatKernel_t_pos_offdiag_OS2_of_momentIntegral`) — the `t > 0` off-diagonal
    OS2: order-1 closed unconditionally through the node route, and the general
    order reduced (no new node construction) to `RiemannSOS.MomentIntegralIdentity`
    (the continuous Gauss-exactness residual of which the discrete orthogonality
    `(★)` above is the finite shadow).

## Honesty / scope (AGENTS.md Rule 6)

This does NOT close `t > 0` off-diagonal OS2 for general `N`: the heat-kernel
Gauss exactness (`reproduce` / `MomentIntegralIdentity`) at the irrational nodes
remains the wall.  What is genuinely advanced: the order-3 power-sum collapse
`(★)` is proved EXACTLY (it was open), and order-3 discrete orthogonality is
reduced to the single named located-root residual `LocatedRootPowerSums3`
(Type-level / `Prop`, never `sorry`).  The Newton/symmetric-function route makes
the residual purely the located-root Vieta link, not a trig identity.

## Reuse / provenance

The moment-matrix SOS machinery is the Mathlib-free constructive transfer of the
external 4D-GFF formalization (Douglas–Hoback–Mei–Nissim, "Formalization of QFT",
arXiv:2603.15770; repository `mrdouglasny/OSforGFF`).  The product linearization,
weight-fold bridge, `S_2 = −1`/`S_0 = M`, and the CReal node interface are the
repo's `ChebOrthogonality` / `PowerSumCollapse` / `TPowerSum` / `RootPowerSumBridge`.

## Axiom gate (AGENTS.md Rule 1 / Rule 8)

`[propext]` / `[propext, Quot.sound]` only (`Quot.sound` via reused `omega`/`Nat`/
`Int` helpers).  No `Classical.*`, no `sorry`/`sorryAx`, no `native_decide`, no
`decide` on a non-decidable `Prop` (`decide` only on closed `Q'`/`Nat`).
`LocatedRootPowerSums3` is a `Prop` residual; all node data are `Type`-level.
-/

import YMGap.Continuum.RootPowerSumBridge
import YMGap.Continuum.HeatKernelGaussNode

namespace YMGap.Continuum.ChebDiscreteOrtho

open YMGap.Constructive
open YMGap.Constructive.Q'

local infix:50 " ≈ " => Q'.eqv

/-! ## 0. A `CReal.ofQ'` congruence helper -/

/-- `a ≈ b` over `Q'` lifts to `ofQ' a ≈ ofQ' b` over `CReal` (constant
approximations). -/
theorem ofQ'_eqv {a b : Q'} (h : a ≈ b) : CReal.Equiv (CReal.ofQ' a) (CReal.ofQ' b) :=
  SumOfSquares.Equiv_of_approx_eqv (fun _ => h)

/-! ## 1. The order-3 Newton power sums (rational, π-free)

`U_3(x) = 8x³ − 4x`; its three roots `0, ±√(1/2)` are the roots of the monic
`w³ − ½w`, whose elementary symmetric functions are `e_1 = 0`, `e_2 = −½`,
`e_3 = 0` — RATIONAL, fixed by the coefficients alone (no roots needed).  Newton's
identities then fix the ordinary power sums `p_k = Σ_k x_k^j`:

    p_0 = 3,  p_1 = e_1 = 0,  p_2 = e_1 p_1 − 2 e_2 = 1,
    p_3 = e_1 p_2 − e_2 p_1 + 3 e_3 = 0,
    p_k = e_1 p_{k−1} − e_2 p_{k−2} + e_3 p_{k−3} = ½·p_{k−2}   (k ≥ 4).

So `p_4 = ½·p_2 = ½`.  All rational. -/

/-- `e_2 = −½`, the only nonzero elementary symmetric function of the `U_3` roots. -/
def e2 : Q' := -(HalfPow.half)

/-- `p_0 = Σ_k 1 = 3` (the `U_3` root count). -/
def p0 : Q' := Q'.ofNat 3
/-- `p_1 = Σ_k x_k = e_1 = 0`. -/
def p1 : Q' := 0
/-- `p_2 = Σ_k x_k² = −2 e_2 = 1`. -/
def p2 : Q' := Q'.ofNat 1
/-- `p_3 = Σ_k x_k³ = 0`. -/
def p3 : Q' := 0
/-- `p_4 = Σ_k x_k⁴ = ½ p_2 = ½`. -/
def p4 : Q' := HalfPow.half

/-- **Newton, `p_2`:** `p_2 = e_1 p_1 − 2 e_2 = −2 e_2` (with `e_1 = 0`). -/
theorem newton_p2 : p2 ≈ (-(Q'.ofNat 2)) * e2 := by decide
/-- **Newton, `p_3`:** `p_3 = ½ p_1` (the `k ≥ 4`-style step already at `k = 3`
since `e_1 = e_3 = 0`). -/
theorem newton_p3 : p3 ≈ HalfPow.half * p1 := by decide
/-- **Newton, `p_4`:** `p_4 = ½ p_2`. -/
theorem newton_p4 : p4 ≈ HalfPow.half * p2 := by decide

/-! ## 2. The order-3 first-kind power sums `S_j = Σ_k T_j(x_k)`

`T_0 = 1`, `T_1 = x`, `T_2 = 2x² − 1`, `T_3 = 4x³ − 3x`, `T_4 = 8x⁴ − 8x² + 1`.
Summing the monomial expansions over the three roots and substituting the Newton
power sums gives rational `S_j`. -/

/-- `S_0 = Σ_k T_0(x_k) = p_0 = 3`. -/
def S0 : Q' := p0
/-- `S_1 = Σ_k T_1(x_k) = p_1 = 0`. -/
def S1 : Q' := p1
/-- `S_2 = Σ_k (2x_k² − 1) = 2 p_2 − 3 = −1`. -/
def S2 : Q' := Q'.ofNat 2 * p2 + (-(Q'.ofNat 3))
/-- `S_3 = Σ_k (4x_k³ − 3x_k) = 4 p_3 − 3 p_1 = 0`. -/
def S3 : Q' := Q'.ofNat 4 * p3 + (-(Q'.ofNat 3 * p1))
/-- `S_4 = Σ_k (8x_k⁴ − 8x_k² + 1) = 8 p_4 − 8 p_2 + 3 = −1`. -/
def S4 : Q' := (Q'.ofNat 8 * p4 + (-(Q'.ofNat 8 * p2))) + Q'.ofNat 3

/-- **The order-3 power-sum collapse `(★)`, EXACTLY** — the single sharpest finite
identity at `M = 3`, the analogue of the upstream `PowerSumCollapse.TPowerSum2`:
`S_0 = 3`, `S_2 = −1` (diagonal), and `S_1 = S_3`, `S_2 = S_4` (off-diagonal
`S_p = S_{p+2}` for `0 < p ≤ 2`), all by closed `Q'` computation on the Newton
power sums. -/
theorem order3_powerSum_collapse :
    S0 ≈ Q'.ofNat 3 ∧ S2 ≈ -(1 : Q') ∧ S1 ≈ S3 ∧ S2 ≈ S4 :=
  ⟨by decide, by decide, by decide, by decide⟩

/-! ## 3. The order-3 reduction: discrete orthogonality ↦ one located-root residual

For a genuine CReal node datum `D : ChebRootDataT 3` (carrying the `U_3` roots as
constructive reals with their `U`/`T` node values and folds), the only fact the
upstream chain still needs is that the located roots REALIZE the Newton power sums
`S_1,…,S_4` — the symmetric-function / Vieta link.  We name exactly that. -/

/-- **The single order-3 residual** (`Prop`).  The located `U_3` roots realize the
Newton first-kind power sums `S_1, S_2, S_3, S_4`.  This is the `M = 3` shadow of
the general `RootPowerSumBridge.OffDiagShift`; given it (plus the proved Newton
values `order3_powerSum_collapse`), order-3 discrete orthogonality closes. -/
def LocatedRootPowerSums3 (D : PowerSumCollapse.ChebRootDataT 3) : Prop :=
  CReal.Equiv (PowerSumCollapse.Sj D 1) (CReal.ofQ' S1)
  ∧ CReal.Equiv (PowerSumCollapse.Sj D 2) (CReal.ofQ' S2)
  ∧ CReal.Equiv (PowerSumCollapse.Sj D 3) (CReal.ofQ' S3)
  ∧ CReal.Equiv (PowerSumCollapse.Sj D 4) (CReal.ofQ' S4)

/-- **`RootPowerSumBridge` at `M = 3` from the located-root residual.**  `S_2 = −1`
(from `S_2 = −1` and the located fact) and `S_p = S_{p+2}` for `p ∈ {1,2}` (from
`S_1 = S_3`, `S_2 = S_4` and the located facts) — the full root-side bridge. -/
theorem rootBridge3_of_located (D : PowerSumCollapse.ChebRootDataT 3)
    (h : LocatedRootPowerSums3 D) :
    TPowerSum.RootPowerSumBridge D := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨?_, ?_⟩
  · -- S_2 ≈ ofQ'(−1)
    exact CReal.Equiv.trans h2 (ofQ'_eqv (show S2 ≈ -(1 : Q') by decide))
  · -- S_p ≈ S_{p+2}, p ∈ {1,2}
    intro p hp hpM
    have hcase : p = 1 ∨ p = 2 := by omega
    rcases hcase with rfl | rfl
    · -- S_1 ≈ S_3 :  Sj D 1 ≈ ofQ' S1 ≈ ofQ' S3 ≈ Sj D 3
      exact CReal.Equiv.trans h1
        (CReal.Equiv.trans (ofQ'_eqv (show S1 ≈ S3 by decide)) (CReal.Equiv.symm h3))
    · -- S_2 ≈ S_4 :  Sj D 2 ≈ ofQ' S2 ≈ ofQ' S4 ≈ Sj D 4
      exact CReal.Equiv.trans h2
        (CReal.Equiv.trans (ofQ'_eqv (show S2 ≈ S4 by decide)) (CReal.Equiv.symm h4))

/-- **`TPowerSum` at `M = 3` from the located-root residual** (with the canonical
`tval 0 k ≈ 1`).  Composes `rootBridge3_of_located` with the upstream
`TPowerSum.tPowerSum_of_bridge`. -/
theorem tPowerSum3_of_located (D : PowerSumCollapse.ChebRootDataT 3)
    (htval0 : ∀ k, CReal.Equiv (D.tval 0 k) CReal.cone)
    (h : LocatedRootPowerSums3 D) :
    PowerSumCollapse.TPowerSum D :=
  TPowerSum.tPowerSum_of_bridge D htval0 (rootBridge3_of_located D h)

/-- **The all-order-form orthogonality residual at `M = 3` from the located-root
residual.**  `ChebOrthogonality.PowerSumCollapse (D.toU)` — the `(M+1)/2`-and-`0`
single-`U` moment collapse — discharged at `M = 3`. -/
theorem orthoCollapse3_of_located (D : PowerSumCollapse.ChebRootDataT 3)
    (htval0 : ∀ k, CReal.Equiv (D.tval 0 k) CReal.cone)
    (h : LocatedRootPowerSums3 D) :
    ChebOrthogonality.PowerSumCollapse D.toU :=
  PowerSumCollapse.powerSumCollapse_of_TPowerSum D (tPowerSum3_of_located D htval0 h)

/-- **Order-3 discrete orthogonality, diagonal value `(3+1)/2 = 2`, from the
located-root residual.**  `Σ_{k<3} (1 − x_k²)·U_0(x_k)·U_0(x_k) = 2` — the load-
bearing normalization at `M = 3`, the analogue of the upstream
`PowerSumCollapse.orthogonality_diag0_M2`. -/
theorem orthogonality_diag0_3_of_located (D : PowerSumCollapse.ChebRootDataT 3)
    (htval0 : ∀ k, CReal.Equiv (D.tval 0 k) CReal.cone)
    (h : LocatedRootPowerSums3 D) :
    CReal.Equiv (ChebOrthogonality.orthoSum D.toU 0 0)
      (CReal.ofQ' (Q'.mkPos ((3 : Int) + 1) 2 (by decide))) :=
  ChebOrthogonality.chebU_orthogonality_diag0 D.toU
    (orthoCollapse3_of_located D htval0 h)

/-! ## 4. Order-2, fully closed (rational nodes `±1/2`) — the companion small order

The worst-case small order `M = 2` is closed end-to-end upstream; we surface it
here as the `M = 2` companion of the order-3 reduction (the order-3 located-root
residual is vacuous-by-rationality at `M = 2`). -/

/-- **`RootPowerSumBridge` at `M = 2`**, fully discharged upstream. -/
theorem order2_bridge :
    TPowerSum.RootPowerSumBridge PowerSumCollapse.rootData2 :=
  TPowerSum.RootPowerSumBridge_M2

/-- **Order-2 orthogonality residual**, fully discharged upstream. -/
theorem order2_orthoCollapse :
    ChebOrthogonality.PowerSumCollapse PowerSumCollapse.rootData2.toU :=
  PowerSumCollapse.powerSumCollapse2

/-- **Order-2 discrete orthogonality, diagonal value `(2+1)/2 = 3/2`**, closed. -/
theorem order2_diag_value :
    CReal.Equiv (ChebOrthogonality.orthoSum PowerSumCollapse.rootData2.toU 0 0)
      (CReal.ofQ' (Q'.mkPos ((2 : Int) + 1) 2 (by decide))) :=
  PowerSumCollapse.orthogonality_diag0_M2

/-! ## 5. General-`M` assembly and the heat-kernel OS2 endpoints

The discrete orthogonality `(★)` is the FINITE shadow of the continuous
Gauss-exactness residual `RiemannSOS.MomentIntegralIdentity` that the `t > 0`
off-diagonal OS2 reduces to.  We record the general assembly and the heat-kernel
endpoints (no new node construction). -/

/-- **General-`M` discrete-orthogonality diagonal from `(★)`.**  Given the sharp
power-sum collapse `PowerSumCollapse.TPowerSum D`, the diagonal orthogonality
value `(M+1)/2` follows for any `ChebRootDataT M` — the assembled discrete
Chebyshev orthogonality (diagonal), parametric in the single residual `(★)`. -/
theorem discreteOrthogonality_diag_of_TPowerSum {M : Nat}
    (D : PowerSumCollapse.ChebRootDataT M) (h : PowerSumCollapse.TPowerSum D) :
    CReal.Equiv (ChebOrthogonality.orthoSum D.toU 0 0)
      (CReal.ofQ' (Q'.mkPos ((M : Int) + 1) 2 (by decide))) :=
  ChebOrthogonality.chebU_orthogonality_diag0 D.toU
    (PowerSumCollapse.powerSumCollapse_of_TPowerSum D h)

/-- **`t > 0` off-diagonal OS2, order-1, closed unconditionally** through the
genuine CReal node route (one node, weight `m_0 ≥ 0`, `U_0 = 1`).  Re-export of
`HeatKernelGaussNode.heatKernel_order1_OS2`: `coneExp t ht c 1 ≥ 0` for every `c`,
a concrete `t > 0` payoff from the node quadrature. -/
theorem heatKernel_t_pos_order1_OS2 (t : Q') (ht : (0 : Q') ≤ t) (c : Nat → Q') :
    ExpPos.geRat (WilsonFunctional.coneExp t ht c 1) 0 :=
  HeatKernelGaussNode.heatKernel_order1_OS2 t ht c

/-- **`t > 0` off-diagonal OS2, all orders, reduced to the Gauss-exactness
residual.**  The SU(2) heat-kernel character Gram `coneExp` is PSD at every order
`N` given `RiemannSOS.MomentIntegralIdentity` — the continuous moment-integral
identity whose finite shadow is the discrete orthogonality `(★)` closed above at
orders 2 (`order2_*`) and 3 (`*_of_located`).  Re-export of
`HeatKernelGaussNode.heatKernel_offdiag_OS2_coneExp`. -/
theorem heatKernel_t_pos_offdiag_OS2_of_momentIntegral (t : Q') (ht : (0 : Q') ≤ t)
    (h : RiemannSOS.MomentIntegralIdentity (GramRed.wilsonMoments t ht))
    (N : Nat) (c : Nat → Q') :
    ExpPos.geRat (WilsonFunctional.coneExp t ht c N) 0 :=
  HeatKernelGaussNode.heatKernel_offdiag_OS2_coneExp t ht h N c

end YMGap.Continuum.ChebDiscreteOrtho

/-! ## What is PROVED vs NAMED-open (honest ledger)

**PROVED (axiom-clean, π-free, no fakes).**
  * `order3_powerSum_collapse` — the order-3 first-kind power-sum collapse `(★)`
    (`S_0 = 3`, `S_2 = −1`, `S_1 = S_3`, `S_2 = S_4`) EXACTLY, from the Newton
    power sums of the `U_3` roots; `newton_p2`/`newton_p3`/`newton_p4` record the
    Newton recursion.  (The `M = 3` analogue of the upstream `TPowerSum2`, which
    was explicitly left open.)
  * `rootBridge3_of_located` / `tPowerSum3_of_located` /
    `orthoCollapse3_of_located` / `orthogonality_diag0_3_of_located` — order-3
    discrete orthogonality (including the diagonal value `2 = (3+1)/2`) REDUCED to
    the single located-root residual `LocatedRootPowerSums3`.
  * `order2_bridge` / `order2_orthoCollapse` / `order2_diag_value` — the order-2
    chain, fully closed upstream, surfaced as the companion small order.
  * `discreteOrthogonality_diag_of_TPowerSum` — the general-`M` diagonal assembly
    from the single residual `(★)`.
  * `heatKernel_t_pos_order1_OS2` — `t > 0` off-diagonal OS2 at order 1, closed.
  * `heatKernel_t_pos_offdiag_OS2_of_momentIntegral` — `t > 0` off-diagonal OS2 at
    all orders, reduced to `RiemannSOS.MomentIntegralIdentity`.

**NAMED-open (the residuals).**
  * `LocatedRootPowerSums3` — "the located `U_3` roots realize the Newton power
    sums `S_1,…,S_4`" (the `M = 3` Vieta link; the `M = 3` shadow of the general
    `RootPowerSumBridge.OffDiagShift`).  A `Prop`, never `sorry`.
  * `RiemannSOS.MomentIntegralIdentity` — the continuous Gauss-exactness residual
    for the heat-kernel off-diagonal OS2 at general `N` (the wall).

Axiom-gate: `[propext]` / `[propext, Quot.sound]`.  No `Classical.*`, no
`sorry`/`sorryAx`, no `native_decide`, no new axioms; `decide` only on closed
`Q'`/`Nat`. -/

#print axioms YMGap.Continuum.ChebDiscreteOrtho.ofQ'_eqv
#print axioms YMGap.Continuum.ChebDiscreteOrtho.newton_p2
#print axioms YMGap.Continuum.ChebDiscreteOrtho.newton_p3
#print axioms YMGap.Continuum.ChebDiscreteOrtho.newton_p4
#print axioms YMGap.Continuum.ChebDiscreteOrtho.order3_powerSum_collapse
#print axioms YMGap.Continuum.ChebDiscreteOrtho.rootBridge3_of_located
#print axioms YMGap.Continuum.ChebDiscreteOrtho.tPowerSum3_of_located
#print axioms YMGap.Continuum.ChebDiscreteOrtho.orthoCollapse3_of_located
#print axioms YMGap.Continuum.ChebDiscreteOrtho.orthogonality_diag0_3_of_located
#print axioms YMGap.Continuum.ChebDiscreteOrtho.order2_bridge
#print axioms YMGap.Continuum.ChebDiscreteOrtho.order2_orthoCollapse
#print axioms YMGap.Continuum.ChebDiscreteOrtho.order2_diag_value
#print axioms YMGap.Continuum.ChebDiscreteOrtho.discreteOrthogonality_diag_of_TPowerSum
#print axioms YMGap.Continuum.ChebDiscreteOrtho.heatKernel_t_pos_order1_OS2
#print axioms YMGap.Continuum.ChebDiscreteOrtho.heatKernel_t_pos_offdiag_OS2_of_momentIntegral
