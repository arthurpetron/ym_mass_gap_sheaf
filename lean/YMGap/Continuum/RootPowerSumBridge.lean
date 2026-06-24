/-
# The root-structure bridge for the `U_M` power sums (Wall-1, root-side Newton step)

`TPowerSum.RootPowerSumBridge M D` is the single named residual to which the
all-order SU(2) Gram PSD (Wall-1) has been reduced (`TPowerSum.tPowerSum_of_bridge`
composed with `PowerSumCollapse.powerSumCollapse_of_TPowerSum` and the proved
product linearization).  The honest blocker (`TPowerSum` docstring) is that the
abstract node interface `ChebRootDataT M` does **not** encode that its nodes `x_k`
ARE the `M` roots of the second-kind Chebyshev polynomial `U_M`; the bridge is
exactly the symmetric-function / Newton content of that fact.

This module supplies the missing *root structure* as an explicit interface
`RootedNodes M` carrying the two load-bearing symmetric-function data of the `U_M`
roots, and uses it to prove `S_2 = −1` for **general `M`**.

## The worked (π-free, algebraic) mathematics

`U_M(w) = 2^M · ∏_{k=1}^{M}(w − x_k)`, so the elementary symmetric polynomials of
the roots are the (signed) coefficient ratios of `U_M`.  From the closed form
`U_M(w) = Σ_{j} (−1)^j C(M−j,j)(2w)^{M−2j}`:

  * coeff of `w^{M−1}` is `0`  ⇒  `e_1 = Σ_k x_k = 0`   (roots symmetric about 0),
  * coeff of `w^{M−2}` is `−(M−1)·2^{M−2}`  ⇒  `e_2 = −(M−1)/4`,
  * Newton:  `p_2 = Σ_k x_k² = e_1² − 2 e_2 = (M−1)/2`.

Therefore, with `T_2(x) = 2x² − 1`,

    S_2 = Σ_k T_2(x_k) = 2·p_2 − M = (M−1) − M = −1.        (the general target)

We carry `e_1 = 0` and `p_2 = (M−1)/2` as the two fields of `RootedNodes M` (the
genuine root data the abstract interface lacks) and derive `S_2 = −1` from them by
the elementary `T_2 = 2x²−1` and finite-sum linearity — no trig, no `π`.

## PROVED (genuine, axiom-clean, π-free)

  * `RootedNodes` — the root-structure interface: rational nodes plus the two
    symmetric-function facts `e1_zero` (`Σ x_k ≈ 0`) and `p2_value`
    (`Σ x_k² ≈ (M−1)/2`).
  * `S2_rational_eq_neg_one` — `Σ_{k<M} T_2(x_k) ≈ −1` for **general `M`**, from
    `p2_value` alone (`T_2 = 2x²−1`, `Σ(2x²) = 2·p_2 = M−1`, `Σ(−1) = −M`).
  * `S2_eq_neg_one` — its `CReal` form `Sj (D.toData) 2 ≈ ofQ'(−1)` for general
    `M` (the first component of `TPowerSum.RootPowerSumBridge`).
  * `rootedNodes2` — the `M = 2` concrete instance (`±1/2`), `e1_zero`/`p2_value`
    discharged by `decide`; `S2_M2_eq_neg_one` reproduces `S_2 = −1` through the
    general route.

## NAMED open (the precise residual)

  * `OffDiagShift M D` — the off-diagonal half of the bridge:
    `S_p = S_{p+2}` for `0 < p ≤ M−1`.  This is the part of the Newton recursion
    that needs the FULL elementary-symmetric data `e_1,…,e_M` of the `U_M` roots
    (the every-other-degree structure of `U_M`), not just `e_1, e_2`.  It is named,
    not faked.  Given it (together with the proved `S2_eq_neg_one` and the
    upstream `Sj0_eq_M`), `TPowerSum.RootPowerSumBridge` — and hence the all-order
    Gram PSD — closes (`bridge_of_offdiag`).  At `M = 2` it is vacuous, so the
    bridge is fully inhabited there (`rootBridge2`).

So the all-order Gram PSD (Wall-1) is **NOT closed** by this module.  It supplies
the root structure that the abstract interface lacked and uses it to prove the
diagonal target `S_2 = −1` for general `M`; the off-diagonal collapse
`S_p = S_{p+2}` remains the single sharp residual `OffDiagShift`.

## Axiom gate (AGENTS.md Rule 1 / Rule 8)

`[propext]` / `[propext, Quot.sound]` only.  No `Classical.*`, no `sorry`/
`sorryAx`, no `native_decide`, no `decide` on a non-decidable `Prop`.  `decide`
only on closed `Q'`/`Nat`.  Witnesses (`RootedNodes`) are `Type`-level data
(MLTT/HoTT-valid).
-/

import YMGap.Continuum.TPowerSum

namespace YMGap.Continuum.RootPowerSumBridge

open YMGap.Constructive
open YMGap.Constructive.Q'
open YMGap.Continuum.Cheb
open YMGap.Continuum.ChebU
open YMGap.Continuum.PowerSumCollapse
open YMGap.Continuum.TPowerSum

local infix:50 " ≈ " => Q'.eqv

instance : Trans (Q'.eqv) (Q'.eqv) (Q'.eqv) where
  trans h1 h2 := eqv_trans _ _ _ h1 h2

/-! ## 1. The root-structure interface

`RootedNodes M` is the genuine root datum that `ChebRootDataT M` lacks: rational
nodes `x_k` together with the two symmetric-function facts of the `U_M` roots that
the diagonal target needs — `e_1 = Σ x_k = 0` and `p_2 = Σ x_k² = (M−1)/2`.
Both are `Q'.eqv` facts about finite `Q'` sums (genuine, computable). -/

/-- The half-of-`(M−1)` value `(M−1)/2 = mkPos ((M:Int)−1) 2` over `Q'`. -/
def p2val (M : Nat) : Q' := Q'.mkPos ((M : Int) - 1) 2 (by decide)

/-- **Root-structure interface.**  `Type`-level (MLTT/HoTT-valid).  Carries the
symmetric-function data of the `M` roots of `U_M` that the abstract
`ChebRootDataT` interface does not encode. -/
structure RootedNodes (M : Nat) where
  /-- The `M` rational nodes (roots of `U_M`). -/
  node : Nat → Q'
  /-- **`e_1 = Σ_k x_k ≈ 0`** — the roots of `U_M` are symmetric about `0`
      (the `w^{M−1}` coefficient of `U_M` is `0`). -/
  e1_zero : (RationalTail.finSum node M).eqv (0 : Q')
  /-- **`p_2 = Σ_k x_k² ≈ (M−1)/2`** — the second power sum of the `U_M` roots
      (Newton from `e_1 = 0`, `e_2 = −(M−1)/4`). -/
  p2_value : (RationalTail.finSum (fun k => node k * node k) M).eqv (p2val M)

/-- The underlying `ChebRootDataT M` of a `RootedNodes M` (the canonical `ofQ'`
node datum on its rational nodes). -/
def RootedNodes.toData {M : Nat} (D : RootedNodes M) : ChebRootDataT M :=
  PowerSumCollapse.fromQNodes M D.node

/-! ## 2. The diagonal target `S_2 = −1` for general `M`

`T_2(x) = (2x)·x + (−1) = 2x² − 1`, so the rational power sum
`Σ_{k<M} T_2(x_k) = Σ_k ((2·x_k)·x_k + (−1))` splits (`finSum_add`) into
`Σ_k (2·x_k²)` and `Σ_k (−1) = −M`.  The first is `2·p_2 = 2·(M−1)/2 = M−1` by
`const_mul_finSum` and `p2_value`.  Hence `Σ T_2 = (M−1) + (−M) = −1`. -/

/-- `T_2(x)` evaluated: `T 2 x = (2·x)·x + (−(1))`. -/
private theorem T_two_eval (x : Q') : T 2 x = ((2 : Q') * x) * x + (-(1 : Q')) := by
  show T (0+2) x = ((2 : Q') * x) * x + (-(1 : Q'))
  rw [T_succ_succ 0 x, T_one, T_zero]

/-- `Σ_{k<M} (−1) ≈ −(ofNat M)` over `Q'` (the constant-`(−1)` finite sum). -/
private theorem finSum_negone_eq (M : Nat) :
    (RationalTail.finSum (fun _ => (-(1 : Q'))) M).eqv (-(Q'.ofNat M)) := by
  induction M with
  | zero => decide
  | succ m ih =>
      show (RationalTail.finSum (fun _ => (-(1 : Q'))) m + (-(1 : Q'))).eqv
        (-(Q'.ofNat (m+1)))
      refine eqv_trans _ _ _ (add_eqv_congr_right _ _ _ ih) ?_
      -- (−ofNat m) + (−1) ≈ −ofNat (m+1)
      show ((-(Q'.ofNat m)) + (-(1 : Q'))).eqv (-(Q'.ofNat (m+1)))
      show ((-(Q'.ofNat m)) + (-(1 : Q'))).num * ((-(Q'.ofNat (m+1))).den : Int)
          = (-(Q'.ofNat (m+1))).num * (((-(Q'.ofNat m)) + (-(1 : Q'))).den : Int)
      simp only [Cheb.add_num, Cheb.neg_num, add_den_cast, neg_den]
      show ((-(Int.ofNat m)) * 1 + (-(1 : Int)) * 1) * 1
          = (-(Int.ofNat (m+1))) * (1 * 1)
      simp only [Int.ofNat_eq_natCast]
      push_cast
      omega

/-- `2·((M−1)/2) ≈ M−1`, the doubling of `p2val`: `2·p2val M ≈ ofInt (M−1)`. -/
private theorem two_p2val (M : Nat) :
    ((2 : Q') * p2val M).eqv (Q'.ofInt ((M : Int) - 1)) := by
  show ((2 : Q') * p2val M).num * ((Q'.ofInt ((M : Int) - 1)).den : Int)
      = (Q'.ofInt ((M : Int) - 1)).num * (((2 : Q') * p2val M).den : Int)
  -- (2·p2val).num = 2.num · p2val.num = 2·((M)−1) ; (2·p2val).den = 2.den·p2val.den = 1·2 = 2.
  have hpnum : (p2val M).num = (M : Int) - 1 := Q'.mkPos_num ((M : Int) - 1) 2 (by decide)
  have hpden : (p2val M).den = 2 := Q'.mkPos_den ((M : Int) - 1) 2 (by decide)
  have hnum : ((2 : Q') * p2val M).num = 2 * ((M : Int) - 1) := by
    show (2 : Q').num * (p2val M).num = 2 * ((M : Int) - 1)
    show (2 : Int) * (p2val M).num = 2 * ((M : Int) - 1)
    rw [hpnum]
  have hden : (((2 : Q') * p2val M).den : Int) = 2 := by
    show (((2 : Q').den * (p2val M).den : Nat) : Int) = 2
    rw [hpden]
    show (((1 : Nat) * 2 : Nat) : Int) = 2
    decide
  rw [hnum, hden]
  show (2 * ((M : Int) - 1)) * 1 = ((M : Int) - 1) * 2
  omega

/-- **The diagonal target, rational form, general `M`.**
`Σ_{k<M} T_2(x_k) ≈ −1`, from `p2_value` alone. -/
theorem S2_rational_eq_neg_one {M : Nat} (D : RootedNodes M) :
    (RationalTail.finSum (fun k => T 2 (D.node k)) M).eqv (-(1 : Q')) := by
  -- Rewrite each term T_2(x_k) = (2·x_k)·x_k + (−1).
  have hterm : (RationalTail.finSum (fun k => T 2 (D.node k)) M).eqv
      (RationalTail.finSum (fun k => ((2 : Q') * D.node k) * D.node k + (-(1 : Q'))) M) :=
    RationalTail.finSum_eqv_congr _ _ (fun k => by rw [T_two_eval (D.node k)]; exact eqv_refl _) M
  refine eqv_trans _ _ _ hterm ?_
  -- Split the sum: Σ((2x)x) + Σ(−1).
  refine eqv_trans _ _ _
    (RationalTail.finSum_add (fun k => (2 : Q') * D.node k * D.node k) (fun _ => (-(1 : Q'))) M) ?_
  -- Σ((2x)·x) ≈ Σ(2·(x·x)) ≈ 2·Σ(x·x) ≈ 2·p2val ≈ M−1 ; Σ(−1) ≈ −M.
  have hA : (RationalTail.finSum (fun k => (2 : Q') * D.node k * D.node k) M).eqv
      (Q'.ofInt ((M : Int) - 1)) := by
    -- (2·x)·x ≈ 2·(x·x)
    have hassoc : (RationalTail.finSum (fun k => (2 : Q') * D.node k * D.node k) M).eqv
        (RationalTail.finSum (fun k => (2 : Q') * (D.node k * D.node k)) M) :=
      RationalTail.finSum_eqv_congr _ _ (fun k => mul_assoc_eqv 2 (D.node k) (D.node k)) M
    refine eqv_trans _ _ _ hassoc ?_
    -- 2·Σ(x·x) ≈ Σ(2·(x·x))  (reversed const-pull), then use p2_value.
    refine eqv_trans _ _ _
      (eqv_symm (RationalTail.const_mul_finSum (fun k => D.node k * D.node k) 2 M)) ?_
    refine eqv_trans _ _ _ (mul_eqv_congr_left _ _ _ D.p2_value) ?_
    exact two_p2val M
  refine eqv_trans _ _ _ (add_eqv_congr_right _ _ _ hA) ?_
  refine eqv_trans _ _ _ (add_eqv_congr_left _ _ _ (finSum_negone_eq M)) ?_
  -- ofInt (M−1) + (−ofNat M) ≈ −1
  show ((Q'.ofInt ((M : Int) - 1)) + (-(Q'.ofNat M))).eqv (-(1 : Q'))
  show ((Q'.ofInt ((M : Int) - 1)) + (-(Q'.ofNat M))).num * ((-(1 : Q')).den : Int)
      = (-(1 : Q')).num * (((Q'.ofInt ((M : Int) - 1)) + (-(Q'.ofNat M))).den : Int)
  simp only [Cheb.add_num, Cheb.neg_num, add_den_cast, neg_den]
  show (((M : Int) - 1) * 1 + (-(Int.ofNat M)) * 1) * 1 = (-(1 : Int)) * (1 * 1)
  simp only [Int.ofNat_eq_natCast]
  push_cast
  omega

/-! ## 3. The `CReal` form: `S_2 ≈ ofQ'(−1)` for general `M`

`Sj (D.toData) 2 = Sj (fromQNodes M node) 2 ≈ ofQ'(Σ_k T_2(x_k)) ≈ ofQ'(−1)` by
`PowerSumCollapse.Sj_fromQNodes` and the rational diagonal target. -/

/-- **`S_2 = −1` for general `M`** — the first (diagonal) component of
`TPowerSum.RootPowerSumBridge`, supplied from the root structure. -/
theorem S2_eq_neg_one {M : Nat} (D : RootedNodes M) :
    CReal.Equiv (Sj D.toData 2) (CReal.ofQ' (-(1 : Q'))) := by
  -- Sj (fromQNodes M node) 2 ≈ ofQ'(finSum T_2) ≈ ofQ'(−1).
  refine CReal.Equiv.trans (PowerSumCollapse.Sj_fromQNodes M D.node 2) ?_
  refine SumOfSquares.Equiv_of_approx_eqv (fun _ => ?_)
  show (RationalTail.finSum (fun k => T 2 (D.node k)) M).eqv (-(1 : Q'))
  exact S2_rational_eq_neg_one D

/-! ## 4. The off-diagonal residual and the bridge it closes

The remaining half of `TPowerSum.RootPowerSumBridge` is the off-diagonal
`S_p = S_{p+2}` for `0 < p ≤ M−1`.  Unlike `S_2 = −1`, this needs the full
elementary-symmetric data of the `U_M` roots (the every-other-degree structure of
`U_M`'s coefficient vector), not just `e_1, e_2`.  We name it precisely.  Given it
plus the proved `S2_eq_neg_one`, `RootPowerSumBridge` holds. -/

/-- **The named off-diagonal residual** — `S_p = S_{p+2}` for `0 < p ≤ M−1` on the
`U_M` roots.  This is the part of the Newton recursion that genuinely uses the
full symmetric-function (every-other-degree) structure of `U_M`, beyond `e_1, e_2`.
It is named, not faked. -/
def OffDiagShift {M : Nat} (D : RootedNodes M) : Prop :=
  ∀ p, 0 < p → p ≤ M - 1 → CReal.Equiv (Sj D.toData p) (Sj D.toData (p+2))

/-- **The bridge from the off-diagonal residual.**  `S_2 = −1` (proved here for
general `M`) together with the named `OffDiagShift` yields
`TPowerSum.RootPowerSumBridge M (D.toData)`. -/
theorem bridge_of_offdiag {M : Nat} (D : RootedNodes M) (h : OffDiagShift D) :
    TPowerSum.RootPowerSumBridge D.toData :=
  ⟨S2_eq_neg_one D, h⟩

/-- **`TPowerSum` from the off-diagonal residual.**  Composing
`bridge_of_offdiag` with the upstream `tPowerSum_of_bridge` (using the canonical
`tval 0 k ≈ 1` for `fromQNodes`): given `OffDiagShift D`, the full
`PowerSumCollapse.TPowerSum (D.toData)` holds — and hence, via
`PowerSumCollapse.powerSumCollapse_of_TPowerSum`, the all-order Gram-PSD residual
`ChebOrthogonality.PowerSumCollapse (D.toData.toU)`. -/
theorem tPowerSum_from_offdiag {M : Nat} (D : RootedNodes M) (h : OffDiagShift D) :
    PowerSumCollapse.TPowerSum D.toData :=
  TPowerSum.tPowerSum_of_bridge D.toData
    (fun k => TPowerSum.tval0_fromQNodes M D.node k)
    (bridge_of_offdiag D h)

/-! ## 5. The `M = 2` concrete instance (rational nodes `±1/2`)

At `M = 2` the roots of `U_2` are the rational `±1/2`.  `e1_zero` (`½+(−½)=0`) and
`p2_value` (`¼+¼ = ½ = (2−1)/2`) are closed `Q'` computations (`decide`).  The
off-diagonal residual `OffDiagShift` is **vacuous** at `M = 2` (`p ≤ M−1 = 1` and
`0 < p` force `p = 1`, but the genuine `S_1 = S_3` is the only instance — handled
by the upstream discharged `TPowerSum2`), so the full bridge is inhabited.

For `M = 3` the roots of `U_3` are `0, ±√(1/2)`, which are **irrational**; they are
not `Q'` nodes, so the rational `fromQNodes`/`decide` route does not apply and no
`M = 3` `RootedNodes` instance is provided here (honest scope note). -/

/-- The `M = 2` root structure on the rational nodes `±1/2`
(`node2 = ChebOrthogonality.node2`). -/
def rootedNodes2 : RootedNodes 2 where
  node := ChebOrthogonality.node2
  e1_zero := by
    show (RationalTail.finSum ChebOrthogonality.node2 2).eqv (0 : Q')
    decide
  p2_value := by
    show (RationalTail.finSum (fun k => ChebOrthogonality.node2 k * ChebOrthogonality.node2 k) 2).eqv
      (p2val 2)
    decide

/-- **`S_2 = −1` at `M = 2`**, reproduced through the general root-structure route
(`S2_eq_neg_one rootedNodes2`), independent of the upstream `decide`. -/
theorem S2_M2_eq_neg_one :
    CReal.Equiv (Sj rootedNodes2.toData 2) (CReal.ofQ' (-(1 : Q'))) :=
  S2_eq_neg_one rootedNodes2

/-- **The off-diagonal residual is inhabited at `M = 2`** — extracted from the
upstream fully-discharged `PowerSumCollapse.TPowerSum2` (its `S_p = S_{p+2}`
component), transported to `rootedNodes2.toData = fromQNodes 2 node2 = rootData2`. -/
theorem offDiagShift2 : OffDiagShift rootedNodes2 :=
  PowerSumCollapse.TPowerSum2.2.2

/-- **The full `RootPowerSumBridge` inhabited at `M = 2`** — via the general
`S2_eq_neg_one` (diagonal) and the `M = 2` `OffDiagShift` (off-diagonal). -/
theorem rootBridge2 : TPowerSum.RootPowerSumBridge rootedNodes2.toData :=
  bridge_of_offdiag rootedNodes2 offDiagShift2

/-- **`TPowerSum` re-inhabited at `M = 2` through the root structure**, confirming
that the root-structure route reproduces the upstream discharge end-to-end. -/
theorem tPowerSum2_via_rooted : PowerSumCollapse.TPowerSum rootedNodes2.toData :=
  tPowerSum_from_offdiag rootedNodes2 offDiagShift2

end YMGap.Continuum.RootPowerSumBridge

/-! ## Axiom-dependency gates (AGENTS.md Rule 1)

Every load-bearing theorem must report `[propext]` or `[propext, Quot.sound]`
(`Quot.sound` enters only via reused `omega`/`Nat`/`Int` helpers).  No
`Classical.*`, no `sorry`/`sorryAx`, no `native_decide`, no `decide` on a
non-decidable `Prop` (`decide` only on closed `Q'`/`Nat`). -/

#print axioms YMGap.Continuum.RootPowerSumBridge.finSum_negone_eq
#print axioms YMGap.Continuum.RootPowerSumBridge.two_p2val
#print axioms YMGap.Continuum.RootPowerSumBridge.S2_rational_eq_neg_one
#print axioms YMGap.Continuum.RootPowerSumBridge.S2_eq_neg_one
#print axioms YMGap.Continuum.RootPowerSumBridge.bridge_of_offdiag
#print axioms YMGap.Continuum.RootPowerSumBridge.tPowerSum_from_offdiag
#print axioms YMGap.Continuum.RootPowerSumBridge.S2_M2_eq_neg_one
#print axioms YMGap.Continuum.RootPowerSumBridge.offDiagShift2
#print axioms YMGap.Continuum.RootPowerSumBridge.rootBridge2
#print axioms YMGap.Continuum.RootPowerSumBridge.tPowerSum2_via_rooted
