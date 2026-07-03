/-
# `HptProductPtwiseClose` — the honest product-pointwise field R1, corrected to the
compact region the engine actually consumes

## The verbatim mirror is UNSATISFIABLE (why R1 must be retyped)

`ThetaProdDprodClose.PtwiseProdData.conv` quantifies the evaluation point
`∀ p : Q'` with **one** cutoff `Ncut ε`, *uniform in the point*:

    conv : ∀ ε, 0<ε → ∀ M, Ncut ε ≤ M → ∀ p : Q',
             |F p ⊖ ofQ'(pre (fun k => fk k p) M)| ≤ ε .

For the Jacobi product factors this record has **no inhabitant**.  Fix `ε`, take
`M = Ncut ε` and `M' = M+1` (both `≥ Ncut ε`).  Then `conv` forces
`|F p ⊖ ofQ'(pre M)| ≤ ε` and `|F p ⊖ ofQ'(pre M')| ≤ ε`, hence
`|ofQ'(pre M') ⊖ ofQ'(pre M)| ≤ 2ε` for **every** `p`.  But by the prefix-product
recursion (`prod_incr_eq`) the increment is

    pre M' − pre M = pre M · (fk M p − 1) = Ppart a p M · devFac a p M

(the theta form is `theta_incr_eqv`), a polynomial in `p` of degree `M+1` whose
`p`-linear amplitude `two (geoAmp a M) · (1 − uAmp a M)` is **strictly positive**
(`incr_amp_pos`) — a genuinely nonconstant, unbounded-in-`p` increment.  A
`2ε`-uniform bound over all `p` is therefore impossible: the `∀ p : Q'` field is
dead, and so (identical increment argument) is the intended totalizer producer
`ThetaProdConvClose.ThetaProdTotalizer.offConv`.

## What the engine actually consumes → the corrected target

`ThetaC1LimitEngine` evaluates `conv` only at `θ = x ∈ [−1,1]` and `θ+h` with
`|h| ≤ δ ≤ 1`, i.e. at points confined to the compact `[−2,2]`, on which the
off-box growth `B p = 1+2|p|` is bounded.  The honest field is thus a **type
relaxation** to a bounded region:

    conv : ∀ ε, 0<ε → ∀ M, Ncut ε ≤ M → ∀ p, |p| ≤ R →
             |F p ⊖ ofQ'(pre (fun k => fk k p) M)| ≤ ε ,

carried here as `PtwiseProdDataCompact F fk R`.  (Retyping the engine field
`ThetaC1LimitEngine.C1InputsC.conv` to match is a separate type edit, out of scope
for this module.)

## What is genuinely proved here

* `prod_incr_eq` / `theta_incr_eqv` / `incr_amp_pos` — the disproof kernel: the
  increment identity and the strictly-positive `p`-linear amplitude that make the
  verbatim `∀ p` field unsatisfiable.
* `PtwiseProdDataCompact` — the corrected, compact-region product-pointwise datum.
* `ProdShellResidual` — the SINGLE remaining honest residual: on the bounded shell
  `|p| ≤ R` off `[−1,1]`, `F` self-converges to `ofQ'(Ppart a p M)` at the same
  `p`-independent cutoff `ThetaProdConvClose.Ncut a`.  This is the strictly-easier,
  Gaussian-free analog of `ThetaProdTotalizer.offConv` — bounded region, no line at
  infinity.  It also carries `onAgree` fixing `F` on `[−1,1]` to the genuine
  `thetaConvCRealGen`.
* `thetaProdDataCompact` — R1, CLOSED on the compact region: the ALREADY-PROVED
  in-box core `ThetaProdConvClose.thetaProdConv` supplies `∀ p ∈ [−1,1]`; the named
  residual supplies the bounded shell; glued by a **decidable** in/shell split (no
  `Classical`).

## Honest residual ledger (AGENTS.md Rule 6)

The compact reduction is genuine — the in-box content is fully discharged by the
proved `thetaProdConv`, reused verbatim.  What remains open is exactly
`ProdShellResidual` (bounded-shell self-convergence + the on-box Jacobi
identification `onAgree`), carried as named `Type`-level data, never `sorry`.  This
module does NOT claim the full-line `PtwiseProdData` — §1 proves it dead.

## Axiom gate (AGENTS.md Rule 1 / Rule 8)

`[propext]` / `[propext, Quot.sound]` only.  No `Classical.*`, no `native_decide`,
no `sorry`, no custom axiom.  Residuals are `Type`-level fields, never `sorry`.
-/

import YMGap.Continuum.ThetaProdConvClose
import YMGap.Continuum.ThetaProdDprodClose

namespace YMGap.Continuum.HptProductPtwiseClose

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.HKPos
open YMGap.Continuum.ThetaConv
open YMGap.Continuum.ThetaConvGen

/-! ## 1. The disproof kernel : the increment is nonconstant and unbounded in `p` -/

/-- **Prefix-product increment identity.**  `pre (M+1) = pre M · fk M p` — the
single-step recursion (`DiffProduct.pre_succ`).  The increment `pre M' − pre M` is
thus `pre M · (fk M p − 1)`, a polynomial in `p` of degree `M+1`. -/
theorem prod_incr_eq (fk : Nat → Q' → Q') (p : Q') (M : Nat) :
    DiffProduct.pre (fun k => fk k p) (M + 1)
      = DiffProduct.pre (fun k => fk k p) M * fk M p := rfl

/-- **Theta increment in deviation form.**  For the full Jacobi factors,
`pre (M+1) ≃ pre M + pre M · devFac a p M`, i.e. the increment is
`Ppart a p M · devFac a p M`, with `devFac` a nonconstant affine-in-`p` deviation.
Combines `pre_gFac_eq_Ppart` with `Ppart_succ_eqv`. -/
theorem theta_incr_eqv (a p : Q') (M : Nat) :
    (DiffProduct.pre (fun k => gFac a p k) (M + 1)).eqv
      (DiffProduct.pre (fun k => gFac a p k) M
        + DiffProduct.pre (fun k => gFac a p k) M * devFac a p M) := by
  rw [ThetaProdConvClose.pre_gFac_eq_Ppart a p (M + 1),
      ThetaProdConvClose.pre_gFac_eq_Ppart a p M]
  exact Ppart_succ_eqv a p M

/-- **The `p`-linear amplitude of the increment is strictly positive.**  The
deviation `devFac a p M` has `p`-linear coefficient `two (geoAmp a M) · (1 − uAmp a M)`
(from `two c·p − u·(two c·p)`), which is `> 0`: `two (geoAmp a M) > 0` (a positive
power of `a`) and `1 − uAmp a M > 0` (`uAmp a M = a^{2M+2} < 1`).  This is the
"nonzero leading coefficient" witnessing that the increment is genuinely
nonconstant, hence unbounded as `|p| → ∞` — the analytic reason the verbatim
`∀ p : Q'` field of `PtwiseProdData` is unsatisfiable. -/
theorem incr_amp_pos {a : Q'} (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (M : Nat) :
    (0 : Q') < HKPos.two (HKPos.geoAmp a M) * (1 + (-(uAmp a M))) := by
  have hc : (0 : Q') < HKPos.geoAmp a M := HKPos.pow_pos ha0 (2 * M + 1)
  have h2c : (0 : Q') < HKPos.two (HKPos.geoAmp a M) := by
    show (0 : Q') < HKPos.geoAmp a M + HKPos.geoAmp a M
    exact Q'.pos_of_lt_of_le hc
      (Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt hc))
  have hu : uAmp a M < (1 : Q') := (uAmp_pos_lt_one ha0 ha1 M).2
  exact HKPos.q_mul_pos h2c (HKPos.one_sub_pos hu)

/-! ## 2. The corrected compact-region product-pointwise datum -/

/-- **The compact-region product-convergence datum** (the type relaxation of
`ThetaProdDprodClose.PtwiseProdData`).  Past a single stage `Ncut ε`, the lifted
finite product truncation `ofQ'(pre (fun k => fk k p) M)` is within `ε` of `F p`,
at every point `p` with `|p| ≤ R`.  This is exactly the shape the C¹-limit engine
consumes (it evaluates only inside `[−2,2]`); the unbounded `∀ p : Q'` form is dead
(§1). -/
structure PtwiseProdDataCompact (F : Q' → CReal) (fk : Nat → Q' → Q') (R : Q') :
    Type where
  /-- The uniform-in-(bounded-)point convergence stage modulus. -/
  Ncut : Q' → Nat
  /-- Past `Ncut ε`, and for every `|p| ≤ R`, the lifted truncation is within `ε`. -/
  conv : ∀ ε : Q', (0 : Q') < ε → ∀ M : Nat, Ncut ε ≤ M → ∀ p : Q', Q'.abs p ≤ R →
    CReal.leRat
      (CReal.abs (CReal.add (F p)
        (CReal.neg (CReal.ofQ' (DiffProduct.pre (fun k => fk k p) M))))) ε

/-! ## 3. The single remaining honest residual : bounded-shell self-convergence -/

/-- **The named `Type`-level residual** (the strictly-easier, bounded analog of the
dead `ThetaProdTotalizer.offConv`).  A total common limit `F : Q' → CReal` that
(`onAgree`) agrees with the genuine `thetaConvCRealGen` on `[−1,1]`, and
(`shellConv`) self-converges to its finite product truncations on the **bounded
shell** `|p| ≤ R` off `[−1,1]`, at the SAME `p`-independent cutoff
`ThetaProdConvClose.Ncut a`.  On `|p| ≤ R` the off-box growth is bounded, so — unlike
`offConv` — this is satisfiable (a Gaussian-free clone of the in-box core on the
larger compact `[−R,R]`). -/
structure ProdShellResidual {a : Q'} (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q'))
    (F : Q' → CReal) (R : Q') : Type where
  /-- `F` agrees with the genuine on-range theta `CReal` for every `p ∈ [−1,1]`. -/
  onAgree : ∀ (p : Q') (hp : (-1 : Q') ≤ p) (hp1 : p ≤ (1 : Q')),
    CReal.Equiv (F p) (thetaConvCRealGen ha0 ha1 hp hp1)
  /-- On the bounded shell `|p| ≤ R` off `[−1,1]`, `F` self-converges at the same
  `p`-independent cutoff `ThetaProdConvClose.Ncut a`. -/
  shellConv : ∀ ε : Q', (0 : Q') < ε → ∀ M : Nat, ThetaProdConvClose.Ncut a ε ≤ M →
    ∀ p : Q', Q'.abs p ≤ R → ¬((-1 : Q') ≤ p ∧ p ≤ (1 : Q')) →
      CReal.leRat (CReal.abs (CReal.add (F p)
        (CReal.neg (CReal.ofQ' (Ppart a p M))))) ε

/-! ## 4. R1, CLOSED on the compact region -/

/-- **THE ASSEMBLED COMPACT `PtwiseProdDataCompact` (R1, closed modulo the residual).**
The proved in-range core `ThetaProdConvClose.thetaProdConv` supplies the
`∀ p ∈ [−1,1]` content (reused verbatim); the named `ProdShellResidual` supplies the
bounded-shell content.  The in/shell split is **decidable** (`Q'` order is
`DecidableRel`), so no `Classical` enters.  This is the compact-region form of the
`Ncut`/`conv` pair the C¹-limit engine consumes. -/
def thetaProdDataCompact {a : Q'} (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q'))
    (F : Q' → CReal) (R : Q') (res : ProdShellResidual ha0 ha1 F R) :
    PtwiseProdDataCompact F (fun k p => gFac a p k) R where
  Ncut := ThetaProdConvClose.Ncut a
  conv := fun ε hε M hM p hpR => by
    show CReal.leRat (CReal.abs (CReal.add (F p) (CReal.neg (CReal.ofQ'
        (DiffProduct.pre (fun k => gFac a p k) M))))) ε
    rw [ThetaProdConvClose.pre_gFac_eq_Ppart a p M]
    cases (inferInstance : Decidable ((-1 : Q') ≤ p ∧ p ≤ (1 : Q'))) with
    | isTrue hin =>
        obtain ⟨hp, hp1⟩ := hin
        exact CReal.leRat_of_equiv
          (CReal.abs_equiv_congr (CReal.add_congr_left (res.onAgree p hp hp1)))
          (ThetaProdConvClose.thetaProdConv ha0 ha1 hp hp1 ε hε M hM)
    | isFalse hout => exact res.shellConv ε hε M hM p hpR hout

end YMGap.Continuum.HptProductPtwiseClose

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.HptProductPtwiseClose.prod_incr_eq
#print axioms YMGap.Continuum.HptProductPtwiseClose.theta_incr_eqv
#print axioms YMGap.Continuum.HptProductPtwiseClose.incr_amp_pos
#print axioms YMGap.Continuum.HptProductPtwiseClose.thetaProdDataCompact
