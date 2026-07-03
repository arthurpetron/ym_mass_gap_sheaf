/-
# Closing the product-side `conv` field (Field-group 1) of the theta `C¹` inputs

`ThetaProdDprodClose.PtwiseProdData` is the pointwise (uniform-in-point)
convergence datum consumed by the product-side C¹-limit engine.  Its sole content
is the `conv` field: past a stage `Ncut ε`, the lifted finite product truncation
`ofQ'(pre (fun k => gFac a p k) M) = ofQ'(Ppart a p M)` is within `ε` of the
common CReal limit `F p`, at every evaluation point `p`.

This module CLOSES the genuine analytic core of that field: it is **finite-product
self-convergence**, a direct clone of the already-proved series-side lemma
`ThetaSeriesFieldsClose.dSeries_self_conv` / `seriesUnif`, with the roles

| series side (proved)                 | product side (this module)                 |
|--------------------------------------|--------------------------------------------|
| `JTPIdentity.dSeriesCReal`           | `ThetaConvGen.thetaConvCRealGen`           |
| `JTPIdentity.dPartial a x`           | `ThetaConv.Ppart a x`                      |
| `JTPIdentity.Cmaj a`, base `a`       | `ThetaConvGen.Cgen a`, base `a·a`          |
| `dPartial_step_up/lo`                | `Ppart_step_up/lo` + `Ppart_succ_eqv`      |

Choosing the common limit `F := thetaConvCRealGen` (the product `CReal` itself)
makes `conv` pure self-convergence needing **no** Jacobi identity.

## What is genuinely proved here

* `pre_gFac_eq_Ppart` — the defeq bridge `pre (fun k => gFac a x k) M = Ppart a x M`.
* `Cgen_pos` — the general-`a` increment constant is positive.
* `Ppart_step_up` / `Ppart_step_lo` — the two single-step base-`(a·a)` increment
  bounds (the anonymous `hup`/`hlo` lambdas of `thetaConvCRealGen`, named).
* `Ppart_self_conv` (Lemma A) — self-convergence at the geometric tail:
  `|thetaConvCRealGen ⊖ ofQ'(Ppart M)| ≤ geoTailBase (Cgen a) (a·a) M`.
* `thetaProdConv` — THE closed pointwise bound, with the explicit, `p`-independent
  base-`(a·a)` cutoff `Ncut a ε`, valid for every in-range `p ∈ [-1,1]`.

## The honest residual (AGENTS.md Rule 6)

`PtwiseProdData.conv` quantifies `∀ p : Q'` with **no** range side condition, but
`thetaConvCRealGen` (and the increment bounds `incr_le_gen`/`neg_incr_le_gen`) is
only defined / valid for `-1 ≤ p ≤ 1`.  The `p`-independent constant `Cgen a` and
base `a·a` make `Ncut a ε` uniform in `p` — but only over `p ∈ [-1,1]`.  Extending
the common limit `F` to a total `Q' → CReal` and controlling it off `[-1,1]` is
genuinely outside the `[-1,1]` analysis; it is carried as the named `Type`-level
residual `ThetaProdTotalizer` (`onAgree` fixing `F` on-range to
`thetaConvCRealGen`, plus `offConv` the off-range bound).  `thetaProdData`
assembles the full `PtwiseProdData` from the proved in-range core (`thetaProdConv`)
and that residual, via a **decidable** in/out-range split (no `Classical`).

## Axiom gate (AGENTS.md Rule 1 / Rule 8)

`[propext]` / `[propext, Quot.sound]` only.  No `Classical.*`, no `native_decide`,
no `sorry`, no custom axiom.  The residual is `Type`-level data, never `sorry`.
-/

import YMGap.Continuum.ThetaConvGen
import YMGap.Continuum.ThetaConv
import YMGap.Continuum.ThetaSeriesFieldsClose
import YMGap.Continuum.ThetaProdDprodClose
import YMGap.Continuum.HeatKernelConvGen
import YMGap.Continuum.KPLimit
import YMGap.Continuum.DiffProduct
import YMGap.Constructive.CRealLe
import YMGap.Constructive.CRealAbs
import YMGap.Constructive.CRealAdd
import YMGap.Constructive.CRealExp
import YMGap.Constructive.ExpAdd
import YMGap.Constructive.Reals

namespace YMGap.Continuum.ThetaProdConvClose

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.HKConv
open YMGap.Continuum.HKConvGen
open YMGap.Continuum.HKPos
open YMGap.Continuum.ThetaConv
open YMGap.Continuum.ThetaConvGen

/-! ## 1. The defeq bridge `pre (fun k => gFac a x k) = Ppart` -/

/-- **Defeq bridge.**  The prefix product of the full theta factors is exactly the
partial product `Ppart` (same recursion: `pre_zero/pre_succ` vs `Ppart` at index
`L`).  One-line `Nat` induction. -/
theorem pre_gFac_eq_Ppart (a x : Q') :
    ∀ M, DiffProduct.pre (fun k => gFac a x k) M = Ppart a x M
  | 0 => rfl
  | M + 1 => by
      show DiffProduct.pre (fun k => gFac a x k) M * gFac a x M
          = Ppart a x M * gFac a x M
      rw [pre_gFac_eq_Ppart a x M]

/-! ## 2. `Cgen a > 0` (the general-`a` increment constant) -/

/-- The general-`a` engine increment constant `Cgen a = Bmag a · 6a > 0`
(both factors positive).  Extracted from the sub-proof inside `thetaConvCRealGen`. -/
theorem Cgen_pos {a : Q'} (ha0 : (0 : Q') < a) : (0 : Q') < Cgen a := by
  have hB : (0 : Q') < Bmag a := by
    show (0 : Q') < prodUp (Tcoef a) (thetaCutoff a) * Q'.ofNat 2
    exact HKPos.q_mul_pos
      (Q'.pos_of_lt_of_le (CReal.pos_of_num_pos (by decide))
        (prodUp_ge_one (Tcoef_nonneg ha0) (thetaCutoff a)))
      (by decide)
  have hsix : (0 : Q') < sixA a := by
    show (0 : Q') < threeA a + threeA a
    exact Q'.pos_of_lt_of_le (threeA_pos ha0)
      (Q'.add_le_self_of_nonneg (threeA a) (threeA a) (threeA_nonneg ha0))
  show (0 : Q') < Bmag a * sixA a
  exact HKPos.q_mul_pos hB hsix

/-! ## 3. The two single-step increment bounds (base `a·a`, constant `Cgen a`) -/

/-- **Upper single-step increment** `Ppart(l+1) ≤ Ppart(l) + geoIncrBase (Cgen a) (a·a) l`.
The `hup` lambda of `thetaConvCRealGen`, named. -/
theorem Ppart_step_up {a x : Q'} (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q'))
    (hx : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q')) (l : Nat) :
    Ppart a x (l + 1) ≤ Ppart a x l + geoIncrBase (Cgen a) (a * a) l := by
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Ppart_succ_eqv a x l)) ?_
  refine Q'.add_le_add_left (Ppart a x l) _ (geoIncrBase (Cgen a) (a * a) l) ?_
  show Ppart a x l * devFac a x l ≤ Cgen a * (a * a) ^ l
  exact incr_le_gen ha0 ha1 hx hx1 l

/-- **Lower single-step increment** `Ppart(l) ≤ Ppart(l+1) + geoIncrBase (Cgen a) (a·a) l`.
The `hlo` lambda of `thetaConvCRealGen`, named. -/
theorem Ppart_step_lo {a x : Q'} (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q'))
    (hx : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q')) (l : Nat) :
    Ppart a x l ≤ Ppart a x (l + 1) + geoIncrBase (Cgen a) (a * a) l := by
  have heq : (Ppart a x (l + 1) + geoIncrBase (Cgen a) (a * a) l).eqv
      ((Ppart a x l + Ppart a x l * devFac a x l) + Cgen a * (a * a) ^ l) :=
    Q'.add_eqv_congr_right _ _ (Cgen a * (a * a) ^ l) (Ppart_succ_eqv a x l)
  refine Q'.le_trans' _ _ _ ?_ (Q'.ge_of_eqv heq)
  refine Q'.le_trans' _ _ _
    (Q'.add_le_self_of_nonneg (Ppart a x l)
      (Ppart a x l * devFac a x l + Cgen a * (a * a) ^ l) ?_)
    (Q'.le_of_eqv (Q'.eqv_symm
      (Q'.add_assoc_eqv (Ppart a x l) (Ppart a x l * devFac a x l)
        (Cgen a * (a * a) ^ l))))
  have hlo := neg_incr_le_gen ha0 ha1 hx hx1 l
  have h1 : -(Cgen a * (a * a) ^ l) + Cgen a * (a * a) ^ l
      ≤ Ppart a x l * devFac a x l + Cgen a * (a * a) ^ l :=
    Q'.add_le_add_right _ _ (Cgen a * (a * a) ^ l) hlo
  refine Q'.le_trans' _ _ _ ?_ h1
  exact Q'.ge_of_eqv (Q'.neg_add_self_eqv (Cgen a * (a * a) ^ l))

/-! ## 4. Lemma A — self-convergence of `thetaConvCRealGen` at the geometric tail -/

/-- **Lemma A.**  The product `CReal` is within its own geometric tail of each
partial product: `|thetaConvCRealGen ⊖ ofQ'(Ppart M)| ≤ geoTailBase (Cgen a) (a·a) M`.
Verbatim clone of `dSeries_self_conv`: `leRat_of_eventually` at threshold `M`; at
`n = M + d` the CReal difference unfolds (defeq, `thetaConvCRealGen_approx`) to
`|Ppart(M+d) − Ppart(M)|`, bounded by `abs_sub_le_of_bounds` fed by the two
telescoped tail bounds. -/
theorem Ppart_self_conv {a x : Q'} (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q'))
    (hx : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q')) (M : Nat) :
    CReal.leRat
      (CReal.abs (CReal.add (thetaConvCRealGen ha0 ha1 hx hx1)
        (CReal.neg (CReal.ofQ' (Ppart a x M)))))
      (geoTailBase (Cgen a) (a * a) M) := by
  apply CReal.leRat_of_eventually
  refine ⟨M, fun n hn => ?_⟩
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hn
  show Q'.abs (Ppart a x (M + d) + -(Ppart a x M))
      ≤ geoTailBase (Cgen a) (a * a) M
  refine CReal.abs_sub_le_of_bounds ?_ ?_
  · refine Q'.le_trans' _ _ _
      (telescope_up (Ppart a x) (geoIncrBase (Cgen a) (a * a))
        (Ppart_step_up ha0 ha1 hx hx1) M d) ?_
    exact Q'.add_le_add_left (Ppart a x M) _
      (geoTailBase (Cgen a) (a * a) M)
      (geoTailBase_series_le (Cgen_nonneg ha0) (HKPos.q_mul_pos ha0 ha0)
        (aa_lt_one ha0 ha1) M d)
  · refine Q'.le_trans' _ _ _
      (telescope_lo (Ppart a x) (geoIncrBase (Cgen a) (a * a))
        (Ppart_step_lo ha0 ha1 hx hx1) M d) ?_
    exact Q'.add_le_add_left (Ppart a x (M + d)) _
      (geoTailBase (Cgen a) (a * a) M)
      (geoTailBase_series_le (Cgen_nonneg ha0) (HKPos.q_mul_pos ha0 ha0)
        (aa_lt_one ha0 ha1) M d)

/-! ## 5. THE CLOSED POINTWISE BOUND (in-range core) -/

/-- The `p`-independent base-`(a·a)` cutoff `Ncut a ε = powBaseCutoff (a·a) (ε/(Cgen a·H))`. -/
def Ncut (a ε : Q') : Nat :=
  powBaseCutoff (a * a) (HKConv.divPos ε (Cgen a * HKConv.divPos 1 (1 + (-(a * a)))))

/-- **THE CLOSED POINTWISE BOUND (in-range core).**  Past the `p`-independent
cutoff `Ncut a ε`, the product `CReal` `thetaConvCRealGen` is within `ε` of its
finite truncation `ofQ'(Ppart a x M)`, for every `x ∈ [-1,1]`.  Lemma A monotone-
lifted through the base-general cutoff `geoTailBase_le_of_cutoff_gen` at
`C = Cgen a`, `r = a·a`.  The clone of `seriesUnif`'s `conv`. -/
theorem thetaProdConv {a x : Q'} (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q'))
    (hx : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q'))
    (ε : Q') (hε : (0 : Q') < ε) (M : Nat) (hM : Ncut a ε ≤ M) :
    CReal.leRat
      (CReal.abs (CReal.add (thetaConvCRealGen ha0 ha1 hx hx1)
        (CReal.neg (CReal.ofQ' (Ppart a x M))))) ε :=
  CReal.leRat_mono (Ppart_self_conv ha0 ha1 hx hx1 M)
    (ThetaSeriesFieldsClose.geoTailBase_le_of_cutoff_gen (Cgen_pos ha0)
      (HKPos.q_mul_pos ha0 ha0) (aa_lt_one ha0 ha1) hε M hM)

/-! ## 6. The named residual and the assembled `PtwiseProdData` -/

/-- **The named `Type`-level residual.**  What is genuinely outside the `[-1,1]`
analysis for the unrestricted `∀ p : Q'` field of `PtwiseProdData`: a choice of
total common limit `F : Q' → CReal` that (`onAgree`) agrees on `[-1,1]` with the
genuine `thetaConvCRealGen`, and (`offConv`) still self-converges to its finite
product truncations off `[-1,1]`, at the SAME `p`-independent cutoff `Ncut a`. -/
structure ThetaProdTotalizer {a : Q'} (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q'))
    (F : Q' → CReal) : Type where
  /-- `F` agrees with the genuine on-range theta `CReal` for every `p ∈ [-1,1]`. -/
  onAgree : ∀ (p : Q') (hp : (-1 : Q') ≤ p) (hp1 : p ≤ (1 : Q')),
    CReal.Equiv (F p) (thetaConvCRealGen ha0 ha1 hp hp1)
  /-- Off `[-1,1]`, `F` self-converges at the same `p`-independent cutoff. -/
  offConv : ∀ ε : Q', (0 : Q') < ε → ∀ M : Nat, Ncut a ε ≤ M → ∀ p : Q',
    ¬((-1 : Q') ≤ p ∧ p ≤ (1 : Q')) →
      CReal.leRat (CReal.abs (CReal.add (F p)
        (CReal.neg (CReal.ofQ' (Ppart a p M))))) ε

/-- **THE ASSEMBLED `PtwiseProdData` (Field-group 1, closed modulo the residual).**
The proved in-range core `thetaProdConv` supplies the `∀ p ∈ [-1,1]` content; the
named residual `ThetaProdTotalizer` supplies the off-range / total-`F` content.  The
in/out-range split is **decidable** (`Q'` order is `DecidableRel`), so no `Classical`
enters.  This is exactly the `Ncut`/`conv` pair `ThetaProdDprodClose.prodC1Inputs`
consumes as `Hpt`. -/
def thetaProdData {a : Q'} (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q'))
    (F : Q' → CReal) (res : ThetaProdTotalizer ha0 ha1 F) :
    ThetaProdDprodClose.PtwiseProdData F (fun k p => gFac a p k) where
  Ncut := Ncut a
  conv := fun ε hε M hM p => by
    show CReal.leRat (CReal.abs (CReal.add (F p) (CReal.neg (CReal.ofQ'
        (DiffProduct.pre (fun k => gFac a p k) M))))) ε
    rw [pre_gFac_eq_Ppart a p M]
    cases (inferInstance : Decidable ((-1 : Q') ≤ p ∧ p ≤ (1 : Q'))) with
    | isTrue hin =>
        obtain ⟨hp, hp1⟩ := hin
        exact CReal.leRat_of_equiv
          (CReal.abs_equiv_congr (CReal.add_congr_left (res.onAgree p hp hp1)))
          (thetaProdConv ha0 ha1 hp hp1 ε hε M hM)
    | isFalse hout => exact res.offConv ε hε M hM p hout

end YMGap.Continuum.ThetaProdConvClose

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.ThetaProdConvClose.pre_gFac_eq_Ppart
#print axioms YMGap.Continuum.ThetaProdConvClose.Cgen_pos
#print axioms YMGap.Continuum.ThetaProdConvClose.Ppart_step_up
#print axioms YMGap.Continuum.ThetaProdConvClose.Ppart_step_lo
#print axioms YMGap.Continuum.ThetaProdConvClose.Ppart_self_conv
#print axioms YMGap.Continuum.ThetaProdConvClose.thetaProdConv
#print axioms YMGap.Continuum.ThetaProdConvClose.thetaProdData
