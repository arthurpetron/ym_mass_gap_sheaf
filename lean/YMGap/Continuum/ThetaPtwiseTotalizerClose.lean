/-
# Closing the `F`-entangled pointwise theta limits `ThetaPtwiseData` (Target A)

`ThetaSeriesC1Close.ThetaPtwiseData a x F` bundles the two undifferentiated
pointwise theta limits of the Chebyshev-`T` truncation `chebTTrunc a`:

  * `ptθ  : PtwiseConvC (chebTTrunc a) F x`
  * `ptθh : ∀ h, PtwiseConvC (chebTTrunc a) F (x + h)`.

Both are *self-convergence of the `T`-truncation to its own limit at a per-point
stage*.  This module closes them GENUINELY once the common limit `F` is taken to
be the per-point CReal limit of the truncations, and once a per-point geometric
majorant of the `T`-terms is supplied.

## What is genuinely proved here

* **`chebTTerm_abs_le_onbox`** — the ON-BOX termwise bound (Atom 0):
  `|chebTTerm a l y| ≤ geoIncrBase a a l = a·aˡ` for `y ∈ [−1,1]`.  Routes through
  `ChebU.Tabs_le_one` (`|T_{l+1}| ≤ 1` on the box), `abs_mul_le`, and
  `pow_base_antitone` (`a^{(l+1)²} ≤ a^{l+1}`, since `l+1 ≤ (l+1)²`).  This is the
  concrete crux — the per-point majorant IS discharged on the box.

* **`chebT_step_up` / `chebT_step_lo`** — the two single-step increment bounds
  `|chebTTrunc(l+1) − chebTTrunc(l)| ≤ geoIncrBase (C y) a l` from a per-point
  geometric majorant `PtMajorant`.

* **`chebTConvPt`** — the per-point CReal limit of the truncations, built from
  `PtMajorant` via `HKConvGen.crealOfGeoIncrementBase`.

* **`chebT_self_conv`** (the `T`-analogue of `dSeries_self_conv`) — the
  self-convergence at the geometric tail:
  `|chebTConvPt ⊖ ofQ'(chebTTrunc a M y)| ≤ geoTailBase (C y) a M`.

* **`ptwiseConv`** — THE closed `PtwiseConvC` field, modulus
  `Nθ ε = powBaseCutoff a (ε/(C y·H))`.

* **`thetaPtwiseData_of_totalMajorant`** — THE ASSEMBLED `ThetaPtwiseData`, both
  fields (`ptθ`, `ptθh`), from a total per-point majorant `TotalMajorant`.

## The honest residual (AGENTS.md Rule 6)

`ptθh` quantifies over ALL `h`, so `x+h` ranges over all of `Q'` and the on-box
`|T|≤1` fails off `[−1,1]`.  Constructing `TotalMajorant a` therefore requires the
OFF-BOX per-point Gaussian-beats-polynomial constant: a rational `C_y` with
`a^{(l+1)²}·(2B_y)^{l+1} ≤ C_y·aˡ` (with `|T_m(y)| ≤ (2B_y)^m` the elementary
Chebyshev poly bound).  That single per-point constant — "`a^{n²}` beats any
bounded/exponential argument" — is the sharpest remaining piece; it is NOT closed
here and is left as the named `Type`-level obligation `TotalMajorant`.  The on-box
case (`onBoxPtMajorant`) shows the obligation is genuinely met on `[−1,1]`.

## Coupling caveat (honesty)

Choosing `F := chebTConv` makes `ThetaPtwiseData` self-referential and closable in
isolation, but the SAME `F` feeds the product side, which pins `F` to the
undifferentiated Jacobi product.  So `ThetaPtwiseData` is closable, but its `F` is
not free of the product side.

## Axiom gate (AGENTS.md Rule 1)

`[propext]` / `[propext, Quot.sound]` only.  No `Classical.*`, no `native_decide`,
no `sorry`.
-/

import YMGap.Continuum.ThetaSeriesFDDeriv
import YMGap.Continuum.ThetaSeriesC1Close
import YMGap.Continuum.ThetaSeriesFieldsClose
import YMGap.Continuum.JTPIdentity
import YMGap.Continuum.HeatKernelConvGen
import YMGap.Continuum.ChebyshevBound
import YMGap.Continuum.ChebyshevU
import YMGap.Continuum.KPLimit
import YMGap.Constructive.CRealLe
import YMGap.Constructive.CRealAbs
import YMGap.Constructive.CRealAdd
import YMGap.Constructive.CRealExp
import YMGap.Constructive.Reals

namespace YMGap.Continuum.ThetaPtwiseTotalizerClose

open YMGap.Constructive
open YMGap.Continuum

/-! ## 1. Atom 0 — the on-box termwise bound `|chebTTerm a l y| ≤ a·aˡ` -/

/-- **Atom 0 (on-box).**  For `0 < a < 1` and `y ∈ [−1,1]`, the `l`-th Chebyshev-`T`
truncation term is dominated by the geometric increment `geoIncrBase a a l = a·aˡ`:
`|a^{(l+1)²}·T_{l+1}(y)| ≤ a^{(l+1)²} ≤ a^{l+1} = a·aˡ`. -/
theorem chebTTerm_abs_le_onbox {a : Q'} (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q'))
    (l : Nat) {y : Q'} (hy1 : y ≤ (1 : Q')) (hym1 : (-(1 : Q')) ≤ y) :
    Q'.abs (ThetaSeriesC1Close.chebTTerm a l y)
      ≤ HKConvGen.geoIncrBase a a l := by
  -- |T_{l+1}(y)| ≤ 1 on the box
  have hTb := ChebU.Tabs_le_one l y hy1 hym1
  have hTabs : Q'.abs (Cheb.T (l + 1) y) ≤ (1 : Q') := Q'.abs_le hTb.1 hTb.2
  have hpownn : (0 : Q') ≤ a ^ ((l + 1) * (l + 1)) := Q'.pow_nonneg a (Q'.le_of_lt ha0) _
  -- exponent inequality `l+1 ≤ (l+1)²`
  have hle_exp : l + 1 ≤ (l + 1) * (l + 1) := by
    rw [Nat.succ_mul]
    exact Nat.le_add_left (l + 1) (l * (l + 1))
  -- unfold chebTTerm and chase
  show Q'.abs (a ^ ((l + 1) * (l + 1)) * Cheb.T (l + 1) y)
      ≤ HKConvGen.geoIncrBase a a l
  refine Q'.le_trans' _ _ _
    (TsumDeriv.Q'.abs_mul_le (a ^ ((l + 1) * (l + 1))) (Cheb.T (l + 1) y)) ?_
  -- |a^N|·|T| ≤ |a^N|·1
  refine Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ _ hTabs (Q'.abs_nonneg _)) ?_
  -- |a^N|·1 ≈ |a^N| = a^N
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.mul_one_eqv (Q'.abs (a ^ ((l + 1) * (l + 1)))))) ?_
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv (TsumDeriv.Q'.abs_of_nonneg hpownn)) ?_
  -- a^{(l+1)²} ≤ a^{l+1} = a·aˡ = geoIncrBase a a l  (defeq on the RHS)
  exact HKConvGen.pow_base_antitone (Q'.le_of_lt ha0) (Q'.le_of_lt ha1) hle_exp

/-! ## 2. The per-point geometric majorant and the single-step increments -/

/-- **A per-point geometric majorant** of the Chebyshev-`T` terms at `y`: a
positive rational `C` with `|chebTTerm a l y| ≤ C·aˡ` for all `l`. -/
structure PtMajorant (a y : Q') : Type where
  /-- The per-point geometric constant. -/
  C : Q'
  /-- Positivity of the constant. -/
  Cpos : (0 : Q') < C
  /-- The per-term geometric bound. -/
  bound : ∀ l : Nat,
    Q'.abs (ThetaSeriesC1Close.chebTTerm a l y) ≤ HKConvGen.geoIncrBase C a l

/-- On the box `[−1,1]` the majorant is realised with constant `C = a`
(Atom 0). -/
def onBoxPtMajorant {a : Q'} (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q'))
    {y : Q'} (hy1 : y ≤ (1 : Q')) (hym1 : (-(1 : Q')) ≤ y) : PtMajorant a y where
  C := a
  Cpos := ha0
  bound := fun l => chebTTerm_abs_le_onbox ha0 ha1 l hy1 hym1

/-- **Upper single-step increment**
`chebTTrunc(l+1) ≤ chebTTrunc(l) + geoIncrBase (C y) a l`. -/
theorem chebT_step_up {a : Q'} {y : Q'} (pm : PtMajorant a y) (l : Nat) :
    ThetaSeriesFDDeriv.chebTTrunc a (l + 1) y
      ≤ ThetaSeriesFDDeriv.chebTTrunc a l y + HKConvGen.geoIncrBase pm.C a l := by
  -- chebTTrunc a (l+1) y = chebTTrunc a l y + chebTTerm a l y  (finSum succ, defeq)
  have hstep : ThetaSeriesFDDeriv.chebTTrunc a (l + 1) y
      = ThetaSeriesFDDeriv.chebTTrunc a l y + ThetaSeriesC1Close.chebTTerm a l y := rfl
  rw [hstep]
  exact Q'.add_le_add_left _ _ _
    (Q'.le_trans' _ _ _ (Q'.le_abs_self _) (pm.bound l))

/-- **Lower single-step increment**
`chebTTrunc(l) ≤ chebTTrunc(l+1) + geoIncrBase (C y) a l`. -/
theorem chebT_step_lo {a : Q'} {y : Q'} (pm : PtMajorant a y) (l : Nat) :
    ThetaSeriesFDDeriv.chebTTrunc a l y
      ≤ ThetaSeriesFDDeriv.chebTTrunc a (l + 1) y + HKConvGen.geoIncrBase pm.C a l := by
  have hstep : ThetaSeriesFDDeriv.chebTTrunc a (l + 1) y
      = ThetaSeriesFDDeriv.chebTTrunc a l y + ThetaSeriesC1Close.chebTTerm a l y := rfl
  rw [hstep]
  refine Q'.le_trans' _ _ _ ?_
    (Q'.le_of_eqv (Q'.eqv_symm
      (Q'.add_assoc_eqv (ThetaSeriesFDDeriv.chebTTrunc a l y)
        (ThetaSeriesC1Close.chebTTerm a l y) (HKConvGen.geoIncrBase pm.C a l))))
  refine Q'.add_le_self_of_nonneg (ThetaSeriesFDDeriv.chebTTrunc a l y)
    (ThetaSeriesC1Close.chebTTerm a l y + HKConvGen.geoIncrBase pm.C a l) ?_
  -- 0 ≤ chebTTerm + geoIncrBase  ⟺  −geoIncrBase ≤ chebTTerm
  have hlo' : -(HKConvGen.geoIncrBase pm.C a l) ≤ ThetaSeriesC1Close.chebTTerm a l y := by
    have h1 : -(ThetaSeriesC1Close.chebTTerm a l y) ≤ HKConvGen.geoIncrBase pm.C a l :=
      Q'.le_trans' _ _ _ (Q'.neg_le_abs _) (pm.bound l)
    have h2 := Q'.neg_le_neg h1
    exact Q'.le_trans' _ _ _ h2
      (Q'.le_of_eqv (Q'.neg_neg_eqv (ThetaSeriesC1Close.chebTTerm a l y)))
  have h3 : -(HKConvGen.geoIncrBase pm.C a l) + HKConvGen.geoIncrBase pm.C a l
      ≤ ThetaSeriesC1Close.chebTTerm a l y + HKConvGen.geoIncrBase pm.C a l :=
    Q'.add_le_add_right _ _ (HKConvGen.geoIncrBase pm.C a l) hlo'
  refine Q'.le_trans' _ _ _ ?_ h3
  exact Q'.ge_of_eqv (Q'.neg_add_self_eqv (HKConvGen.geoIncrBase pm.C a l))

/-- The base-`a` `divPos` modulus witness (verbatim clone of `dSeriesCReal`). -/
theorem chebT_modulus {a : Q'} (ha0 : (0 : Q') < a) {y : Q'} (pm : PtMajorant a y) :
    ∀ ε : Q', (0 : Q') < ε →
      ∃ δ : Q', (0 : Q') < δ ∧
        (pm.C * HKConv.divPos 1 (1 + (-a))) * δ ≤ ε := by
  intro ε hε
  have hKpos : 0 < (pm.C * HKConv.divPos 1 (1 + (-a))).num := by
    have hDpos : (0 : Q') < HKConv.divPos 1 (1 + (-a)) :=
      HKConv.divPos_pos (by decide : (0 : Int) < (1 : Q').num)
    exact CReal.num_pos_of_pos (HKPos.q_mul_pos pm.Cpos hDpos)
  refine ⟨HKConv.divPos ε (pm.C * HKConv.divPos 1 (1 + (-a))),
    HKConv.divPos_pos (CReal.num_pos_of_pos hε), ?_⟩
  refine Q'.le_of_eqv ?_
  refine Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) ?_
  exact HKConv.divPos_mul_eqv hKpos

/-! ## 3. The per-point CReal limit of the truncations -/

/-- **The per-point CReal limit** of the Chebyshev-`T` truncations at `y`, from a
per-point geometric majorant.  `approx k = chebTTrunc a k y`. -/
def chebTConvPt {a : Q'} (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q'))
    {y : Q'} (pm : PtMajorant a y) : CReal :=
  HKConvGen.crealOfGeoIncrementBase
    (fun l => ThetaSeriesFDDeriv.chebTTrunc a l y) pm.C a
    (Q'.le_of_lt pm.Cpos) ha0 ha1
    (chebT_step_up pm) (chebT_step_lo pm) (chebT_modulus ha0 pm)

@[simp] theorem chebTConvPt_approx {a : Q'} (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q'))
    {y : Q'} (pm : PtMajorant a y) (k : Nat) :
    (chebTConvPt ha0 ha1 pm).approx k = ThetaSeriesFDDeriv.chebTTrunc a k y := rfl

/-! ## 4. Self-convergence of the per-point limit at the geometric tail -/

/-- **`chebT_self_conv`** (the `T`-analogue of `dSeries_self_conv`).  The per-point
CReal limit is within its own geometric tail of each truncation:
`|chebTConvPt ⊖ ofQ'(chebTTrunc a M y)| ≤ geoTailBase (C y) a M`. -/
theorem chebT_self_conv {a : Q'} (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q'))
    {y : Q'} (pm : PtMajorant a y) (M : Nat) :
    CReal.leRat
      (CReal.abs (CReal.add (chebTConvPt ha0 ha1 pm)
        (CReal.neg (CReal.ofQ' (ThetaSeriesFDDeriv.chebTTrunc a M y)))))
      (HKConvGen.geoTailBase pm.C a M) := by
  apply CReal.leRat_of_eventually
  refine ⟨M, fun n hn => ?_⟩
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hn
  show Q'.abs (ThetaSeriesFDDeriv.chebTTrunc a (M + d) y
      + -(ThetaSeriesFDDeriv.chebTTrunc a M y))
      ≤ HKConvGen.geoTailBase pm.C a M
  refine CReal.abs_sub_le_of_bounds ?_ ?_
  · -- chebTTrunc(M+d) ≤ chebTTrunc M + geoTailBase
    refine Q'.le_trans' _ _ _
      (telescope_up (fun l => ThetaSeriesFDDeriv.chebTTrunc a l y)
        (HKConvGen.geoIncrBase pm.C a) (chebT_step_up pm) M d) ?_
    exact Q'.add_le_add_left _ _
      (HKConvGen.geoTailBase pm.C a M)
      (HKConvGen.geoTailBase_series_le (Q'.le_of_lt pm.Cpos) ha0 ha1 M d)
  · -- chebTTrunc M ≤ chebTTrunc(M+d) + geoTailBase
    refine Q'.le_trans' _ _ _
      (telescope_lo (fun l => ThetaSeriesFDDeriv.chebTTrunc a l y)
        (HKConvGen.geoIncrBase pm.C a) (chebT_step_lo pm) M d) ?_
    exact Q'.add_le_add_left _ _
      (HKConvGen.geoTailBase pm.C a M)
      (HKConvGen.geoTailBase_series_le (Q'.le_of_lt pm.Cpos) ha0 ha1 M d)

/-! ## 5. A total per-point majorant and the assembled pointwise data -/

/-- **A total per-point geometric majorant**: for EVERY point `y : Q'`, a positive
per-point geometric constant `C y` dominating the truncation terms.  On `[−1,1]`,
`C y = a` works (`onBoxPtMajorant`); off `[−1,1]` it is the Gaussian-beats-poly
per-point constant (the sharp residual).  This is the sole `Type`-level obligation
of Target A. -/
structure TotalMajorant (a : Q') : Type where
  /-- The per-point geometric constant, as a function of the point. -/
  C : Q' → Q'
  /-- Positivity everywhere. -/
  Cpos : ∀ y : Q', (0 : Q') < C y
  /-- The per-term geometric bound at every point. -/
  bound : ∀ y : Q', ∀ l : Nat,
    Q'.abs (ThetaSeriesC1Close.chebTTerm a l y) ≤ HKConvGen.geoIncrBase (C y) a l

/-- The per-point majorant at `y` extracted from a total majorant. -/
def TotalMajorant.pt {a : Q'} (tm : TotalMajorant a) (y : Q') : PtMajorant a y where
  C := tm.C y
  Cpos := tm.Cpos y
  bound := tm.bound y

/-- **The common CReal limit** `F : Q' → CReal` from a total majorant. -/
def chebTConv {a : Q'} (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q'))
    (tm : TotalMajorant a) : Q' → CReal :=
  fun y => chebTConvPt ha0 ha1 (tm.pt y)

/-- **The closed per-point convergence field** `PtwiseConvC (chebTTrunc a) F y`,
modulus `Nθ ε = powBaseCutoff a (ε/(C y·H))`. -/
def ptwiseConv {a : Q'} (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q'))
    (tm : TotalMajorant a) (y : Q') :
    ThetaSeriesFDDeriv.PtwiseConvC (ThetaSeriesFDDeriv.chebTTrunc a)
      (chebTConv ha0 ha1 tm) y where
  Nθ := fun ε => HKConvGen.powBaseCutoff a
    (HKConv.divPos ε (tm.C y * HKConv.divPos 1 (1 + (-a))))
  conv := fun ε hε M hM =>
    CReal.leRat_mono (chebT_self_conv ha0 ha1 (tm.pt y) M)
      (ThetaSeriesFieldsClose.geoTailBase_le_of_cutoff_gen (tm.Cpos y) ha0 ha1 hε M hM)

/-- **THE ASSEMBLED `ThetaPtwiseData` (both fields).**  From a total per-point
geometric majorant, the two `F`-entangled pointwise theta limits of the
Chebyshev-`T` truncations are both closed, with the common limit
`F := chebTConv`.  The only open input is the total majorant itself (on-box
proved, off-box = the Gaussian-beats-poly per-point constant). -/
def thetaPtwiseData_of_totalMajorant {a x : Q'} (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q'))
    (tm : TotalMajorant a) :
    ThetaSeriesC1Close.ThetaPtwiseData a x (chebTConv ha0 ha1 tm) where
  ptθ := ptwiseConv ha0 ha1 tm x
  ptθh := fun h => ptwiseConv ha0 ha1 tm (x + h)

end YMGap.Continuum.ThetaPtwiseTotalizerClose

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.ThetaPtwiseTotalizerClose.chebTTerm_abs_le_onbox
#print axioms YMGap.Continuum.ThetaPtwiseTotalizerClose.chebT_step_up
#print axioms YMGap.Continuum.ThetaPtwiseTotalizerClose.chebT_step_lo
#print axioms YMGap.Continuum.ThetaPtwiseTotalizerClose.chebT_modulus
#print axioms YMGap.Continuum.ThetaPtwiseTotalizerClose.chebTConvPt
#print axioms YMGap.Continuum.ThetaPtwiseTotalizerClose.chebT_self_conv
#print axioms YMGap.Continuum.ThetaPtwiseTotalizerClose.ptwiseConv
#print axioms YMGap.Continuum.ThetaPtwiseTotalizerClose.thetaPtwiseData_of_totalMajorant
