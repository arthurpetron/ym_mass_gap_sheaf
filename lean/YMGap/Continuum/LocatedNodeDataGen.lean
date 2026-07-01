/-
# Inhabiting `LocatedNodeData M` from a per-`M` located rational bracket
# (`LocatedNodeDataGen` — bisection + T-sign closes general-`M` off-diagonal OS2)

`DeMoivreHalfGen.LocatedNodeData M` is the WHOLE residual of the uniform-in-`M`
de Moivre chain (the branch collapse is already proved): a node `x` with
`U_M(x) ≈ 0` (`root`) and the co-located branch sign `T_{M+1}(x) ≤ 0` (`sign`).
`deMoivreNode_of_located` turns any inhabitant into a full `DeMoivreNode M`, hence
general-`M` off-diagonal OS2 Gram positivity downstream.

## What is proved here (both fields of `LocatedNodeData M`, general `M`)

Given a **`LocatedBracketM M`** — the honest per-`M` rational datum: a sign-change
bracket `[lo,hi]` for `U_M`, two-sided Lipschitz constants `LipU`/`LipT` for `U_M`
and `T_{M+1}` on `[lo,hi]`, and the co-located rational T-sign certificate
`T_{M+1}(hi) + LipT·(hi−lo) ≤ 0` — we produce, for ALL `M`:

  * `xM`      — the located node `x` by bisection on `U_M` (`ChebRoot.bisectRoot`).
  * `xM_root` — `U_M(xM) ≈ 0`: a definitional approx-wise bridge from `Ucr` to
    `bisectFLo`, then `ChebRoot.bisectRoot_eval_zero`.  Free, fully general.
  * `xM_sign` — `T_{M+1}(xM) ≤ 0`: a `T`-branch Lipschitz enclosure across the whole
    bracket (`bound'` + width-monotonicity + the rational `tsign` certificate).
  * `locatedNodeData_of_bracket` / `deMoivreNode_of_bracket` — assembly:
    `LocatedBracketM M ⟹ LocatedNodeData M ⟹ DeMoivreNode M`.

## The honest residual (NOT closed here)

The sole remaining input is `LocatedBracketM M`.  For a FIXED `M` every field is a
`decide`/explicit-polynomial obligation (the `ueval2_*` template does exactly this
for `M = 2`).  For WIDE/general `M` two sub-obligations remain non-`decide`: the
uniform root-separation bracket enclosing `cos(π/(M+1))` (the standing rational-π
wall) and the packaging of `|U_M| ≤ M+1` into a `ChebRoot.LipBound` for `U_M` and
`T_{M+1}`.  Neither is discharged here; the construction consumes them as the
`LocatedBracketM` fields.

## Axiom gate (AGENTS.md Rule 1 / Rule 8)

`[propext]` / `[propext, Quot.sound]` only.  No `Classical.*`, no `sorry`/`sorryAx`,
no `native_decide`, no custom axiom.  `LocatedBracketM`/`LocatedNodeData` are
`Type`-level records (witnesses as data, not `Prop`-∃).
-/

import YMGap.Continuum.DeMoivreHalfGen
import YMGap.Continuum.ChebRoot
import YMGap.Continuum.ChebLocatedRoots

namespace YMGap.Continuum.LocatedNodeDataGen

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.ChebRoot
open YMGap.Continuum.ChebLocatedRoots (Ucr Tcr Ucr_approx Tcr_approx)
open YMGap.Constructive.SumOfSquares (Equiv_of_approx_eqv)

local infix:50 " ≈ " => Q'.eqv

/-! ## 0. Small rational rearrangement helpers (local copies of the private
`ChebRoot` lemmas) -/

/-- `(a + -b) + b ≃ a`. -/
private theorem sub_add_cancel_eqv (a b : Q') : ((a + -b) + b) ≈ a := by
  refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv a (-b) b) ?_
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left a (-b + b) 0 (Q'.neg_add_self_eqv b)) ?_
  exact Q'.eqv_of_eq (Q'.add_zero' a)

/-- From `p + -q ≤ ε` conclude `p ≤ q + ε`. -/
private theorem le_add_of_sub_le {p q ε : Q'} (h : p + -q ≤ ε) : p ≤ q + ε := by
  have hstep := Q'.add_le_add_right _ ε q h
  refine Q'.le_trans' _ _ _ (Q'.ge_of_eqv (sub_add_cancel_eqv p q)) ?_
  exact Q'.le_trans' _ _ _ hstep (Q'.le_of_eqv (Q'.add_comm_eqv ε q))

/-! ## 1. The per-`M` located rational bracket datum (the ONLY genuine input) -/

/-- **The honest per-`M` located bracket** for the largest `U_M`-root.  All fields are
`decide`/explicit-polynomial obligations for each fixed `M` (the `ueval2_*` template);
for general `M` the bracket and the two Lipschitz constants are the standing
rational-π / `LipBound`-adapter walls.

* `initU` — sign-change bracket `U_M(lo) ≤ 0 ≤ U_M(hi)` (bracketing the node).
* `lipU`  — two-sided Lipschitz bound for `U_M` on `[lo,hi]` (the bisection needs it).
* `lipT`  — two-sided Lipschitz bound for `T_{M+1}` on `[lo,hi]`.
* `tsign` — the co-located rational certificate that `T_{M+1}` stays `≤ 0` across the
  whole bracket (it equals `−1` at the exact node). -/
structure LocatedBracketM (M : Nat) where
  /-- The rational left endpoint of the sign-change bracket. -/
  lo : Q'
  /-- The rational right endpoint of the sign-change bracket. -/
  hi : Q'
  /-- Two-sided Lipschitz constant for `U_M` on `[lo,hi]`. -/
  LipU : Q'
  /-- Two-sided Lipschitz constant for `T_{M+1}` on `[lo,hi]`. -/
  LipT : Q'
  /-- The `U_M` sign-change bracket. -/
  initU : BisectInit (Ueval M) lo hi
  /-- `U_M` is two-sided Lipschitz with constant `LipU` on `[lo,hi]`. -/
  lipU : LipBound (Ueval M) lo hi LipU
  /-- `T_{M+1}` is two-sided Lipschitz with constant `LipT` on `[lo,hi]`. -/
  lipT : LipBound (Cheb.T (M + 1)) lo hi LipT
  /-- The co-located rational branch-sign certificate. -/
  tsign : Cheb.T (M + 1) hi + LipT * (hi + -lo) ≤ (0 : Q')

/-! ## 2. The located node -/

/-- The located `U_M`-node produced by bisection on the bracket. -/
def xM (M : Nat) (b : LocatedBracketM M) : CReal :=
  bisectRoot (Ueval M) b.lo b.hi b.initU

@[simp] theorem xM_approx (M : Nat) (b : LocatedBracketM M) (n : Nat) :
    (xM M b).approx n = bisectLo (Ueval M) b.lo b.hi n := rfl

/-! ## 3. `root` field — `U_M(xM) ≈ 0` (free, fully general) -/

/-- `U_M(xM) ≈ 0`.  The `Ucr` approx sequence is definitionally the `bisectFLo`
approx sequence of `U_M`, so `Equiv_of_approx_eqv` transports `bisectRoot_eval_zero`. -/
theorem xM_root (M : Nat) (b : LocatedBracketM M) :
    CReal.Equiv (Ucr (xM M b) M) (CReal.ofQ' 0) := by
  have happrox : ∀ n, ((Ucr (xM M b) M).approx n).eqv
      ((bisectFLo (Ueval M) b.lo b.hi b.LipU b.initU b.lipU).approx n) := by
    intro n
    exact Q'.eqv_of_eq
      (show (Ucr (xM M b) M).approx n
          = (bisectFLo (Ueval M) b.lo b.hi b.LipU b.initU b.lipU).approx n
        from Ucr_approx (xM M b) n M)
  have hid : CReal.Equiv (Ucr (xM M b) M)
      (bisectFLo (Ueval M) b.lo b.hi b.LipU b.initU b.lipU) :=
    Equiv_of_approx_eqv happrox
  have hbis : CReal.Equiv (bisectFLo (Ueval M) b.lo b.hi b.LipU b.initU b.lipU) 0 :=
    bisectRoot_eval_zero (Ueval M) b.lo b.hi b.LipU b.initU b.lipU
  exact CReal.Equiv.trans hid hbis

/-! ## 4. `sign` field — `T_{M+1}(xM) ≤ 0` (T-branch Lipschitz enclosure) -/

/-- `T_{M+1}(xM) ≤ 0`.  Pointwise: each approx `T_{M+1}(zₙ)` with `zₙ ∈ [lo,hi]` is
`≤ T_{M+1}(hi) + LipT·(hi−lo) ≤ 0` by the two-sided Lipschitz bound, width-monotonicity,
and the rational `tsign` certificate. -/
theorem xM_sign (M : Nat) (b : LocatedBracketM M) :
    Tcr (xM M b) (M + 1) ≤ CReal.czero := by
  refine CReal.le_ofQ'_of_approx_le (ub := (0 : Q')) ?_
  intro n
  have e : (Tcr (xM M b) (M + 1)).approx n
      = Cheb.T (M + 1) (bisectLo (Ueval M) b.lo b.hi n) :=
    Tcr_approx (xM M b) n (M + 1)
  rw [e]
  -- Abbreviate the located lower endpoint `zₙ` (no `set`: keep the explicit term).
  have hlo : b.lo ≤ bisectLo (Ueval M) b.lo b.hi n :=
    bisectLo_ge (Ueval M) b.lo b.hi b.initU n
  have hhi : bisectLo (Ueval M) b.lo b.hi n ≤ b.hi :=
    Q'.le_trans' _ _ _
      (bisectLo_le_bisectHi (Ueval M) b.lo b.hi b.initU n)
      (bisectHi_le (Ueval M) b.lo b.hi b.initU n)
  -- Two-sided Lipschitz: T_{M+1}(zₙ) − T_{M+1}(hi) ≤ LipT·(hi − zₙ).
  have hbnd : Cheb.T (M + 1) (bisectLo (Ueval M) b.lo b.hi n) + -(Cheb.T (M + 1) b.hi)
      ≤ b.LipT * (b.hi + -(bisectLo (Ueval M) b.lo b.hi n)) :=
    b.lipT.bound' (bisectLo (Ueval M) b.lo b.hi n) b.hi hlo hhi (Q'.le_refl' b.hi)
  -- Width-monotone: hi − zₙ ≤ hi − lo, so LipT·(hi − zₙ) ≤ LipT·(hi − lo).
  have hwidth : b.hi + -(bisectLo (Ueval M) b.lo b.hi n) ≤ b.hi + -b.lo :=
    Q'.add_le_add_left b.hi (-(bisectLo (Ueval M) b.lo b.hi n)) (-b.lo) (Q'.neg_le_neg hlo)
  have hmul : b.LipT * (b.hi + -(bisectLo (Ueval M) b.lo b.hi n)) ≤ b.LipT * (b.hi + -b.lo) :=
    Q'.mul_le_mul_of_nonneg_left (b.hi + -(bisectLo (Ueval M) b.lo b.hi n)) (b.hi + -b.lo)
      b.LipT hwidth b.lipT.nonneg
  have hsub : Cheb.T (M + 1) (bisectLo (Ueval M) b.lo b.hi n) + -(Cheb.T (M + 1) b.hi)
      ≤ b.LipT * (b.hi + -b.lo) :=
    Q'.le_trans' _ _ _ hbnd hmul
  have hle2 : Cheb.T (M + 1) (bisectLo (Ueval M) b.lo b.hi n)
      ≤ Cheb.T (M + 1) b.hi + b.LipT * (b.hi + -b.lo) :=
    le_add_of_sub_le hsub
  exact Q'.le_trans' _ _ _ hle2 b.tsign

/-! ## 5. Assembly: `LocatedBracketM M ⟹ LocatedNodeData M ⟹ DeMoivreNode M` -/

/-- The per-`M` located node datum from the rational bracket. -/
def locatedNodeData_of_bracket (M : Nat) (b : LocatedBracketM M) :
    DeMoivreHalfGen.LocatedNodeData M where
  x := xM M b
  root := xM_root M b
  sign := xM_sign M b

/-- A fully inhabited de Moivre node from the rational bracket (branch collapse
already proved), hence general-`M` off-diagonal OS2 Gram positivity downstream. -/
def deMoivreNode_of_bracket (M : Nat) (b : LocatedBracketM M) :
    ChebRotationPair.DeMoivreNode M :=
  DeMoivreHalfGen.deMoivreNode_of_located M (locatedNodeData_of_bracket M b)

end YMGap.Continuum.LocatedNodeDataGen

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.LocatedNodeDataGen.xM_root
#print axioms YMGap.Continuum.LocatedNodeDataGen.xM_sign
#print axioms YMGap.Continuum.LocatedNodeDataGen.locatedNodeData_of_bracket
#print axioms YMGap.Continuum.LocatedNodeDataGen.deMoivreNode_of_bracket
