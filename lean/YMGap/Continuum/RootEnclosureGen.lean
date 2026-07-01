/-
# Polynomial-`LipT` located bracket: the uniform-`M` off-diagonal OS2 residual
# with a POLYNOMIAL width budget (`RootEnclosureGen`)

`LocatedBracketGen.RootEnclosure` reduces general-`M` off-diagonal OS2 Gram
positivity to a two-sided rational enclosure of the largest `U`-root inside the
`T`-negative window — but with the `T`-branch Lipschitz constant baked in as the
EXPONENTIAL `Amaj(k+2)+Amaj k` (`(2+√5)^k`-style, from the reused `QB_all`
majorant engine).  Under an exponential width budget the co-located `T`-sign
certificate `tsign : T_{k+2}(hi) + LipT·(hi−lo) ≤ 0` is unsatisfiable for any
rational `cos`-bracket whose margins are `O(1/n²)`: the budget `Amaj·width`
blows up.  This module supplies the missing structural move.

## The decisive structural fact

`LocatedNodeDataGen.LocatedBracketM M` carries **`LipT : Q'` as a genuine data
field**, and the whole downstream chain (`xM_sign`, `deMoivreNode_of_bracket`)
references *that field*, not any global constant.  The exponential is baked in
ONLY inside `RootEnclosure`/`locatedBracket_of_enclosure`.  Therefore the correct
move is to **bypass `RootEnclosure` with a parallel constructor** that supplies a
POLYNOMIAL `LipT := ofNat ((k+2)²)`.  A corollary read off the located-node
engine: `LipU` never enters the width budget (it only sets the root-`CReal`
Cauchy modulus in `bisectFLo`), so `LipU` stays the existing exponential
`Amaj(k+1)` and the already-proved `lipBound_U_of_QB (k+1)` is **reused
verbatim**.  Only `LipT` must go polynomial.

## What is PROVED here (axiom-clean)

  * `LipBound_mono` — a `LipBound` is monotone in its constant: any valid
    Lipschitz constant may be enlarged (`L ≤ L' → LipBound f lo hi L →
    LipBound f lo hi L'`).  Genuine reusable `Q'` lemma.
  * `locatedBracketPoly` — the parallel constructor `RootEnclosurePoly k ⟹
    LocatedBracketM (k+1)` with the POLYNOMIAL `LipT = ofNat ((k+2)²)`,
    **reusing** `LocatedBracketGen.lipBound_U_of_QB (k+1)` for the `lipU` field.
  * `deMoivreNodePoly` — the assembly `RootEnclosurePoly k ⟹ DeMoivreNode (k+1)`
    (branch collapse and `lipU` already proved), hence general-`M` off-diagonal
    OS2 Gram positivity downstream, RELATIVE TO the polynomial-budget residual.

## The honest residual — now with a POLYNOMIAL budget

`RootEnclosurePoly k` carries the three genuine walls as `Type`-level data:

  * `loSign` / `hiSign` — the rational-`π` `U`-sign facts `U_{k+1}(lo) ≤ 0`,
    `0 ≤ U_{k+1}(hi)` (the cyclotomic/`cos`-bridge wall; NOT a uniform `decide`).
  * `lipTpoly` — the POLYNOMIAL Markov `T`-secant `LipBound (T_{k+2}) lo hi
    (ofNat ((k+2)²))`, i.e. `|T_{k+2}(b)−T_{k+2}(a)| ≤ (k+2)²·(b−a)`.  This is the
    exact first-kind divided-difference bound; the `QB_all` engine provably
    supplies only the EXPONENTIAL constant, so the polynomial one is carried
    honestly here.
  * `tsign` — the co-located `T`-sign certificate `T_{k+2}(hi) + ofNat((k+2)²)·
    (hi−lo) ≤ 0`, now against the polynomial budget.

The delta versus `RootEnclosure` is exactly the postulate's structural point:
the `T`-branch budget is converted from `(2+√5)^k` to `(k+2)²`, which is the sole
thing making any `O(1/n²)`-margin rational `cos`-bracket admissible.  The `lipU`
field is discharged unconditionally (reused); the interval endpoints and the
three walls above remain the honest inputs, uniform in `k`.

## Axiom gate (AGENTS.md Rule 1 / Rule 8)

`[propext]` / `[propext, Quot.sound]` only.  No `Classical.*`, no
`sorry`/`sorryAx`, no `native_decide`, no custom axiom.  `RootEnclosurePoly` /
`LocatedBracketM` are `Type`-level records (witnesses as data, not `Prop`-∃).
-/

import YMGap.Continuum.LocatedBracketGen

namespace YMGap.Continuum.RootEnclosureGen

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.ChebRoot
open YMGap.Continuum.ChebMarkovModulus

/-! ## 1. `LipBound` is monotone in its constant (genuine reusable lemma) -/

/-- **`LipBound` is monotone in the Lipschitz constant.**  Any valid Lipschitz
constant may be enlarged: from `L ≤ L'` and `LipBound f lo hi L` conclude
`LipBound f lo hi L'`.  The width factor `b−a ≥ 0` (from `a ≤ b`) lets
`L·(b−a) ≤ L'·(b−a)`.  This records, in one clean fact, that the polynomial
budget `ofNat ((k+2)²)` supplied below is the SHARP requirement: the existing
exponential `lipBound_T_of_QB` is recoverable from it, never the converse. -/
theorem LipBound_mono {f : Q' → Q'} {lo hi L L' : Q'} (hLL : L ≤ L')
    (hb : LipBound f lo hi L) : LipBound f lo hi L' where
  nonneg := Q'.le_trans' _ _ _ hb.nonneg hLL
  bound := by
    intro a b ha hab hbb
    refine Q'.le_trans' _ _ _ (hb.bound a b ha hab hbb) ?_
    exact Q'.mul_le_mul_of_nonneg_right L L' (b + -a) hLL
      (LocatedBracketGen.sub_nonneg a b hab)
  bound' := by
    intro a b ha hab hbb
    refine Q'.le_trans' _ _ _ (hb.bound' a b ha hab hbb) ?_
    exact Q'.mul_le_mul_of_nonneg_right L L' (b + -a) hLL
      (LocatedBracketGen.sub_nonneg a b hab)

/-! ## 2. The polynomial-budget root enclosure (the honest residual) -/

/-- **The polynomial-budget rational root-enclosure residual.**  Identical in
role to `LocatedBracketGen.RootEnclosure`, but the `T`-branch Lipschitz constant
is the POLYNOMIAL `ofNat ((k+2)²)` rather than the exponential `Amaj(k+2)+Amaj k`.

* `hlo1`/`hhi1`/`hle` — the interval bounds `−1 ≤ lo ≤ hi ≤ 1`.
* `loSign`/`hiSign` — the rational-`π` `U`-sign facts (the `cos`-bridge wall).
* `lipTpoly` — the POLYNOMIAL Markov `T`-secant bound (the divided-difference
  wall; the `QB_all` engine yields only the exponential constant).
* `tsign` — the co-located `T`-sign certificate against the polynomial budget. -/
structure RootEnclosurePoly (k : Nat) where
  /-- Rational left endpoint. -/
  lo : Q'
  /-- Rational right endpoint. -/
  hi : Q'
  /-- `−1 ≤ lo` (strict-interior left). -/
  hlo1 : (-1 : Q') ≤ lo
  /-- `hi ≤ 1` (strict-interior right). -/
  hhi1 : hi ≤ (1 : Q')
  /-- `lo ≤ hi`. -/
  hle : lo ≤ hi
  /-- `U_{k+1}(lo) ≤ 0` (left sign, the rational-`π` fact). -/
  loSign : Ueval (k + 1) lo ≤ (0 : Q')
  /-- `0 ≤ U_{k+1}(hi)` (right sign, the rational-`π` fact). -/
  hiSign : (0 : Q') ≤ Ueval (k + 1) hi
  /-- **Polynomial** two-sided Lipschitz bound for `T_{k+2}` on `[lo,hi]` with
  constant `(k+2)²`: `|T_{k+2}(b) − T_{k+2}(a)| ≤ (k+2)²·(b−a)`. -/
  lipTpoly : LipBound (Cheb.T (k + 2)) lo hi (Q'.ofNat ((k + 2) ^ 2))
  /-- The co-located `T`-sign certificate against the polynomial budget. -/
  tsign : Cheb.T (k + 2) hi + Q'.ofNat ((k + 2) ^ 2) * (hi + -lo) ≤ (0 : Q')

/-! ## 3. The parallel constructor — polynomial `LipT`, reused `lipU` -/

/-- **The polynomial-`LipT` located bracket.**  From a `RootEnclosurePoly k`, the
four non-trivial fields of `LocatedBracketM (k+1)` are supplied with a POLYNOMIAL
`LipT = ofNat ((k+2)²)`:

* `lipU` — REUSED verbatim from `LocatedBracketGen.lipBound_U_of_QB (k+1)` (the
  exponential `Amaj(k+1)` constant is fine: `LipU` sets only the root-`CReal`
  Cauchy modulus, never the width budget).
* `lipT` — the polynomial `lipTpoly` field.
* `initU` — the `U`-sign bracket from `hle`/`loSign`/`hiSign`.
* `tsign` — the polynomial-budget `T`-sign certificate. -/
def locatedBracketPoly (k : Nat) (e : RootEnclosurePoly k) :
    LocatedNodeDataGen.LocatedBracketM (k + 1) where
  lo := e.lo
  hi := e.hi
  LipU := Q'.ofNat (Amaj (k + 1))
  LipT := Q'.ofNat ((k + 2) ^ 2)
  initU := ⟨e.hle, e.loSign, e.hiSign⟩
  lipU := LocatedBracketGen.lipBound_U_of_QB (k + 1) e.lo e.hi e.hlo1 e.hhi1
  lipT := e.lipTpoly
  tsign := e.tsign

/-- A fully inhabited de Moivre node from the polynomial-budget enclosure (branch
collapse and the `lipU` field already proved), hence general-`M` off-diagonal
OS2 Gram positivity downstream — conditional ONLY on the polynomial-budget
`RootEnclosurePoly` walls. -/
def deMoivreNodePoly (k : Nat) (e : RootEnclosurePoly k) :
    ChebRotationPair.DeMoivreNode (k + 1) :=
  LocatedNodeDataGen.deMoivreNode_of_bracket (k + 1) (locatedBracketPoly k e)

end YMGap.Continuum.RootEnclosureGen

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.RootEnclosureGen.LipBound_mono
#print axioms YMGap.Continuum.RootEnclosureGen.locatedBracketPoly
#print axioms YMGap.Continuum.RootEnclosureGen.deMoivreNodePoly
