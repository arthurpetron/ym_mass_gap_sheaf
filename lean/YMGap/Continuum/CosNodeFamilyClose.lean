/-
# Closing the general-`M` off-diagonal OS2 walls for a WIDE explicit family
# (`CosNodeFamilyClose`) — and reducing the uniform-`k` case to ONE named bridge

`DDIdentity.deMoivreNode_of` reduced general-`M` off-diagonal OS2 Gram positivity
to the three rational-`π` walls at the Gauss–Chebyshev node
`x⋆ = cos(π/(k+2))` (the largest root of the second-kind Chebyshev `U_{k+1}`):

  * `loSign : U_{k+1}(lo) ≤ 0`,
  * `hiSign : 0 ≤ U_{k+1}(hi)`,
  * `tsign  : T_{k+2}(hi) + (k+2)²·(hi − lo) ≤ 0`,

together with the interval bounds `−1 ≤ lo ≤ hi ≤ 1`.  The whole DD/Markov side
(`ddId`, the `(k+2)²` divided-difference budget) is already PROVED upstream, so
these three sign facts are the SOLE residual.

## What is CLOSED here (axiom-clean, `decide`-discharged)

For every order in the explicit family `M = 1,…,16` (`k = 0,…,15`) a two-sided
rational bracket `[lo,hi] ∋ cos(π/(k+2))` (denominators `≤ 500`) is exhibited and
ALL THREE walls are discharged by `decide` on the closed `Q'` polynomial values
(`Ueval`/`T` are the recurrence-defined Chebyshev evaluations; `decide` on their
rational values is exactly the small-order pattern of `ChebRoot.ueval2_lo`).

  * `deMoivreNodeM1 … deMoivreNodeM16 : ChebRotationPair.DeMoivreNode M` — each a
    FULLY INHABITED de Moivre rotation node (`U_M(x⋆) ≈ 0`, `T_{M+1}(x⋆) ≈ −1`,
    located `CReal` node `x⋆` built by the upstream bisection from the bracket),
    hence general-`M` off-diagonal OS2 Gram positivity at each of these `M`.

Because the sign of `U_{k+1}` / `T_{k+2}` at a *fixed* rational point is a finite
`Q'` computation, the family is closed unconditionally.  What it is NOT is uniform
in `k`.

## The honest general-`k` residual (NOT faked)

The bracket signs `loSign`/`hiSign` say the rational `lo,hi` straddle the largest
`U_{k+1}`-root with the correct polynomial signs.  Making this UNIFORM in `k`
requires the de Moivre sign bridge

    U_{k+1}(cos θ) = sin((k+2)θ) / sin θ ,   T_{k+2}(cos θ) = cos((k+2)θ),

i.e. locating `x⋆ = cos(π/(k+2))` by rational bounds on `π` (available coarsely
as `3 ≤ π ≤ 4` from `Pi.pi`) and reading the sign of `sin((k+2)θ)` across the
node.  That sine-at-a-rational-multiple-of-`π` sign fact is exactly the residual
already named in the `cosC`/`sinC` development (the `sinC(k·π) ≃ 0` bridge): the
`cosC` primitive supplies the node *value* but not the polynomial *sign*, which is
the sine bridge.  The general-`k` walls are therefore reduced to that SINGLE named
monotonicity/sign lemma; they are not discharged here for arbitrary `k`.

## Axiom gate (AGENTS.md Rule 1 / Rule 8)

`[propext]` / `[propext, Quot.sound]` only.  No `Classical.*`, no
`sorry`/`sorryAx`, no `native_decide`, no custom axiom.  `decide` is used only on
closed `Q'` (in)equalities (the bracket sign checks).  `DeMoivreNode` is a
`Type`-level record (witnesses as data, not `Prop`-∃).
-/

import YMGap.Continuum.DDIdentity

namespace YMGap.Continuum.CosNodeFamilyClose

open YMGap.Constructive
open YMGap.Continuum

/-! ## The explicit rational brackets (denominators `≤ 100`)

Each `[lo,hi]` two-sidedly encloses `cos(π/(k+2))`; the three walls are checked by
`decide` inside the node constructors below.  For `k = 0,1` the node is rational
(`cos(π/2)=0`, `cos(π/3)=1/2`) so `lo = hi`; for `k ≥ 2` a genuine two-sided
bracket is needed. -/

/-- `M = 1` (`k = 0`): node `cos(π/2) = 0`. -/
def deMoivreNodeM1 : ChebRotationPair.DeMoivreNode 1 :=
  DDIdentity.deMoivreNode_of 0 (0 : Q') (0 : Q')
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- `M = 2` (`k = 1`): node `cos(π/3) = 1/2`. -/
def deMoivreNodeM2 : ChebRotationPair.DeMoivreNode 2 :=
  DDIdentity.deMoivreNode_of 1 (Q'.mkPos 1 2 (by decide)) (Q'.mkPos 1 2 (by decide))
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- `M = 3` (`k = 2`): bracket `[70/100, 71/100] ∋ cos(π/4)`. -/
def deMoivreNodeM3 : ChebRotationPair.DeMoivreNode 3 :=
  DDIdentity.deMoivreNode_of 2 (Q'.mkPos 70 100 (by decide)) (Q'.mkPos 71 100 (by decide))
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- `M = 4` (`k = 3`): bracket `[80/100, 81/100] ∋ cos(π/5)`. -/
def deMoivreNodeM4 : ChebRotationPair.DeMoivreNode 4 :=
  DDIdentity.deMoivreNode_of 3 (Q'.mkPos 80 100 (by decide)) (Q'.mkPos 81 100 (by decide))
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- `M = 5` (`k = 4`): bracket `[86/100, 87/100] ∋ cos(π/6)`. -/
def deMoivreNodeM5 : ChebRotationPair.DeMoivreNode 5 :=
  DDIdentity.deMoivreNode_of 4 (Q'.mkPos 86 100 (by decide)) (Q'.mkPos 87 100 (by decide))
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- `M = 6` (`k = 5`): bracket `[90/100, 91/100] ∋ cos(π/7)`. -/
def deMoivreNodeM6 : ChebRotationPair.DeMoivreNode 6 :=
  DDIdentity.deMoivreNode_of 5 (Q'.mkPos 90 100 (by decide)) (Q'.mkPos 91 100 (by decide))
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- `M = 7` (`k = 6`): bracket `[92/100, 93/100] ∋ cos(π/8)`. -/
def deMoivreNodeM7 : ChebRotationPair.DeMoivreNode 7 :=
  DDIdentity.deMoivreNode_of 6 (Q'.mkPos 92 100 (by decide)) (Q'.mkPos 93 100 (by decide))
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- `M = 8` (`k = 7`): bracket `[93/100, 94/100] ∋ cos(π/9)`. -/
def deMoivreNodeM8 : ChebRotationPair.DeMoivreNode 8 :=
  DDIdentity.deMoivreNode_of 7 (Q'.mkPos 93 100 (by decide)) (Q'.mkPos 94 100 (by decide))
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- `M = 9` (`k = 8`): bracket `[190/200, 191/200] ∋ cos(π/10)`. -/
def deMoivreNodeM9 : ChebRotationPair.DeMoivreNode 9 :=
  DDIdentity.deMoivreNode_of 8 (Q'.mkPos 190 200 (by decide)) (Q'.mkPos 191 200 (by decide))
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- `M = 10` (`k = 9`): bracket `[191/200, 192/200] ∋ cos(π/11)`. -/
def deMoivreNodeM10 : ChebRotationPair.DeMoivreNode 10 :=
  DDIdentity.deMoivreNode_of 9 (Q'.mkPos 191 200 (by decide)) (Q'.mkPos 192 200 (by decide))
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- `M = 11` (`k = 10`): bracket `[193/200, 194/200] ∋ cos(π/12)`. -/
def deMoivreNodeM11 : ChebRotationPair.DeMoivreNode 11 :=
  DDIdentity.deMoivreNode_of 10 (Q'.mkPos 193 200 (by decide)) (Q'.mkPos 194 200 (by decide))
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- `M = 12` (`k = 11`): bracket `[194/200, 195/200] ∋ cos(π/13)`. -/
def deMoivreNodeM12 : ChebRotationPair.DeMoivreNode 12 :=
  DDIdentity.deMoivreNode_of 11 (Q'.mkPos 194 200 (by decide)) (Q'.mkPos 195 200 (by decide))
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- `M = 13` (`k = 12`): bracket `[194/200, 195/200] ∋ cos(π/14)`. -/
def deMoivreNodeM13 : ChebRotationPair.DeMoivreNode 13 :=
  DDIdentity.deMoivreNode_of 12 (Q'.mkPos 194 200 (by decide)) (Q'.mkPos 195 200 (by decide))
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- `M = 14` (`k = 13`): bracket `[489/500, 490/500] ∋ cos(π/15)`. -/
def deMoivreNodeM14 : ChebRotationPair.DeMoivreNode 14 :=
  DDIdentity.deMoivreNode_of 13 (Q'.mkPos 489 500 (by decide)) (Q'.mkPos 490 500 (by decide))
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- `M = 15` (`k = 14`): bracket `[490/500, 491/500] ∋ cos(π/16)`. -/
def deMoivreNodeM15 : ChebRotationPair.DeMoivreNode 15 :=
  DDIdentity.deMoivreNode_of 14 (Q'.mkPos 490 500 (by decide)) (Q'.mkPos 491 500 (by decide))
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- `M = 16` (`k = 15`): bracket `[491/500, 492/500] ∋ cos(π/17)`. -/
def deMoivreNodeM16 : ChebRotationPair.DeMoivreNode 16 :=
  DDIdentity.deMoivreNode_of 15 (Q'.mkPos 491 500 (by decide)) (Q'.mkPos 492 500 (by decide))
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

end YMGap.Continuum.CosNodeFamilyClose

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.CosNodeFamilyClose.deMoivreNodeM1
#print axioms YMGap.Continuum.CosNodeFamilyClose.deMoivreNodeM2
#print axioms YMGap.Continuum.CosNodeFamilyClose.deMoivreNodeM3
#print axioms YMGap.Continuum.CosNodeFamilyClose.deMoivreNodeM4
#print axioms YMGap.Continuum.CosNodeFamilyClose.deMoivreNodeM5
#print axioms YMGap.Continuum.CosNodeFamilyClose.deMoivreNodeM6
#print axioms YMGap.Continuum.CosNodeFamilyClose.deMoivreNodeM7
#print axioms YMGap.Continuum.CosNodeFamilyClose.deMoivreNodeM8
#print axioms YMGap.Continuum.CosNodeFamilyClose.deMoivreNodeM9
#print axioms YMGap.Continuum.CosNodeFamilyClose.deMoivreNodeM10
#print axioms YMGap.Continuum.CosNodeFamilyClose.deMoivreNodeM11
#print axioms YMGap.Continuum.CosNodeFamilyClose.deMoivreNodeM12
#print axioms YMGap.Continuum.CosNodeFamilyClose.deMoivreNodeM13
#print axioms YMGap.Continuum.CosNodeFamilyClose.deMoivreNodeM14
#print axioms YMGap.Continuum.CosNodeFamilyClose.deMoivreNodeM15
#print axioms YMGap.Continuum.CosNodeFamilyClose.deMoivreNodeM16
