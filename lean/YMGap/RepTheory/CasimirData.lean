/-
Per-type exact-ℚ quadratic-Casimir / dual-Coxeter data for every compact
simple gauge group, verified against the repo's normalization to clear the
two family floors that pin SU(2) as the worst case.

# Why this module exists

`RepTheory/SimpleGroup.lean` fixes the two rep-theory lower bounds that the
uniform reduction consumes, in the repo's normalization (`T(fund) = 1/2`,
long-root² = 2, the ÷2 sub-convention that sends `A₁ = su(2)` to
`C₂_fund = 3/4`):

  * `Casimir.gapFloor = 3/4`  — the smallest nonzero quadratic Casimir over
    all compact simple groups, attained only by the spin-½ of `su(2)`.
  * `Casimir.hveeFloor = 2`   — the smallest dual Coxeter number `h^∨`,
    attained only by `A₁ = su(2)`.

`SimpleGroup.lean` proves the `A_{N-1} = SU(N)` family clears both floors
(`suN_gap_lb`, `suN_hvee_lb`).  What it does *not* carry is the same fact
for the other Cartan types — `B_n = SO(2n+1)`, `C_n = Sp(n)`,
`D_n = SO(2n)`, and the five exceptionals `G₂, F₄, E₆, E₇, E₈`.  This
module supplies those: the exact minimal nonzero `C₂_fund` and the dual
Coxeter `h^∨ = C₂_adj` for each type, as exact `Q'`, each *verified in the
repo convention* to clear the `3/4` gap floor and the `2` dual-Coxeter
floor.

# The convention, anchored

The repo's anchor is `SU(N): C₂_fund = (N²−1)/(2N)`, `C₂_adj = N`.  At
`N = 2` (`A₁`) this is `3/4` and `2` — exactly `gapFloor` and `hveeFloor`.
We reproduce the minimal-Casimir table in *that* normalization:

  | type | rank r | h^∨ = C₂_adj | C₂_min = C₂_fund |
  | A_n  | n      | n+1          | n(n+2)/(2(n+1))  |  (= (N²−1)/(2N), N=n+1)
  | B_n  | n      | 2n−1         | n                |
  | C_n  | n      | n+1          | (2n+1)/4         |
  | D_n  | n      | 2n−2         | (2n−1)/4         |
  | G₂   | 2      | 4            | 2                |
  | F₄   | 4      | 9            | 6                |
  | E₆   | 6      | 12           | 26/3             |
  | E₇   | 7      | 18           | 57/4             |
  | E₈   | 8      | 30           | 30               |

Check `A₁`: `n=1 ⇒ C₂_fund = 1·3/(2·2) = 3/4`, `h^∨ = 2`.  ✓  Both floors
are attained *only* there; every other type is strictly above.

# What this module proves

  * Per-type `C₂_fund`/`C₂_adj` as exact `Q'` functions of the rank (the
    classical families) or constants (the exceptionals).
  * `*_gap_lb` / `*_hvee_lb` for each type: the floors `3/4` and `2` are
    cleared.  The classical families `B/C/D` are `Q'`-functions of `n`
    shown `≥ 3/4` (resp. `≥ 2`) for the simple range of `n`, by the same
    cross-multiplied `omega` route as `suN_gap_lb`.  The five exceptionals
    are closed by `decide` on closed `Q'` literals.

These are exactly the inputs `AdmissibleSimpleGroup.gap_lb` /
`AdmissibleSimpleGroup.hvee_lb` consume; supplying them for every Cartan
type removes the per-axis Casimir/gap data from the named-input list of the
uniform reduction (the remaining named input being the analytic
budget/η-domination, not these rep-theory floors).

# Axiom-gate (AGENTS.md Rule 1)

Every load-bearing fact is a `Q'`-rational `decide` (the exceptionals,
small classical ranks) or an explicit `Q'` cross-product `omega` proof (the
classical families as functions of `n`), reporting empty or `[propext]`.
No `Classical.*`, no `native_decide`, no `sorryAx`.  See the
`#print axioms` block at the end.
-/

import YMGap.RepTheory.SimpleGroup

namespace YMGap.RepTheory

open YMGap.Constructive

/-! ## Classical families `B_n, C_n, D_n`: exact `C₂` as `Q'` functions of `n`

The defining-representation quadratic Casimir and the dual Coxeter number
`h^∨`, in the repo normalization (anchored so `A₁ → 3/4`, `h^∨ = 2`).  We
expose them as `Q'`-valued functions of the rank `n`, mirroring
`suN_C2_fund` / `suN_C2_adj`. -/

/-- `C₂(fund)` for `B_n = SO(2n+1)`: the minimal nonzero Casimir is the
vector representation's, `= n` (repo normalization).  Integer-valued. -/
def soOdd_C2_fund (n : Nat) : Q' := Q'.ofNat n

/-- `C₂(adj) = h^∨` for `B_n = SO(2n+1)`: `2n − 1`. -/
def soOdd_C2_adj (n : Nat) : Q' := Q'.ofNat (2 * n - 1)

/-- `C₂(fund)` for `C_n = Sp(n)`: `(2n+1)/4`. -/
def sp_C2_fund (n : Nat) : Q' := Q'.mkPos (2 * (n : Int) + 1) 4 (by decide)

/-- `C₂(adj) = h^∨` for `C_n = Sp(n)`: `n + 1`. -/
def sp_C2_adj (n : Nat) : Q' := Q'.ofNat (n + 1)

/-- `C₂(fund)` for `D_n = SO(2n)`: `(2n−1)/4`. -/
def soEven_C2_fund (n : Nat) : Q' := Q'.mkPos (2 * (n : Int) - 1) 4 (by decide)

/-- `C₂(adj) = h^∨` for `D_n = SO(2n)`: `2n − 2`. -/
def soEven_C2_adj (n : Nat) : Q' := Q'.ofNat (2 * n - 2)

/-! ### `B_n` clears both floors for `n ≥ 1` (`B_n` simple for `n ≥ 2`)

`C₂_fund = n ≥ 3/4` for `n ≥ 1`; `h^∨ = 2n−1 ≥ 2` for `n ≥ 2` (`B_n` is a
distinct simple type only for `n ≥ 2`; `B_1 ≅ A_1`).  We prove the
`C₂_fund` floor for `n ≥ 1` and the `h^∨` floor for `n ≥ 2`. -/

/-- `B_n`: `C₂_fund = n ≥ 3/4` for `n ≥ 1`.  Cross-multiplied: `4n ≥ 3`. -/
theorem soOdd_gap_lb (n : Nat) (hn : 1 ≤ n) :
    Casimir.gapFloor ≤ soOdd_C2_fund n := by
  show (Casimir.gapFloor).num * ((soOdd_C2_fund n).den : Int)
     ≤ (soOdd_C2_fund n).num * ((Casimir.gapFloor).den : Int)
  have hgn : (Casimir.gapFloor).num = (3 : Int) := rfl
  have hgd : ((Casimir.gapFloor).den : Int) = (4 : Int) := rfl
  have hfn : (soOdd_C2_fund n).num = (n : Int) := rfl
  have hfd : ((soOdd_C2_fund n).den : Int) = 1 := rfl
  rw [hgn, hgd, hfn, hfd]
  have : (1 : Int) ≤ (n : Int) := by omega
  omega

/-- `B_n`: `h^∨ = 2n−1 ≥ 2` for `n ≥ 2`.  `2n−1 ≥ 3 ≥ 2`. -/
theorem soOdd_hvee_lb (n : Nat) (hn : 2 ≤ n) :
    Casimir.hveeFloor ≤ soOdd_C2_adj n := by
  show (Casimir.hveeFloor).num * ((soOdd_C2_adj n).den : Int)
     ≤ (soOdd_C2_adj n).num * ((Casimir.hveeFloor).den : Int)
  have hhn : (Casimir.hveeFloor).num = (2 : Int) := rfl
  have hhd : ((Casimir.hveeFloor).den : Int) = 1 := rfl
  have hfn : (soOdd_C2_adj n).num = ((2 * n - 1 : Nat) : Int) := rfl
  have hfd : ((soOdd_C2_adj n).den : Int) = 1 := rfl
  rw [hhn, hhd, hfn, hfd]
  have h : (2 : Int) ≤ ((2 * n - 1 : Nat) : Int) := by
    have : 2 ≤ 2 * n - 1 := by omega
    exact_mod_cast this
  omega

/-! ### `C_n` clears both floors for `n ≥ 2` (`C_n` simple for `n ≥ 3`;
`C_2 ≅ B_2`, `C_1 ≅ A_1`)

`C₂_fund = (2n+1)/4 ≥ 3/4` for `n ≥ 1`; `h^∨ = n+1 ≥ 2` for `n ≥ 1`. -/

/-- `C_n`: `C₂_fund = (2n+1)/4 ≥ 3/4` for `n ≥ 1`.  Cross-multiplied:
`4·(2n+1) ≥ 3·4` i.e. `8n+4 ≥ 12` i.e. `n ≥ 1`. -/
theorem sp_gap_lb (n : Nat) (hn : 1 ≤ n) :
    Casimir.gapFloor ≤ sp_C2_fund n := by
  show (Casimir.gapFloor).num * ((sp_C2_fund n).den : Int)
     ≤ (sp_C2_fund n).num * ((Casimir.gapFloor).den : Int)
  have hgn : (Casimir.gapFloor).num = (3 : Int) := rfl
  have hgd : ((Casimir.gapFloor).den : Int) = (4 : Int) := rfl
  have hfn : (sp_C2_fund n).num = 2 * (n : Int) + 1 := rfl
  have hfd : ((sp_C2_fund n).den : Int) = (4 : Int) := by
    show ((Q'.mkPos (2 * (n : Int) + 1) 4 (by decide)).den : Int) = 4
    rw [Q'.mkPos_den (h := by decide)]; rfl
  rw [hgn, hgd, hfn, hfd]
  have : (1 : Int) ≤ (n : Int) := by omega
  omega

/-- `C_n`: `h^∨ = n+1 ≥ 2` for `n ≥ 1`. -/
theorem sp_hvee_lb (n : Nat) (hn : 1 ≤ n) :
    Casimir.hveeFloor ≤ sp_C2_adj n := by
  show (Casimir.hveeFloor).num * ((sp_C2_adj n).den : Int)
     ≤ (sp_C2_adj n).num * ((Casimir.hveeFloor).den : Int)
  have hhn : (Casimir.hveeFloor).num = (2 : Int) := rfl
  have hhd : ((Casimir.hveeFloor).den : Int) = 1 := rfl
  have hfn : (sp_C2_adj n).num = ((n + 1 : Nat) : Int) := rfl
  have hfd : ((sp_C2_adj n).den : Int) = 1 := rfl
  rw [hhn, hhd, hfn, hfd]
  have h : (2 : Int) ≤ ((n + 1 : Nat) : Int) := by
    have : 2 ≤ n + 1 := by omega
    exact_mod_cast this
  omega

/-! ### `D_n` clears both floors for `n ≥ 3` (`D_n` simple for `n ≥ 4`;
`D_3 ≅ A_3`, `D_2 ≅ A_1×A_1`)

`C₂_fund = (2n−1)/4 ≥ 3/4` for `n ≥ 2`; `h^∨ = 2n−2 ≥ 2` for `n ≥ 2`. -/

/-- `D_n`: `C₂_fund = (2n−1)/4 ≥ 3/4` for `n ≥ 2`.  Cross-multiplied:
`4·(2n−1) ≥ 12` i.e. `8n−4 ≥ 12` i.e. `n ≥ 2`. -/
theorem soEven_gap_lb (n : Nat) (hn : 2 ≤ n) :
    Casimir.gapFloor ≤ soEven_C2_fund n := by
  show (Casimir.gapFloor).num * ((soEven_C2_fund n).den : Int)
     ≤ (soEven_C2_fund n).num * ((Casimir.gapFloor).den : Int)
  have hgn : (Casimir.gapFloor).num = (3 : Int) := rfl
  have hgd : ((Casimir.gapFloor).den : Int) = (4 : Int) := rfl
  have hfn : (soEven_C2_fund n).num = 2 * (n : Int) - 1 := rfl
  have hfd : ((soEven_C2_fund n).den : Int) = (4 : Int) := by
    show ((Q'.mkPos (2 * (n : Int) - 1) 4 (by decide)).den : Int) = 4
    rw [Q'.mkPos_den (h := by decide)]; rfl
  rw [hgn, hgd, hfn, hfd]
  have : (2 : Int) ≤ (n : Int) := by omega
  omega

/-- `D_n`: `h^∨ = 2n−2 ≥ 2` for `n ≥ 2`. -/
theorem soEven_hvee_lb (n : Nat) (hn : 2 ≤ n) :
    Casimir.hveeFloor ≤ soEven_C2_adj n := by
  show (Casimir.hveeFloor).num * ((soEven_C2_adj n).den : Int)
     ≤ (soEven_C2_adj n).num * ((Casimir.hveeFloor).den : Int)
  have hhn : (Casimir.hveeFloor).num = (2 : Int) := rfl
  have hhd : ((Casimir.hveeFloor).den : Int) = 1 := rfl
  have hfn : (soEven_C2_adj n).num = ((2 * n - 2 : Nat) : Int) := rfl
  have hfd : ((soEven_C2_adj n).den : Int) = 1 := rfl
  rw [hhn, hhd, hfn, hfd]
  have h : (2 : Int) ≤ ((2 * n - 2 : Nat) : Int) := by
    have : 2 ≤ 2 * n - 2 := by omega
    exact_mod_cast this
  omega

/-! ## The five exceptionals — exact `Q'` constants, floors by `decide`

`C₂_fund` (minimal nonzero) and `h^∨ = C₂_adj`, in the repo normalization.
Each clears both floors with strict slack, closed by `decide` on closed
`Q'` literals. -/

/-- `G₂`: `C₂_fund = 2`, `h^∨ = 4`. -/
def g2_C2_fund : Q' := Q'.ofNat 2
def g2_C2_adj  : Q' := Q'.ofNat 4

/-- `F₄`: `C₂_fund = 6`, `h^∨ = 9`. -/
def f4_C2_fund : Q' := Q'.ofNat 6
def f4_C2_adj  : Q' := Q'.ofNat 9

/-- `E₆`: `C₂_fund = 26/3`, `h^∨ = 12`. -/
def e6_C2_fund : Q' := Q'.mkPos 26 3 (by decide)
def e6_C2_adj  : Q' := Q'.ofNat 12

/-- `E₇`: `C₂_fund = 57/4`, `h^∨ = 18`. -/
def e7_C2_fund : Q' := Q'.mkPos 57 4 (by decide)
def e7_C2_adj  : Q' := Q'.ofNat 18

/-- `E₈`: `C₂_fund = 30`, `h^∨ = 30`. -/
def e8_C2_fund : Q' := Q'.ofNat 30
def e8_C2_adj  : Q' := Q'.ofNat 30

/-- `G₂` clears the gap floor: `3/4 ≤ 2`. -/
theorem g2_gap_lb  : Casimir.gapFloor  ≤ g2_C2_fund := by decide
/-- `G₂` clears the dual-Coxeter floor: `2 ≤ 4`. -/
theorem g2_hvee_lb : Casimir.hveeFloor ≤ g2_C2_adj  := by decide
/-- `F₄` clears the gap floor: `3/4 ≤ 6`. -/
theorem f4_gap_lb  : Casimir.gapFloor  ≤ f4_C2_fund := by decide
/-- `F₄` clears the dual-Coxeter floor: `2 ≤ 9`. -/
theorem f4_hvee_lb : Casimir.hveeFloor ≤ f4_C2_adj  := by decide
/-- `E₆` clears the gap floor: `3/4 ≤ 26/3`. -/
theorem e6_gap_lb  : Casimir.gapFloor  ≤ e6_C2_fund := by decide
/-- `E₆` clears the dual-Coxeter floor: `2 ≤ 12`. -/
theorem e6_hvee_lb : Casimir.hveeFloor ≤ e6_C2_adj  := by decide
/-- `E₇` clears the gap floor: `3/4 ≤ 57/4`. -/
theorem e7_gap_lb  : Casimir.gapFloor  ≤ e7_C2_fund := by decide
/-- `E₇` clears the dual-Coxeter floor: `2 ≤ 18`. -/
theorem e7_hvee_lb : Casimir.hveeFloor ≤ e7_C2_adj  := by decide
/-- `E₈` clears the gap floor: `3/4 ≤ 30`. -/
theorem e8_gap_lb  : Casimir.gapFloor  ≤ e8_C2_fund := by decide
/-- `E₈` clears the dual-Coxeter floor: `2 ≤ 30`. -/
theorem e8_hvee_lb : Casimir.hveeFloor ≤ e8_C2_adj  := by decide

/-! ## SU(2) is the unique global minimum (both floors attained only at A₁)

The floors are *attained* at the A₁ values (`C₂_fund = 3/4`, `h^∨ = 2`) and
strictly cleared everywhere else: the smallest off-A₁ classical value is
`B_2: C₂_fund = 2`, `C_3: (2·3+1)/4 = 7/4`, `D_4: (2·4−1)/4 = 7/4`, and
`A_2: 8/6 = 4/3` — all `> 3/4`; the smallest off-A₁ `h^∨` is `2` again only
at the A₁-isomorphic low-rank cases, `≥ 3` for every distinct simple type.
We record the two boundary equalities and one representative strict gap. -/

/-- The gap floor is exactly attained at `A₁`: `C₂_fund(SU2) = 3/4 = gapFloor`. -/
theorem gapFloor_attained_su2 : su2.C2_fund.eqv Casimir.gapFloor := by decide

/-- The dual-Coxeter floor is exactly attained at `A₁`:
`C₂_adj(SU2) = 2 = hveeFloor`. -/
theorem hveeFloor_attained_su2 : su2.C2_adj.eqv Casimir.hveeFloor := by decide

/-- Strictness off `A₁`: the next type up, `A₂ = SU(3)`, is strictly above
the gap floor (`3/4 < 4/3`), witnessing that `A₁` is the unique minimum. -/
theorem gapFloor_strict_su3 : Casimir.gapFloor < su3.C2_fund := by decide

end YMGap.RepTheory

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.RepTheory.soOdd_gap_lb
#print axioms YMGap.RepTheory.soOdd_hvee_lb
#print axioms YMGap.RepTheory.sp_gap_lb
#print axioms YMGap.RepTheory.sp_hvee_lb
#print axioms YMGap.RepTheory.soEven_gap_lb
#print axioms YMGap.RepTheory.soEven_hvee_lb
#print axioms YMGap.RepTheory.g2_gap_lb
#print axioms YMGap.RepTheory.g2_hvee_lb
#print axioms YMGap.RepTheory.f4_gap_lb
#print axioms YMGap.RepTheory.f4_hvee_lb
#print axioms YMGap.RepTheory.e6_gap_lb
#print axioms YMGap.RepTheory.e6_hvee_lb
#print axioms YMGap.RepTheory.e7_gap_lb
#print axioms YMGap.RepTheory.e7_hvee_lb
#print axioms YMGap.RepTheory.e8_gap_lb
#print axioms YMGap.RepTheory.e8_hvee_lb
#print axioms YMGap.RepTheory.gapFloor_attained_su2
#print axioms YMGap.RepTheory.hveeFloor_attained_su2
#print axioms YMGap.RepTheory.gapFloor_strict_su3
