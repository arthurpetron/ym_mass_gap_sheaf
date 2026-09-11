/-
Legacy per-type rational scalar data used to clear two budget floors.

# Why this module exists

`RepTheory/SimpleGroup.lean` asks only for the inequalities
`3/4 ≤ C2_fund` and `2 ≤ C2_adj` on legacy `RepData` scalars.  This module
supplies rational literals and proves those inequalities.  It does **not**
derive a least nonzero Casimir from a root datum, impose a global-form descent
condition, or relate the stored scalar to a realized representation.

# The convention, anchored

The repo's anchor is `SU(N): C₂_fund = (N²−1)/(2N)`, `C₂_adj = N`.  At
`N = 2` (`A₁`) this is `3/4` and `2`.  The legacy scalar table currently
stored here is:

  | type | rank r | stored `C₂_adj` | stored `C₂_fund` |
  | A_n  | n      | n+1          | n(n+2)/(2(n+1))  |  (= (N²−1)/(2N), N=n+1)
  | B_n  | n      | 2n−1         | n                |
  | C_n  | n      | n+1          | (2n+1)/4         |
  | D_n  | n      | 2n−2         | (2n−1)/4         |
  | G₂   | 2      | 4            | 2                |
  | F₄   | 4      | 9            | 6                |
  | E₆   | 6      | 12           | 26/3             |
  | E₇   | 7      | 18           | 57/4             |
  | E₈   | 8      | 30           | 30               |

These rows must not be read as a global minimum table.  Cover representations
can be rejected by a quotient.  For simply connected `B₂` and `B₃`, the
spinor Casimir `n(2n+1)/8` is smaller than the vector value `n`.  In type
`D_n`, the vector and half-spin values in the stated long-root-square-two
normalization are `(2n-1)/2` and `n(2n-1)/8`; the stored `(2n-1)/4` is therefore
neither claimed value and is retained only as a legacy floor-clearing scalar.

# What this module proves

  * Per-type legacy `C₂_fund`/`C₂_adj` literals as exact `Q'` functions of the
    rank (the classical families) or constants (the exceptionals).
  * `*_gap_lb` / `*_hvee_lb` for each type: the floors `3/4` and `2` are
    cleared.  The classical families `B/C/D` are `Q'`-functions of `n`
    shown `≥ 3/4` (resp. `≥ 2`) for the simple range of `n`, by the same
    cross-multiplied `omega` route as `suN_gap_lb`.  The five exceptionals
    are closed by `decide` on closed `Q'` literals.

These are exactly the numeric inequalities consumed by
`AdmissibleSimpleGroup.gap_lb` / `AdmissibleSimpleGroup.hvee_lb`.  They do not
remove the representation-theoretic obligation: the future constructive
`P/Q`, central-character, normalized-root-metric, and highest-weight minimum
layers must supply provenance and the actual global-form spectral pin.

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

/-! ## Classical-family legacy scalars as `Q'` functions of `n`

These historical names mirror `suN_C2_fund` / `suN_C2_adj`.  Only their exact
rational values and the proved floor inequalities are load-bearing here; no
minimum or global-form semantics is attached by this module. -/

/-- Legacy `B_n` vector scalar, `n`.  It need not be the simply connected
spectral minimum at low rank and need not descend to every global form. -/
def soOdd_C2_fund (n : Nat) : Q' := Q'.ofNat n

/-- `C₂(adj) = h^∨` for `B_n = SO(2n+1)`: `2n − 1`. -/
def soOdd_C2_adj (n : Nat) : Q' := Q'.ofNat (2 * n - 1)

/-- `C₂(fund)` for `C_n = Sp(n)`: `(2n+1)/4`. -/
def sp_C2_fund (n : Nat) : Q' := Q'.mkPos (2 * (n : Int) + 1) 4 (by decide)

/-- `C₂(adj) = h^∨` for `C_n = Sp(n)`: `n + 1`. -/
def sp_C2_adj (n : Nat) : Q' := Q'.ofNat (n + 1)

/-- Legacy `D_n` floor-clearing scalar `(2n−1)/4`.  This is not the vector or
half-spin Casimir in the stated long-root-square-two normalization. -/
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

/-! ## Five exceptional-type legacy constants, floors by `decide`

Each stored literal clears the relevant floor, closed by `decide` on exact
`Q'` data.  Actual global-form minima still require the highest-weight and
central-character calculation. -/

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

/-! ## Scalar boundary checks at SU(2)

We record two A₁ equalities and the single comparison `3/4 < 4/3` for the
stored A₂ scalar.  These three facts do not prove uniqueness of a minimum over
all Cartan types or global forms. -/

/-- The gap floor is exactly attained at `A₁`: `C₂_fund(SU2) = 3/4 = gapFloor`. -/
theorem gapFloor_attained_su2 : su2.C2_fund.eqv Casimir.gapFloor := by decide

/-- The dual-Coxeter floor is exactly attained at `A₁`:
`C₂_adj(SU2) = 2 = hveeFloor`. -/
theorem hveeFloor_attained_su2 : su2.C2_adj.eqv Casimir.hveeFloor := by decide

/-- The stored `A₂ = SU(3)` scalar is strictly above the floor:
`3/4 < 4/3`. -/
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
