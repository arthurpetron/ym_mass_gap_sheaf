/-
Rank- and family-code-general crude squared-Weyl-dimension `WeylDimData`,
instantiated for every raw `CartanType` code by one generic crude engine.

# What this module supplies (and what stays a NAMED residual)

`RG/WeylDimGeneral.lean` proves the generic crude engine once — a bare finite
product of `m` factors each in `[0, B]` with `1 ≤ B` is `≤ B^m`
(`prodFac_le_pow`), hence the squared-dimension majorant `dimVal² ≤ B^{2m}`
(`dimSq_le_crude`), packaged as `weylDimData_crude`.  It then instantiated the
type-A family (`suN_weylDimData_crude`) with `m = #Δ⁺(A_{N−1}) = N(N−1)/2`.

This module carries the arithmetic formula called `numPosRoots` on every raw
Cartan code and packages the crude `WeylDimData` from it.  On a code satisfying
`IsCanonicalSimpleCode`, this is the corresponding positive-root count; on
invalid raw values such as `A 0` it is only the same total `Nat` formula.  The
crude route is **convention-blind**: it needs only that number, never root
lengths, so the non-simply-laced families `B_n, C_n, G₂, F₄` need no special
treatment here (the short/long-root convention enters elsewhere).

  * `CartanType` — raw Dynkin-family/rank codes; classical constructors accept
    every `Nat`.
  * `IsCanonicalSimpleCode` — the preferred validation/nonredundancy predicate;
    `IsSimpleRank` is retained only as its legacy compatibility alias.
  * `CartanType.rank` — the Lie rank `r` (number of Cartan axes).
  * `CartanType.numPosRoots` — `#Δ⁺` per type
    (A_n: n(n+1)/2, B_n/C_n: n², D_n: n(n−1), G₂:6, F₄:24, E₆:36, E₇:63, E₈:120).
  * `numPosRoots_*_le` — the crude cardinality bounds (`Nat`, no per-axis
    identity), mirroring `suN_numPosRoots_le`.
  * `cartanType_weylDimData_crude` — the type-general crude `WeylDimData R` at
    `m := numPosRoots T`, `B := crudeBound lab (rank T)`, plus thin per-type
    aliases (`weylDimData_A`, `_B`, `_C`, `_D`, `_G2`, `_F4`, `_E6`, `_E7`,
    `_E8`).

The **honest residual** stays exactly the same as the existing SU(N) boundary:
the abstract Weyl-dimension product `dimVal ≤ ∏_{j<m} fac j` over the `m`
positive roots, with each Weyl factor `fac j ≤ B` under the crude bound, is
supplied as HYPOTHESES (the group-specific Weyl dimension formula this `Q'`
stack does not carry), never faked.  The squared majorization itself is proven.

# Axiom-gate (AGENTS.md Rule 1)

Every load-bearing fact reports `[propext]` / `[propext, Quot.sound]` (the
`Q'`/`Nat` order layer).  No `Classical.*`, no `native_decide`, no `sorryAx`,
no custom axiom.  See the `#print axioms` block at the end.
-/

import YMGap.RepTheory.CartanType
import YMGap.RG.WeylDimGeneral

namespace YMGap.RG

open YMGap.Constructive
open YMGap.RepTheory

/-! ## The raw Cartan-family classification input

`CartanType`, `CartanType.rank`, and `CartanType.numPosRoots` now come from the
cycle-free `RepTheory/CartanType.lean` leaf.  They retain their original
`YMGap.RG` names.  The classical families remain parametric in `n`, including
invalid and noncanonical low-rank codes.  Use `IsCanonicalSimpleCode` before
reading a value as the repository's nonredundant simple classification;
`IsSimpleRank` is the historical alias, not a literal simplicity test.

These declarations classify Lie algebras/root systems only.  They do not
select a simply connected compact group, adjoint group, or intermediate
finite central quotient.  This RG module consumes only the positive-root
count and rank. -/

/-! ## Crude cardinality bounds `#Δ⁺ ≤ (r+1)²` (classical) / exact (exceptional)

The only counting facts the uniform crude route uses.  Pure `Nat`, no per-axis
`p(N−p)` identity — a positive-root count is dominated by a clean quadratic in
the rank (classical) or its exact literal (exceptional). -/

/-- `A_n`: `#Δ⁺ = n(n+1)/2 ≤ (n+1)²`  (`div_le_self`, then `n(n+1) ≤ (n+1)²`).
Mirrors `suN_numPosRoots_le` with `N = n+1`. -/
theorem numPosRoots_A_le (n : Nat) :
    CartanType.numPosRoots (.A n) ≤ (n + 1) * (n + 1) := by
  show n * (n + 1) / 2 ≤ (n + 1) * (n + 1)
  have h1 : n * (n + 1) ≤ (n + 1) * (n + 1) := Nat.mul_le_mul_right (n + 1) (by omega)
  exact Nat.le_trans (Nat.div_le_self _ 2) h1

/-- `B_n`: `#Δ⁺ = n² ≤ (n+1)²`. -/
theorem numPosRoots_B_le (n : Nat) :
    CartanType.numPosRoots (.B n) ≤ (n + 1) * (n + 1) := by
  show n * n ≤ (n + 1) * (n + 1)
  exact Nat.mul_le_mul (by omega) (by omega)

/-- `C_n`: `#Δ⁺ = n² ≤ (n+1)²`. -/
theorem numPosRoots_C_le (n : Nat) :
    CartanType.numPosRoots (.C n) ≤ (n + 1) * (n + 1) := by
  show n * n ≤ (n + 1) * (n + 1)
  exact Nat.mul_le_mul (by omega) (by omega)

/-- `D_n`: `#Δ⁺ = n(n−1) ≤ (n+1)²`. -/
theorem numPosRoots_D_le (n : Nat) :
    CartanType.numPosRoots (.D n) ≤ (n + 1) * (n + 1) := by
  show n * (n - 1) ≤ (n + 1) * (n + 1)
  exact Nat.mul_le_mul (by omega) (by omega)

/-- The five exceptionals: exact positive-root counts (`6, 24, 36, 63, 120`),
each `≤ 120`.  Recorded as the crude cardinality datum for the exceptionals. -/
theorem numPosRoots_G2 : CartanType.numPosRoots .G2 = 6 := rfl
theorem numPosRoots_F4 : CartanType.numPosRoots .F4 = 24 := rfl
theorem numPosRoots_E6 : CartanType.numPosRoots .E6 = 36 := rfl
theorem numPosRoots_E7 : CartanType.numPosRoots .E7 = 63 := rfl
theorem numPosRoots_E8 : CartanType.numPosRoots .E8 = 120 := rfl

/-- All five exceptional counts are `≤ 120` (the crude cardinality cap for the
exceptional block). -/
theorem numPosRoots_exceptional_le :
    ∀ T : CartanType, (T = .G2 ∨ T = .F4 ∨ T = .E6 ∨ T = .E7 ∨ T = .E8) →
      CartanType.numPosRoots T ≤ 120 := by
  intro T hT
  rcases hT with h | h | h | h | h <;> subst h <;> decide

/-! ## The type-general crude `WeylDimData`

For any raw Cartan code `T`, the crude algebraic wrapper uses
`m := numPosRoots T` and `B := crudeBound lab (rank T)`.  This totality is not a
claim that every raw code denotes a simple root system.  On validated codes it
covers the classical and exceptional classification uniformly.  The abstract
Weyl-product datum (`hdim`, `hle`) stays the named honest residual, identical
to `suN_weylDimData_crude`. -/

/-- **The code-general crude `WeylDimData`.**  Given a raw Cartan code `T`, the
`m = numPosRoots T` formal Weyl factors `fac` each under the crude bound
`B = ∏_{p<r}(1 + λ_p)` (`hle`, discharged concretely by
`weyl_factor_le_crudeBound`), and the Weyl dimension as their product
(`hdim`), this packages the crude squared bound `(dim V_λ)² ≤ B^{2·#Δ⁺(T)}`
as a `WeylDimData R` at the UNIFORM per-axis exponent.

The root-system interpretation requires a validated canonical code.  In every
case the abstract Weyl-product inequality is a hypothesis, not a constructed
group formula; only the squared majorization from those hypotheses is proven. -/
def cartanType_weylDimData_crude {R : RepData} (T : CartanType)
    {lab fac : Nat → Q'} {dimVal : Q'}
    (hlab : ∀ p, (0 : Q') ≤ lab p)
    (hfac : ∀ j, (0 : Q') ≤ fac j)
    (hle : ∀ j, fac j ≤ crudeBound lab T.rank)
    (hdim_nonneg : (0 : Q') ≤ dimVal)
    (hdim : dimVal ≤ prodFac fac T.numPosRoots) :
    WeylDimData R :=
  weylDimData_crude (B := crudeBound lab T.rank) (m := T.numPosRoots)
    (crudeBound_ge_one hlab T.rank) hfac hle hdim_nonneg hdim

/-! ### Thin per-type aliases

Named entry points for each family/exceptional, each just `cartanType_weylDimData_crude`
at the given type.  Discoverability only — no new mathematics. -/

/-- `A_n`-code crude `WeylDimData` (`m = n(n+1)/2`). -/
def weylDimData_A {R : RepData} (n : Nat) {lab fac : Nat → Q'} {dimVal : Q'}
    (hlab : ∀ p, (0 : Q') ≤ lab p) (hfac : ∀ j, (0 : Q') ≤ fac j)
    (hle : ∀ j, fac j ≤ crudeBound lab (CartanType.A n).rank)
    (hdim_nonneg : (0 : Q') ≤ dimVal)
    (hdim : dimVal ≤ prodFac fac (CartanType.A n).numPosRoots) : WeylDimData R :=
  cartanType_weylDimData_crude (.A n) hlab hfac hle hdim_nonneg hdim

/-- `B_n`-code crude `WeylDimData` (`m = n²`). -/
def weylDimData_B {R : RepData} (n : Nat) {lab fac : Nat → Q'} {dimVal : Q'}
    (hlab : ∀ p, (0 : Q') ≤ lab p) (hfac : ∀ j, (0 : Q') ≤ fac j)
    (hle : ∀ j, fac j ≤ crudeBound lab (CartanType.B n).rank)
    (hdim_nonneg : (0 : Q') ≤ dimVal)
    (hdim : dimVal ≤ prodFac fac (CartanType.B n).numPosRoots) : WeylDimData R :=
  cartanType_weylDimData_crude (.B n) hlab hfac hle hdim_nonneg hdim

/-- `C_n`-code crude `WeylDimData` (`m = n²`). -/
def weylDimData_C {R : RepData} (n : Nat) {lab fac : Nat → Q'} {dimVal : Q'}
    (hlab : ∀ p, (0 : Q') ≤ lab p) (hfac : ∀ j, (0 : Q') ≤ fac j)
    (hle : ∀ j, fac j ≤ crudeBound lab (CartanType.C n).rank)
    (hdim_nonneg : (0 : Q') ≤ dimVal)
    (hdim : dimVal ≤ prodFac fac (CartanType.C n).numPosRoots) : WeylDimData R :=
  cartanType_weylDimData_crude (.C n) hlab hfac hle hdim_nonneg hdim

/-- `D_n`-code crude `WeylDimData` (`m = n(n−1)`). -/
def weylDimData_D {R : RepData} (n : Nat) {lab fac : Nat → Q'} {dimVal : Q'}
    (hlab : ∀ p, (0 : Q') ≤ lab p) (hfac : ∀ j, (0 : Q') ≤ fac j)
    (hle : ∀ j, fac j ≤ crudeBound lab (CartanType.D n).rank)
    (hdim_nonneg : (0 : Q') ≤ dimVal)
    (hdim : dimVal ≤ prodFac fac (CartanType.D n).numPosRoots) : WeylDimData R :=
  cartanType_weylDimData_crude (.D n) hlab hfac hle hdim_nonneg hdim

/-- `G₂` crude `WeylDimData` (`m = 6`). -/
def weylDimData_G2 {R : RepData} {lab fac : Nat → Q'} {dimVal : Q'}
    (hlab : ∀ p, (0 : Q') ≤ lab p) (hfac : ∀ j, (0 : Q') ≤ fac j)
    (hle : ∀ j, fac j ≤ crudeBound lab CartanType.G2.rank)
    (hdim_nonneg : (0 : Q') ≤ dimVal)
    (hdim : dimVal ≤ prodFac fac CartanType.G2.numPosRoots) : WeylDimData R :=
  cartanType_weylDimData_crude .G2 hlab hfac hle hdim_nonneg hdim

/-- `F₄` crude `WeylDimData` (`m = 24`). -/
def weylDimData_F4 {R : RepData} {lab fac : Nat → Q'} {dimVal : Q'}
    (hlab : ∀ p, (0 : Q') ≤ lab p) (hfac : ∀ j, (0 : Q') ≤ fac j)
    (hle : ∀ j, fac j ≤ crudeBound lab CartanType.F4.rank)
    (hdim_nonneg : (0 : Q') ≤ dimVal)
    (hdim : dimVal ≤ prodFac fac CartanType.F4.numPosRoots) : WeylDimData R :=
  cartanType_weylDimData_crude .F4 hlab hfac hle hdim_nonneg hdim

/-- `E₆` crude `WeylDimData` (`m = 36`). -/
def weylDimData_E6 {R : RepData} {lab fac : Nat → Q'} {dimVal : Q'}
    (hlab : ∀ p, (0 : Q') ≤ lab p) (hfac : ∀ j, (0 : Q') ≤ fac j)
    (hle : ∀ j, fac j ≤ crudeBound lab CartanType.E6.rank)
    (hdim_nonneg : (0 : Q') ≤ dimVal)
    (hdim : dimVal ≤ prodFac fac CartanType.E6.numPosRoots) : WeylDimData R :=
  cartanType_weylDimData_crude .E6 hlab hfac hle hdim_nonneg hdim

/-- `E₇` crude `WeylDimData` (`m = 63`). -/
def weylDimData_E7 {R : RepData} {lab fac : Nat → Q'} {dimVal : Q'}
    (hlab : ∀ p, (0 : Q') ≤ lab p) (hfac : ∀ j, (0 : Q') ≤ fac j)
    (hle : ∀ j, fac j ≤ crudeBound lab CartanType.E7.rank)
    (hdim_nonneg : (0 : Q') ≤ dimVal)
    (hdim : dimVal ≤ prodFac fac CartanType.E7.numPosRoots) : WeylDimData R :=
  cartanType_weylDimData_crude .E7 hlab hfac hle hdim_nonneg hdim

/-- `E₈` crude `WeylDimData` (`m = 120`). -/
def weylDimData_E8 {R : RepData} {lab fac : Nat → Q'} {dimVal : Q'}
    (hlab : ∀ p, (0 : Q') ≤ lab p) (hfac : ∀ j, (0 : Q') ≤ fac j)
    (hle : ∀ j, fac j ≤ crudeBound lab CartanType.E8.rank)
    (hdim_nonneg : (0 : Q') ≤ dimVal)
    (hdim : dimVal ≤ prodFac fac CartanType.E8.numPosRoots) : WeylDimData R :=
  cartanType_weylDimData_crude .E8 hlab hfac hle hdim_nonneg hdim

/-! ## Consistency: the type-A alias agrees with `suN_numPosRoots`

`#Δ⁺(A_n) = n(n+1)/2 = (n+1)((n+1)−1)/2 = suN_numPosRoots (n+1)`, so
`weylDimData_A n` is `suN_weylDimData_crude (n+1)` up to this `Nat` identity. -/

/-- `#Δ⁺(A_n) = suN_numPosRoots (n+1)` — the type-A count matches the SU(N)
count with `N = n+1`. -/
theorem numPosRoots_A_eq_suN (n : Nat) :
    CartanType.numPosRoots (.A n) = suN_numPosRoots (n + 1) := by
  show n * (n + 1) / 2 = (n + 1) * (n + 1 - 1) / 2
  congr 1
  have : n + 1 - 1 = n := by omega
  rw [this, Nat.mul_comm]

end YMGap.RG

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.RG.numPosRoots_A_le
#print axioms YMGap.RG.numPosRoots_B_le
#print axioms YMGap.RG.numPosRoots_C_le
#print axioms YMGap.RG.numPosRoots_D_le
#print axioms YMGap.RG.numPosRoots_exceptional_le
#print axioms YMGap.RG.cartanType_weylDimData_crude
#print axioms YMGap.RG.weylDimData_A
#print axioms YMGap.RG.weylDimData_B
#print axioms YMGap.RG.weylDimData_C
#print axioms YMGap.RG.weylDimData_D
#print axioms YMGap.RG.weylDimData_G2
#print axioms YMGap.RG.weylDimData_F4
#print axioms YMGap.RG.weylDimData_E6
#print axioms YMGap.RG.weylDimData_E7
#print axioms YMGap.RG.weylDimData_E8
#print axioms YMGap.RG.numPosRoots_A_eq_suN
