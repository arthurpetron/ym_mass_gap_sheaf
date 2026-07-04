/-
Rank- and type-general crude squared-Weyl-dimension `WeylDimData`, instantiated
for EVERY compact-simple Cartan type from the single generic crude engine.

# What this module supplies (and what stays a NAMED residual)

`RG/WeylDimGeneral.lean` proves the generic crude engine once — a bare finite
product of `m` factors each in `[0, B]` with `1 ≤ B` is `≤ B^m`
(`prodFac_le_pow`), hence the squared-dimension majorant `dimVal² ≤ B^{2m}`
(`dimSq_le_crude`), packaged as `weylDimData_crude`.  It then instantiated the
type-A family (`suN_weylDimData_crude`) with `m = #Δ⁺(A_{N−1}) = N(N−1)/2`.

This module carries the *counting* fact — the number of positive roots
`m = #Δ⁺` — for every Cartan type, and packages the crude `WeylDimData` per
type from it.  The crude route is **convention-blind**: it needs only the
positive-root COUNT `m` (a pure `Nat`), never the root lengths, so the
non-simply-laced types `B_n, C_n, G₂, F₄` need no special treatment here (the
short/long-root convention only enters the *tail coefficient* `c_i` of
`AxisFactorBound`, a different structure).

  * `CartanType` — the nine compact-simple families/exceptionals, tagged by
    rank where relevant.
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

import YMGap.RG.WeylDimGeneral

namespace YMGap.RG

open YMGap.Constructive
open YMGap.RepTheory

/-! ## The compact-simple Cartan types

The four classical families (tagged by rank `n`) plus the five exceptionals.
This inductive is the scalar-invariant carrier: the crude `WeylDimData` route
depends on a Cartan type ONLY through its positive-root count, exposed below.
No enumeration of "19 types" lives in the logic — the classical families are
parametric in `n`. -/

/-- The compact-simple Cartan types: `A_n, B_n, C_n, D_n` (rank `n`) and the
five exceptionals `G₂, F₄, E₆, E₇, E₈`. -/
inductive CartanType
  | A (n : Nat)
  | B (n : Nat)
  | C (n : Nat)
  | D (n : Nat)
  | G2
  | F4
  | E6
  | E7
  | E8
  deriving DecidableEq

/-- The Lie rank `r` (number of Cartan axes) of each type. -/
def CartanType.rank : CartanType → Nat
  | .A n => n
  | .B n => n
  | .C n => n
  | .D n => n
  | .G2 => 2
  | .F4 => 4
  | .E6 => 6
  | .E7 => 7
  | .E8 => 8

/-- The number of positive roots `#Δ⁺` of each type — the ONLY combinatorial
input the crude route needs (convention-blind: root COUNT, not root lengths).

  * `A_n`: `n(n+1)/2`  (`= N(N−1)/2` with `N = n+1`)
  * `B_n`, `C_n`: `n²`
  * `D_n`: `n(n−1)`
  * `G₂`: 6, `F₄`: 24, `E₆`: 36, `E₇`: 63, `E₈`: 120. -/
def CartanType.numPosRoots : CartanType → Nat
  | .A n => n * (n + 1) / 2
  | .B n => n * n
  | .C n => n * n
  | .D n => n * (n - 1)
  | .G2 => 6
  | .F4 => 24
  | .E6 => 36
  | .E7 => 63
  | .E8 => 120

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

For ANY Cartan type `T`, the crude squared bound at `m := numPosRoots T` and
`B := crudeBound lab (rank T)`.  A single wrapper over the proven
`weylDimData_crude`, parametric in the type — the whole classical + exceptional
landscape at once.  The abstract Weyl-product datum (`hdim`, `hle`) stays the
named honest residual, identical to `suN_weylDimData_crude`. -/

/-- **The type-general crude `WeylDimData`.**  Given a Cartan type `T`, the
`m = #Δ⁺(T)` positive-root Weyl factors `fac` each under the crude bound
`B = ∏_{p<r}(1 + λ_p)` (`hle`, discharged concretely by
`weyl_factor_le_crudeBound`), and the Weyl dimension as their product
(`hdim`), this packages the crude squared bound `(dim V_λ)² ≤ B^{2·#Δ⁺(T)}`
as a `WeylDimData R` at the UNIFORM per-axis exponent.

The genuine per-type residual — the abstract Weyl dimension product over the
`#Δ⁺(T)` positive roots — is the hypothesis, not faked; the squared
majorization is proven. -/
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

/-- `A_n = SU(n+1)` crude `WeylDimData` (`m = n(n+1)/2`). -/
def weylDimData_A {R : RepData} (n : Nat) {lab fac : Nat → Q'} {dimVal : Q'}
    (hlab : ∀ p, (0 : Q') ≤ lab p) (hfac : ∀ j, (0 : Q') ≤ fac j)
    (hle : ∀ j, fac j ≤ crudeBound lab (CartanType.A n).rank)
    (hdim_nonneg : (0 : Q') ≤ dimVal)
    (hdim : dimVal ≤ prodFac fac (CartanType.A n).numPosRoots) : WeylDimData R :=
  cartanType_weylDimData_crude (.A n) hlab hfac hle hdim_nonneg hdim

/-- `B_n = SO(2n+1)` crude `WeylDimData` (`m = n²`). -/
def weylDimData_B {R : RepData} (n : Nat) {lab fac : Nat → Q'} {dimVal : Q'}
    (hlab : ∀ p, (0 : Q') ≤ lab p) (hfac : ∀ j, (0 : Q') ≤ fac j)
    (hle : ∀ j, fac j ≤ crudeBound lab (CartanType.B n).rank)
    (hdim_nonneg : (0 : Q') ≤ dimVal)
    (hdim : dimVal ≤ prodFac fac (CartanType.B n).numPosRoots) : WeylDimData R :=
  cartanType_weylDimData_crude (.B n) hlab hfac hle hdim_nonneg hdim

/-- `C_n = Sp(n)` crude `WeylDimData` (`m = n²`). -/
def weylDimData_C {R : RepData} (n : Nat) {lab fac : Nat → Q'} {dimVal : Q'}
    (hlab : ∀ p, (0 : Q') ≤ lab p) (hfac : ∀ j, (0 : Q') ≤ fac j)
    (hle : ∀ j, fac j ≤ crudeBound lab (CartanType.C n).rank)
    (hdim_nonneg : (0 : Q') ≤ dimVal)
    (hdim : dimVal ≤ prodFac fac (CartanType.C n).numPosRoots) : WeylDimData R :=
  cartanType_weylDimData_crude (.C n) hlab hfac hle hdim_nonneg hdim

/-- `D_n = SO(2n)` crude `WeylDimData` (`m = n(n−1)`). -/
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
