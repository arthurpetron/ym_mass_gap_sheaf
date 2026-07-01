/-
# Uniform-in-`M` roots-of-unity finite-sum engine for the second-kind power-sum collapse

The general-`M` discrete Chebyshev-`U` orthogonality (Wall-1, all-order Gram PSD) was
reduced — with the entire formal-power-series telescoping/swap/Leibniz content already
PROVED, general `M` — to the single unweighted second-kind power-sum evaluation
`(U★)` (`NewtonRecurrence.RootedNodesU.Usum_value`):

    Asum D n  ≈  Uval M n        (1 ≤ n ≤ 2M),

i.e. `Σ_{k<M} U_n(x_k) = (M − n)` (`n` even) / `0` (`n` odd) on the `M` roots `x_k` of
`U_M`.  Its honest engine is the finite **roots-of-unity / Dirichlet-kernel geometric
sum** in the reciprocal-pair encoding `cos θ = (z + w)·½`, `z·w ≈ 1` (the codebase's
π-free, radical-free avatar of `e^{±iθ}`).

This module supplies that engine ABSTRACTLY and UNIFORMLY in `M`, over `Q'`, with NO
per-`M` nested radicals:

  * **`geomSum` / `geomSum_telescope`** — the general-base finite geometric sum
    `Σ_{k=0}^{M} y^k` and its closed form `(y − 1)·Σ_{k=0}^{M} y^k ≈ y^{M+1} − 1`,
    uniform in `M`, for ANY `y : Q'` (radical-free).  This is the abstract Dirichlet
    kernel; `OffDiagShift.geom_telescope` (base `z²`) is a special case.
  * **`geomSum_unit_cleared`** — the ROOTS-OF-UNITY finite-sum identity: if `y^N ≈ 1`
    (`N ≥ 1`) then `(y − 1)·Σ_{k=0}^{N−1} y^k ≈ 0` (the sum of all `N`-th roots of unity's
    powers vanishes, in cleared form — no division/inversion needed).  Uniform in `N`.
  * **`geomEven_eq` / `geom_telescope_via_geomSum`** — the abstract engine SUBSUMES the
    factorization's geometric core: `geomEven z M ≈ geomSum (z²) M`, and
    `OffDiagShift.geom_telescope` is re-derived from `geomSum_telescope`.
  * **`cleared_via_engine`** — the cleared product identity
    `(z² − 1)·(z^M·U_M((z+w)·½)) ≈ z^{2(M+1)} − 1` (`z·w ≈ 1`), general `M`, obtained by
    routing `OffDiagShift.prodIdentity_geom` through this abstract engine.  This is the
    single-variable generating shadow of `∏_{k<M}(1 − 2x_k z + z²) = Σ_{j=0}^M z^{2j}`
    that feeds `Usum_value`.
  * **`UnitRootPair`** — the abstract located reciprocal-pair primitive-root datum `ω`
    (`Type`-level): `z, w` with `z·w ≈ 1`, `z^{2(M+1)} ≈ 1`, `z^{M+1} ≈ −1` carried as
    `Q'` relations WITHOUT a radical value — the "genuine new object" the general-`M`
    Dirichlet route needs; `unitPair_dirichlet_cleared` fires the roots-of-unity collapse
    on it.

## Reduction and honest scope (AGENTS.md Rule 6)

`Usum_value` (general `M`) ⇒ all-order Gram PSD is the already-PROVED
`NewtonRecurrence.gram_psd_closed`; we re-export it as `gram_psd_of_rootedU`.  This module
PROVES the uniform roots-of-unity engine that drives `Usum_value`, and the reduction of the
factorization's geometric core to it (`cleared_via_engine`).  The single remaining named
residual is the LOCATED REALIZATION: instantiating `UnitRootPair`/the convolution bridge at
the located general-`M` `ChebRoot` cos-nodes (the `FactoredNodes` fields, `UsumFactorization`
VERDICT R-a/R-b/R-c).  It is NOT faked; it is carried as `Type`-level data.

The discrete Chebyshev-`U` orthogonality is DISCHARGED UNCONDITIONALLY for every `M ≤ 4`
(`discreteOrtho_M2/M3/M4`), so the roots-of-unity identity's downstream consequence is
proved uniformly across the small-order range.

## Axiom gate (AGENTS.md Rule 1 / Rule 8)

`[propext]` / `[propext, Quot.sound]` only.  No `Classical.*`, no `sorry`/`sorryAx`,
no `native_decide`, no `decide` on a non-decidable `Prop`.  `decide` only on closed
`Q'`/`Nat`.  `UnitRootPair` is `Type`-level data (MLTT/HoTT-valid).
-/

import YMGap.Continuum.OffDiagShift
import YMGap.Continuum.NewtonRecurrence
import YMGap.Continuum.ChebGeneralOrtho
import YMGap.Continuum.ChebLocatedRoots4Even

namespace YMGap.Continuum.ChebUniformOrtho

open YMGap.Constructive
open YMGap.Constructive.Q'
open YMGap.Continuum.Cheb
open YMGap.Continuum.ChebU
open YMGap.Continuum.OffDiagShift

local infix:50 " ≈ " => Q'.eqv

instance : Trans (Q'.eqv) (Q'.eqv) (Q'.eqv) where
  trans h1 h2 := eqv_trans _ _ _ h1 h2

/-! ## 1. The general-base finite geometric sum and its closed form (uniform in `M`) -/

/-- The finite geometric partial sum `Σ_{k=0}^{M} y^k` over `Q'` (general base). -/
def geomSum (y : Q') : Nat → Q'
  | 0 => (1 : Q')
  | (m+1) => geomSum y m + y ^ (m+1)

@[simp] theorem geomSum_zero (y : Q') : geomSum y 0 = 1 := rfl
theorem geomSum_succ (y : Q') (m : Nat) : geomSum y (m+1) = geomSum y m + y ^ (m+1) := rfl

/-- **The abstract Dirichlet-kernel closed form** (uniform in `M`, any `y`):
`(y − 1)·(Σ_{k=0}^{M} y^k) ≈ y^{M+1} − 1`.  Radical-free; the general-base generalization
of `OffDiagShift.geom_telescope`. -/
theorem geomSum_telescope (y : Q') (M : Nat) :
    (y + (-(1 : Q'))) * geomSum y M ≈ y ^ (M+1) + (-(1 : Q')) := by
  induction M with
  | zero =>
      show (y + (-(1 : Q'))) * geomSum y 0 ≈ y ^ (0+1) + (-(1 : Q'))
      rw [geomSum_zero]
      refine eqv_trans _ _ _ (mul_one_eqv _) ?_
      refine add_eqv_congr_right _ _ _ ?_
      -- y ≈ y^(0+1)
      rw [Q'.pow_succ, Q'.pow_zero]
      exact eqv_symm (mul_one_eqv y)
  | succ m ih =>
      rw [geomSum_succ]
      refine eqv_trans _ _ _ (mul_add_eqv (y + (-(1 : Q'))) (geomSum y m) (y ^ (m+1))) ?_
      refine eqv_trans _ _ _ (add_eqv_congr_right _ _ _ ih) ?_
      -- (y^(m+1) + (−1)) + (y+(−1))·y^(m+1) ≈ y^(m+2) + (−1)
      have hsec : (y + (-(1 : Q'))) * y ^ (m+1) ≈ y ^ (m+2) + (-(y ^ (m+1))) := by
        refine eqv_trans _ _ _ (Cheb.add_mul_eqv y (-(1 : Q')) (y ^ (m+1))) ?_
        refine Cheb.add_eqv_congr _ _ _ _ ?_ ?_
        · -- y·y^(m+1) ≈ y^(m+2)
          show y * y ^ (m+1) ≈ y ^ (m+2)
          have he : (m+2 : Nat) = (m+1)+1 := rfl
          rw [he, Q'.pow_succ]; exact eqv_refl _
        · exact eqv_trans _ _ _ (neg_mul_eqv 1 (y ^ (m+1)))
            (neg_eqv_congr _ _ (one_mul_eqv (y ^ (m+1))))
      refine eqv_trans _ _ _ (add_eqv_congr_left _ _ _ hsec) ?_
      -- cancel y^(m+1) (identical telescope to OffDiagShift.geom_telescope)
      calc (y ^ (m+1) + (-(1 : Q'))) + (y ^ (m+2) + (-(y ^ (m+1))))
          ≈ ((-(1 : Q')) + y ^ (m+1)) + (y ^ (m+2) + (-(y ^ (m+1)))) :=
            add_eqv_congr_right _ _ _ (add_comm_eqv (y ^ (m+1)) (-(1 : Q')))
        _ ≈ (-(1 : Q')) + (y ^ (m+1) + (y ^ (m+2) + (-(y ^ (m+1))))) :=
            add_assoc_eqv (-(1 : Q')) (y ^ (m+1)) (y ^ (m+2) + (-(y ^ (m+1))))
        _ ≈ (-(1 : Q')) + (y ^ (m+1) + ((-(y ^ (m+1))) + y ^ (m+2))) :=
            add_eqv_congr_left _ _ _ (add_eqv_congr_left _ _ _
              (add_comm_eqv (y ^ (m+2)) (-(y ^ (m+1)))))
        _ ≈ (-(1 : Q')) + ((y ^ (m+1) + (-(y ^ (m+1)))) + y ^ (m+2)) :=
            add_eqv_congr_left _ _ _ (eqv_symm (add_assoc_eqv (y ^ (m+1)) (-(y ^ (m+1))) (y ^ (m+2))))
        _ ≈ (-(1 : Q')) + ((0 : Q') + y ^ (m+2)) :=
            add_eqv_congr_left _ _ _ (add_eqv_congr_right _ _ _ (Q'.add_neg_self_eqv (y ^ (m+1))))
        _ ≈ (-(1 : Q')) + y ^ (m+2) := by
            refine add_eqv_congr_left _ _ _ ?_; rw [zero_add']; exact eqv_refl _
        _ ≈ y ^ (m+2) + (-(1 : Q')) := add_comm_eqv (-(1 : Q')) (y ^ (m+2))

/-! ## 2. The roots-of-unity finite-sum identity (uniform in `N`, cleared) -/

/-- **The roots-of-unity finite-sum identity** (cleared, uniform in `N`): if `y^N ≈ 1`
(`N ≥ 1`) then `(y − 1)·(Σ_{k=0}^{N−1} y^k) ≈ 0`.  The sum of the powers of an `N`-th root
of unity vanishes — the π-free, division-free core of the Dirichlet collapse
`Σ_{k=1}^{M} cos(mkπ/(M+1)) = −1/0`.  Radical-free. -/
theorem geomSum_unit_cleared (y : Q') (N : Nat) (hN : 1 ≤ N) (h : y ^ N ≈ (1 : Q')) :
    (y + (-(1 : Q'))) * geomSum y (N - 1) ≈ (0 : Q') := by
  have ht := geomSum_telescope y (N - 1)
  have he : (N - 1) + 1 = N := by omega
  rw [he] at ht
  refine eqv_trans _ _ _ ht ?_
  refine eqv_trans _ _ _ (add_eqv_congr_right _ _ _ h) ?_
  decide

/-! ## 3. Subsumption: the abstract engine reproduces the factorization's geometric core -/

/-- `(z²)^k ≈ z^{2k}` — the squared-base power. -/
theorem sqpow (z : Q') : ∀ k, (z ^ 2) ^ k ≈ z ^ (2 * k)
  | 0 => by rw [Q'.pow_zero, Q'.pow_zero]; exact eqv_refl _
  | (k+1) => by
      rw [Q'.pow_succ]
      refine eqv_trans _ _ _ (mul_eqv_congr_left _ _ _ (sqpow z k)) ?_
      refine eqv_trans _ _ _ (zpow_add z 2 (2 * k)) ?_
      have he : 2 + 2 * k = 2 * (k+1) := by omega
      rw [he]; exact eqv_refl _

/-- `geomEven z M ≈ geomSum (z²) M`: the base-`z²` geometric sum `Σ_{j=0}^M z^{2j}` is the
general-base `geomSum` at base `z²`. -/
theorem geomEven_eq (z : Q') : ∀ M, geomEven z M ≈ geomSum (z ^ 2) M
  | 0 => by rw [geomEven_zero, geomSum_zero]; exact eqv_refl _
  | (m+1) => by
      rw [geomEven_succ, geomSum_succ]
      exact Cheb.add_eqv_congr _ _ _ _ (geomEven_eq z m) (eqv_symm (sqpow z (m+1)))

/-- **`OffDiagShift.geom_telescope`, re-derived through the abstract engine.**
`(z² − 1)·geomEven z M ≈ z^{2(M+1)} − 1`, obtained from `geomSum_telescope` at base `z²`
plus the squared-base bridge — the abstract engine subsumes the factorization's
geometric core. -/
theorem geom_telescope_via_geomSum (z : Q') (M : Nat) :
    (z ^ 2 + (-(1 : Q'))) * geomEven z M ≈ z ^ (2 * (M+1)) + (-(1 : Q')) := by
  refine eqv_trans _ _ _ (mul_eqv_congr_left _ _ _ (geomEven_eq z M)) ?_
  refine eqv_trans _ _ _ (geomSum_telescope (z ^ 2) M) ?_
  exact add_eqv_congr_right _ _ _ (sqpow z (M+1))

/-- **The cleared product identity via the abstract engine** (general `M`, `z·w ≈ 1`):
`(z² − 1)·(z^M·U_M((z+w)·½)) ≈ z^{2(M+1)} − 1`.  Routes `OffDiagShift.prodIdentity_geom`
(the single-variable factorization shadow `∏_k(1−2x_k z+z²) = Σ_{j=0}^M z^{2j}`) through
`geom_telescope_via_geomSum`.  This is the generating identity that feeds `Usum_value`. -/
theorem cleared_via_engine (z w : Q') (hzw : z * w ≈ (1 : Q')) (M : Nat) :
    (z ^ 2 + (-(1 : Q'))) * (z ^ M * U M ((z + w) * HalfPow.half))
      ≈ z ^ (2 * (M+1)) + (-(1 : Q')) :=
  eqv_trans _ _ _ (OffDiagShift.prodIdentity_geom z w hzw M) (geom_telescope_via_geomSum z M)

/-! ## 4. The abstract located primitive-root datum `ω` and its Dirichlet collapse -/

/-- **The located reciprocal-pair primitive-root datum `ω`** (`Type`-level, MLTT/HoTT-valid).
Carries `z, w : Q'` (the codebase's π-free avatar of `e^{±iπ/(M+1)}`) with `z·w ≈ 1` and the
roots-of-unity relations `z^{2(M+1)} ≈ 1`, `z^{M+1} ≈ −1`, as `Q'` relations WITHOUT a
radical value — the single new object the general-`M` Dirichlet route needs.  The cos-node is
`(z+w)·½` (no nested surd). -/
structure UnitRootPair (M : Nat) where
  /-- The primitive root `ω` (`z`) and its reciprocal/conjugate `ω⁻¹` (`w`). -/
  z : Q'
  w : Q'
  /-- `z·w ≈ 1` — the reciprocal pair (`ω·ω⁻¹ = 1`). -/
  recip : z * w ≈ (1 : Q')
  /-- `z^{2(M+1)} ≈ 1` — `ω` is a `2(M+1)`-th root of unity. -/
  order : z ^ (2 * (M+1)) ≈ (1 : Q')
  /-- `z^{M+1} ≈ −1` — the half-period reflection `ω^{M+1} = e^{iπ} = −1`. -/
  half : z ^ (M+1) ≈ (-(1 : Q'))

/-- **The Dirichlet collapse fired on the located datum** (general `M`): the full geometric
node sum over `ω`'s `2(M+1)` powers is cleared to `0`,
`(z − 1)·(Σ_{k=0}^{2M+1} z^k) ≈ 0`, directly from `geomSum_unit_cleared` at `N = 2(M+1)`. -/
theorem unitPair_dirichlet_cleared {M : Nat} (P : UnitRootPair M) :
    (P.z + (-(1 : Q'))) * geomSum P.z (2 * (M+1) - 1) ≈ (0 : Q') :=
  geomSum_unit_cleared P.z (2 * (M+1)) (by omega) P.order

/-! ## 5. Reduction to `Usum_value` ⇒ all-order Gram PSD (Wall-1) -/

/-- **`Usum_value` ⇒ all-order Gram PSD** (re-export of `NewtonRecurrence.gram_psd_closed`,
general `M`).  Given the enriched root datum `RootedNodesU M` — whose sole field `Usum_value`
is exactly what the roots-of-unity engine above drives — the all-order Gram-PSD residual
`ChebOrthogonality.PowerSumCollapse` is inhabited.  The formal-power-series derivation is
fully PROVED; the single remaining input is the LOCATED REALIZATION of `Usum_value`. -/
theorem gram_psd_of_rootedU {M : Nat} (D : NewtonRecurrence.RootedNodesU M) :
    ChebOrthogonality.PowerSumCollapse D.toRooted.toData.toU :=
  NewtonRecurrence.gram_psd_closed D

/-! ## 6. The discrete Chebyshev-`U` orthogonality, UNCONDITIONAL for every `M ≤ 4` -/

/-- **`M = 2`, UNCONDITIONAL** — through the telescoping/swap/`(U★)` chain. -/
theorem discreteOrtho_M2 :
    ChebOrthogonality.PowerSumCollapse RootPowerSumBridge.rootedNodes2.toData.toU :=
  NewtonRecurrence.gram_psd_closed2
/-- **`M = 3`, UNCONDITIONAL** — the discharged located `√½`-node instance. -/
theorem discreteOrtho_M3 :
    ChebOrthogonality.PowerSumCollapse ChebLocatedRoots.rootData3.toU :=
  ChebGeneralOrtho.order3_orthoCollapse_closed
/-- **`M = 4`, UNCONDITIONAL** — the discharged located `√5`-node instance. -/
theorem discreteOrtho_M4 :
    ChebOrthogonality.PowerSumCollapse ChebLocatedRoots4.rootData4.toU :=
  ChebLocatedRoots4Even.order4_orthoCollapse_locatedNodes

end YMGap.Continuum.ChebUniformOrtho

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.ChebUniformOrtho.geomSum_telescope
#print axioms YMGap.Continuum.ChebUniformOrtho.geomSum_unit_cleared
#print axioms YMGap.Continuum.ChebUniformOrtho.sqpow
#print axioms YMGap.Continuum.ChebUniformOrtho.geomEven_eq
#print axioms YMGap.Continuum.ChebUniformOrtho.geom_telescope_via_geomSum
#print axioms YMGap.Continuum.ChebUniformOrtho.cleared_via_engine
#print axioms YMGap.Continuum.ChebUniformOrtho.unitPair_dirichlet_cleared
#print axioms YMGap.Continuum.ChebUniformOrtho.gram_psd_of_rootedU
#print axioms YMGap.Continuum.ChebUniformOrtho.discreteOrtho_M2
#print axioms YMGap.Continuum.ChebUniformOrtho.discreteOrtho_M3
#print axioms YMGap.Continuum.ChebUniformOrtho.discreteOrtho_M4
