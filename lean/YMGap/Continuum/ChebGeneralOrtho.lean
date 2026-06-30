/-
# General-`M` discrete Chebyshev-`U` orthogonality on the LOCATED substrate, and the
# order-4 Newton–Vieta closure (Track B: general-`M` power-sum collapse)

The `t > 0` heat-kernel off-diagonal OS2 reduces (`HeatKernelGaussNode`, `RiemannSOS`)
to the Gauss–Chebyshev exactness of the second-kind discrete orthogonality at the roots
`x_k = cos(kπ/(M+1))` of `U_M`, i.e. to the first-kind Dirichlet power-sum collapse
`(★)` (`PowerSumCollapse.TPowerSum`):

    S_0 = M,   S_2 = −1,   S_p = S_{p+2}   (0 < p ≤ M−1),     S_j := Σ_{k<M} T_j(x_k).

Two substrates can carry the nodes.  The *rational* `RootPowerSumBridge.RootedNodes`
(`node : Q'`) is only inhabitable at the true roots when those roots are rational, i.e.
`M ≤ 2`; the cyclotomic `(U★)` route (`NewtonRecurrence`, `UsumFactorization`) lives
there and is closed at `M = 2`.  The *constructive-real* `PowerSumCollapse.ChebRootDataT`
(`x : Nat → CReal`) CAN hold the irrational located nodes; `ChebLocatedRoots.rootData3`
lives there and the order-3 instance is closed UNCONDITIONALLY
(`ChebLocatedRoots.locatedRootPowerSums3`).

This module supplies the **general-`M` located-substrate assembly** — the abstract-`M`
generalization of `ChebDiscreteOrtho.rootBridge3_of_located` — and the **order-4
Newton–Vieta rational collapse**, RADICAL-FREE, which reduces order-4 discrete
orthogonality to a SINGLE named located residual exactly as the order-3 file did.

## What this module proves (genuine, axiom-clean, π-free, no explicit radicals)

  * **`locatedCollapse_of_rationalShift`** — the general-`M` located-substrate assembly.
    For ANY `ChebRootDataT M` (`M ≥ 1`) and ANY rational power-sum profile `Sval`, the
    located realization `Sj D j ≈ ofQ'(Sval j)` (`1 ≤ j ≤ 2M`) TOGETHER WITH the two
    RATIONAL collapse facts `Sval 2 ≈ −1` and `Sval p ≈ Sval (p+2)` (`0 < p ≤ M−1`)
    discharges the full upstream chain `RootPowerSumBridge → TPowerSum →
    ChebOrthogonality.PowerSumCollapse`, and (with `tval 0 k ≈ 1`) the diagonal
    orthogonality value `(M+1)/2`.  This is the abstract-`M` Vieta link: the located
    irrational nodes realize a rational power-sum profile whose RATIONAL collapse the
    Newton–Vieta arithmetic certifies.

  * **The order-4 Newton–Vieta rational power sums** (`order4_newton_*`,
    `order4_powerSum_collapse`), RADICAL-FREE.  `U_4 = 16x⁴ − 12x² + 1` has monic
    minimal polynomial `w⁴ − ¾w² + 1/16`, so `e_1 = 0`, `e_2 = −¾`, `e_3 = 0`,
    `e_4 = 1/16` (rational, root-independent).  Newton's identities fix the ordinary
    power sums `p_2 = 3/2, p_4 = 7/8, p_6 = 9/16, p_8 = 47/128` and the first-kind
    `S_2 = S_4 = S_6 = S_8 = −1`, `S_1 = S_3 = S_5 = S_7 = 0`, by closed `Q'`
    computation — the order-4 analogue of `ChebDiscreteOrtho.order3_powerSum_collapse`.

  * **`order4_orthoCollapse_of_located` / `order4_diag_value_of_located`** — order-4
    discrete orthogonality (including the diagonal value `(4+1)/2 = 5/2`) REDUCED to the
    single named located residual `LocatedRootPowerSums4` ("the located `U_4` roots
    `±(√5±1)/4` realize the Newton power sums `S_1,…,S_8`"), via the general assembly.

  * **The `MomentIntegralIdentity` reduction, narrowed.**  The continuous heat-kernel
    moment-integral residual `RiemannSOS.MomentIntegralIdentity` is re-exported together
    with the PROVED input #1 (`RCoeffReproduction.rCoeff_eq_two_a_moment`,
    `m_s = (s+1)a^{s(s+2)}`, node-free): closing it requires only the continuous
    `U`-weight orthogonality `∫U_cU_d√(1−x²) = (π/2)δ` (input #2, the continuous shadow
    of the discrete collapse closed above) and Riemann convergence (input #3).  We make
    the narrowed residual explicit and re-export the proved reduction
    `MomentIntegralIdentity ⇒` all-order character Gram PSD.

## Honesty / scope (AGENTS.md Rule 6)

This does NOT close general `M`: the located realization (`LocatedRootPowerSums4` and its
general-`M` analogue) and the continuous moment-integral identity remain the named walls.
What is genuinely advanced: (i) the located-substrate assembly is now abstract over `M`
(it was order-3-specific); (ii) the order-4 Newton–Vieta collapse is proved EXACTLY,
radical-free (it was open beyond order 3); (iii) order-4 orthogonality is reduced to ONE
named located residual; (iv) the `MomentIntegralIdentity` residual is narrowed to inputs
#2/#3 with input #1 cited as proved.  No claim that closing the discrete collapse closes
`MomentIntegralIdentity` — the two routes (exact-Gauss vs rational-Riemann) are distinct
and share only the proved input #1.

## Reuse / provenance

The moment-matrix SOS machinery is the Mathlib-free constructive transfer of the external
4D-GFF formalization (Douglas–Hoback–Mei–Nissim, "Formalization of QFT",
arXiv:2603.15770; repository `mrdouglasny/OSforGFF`).  The product linearization, the
weight-fold bridge, the `ChebRootDataT` node interface, `RootPowerSumBridge`,
`tPowerSum_of_bridge`, and `chebU_orthogonality_diag0` are the repo's `ChebOrthogonality`
/ `PowerSumCollapse` / `TPowerSum` layers; the order-3 located template is
`ChebDiscreteOrtho` / `ChebLocatedRoots`.

## Axiom gate (AGENTS.md Rule 1 / Rule 8)

`[propext]` / `[propext, Quot.sound]` only (`Quot.sound` via reused `omega`/`Nat`/`Int`
helpers).  No `Classical.*`, no `sorry`/`sorryAx`, no `native_decide`, no `decide` on a
non-decidable `Prop` (`decide` only on closed `Q'`/`Nat`).  All node data are `Type`-level
(MLTT/HoTT-valid); the residual `LocatedRootPowerSums4` is a `Prop`, never `sorry`.
-/

import YMGap.Continuum.ChebLocatedRoots
import YMGap.Continuum.RiemannSOS
import YMGap.Continuum.RCoeffReproduction

namespace YMGap.Continuum.ChebGeneralOrtho

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.PowerSumCollapse (ChebRootDataT Sj)

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The general-`M` located-substrate assembly

The order-3 file (`ChebDiscreteOrtho.rootBridge3_of_located`) discharges the root-side
bridge at `M = 3` from the four located facts `Sj D j ≈ ofQ'(S_j)` (`j = 1,…,4`) plus the
explicit rational relations `S_1 = S_3`, `S_2 = S_4`, `S_2 = −1`.  We lift that to abstract
`M`: a rational profile `Sval : Nat → Q'` whose realization the located nodes carry, plus
the two RATIONAL collapse facts, yields `TPowerSum.RootPowerSumBridge D` for any `M ≥ 1`. -/

/-- **The general-`M` root-side bridge from a realized rational profile.**  Given a located
node datum `D : ChebRootDataT M` (`M ≥ 1`) realizing the rational power-sum profile `Sval`
on the range `1 ≤ j ≤ 2M`, together with the two RATIONAL collapse facts `Sval 2 ≈ −1` and
`Sval p ≈ Sval (p+2)` (`0 < p ≤ M−1`), the root-side bridge `RootPowerSumBridge D` holds.
The abstract-`M` generalization of `ChebDiscreteOrtho.rootBridge3_of_located`. -/
theorem rootBridge_of_locatedGen {M : Nat} (hM : 1 ≤ M) (D : ChebRootDataT M)
    (Sval : Nat → Q')
    (hloc : ∀ j, 1 ≤ j → j ≤ 2 * M → CReal.Equiv (Sj D j) (CReal.ofQ' (Sval j)))
    (h2 : Sval 2 ≈ (-(1 : Q')))
    (hshift : ∀ p, 0 < p → p ≤ M - 1 → Sval p ≈ Sval (p + 2)) :
    TPowerSum.RootPowerSumBridge D := by
  refine ⟨?_, ?_⟩
  · -- S_2 ≈ ofQ'(−1) : realize at j = 2, then the rational fact.
    exact CReal.Equiv.trans (hloc 2 (by omega) (by omega))
      (ChebDiscreteOrtho.ofQ'_eqv h2)
  · -- S_p ≈ S_{p+2} : realize at p and p+2, bridged by the rational shift.
    intro p hp hpM
    have hp1 : 1 ≤ p := by omega
    have hp2M : p ≤ 2 * M := by omega
    have hpp2M : p + 2 ≤ 2 * M := by omega
    exact CReal.Equiv.trans (hloc p hp1 hp2M)
      (CReal.Equiv.trans (ChebDiscreteOrtho.ofQ'_eqv (hshift p hp hpM))
        (CReal.Equiv.symm (hloc (p + 2) (by omega) hpp2M)))

/-- **The general-`M` orthogonality collapse from a realized rational profile.**  Composing
`rootBridge_of_locatedGen` with `TPowerSum.tPowerSum_of_bridge` (using `tval 0 k ≈ 1`) and
`PowerSumCollapse.powerSumCollapse_of_TPowerSum`: the all-order single-`U` moment collapse
`ChebOrthogonality.PowerSumCollapse D.toU` holds for any `M ≥ 1`. -/
theorem locatedCollapse_of_rationalShift {M : Nat} (hM : 1 ≤ M) (D : ChebRootDataT M)
    (htval0 : ∀ k, CReal.Equiv (D.tval 0 k) CReal.cone)
    (Sval : Nat → Q')
    (hloc : ∀ j, 1 ≤ j → j ≤ 2 * M → CReal.Equiv (Sj D j) (CReal.ofQ' (Sval j)))
    (h2 : Sval 2 ≈ (-(1 : Q')))
    (hshift : ∀ p, 0 < p → p ≤ M - 1 → Sval p ≈ Sval (p + 2)) :
    ChebOrthogonality.PowerSumCollapse D.toU :=
  PowerSumCollapse.powerSumCollapse_of_TPowerSum D
    (TPowerSum.tPowerSum_of_bridge D htval0
      (rootBridge_of_locatedGen hM D Sval hloc h2 hshift))

/-- **The general-`M` diagonal orthogonality value `(M+1)/2` from a realized rational
profile.**  `Σ_{k<M} (1 − x_k²)·U_0(x_k)² = (M+1)/2` — the load-bearing normalization,
abstract over `M ≥ 1`, given the located realization and the rational collapse. -/
theorem locatedDiag_of_rationalShift {M : Nat} (hM : 1 ≤ M) (D : ChebRootDataT M)
    (htval0 : ∀ k, CReal.Equiv (D.tval 0 k) CReal.cone)
    (Sval : Nat → Q')
    (hloc : ∀ j, 1 ≤ j → j ≤ 2 * M → CReal.Equiv (Sj D j) (CReal.ofQ' (Sval j)))
    (h2 : Sval 2 ≈ (-(1 : Q')))
    (hshift : ∀ p, 0 < p → p ≤ M - 1 → Sval p ≈ Sval (p + 2)) :
    CReal.Equiv (ChebOrthogonality.orthoSum D.toU 0 0)
      (CReal.ofQ' (Q'.mkPos ((M : Int) + 1) 2 (by decide))) :=
  ChebOrthogonality.chebU_orthogonality_diag0 D.toU
    (locatedCollapse_of_rationalShift hM D htval0 Sval hloc h2 hshift)

/-! ## 2. The order-4 Newton–Vieta rational power sums (RADICAL-FREE)

`U_4(x) = 16x⁴ − 12x² + 1`; its four roots `±(√5±1)/4` are the roots of the monic
`w⁴ − ¾w² + 1/16`, whose elementary symmetric functions are `e_1 = 0`, `e_2 = −¾`,
`e_3 = 0`, `e_4 = 1/16` — RATIONAL, fixed by the coefficients alone (no roots).  Newton's
identities (with `e_1 = e_3 = 0`) then fix the ordinary power sums

    p_2 = −2e_2 = 3/2,
    p_4 = −e_2 p_2 − 4e_4 = 7/8,
    p_6 = −e_2 p_4 − e_4 p_2 = 9/16,
    p_8 = −e_2 p_6 − e_4 p_4 = 47/128,

all rational. -/

/-- `e_2 = −3/4`, the dominant elementary symmetric function of the `U_4` roots. -/
def e2_4 : Q' := Q'.mkPos (-3) 4 (by decide)
/-- `e_4 = 1/16`, the constant elementary symmetric function of the `U_4` roots. -/
def e4_4 : Q' := Q'.mkPos 1 16 (by decide)

/-- `p_2 = Σ_k x_k² = 3/2`. -/
def q2 : Q' := Q'.mkPos 3 2 (by decide)
/-- `p_4 = Σ_k x_k⁴ = 7/8`. -/
def q4 : Q' := Q'.mkPos 7 8 (by decide)
/-- `p_6 = Σ_k x_k⁶ = 9/16`. -/
def q6 : Q' := Q'.mkPos 9 16 (by decide)
/-- `p_8 = Σ_k x_k⁸ = 47/128`. -/
def q8 : Q' := Q'.mkPos 47 128 (by decide)

/-- **Newton, `p_2`:** `p_2 = −2 e_2`. -/
theorem order4_newton_p2 : q2 ≈ (-(Q'.ofNat 2)) * e2_4 := by decide
/-- **Newton, `p_4`:** `p_4 = −e_2 p_2 − 4 e_4`. -/
theorem order4_newton_p4 : q4 ≈ (-(e2_4 * q2)) + (-(Q'.ofNat 4 * e4_4)) := by decide
/-- **Newton, `p_6`:** `p_6 = −e_2 p_4 − e_4 p_2`. -/
theorem order4_newton_p6 : q6 ≈ (-(e2_4 * q4)) + (-(e4_4 * q2)) := by decide
/-- **Newton, `p_8`:** `p_8 = −e_2 p_6 − e_4 p_4`. -/
theorem order4_newton_p8 : q8 ≈ (-(e2_4 * q6)) + (-(e4_4 * q4)) := by decide

/-! The first-kind power sums `S_j = Σ_k T_j(x_k)` from the monomial expansions of `T_j`
substituting the Newton ordinary power sums (`p_0 = 4`):

    S_2 = 2p_2 − 4,
    S_4 = 8p_4 − 8p_2 + 4,
    S_6 = 32p_6 − 48p_4 + 18p_2 − 4,
    S_8 = 128p_8 − 256p_6 + 160p_4 − 32p_2 + 4. -/

/-- `S_2 = 2p_2 − 4`. -/
def Sc2 : Q' := Q'.ofNat 2 * q2 + (-(Q'.ofNat 4))
/-- `S_4 = 8p_4 − 8p_2 + 4`. -/
def Sc4 : Q' := (Q'.ofNat 8 * q4 + (-(Q'.ofNat 8 * q2))) + Q'.ofNat 4
/-- `S_6 = 32p_6 − 48p_4 + 18p_2 − 4`. -/
def Sc6 : Q' :=
  ((Q'.ofNat 32 * q6 + (-(Q'.ofNat 48 * q4))) + Q'.ofNat 18 * q2) + (-(Q'.ofNat 4))
/-- `S_8 = 128p_8 − 256p_6 + 160p_4 − 32p_2 + 4`. -/
def Sc8 : Q' :=
  (((Q'.ofNat 128 * q8 + (-(Q'.ofNat 256 * q6))) + Q'.ofNat 160 * q4)
    + (-(Q'.ofNat 32 * q2))) + Q'.ofNat 4

/-- **The order-4 power-sum collapse, EXACTLY** (the order-4 analogue of
`ChebDiscreteOrtho.order3_powerSum_collapse`): the even first-kind power sums all equal
`−1` and chain `S_2 = S_4 = S_6 = S_8`, by closed `Q'` computation on the Newton power
sums — RADICAL-FREE. -/
theorem order4_powerSum_collapse :
    Sc2 ≈ (-(1 : Q')) ∧ Sc4 ≈ (-(1 : Q')) ∧ Sc6 ≈ (-(1 : Q')) ∧ Sc8 ≈ (-(1 : Q'))
    ∧ Sc2 ≈ Sc4 ∧ Sc4 ≈ Sc6 ∧ Sc6 ≈ Sc8 :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-! ## 3. The order-4 rational profile and its located reduction

The Newton collapse certifies the rational profile `Sval4 j = −1` (`j` even) / `0`
(`j` odd) on `1 ≤ j ≤ 8`.  The order-4 instance of the general assembly reduces order-4
discrete orthogonality to the single located residual `LocatedRootPowerSums4`. -/

/-- The rational first-kind power-sum profile of the `U_4` roots on `j ≥ 1`:
`−1` (even `j`) / `0` (odd `j`).  (`S_0 = M = 4` is handled separately by `Sj0_eq_M`.) -/
def Sval4 (j : Nat) : Q' := if j % 2 = 0 then (-(1 : Q')) else (0 : Q')

/-- `Sval4 2 ≈ −1`. -/
theorem Sval4_two : Sval4 2 ≈ (-(1 : Q')) := by decide

/-- The rational shift `Sval4 p ≈ Sval4 (p+2)` for `0 < p ≤ 4 − 1 = 3`
(`S_1 = S_3`, `S_2 = S_4`, `S_3 = S_5`), the order-4 collapse certified above. -/
theorem Sval4_shift : ∀ p, 0 < p → p ≤ 4 - 1 → Sval4 p ≈ Sval4 (p + 2) := by
  intro p hp hp3
  match p, hp, hp3 with
  | 0, h, _ => exact absurd h (by omega)
  | 1, _, _ => decide
  | 2, _, _ => decide
  | 3, _, _ => decide
  | (n + 4), _, h => exact absurd h (by omega)

/-- **The single order-4 located residual** (`Prop`).  The located `U_4` roots
`±(√5±1)/4` realize the Newton first-kind power sums `S_j = Sval4 j` on `1 ≤ j ≤ 8` — the
`M = 4` Vieta link, the order-4 analogue of `ChebDiscreteOrtho.LocatedRootPowerSums3`.
Unlike `M = 3` (where the node squares are rational, `s² = ½`), the `U_4` node squares
`(3 ± √5)/8` are irrational, so realizing this residual needs `√5`-located bookkeeping; it
is named, never `sorry`. -/
def LocatedRootPowerSums4 (D : ChebRootDataT 4) : Prop :=
  ∀ j, 1 ≤ j → j ≤ 8 → CReal.Equiv (Sj D j) (CReal.ofQ' (Sval4 j))

/-- **Order-4 discrete orthogonality collapse from the located residual.**  For any located
`ChebRootDataT 4` realizing the order-4 Newton profile, the all-order single-`U` moment
collapse `ChebOrthogonality.PowerSumCollapse D.toU` holds — via the general assembly with
the order-4 rational collapse `Sval4_two`/`Sval4_shift` (proved above, radical-free). -/
theorem order4_orthoCollapse_of_located (D : ChebRootDataT 4)
    (htval0 : ∀ k, CReal.Equiv (D.tval 0 k) CReal.cone)
    (h : LocatedRootPowerSums4 D) :
    ChebOrthogonality.PowerSumCollapse D.toU :=
  locatedCollapse_of_rationalShift (by decide) D htval0 Sval4
    (fun j hj1 hj8 => h j hj1 (by omega)) Sval4_two Sval4_shift

/-- **Order-4 discrete orthogonality diagonal value `(4+1)/2 = 5/2` from the located
residual.**  `Σ_{k<4} (1 − x_k²)·U_0(x_k)² = 5/2` at the located nodes `±(√5±1)/4` — the
order-4 normalization, reduced to `LocatedRootPowerSums4`. -/
theorem order4_diag_value_of_located (D : ChebRootDataT 4)
    (htval0 : ∀ k, CReal.Equiv (D.tval 0 k) CReal.cone)
    (h : LocatedRootPowerSums4 D) :
    CReal.Equiv (ChebOrthogonality.orthoSum D.toU 0 0)
      (CReal.ofQ' (Q'.mkPos ((4 : Int) + 1) 2 (by decide))) :=
  locatedDiag_of_rationalShift (by decide) D htval0 Sval4
    (fun j hj1 hj8 => h j hj1 (by omega)) Sval4_two Sval4_shift

/-! ## 4. The order-3 closure as the discharged instance of the same pattern

The order-3 located residual is already DISCHARGED unconditionally
(`ChebLocatedRoots.locatedRootPowerSums3` on the constructed `√½`-node datum
`rootData3`), so its orthogonality collapse is unconditional.  We surface it here as the
fully-closed companion of the order-4 reduction — the order-4 residual
`LocatedRootPowerSums4` is the next instance of this same located-Vieta pattern. -/

/-- **Order-3 discrete orthogonality collapse, UNCONDITIONAL** (re-export of
`ChebLocatedRoots.order3_discreteOrthogonality_collapse`): the discharged companion of the
order-4 reduction `order4_orthoCollapse_of_located`. -/
theorem order3_orthoCollapse_closed :
    ChebOrthogonality.PowerSumCollapse ChebLocatedRoots.rootData3.toU :=
  ChebLocatedRoots.order3_discreteOrthogonality_collapse

/-! ## 5. The continuum `MomentIntegralIdentity` residual, narrowed

The discrete collapse above is the finite Gauss shadow of the continuous `U`-weight
orthogonality `∫_{−1}^1 U_c U_d √(1−x²) dx = (π/2)δ_{cd}` (input #2).  Closing the
heat-kernel moment-integral residual `RiemannSOS.MomentIntegralIdentity` needs inputs #2
and #3 (Riemann convergence); input #1 — the Christoffel moment reproduction `m_s =
(s+1)a^{s(s+2)}`, i.e. that `R = ϑ₃·S`'s Chebyshev-`U` coefficients ARE `2a·m_s` — is
ALREADY PROVED, node-free.  We surface #1 and re-export the proved reduction. -/

/-- **Input #1, PROVED (node-free): the Christoffel moment reproduction.**  Re-export of
`RCoeffReproduction.rCoeff_eq_two_a_moment`: `r_c = 2a·m_c` with `m_c = (c+1)a^{c(c+2)}`,
via the exponent identity `(c+1)² = c(c+2)+1`.  This is the half of `MomentIntegralIdentity`
that is NOT the obstruction — the residual is narrowed to inputs #2 (continuous
`U`-orthogonality) + #3 (Riemann convergence). -/
theorem christoffel_moment_reproduction (a : Q') (c : Nat) :
    RCoeffReproduction.rCoeff a c ≈ (Q'.ofNat 2 * a) * RCoeffReproduction.aMoment a c :=
  RCoeffReproduction.rCoeff_eq_two_a_moment a c

/-- **All-order heat-kernel character Gram PSD, reduced to `MomentIntegralIdentity`.**
Re-export of `RiemannSOS.wilson_gramPSD_of_momentIntegral`: the SU(2) heat-kernel character
Gram `coneExp` is PSD at every order `N` given the single continuous residual
`MomentIntegralIdentity` (inputs #2 + #3, with #1 = `christoffel_moment_reproduction`
proved).  The discrete-orthogonality collapse closed above (orders 2, 3, and 4-reduced) is
its finite Gauss shadow. -/
theorem wilson_gramPSD_of_momentIntegral (t : Q') (ht : (0 : Q') ≤ t)
    (h : RiemannSOS.MomentIntegralIdentity (GramRed.wilsonMoments t ht))
    (N : Nat) (c : Nat → Q') :
    ExpPos.geRat (WilsonFunctional.coneExp t ht c N) 0 :=
  RiemannSOS.wilson_gramPSD_of_momentIntegral t ht h N c

end YMGap.Continuum.ChebGeneralOrtho

/-! ## What is PROVED vs NAMED-open (honest ledger)

**PROVED (axiom-clean, π-free, no explicit radicals).**
  * `rootBridge_of_locatedGen` / `locatedCollapse_of_rationalShift` /
    `locatedDiag_of_rationalShift` — the general-`M` (`M ≥ 1`) located-substrate assembly:
    a realized rational power-sum profile with rational collapse discharges
    `RootPowerSumBridge → TPowerSum → ChebOrthogonality.PowerSumCollapse` and the diagonal
    value `(M+1)/2`.  Abstract over `M` (the order-3-specific `rootBridge3_of_located`
    generalized).
  * `order4_newton_p2/p4/p6/p8` / `order4_powerSum_collapse` — the order-4 Newton–Vieta
    rational power sums and the EXACT first-kind collapse `S_2 = S_4 = S_6 = S_8 = −1`,
    radical-free (the order-4 analogue of `order3_powerSum_collapse`).
  * `Sval4_two` / `Sval4_shift` — the order-4 rational collapse facts feeding the assembly.
  * `order4_orthoCollapse_of_located` / `order4_diag_value_of_located` — order-4 discrete
    orthogonality (diagonal value `5/2`) REDUCED to the single located residual
    `LocatedRootPowerSums4`.
  * `christoffel_moment_reproduction` — input #1 of `MomentIntegralIdentity`, PROVED,
    node-free (re-export); `wilson_gramPSD_of_momentIntegral` — the proved reduction
    `MomentIntegralIdentity ⇒` all-order character Gram PSD.

**NAMED-open (the residuals).**
  * `LocatedRootPowerSums4` — "the located `U_4` roots `±(√5±1)/4` realize the Newton power
    sums `S_1,…,S_8`" (the `M = 4` Vieta link; needs `√5`-located bookkeeping, the node
    squares being irrational).  A `Prop`, never `sorry`.
  * `RiemannSOS.MomentIntegralIdentity` — the continuous heat-kernel moment-integral
    residual, narrowed to inputs #2 (continuous `U`-orthogonality) + #3 (Riemann
    convergence), with input #1 proved.

Axiom-gate: `[propext]` / `[propext, Quot.sound]`.  No `Classical.*`, no `sorry`/`sorryAx`,
no `native_decide`, no new axioms; `decide` only on closed `Q'`/`Nat`. -/

#print axioms YMGap.Continuum.ChebGeneralOrtho.rootBridge_of_locatedGen
#print axioms YMGap.Continuum.ChebGeneralOrtho.locatedCollapse_of_rationalShift
#print axioms YMGap.Continuum.ChebGeneralOrtho.locatedDiag_of_rationalShift
#print axioms YMGap.Continuum.ChebGeneralOrtho.order4_newton_p2
#print axioms YMGap.Continuum.ChebGeneralOrtho.order4_newton_p4
#print axioms YMGap.Continuum.ChebGeneralOrtho.order4_newton_p6
#print axioms YMGap.Continuum.ChebGeneralOrtho.order4_newton_p8
#print axioms YMGap.Continuum.ChebGeneralOrtho.order4_powerSum_collapse
#print axioms YMGap.Continuum.ChebGeneralOrtho.Sval4_two
#print axioms YMGap.Continuum.ChebGeneralOrtho.Sval4_shift
#print axioms YMGap.Continuum.ChebGeneralOrtho.order4_orthoCollapse_of_located
#print axioms YMGap.Continuum.ChebGeneralOrtho.order4_diag_value_of_located
#print axioms YMGap.Continuum.ChebGeneralOrtho.order3_orthoCollapse_closed
#print axioms YMGap.Continuum.ChebGeneralOrtho.christoffel_moment_reproduction
#print axioms YMGap.Continuum.ChebGeneralOrtho.wilson_gramPSD_of_momentIntegral
