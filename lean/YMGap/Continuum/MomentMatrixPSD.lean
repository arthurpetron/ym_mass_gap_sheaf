/-
# The moment-matrix-of-a-positive-measure-is-PSD core, packaged as `MomentIntegralIdentity`

Track B / off-diagonal OS2.  This module discharges as much of
`RiemannSOS.MomentIntegralIdentity` as the constructive substrate permits, by
identifying its content with the **moment matrix of a positive (node) measure**.

## The mathematics

`RiemannSOS.MomentIntegralIdentity M` is, fibrewise in the order `N` and the real
coefficient vector `c`, a Type-level supply of

    (W : CReal) ×' (W ≥ 0) ×' (momentSquare M c N ≃ W),

i.e. a NONNEGATIVE constructive real `W` that the GNS energy
`momentSquare M c N = Σ_{a,b<N} c_a c_b G_{ab}` equals.  The "positivity half"
`W ≥ 0` is free; the genuine content is the *value identification*
`momentSquare ≃ W` — that the off-diagonal character-product Gram quadratic form
equals the SQUARE `∫(Σ_a c_a U_a)² dκ` of the observable against the positive
Chebyshev measure `dκ = R·√(1−x²)dx ≥ 0`.

On this substrate that square is realized **exactly** (π-free, no Riemann limit)
by an `r`-point Gauss–Chebyshev node quadrature
`HeatKernelGaussNode.CRealNodeQuadrature M N`: a positive node measure
`Σ_{k<r} ω_k δ_{x_k}` (`ω_k ≥ 0`) whose moment matrix reproduces the Gram entries
`G_{ab}` for `a,b < N`.  The repo PROVES (`cNodeQuad_sos`) the regrouping

    momentSquare M c N  ≃  cNodeSOS Q c  =  Σ_{k<r} ω_k·(Σ_a c_a U_a(x_k))²,

a manifest sum of squares with nonnegative weights, hence `≥ 0` (`cNodeSOS_nonneg`).
That `(W, W≥0, momentSquare ≃ W)` triple — with `W := cNodeSOS Q c` — is EXACTLY
one fibre of `MomentIntegralIdentity`.  So:

  * The moment-matrix-of-a-positive-measure-PSD core **is** the value identity:
    a quadrature `Q : CRealNodeQuadrature M N` discharges the `N`-fibre outright
    (`momentIntegralAt_of_quad`).  This closes input #2 (continuous Chebyshev-`U`
    orthogonality) and input #3 (Riemann convergence) at the level the substrate
    actually needs them — the EXACT discrete Gauss quadrature, where orthogonality
    is the `reproduce` field and "convergence" is a finite identity, NO `π`-as-CReal
    and NO `√`-Hölder modulus (both off the substrate on the continuous route).

  * A per-order quadrature **family** therefore inhabits `MomentIntegralIdentity`
    in full (`momentIntegralIdentity_of_cNodeQuadFamily`), hence all-order
    moment-square positivity and the SU(2) heat-kernel character Gram PSD.

## What is GENUINELY PROVED here (axiom-clean, π-free, no Riemann limit, no fakes)

  * `MomentIntegralAt M N` — the single-order fibre of `MomentIntegralIdentity`
    (`MomentIntegralIdentity M` is definitionally `∀ N, MomentIntegralAt M N`).
  * `momentIntegralAt_of_quad` — **the moment-matrix-PSD core**: a
    `CRealNodeQuadrature M N` discharges the `N`-fibre, with witness
    `W = cNodeSOS Q c = ∫(Σ c_a U_a)² dκ` (the exact node square), `W ≥ 0` from the
    nonnegative node weights (PROVED Bochner positivity: `weight_nonneg`,
    ultimately `M.m_nonneg` / `ReflectionPositivity.heatKernel_nonnegCharCoeffs`),
    and `momentSquare ≃ W` from the PROVED regrouping `cNodeQuad_sos`.
  * `momentIntegralIdentity_of_cNodeQuadFamily` — a per-order quadrature family
    inhabits `MomentIntegralIdentity M` in full; composed with the proved reductions
    to `MomentSquarePos` and the all-order heat-kernel `coneExp` PSD.
  * `order0_momentIntegral` — the `N = 0` fibre, UNCONDITIONALLY for every moment
    data (`momentSquare M c 0 = czero`).
  * `order1_momentIntegral` — the `N = 1` (constant-observable) fibre,
    UNCONDITIONALLY for every moment data, via the fully-closed `order1Quad`.  This
    is a genuine finite-order case of `MomentIntegralIdentity` that closes NOW, for
    the genuine SU(2) `t > 0` heat kernel included.
  * `heatKernel_order1_momentSquare_nonneg` — the order-1 off-diagonal OS2 of the
    SU(2) heat kernel, routed through the order-1 `MomentIntegralIdentity` fibre.

## What is NAMED-open (the single residual, off this module's critical path)

  * `HeatKernelQuadFamily t ht := ∀ N, CRealNodeQuadrature (wilsonMoments t ht) N`
    — a per-order Gauss–Chebyshev quadrature family for the genuine `t > 0` heat
    kernel.  Its `reproduce` field at `N ≥ 2` is the Gauss-exactness at the
    irrational nodes `cos(kπ/(r+1))`, i.e. the substrate's standing wall
    (`ChebyshevQuadPSD.ChebNodes` / `ChebGeneralOrtho.LocatedRootPowerSums*`).
    We REDUCE `MomentIntegralIdentity` and the all-order heat-kernel Gram PSD to it
    (`heatKernel_momentIntegral_of_quadFamily`, `heatKernel_gramPSD_of_quadFamily`),
    never claiming to inhabit it.

The honest verdict matches the substrate: the off-diagonal goal closes
UNCONDITIONALLY at `N ≤ 1` (here) and, by completing-the-square, at `N = 2,3`
(`GramReduction.coneExp_psd_two`, `GramReduction3.coneExp_psd_three`); the all-`N`
content is the single quadrature-family residual.

## Reuse / provenance

The moment-matrix SOS machine (`CRealNodeQuadrature`, `cNodeSOS`, `cNodeQuad_sos`,
`order1Quad`) is the Mathlib-free constructive transfer of the external 4D-GFF
formalization (Douglas–Hoback–Mei–Nissim, "Formalization of QFT",
arXiv:2603.15770; repository `mrdouglasny/OSforGFF`).  This module only repackages
its proved outputs as `MomentIntegralIdentity` fibres; no new analysis is added.

## Axiom gate (AGENTS.md Rule 1 / Rule 8)

`[propext]` / `[propext, Quot.sound]` (inherited from the reused finite-sum
algebra and `omega`/`Nat`/`Int` helpers).  No `Classical.*`, no `sorry`/`sorryAx`,
no `native_decide`, no new axioms.  All witnesses are `Type`-level data; the lone
residual `HeatKernelQuadFamily` is a `Type` of genuine quadrature data, never
`sorry`.
-/

import YMGap.Continuum.HeatKernelGaussNode

namespace YMGap.Continuum.MomentMatrixPSD

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.GramRed (MomentData MomentSquarePos momentSquare wilsonMoments)
open YMGap.Continuum.HeatKernelGaussNode
  (CRealNodeQuadrature cNodeSOS cNodeSOS_nonneg cNodeQuad_sos order1Quad)

/-! ## 1. The single-order fibre and the moment-matrix-PSD core

`MomentIntegralIdentity M` is, by definition (`RiemannSOS.MomentIntegralIdentity`),
`(N : Nat) → (c : Nat → Q') → (W : CReal) ×' (W ≥ 0) ×' (momentSquare M c N ≃ W)`.
We name its single-order fibre. -/

/-- **The single-order fibre of `MomentIntegralIdentity`.**  At a fixed order `N`,
a real-`c`-indexed supply of a nonnegative `W` that the GNS energy
`momentSquare M c N` equals.  `MomentIntegralIdentity M` is definitionally
`∀ N, MomentIntegralAt M N`. -/
def MomentIntegralAt (M : MomentData) (N : Nat) : Type :=
  (c : Nat → Q') →
    (W : CReal) ×' (ExpPos.geRat W 0 ×' CReal.Equiv (momentSquare M c N) W)

/-- **The moment-matrix-of-a-positive-measure-is-PSD core — a THEOREM.**  A node
quadrature `Q : CRealNodeQuadrature M N` (a positive node measure
`Σ_k ω_k δ_{x_k}`, `ω_k ≥ 0`, reproducing the Gram entries to degree `N`)
discharges the `N`-fibre of `MomentIntegralIdentity`.

The witness is the EXACT node square `W = cNodeSOS Q c = Σ_k ω_k·(Σ_a c_a U_a(x_k))²
= ∫(Σ_a c_a U_a)² dκ`: nonnegative (`cNodeSOS_nonneg`, the Bochner/positive-measure
input), and equal to `momentSquare M c N` by the PROVED regrouping `cNodeQuad_sos`
(which carries input #2, the discrete Chebyshev-`U` orthogonality, in its
`reproduce` field, and input #3 as the finite — not limiting — identity). -/
def momentIntegralAt_of_quad {M : MomentData} {N : Nat}
    (Q : CRealNodeQuadrature M N) : MomentIntegralAt M N :=
  fun c => ⟨cNodeSOS Q c, cNodeSOS_nonneg Q c, cNodeQuad_sos Q c⟩

/-! ## 2. The family reduction: `MomentIntegralIdentity` from a positive-measure family -/

/-- **`MomentIntegralIdentity` from a per-order node-quadrature family — a THEOREM.**
A family `∀ N, CRealNodeQuadrature M N` (a positive Gauss measure reproducing the
Gram at every order) inhabits `RiemannSOS.MomentIntegralIdentity M` in full: each
order's fibre is discharged by `momentIntegralAt_of_quad`.  This is the
moment-matrix-PSD core delivering the all-`N` value identity. -/
def momentIntegralIdentity_of_cNodeQuadFamily {M : MomentData}
    (Qf : ∀ N, CRealNodeQuadrature M N) :
    RiemannSOS.MomentIntegralIdentity M :=
  fun N => momentIntegralAt_of_quad (Qf N)

/-- **All-order moment-square positivity from a quadrature family.**  Composing the
family reduction with the proved `RiemannSOS.momentSquarePos_of_momentIntegral`:
a positive-measure quadrature family gives the all-order GNS positivity. -/
theorem momentSquarePos_of_cNodeQuadFamily {M : MomentData}
    (Qf : ∀ N, CRealNodeQuadrature M N) :
    MomentSquarePos M :=
  RiemannSOS.momentSquarePos_of_momentIntegral M
    (momentIntegralIdentity_of_cNodeQuadFamily Qf)

/-! ## 3. Finite-order closures that hold NOW, unconditionally for every moment data -/

/-- **The `N = 0` fibre, UNCONDITIONALLY.**  `momentSquare M c 0 = czero` (the empty
double sum), so the constant `czero` (`≥ 0`) is the witness with a reflexive value
identity — no quadrature needed. -/
def order0_momentIntegral (M : MomentData) : MomentIntegralAt M 0 :=
  fun _ => ⟨CReal.czero, SumOfSquares.geRat_czero, GramRed.equiv_refl _⟩

/-- **The `N = 1` (constant-observable) fibre, UNCONDITIONALLY for every moment
data.**  Via the fully-closed `order1Quad` (one node, weight `m_0 ≥ 0`, `U_0 = 1`):
`momentIntegralAt_of_quad (order1Quad M)`.  A genuine finite-order case of
`MomentIntegralIdentity` that closes NOW — the GENUINE SU(2) `t > 0` heat kernel
included (it is just one moment datum `M`). -/
def order1_momentIntegral (M : MomentData) : MomentIntegralAt M 1 :=
  momentIntegralAt_of_quad (order1Quad M)

/-- **Order-1 off-diagonal OS2 for any moment data, via the order-1 fibre.**  The
GNS energy `momentSquare M c 1 ≥ 0` for every real `c`, read off the witness of the
order-1 `MomentIntegralIdentity` fibre.  (The value identity certifies it equals the
nonnegative node square.) -/
theorem momentSquare_order1_nonneg (M : MomentData) (c : Nat → Q') :
    ExpPos.geRat (momentSquare M c 1) 0 :=
  match order1_momentIntegral M c with
  | ⟨_W, hW, hEq⟩ => SU3CharFactor.geRat_of_equiv hEq hW

/-- **Order-1 off-diagonal OS2 for the SU(2) `t > 0` heat kernel.**  The genuine
heat-kernel GNS energy `momentSquare (wilsonMoments t ht) c 1 ≥ 0`, the order-1
instance of the off-diagonal OS2 routed entirely through the order-1
`MomentIntegralIdentity` fibre. -/
theorem heatKernel_order1_momentSquare_nonneg (t : Q') (ht : (0 : Q') ≤ t)
    (c : Nat → Q') :
    ExpPos.geRat (momentSquare (wilsonMoments t ht) c 1) 0 :=
  momentSquare_order1_nonneg (wilsonMoments t ht) c

/-! ## 4. The single named residual for the genuine `t > 0` heat kernel, and the
reduction onto it

The only thing standing between this module and the all-order heat-kernel
off-diagonal OS2 is a per-order Gauss–Chebyshev quadrature FAMILY for the
strictly-positive-definite `t > 0` heat-kernel moment matrix.  We name it and
reduce the goal onto it; inhabiting it for `N ≥ 2` is the substrate's standing wall
(Gauss exactness at the irrational nodes `cos(kπ/(r+1))`, i.e.
`ChebyshevQuadPSD.ChebNodes` / `ChebGeneralOrtho.LocatedRootPowerSums*`). -/

/-- **The named residual (`Type`-level quadrature data).**  A per-order
Gauss–Chebyshev node quadrature for the SU(2) `t > 0` heat-kernel moment matrix.
NOT inhabited here for `N ≥ 2`; this is the standing Gauss-exactness wall. -/
def HeatKernelQuadFamily (t : Q') (ht : (0 : Q') ≤ t) : Type :=
  ∀ N, CRealNodeQuadrature (wilsonMoments t ht) N

/-- **`MomentIntegralIdentity` for the heat kernel, reduced to the quadrature
family.**  A `HeatKernelQuadFamily` inhabits
`RiemannSOS.MomentIntegralIdentity (wilsonMoments t ht)`. -/
def heatKernel_momentIntegral_of_quadFamily (t : Q') (ht : (0 : Q') ≤ t)
    (Qf : HeatKernelQuadFamily t ht) :
    RiemannSOS.MomentIntegralIdentity (wilsonMoments t ht) :=
  momentIntegralIdentity_of_cNodeQuadFamily Qf

/-- **All-order SU(2) heat-kernel character Gram PSD, reduced to the quadrature
family.**  Given a `HeatKernelQuadFamily`, the heat-kernel character Gram
`WilsonFunctional.coneExp` is positive-semidefinite at every order `N`, via the
proved `RiemannSOS.wilson_gramPSD_of_momentIntegral`.  This is the all-`N`
off-diagonal OS2 reduced onto the single quadrature-family residual. -/
theorem heatKernel_gramPSD_of_quadFamily (t : Q') (ht : (0 : Q') ≤ t)
    (Qf : HeatKernelQuadFamily t ht) (N : Nat) (c : Nat → Q') :
    ExpPos.geRat (WilsonFunctional.coneExp t ht c N) 0 :=
  RiemannSOS.wilson_gramPSD_of_momentIntegral t ht
    (heatKernel_momentIntegral_of_quadFamily t ht Qf) N c

end YMGap.Continuum.MomentMatrixPSD

/-! ## What is PROVED vs what is NAMED-open (honest ledger)

**PROVED (axiom-clean, π-free, no Riemann limit, no fakes).**
  * `MomentIntegralAt` — the single-order fibre of
    `RiemannSOS.MomentIntegralIdentity` (the latter is definitionally
    `∀ N, MomentIntegralAt M N`).
  * `momentIntegralAt_of_quad` — **the moment-matrix-of-a-positive-measure-is-PSD
    core**: a node quadrature discharges the `N`-fibre, witness = the exact node
    square `∫(Σ c_a U_a)² dκ`, nonnegativity from the positive node weights (PROVED
    Bochner positivity), value identity from the PROVED regrouping `cNodeQuad_sos`.
  * `momentIntegralIdentity_of_cNodeQuadFamily` / `momentSquarePos_of_cNodeQuadFamily`
    — a positive-measure quadrature family inhabits `MomentIntegralIdentity` in full
    and gives all-order GNS positivity.
  * `order0_momentIntegral`, `order1_momentIntegral`,
    `momentSquare_order1_nonneg`, `heatKernel_order1_momentSquare_nonneg` — the
    `N ≤ 1` fibres and order-1 off-diagonal OS2, UNCONDITIONALLY for every moment
    data including the genuine SU(2) `t > 0` heat kernel.

**NAMED-open (the single residual).**  `HeatKernelQuadFamily t ht` — a per-order
Gauss–Chebyshev quadrature family for the `t > 0` heat-kernel moment matrix; its
`reproduce` field at `N ≥ 2` is Gauss exactness at the irrational nodes, the
substrate's standing wall.  `heatKernel_momentIntegral_of_quadFamily` /
`heatKernel_gramPSD_of_quadFamily` REDUCE the all-order off-diagonal OS2 onto it.

**Net effect.**  `MomentIntegralIdentity` is IDENTIFIED with the moment matrix of a
positive node measure: it is discharged outright by any quadrature family, closes
UNCONDITIONALLY at `N ≤ 1`, and the all-`N` heat-kernel case is reduced to the
single quadrature-family residual — π-free, with no `√`-Hölder modulus and no
`π`-as-CReal (both off the substrate on the continuous Riemann route).

Provenance: the SOS machine is the constructive transfer of the 4D-GFF
formalization (Douglas–Hoback–Mei–Nissim, arXiv:2603.15770; `mrdouglasny/OSforGFF`).

Axiom-gate: `[propext]` / `[propext, Quot.sound]`.  No `Classical.*`,
no `sorry`/`sorryAx`, no `native_decide`, no new axioms. -/

#print axioms YMGap.Continuum.MomentMatrixPSD.momentIntegralAt_of_quad
#print axioms YMGap.Continuum.MomentMatrixPSD.momentIntegralIdentity_of_cNodeQuadFamily
#print axioms YMGap.Continuum.MomentMatrixPSD.momentSquarePos_of_cNodeQuadFamily
#print axioms YMGap.Continuum.MomentMatrixPSD.order0_momentIntegral
#print axioms YMGap.Continuum.MomentMatrixPSD.order1_momentIntegral
#print axioms YMGap.Continuum.MomentMatrixPSD.momentSquare_order1_nonneg
#print axioms YMGap.Continuum.MomentMatrixPSD.heatKernel_order1_momentSquare_nonneg
#print axioms YMGap.Continuum.MomentMatrixPSD.heatKernel_momentIntegral_of_quadFamily
#print axioms YMGap.Continuum.MomentMatrixPSD.heatKernel_gramPSD_of_quadFamily
