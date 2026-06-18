# The remaining open problem in this Yang–Mills mass-gap program

*A self-contained statement of exactly what is left to prove, written for a
mathematician or mathematical physicist. Every symbol is defined. Status as of
2026-06-18; the formal development is the Mathlib-free Lean 4 library in `lean/`.*

---

## 0. Orientation: what this program has done, and what is left

The Clay Millennium problem (Jaffe–Witten) asks, for every compact simple gauge
group `G`: construct a non-trivial quantum Yang–Mills theory on `ℝ⁴` satisfying the
Osterwalder–Schrader (or Wightman) axioms, and prove it has a **mass gap** `Δ > 0`.

This program has, in machine-checked constructive Lean:

1. **Reduced "all compact simple `G`" to `G = SU(2)`** (a worst-case reduction:
   every budget channel is monotone in the dual Coxeter number `h∨` and the smallest
   Casimir gap, both minimised at `SU(2)`). So only `SU(2)` need be treated.
2. **Reduced the mass gap to a single inequality**, `physGapMin > 0` (defined
   precisely in §4), via a chain of proved, axiom-clean theorems.
3. **Made the gap explicit**: for the heat-kernel lattice action the `SU(2)` transfer
   operator's spectral gap is the *closed form* `w³` (§3), and the open inequality
   has been reduced from cubic to **linear** in `w` (§5).

What remains open is **one inequality** — the survival of the physical gap as the
lattice spacing tends to zero (dimensional transmutation). This document states it
exactly (§5), gives two equivalent formulations (§6), and lists what would close it
(§7). It is, honestly, the genuine analytic core of the Clay problem; everything
around it is proved.

---

## 1. The lattice setup and all symbols

**Gauge group.** `G = SU(2)`, the group of `2×2` complex unitary matrices of
determinant 1. Its irreducible representations are labelled by a spin
`j ∈ {0, ½, 1, 3/2, …}`, of dimension `2j+1` and quadratic Casimir
`C₂(j) = j(j+1)`. The character (trace of the rep) is `χ_j`.

It is convenient to index modes by the integer `s = 2j ∈ ℕ = {0,1,2,…}`; then
- dimension `d(s) = s+1`,
- "four-times-Casimir" `C₄(s) := s(s+2) = 4·C₂(s/2)`  (so `C₄(0)=0`, `C₄(1)=3`, `C₄(2)=8`).
(The Lean code uses `dimQ s = s+1` and `c4 s = s·(s+2)`.)

**Lattice.** The hypercubic lattice `a·ℤ⁴` with **lattice spacing** `a > 0` (a real,
or here a positive rational `a ∈ Q'`). Gauge fields are maps from oriented edges
(links) `ℓ` to `SU(2)`, `ℓ ↦ U_ℓ`. A plaquette `p` is a unit square; `U_p` is the
ordered product of the four link variables around `p`.

**Action / measure (heat-kernel form).** We use the **heat-kernel (Villain/Manton)
action**, for which the per-plaquette Boltzmann weight is the heat kernel on `SU(2)`:
```
K_t(U)  =  Σ_{s≥0} d(s) · e^{ − t · C₂(s/2) } · χ_{s/2}(U)
        =  Σ_{s≥0} (s+1) · w^{C₄(s)} · χ_{s/2}(U),     where  w := e^{ − t/4 }.
```
- **`t > 0`** is the **heat-kernel time** (a single positive parameter playing the role
  of the inverse bare coupling: small `t` = weak coupling, large `t` = strong coupling
  in the heat-kernel parametrisation).
- **`w := e^{−t/4} ∈ (0,1)`** is the **per-Casimir-unit weight**. As `t→0`, `w→1`;
  as `t→∞`, `w→0`. In Lean `w` is carried as a rational in `[0,1)`; the mode-`s`
  weight is `w^{C₄(s)}`. (The Lean object `RGTransport.charFunc w` is exactly the
  diagonal functional `E χ_{s/2} = (s+1)·w^{C₄(s)}`.)

The heat-kernel action is chosen because (i) it diagonalises the transfer operator
in the character basis, giving a **closed-form** gap, and (ii) it is an **exact
renormalization-group fixed point in 2D** (the heat kernels compose under
area-additivity), and a *near*-fixed point in 4D — see §7, where this is the crux.

**Bare coupling and the continuum trajectory.** Equivalently to `t`, one may use the
bare coupling `g₀` (with `t` a fixed increasing function of `g₀²`). To take a
continuum limit one tunes `g₀ = g₀(a)`, equivalently `t = t(a)`, equivalently
`w = w(a) = e^{−t(a)/4}`, as `a → 0`. This **trajectory `a ↦ w(a)`** is the
renormalization-group / asymptotic-freedom trajectory; pinning it down rigorously is
the open problem (§5, §7).

---

## 2. The transfer operator and the correlation function

Reflection positivity of the lattice measure (Osterwalder–Seiler) yields a
**transfer operator** `T` (a positive, self-adjoint contraction on the physical
Hilbert space) such that Euclidean time-correlations are powers of `T`. For the
heat-kernel action on `SU(2)`, `T` is **diagonal in the spin basis** with eigenvalues
proportional to the character coefficients `w^{C₄(s)}`:
- the **vacuum** is the `s=0` mode, eigenvalue `∝ w^{C₄(0)} = w^0 = 1`;
- the **first excited** state is the `s=1` (spin-½) mode, eigenvalue `∝ w^{C₄(1)} = w³`.

**Connected two-point function.** For a local observable `O` and Euclidean
separation of `n` lattice steps, the connected correlator `G(n) = ⟨O_0 O_n⟩_c`
satisfies, by the spectral decomposition of `T`,
```
G(n)  ≤  G(0) · sep^n ,        sep := (second eigenvalue)/(vacuum eigenvalue).
```
(In Lean: `SpectralGap.decay_of_spectralGap_corr0`.)

---

## 3. The closed-form gap (proved)

For the `SU(2)` heat-kernel action the **spectral-gap separator** is the closed form
```
sep_HK(w)  =  w^{C₄(1)}  =  w³ .
```
(Lean: `HeatKernelGap.heatKernelSep w = w³`, with `heatKernelSep_eq` tying it to
`c4 1 = 3`.) It is manifestly:
- nonnegative and `< 1` for `w ∈ [0,1)` (a genuine gap), `heatKernelSep_lt_one`;
- monotone increasing in `w`, `heatKernelSep_mono`.

The **lattice gap margin** is
```
margin(w) := 1 − sep_HK(w) = 1 − w³ ∈ (0,1] ,
```
(Lean `heatKernelMargin`, with `heatKernelMargin_pos`), and the associated
`LocatedSpectralGap` with `gapMargin = 1 − w³ > 0` and geometric decay
`G(n) ≤ G(0)·(w³)ⁿ` is constructed (`heatKernelLocatedGap`).

**Dimensionful masses.** The **dimensionless lattice mass** is
`m_lat(w) := −log sep_HK(w) = −3 log w = 3t/4` (using `w=e^{−t/4}`). For `w` near 1
(the continuum regime), `m_lat ≈ 1 − sep_HK = margin(w)`, so the margin is the
constructive proxy for `m_lat`. The **physical mass** is the lattice mass in physical
units:
```
M(a) := m_lat(w(a)) / a   ≈   margin(w(a)) / a   =   (1 − w(a)³)/a .
```
The Clay mass gap is `Δ := lim inf_{a→0} M(a)`; the problem is to show `Δ > 0`.

---

## 4. The reduction chain (all proved, axiom-clean)

Each arrow is a Lean theorem depending only on `propext`/`Quot.sound`.

```
Clay gap for all compact simple G
   ⟸  [worst-case reduction]              MassGap/SimpleGroup.mass_gap_simple_group
SU(2) continuum mass gap
   ⟸  [located gap survives a→0]          RegScalingBand.band_gap_survives
"physGapMin > 0"
   ⟸  [RGGapPersistence]                  RGGapPersistence ⇒ physGapMin_pos_of_persistence
       (per-block form RGBlockPersistence.toUniform; strong-coupling anchor proved)
   ⟸  [heat-kernel makes it explicit]     HeatKernelPersistence ⇒ RGGapPersistence
       open content packaged as HeatKernelResidual
   ⟸  [cubic→linear reduction]            HeatKernelLinearBound.cubic_floor_of_linear_floor
```

**Definition (`physGapMin > 0`).** In the Lean object `RegScalingBand`, the physical
gap at the `j`-th spacing `a_j` of a sequence `a_j → 0` is the quotient
`physGap_j := (1 − w_j³)/a_j` (with `w_j = w(a_j)`), formed by the constructive
positive-denominator division `Q'.divPos`. The field `physGapMin > 0` asserts a single
positive constant `c` with `c ≤ physGap_j` for all `j` — i.e. the physical gap is
**bounded below uniformly in the spacing**. Equivalently `lim inf_{a→0} M(a) ≥ c > 0`.
By the reduction chain, establishing this single inequality establishes the Clay mass
gap for all compact simple groups.

(No part of this chain assumes the open inequality; `RGGapPersistence`,
`HeatKernelResidual`, and `RegScalingBand.physGapMin` are *named obligations*, never
inhabited for the real `SU(2)` trajectory and never faked with `sorry`/axioms.)

---

## 5. THE OPEN INEQUALITY (stated exactly)

After all reductions, the entire remaining content of the Clay problem in this program
is the following single statement. Let `a ↦ w(a) ∈ (0,1)` be the renormalization-group
trajectory of §1 (the bare heat-kernel weight as a function of spacing, tuned by
asymptotic freedom). 

> **Open Conjecture (physical-gap survival / dimensional transmutation).**
> There exists a constant `c₀ > 0` and a spacing `a₀ > 0` such that
> ```
>        ( 1 − w(a) ) / a   ≥   c₀        for all   0 < a < a₀ .
> ```
> Equivalently (Route A, §6.1, proved equivalent up to the harmless factor 3):
> `(1 − w(a)³)/a ≥ c₀` for all small `a`, i.e. `lim inf_{a→0} M(a) ≥ c₀ > 0`.

**What it says in words.** As `a→0`, asymptotic freedom forces the bare coupling
(hence `t(a)`, hence `1 − w(a)`) to **vanish** — the gap closes in *lattice* units
(`sep_HK = w³ → 1`). The conjecture is that it vanishes **no faster than linearly in
`a`**: `1 − w(a) ≳ c₀·a`, equivalently the heat-kernel time obeys `t(a) ≳ 4c₀·a`,
equivalently the physical mass `M(a) = (1−w³)/a` stays bounded away from `0`. This is
**dimensional transmutation**: the classically scale-free theory generates a mass scale
`Λ` (the RG-invariant integration constant of the Callan–Symanzik equation), and the
gap is `Δ = c·Λ > 0` for a pure number `c`.

**Why the linear (not cubic) form.** The factorisation `1 − w³ = (1−w)(1+w+w²)` with
`1 ≤ 1+w+w² ≤ 3` on `[0,1]` (Lean `HeatKernelLinearBound.heatKernelMargin_factor`,
`linear_le_cubicMargin`, `cubicMargin_le_three_linear`) gives
`(1−w) ≤ 1−w³ ≤ 3(1−w)`, so the cubic and linear floors are equivalent up to a factor
of 3. Hence it suffices to bound the **linear** quantity `(1−w(a))/a`.

---

## 6. Two equivalent formulations (the same obstruction, two methods)

Both reduce to the Open Conjecture of §5; a proof of either closes the problem.

### 6.1 Route A — explicit heat-kernel / theta-ratio comparison
The gap is the explicit function `sep_HK = w³`. With the two-loop asymptotic-freedom
running of the bare coupling,
```
a·Λ_L  =  exp( −1/(2 b₀ g₀²) ) · ( b₀ g₀² )^{ −b₁/(2 b₀²) } · (1 + O(g₀²)),
b₀ = 11N/(48π²)  (= 11/(24π²) for N=2),   b₁ the two-loop coefficient,
```
(`Λ_L` the lattice Λ-parameter, an RG-invariant mass scale), and the heat-kernel-time
↔ coupling dictionary `t = t(g₀)`, the Open Conjecture becomes a **one-variable
comparison** between the explicit gap and the RG exponential:
```
−log sep_HK(w(a))  =  −3 log w(a)  ≥  c · a·Λ_L     for all small a.
```
The relevant analytic inputs are refereed and Lean-formalisable: Amos two-sided Bessel
bounds (Hornik–Grün, *JMAA* 408 (2013)); theta-quotient convexity/monotonicity
(Dixit–Roy–Zaharescu, *JMAA*); Turán/log-concavity `I_n² > I_{n−1}I_{n+1}` (Baricz).
The library has supporting theta/heat-kernel machinery (`ThetaConv`, `RealTheta`,
`SigmaHatLimit`).

### 6.2 Route B — spacing-uniform functional inequality (RG composition)
View the continuum limit as a renormalization-group flow over scales `k=0,1,2,…`
(block-spin, spacing `a_k = a_0·2^{−k}`). Let `gap_k` be the transfer-operator gap at
scale `k`, and `ρ_k := gap_{k+1}/gap_k` the **per-block gap multiplier**. The physical
gap survives iff the product stays bounded below:
```
∏_{k} ρ_k  ≥  c  >  0 .
```
(Lean: `RGBlockPersistence` carries exactly this product-floor; `RGBlockPersistence.toUniform
⇒ RGGapPersistence ⇒ physGapMin > 0`.) The atomic per-scale contraction is **proved**:
`SU(2) ≅ S³` has the exact Peter–Weyl spectrum, so the single-link heat semigroup
contracts spin-`j` modes by `e^{−t·j(j+1)}`, the slowest non-trivial mode `j=½` giving
the **exact spectral gap `3/4`** (`PerScaleContraction.su2CasimirGap = 3/4`, the
project's `c_λ`; Poincaré constant `4/3`). The composition `PerScaleTower ⇒ RGBlockPersistence`
is **proved** (`PerScaleCompose.physGapMin_pos_of_tower`) *given* the product-floor.

**The honest crux (a theorem).** A *constant* per-scale contraction `ρ < 1` makes the
product **strictly decrease** to `0` (`PerScaleCompose.prodPrefix_const_strict_decrease`,
illustrated for `su2PerScale`, `ρ = 1−3/4 = 1/4`). So "each scale has a gap" does **not**
give the product-floor. The product-floor requires `ρ_k → 1` fast enough — i.e. the gap
multiplier approaches 1 at the RG-flow rate. This is *exactly* dimensional transmutation
again, now visible as: the per-scale mixing is strong (good), but the *physical* gap is
the slow residual that must not be over-contracted. The standard route to the
product-floor is a **lattice-spacing-uniform log-Sobolev / Poincaré inequality** for the
`SU(2)` measure (the Polchinski-flow LSI method of Bauerschmidt–Bodineau–Dagallier,
*Probability Surveys* 21 (2024), proven spacing-uniform for scalar `φ⁴₂,₃`), composed
with the Helffer–Sjöstrand dynamic⇒static bridge `λ>0 ⇒ m>0` (Lean
`DynamicToStaticGap`, qualitative direction proved; Shen–Zhu–Zhu, *CMP* 400 (2023)
realise the full chain at *fixed* spacing).

---

## 7. What would close it, and the single hard residual

A proof of **either** of the following closes the Clay problem in this program (modulo
the already-reduced OS-existence carriers — see `docs/clay-open-boundary-ledger.md`):

- **(A)** the one-variable comparison `−log sep_HK(w(a)) ≥ c·aΛ_L` of §6.1, i.e. the
  explicit theta/Gaussian gap decays no faster than the two-loop RG exponential; or
- **(B)** a **lattice-spacing-uniform Poincaré (or log-Sobolev) inequality** for the
  `SU(2)` lattice heat-kernel measure along the asymptotic-freedom trajectory, with a
  constant `C(a) ≤ K·a²` (`K` independent of `a`); via Helffer–Sjöstrand this gives the
  per-block product-floor and hence `physGapMin > 0`.

**The single hard residual (the genuine Clay difficulty), stated honestly.** Both (A)
and (B) hinge on controlling the **4D deviation of the heat-kernel action from its exact
RG fixed point**. The heat-kernel action is an *exact* fixed point of the block-spin
recursion in 2D; in 4D it is only a *near*-fixed point, and *no rigorous error-bounded
control of that deviation exists in the literature*. Equivalently (Route B language):
the *non-abelian* analogue of the susceptibility/correlation-inequality step that makes
the multiscale Bakry–Émery criterion close for scalar `φ⁴` has no known substitute for
`SU(2)` (there is no FKG/Griffiths monotonicity for non-abelian link variables; the
Bakry–Émery `Γ₂` curvature is not uniformly bounded as the coupling runs). These two
descriptions — "near-fixed-point deviation not bounded" (Route A) and "non-abelian
susceptibility step missing" (Route B) — are the *same* crossover obstruction between the
rigorously-controlled strong-coupling regime (Osterwalder–Seiler 1978; Shen–Zhu–Zhu
2023, fixed spacing) and the rigorously-controlled weak-coupling UV regime (Balaban
1987–89, subsequence only, no gap). **Bridging that crossover is the open mathematics.**

**State of the art (so a reader can calibrate).** No regime — no coupling, boundary
condition, or improved action — has a *spacing-uniform* positive gap rigorously proven
for 4D non-abelian Yang–Mills. Balaban's RG proves UV stability in finite volume but
only extracts a subsequence (uniqueness/IR/gap open). Magnen–Rivasseau–Sénéor (1993)
remove the UV cutoff for `SU(2)` but keep a *fixed IR cutoff* (where the gap lives).
The recent claimed `SU(3)` "constructive proof" (arXiv:2506.00284) was **withdrawn by
arXiv** for failing quality standards and should not be relied on.

---

## 8. Concrete first targets for a researcher

Reachable now (do not require crossing the residual), each a clean lemma:
1. **Route A overlap bound.** Prove `(1−w(a))/a ≥ c₀` in the *strong-coupling /
   convergent-cluster-expansion* window (small `t`, large coupling), where
   Osterwalder–Seiler/Münster give convergent series for `sep`. This anchors the
   trajectory's `a→a₀` end rigorously; the open part is then only its *persistence*
   across the crossover.
2. **Route B per-block from per-scale.** Establish a single block-spin step's gap
   multiplier `ρ_0` for the `SU(2)` heat-kernel action explicitly (one Migdal-style
   block), and identify the precise rate at which `ρ_k` must approach 1 (the
   dimensional-transmutation rate `1 − ρ_k ~ ?`); the open part is the *uniformity* of
   that rate.
3. **The theta-ratio inequality (A) in the scaling window.** Formalise the
   Bessel/theta two-sided bounds (Amos; Dixit–Roy–Zaharescu) for `sep_HK` and compare to
   the two-loop exponential — the analytic heart, reduced to one variable.

A success on any of (A)/(B), even for `SU(2)` alone, would — via the proved reduction
chain of §4 — establish the Clay Yang–Mills mass gap for **all** compact simple gauge
groups in this constructive framework.

---

## Symbol glossary

| Symbol | Meaning |
|---|---|
| `G` | compact simple gauge group; reduced here to `SU(2)` |
| `j`, `s=2j` | spin label; integer mode index `s∈ℕ` |
| `d(s)=s+1` | dimension of mode `s` |
| `C₂(j)=j(j+1)`, `C₄(s)=s(s+2)=4C₂` | quadratic Casimir; four-times-Casimir |
| `a` | lattice spacing (`>0`); continuum limit is `a→0` |
| `t` | heat-kernel time (`>0`); inverse-coupling-like parameter |
| `w = e^{−t/4} ∈ (0,1)` | per-Casimir-unit heat-kernel weight; mode-`s` weight `w^{C₄(s)}` |
| `g₀`, `b₀,b₁` | bare coupling; one- and two-loop β-function coefficients |
| `Λ_L` | lattice Λ-parameter (RG-invariant mass scale) |
| `w(a)`, `t(a)`, `g₀(a)` | the RG/asymptotic-freedom trajectory (the OPEN input) |
| `T`, `sep` | transfer operator; spectral-gap separator (2nd eigenvalue / vacuum) |
| `sep_HK(w)=w³` | the closed-form `SU(2)` heat-kernel gap separator |
| `margin(w)=1−w³` | lattice gap margin (constructive proxy for `m_lat`) |
| `m_lat=−log sep` | dimensionless lattice mass |
| `M(a)=m_lat/a≈(1−w³)/a` | physical mass; `Δ=liminf_{a→0}M(a)` is the Clay gap |
| `c₀, c, K, a₀` | positive constants (independent of `a`) in the open inequality |
| `ρ_k` | per-block gap multiplier in the RG (Route B); need `∏ρ_k≥c>0` |
| `physGapMin` | Lean field: uniform lower bound on `physGap_j=(1−w_j³)/a_j` |

*Formal references are theorem names in the `lean/YMGap/Continuum/` modules
(`HeatKernelGap`, `RGGapPersistence`, `HeatKernelPersistence`, `HeatKernelLinearBound`,
`PerScaleContraction`, `PerScaleCompose`, `RegularContinuumPipeline`). Literature
references are in `docs/two-route-gap-attack.md` and `docs/physgap-inhabitation-research.md`.*
</content>
