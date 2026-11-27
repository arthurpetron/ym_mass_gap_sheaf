# SCOPE: Bakry–Émery / Ollivier curvature for the interacting slab (YB-14 Phase 1, 2026-11-27)

**Scripts:** box-only, `/workspace/novel_paths/yb14/` (hk_curv.py, be_nogo_cert.py, z2_lmax.py, so3_split.py, be_opt.py); not committed (docs-only push).

**Label: paper analysis + box numerics (exact-rational where stated). No Lean. NOT gap evidence.**
Base: origin/main 78fec11b. Builds on `novel_paths/w2_w27_hand.md` (free-link W2/W27).
Carrier: the repo's temporal-gauge slab measure (`steps01_uniform.md` §1):
μ ∝ Π_t Π_{spatial p} f_w(U_{p,t}) · Π_{t,ℓ} f_w(U_{ℓ,t} U_{ℓ,t+1}⁻¹) · Haar,
f_w = Σ_s (s+1) w^{s(s+2)} χ_s (repo `coeffW`). Each spatial link: ≤ 4 spatial plaquettes + ≤ 2 kinetic factors.

## 0. Verdict (one paragraph)
Configuration-uniform curvature (Bakry–Émery Γ₂, hence also the Ollivier route through it) **fails for the
interacting slab already at step 1 (w = 7/20), and at steps 2, 3, 4 by factors 5–80.** The threshold is
**w\* ≈ 0.304 (u\* ≈ 0.028)** in a long slab (λ = 16) and 0.332 for a single spatial slice (λ = 12). This is
*below* the repo's existing reach (TV-Dobrushin 0.2418 < **BE 0.304** < W₁-Dobrushin 0.367–0.401 ideal), so
curvature adds nothing to the strong tier. The free-link w⁸ pass at steps 2–3 (`w2_w27_hand.md`) is a
property of the **non-interacting** kernel only. The obstruction is exact and elementary: at the centre
configuration (every plaquette and kinetic factor = −1, the π-flux × time-staggered field) the action
Hessian is φ''(π)·Q with φ''(π) < 0 and λ_max(Q) = 12 + 2 + 2cos(π/N) → 16.

## 1. Dictionary (from the repo; exact)
- `coeffW w s = (s+1)·w^{s(s+2)}`, so u := c_{1/2}/(2c₀) = w³; Casimir C_j = j(j+1) = s(s+2)/4.
- Heat time: Casimir normalisation τ = −4 ln w (radius-2 S³, K = ½); **unit-S³ metric t = −ln w (Ric = 2)**.
  All numbers below use the unit metric (Ric = 2), the convention of Shen–Zhu–Zhu (SZZ) after rescaling.
- Wilson matches (for orientation only; the carrier is heat-kernel):

| step | fine w | u = w³ | β_W (char. match I₂/I₁ = u) | φ''(0) (Hessian at 1) | φ''(π) | K at centre config, λ=16 | λ=12 |
|---|---|---|---|---|---|---|---|
| 0 | 1/8 | 0.00195 | 0.0078 | 0.0078 | −0.0079 | **+1.87** | +1.91 |
| 1 | 7/20 | 0.0429 | 0.172 | 0.151 | −0.200 | **−1.20** | −0.40 |
| 2 | 1/2 | 0.125 | 0.505 | 0.388 | −0.764 | **−10.2** | −7.2 |
| 3 | 0.606841 | 0.2235 | 0.925 | 0.668 | −1.886 | **−28.2** | −20.6 |
| 4 | 0.779 | 0.4727 | 2.255 | 1.669 | −10.11 | **−159.8** | −119.3 |

(`novel_paths/yb14/hk_curv.py`; φ = −log f_w; min over ψ of both Hessian eigenvalues of the class
function is attained at ψ = π, so the centre configuration is the worst *diagonal* case.)

## 2. The no-go, precisely (V3; exact-rational certificate)
**Lemma NG-BE (paper, elementary).** Let g = ⊕_e c_e g_e be any product of bi-invariant metrics with
constant weights c_e > 0 on SU(2)^{links}. At the centre configuration Q₀ (all factors = −1; exists for
even spatial side, e.g. Q₀(x,μ,t) = (−1)^{x₁+…+x_{μ−1}+t}), every factor sits at ψ = π where ∇V = 0
and Ad = id, so Ric + Hess S = 2·I + φ''(π)·Q (unit metric per factor; Ric is scale-invariant), with
Q = temporal-gauge lattice d*d. Positivity of this tensor does not depend on the weights c_e. Hence
**no K > 0 exists** whenever 2 + λ_max(Q)·φ''(π) < 0.
- λ_max(Q): 12 (3D slice, staggered mode) + 2 + 2cos(π/N) (kinetic chain); numerically 15.8478 at
  L = 4, N = 8 (`z2_lmax.py`), = 14 at L = 2, N = 2 (cross-checked by `be_opt.py`, −0.8 at w = 7/20).
- **Exact-rational certificate** (`be_nogo_cert.py`, Fraction, 40 terms, tail < 10⁻¹⁷⁶):
  2F_π + λS'' < 0 with F_π = Σ(s+1)²(−1)^s w^{s(s+2)} > 0, S'' = Σ(s+1)²(−1)^s s(s+2) w^{s(s+2)}/3, at
  w ∈ {7/20, 1/2, 606841/10⁶, 779/1000} for both λ = 12 and λ = 15.847.
- Same mechanism for Wilson: λ_min(Hess) = −16β (SZZ normalisation: β_W < 1/8 is the ceiling); the
  heat-kernel action is *worse* near −1 because −log f_w has a deep concave maximum at the antipode.
- **U(1) test:** U(1) has Ric = 0, so BE fails for U(1) at every w. The no-go is a statement about a
  *method*; it is neither U(1) evidence nor non-abelian evidence.

## 3. Perturbative rescues tried (all fail at w = 1/2)
| rescue | quantity | w = 7/20 | **w = 1/2** | 0.607 | verdict |
|---|---|---|---|---|---|
| single-link conditional BE (isometry: no bracket terms) | 2 + 6 φ''_min | +0.80 | −2.59 | −9.3 | fails ≥ step 2 |
| Holley–Stroock single link | ρ_s ≥ 3e^{−osc}, osc = 6 ln(f(1)/f(−1)) | 0.377 | 0.0053 | 1.3e−5 | then Zegarlinski needs Σ_j J_ij < ρ_s with 18 neighbours: hopeless |
| gauge-fixed (axial/tree) slice | centre config is gauge-equivalent to an axial one; spatial part alone has λ = 12 | fails | fails | fails | no gain (NG-BE survives) |
| one-link integration before BE (UNVERIFIED preprint, computoergosum "ym-onelink-bakry-emery", Mathlib Lean) | claimed β_W < √(2/27) = 0.272, method ceiling √(2/21) = 0.309 | — | needs 0.505 | 0.925 | fails even if correct |
| sharp ungauged ceiling (UNVERIFIED preprint, hexagonmath 2610.00341: inf λ_min = N/2 − 4dN|β|) | β_W < 1/(8d) | — | — | — | consistent with NG-BE |

Published anchor: Shen–Zhu–Zhu, *CMP* (arXiv 2204.12737): SU(N) BE for |β| < 1/(16(d−1)) ⇒ uniform LSI,
uniqueness, exponential decay (mass gap) at strong coupling. Read: abstract/intro/assumption 1.1 and §4
statements (not every proof line). The two preprints: claims and theorem statements read; proofs not audited.

## 4. One surviving non-abelian candidate: the SO(3) × Z₂-vortex split (CANDIDATE, OPEN)
Write U = σ·Ũ(R) (R ∈ SO(3), σ ∈ Z₂ lift). Then f = f_e + f_o (even/odd spins), f(U_p) = f_e(R_p) +
σ_p f_o(R_p), |f_o| < f_e, and exactly
μ_SO(3)(dR) ∝ Π_p f_e(R_p) · Z_{Z₂}(t(R)), t_p = f_o/f_e ∈ (−1,1), Z_{Z₂} = Σ_{closed Z₂ surfaces} Π t_p.
- The **adjoint part** −log f_e has curvature defect only O(9w⁸) (first even character s = 2), not O(4w³):

| w | min Hess(−log f_e) (at ψ = π/2) | K centre-type (λ=16) | K crude config-uniform (20h + 14 sup|φ'|) |
|---|---|---|---|
| 7/20 | −0.0054 | +1.91 | +1.85 |
| **1/2** | −0.0949 | **+0.48** | −0.55 (inconclusive) |
| 0.607 | −0.466 | −5.5 | −10.3 |

- **But** all the fundamental-rep coupling moves into the Z₂ vortex sector, with plaquette activity
  t_p up to f_o/f_e(1) = 0.48 at w = 1/2 (0.77 at 0.607, ≈ 1 at 0.779): a random-coupling 4D Z₂ gauge
  model near/above its transition (tanh β_c ≈ 0.414). Dobrushin for σ needs 18|t| < 1. So the split
  **relocates** the difficulty; it does not remove it. Also −Hess log Z_{Z₂} = −E[Hess h] − Var(∇h)
  adds negative curvature proportional to the vortex susceptibility.
- U(1) test: U(1)/Z₂ ≅ U(1) has Ric = 0 ⇒ the "adjoint curvature" half is **U(1)-false (genuinely
  non-abelian)**; the Z₂ half is U(1)-analogous. Literature: Mack–Petkova, Tomboulis (2007 claim, not
  accepted) — status UNVERIFIED for any rigorous use.
- **Phase-4 numerics (heuristic search, `be_opt.py`)**: λ_min(Ric + Hess S_e) minimised over configurations
  of a periodic L³ × N temporal-gauge slab by seeded random local search (seeds: all plaquettes at ψ ≈ π/2;
  validated on the full action, where the search recovers the π-flux value −0.79 vs exact −0.80 at w = 7/20).
  Found minima are **upper bounds** on the true infimum, so positive values are *not* proofs:

| w | lattice | best λ_min found (SO(3) part) | reading |
|---|---|---|---|
| 1/2 | L=2,N=2 (15 restarts) | **+1.09** | consistent with SO3-BE at step 2 (unproved) |
| 1/2 | L=4,N=2 (3 restarts) | +1.18 | same |
| 0.55 | L=2,N=2 | +0.15 | marginal |
| 0.606841 | L=2,N=2 | **−1.92** | **SO3-BE fails at step 3** (numerical witness; exactness not checked) |

  So the adjoint half reaches step 2 at best, never step 3, and the full SU(2) measure still needs Z2-VORTEX.

## 5. What step 4 (w = 0.779) needs beyond Ricci
1. **Any configuration-uniform curvature/Dobrushin method is dead there by ~2 orders of magnitude**
   (K = −160; f(−1)/f(1) = 0.0088; vortex activity ≈ 0.996). Step 4 is past the matched-U(1) transition,
   so a proof is non-abelian content by definition.
2. Structural reason (V3, docs-level): group curvature is a **cutoff-scale** effect. With U = exp(a g A),
   Ric of SU(2)^{links} in the A-coordinates is O(g²a²); it is the lattice electric-Casimir gap
   (Kogut–Susskind g²C/2a) seen through W₁, and it vanishes in the continuum. A volume-uniform K > 0 with
   finite-range interaction gives a correlation-length bound ξ_lat ≤ F(β, K) that is finite at each
   coupling, while AF forces ξ_lat → ∞ (exponentially in 1/g²). So a curvature bound can never be uniform
   along AF; at best it seeds the strong end of the schedule (and NG-BE says: only below w ≈ 0.30).
3. What is needed instead: a **non-uniform** (small-field/large-field) argument — curvature is positive
   on configurations whose plaquettes are near 1 (Wilson Hess = β cos ψ_p ≥ 0 there, and Ric = 2 adds
   to *all* directions, including the coexact modes where U(1) is massless), plus a large-field
   suppression and a multiscale (RG) transfer — i.e. Balaban-type control, or a computer-assisted
   **finite-box Dobrushin–Shlosman** certificate at w = 0.779 (ξ_glue ≈ 0.5–2 lattice units, box side
   ≳ 8: far beyond present certificate technology). Neither exists in the repo; no convergent method is
   known past the U(1) transition.

## 6. Lean-able lemma statements (constructive, ℚ, no Classical.choice) and map to open hypotheses
| id | statement (Lean shape) | status | U(1) | maps to |
|---|---|---|---|---|
| **NG-BE-ℚ** | `∀ w ∈ {7/20,1/2,606841/10⁶,779/1000}, 2·Fpi w 40 + λ·Spp w 40 + tailBound < 0` (decide on truncated sums + explicit geometric tail) | CANDIDATE (pure arithmetic; geometric half is paper) | n/a (method no-go) | documents that `hfine_T2_half_OPEN`, `hfine_T3_6068_OPEN`, `hfine_T4_779_OPEN` cannot be discharged by uniform BE; low priority |
| **DOB-NEU** | finite index set, `C ≥ 0`, metric `d` (ℕ-valued, triangle), `r ∈ (0,1]`: `(∀i, Σ_j C i j * r^{-d i j} ≤ α) → ∀k i j, (C^k) i j ≤ α^k * r^{d i j}`; hence `Σ_k (C^k) i j ≤ r^{d i j}/(1−α)` | CANDIDATE, easy (≈150–300 lines) | U(1)-true infrastructure | combinatorial half of `hDob_OPEN` (Step0) / `hDobW1_OPEN` (Step1) — Theorem 3.1 weighted form of `steps01_uniform.md` |
| **SO3-BE** | Γ₂ for the adjoint-part slab measure ≥ K > 0 at w = 1/2 | OPEN (paper/numerics first; manifold calculus not in repo) | U(1)-false | would feed step 2 only together with **Z2-VORTEX** |
| **Z2-VORTEX** | W-uniform decay for the Z₂ gauge field with activities |t_p| ≤ f_o/f_e | OPEN, likely false at w=1/2 by Dobrushin; unknown otherwise | U(1)-analogous | step 2 (with SO3-BE) |
| **FREE-W1** | free-link heat-kernel W₁ contraction e^{−2t} = w² (Ollivier) | paper (Renesse–Sturm) | U(1)-false (U(1) κ ≡ 0) | non-interacting carrier only; **not** an `hfine` discharge |

Not proposed: `βLinkBound` (w³, spectral) — U(1)-true, previously overridden.

## Resources
All box jobs `prlimit --as=1 GiB`, `OMP_NUM_THREADS=1`, `python3 -P`; each < 5 s CPU, peak RSS < 60 MiB
(except `be_opt.py`, §6 of the Phase-4 log). Box had 16 GiB total, 5–13 GiB available during the runs.
