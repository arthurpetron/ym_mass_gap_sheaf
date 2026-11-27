# Scale-time and inside/outside observers: brainstorm, filtered (YB-14 Phase 2, 2026-11-27)

**Scripts:** box-only, `/workspace/novel_paths/yb14/` (hk_curv.py, be_nogo_cert.py, z2_lmax.py, so3_split.py, be_opt.py); not committed (docs-only push).

**Label: exploratory. Ideas first (deliberately wide), then a hard filter. Nothing here is machine-checked
unless it points at an existing repo theorem by name. NOT gap evidence.**
Scoring = the project usefulness method: **V2** (is there a finite check?) → **V1** (does it move a bound on
the open chain?) → **V3** (is it a no-go that saves effort?). U(1) test on every item.

## A. The clocks in this project
| clock | parameter | exact semigroup? | who reads it |
|---|---|---|---|
| Euclidean transfer time | n (ticks), T = `completedTime` | **yes**: T(m+n) = T(m)T(n), self-adjoint (`completedInner_time_sum/_balance`); Markov in temporal gauge; RP | inside observer on one lattice |
| kinetic heat time | t = −ln w (unit S³), τ = −4 ln w | **yes**: f_w ⋆ f_w = f_{w²} (coefficientwise (w^{s(s+2)})² = (w²)^{s(s+2)}) | one link |
| RG / resolution time | step index n of schedule T; physical spacing a_n | **no**: block-spin maps are not a semigroup on measures; only inequalities between scales (`scaleChain_of_twoStepFactor`, spacing ρ_n) | an observer whose resolution changes |
| physical time | t_phys = n·a(w) | derived | outside observer (continuum) |
| modular (thermal) time | Tomita–Takesaki flow of the half-space algebra in the RP vacuum | yes, but not geometric on a lattice | observer confined to a half-space |

Two facts organise everything below:
1. **Time-decimation is exact, space-decimation is not.** An observer who reads every 2nd tick sees the
   kinetic kernel at nome w² *exactly*; the schedule's `∀n, wf*wf ≤ wc` says the coarse observer's heat time
   is *at most* the time-decimated one (t_c ≤ 2t_f), i.e. spatial blocking must make the coupling no weaker
   than pure time-decimation. All the difficulty of RG sits in the spatial (plaquette) half.
2. **The decorrelation clock slows down monotonically.** For y in the vacuum complement,
   G_n = B(y, T_{2n} y) is log-convex (repo: `completedInner_cauchySchwarz`, `completedInner_even_diagonal`,
   used in Step0's prefactor removal), so the per-tick decorrelation ratio G_{n+1}/G_n is *nondecreasing*
   in n: the effective mass m_eff(n) = ln(G_n/G_{n+1}) decreases to the gap. Short-time (UV) observation
   always sees faster decorrelation than the asymptotic (IR) one.

## B. Brainstorm (wide; 14 ideas, unfiltered)
1. Mass gap = exchange rate between the inside tick and the outside second: m = −ln r(w)/a(w).
2. RG time runs opposite to resolution; confinement = the coarse observer sees stronger coupling (w falls toward the IR along schedule T), so every resolution-changing observer eventually lands in a certifiable strong-coupling regime.
3. Bar induction: if every resolution path reaches a "secured" (certified) node, the fan theorem gives a *uniform* depth. Lean core does not supply FT, so the depth must be built explicitly.
4. Measurement = conditioning. Observing slice 0 conditions the future via the Markov/RP structure; the gap is the contraction rate of the conditioning map; Dobrushin influence is "how much what I saw at 0 constrains what I will see at n".
5. Finite-volume conditional data suffices: Dobrushin–Shlosman ("constructive criterion for uniqueness", 1985): one finite-box inequality ⇒ uniform decay in all volumes.
6. Page–Wootters: on the time-periodic torus the global state is stationary (no outside time); time is relational (correlate the system with a clock register). Wrap-around: G(n) = G(N−n).
7. Effective mass monotone (A.2): data give only *upper* bounds on the gap; MC Creutz/effective-mass values overestimate (seen in `spacing_recheck.md`: χ(2,2) drifts down at 0.779).
8. Constructive location: inf of a monotone sequence is not located without a modulus (it would decide LPO-type questions). So the gap as a real is generally not computable from effective masses; a positive *floor* is the right constructive object (apartness m # 0 with a witness), which is what the repo states.
9. Brouwer continuity: any statement about the continuum (W → ∞, N → ∞, steps → ∞) that an inside observer can verify depends on a finite initial segment plus a modulus ⇒ width-uniformity is not optional constructively; infinite-volume limits must be Cauchy-with-modulus, not compactness (Prokhorov/Banach–Alaoglu use choice).
10. Thermal time: the half-space observer's natural flow is modular; Bisognano–Wichmann makes it a Euclidean rotation about the reflection plane — not available on a hypercubic lattice (only π/2 rotations).
11. Θ as Euclidean modular conjugation; the RP cone {Θ(F̄)F} is the natural positive cone; T positivity-improving ⇒ Perron–Frobenius ⇒ unique vacuum and a *finite-volume* gap (not uniform).
12. Non-abelian edge modes: across a cut each link contributes log(2j+1) to the vacuum's entanglement (zero for U(1)).
13. Curvature as the cutoff observer's private clock: Ric = ½ (radius-2) is the lattice electric Casimir seen in W₁; it is O(g²a²) in continuum variables, invisible to the outside observer.
14. Centre (Z₂) as the frustration of the clock: the configurations that destroy uniform curvature are exactly the centre-vortex sheets (plaquettes = −1); splitting SU(2) = SO(3) × Z₂ moves all fundamental-rep difficulty into the vortex sector.

## C. Filtered: the 6 that survive, with lemma, U(1) test, score
| # | idea | concrete candidate | U(1) | V2 | V1 | V3 | verdict |
|---|---|---|---|---|---|---|---|
| **C1** | conditioning / finite-volume data (B4, B5) | **TB-DOB**: time-weighted block Dobrushin with blocks = slabs of thickness h; if sup_ℓ Σ_{ℓ'} C^{(h)}_{ℓℓ'} e^{m·Δt} ≤ θ < 1 then `CentredPowerDecayVC` at rate e^{−m}. Plus **DOB-NEU** (finite-matrix Neumann bound, Lean-easy) as its combinatorial core | U(1)-true | yes in principle (MC for typical; worst case needs a certificate) | the only finite-computation route known to us that could reach step 2 (w = 1/2) | — | **highest priority framework**; DOB-NEU → Prover |
| **C2** | no compactness (B3, B9) | **GRID-SUP**: an explicit-Lipschitz function on S³ bounded on a rational δ-net is bounded everywhere (constructive replacement for sup over compact boundary-condition space); needed to put the 1119 κ-certificate (`hDobW1_OPEN`) into Lean. **DOB-CAUCHY**: under DOB-NEU, finite-volume expectations of a local observable form a Cauchy sequence in the volume with modulus C·r^{dist} (constructive infinite-volume limit) | U(1)-true | yes | GRID-SUP: on the critical path of step 1's `hDobW1_OPEN`; DOB-CAUCHY: future W → ∞ object | — | CANDIDATE; medium |
| **C3** | monotone decorrelation clock (A.2, B7, B8) | **PW-CONVEX**: on the time-periodic torus, n ↦ Tr(T^{N−n} F T^n F) is log-convex for PSD T and self-adjoint F (from P4 `FiniteTransferTrace` trace CS). Consequences: effective masses are upper bounds on the gap; a gap *floor* cannot come from any finite set of correlator values alone | U(1)-true | yes (Lean, finite matrices) | none | **yes**: rules out "certify the gap from finite MC/effective-mass data" | CANDIDATE, low-medium; honesty tool |
| **C4** | exact time-decimation vs inexact RG (A.1) | **TIME-DEC**: `coeffW` at w² equals the coefficientwise square of the normalised `coeffW` at w, and the strong-tier relation wf² ≤ wc ⇔ t_c ≤ 2t_f. Docs-level clarification of what each schedule step must prove (spatial blocking only) | U(1)-true | trivial | none directly | — | adopt as a docs note; Lean optional (trivial) |
| **C5** | curvature = cutoff clock; centre = frustration (B13, B14) | **SO3-BE** (adjoint-part slab measure has Γ₂ ≥ K > 0 at w = 1/2; Phase-4 numerics) + **Z2-VORTEX** (W-uniform decay of the Z₂ vortex sector with activities ≤ f_o/f_e) ⇒ step 2. Also the V3 statement: no curvature bound is uniform along AF | SO3-BE **U(1)-false** (U(1)/Z₂ ≅ U(1), Ric = 0); Z2-VORTEX U(1)-analogous | numerics yes | possible for step 2 only if Z2-VORTEX holds; unknown, Dobrushin for the Z₂ sector fails (18·0.48 ≫ 1) | yes (AF no-go) | CANDIDATE; the only genuinely non-abelian lead, but the hard part is relocated, not removed |
| **C6** | modular vs transfer time (B10–B12) | Θ ↔ modular conjugation; Perron–Frobenius finite-volume gap; edge entropy Σ⟨log(2j+1)⟩ | PF U(1)-true; edge term U(1)-false | partly | **none** (finite-volume gaps are never uniform; edge entropy is not a rate) | — | **vacuous for the gap**; recorded, not pursued |

Dropped as restatements of existing repo structure: B1 (= `floor_physical`, r3Rho), B2/B3 (= schedule T + strong-tier certificates), B8/B9 as *lemmas* (they justify the existing design: rational floor, ∀W uniform constants).

## D. What this implies intuitionistically (the synthesis)
1. **The mass gap is a rate witness, not a number.** Constructively one proves `∃ q > 0` (a rational floor) with a uniform modulus; the gap itself (an infimum of monotone effective masses) is not located in general. The repo already states the floor (≈ 0.0177 in physical units).
2. **Inside observers can only refute, not certify, from finite data** (C3): any finite set of correlator values gives upper bounds on the gap. A *certificate* must be a finite inequality whose truth implies a uniform statement — Dobrushin(-Shlosman) type (C1). This is the precise sense in which "finite-volume conditional data" can suffice.
3. **Every sup over a compact configuration space must carry an explicit modulus** (C2). This is exactly what the 1119 κ-certificate did numerically; Lean needs GRID-SUP.
4. **Uniformity in width/volume is forced** (B9): it is the constructive substitute for compactness-based infinite-volume limits.
5. **Non-abelian content lives where the clocks disagree**: the cutoff observer's curvature clock (U(1) has none) only seeds the strong end; past the U(1) transition (step 4) an outside-scale mechanism is required (multiscale), and the centre/vortex sector is where uniform methods break (C5).

## E. Work-plan consequences (added to work_plan.md)
- Prover queue: DOB-NEU (critical path of `hDob_OPEN`/`hDobW1_OPEN`), then GRID-SUP.
- Math queue: TB-DOB/DS feasibility at w = 1/2 (MC estimate of typical block influence first, V2), SO3-BE numerics (Phase 4), Z2-VORTEX feasibility.
- Docs: TIME-DEC note; PW-CONVEX as honesty lemma (optional Lean, reuses P4).
