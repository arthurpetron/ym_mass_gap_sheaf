# SCOPE — C1 SquareBoxDoubling (volume uniformity) — 2026-10-06 ~10:45 PM PT

Status: SCOPE NOTE ONLY (no Lean in this commit for C1). Labels: OPEN / packaging plan.

## 0. Prior references in the repo

Searched `lean/`, `audits/`, `docs/`, `work_plan.md` for `SquareBox`, `square box`,
`SquareBoxDoubling`, `Doubling`, `C1`, `torus`, `periodic`, `finite-size`, `Martinelli`,
`Family 215`.

* No `SquareBoxDoubling` (or any square-box doubling statement) exists. The only
  "square box" hit is `P2HalfTimeEndpointSupportCompiler.boxSum_top_endpointDirect`, a
  cutoff-square index box in a coefficient sum. It is unrelated.
* "Doubling" hits are time-doubling (`BoundedMidpointDoublingEventual.
  bounded_midpointDoubling_leEv_anchor`, `RationalTwoModeSurvivalObstruction`
  `response_doubling_upper`), not spatial box doubling.
* `BF4DyadicWilsonSquare*` (49 files) are PLANAR Wilson LOOPS of side `2^s` with
  `spacing s = half^s`. They are not boxes; the loop-specific constant
  `384·(2^s)^3·(1−w)` (file header) is not reusable for volume doubling.
* Finite-size criteria: `audits/RESEARCH-DEFECT-RETAINING-COLLECTIVE-ROUTE-2026-09-30.md`
  says "Refined inverse-square finite-size criteria are a separate possible route, not
  yet transferred to this carrier", and rejects the earlier `18/L − 3/L²` patch threshold
  as a necessary condition.
* `work_plan.md:49`: "Witness of `WilsonAFPaddedGapInput` on AF | OPEN (needs a
  weak-coupling, volume-uniform producer with `1−r_j ≍ 2^-j`)". This is the consumer.
* `work_plan.md` "## 215." is "global dependent recoupling column capacity" (2026-08-27).
  It is unrelated, and I found no "Family 215" read in the repo.

## 1. The doubling statement (target shape)

Finite-size doubling (Martinelli–Olivieri-type criterion, adapted to lattice gauge theory).
For boxes `Λ_L` of side `L` (in a torus of side `N ≥ 2L + pad`), with a per-box rate
`r(Λ_L) < 1`, the claim is: for every `L ≥ L0`,
`1 − r(Λ_{2L}) ≥ (1 − r(Λ_L))·(1 − ε_L)`, with `Π_k (1 − ε_{2^k L0}) ≥ c > 0`.
Iterating gives `1 − r(Λ_{2^k L0}) ≥ c·(1 − r(Λ_{L0}))` uniformly in volume. Seeding
then needs only ONE finite-box certificate, e.g. through the trace sandwich
(`SpectralTraceSandwich` / `SpectralHalvingMargin`).

In 4D, `Λ_L → Λ_{2L}` is a chain of `d = 4` one-direction doublings
(`L^4 → 2L·L^3 → … → (2L)^4`), each covering by two overlapping slabs. The loss `ε`
compounds 4 times per doubling (2D: 2 times). The analytic input for each step
(decoupling of the overlap at weak coupling) is the real content. It is OPEN, and no
existing Lean supplies it.

## 2. Torus / periodic layer: status

**Missing in Lean.** What exists:
* `ClusterCount4DProgress`: `Z4Vertex := Nat × Nat × Nat × Nat` ("corner-anchored"),
  `addE`, truncated `subE` (`subE_addE`), `Z4Link`, `Z4Plaq`, `Z4Plane`, `edgesOf`.
  Coordinates do not wrap.
* `Z4FiniteBoxExhaustion`: `boxVertices`, `boxPlaquettes`, `boxLinks` (FREE boundary),
  `boxVertices_length = n^4`, `boxPlaquettes_length = 6n^4`, `boxLinks_length = 24n^4`
  (boundary OCCURRENCES, with repetition), monotonicity, `CofinalFiniteZ4Exhaustion`,
  `z4BoxExhaustion`.
* `Z4FiniteBoxTrivalentResolution` (`distinctBoxLinks`, `incidentPlaqIds`): its header
  calls the boxes "cofinal periodic", but the definitions are the corner-anchored
  free-boundary boxes above. That wording is misleading.
* `Z4FiniteBoxIncidentDegreeBound.incidentPlaqIds_length_le_six`: `≤ 6` incident
  plaquettes (an upper bound only; boundary links have fewer).
* `Z4UniformShiftPhysicalTransport.uniformShiftLink` / `uniformShiftPlaquette`: positive
  translation by a padding (no wraparound).
* `SepLatticeZ4Linf.linfDist`, `Z4LinfShellCount.ball_count`
  (`≤ (2r+1)^4·6` faces in an ℓ∞ ball).
* Periodic only abstractly, and only in time: `ReferenceWeightTimeGeometry.
  GeometryEnrichedReferenceWeight` (`timeExtent`, `periodic` via `iterateTau`), with
  instances in `TwoSliceCharacterReflection` and `MultiSliceWilsonPositiveTimePilot`.
* The `BF4ExactSlab*` carriers are time-reflection slabs with an `extent` parameter, not
  spatial tori.

Needed: a spatial (and temporal) 4-torus with wraparound links and plaquettes, exact
incidence (every link in exactly 6 plaquettes for `N ≥ 3`), a translation group action,
and an embedding of free boxes `boxPlaquettes L` into the torus for `L + 1 ≤ N`.

## 3. Constants that are 2D- or cube-specific and must be re-derived in 4D

| Quantity | 2D value | 4D value | Where it lives now |
|---|---|---|---|
| plaquettes per link | 2 | `2(d−1) = 6` (exact on torus) | `incidentPlaqIds_length_le_six` (≤ only, free box) |
| plaquettes per site | 1 | `C(4,2) = 6` | `boxPlaquettes_length = 6n^4` |
| link occurrences per site | 4 | 24 | `boxLinks_length = 24n^4` |
| ℓ∞-ball face count | `(2r+1)^2` | `(2r+1)^4·6` | `Z4LinfShellCount.ball_count` |
| dyadic block growth | 4 | `16 = 2^4` | `Z4LinfGeometricSum.countCap` (`…*16`, `16·r^N ≤ 1/2`) |
| sub-boxes per doubling | 4 | `2^d = 16` | none (new) |
| one-direction doublings per step | 2 | 4 (loss compounds 4×) | none (new) |
| box boundary faces | `4L` | `2d·L^{d−1} = 8L^3` (cubes), ×6 planes for plaquettes | none (new) |
| overlap width / padding | rectangle `L×2L` | slab `L^3×2L`, padding for `uniformShift*` | `Z4UniformShift*` (padding only) |
| finite-size threshold | e.g. `18/L − 3/L²` (patch, rejected as necessary) | to be re-derived | `RESEARCH-DEFECT-RETAINING-COLLECTIVE-ROUTE-2026-09-30.md` |
| polymer / animal connectivity | — | 4D plaquette animals | `ClusterCount4DProgress`, `Z4CanonicalPolymer*` |

The `BF4DyadicWilsonSquare` loop constants (perimeter 4, `384·(2^s)^3`) are loop data,
not box data. The doubling step should not reuse them.

## 4. Dependencies on existing files

* Geometry: `ClusterCount4DProgress`, `Z4FiniteBoxExhaustion`,
  `Z4FiniteBoxTrivalentResolution`, `Z4FiniteBoxIncidentDegreeBound`,
  `Z4UniformShiftPhysicalTransport`, `SepLatticeZ4Linf`, `Z4LinfShellCount`,
  `Z4LinfGeometricSum`, `FiniteSizeGeometricSum`.
* Seeding and rate side: `SpectralTraceSandwich`, `SpectralHalvingMargin`,
  `BF4WilsonHalvingTimeMargin` (`WilsonAFPaddedGapInput` consumer),
  `BF4WilsonAllNomeWilsonDynamicFamily` (`WilsonDynamicFamily`, all-vector contraction).
* Not reusable as-is: `BF4DyadicWilsonSquare*` (loops), `BF4ExactSlab*` (time slabs,
  free spatial boundary).

## 5. Minimal first Lean milestone (finite and decidable, no analysis)

`Continuum/Z4TorusGeometry.lean`:
1. `TorusVertex N := Fin N × Fin N × Fin N × Fin N` (or Nat with `% N`), `torusAddE` and
   `torusSubE` with `torusSubE (torusAddE v m) m = v` exactly (wraparound, `0 < N`).
2. `torusLinks N`, `torusPlaquettes N`, with lengths `4N^4` and `6N^4` (distinct, Nodup).
3. Exact incidence: for `N ≥ 3`, every link lies in exactly 6 plaquettes (upgrading
   `incidentPlaqIds_length_le_six` from ≤ to =).
4. Translation action `torusShift` preserving incidence, plus the free-box embedding
   `boxPlaquettes L ↪ torusPlaquettes N` for `L + 1 ≤ N` (compatible with
   `Z4FiniteBoxExhaustion.mem_boxPlaquettes`).

Milestone 2 (pure `Q'` algebra, cheap): `SquareBoxDoubling` as a Prop on a scale-indexed
rate `r : Nat → Q'` (`1 − r (k+1) ≥ (1 − r k)(1 − ε k)`), and the iteration lemma
`Π (1 − ε) ≥ c ⇒ 1 − r k ≥ c (1 − r 0)`. Output in `WilsonLowerMargin` form.

Milestone 3 (OPEN, the real content): the per-step overlap-decoupling estimate for the
Wilson transfer on torus boxes at weak coupling, with 4D constants from §3.

## 6. Milestones 1 and 2: status (2026-10-06 PT)

Milestone 1 (`Continuum/Z4TorusGeometry.lean`, proved finite combinatorics, GENERAL `N`):
vertices are `boxVertices N` (Nat coordinates `< N`, `InBox N`); `tAdd`/`tSub` use
`(x+1) % N`, `(x+N−1) % N`; `tSub_tAdd`, `tAdd_tSub` exact on in-range vertices; `tSub_ne`
for `2 ≤ N`. `torusLinks_length = 4N⁴`, `torusPlaquettes_length = 6N⁴`, both Nodup.
`torus_link_incidence_eq_six`: for `2 ≤ N` (so for `N ≥ 3`) each torus link is on EXACTLY 6
plaquettes (two inclusions with the explicit 6-element `incidentPlaqs`, no enumeration).
Translation `tShift` (range, identity, composition, `tAdd_tShift`, `torusEdgesOf_shift`);
embedding `box_torusEdges_eq` (`L + 1 ≤ N` ⇒ `torusEdgesOf N p = edgesOf p`). Not done:
any measure, transfer matrix or reflection positivity on the torus.

Milestone 2 (`Continuum/SquareBoxDoublingIteration.lean`, REDUCTION): `doubling_iterate`
(`g k(1−ε k) ≤ g(k+1)`, `ε ≤ 1` ⇒ `g 0·Π_{i<k}(1−ε i) ≤ g k`), `slab_doubling_iterate`
(four slab steps per doubling, read at `4k`), `prodLoss_ge_one_sub_sumLoss`
(`1 − Σε ≤ Π(1−ε)`), `doubling_uniform_gap` (`Σ_{i<k} ε ≤ σ` ⇒ `g 0(1−σ) ≤ g k`). The
doubling inequality itself and summability of `ε` are OPEN.

## 7. Milestone 3 framing: the "proves too much" test

The test. Any proof of the per-doubling inequality `1 − r(2L) ≥ (1 − r(L))(1 − ε_L)`
with `Σ ε_L < 1` (at fixed weak coupling `β`, uniformly in `L`) that never uses the
structure of `SU(N)` applies verbatim to the 4D `U(1)` Wilson model. That model at weak
coupling (`β` above the deconfinement point) is in the Coulomb phase: a massless photon,
`⟨W(C)⟩` with perimeter law, and power-law (`|x|^{-4}`-type for plaquette observables)
correlations. Its vacuum-sector transfer gap on `L`-boxes closes like `~ 1/L` (lowest
photon momentum `2π/L`). So `1 − r(L) → 0`, and no summable `ε` can exist for `U(1)`.
A group-insensitive decoupling estimate therefore proves a false theorem.

Which step must fail for `U(1)`. With `1 − r(L) ~ c/L`, the doubling ratio is
`(1−r(2L))/(1−r(L)) ~ 1/2`, i.e. `ε_L ~ 1/2` for every `L`, not summable. The failing step
is the per-step overlap-decoupling bound itself: the claim that the cross-slab coupling
across the four slab interfaces costs only `ε_L → 0`. For `U(1)` the interface carries a
long-range (massless) Gaussian mode whose contribution does not decay with `L`. Any
estimate that bounds the interface coupling by local norms (`‖e^{-H}‖`, cluster
expansion, Kotecký–Preiss at the interface) without a group-dependent input must be
wrong at weak coupling, because those same tools are uniform in the gauge group.
(At strong coupling such estimates are fine and do hold for `U(1)` too; there `U(1)` has
a gap. That is consistent: the gap there comes from `β` small, not from the group.)

Where non-abelianness must enter (at least one is necessary):
1. Asymptotic freedom (sign of the one-loop β-function coefficient `b₀ = 11N/(48π²) > 0`
   for `SU(N)`; `b₀ < 0` / zero for `U(1)`). This is what makes the effective coupling at
   scale `2^k L₀` GROW, so that each doubling eventually reaches the strong-coupling regime
   where `ε` is small. Concretely, `ε_L` should be a function of the running coupling
   `g(L)`, small only once `g(L)` is large; `U(1)` has `g(L)` decreasing to a fixed value.
2. No massless gauge bosons: the self-interaction (commutator term `[A_μ, A_ν]` in `F`)
   gives the quartic and cubic vertices that, nonperturbatively, gap the gluon. In `U(1)`
   `F = dA` is linear and the free photon is exact at long distances.
3. Center symmetry / confinement: `Z_N` center vortices disorder Wilson loops (area law).
   `U(1)` in 4D lacks the compact-monopole condensation at weak coupling (it occurs only at
   strong coupling), and its center is all of `U(1)`.
For the doubling inequality this means: the per-step ε must be stated as a function of an
input (the running coupling at scale `L`, or a vortex-free-energy / 't Hooft-loop bound)
that is provably different for `SU(N)` and `U(1)`. A Milestone-3 statement whose
hypotheses are all satisfied by the 4D `U(1)` Wilson action at large `β` is refuted by the
Coulomb phase and must not be pursued.

Status. Framing only; nothing in Milestone 3 is proved. OPEN.

## 8. C11 slab insertion and the torus Wilson action (2026-10-06 PT)

PP Lemma 3.3 (F215 paper 5, `reviews/openai-math/F215-METHODS.md` §1.6 P6): for bounded `F`
in a time slab of thickness `r`, `‖A_F‖ ≤ ‖F‖_∞` and, for `t > r`,
`|E_tor;t,w F − E_cyl,w F| ≤ ‖F‖_∞ (s(t−r) + s(t))`, via `E_tor F = Tr(A_F T^{(t−r)/a})/(1+s(t))`.

`Continuum/TorusSlabInsertion.lean`:
- proved finite geometry: `slabVertices N s r` (time slab mod `N`), `slabVertices_length = r·N³`,
  `slabPlaquettes_length = 6·r·N³`, `mem_slabVertices`, `slabPlaquettes_sub` (in torus),
  `slab_complement_count` (`r ≤ N`: slab + complement = `N⁴`), `slab_timeShift`.
- REDUCTION: `SlabInsertionSpectrum` carries the analytic inputs as fields (spectral
  decomposition / trace-ratio identity `E·(1+s_n) ≈ d₀ + Σ d_iλ_i^m`, `λ_i ≥ 0`,
  `|d_i| ≤ M = ‖F‖_∞`, `m + r = n`); proved `slab_insertion_bound`:
  `|E − d₀| ≤ M(s_m + s_n)`.
- U(1) test: group-blind; geometric/spectral PLUMBING. It moves smallness of `s` into a
  torus≈cylinder comparison and cannot carry the gap.

`Continuum/TorusWilsonAction.lean`: `GaugeConfig G = Z4Link → G.Carrier` for
`RepTheory.ConstructiveGroup`; periodic `holonomy`; `wilsonAction G N f U = Σ_p f(U_p)` with
abstract weight `f : G.Carrier → Q'` (no `Re tr` on `Q'`); `torusPlaquettes_shift_perm`
(choice-free perm via `perm_of_nodup_mem`); `wilsonAction_shift_invariant`. Group-blind
plumbing (U(1) satisfies it); no measure, no gauge invariance, no transfer matrix yet.
