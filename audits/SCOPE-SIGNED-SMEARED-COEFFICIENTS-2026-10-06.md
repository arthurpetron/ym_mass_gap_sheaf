# Scope: signed (Newton-Schulz-normalized) smeared observables versus the 7bf9dcde nondegeneracy chain and the A03 consumers (2026-10-06 UTC)

Status: scoping only. No Lean edits and no Lean runs. The Mac was used only for git
and for reading/grepping Lean source. Line numbers are at `0011f759`, under
`lean/YMGap/Continuum/`.

Question (from `reviews/YM-anchor-projection-note-2026-10-06.md`). For SU(2),
staple smearing followed by Newton-Schulz normalization (NS-k), `V ↦ V·p_k(det V)`,
is a polynomial in the links: a SIGNED rational combination of products of
closed-word traces. Does the checked chain need POSITIVE loop coefficients or
plaquette-specific structure? Or does it only need a bounded slab-local
expression with a nonzero centered part?

## 1. Answer

- **Positive coefficients: NO.** No lemma in the nondegeneracy chain or in the A03
  consumers uses `c ≥ 0`.
  - The family state is already the signed combination `Σ_p c(p)·χ_1(U_p)`
    (`familyExpression`, `BF4WilsonPlaquetteFamilySourcePin.lean:51`).
  - Every floor is written with `Σ c(p)²`, never `(Σ c(p))²`.
  - The trajectory needs only `coeff_mass_pos : 0 < Σ c²`
    (`BF4WilsonAllNomeDyadicSmoothedTrajectory.lean:329`).
  - The only positivity used is time-kernel positivity and spectral positivity of
    the transfer operator. Neither involves loop coefficients:
    - `smoothingWeight_nonneg`, `BF4WilsonAllNomeSmoothedCoherentState.lean:170`;
    - `response_le_of_le`, `BF4WilsonAllNomeOddResponseJensen.lean:242`.
- **Plaquette-specific structure: YES, but only in the nondegeneracy chain.** The
  variance floor, the lag-one Rayleigh/band floor and the source moment pins are
  proved only for spans of single fundamental plaquette characters on distinct
  spatial faces of one time slice.
- **A03 consumers: generic.** They need a vacuum-complement vector built from a
  bounded IntrinsicExpression supported in one time slab, plus a quantitative
  positive floor `fl_j ≤ R_j(side_j)`. In practice the hypothesis is
  `PathShiftedNondegenerate`: a floor on the side-shifted response, which is
  stronger than "nonzero centered part". "Nonzero centered part" is enough only
  together with a lag-one Rayleigh floor (§3).
  - The current statements are typed through `familyState` / `DyadicSmoothedTrajectory`,
    so they need restating, not reproving.
- **Syntax already fits.** `WindowExpression`
  (`BF4ExactSlabFixedSpatialWilsonWindow.lean:50`) has
  `one | loop offset (SourceLoop) spin | add | mul | smul (q : Q')`.
  - A `SourceLoop` (`BF4ExactSlabFixedSpatialWilsonProbe.lean:44`) is any closed,
    compatible oriented word on `baseLinks width`.
  - So an NS-k-normalized, spatially staple-smeared Wilson loop is an
    `IntrinsicExpression` of radius 0, i.e. one slice.
    - `det V_l = ½ tr(V_l V_l†) = ½ Σ_{a,b} tr(P_a P_b†)` is a signed combination
      of closed-word traces through the base point.
    - The smeared loop is `tr(Π_l V_l) · Π_l p_k(det V_l)`.
    - The whole expression is a `.smul`/`.add`/`.mul` tree.
  - Caveat: temporal staples need time offsets. Within one slab that is still
    allowed, with radius = number of smearing steps.

## 2. Exact break list

"Breaks" means the statement or proof does not apply to a general signed
polynomial `IntrinsicExpression`. None of these breaks because of the sign of the
coefficients. Each breaks because the proof is specific to plaquette spans.

### 2a. Variance floor (plaquette-specific, Σc²)

1. `BF4ExactSlabPlaquetteAffineCoercivity.lean:267` `finiteValue_variance_floor`
   (with `varianceFloor :233`, normalized floor ~`:244`).
   - Statement: `varianceFloor w · Σ c(p)² ≤ Var(sourceSpan extent c qs)` for
     signed fundamental-plaquette spans with `qs.Nodup`.
   - Proof: finite face duals that detect each plaquette coefficient separately.
   - Why it breaks: the duals are single-face, single-fundamental-character
     functionals. For products of traces, or for words sharing links (every NS
     term around a smeared link shares links), no such per-term dual exists. The
     detection, not the sign, is what fails.
   - It is not a single-face character expansion in the Haar sense, but it
     relies on distinct-face orthogonality.
2. `BF4ExactSlabFixedSpatialPlaquetteFamilyVariance.lean:82` `chart_variance_floor`,
   `:114` `family_variance_converges` and `:136` `family_joint_variance_floor`.
   - These are time-shifted plaquette charts plus the completed (limit) transfer of
     item 1.
   - They inherit item 1's restriction.
3. `BF4WilsonAllNomePlaquetteFamilyVariance.lean`:
   - `:112` `family_mean_pin` and `:119` `family_square_pin` use
     `mixedProduct_mean` / `mixedProduct_square`, which are plaquette-family
     product identities.
   - `:140` `centered_norm_floor` needs `Nodup` plus item 2.
   - `:151` `familyExcitation_norm_floor` and `:162` `familyExcitation_norm_ne_zero`.
   - The pinning mechanism (`:66` `zero_radius_pairing_pin`, private) is generic
     for radius-0 expressions once a source-polynomial identity is supplied. Only
     the supplied identities are family-specific.

### 2b. Lag-one Rayleigh / band floor (plaquette local band)

4. `BF4ExactSlabFixedSpatialFamilyBandResponse.lean`:
   - `:180` `padded_family_energy_band_cleared` and `:243` `padded_family_energy_band`.
     - These prove the plaquette-family local band `Var = Energy + Bond` with
       `Energy ≤ (1-ρ)·Var`.
     - They use imports specific to the fundamental plaquette character: the
       FamilyLocalBand, UniformLocalBand and SU2QuaternionProductHeatBandResponse
       machinery.
   - `:165` `familyResponseFraction`:
     `ρ = w^12 · localLower(w,4·size)² / localUpper(w,4·size)²`. The `4·size`
     counts four links per plaquette.
   - Why it breaks: it is a band estimate for single fundamental plaquette
     characters. Higher spins, longer words and products are not covered.
   - Inside: `:77` `oddMoment_unprojected_source`, `:95` `centered_unprojected_square`
     and `:130` `energy_shifted` are plaquette/product-heat specific.
5. `BF4WilsonAllNomePlaquetteFamilyBondFloor.lean`:
   - `:147` `finite_family_energy_pin`, `:155` `finite_family_variance_pin`,
     `:165` `finite_family_energy_band`, `:188` `completed_family_bond_fraction`
     and `:217` `family_bond_floor` are stated for the family span and fed by
     item 4.
   - `:181` `finite_family_bond_fraction` is only `retained_fraction` algebra and
     goes through verbatim given an energy band.
6. `BF4WilsonAllNomePlaquetteFamilyBondOrbit.lean`:
   - `:104` `family_rayleigh_floor`, `:110` `family_time_geometric_floor`, `:118`
     `family_bond_geometric_floor` and `:131` `family_bond_response_ne_zero`.
   - These are thin wrappers. They break only through item 5. The geometric step
     itself is generic (§2d).

### 2c. Nondegeneracy assembly (typed by faces/coeff)

7. `BF4WilsonAllNomeShiftedPaddedNondegenerate.lean`:
   - `:171` `PathFacesPadded`, `:176` `paddedNondegFloor`, `:182`
     `paddedNondegFloor_pos` (uses `coeff_mass_pos`) and `:191`
     `pathShiftedNondegenerate_of_padded`.
   - These are stated with `faces`/`coeff` and consume items 3 and 6. Their logic
     transfers, but they must be restated with `(v_j, ρ_j)` from §3.
   - `:144` `smoothedResponse_ge_family_response` is generic in logic:
     `boxSum_ge_const`, `response_le_of_le`, `timeKernel_mass` and
     `smoothedResponse_orbit_expand`. It is typed for `x0 = familyExcitation`, so
     it needs restating, not reproving.
   - `:212` / `:225` `path_normalized_anchor_*_padded`, `:244` `origin_face_mem`
     and `:251` `paddedZeroMomentumTrajectory` are wrappers or instances.

### 2d. Go through verbatim (generic over the vector or the expression)

- `BF4WilsonAllNomeResponseLower.lean`:
  - `:79` `response_second_difference`, `:102` `response_step_lower`, `:117`
    `response_geometric_lower`.
  - Given `ρ B(v,v) ≤ B(v,Tv)` for ANY `v`, they give `ρ^n B(v,v) ≤ B(v,T^n v)`.
- `BF4WilsonAllNomeOddResponseJensen.lean:242` `response_le_of_le` (antitonicity).
  - Box-kernel facts `smoothingWeight_nonneg :170`, `timeKernel_mass` and the
    orbit expansion `:326` are kernel facts. The expansion is typed by
    familyState but proved generically.
- `BF4WilsonAllNomePlaquetteFamilyBondOrbit.lean:63` `connected_source_time_pairing`.
  - Holds for any `IntrinsicExpression`.
  - `BF4WilsonAllNomePlaquetteFamilyVariance.lean:187`
    `familyExcitation_correlator_pin` uses only this.
- `BF4WilsonAllNomeGenericNormalizedAnchor.lean`:
  - `:210` `NormalizedAnchorData` (fields: base vacuum-complement vector, block,
    norm, Cauchy modulus, pins, floor), with `:263`, `:287`, `:325`, `:416` and
    `:450`.
  - `:627` `kernelCSum` and `:666` `repOrbit`.
  - All generic.
  - `:683` `familyStream`, `:692` `smoothedSector`, `:706` `smoothedNorm`, `:729`
    `smoothedAnchorData`, `:742` `smoothedAnchor_macroRatio`, `:756`
    `trajAnchorData`, `:767` `pathAnchor`, `:774` `path_anchor_floor` and `:822`
    `path_normalized_anchor` are typed by `familyState`/`DyadicSmoothedTrajectory`.
    They use only `centeredStream`/`centeredTimeMoment` of an IntrinsicExpression,
    so they need restating.
- `BF4WilsonAllNomeShiftedH1Anchor.lean`:
  - `:235` `OneStepEpsBound`, `:239` `shift_norm_pin`, `:244`
    `shift_response_pin` and `:267`–`:372` `shifted_*`: generic over `x : V`.
  - The path layer `:396`–`:617` is typed by the trajectory and needs restating.
- `BF4WilsonAllNomeShiftedWindowSurvival.lean`:
  - `:211`–`:293` `window_*`, including `window_epsBound`: generic.
  - `pathShiftedEpsBound_of_windowSurvival` and the path layer `:313`–`:353` are
    typed by the trajectory and need restating.
- The `retained_fraction` algebra (BondFloor `:181`).

Checklist from the request:
- `Σc²` vs `(Σc)²`: all floors use `Σc²`. No lemma uses `(Σc)²`.
- Positivity of mixed moments relying on `c ≥ 0`: none found. The mixed-moment
  pins are equalities (Equiv), not sign arguments.
- Plaquette-specific variance floors: items 1–3.
- Single-face character expansions / per-face duals: items 1 and 4.

## 3. Minimal replacement hypothesis

Let `ψ_j : IntrinsicExpression (trajWidth j)` have radius 0 (one slice; an
`r`-step temporal smearing needs radius `r`). Let `x_j` be its centered completed
vector and `B`, `T` the completed inner product and transfer. The minimal generic
replacement for items 1–6 is two per-scale rational inequalities:

- **(H-var)** `0 < v_j` and `v_j ≤ B(x_j, x_j)`, i.e. `v_j ≤ centeredTimeMoment 0 ψ_j ψ_j`
  (centered-variance floor for a bounded slab observable).
- **(H-ray)** `0 < ρ_j ≤ 1` and `ρ_j · B(x_j,x_j) ≤ B(x_j, T x_j)` (lag-one Rayleigh floor).

Then:
- `response_geometric_lower` gives `ρ_j^n v_j ≤ R_{x_j}(n)`.
- A restated `smoothedResponse_ge_family_response` gives
  `fl_j := ρ_j^(2M_j+side_j) · v_j ≤ R_j(side_j)`, which is `PathShiftedNondegenerate`.
- The A03 package then follows from `PathShiftedWindowSurvival` exactly as now.

The coarser alternative is to assume `PathShiftedNondegenerate` directly. It is
one Prop with no Rayleigh step, but it is just the open goal restated.

H-var alone ("nonzero centered part") is not enough unless the shifted response is
also controlled. `T ≥ 0` is not known to be injective with a floor on this sector,
so H-ray, or a direct floor, is genuinely needed.

How H-var / H-ray could be proved for smeared loops (not done; this is the risk):

- H-var. `BF4ExactSlabWilsonWordVariance.lean:196` `finiteValue_variance_floor`
  gives `starRatio w ≤ Var` for ONE Wilson word whose first link is absent from the
  rest, at the finite stage only. I found no completed/limit transfer and nothing
  for combinations.
  - A smeared-loop floor would condition on one selected link `l`. That link must
    enter the polynomial non-trivially after all the signed cancellations.
  - The step is `Var ≥ starRatio · E[Var_{Haar,l}(ψ)]`, followed by an explicit
    spin-½ component lower bound in `U_l`.
  - Sign cancellations are the real issue here: NS terms can cancel the
    `U_l`-dependence, so this needs an explicit coefficient computation, not a
    positivity argument.
- H-ray. This needs a local band `Energy ≤ (1-ρ)Var` for general bounded-degree
  slab polynomials. That generalizes FamilyBandResponse from four-link
  fundamental plaquettes to words of length `L` and spin/degree `D`. Expect
  `ρ ~ w^{O(D²)} · localLower(w, links)²/localUpper(w, links)²`.

## 4. Newton-Schulz degree / norm blowup

- One NS step `y ↦ y(3 - d y²)/2` gives `p_k` of degree `(3^k-1)/2` in `d = det V`.
  - `det V` has degree 2 in `V`.
  - `V` has degree 3 per staple.
  - So one smearing step plus NS-k has degree `3·3^k = 3^{k+1}` per link.
- `n` smearing steps give degree `3^{(k+1)n}` per original link. A loop of
  perimeter `P` has total degree `P·3^{(k+1)n}`.
- The term count and `ℓ¹` coefficient norm grow exponentially in `n·3^k`.
  - Off the small-field set (`det V` not close to 1), `V·p_k(det V)` is not
    unitary. Its size is bounded only by the polynomial, roughly `(6(1+α))^{3^k}`
    per step in 4D.
- Effect on `ρ^(2M+side)·v`:
  - The A03 consumers use only per-`j` positivity of the floor, so the form
    `ρ_j^(2M_j+side_j) v_j` is unaffected and no Lean conclusion breaks.
  - Quantitatively, `ρ_j` from a band argument degrades like `w^{O(D²)}` with
    `D ~ P·3^{(k+1)n}`. The floor is positive but astronomically small, much like
    `familyResponseFraction`'s dependence on `size`.
  - If `n ~ side` or more, `ρ_j^(2M+side)` is doubly-exponentially small in `side`.
    That is harmless for qualitative nondegeneracy and useless for anything
    quantitative.
- Exact one-step projection `V/√det V` with `det V ≥ c > 0` is NOT expressible:
  - `WindowExpression` has no division, square root or indicator.
  - The carrier's sources are `RatPoly`.
  - Using it needs either an NS-k polynomial approximation, or extending the
    observable algebra to bounded continuous (non-polynomial) functions. The
    latter is a carrier-wide change and much larger than anything below.
  - A small-field cutoff set is likewise not a polynomial observable.

## 5. Size estimate (rough)

- **Generalize consumers + assembly** to an expression trajectory, carrying
  `(ψ_j, v_j, ρ_j)` with H-var/H-ray as fields or hypotheses. This is restating
  §2c/§2d and the path layers (F3/F4 of the smeared plan).
  - About 650–900 lines.
  - LOW risk: no new mathematics.
  - Positive coefficients never enter.
- **Prove H-var for one NS-smeared loop** at the finite stage plus a completed
  transfer: 800–1500 lines. HIGH risk because of sign cancellation in the
  selected-link spin-½ component.
- **Prove H-ray (a general local band)**: 800–2500+ lines. HIGH risk. This is the
  F5 `smearedLoop_bond_floor` item.
- **Exact projection `V/√det V`**: carrier-algebra extension; not estimated, at
  least several thousand lines.

Bottom line:
- The sign of the coefficients costs nothing.
- Leaving the plaquette span costs the variance floor and the Rayleigh floor.
- The cheap path is to carry H-var/H-ray as hypotheses next to
  `PathShiftedWindowSurvival` (about 650–900 lines, no new mathematics). Proving
  them is the hard part.
