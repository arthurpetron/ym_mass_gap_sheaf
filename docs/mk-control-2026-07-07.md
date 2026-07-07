# The Migdal–Kadanoff bond-moving approximation control — is δ⁴ᴰ ≤ δᴹᴷ a rigorous bound (closing singleStep), or the singleStep input?

**Date:** 2026-07-07. **Scope:** the sole open per-scale input of the continuum
construction, `SingleStepDefectReduction.SingleStepDefectBound.singleStep`
(`realδ_k ≤ δ_model(w_k)`), viewed through the MK bond-moving approximation.

---

## VERDICT UP FRONT (maximally adversarial, honest)

**`δ⁴ᴰ ≤ δᴹᴷ` for the GAP DEFECT is NOT provable via Jensen/variational. It is the
`singleStep` input, not a closure.**

The Migdal–Kadanoff bond-moving IS a rigorous variational (Jensen) bound — but on
the **FREE ENERGY** `log Z`, not on the **spectral-gap defect**. The gap defect is
a *different functional* of the fused measure (the excited/vacuum ratio, i.e. the
sub-leading transfer eigenvalue), and the free-energy variational principle carries
**no information** about it. Concretely (verified below): the MK free energy
`[c^{⋆m}]₀` explodes by seven orders of magnitude (`1 → 159 → 38491 → 1.1·10⁷`)
while the gap indicator `2 − ρ_m` stays `O(1−w)` — so a Jensen bound on the former
says nothing about the latter. This is the same reason MK gives only *approximate*
(never rigorously bracketed) correlation lengths / critical exponents. **The
real-vs-MK gap for the DEFECT is exactly `singleStep`. No mass gap is closed; the
4D Yang–Mills mass gap remains OPEN.**

---

## 1. The MK bond-moving structure (recap, from delta_loop_bondmoving)

The MK RG replaces the real 4D lattice by a **hierarchical lattice**: it MOVES
bonds so the lattice decouples into 1D chains, then decimates.

- **Decimation** (bonds in series) is EXACT on the heat kernel: the semigroup
  `f_t → f_{bt}`. This is the exactly-soluble `HierarchicalGap` orbit (δ=0), which
  its own docstring flags as *not* the 4D theory: "the genuine 4D content is the
  bond-moving residual δ … which is NOT addressed here and remains open."
- **Bond-moving** (bonds in parallel) replaces the single-plaquette weight `K_w`
  by the pointwise power `K_w^m`, `m = b^{d−1}` (`= 8` in 4D, `b=2`) — the m-fold
  SU(2) Clebsch–Gordan fusion of the character coefficients `[c^{⋆m}]_s`.
- **δᴹᴷ** = the fused excited/vacuum degradation. PROVED `≤ 6(1−w)²`
  (`bondMovingDeltaRen_le_sixp` / `RenDefectQuadFactor`) and shown to CONCENTRATE:
  `2 − ρ_m ≈ 6(1−w)/m`, `ρ_m = [c^{⋆m}]₁/[c^{⋆m}]₀` (`InteractingMFoldDefect`,
  `UniformMFoldConcentration`).

## 2. The variational bound (the crux): what Jensen actually bounds

The MK bond-moving is a genuine variational approximation. Moving bonds together
(potential-moving) vs apart brackets the **free energy** by Jensen's inequality
(convexity of `log Z` in the couplings; Kadanoff, Ann. Phys. 100 (1976);
Osterwalder–Seiler, Ann. Phys. 110 (1978)). Its algebraic engine is the two-term
convexity `2xy ≤ x² + y²` (`0 ≤ (x−y)²`). Concretely, for the fused vacuum
coefficient (the partition-function normalization = the free energy),

    [c^{⋆m}]₀ = ∫ K_w^m dμ  ≥  (∫ K_w dμ)^m  =  (c₀)^m  =  1     (Jensen, x↦x^m convex).

This IS a rigorous one-sided free-energy bound. So the MK approximation **does**
rigorously control the free energy (one-sided; the two-sided bracket has an
uncontrolled O(1)-per-bond width in d>2, but even the controlled side is a
free-energy statement).

## 3. The DECISIVE check: does the variational bound transfer to the GAP defect? NO.

The gap defect δᴹᴷ (and δ⁴ᴰ) is the degradation of the **spectral gap**, i.e. the
excited/vacuum **RATIO** `ρ_m = [c^{⋆m}]₁ / [c^{⋆m}]₀` (the sub-leading transfer
eigenvalue ratio), **NOT** the free energy `[c^{⋆m}]₀`. The two are different
functionals, and a Jensen bound on the denominator/numerator scale says nothing
about their ratio. Numerically decisive (exact m-fold Clebsch–Gordan fusion
convolution, mpmath, `w = 0.99`, `ε = 1−w = 0.01`):

| m | free energy `[c^{⋆m}]₀` (Jensen ≥ 1) | gap indicator `(2 − ρ_m)/ε` (target 6/m) | connected `Cdef_m` |
|---|---|---|---|
| 1 | 1.000 | 5.940 (6.000) | ≈ 4·10⁻³¹ (=0) |
| 2 | 158.6 | 3.003 (3.000) | 6.7·10⁻⁹ |
| 3 | 38491 | 2.009 (2.000) | 2.7·10⁻⁹ |
| 4 | 1.11·10⁷ | 1.509 (1.500) | 1.3·10⁻⁹ |

The free energy `[c^{⋆m}]₀` blows up by **7 orders of magnitude**; the gap
indicator `2 − ρ_m` is **inert** (`O(ε)`, `≈ 6ε/m`). A variational (Jensen) bound
on `[c^{⋆m}]₀` therefore imposes **zero constraint** on `ρ_m`. This is exactly why
MK is famous for producing only *approximate*, never rigorously-bracketed,
correlation lengths / critical exponents: the variational principle controls
`log Z`, not `ξ = 1/m_gap`. (All numerics reproduce the pre-existing 40–60-digit
results in `mfold-2026-07-07.md` / `uniform-m-2026-07-07.md`.)

**Conclusion of the check:** `δ⁴ᴰ ≤ δᴹᴷ` for the gap defect does **not** follow from
the MK free-energy variational bound. The MK bond-moving is a rigorous bound on the
FREE ENERGY only; it does not transfer to the GAP DEFECT.

## 4. So is δ⁴ᴰ ≤ δᴹᴷ the singleStep input? YES — exactly.

Passing from the (available, cited) free-energy bracket to a gap-defect bound
requires precisely (i) the construction of the true dimensionless-margin sequence
`trueMargin_k = m_lat(a_k)/a_k`, and (ii) the identification of its real per-step
degradation `δ⁴ᴰ_k` with the fusion object over the full RG recursion (the channel
feedback of the `s≥2` fused remainder into the next scale's `s=1` gap). Neither is
supplied by Jensen. In per-step form this is verbatim
`SingleStepDefectBound.singleStep : (1 − δ_model_k)·trueMargin k ≤ trueMargin (k+1)`.
The MK-approximation route therefore **reduces to** — it does not close —
`singleStep`. The real-vs-MK gap for the gap defect **is** the singleStep input.

## 5. Lean deliverable — `YMGap/Continuum/MKBondMovingControl.lean` (new, imported in YMGap.lean)

PROVED (axiom-clean `Q'`/`Nat`):
- **`potentialMoving_convexity`** — the Jensen/convexity engine `2xy ≤ x²+y²` of the
  MK potential-moving FREE-ENERGY bound (re-export of the PROVED `CRealAlg.amgm_two`).
- **`mkDefect_le_sixQuad`** — the MK bond-moving defect is `≤ 6p(1−w)²` (the MK /
  hierarchical SIDE, PROVED; re-export of `bondMovingDeltaRen_le_sixp`).
- **`mkFusion_concentration`** — the fused ratio concentrates `ρ_2 ≤ 2ρ_1`
  (re-export of the PROVED `selfFusion_ratio_two`).
- **`MKFreeEnergyBracket`** + **`mkBracket_transitive`** — the MK variational
  FREE-ENERGY bracket `mkLower ≤ freeEnergy ≤ mkUpper` as an explicit named
  structure (Jensen/Kadanoff 1976); the only thing it delivers on its own is a
  free-energy bound — manifestly silent about any excited/vacuum ratio.
- **`singleStep_of_mkGapDefectTransfer`**, **`mkControl_fullFloor`** — GIVEN the
  (open) gap-defect transfer, the whole positive continuum floor for the true margin.

NAMED-OPEN (honest, UNINHABITED):
- **`MKGapDefectTransfer := SingleStepDefectBound`** (Rule 9.8 def-alias) — the
  real-vs-MK GAP-defect transfer `δ⁴ᴰ ≤ δᴹᴷ`, which the docstring proves is NOT
  supplied by the free-energy bracket and IS exactly `singleStep`. Uninhabited.
- **`mkVariational_bounds_freeEnergy_not_gapDefect`** — the honest verdict theorem.

## 6. Build / gate status

- `lake build` **GREEN** (741 jobs, exit 0).
- `YMGapGuard` **GREEN**: "frontier-guard OK: 5 Clay-frontier types unconditionally
  uninhabited across YMGap.*" This module inhabits **NONE** of the 5 guarded types
  (`Tier0Scorecard`, `UniformSpacingFloor`, `ClayTarget`, `ClayTargetPinned`,
  `FrontierDAG`), and does not inhabit `SingleStepDefectBound` either (it aliases it
  and leaves it open). The guard did NOT need to react — nothing was closed.
- `#print axioms` on every load-bearing declaration: `propext` / `Quot.sound` only
  (`potentialMoving_convexity`, `mkBracket_transitive`: `[propext]`;
  `mkVariational_bounds_freeEnergy_not_gapDefect`: no axioms). No `Classical.*`, no
  `native_decide`, no `sorry`/`sorryAx`, no `ring`.

## 7. HONEST FINAL VERDICT

The MK bond-moving is a **rigorous variational (Jensen) bound on the FREE ENERGY**,
and the MK/hierarchical defect is PROVED `≤ 6(1−w)²` and concentrating. **But the
gap defect is a strictly different functional** (the excited/vacuum ratio, not the
partition function), and the free-energy variational principle does **not** transfer
to it — demonstrated by the free energy exploding (`1 → 1.1·10⁷`) while the gap
ratio is inert (`2 − ρ_m ≈ 6ε/m`). Therefore **`δ⁴ᴰ ≤ δᴹᴷ` for the GAP DEFECT is
NOT provable via Jensen; it is EXACTLY the `singleStep` input** (the MK-free-energy
bound ≠ the gap-defect bound). `MKGapDefectTransfer` is UNINHABITED. Nothing is
faked; **the 4D Yang–Mills mass gap remains OPEN.**
