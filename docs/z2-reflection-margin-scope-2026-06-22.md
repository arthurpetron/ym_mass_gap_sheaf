# Scope: proving the ℤ₂ reflection margin (splitting it off the O(4) named wall, 2026-06-22)
**STATUS:** Scope/plan dated 2026-06-22; see the canonical ledgers for the outcome (docs/where-the-wall-sits-2026-06-22.md, docs/stage1-completion-ledger-2026-06-22.md, docs/stage2-progress-ledger-2026-06-22.md, docs/continuum-wall-outstanding-2026-06-22.md).

Target: `RepTheory/Spin4.lean`'s `O4RestorationInput.reflectionMargin` / `reflectionMargin_ge` — currently
a NAMED input ("the discrete parity/reflection sector, the chiral swap L↔R, preserves the gap"). Question:
can it be PROVED from the chiral SU(2) data + a finite-group averaging argument, rather than assumed?

**Verdict: YES — and it should be, because the current named field conflates two distinct things.**

## The key finding: two things are bundled, only one is a wall

`O4RestorationInput` names "reflection sector preserves the gap" as analytic input. But that phrase covers
TWO mathematically separate facts:

1. **The ℤ₂ reflection (L↔R chiral swap) margin** — a FINITE, EXACT, fixed-lattice-spacing fact. The
   reflection is the outer automorphism of `so(4) = su(2)_L ⊕ su(2)_R` (the D₂ Dynkin diagram is two nodes;
   orientation-reversing O(4) elements swap them, i.e. swap the self-dual ↔ anti-self-dual ideals). This is
   **NOT a continuum-limit statement** — it holds at every fixed spacing.

2. **Full continuous O(4) rotation restoration** — rotation-breaking lattice operators being RG-irrelevant
   as `a → 0`. This IS the genuine continuum wall.

The current code treats (1)+(2) as one named input. **(1) is provable; (2) stays named.** Proving (1)
shrinks the O(4) input to ONLY (2).

## Why (1) is provable — and why the physical case is the easy case

- **Reflection symmetry of the heat-kernel action ⟺ `wL = wR`.** In *pure* Yang–Mills there is exactly
  ONE gauge coupling, so the self-dual and anti-self-dual sectors carry the SAME `w`: `wL = wR = w`
  **automatically**. So the reflection is an EXACT symmetry of the transfer operator at every lattice
  spacing — isotropy is not a special case, it is THE physical setup.

- **Restricting to an invariant subspace cannot worsen the gap.** The reflection ℤ₂ commutes with the
  transfer operator `T` (exact, fixed spacing). `T` block-diagonalizes into the ±1 reflection eigenspaces.
  The vacuum is the reflection-even singlet (it stays in the + sector), and restricting `T` to any invariant
  subspace can only REMOVE excited eigenvalues, never add larger ones. Hence the reflection-even ("physical")
  sector's margin **= the connected margin = `1 − w³`**, exactly. The Reynolds/averaging projector
  `P = (1 + σ)/2` is the standard finite-group tool; its image-spectrum ⊆ spec(`T`) is precisely this.

## Formalizing it in our framework (the honest representation)

Our `SpectralModel` is an eigenvalue LIST `(k, lam, lam_nonneg)` — no Hilbert space, no vectors. So we
represent the block-diagonalization at the eigenvalue level, faithfully:

- A `ModeInvolution S`: an involution `σ : Nat → Nat` on modes (`σ∘σ = id` on `i < k`) with `lam (σ i) = lam i`
  (σ-invariance of the eigenvalue assignment). **σ-invariance is the exact eigenvalue-level shadow of "the
  reflection commutes with `T`"** — it is what `wL = wR` gives. This is faithful, not a dodge: with no vectors,
  σ-invariance of `lam` is precisely the content of `[σ, T] = 0` visible to the spectrum.
- The reflection-even sub-spectrum then has eigenvalues ⊆ `{lam i}`, all `≤ sep`, and contains the vacuum;
  the located gap transfers with the SAME `sep`, so `gapMargin` is preserved.

## Build decomposition (all steps small, low risk — finite arithmetic in a framework we control)

1. `ModeInvolution` (structure: σ, involutivity on `i<k`, `lam`-invariance) + the **sub-spectrum located-gap
   transfer lemma**: a `LocatedSpectralGap S` + a `ModeInvolution` ⟹ the reflection-even sector has a
   located gap with the same `sep` (hence same `gapMargin`). [small]
2. The chiral swap involution on `chiralCombinedGap`: `σ` swaps mode 0 (self-dual) ↔ mode 1 (anti-self-dual);
   σ-invariance of `lam` follows from `gL.sep = gR.sep`, i.e. the isotropic `wL = wR`. [small]
3. `reflectionMargin = connectedMargin` THEOREM in the isotropic case (= `1 − w³` via `heatKernelSpin4Gap`). [small]
4. **Upgrade** `O4RestorationInput`: a new constructor `o4InputFromHeatKernelIsotropic` that DISCHARGES the
   `reflectionMargin`/`reflectionMargin_ge` fields from step 3 — leaving ONLY the continuum rotation-restoration
   as the named open input. [small]

New file: `RepTheory/Spin4Reflection.lean` (or extend `Spin4.lean`). Axiom-clean target: `[propext]`/`[Quot.sound]`.

## What stays named after this (honest)

- **Full continuous O(4) rotation restoration** — rotation-breaking operators RG-irrelevant as `a → 0`. The
  genuine continuum wall (the same family as `DimensionlessRatio.ratioConverges`). Unchanged.

## Honest caveats

- This proves the reflection ℤ₂ margin at FIXED spacing for the physical (one-coupling, isotropic) YM — it
  does NOT prove O(4) restoration. It removes the *finite* half of the bundled input, sharpening the wall.
- The eigenvalue-list `SpectralModel` has no vectors, so block-diagonalization is formalized via σ-invariance
  of `lam` (the faithful shadow of `[σ,T]=0`). A full vector-level Reynolds projector would need a Hilbert-space
  enrichment of `SpectralModel` — out of scope and unnecessary for the margin.
- The relevant ℤ₂ is the L↔R *outer* swap (O(4)/SO(4) parity). The OTHER ℤ₂ — the central `Spin(4)→SO(4)`
  (spin vs vector reps) — is a different quotient, not addressed here; note it in-file.

## Recommendation

Build it (steps 1–4). Low risk, ~1 small file, finite list arithmetic; high honesty value — it converts a
bundled named input into a theorem + a strictly smaller, correctly-named continuum wall. The physical isotropy
`wL = wR = w` makes the reflection an exact symmetry, so the reflection margin lands as `1 − w³` outright.
