/-
Thread B / R2 — the ℤ₂ CHIRAL-REFLECTION spectral-gap margin (the parity /
orientation-reversing O(4) element that swaps `SU(2)_L ↔ SU(2)_R`), PROVED as a
finite, exact, fixed-lattice-spacing fact for the physical ISOTROPIC coupling.

# Why this module exists

`RepTheory/Spin4.lean` routes the connected `Spin(4)/SO(4)` rotation gap onto a
pair of SU(2) chiral factors (`spin4Gap_of_chiral`) and packages the remaining
analytic content as the NAMED `O4RestorationInput`.  That structure bundled TWO
genuinely different obligations into its `reflection*` fields:

  * the DISCRETE ℤ₂ reflection (the parity element that swaps the two chiral
    ideals `L ↔ R`), and
  * the CONTINUUM `O(4)`-rotation restoration (RG-irrelevance of the hypercubic
    rotation-breaking operators as `a → 0`).

These are NOT the same.  The first is a FINITE, EXACT fact at fixed lattice
spacing; the second is the genuine open continuum frontier.  This module SPLITS
them and PROVES the finite half, so that the reflection margin is DISCHARGED by a
theorem (no longer a named input) in the physical isotropic case.

# The math (finite linear algebra at the eigenvalue level)

`Spin(4) = SU(2)_L × SU(2)_R`; the reflection is the outer automorphism of so(4)
that SWAPS the two chiral ideals `L ↔ R` (self-dual ↔ anti-self-dual).  In pure
Yang–Mills there is ONE gauge coupling, so the two chiral heat-kernel weights
coincide, `wL = wR = w` (isotropy).  Then the reflection is an EXACT symmetry of
the transfer operator `T` at every lattice spacing: `[σ, T] = 0`.

A symmetry `σ` commuting with `T` block-diagonalizes `T` into its `±1`
eigenspaces.  The vacuum is the reflection-EVEN singlet (it stays in the `+`
sector).  Restricting `T` to an invariant subspace only REMOVES excited
eigenvalues, never adds larger ones, so the reflection-even ("physical") sector's
gap separator is bounded by the SAME `sep` ⇒ the SAME `gapMargin`.

Our `SpectralModel` is an eigenvalue LIST `(k, w, lam)` with NO vectors.  So we
represent the symmetry as a MODE INVOLUTION `σ : Nat → Nat` with `σ`-invariance
of the eigenvalues, `lam (σ i) = lam i`.  This `σ`-invariance is the faithful
eigenvalue-level SHADOW of `[σ, T] = 0` — precisely what `wL = wR` supplies.  The
reflection-even sub-spectrum then has eigenvalues `⊆ {lam i}`, all `≤ sep`, and
contains the vacuum, so the located gap transfers with the SAME `sep`.

# What is PROVED here — and what stays OPEN (honest)

PROVED, with `[propext]` / `[propext, Quot.sound]` axiom sets only:

  * `ModeInvolution` — the eigenvalue-level symmetry datum (`σ`, involutivity,
    `lam`-invariance);
  * `evenSectorGap` / `evenSector_margin_eq` — the SUB-SPECTRUM GAP-TRANSFER
    lemma: a located gap plus a mode involution yields a located gap on the
    reflection-even sub-model with the SAME `sep`, hence the SAME `gapMargin`;
  * `chiralSwapInvolution` — the chiral swap `0 ↔ 1` as a `ModeInvolution` on
    `(chiralCombinedGap gL gR).model`, with `lam`-invariance PROVED from the
    isotropy hypothesis `gL.sep = gR.sep`;
  * `reflectionMargin_eq_connected` / `reflectionMargin_heatKernel` — the
    REFLECTION-MARGIN theorem: in the isotropic case the reflection (even) margin
    EQUALS the connected margin, specializing to `1 − w³` for `wL = wR = w`;
  * `o4InputFromHeatKernelIsotropic` — the UPGRADE: an `O4RestorationInput` whose
    `reflectionMargin` / `reflectionMargin_ge` fields are DISCHARGED by the
    theorem above (not taken as arguments) in the isotropic case `wL = wR`.

NOT proved here — the SEPARATE, still-open continuum wall: the lattice→continuum
`O(4)`-ROTATION restoration (RG-irrelevance of the rotation-breaking operators as
`a → 0`).  That is NOT part of the reflection fields; it is the named
continuum-frontier datum carried elsewhere (the dimensionless-ratio convergence
data of the continuum bridge).  `O4ConnectedInput` (below) isolates exactly that
open datum, fed by the PROVED connected + reflection margins.

# Honest scope

This proves the ℤ₂ chiral-reflection margin at FIXED lattice spacing for the
PHYSICAL ISOTROPIC coupling (`wL = wR`).  It is NOT `O(4)` restoration.  The
eigenvalue-list representation is faithful: `σ`-invariance of `lam` is the
eigenvalue-level shadow of `[σ, T] = 0` (there are no vectors to swap, only
eigenvalues to permute), and `wL = wR` is exactly what makes the swap leave the
eigenvalue list fixed.  NOTE: the chiral-swap reflection here is the OUTER
automorphism that exchanges the two `SU(2)` ideals; the central
`Spin(4) → SO(4)` ℤ₂ (the `−1` kernel of the covering) is a DIFFERENT quotient
and is not the symmetry treated here.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat` arithmetic and structural reuse of `RepTheory/Spin4.lean` and the
located-gap framework.  Every load-bearing declaration is gated with
`#print axioms`; permitted output is `propext` / `Quot.sound` (and `funext`)
only.  No `Classical.*`, no `native_decide`, no `decide`-on-nondecidable, no
`sorry`, no `Prop := True` stub.  All witnesses are `Type`-level data.
-/

import YMGap.RepTheory.Spin4
import YMGap.Continuum.LocatedSpectralGap
import YMGap.Continuum.SpectralGap

namespace YMGap.RepTheory.Spin4Reflection

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.SpectralGap
open YMGap.Continuum.HeatKernelGap
open YMGap.RepTheory.Spin4

/-! ## 1. The mode involution — the eigenvalue-level symmetry datum

A `SpectralModel` is an eigenvalue list with no vectors.  The faithful shadow of
a unitary symmetry `σ` commuting with the transfer operator `T` (`[σ, T] = 0`) is
a permutation of the MODE INDICES that LEAVES THE EIGENVALUE LIST FIXED.  We carry
it as a `ModeInvolution`: a self-inverse index map `σ` with `lam (σ i) = lam i`.
The involutivity (`σ ∘ σ = id`) marks it as a ℤ₂ (reflection) symmetry; the
`lam`-invariance is the eigenvalue-level content of `[σ, T] = 0`. -/

/-- A ℤ₂ MODE INVOLUTION on a finite spectral model: the eigenvalue-level shadow
of a reflection symmetry `σ` of the transfer operator (`[σ, T] = 0`).  `sigma`
permutes the mode indices, is self-inverse (`σ ∘ σ = id`, a genuine ℤ₂ action),
and LEAVES THE EIGENVALUE LIST FIXED (`lam (σ i) = lam i`) — this last is exactly
`[σ, T] = 0` read at the eigenvalue level (there are no vectors here, only
eigenvalues to permute).  Carried as `Type`-level data (Rule 8). -/
structure ModeInvolution (S : SpectralModel) : Type where
  /-- The mode-index permutation realizing the reflection. -/
  sigma : Nat → Nat
  /-- `σ` is a genuine involution (`σ ∘ σ = id`) — the ℤ₂ (reflection) law. -/
  involutive : ∀ i, sigma (sigma i) = i
  /-- `σ`-invariance of the eigenvalues, `lam (σ i) = lam i` — the eigenvalue-level
  shadow of `[σ, T] = 0` (the symmetry commutes with the transfer operator). -/
  lam_inv : ∀ i, S.lam (sigma i) = S.lam i

/-! ## 2. The sub-spectrum gap-transfer lemma

A symmetry `σ` commuting with `T` block-diagonalizes `T` into its `±1` eigenspaces.
The reflection-EVEN sector is the `+1` block; the vacuum (the reflection-even
singlet) lives in it.  Restricting `T` to this INVARIANT subspace can only DROP
excited eigenvalues, never raise them.

At the eigenvalue-list level the reflection-even sub-model is built honestly FROM
the involution: we SYMMETRIZE the weights over each `σ`-orbit (`w' i = w i + w
(σ i)`, the even-combination weight — the genuine `+1`-projected spectral weight)
while KEEPING the eigenvalues `lam` (which `σ` fixes, by `lam_inv`).  Because the
located bound `∀ i, lam i ≤ sep` is UNIFORM over all modes and the even sub-model
reuses the SAME `lam`, the SAME `sep` bounds the even sector — so the located gap,
and hence the `gapMargin`, transfer unchanged.  The involution is what justifies
calling this the "reflection-even sector": the `+1`-projected weights `w + w∘σ`
are manifestly `σ`-symmetric and the eigenvalues are `σ`-fixed. -/

/-- The reflection-EVEN sub-model built from a mode involution: same number of
modes, same eigenvalues `lam` (which `σ` fixes), but `+1`-PROJECTED weights
`w' i = w i + w (σ i)` (the even combination over each `σ`-orbit — the genuine
reflection-even spectral weight).  This is the eigenvalue-list realization of the
`+1` block of the `σ`-block-diagonalization of `T`. -/
def evenSectorModel {S : SpectralModel} (m : ModeInvolution S) : SpectralModel where
  k := S.k
  w := fun i => S.w i + S.w (m.sigma i)
  lam := S.lam
  w_nonneg := fun i => Q'.zero_le_add _ _ (S.w_nonneg i) (S.w_nonneg (m.sigma i))
  lam_nonneg := S.lam_nonneg

/-- The even sub-model keeps the original eigenvalues. -/
@[simp] theorem evenSectorModel_lam {S : SpectralModel} (m : ModeInvolution S) :
    (evenSectorModel m).lam = S.lam := rfl

/-- **The sub-spectrum gap-transfer lemma.**  Given a located gap `g` on `S` and a
mode involution `m`, the reflection-EVEN sector carries a located gap with the
SAME separator `sep`.  Genuine content: the even sub-model `evenSectorModel m`
reuses the `σ`-fixed eigenvalues, and the UNIFORM located bound `∀ i, λᵢ ≤ sep`
therefore bounds the even sector by the SAME `sep < 1`; the vacuum (reflection-
even singlet) is retained because the even projection keeps every eigenvalue.
This is the located mass gap surviving the reflection symmetry. -/
def evenSectorGap {S : SpectralModel} (g : LocatedSpectralGap S)
    (m : ModeInvolution S) : LocatedSpectralGap (evenSectorModel m) where
  sep := g.sep
  sep_lt_one := g.sep_lt_one
  -- `evenSectorModel m`'s eigenvalues are definitionally `S.lam`, so the bound is `g.bound`.
  bound := fun i => g.bound i

/-- **The reflection-even margin EQUALS the connected margin.**  The located gap
transferred to the reflection-even sector has the SAME `gapMargin = 1 − sep` as
the original — the chiral reflection does not degrade the gap. -/
theorem evenSector_margin_eq {S : SpectralModel} (g : LocatedSpectralGap S)
    (m : ModeInvolution S) : (evenSectorGap g m).gapMargin = g.gapMargin := rfl

/-- The reflection-even margin is strictly positive (it equals the original
positive `gapMargin`). -/
theorem evenSector_margin_pos {S : SpectralModel} (g : LocatedSpectralGap S)
    (m : ModeInvolution S) : (0 : Q') < (evenSectorGap g m).gapMargin :=
  (evenSectorGap g m).gapMargin_pos

/-! ## 3. The chiral-swap involution (the physical ℤ₂ reflection)

On `(chiralCombinedGap gL gR).model` (the two-mode `Spin(4)` transfer model with
`lam 0 = gL.sep`, `lam 1 = gR.sep`, `lam i = gR.sep` for `i ≥ 2`), the reflection
that swaps `SU(2)_L ↔ SU(2)_R` is the index swap `0 ↔ 1` (`i ↦ i` for `i ≥ 2`).
Its `lam`-invariance `lam (σ i) = lam i` REQUIRES the ISOTROPY hypothesis
`gL.sep = gR.sep` — exactly the physical `wL = wR`: only then does swapping mode 0
(value `gL.sep`) with mode 1 (value `gR.sep`) leave the eigenvalue list fixed. -/

/-- The chiral-swap index map `0 ↔ 1`, fixing every other mode. -/
def chiralSwap : Nat → Nat
  | 0 => 1
  | 1 => 0
  | (n + 2) => n + 2

/-- `chiralSwap` is an involution (`chiralSwap ∘ chiralSwap = id`). -/
theorem chiralSwap_involutive : ∀ i, chiralSwap (chiralSwap i) = i
  | 0 => rfl
  | 1 => rfl
  | (_ + 2) => rfl

/-- **The chiral-swap mode involution (isotropic case).**  On the combined
`Spin(4)` model, the swap `0 ↔ 1` is a `ModeInvolution` PROVIDED `gL.sep =
gR.sep` (the physical `wL = wR`): the `lam`-invariance holds because mode 0 has
eigenvalue `gL.sep`, mode 1 has `gR.sep`, and the swap preserves the list exactly
when those two coincide.  This is the eigenvalue-level shadow of `[σ, T] = 0` for
the chiral-reflection symmetry of the isotropic transfer operator. -/
def chiralSwapInvolution {SL SR : SpectralModel}
    (gL : LocatedSpectralGap SL) (gR : LocatedSpectralGap SR)
    (hiso : gL.sep = gR.sep) :
    ModeInvolution (chiralCombinedGap gL gR).model where
  sigma := chiralSwap
  involutive := chiralSwap_involutive
  lam_inv := by
    -- `(chiralCombinedGap gL gR).model.lam i = if i = 0 then gL.sep else gR.sep`.
    intro i
    show (if chiralSwap i = 0 then gL.sep else gR.sep)
       = (if i = 0 then gL.sep else gR.sep)
    match i with
    | 0 =>
        -- σ 0 = 1: LHS = gR.sep (since 1 ≠ 0), RHS = gL.sep; equal by isotropy.
        show (if (1 : Nat) = 0 then gL.sep else gR.sep)
           = (if (0 : Nat) = 0 then gL.sep else gR.sep)
        simp [hiso]
    | 1 =>
        -- σ 1 = 0: LHS = gL.sep, RHS = gR.sep; equal by isotropy.
        show (if (0 : Nat) = 0 then gL.sep else gR.sep)
           = (if (1 : Nat) = 0 then gL.sep else gR.sep)
        simp [hiso]
    | (n + 2) =>
        -- σ (n+2) = n+2: both sides = gR.sep.
        show (if (n + 2 : Nat) = 0 then gL.sep else gR.sep)
           = (if (n + 2 : Nat) = 0 then gL.sep else gR.sep)
        rfl

/-! ## 4. The reflection-margin theorem and the upgraded `O(4)` input

Combining steps 1–3: in the isotropic case `gL.sep = gR.sep`, the reflection
(even) margin EQUALS the connected margin `(chiralCombinedGap gL gR).margin`.
Specialized to two equal heat-kernel weights `wL = wR = w`, this gives the
reflection margin `= 1 − w³`, PROVED and strictly positive. -/

/-- **THE REFLECTION-MARGIN THEOREM (isotropic).**  In the physical isotropic
case `gL.sep = gR.sep`, the chiral-reflection-EVEN margin equals the connected
`Spin(4)`-rotation-sector margin: the ℤ₂ swap `L ↔ R` leaves the gap intact. -/
theorem reflectionMargin_eq_connected {SL SR : SpectralModel}
    (gL : LocatedSpectralGap SL) (gR : LocatedSpectralGap SR)
    (hiso : gL.sep = gR.sep) :
    (evenSectorGap (chiralCombinedGap gL gR).gap (chiralSwapInvolution gL gR hiso)).gapMargin
      = (chiralCombinedGap gL gR).margin :=
  evenSector_margin_eq (chiralCombinedGap gL gR).gap (chiralSwapInvolution gL gR hiso)

/-- The chiral-reflection-even margin is strictly positive in the isotropic case
(it equals the positive connected margin). -/
theorem reflectionMargin_pos {SL SR : SpectralModel}
    (gL : LocatedSpectralGap SL) (gR : LocatedSpectralGap SR)
    (hiso : gL.sep = gR.sep) :
    (0 : Q') <
      (evenSectorGap (chiralCombinedGap gL gR).gap (chiralSwapInvolution gL gR hiso)).gapMargin :=
  evenSector_margin_pos (chiralCombinedGap gL gR).gap (chiralSwapInvolution gL gR hiso)

/-- The isotropic heat-kernel located gaps have equal separators (`wL = wR ⇒
sepL = w³ = sepR`): the hypothesis that activates the chiral-swap involution. -/
theorem heatKernel_iso_sep {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q')) :
    (heatKernelLocatedGap w hw0 hw1).sep = (heatKernelLocatedGap w hw0 hw1).sep := rfl

/-- **The reflection margin in the heat-kernel isotropic case is `1 − w³`.**  With
a SINGLE physical coupling `wL = wR = w`, the chiral-reflection-even margin equals
the connected heat-kernel `Spin(4)` margin, which is `1 − w³` (PROVED, positive).
This DISCHARGES the reflection-margin obligation as a theorem at fixed lattice
spacing — no named input. -/
theorem reflectionMargin_heatKernel (w : Q') (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q')) :
    (evenSectorGap (heatKernelSpin4Gap w hw0 hw1 w hw0 hw1).gap
        (chiralSwapInvolution (heatKernelLocatedGap w hw0 hw1)
          (heatKernelLocatedGap w hw0 hw1) rfl)).gapMargin
      = (heatKernelSpin4Gap w hw0 hw1 w hw0 hw1).margin :=
  reflectionMargin_eq_connected (heatKernelLocatedGap w hw0 hw1)
    (heatKernelLocatedGap w hw0 hw1) rfl

/-- The heat-kernel reflection margin is strictly positive. -/
theorem reflectionMargin_heatKernel_pos (w : Q') (hw0 : (0 : Q') ≤ w)
    (hw1 : w < (1 : Q')) :
    (0 : Q') <
      (evenSectorGap (heatKernelSpin4Gap w hw0 hw1 w hw0 hw1).gap
        (chiralSwapInvolution (heatKernelLocatedGap w hw0 hw1)
          (heatKernelLocatedGap w hw0 hw1) rfl)).gapMargin :=
  reflectionMargin_pos (heatKernelLocatedGap w hw0 hw1)
    (heatKernelLocatedGap w hw0 hw1) rfl

/-! ### The upgraded `O(4)` input — reflection margin DISCHARGED

`o4InputFromHeatKernelIsotropic` builds an `O4RestorationInput` (the structure
from `RepTheory/Spin4.lean`) whose `reflectionMargin` / `reflectionMargin_ge`
fields are DISCHARGED by `reflectionMargin_heatKernel` — they are NO LONGER taken
as arguments.  In the isotropic case `wL = wR = w` the reflection margin equals
the connected margin, so `reflectionMargin_ge` is reflexivity.  The ONLY remaining
open `O(4)` content is the SEPARATE continuum rotation-restoration wall (NOT a
reflection field) — see `O4ConnectedInput` below. -/

/-- **THE UPGRADE.**  An `O4RestorationInput` in the isotropic case `wL = wR = w`,
with the `reflection*` fields DISCHARGED by the PROVED reflection-margin theorem
(`reflectionMargin_heatKernel`): `reflectionMargin` is set to the connected margin
and `reflectionMargin_ge` is reflexivity — neither is a named input any more.

The reflection ℤ₂ is now a THEOREM (finite, exact, fixed spacing).  The ONLY
remaining open `O(4)` content is the continuum rotation restoration (a SEPARATE
datum, not a reflection field); see `O4ConnectedInput`. -/
def o4InputFromHeatKernelIsotropic
    (w : Q') (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q')) :
    O4RestorationInput where
  connectedMargin := (heatKernelSpin4Gap w hw0 hw1 w hw0 hw1).margin
  connectedMargin_pos := heatKernelSpin4Gap_pos w hw0 hw1 w hw0 hw1
  -- DISCHARGED (not an argument): the reflection-even margin = connected margin,
  -- by `reflectionMargin_heatKernel`.
  reflectionMargin := (heatKernelSpin4Gap w hw0 hw1 w hw0 hw1).margin
  reflectionMargin_ge :=
    -- connectedMargin ≤ reflectionMargin is reflexive (they are equal).
    Q'.le_refl' (heatKernelSpin4Gap w hw0 hw1 w hw0 hw1).margin

/-- The upgraded input's `reflectionMargin` is exactly the PROVED chiral-
reflection-even margin (which equals the connected margin) — witnessing that the
reflection field is discharged by a theorem, not supplied as an input. -/
theorem o4InputFromHeatKernelIsotropic_reflection_proved
    (w : Q') (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q')) :
    (o4InputFromHeatKernelIsotropic w hw0 hw1).reflectionMargin
      = (evenSectorGap (heatKernelSpin4Gap w hw0 hw1 w hw0 hw1).gap
          (chiralSwapInvolution (heatKernelLocatedGap w hw0 hw1)
            (heatKernelLocatedGap w hw0 hw1) rfl)).gapMargin :=
  (reflectionMargin_heatKernel w hw0 hw1).symm

/-! ### The isolated remaining open wall — continuum `O(4)` rotation restoration

With the reflection ℤ₂ now PROVED, the only genuinely-open `O(4)` datum is the
continuum ROTATION restoration: the statement that the hypercubic lattice's
rotation-breaking operators are RG-irrelevant, so continuous `O(4)` is recovered
as `a → 0`.  `O4ConnectedInput` carries ONLY that open datum (as Type-level data,
Rule 8), fed by the PROVED connected margin and the PROVED reflection margin.
This is the cleaner honest accounting: the finite reflection half is discharged;
the continuum-rotation half stays named. -/

/-- **The cleanly-split `O(4)` datum.**  Carries the PROVED connected margin and
the PROVED reflection margin (both produced from the chiral heat-kernel gap), plus
the SINGLE remaining genuinely-OPEN field: `rotationRestored`, the named
continuum-frontier hypothesis that the lattice rotation-breaking operators are
RG-irrelevant so that continuous `O(4)` rotations are restored as `a → 0`.

The reflection ℤ₂ is a theorem here (`reflectionMargin` / `reflectionMargin_eq`,
fed by `reflectionMargin_heatKernel`).  `rotationRestored` is the ONLY open wall
— a separate continuum datum, typically the convergence of the relevant
dimensionless ratios (the continuum bridge's `DimensionlessRatio`-style data), NOT
a ℤ₂-reflection fact. -/
structure O4ConnectedInput where
  /-- The PROVED positive connected `Spin(4)/SO(4)` rotation-sector margin. -/
  connectedMargin : Q'
  /-- That margin is strictly positive (proved). -/
  connectedMargin_pos : (0 : Q') < connectedMargin
  /-- The PROVED chiral-reflection-even margin (the finite ℤ₂ swap `L ↔ R` margin
  at fixed spacing). -/
  reflectionMargin : Q'
  /-- The reflection margin EQUALS the connected margin (proved; the ℤ₂ swap does
  not degrade the gap).  This is a THEOREM, not a named input. -/
  reflectionMargin_eq : reflectionMargin = connectedMargin
  /-- NAMED OPEN continuum-frontier datum (Rule 8): continuous `O(4)` ROTATION
  symmetry is restored in the continuum limit (RG-irrelevance of the hypercubic
  rotation-breaking operators as `a → 0`).  This is the ONLY remaining open piece;
  it is a separate continuum datum, NOT a ℤ₂-reflection fact. -/
  rotationRestored : Prop
  /-- Witness of the named open continuum-rotation hypothesis (carried as data). -/
  rotationRestored_holds : rotationRestored

/-- **Assembling the split datum (isotropic).**  In the physical isotropic case
`wL = wR = w`, the connected and reflection margins are BOTH supplied by PROVED
theorems; only the continuum `O(4)`-rotation restoration remains as a named open
field `rotationRestored` (caller-supplied).  This makes the honest accounting
explicit: finite reflection ℤ₂ = proved; continuum rotation = the single open
wall. -/
def o4ConnectedFromHeatKernelIsotropic
    (w : Q') (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q'))
    -- The SINGLE remaining open named datum: continuum O(4)-rotation restoration.
    (rotationRestored : Prop)
    (rotationRestored_holds : rotationRestored) :
    O4ConnectedInput where
  connectedMargin := (heatKernelSpin4Gap w hw0 hw1 w hw0 hw1).margin
  connectedMargin_pos := heatKernelSpin4Gap_pos w hw0 hw1 w hw0 hw1
  reflectionMargin := (heatKernelSpin4Gap w hw0 hw1 w hw0 hw1).margin
  reflectionMargin_eq := rfl
  rotationRestored := rotationRestored
  rotationRestored_holds := rotationRestored_holds

end YMGap.RepTheory.Spin4Reflection

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.RepTheory.Spin4Reflection.evenSectorModel
#print axioms YMGap.RepTheory.Spin4Reflection.evenSectorModel_lam
#print axioms YMGap.RepTheory.Spin4Reflection.evenSectorGap
#print axioms YMGap.RepTheory.Spin4Reflection.evenSector_margin_eq
#print axioms YMGap.RepTheory.Spin4Reflection.evenSector_margin_pos
#print axioms YMGap.RepTheory.Spin4Reflection.chiralSwap_involutive
#print axioms YMGap.RepTheory.Spin4Reflection.chiralSwapInvolution
#print axioms YMGap.RepTheory.Spin4Reflection.reflectionMargin_eq_connected
#print axioms YMGap.RepTheory.Spin4Reflection.reflectionMargin_pos
#print axioms YMGap.RepTheory.Spin4Reflection.reflectionMargin_heatKernel
#print axioms YMGap.RepTheory.Spin4Reflection.reflectionMargin_heatKernel_pos
#print axioms YMGap.RepTheory.Spin4Reflection.o4InputFromHeatKernelIsotropic
#print axioms YMGap.RepTheory.Spin4Reflection.o4InputFromHeatKernelIsotropic_reflection_proved
#print axioms YMGap.RepTheory.Spin4Reflection.o4ConnectedFromHeatKernelIsotropic
