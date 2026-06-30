/-
Track B / R2 — `s = 1`-DOMINANCE of the bond-moved transfer spectrum: the gap edge
is the FIRST-EXCITED level, with the bond-moving (Clebsch–Gordan fusion) preserving
that dominance PROVED for the heat-kernel input at `p = 1` on the character window,
and REDUCED (precisely, honestly) to ONE named fusion obligation for the genuine
`p = b^{d−1}` bond-moving.

# Why this module exists — the cleanest sufficient statement for the gap to survive

The bond-moved single-plaquette operator is a class function, hence DIAGONAL in the
SU(2) character basis: its eigenvalues are exactly the bond-moved character
coefficients `bondMovedCoeff N w p s` (`BondMovingStep`).  The mass-gap edge is the
LARGEST EXCITED transfer eigenvalue, i.e. the largest of `bondMovedCoeff N w p s`
over `s ≥ 1`.  If that maximum is attained at `s = 1`,

    bondMovedCoeff N w p 1  ≥  bondMovedCoeff N w p s   for all `s ≥ 1`,

then the gap edge IS the `s = 1` level — which `BondMovingQuadratic`'s
`bondMovingDeltaRen_quadratic` controls QUADRATICALLY (summable) after the marginal
retune.  This `s = 1`-dominance is THE cleanest sufficient statement for the gap to
survive bond-moving, and it is what this module isolates and (partially) proves.

# The physics, made into a Lean question

`coeffW w s = (s+1)·w^{C₄(s)}`, `C₄(s) = s(s+2)`.  The bare Casimir factor
`w^{C₄(s)}` is monotone DECREASING in `s` (the Casimir `C₄` is increasing), so the
heat kernel is `s = 1`-dominant among the EXCITED modes — but only once the slowly
growing dimension factor `(s+1)` is beaten.  The genuine per-rep ratio
`coeffW w (s+1) ≤ (2w⁵)·coeffW w s` (`PlaquetteActivity.coeffW_succ_ratio`) shows the
non-increase holds exactly when `2w⁵ ≤ 1`, i.e. on the character window
`w ≤ wHi = 7/9 < 2^{−1/5}` (`CharacterWindowCeiling`).  Bond-moving raises the
single-plaquette class function to the power `p` and re-expands via the SU(2)
Clebsch–Gordan FUSION convolution (`fusionPow`).  The question this module answers
to the extent provable: does fusion PRESERVE `s = 1`-dominance?

# What is GENUINELY PROVED here — and the precise NAMED-open residual (honest)

PROVED (genuine `Q'`/`Nat`, axiom-clean):

  * `bmc_antitone_excited_p1` — for the HEAT-KERNEL input at `p = 1` (no bond-moving;
    the unit fusion identity makes `bondMovedCoeff N w 1 s ≃ coeffW w s`), the
    bond-moved coefficient is monotone NON-INCREASING in `s` among the excited modes:
    `bondMovedCoeff N w 1 (s+1) ≤ bondMovedCoeff N w 1 s` for `1 ≤ s`, `s+1 ≤ N`, on
    the character window `0 ≤ w ≤ wHi`.  (Reduces to
    `CharacterWindowCeiling.coeffW_succ_le_self_ext`.)
  * `bmc_one_dominates_p1` — the FULL `s = 1`-dominance at `p = 1`:
    `bondMovedCoeff N w 1 s ≤ bondMovedCoeff N w 1 1` for every excited `1 ≤ s ≤ N`
    on `[0, wHi]`.  (Reduces to `CharacterWindowCeiling.coeffW_excited_le_rho_ext`.)
  * `s1Dominance_p1` — INHABITS the `s = 1`-dominance datum `S1Dominance N w 1` on the
    window: the bond-moved (heat-kernel, `p = 1`) spectrum is provably `s = 1`-dominant.
  * `bmc_zero_pos` / `bmc_one_ge_coeffW_one` — the genuine GENERAL-`p` structural
    facts: the vacuum coefficient is strictly positive (`bondMovedCoeff N w p 0 > 0`,
    `p ≥ 1`) and the `s = 1` channel clears the bare heat-kernel floor
    `coeffW w 1 ≤ bondMovedCoeff N w p 1` (the identity fusion channel survives —
    `BondMovingRelResidual.bmc_ge_identity`).  These are the `s = 1` LOWER bound; the
    matching UPPER bound on the excited channels at `p ≥ 2` is the named residual.
  * `excited_spectrum_bounded_by_s1` — THE ASSEMBLY: given the `s = 1`-dominance datum
    `S1Dominance N w p` and the vacuum positivity, EVERY excited NORMALIZED transfer
    eigenvalue `bondMovedCoeff N w p s / bondMovedCoeff N w p 0` is `≤` the `s = 1`
    separator `sepBM` — i.e. the gap edge IS the `s = 1` level (`gapEdge_eq_s1`).
    Combined with `bondMovingDeltaRen_quadratic` (the `s = 1` retuned transverse
    defect is `O((1−w)²)`), `s = 1`-dominance turns the per-mode `s = 1` quadratic
    control into FULL-spectrum control.

NAMED OPEN (NOT inhabited):

  * `S1Dominance N w p` for the genuine 4D bond-moving exponent `p = b^{d−1} ≥ 2`.
    The `p = 1` datum is inhabited (`s1Dominance_p1`); whether the `p`-fold SU(2)
    Clebsch–Gordan FUSION convolution PRESERVES `s = 1`-dominance (the excited
    coefficients of `(Σ_s coeffW(s) χ_s)^p` are maximized at `s = 1`) at `p ≥ 2` is
    the remaining content.  The genuine `s = 1` LOWER bound is proved
    (`bmc_one_ge_coeffW_one`); the sharp residual is the matching UPPER bound on the
    excited fusion channels `bondMovedCoeff N w p s ≤ bondMovedCoeff N w p 1`
    (`s ≥ 2`) — the weighted SU(2) fusion-multiplicity monotonicity, the deep
    discrete-local-CLT tier (cf. `CubedDominance`).  NOT faked.

# Honest verdict and scope

`s = 1`-dominance is the clean sufficient statement for the gap to survive
bond-moving, and it is PROVED for the heat-kernel input at `p = 1` on the character
window `[0, 7/9]`, INHABITING `S1Dominance N w 1`.  The ASSEMBLY
`s1Dominance → gap edge = s = 1` is proved unconditionally in the datum.  For the
genuine `p ≥ 2` bond-moving, the `s = 1` LOWER bound (identity channel) is proved and
the residual is sharply isolated to the excited-channel UPPER bound (fusion
preserving dominance).  This is NOT a 4D Yang–Mills mass-gap proof; it is the
`s = 1`-dominance reduction with the `p = 1` case closed and the `p ≥ 2` case reduced
to one named fusion-monotonicity obligation.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat` arithmetic, the proved unit fusion identity, the proved character
window non-increase, `divPos` monotonicity, and the proved identity-channel lower
bound.  Every load-bearing declaration is gated with `#print axioms`; permitted
output is `propext` / `Quot.sound` only.  No `Classical.*`, no `native_decide` (only
`decide` on closed decidable `Q'` facts), no `sorry`.  All witnesses are `Type`-level
data.
-/

import YMGap.Continuum.BondMovingQuadratic
import YMGap.Continuum.BondMovingRelResidual
import YMGap.Continuum.BondMovingScaledNorm
import YMGap.Continuum.CharacterWindowCeiling

namespace YMGap.Continuum.S1Dominance

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.FusionQuotientCollapse
open YMGap.Continuum.BondMovingRelResidual
open YMGap.Continuum.BondMovingQuadratic
open YMGap.Continuum.CharacterWindowCeiling

/-! ## 0. The vacuum positivity (general `p`)

The bond-moved vacuum coefficient is `≥ coeffW w 0 = 1` by the identity fusion
channel (`bmc_ge_identity`), hence strictly positive: the divisor that normalizes the
transfer spectrum is well defined for every `p ≥ 1`. -/

/-- **`bondMovedCoeff N w p 0 > 0`** for `0 ≤ w ≤ 1`, `p ≥ 1`.  The identity fusion
channel gives `coeffW w 0 = 1 ≤ bondMovedCoeff N w p 0`, so the vacuum coefficient is
strictly positive (`0 < 1 ≤ bmc(0)`). -/
theorem bmc_zero_pos (N : Nat) {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (p : Nat) (hp : 0 < p) : (0 : Q') < bondMovedCoeff N w p 0 := by
  have h1 : coeffW w 0 ≤ bondMovedCoeff N w p 0 :=
    bmc_ge_identity N hw0 hw1 0 (Nat.zero_le N) p hp
  rw [coeffW_zero w] at h1
  exact q_lt_of_lt_of_le (by decide) h1

/-! ## 1. The `s = 1` LOWER bound (general `p`, the identity fusion channel)

For every `p ≥ 1` the `s = 1` bond-moved coefficient is at least the bare
heat-kernel value `coeffW w 1 = 2w³` (the `(1,0,…,0)` fusion channel survives with
coefficient `coeffW w 1`, all other channels are `≥ 0`).  This is the genuine
`s = 1` floor; the excited modes must clear it for `s = 1`-dominance. -/

/-- **`coeffW w 1 ≤ bondMovedCoeff N w p 1`** for `0 ≤ w ≤ 1`, `1 ≤ N`, `p ≥ 1`: the
first-excited bond-moved coefficient clears the bare heat-kernel floor `2w³` (the
identity fusion channel, `bmc_ge_identity`). -/
theorem bmc_one_ge_coeffW_one (N : Nat) {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (hN : 1 ≤ N) (p : Nat) (hp : 0 < p) :
    coeffW w 1 ≤ bondMovedCoeff N w p 1 :=
  bmc_ge_identity N hw0 hw1 1 hN p hp

/-! ## 2. `s = 1`-DOMINANCE at `p = 1` — the heat-kernel input (PROVED on the window)

At `p = 1` (one parallel plaquette = NO bond-moving) the unit fusion identity
collapses the convolution: `bondMovedCoeff N w 1 s ≃ coeffW w s` for `s ≤ N`
(`fusionPow_one_eq`).  So the bond-moved spectrum IS the heat-kernel spectrum on the
certified window, and the proved character non-increase
(`coeffW_succ_le_self_ext` / `coeffW_excited_le_rho_ext`, on `[0, wHi = 7/9]`) gives
both the one-step antitone and the full `s = 1`-dominance. -/

/-- **`bmc_antitone_excited_p1` — the one-step excited non-increase at `p = 1`.**  On
the character window `0 ≤ w ≤ wHi = 7/9`, for `1 ≤ s` and `s+1 ≤ N`,

    bondMovedCoeff N w 1 (s+1)  ≤  bondMovedCoeff N w 1 s.

PROOF: `bondMovedCoeff N w 1 (s+1) ≃ coeffW w (s+1)` and `bondMovedCoeff N w 1 s ≃
coeffW w s` (the unit fusion identity `fusionPow_one_eq`, both indices `≤ N`), then
the proved character non-increase `coeffW w (s+1) ≤ coeffW w s`
(`coeffW_succ_le_self_ext`, the per-rep ratio `2w⁵ ≤ 1` on `[0, wHi]`). -/
theorem bmc_antitone_excited_p1 (N : Nat) {w : Q'} (hw0 : (0 : Q') ≤ w) (hw : w ≤ wHi)
    (s : Nat) (hs : 1 ≤ s) (hsN : s + 1 ≤ N) :
    bondMovedCoeff N w 1 (s + 1) ≤ bondMovedCoeff N w 1 s := by
  have hsN' : s ≤ N := Nat.le_trans (Nat.le_succ s) hsN
  have e1 : (bondMovedCoeff N w 1 (s + 1)).eqv (coeffW w (s + 1)) := fusionPow_one_eq hsN
  have e2 : (bondMovedCoeff N w 1 s).eqv (coeffW w s) := fusionPow_one_eq hsN'
  have hcore : coeffW w (s + 1) ≤ coeffW w s := coeffW_succ_le_self_ext hw0 hw s hs
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv e1)
    (Q'.le_trans' _ _ _ hcore (Q'.le_of_eqv (Q'.eqv_symm e2)))

/-- **`bmc_one_dominates_p1` — FULL `s = 1`-dominance at `p = 1` (PROVED on the
window).**  On `0 ≤ w ≤ wHi = 7/9`, for every excited `1 ≤ s ≤ N`,

    bondMovedCoeff N w 1 s  ≤  bondMovedCoeff N w 1 1.

PROOF: write `s = 1 + k`; `bondMovedCoeff N w 1 (1+k) ≃ coeffW w (1+k)` and
`bondMovedCoeff N w 1 1 ≃ coeffW w 1` (unit fusion identity), and the proved
all-excited domination `coeffW w (1+k) ≤ coeffW w 1`
(`coeffW_excited_le_rho_ext`, `rho w = coeffW w 1`). -/
theorem bmc_one_dominates_p1 (N : Nat) {w : Q'} (hw0 : (0 : Q') ≤ w) (hw : w ≤ wHi)
    (s : Nat) (hs : 1 ≤ s) (hsN : s ≤ N) :
    bondMovedCoeff N w 1 s ≤ bondMovedCoeff N w 1 1 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hs
  -- s = 1 + k
  have h1N : 1 ≤ N := Nat.le_trans (Nat.le_add_right 1 k) hsN
  have eS : (bondMovedCoeff N w 1 (1 + k)).eqv (coeffW w (1 + k)) := fusionPow_one_eq hsN
  have e1 : (bondMovedCoeff N w 1 1).eqv (coeffW w 1) := fusionPow_one_eq h1N
  have hcore : coeffW w (1 + k) ≤ coeffW w 1 := coeffW_excited_le_rho_ext hw0 hw k
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv eS)
    (Q'.le_trans' _ _ _ hcore (Q'.le_of_eqv (Q'.eqv_symm e1)))

/-! ## 3. The `s = 1`-dominance datum and the gap-edge assembly -/

/-- **The `s = 1`-dominance datum** (`Type`-level): the bond-moved transfer spectrum
is maximized, among the excited modes `1 ≤ s ≤ N`, at the first-excited level `s = 1`:

    bondMovedCoeff N w p s  ≤  bondMovedCoeff N w p 1.

This is the clean sufficient statement for the gap edge to be the `s = 1` level.
Inhabited at `p = 1` on the character window (`s1Dominance_p1`); the `p ≥ 2`
(genuine bond-moving) inhabitant is the named-open fusion-monotonicity content. -/
structure S1Dominance (N : Nat) (w : Q') (p : Nat) : Type where
  /-- `s = 1` is the maximal excited bond-moved coefficient (within the cutoff). -/
  dominates : ∀ s, 1 ≤ s → s ≤ N → bondMovedCoeff N w p s ≤ bondMovedCoeff N w p 1

/-- **`s1Dominance_p1` — the `p = 1` `s = 1`-dominance datum (PROVED, INHABITED).**
On the character window `0 ≤ w ≤ wHi = 7/9` the heat-kernel (`p = 1`) bond-moved
spectrum is `s = 1`-dominant: discharged directly by `bmc_one_dominates_p1`. -/
def s1Dominance_p1 (N : Nat) {w : Q'} (hw0 : (0 : Q') ≤ w) (hw : w ≤ wHi) :
    S1Dominance N w 1 where
  dominates := fun s hs hsN => bmc_one_dominates_p1 N hw0 hw s hs hsN

/-- The NORMALIZED bond-moved transfer eigenvalue of mode `s`:
`bondMovedCoeff N w p s / bondMovedCoeff N w p 0`, guarded by the vacuum positivity.
At `s = 1` this is the gap-edge separator `sepBM`. -/
def normSep (N : Nat) (w : Q') (p : Nat)
    (h0 : (0 : Q') < bondMovedCoeff N w p 0) (s : Nat) : Q' :=
  Q'.divPos (bondMovedCoeff N w p s) (bondMovedCoeff N w p 0) h0

/-- `normSep` at `s = 1` is exactly the bond-moved gap separator `sepBM`. -/
theorem normSep_one_eq_sepBM (N : Nat) (w : Q') (p : Nat)
    (h0 : (0 : Q') < bondMovedCoeff N w p 0) :
    normSep N w p h0 1 = sepBM N w p h0 := rfl

/-- **THE ASSEMBLY — `s = 1`-dominance ⟹ the gap edge is the `s = 1` level.**  Given
the `s = 1`-dominance datum and the vacuum positivity, EVERY excited normalized
transfer eigenvalue is dominated by the `s = 1` separator:

    bondMovedCoeff N w p s / bondMovedCoeff N w p 0  ≤  sepBM N w p h0    (1 ≤ s ≤ N).

So the largest excited transfer eigenvalue — the mass-gap EDGE — is the `s = 1`
level.  PROOF: `divPos` is monotone in the numerator (positive divisor), applied to
`sd.dominates s`. -/
theorem excited_spectrum_bounded_by_s1 (N : Nat) {w : Q'} {p : Nat}
    (sd : S1Dominance N w p) (h0 : (0 : Q') < bondMovedCoeff N w p 0)
    (s : Nat) (hs : 1 ≤ s) (hsN : s ≤ N) :
    normSep N w p h0 s ≤ sepBM N w p h0 :=
  HeatKernelLinearBound.divPos_le_divPos_of_le h0 (sd.dominates s hs hsN)

/-- **`gapEdge_eq_s1` — the gap edge is the `s = 1` separator (PROVED, conditional on
the datum).**  Restatement of `excited_spectrum_bounded_by_s1` in `normSep`/`sepBM`
form for the assembly capstone: under `s = 1`-dominance, the `s = 1` separator
`sepBM` is the maximum of the excited normalized spectrum. -/
theorem gapEdge_eq_s1 (N : Nat) {w : Q'} {p : Nat}
    (sd : S1Dominance N w p) (h0 : (0 : Q') < bondMovedCoeff N w p 0)
    (s : Nat) (hs : 1 ≤ s) (hsN : s ≤ N) :
    normSep N w p h0 s ≤ normSep N w p h0 1 := by
  rw [normSep_one_eq_sepBM]
  exact excited_spectrum_bounded_by_s1 N sd h0 s hs hsN

/-! ## 4. The capstone — `s = 1`-dominance + the `s = 1` quadratic defect

`s = 1`-dominance (`excited_spectrum_bounded_by_s1`) places the gap edge at the
`s = 1` level; `BondMovingQuadratic.bondMovingDeltaRen_quadratic` then controls that
level's renormalized transverse defect QUADRATICALLY in the margin `1 − w` (after the
marginal retune).  Together they upgrade the per-mode `s = 1` quadratic control to
FULL-spectrum control — the bond-moving gap survives. -/

/-- **`s1_gap_edge_quadratic` — the capstone reduction.**  Given the `s = 1`-dominance
datum and the vacuum positivity, BOTH hold:

  (i)  the gap edge is the `s = 1` level — every excited normalized eigenvalue is
       `≤ sepBM` (`excited_spectrum_bounded_by_s1`); and
  (ii) the `s = 1` retuned transverse defect is QUADRATIC in the margin,
       `bondMovingDeltaRen N p w ≤ 18p·(1 − w)²` (`bondMovingDeltaRen_quadratic`).

So under `s = 1`-dominance the gap edge is the `s = 1` level whose deviation from the
flat continuum value is quadratic (summable along asymptotic freedom).  This is the
precise sense in which `s = 1`-dominance + the `s = 1` quadratic defect close the
bond-moving gap-survival argument. -/
theorem s1_gap_edge_quadratic (N : Nat) {w : Q'} {p : Nat}
    (sd : S1Dominance N w p) (h0 : (0 : Q') < bondMovedCoeff N w p 0)
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) :
    (∀ s, 1 ≤ s → s ≤ N → normSep N w p h0 s ≤ sepBM N w p h0)
      ∧ bondMovingDeltaRen N p w
          ≤ (Q'.ofNat p * (dimQ 1 * (Q'.ofNat (c4 1) * Q'.ofNat (c4 1))))
              * (((1 : Q') - w) * ((1 : Q') - w)) :=
  ⟨ fun s hs hsN => excited_spectrum_bounded_by_s1 N sd h0 s hs hsN
  , bondMovingDeltaRen_quadratic hw0 hw1 N p ⟩

/-- **`s1_gap_edge_quadratic_p1` — the capstone, fully discharged at `p = 1`.**  On the
character window `0 ≤ w ≤ wHi = 7/9` the `s = 1`-dominance datum is inhabited
(`s1Dominance_p1`), so the capstone holds UNCONDITIONALLY for the heat-kernel input:
the gap edge is the `s = 1` level and its retuned transverse defect is quadratic.
(The vacuum positivity is the proved `bmc_zero_pos`.) -/
theorem s1_gap_edge_quadratic_p1 (N : Nat) {w : Q'} (hw0 : (0 : Q') ≤ w)
    (hw : w ≤ wHi)
    (h0 : (0 : Q') < bondMovedCoeff N w 1 0) :
    (∀ s, 1 ≤ s → s ≤ N → normSep N w 1 h0 s ≤ sepBM N w 1 h0)
      ∧ bondMovingDeltaRen N 1 w
          ≤ (Q'.ofNat 1 * (dimQ 1 * (Q'.ofNat (c4 1) * Q'.ofNat (c4 1))))
              * (((1 : Q') - w) * ((1 : Q') - w)) := by
  have hw1 : w ≤ (1 : Q') := Q'.le_trans' _ _ _ hw (by decide)
  exact s1_gap_edge_quadratic N (s1Dominance_p1 N hw0 hw) h0 hw0 hw1

/-! ## 5. Doc-section — PROVED vs. NAMED-open (CRITICAL honesty)

PROVED (axiom-clean, `[propext]` / `[propext, Quot.sound]`):

  * `bmc_zero_pos` — the vacuum coefficient is strictly positive for every `p ≥ 1`
    (identity channel `coeffW w 0 = 1 ≤ bmc(0)`); the normalizing divisor is well
    defined.
  * `bmc_one_ge_coeffW_one` — the `s = 1` LOWER bound for every `p ≥ 1`: the
    first-excited bond-moved coefficient clears the bare floor `coeffW w 1 = 2w³`.
  * `bmc_antitone_excited_p1` / `bmc_one_dominates_p1` — at `p = 1` (heat-kernel
    input, unit fusion identity), the bond-moved spectrum is one-step antitone and
    fully `s = 1`-dominant on the character window `[0, wHi = 7/9]`.
  * `s1Dominance_p1` — INHABITS `S1Dominance N w 1` on the window: the `p = 1`
    bond-moved spectrum is provably `s = 1`-dominant.
  * `excited_spectrum_bounded_by_s1` / `gapEdge_eq_s1` — THE ASSEMBLY: the
    `s = 1`-dominance datum forces the gap edge to be the `s = 1` normalized
    eigenvalue (`sepBM`).
  * `s1_gap_edge_quadratic` (+ `_p1`) — the capstone: `s = 1`-dominance + the proved
    `s = 1` quadratic retuned defect (`bondMovingDeltaRen_quadratic`) give gap-edge
    control that is quadratic in the margin; fully discharged at `p = 1`.

NAMED OPEN (NOT inhabited):

  * `S1Dominance N w p` at the genuine 4D bond-moving exponent `p = b^{d−1} ≥ 2`.
    The `s = 1` LOWER bound is proved (`bmc_one_ge_coeffW_one`); the sharp residual is
    the matching UPPER bound on the excited fusion channels
    `bondMovedCoeff N w p s ≤ bondMovedCoeff N w p 1` (`s ≥ 2`) — i.e. that the
    `p`-fold SU(2) Clebsch–Gordan FUSION convolution PRESERVES `s = 1`-dominance.
    This is the weighted fusion-multiplicity monotonicity, the deep discrete-local-CLT
    tier (sibling of `CubedDominance`).  It is NOT inhabited here and NOT faked.

HONEST VERDICT.  `s = 1`-dominance is the cleanest sufficient statement for the gap
to survive bond-moving; it is PROVED for the heat-kernel input at `p = 1` on the
character window (`s1Dominance_p1`), and the assembly `s = 1`-dominance ⟹ gap edge
= `s = 1` (whose retuned defect is quadratic) is proved in the datum.  For the genuine
`p ≥ 2` bond-moving the `s = 1` floor is proved and the residual is sharply isolated
to the excited-channel upper bound (fusion preserves dominance).  This is NOT a 4D
Yang–Mills mass-gap proof; it is the `s = 1`-dominance reduction, `p = 1` closed and
`p ≥ 2` reduced to one named fusion-monotonicity obligation. -/

end YMGap.Continuum.S1Dominance

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.S1Dominance.bmc_zero_pos
#print axioms YMGap.Continuum.S1Dominance.bmc_one_ge_coeffW_one
#print axioms YMGap.Continuum.S1Dominance.bmc_antitone_excited_p1
#print axioms YMGap.Continuum.S1Dominance.bmc_one_dominates_p1
#print axioms YMGap.Continuum.S1Dominance.s1Dominance_p1
#print axioms YMGap.Continuum.S1Dominance.normSep_one_eq_sepBM
#print axioms YMGap.Continuum.S1Dominance.excited_spectrum_bounded_by_s1
#print axioms YMGap.Continuum.S1Dominance.gapEdge_eq_s1
#print axioms YMGap.Continuum.S1Dominance.s1_gap_edge_quadratic
#print axioms YMGap.Continuum.S1Dominance.s1_gap_edge_quadratic_p1
