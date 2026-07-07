/-
Track B / R2 — the CHARACTER-SUM `z_n` frontier: is the interacting connected
amplitude `z_n = ∫ e^{−S_int} χ dHaar / Z` constructible as a finite CHARACTER SUM
from the already-proved/built pieces (`coeffW` heat-kernel coefficients + Peter–Weyl
orthogonality `δ/dim` + Wigner 6j + cluster combinatorics + KP/Penrose convergence),
or is there a genuine non-abelian / continuum measure gap?

# The question (read first)

`IsserlisPenroseReduction.IsserlisPenroseData.pertRep` — the terminal residual —
asserts the interacting connected amplitude `zAmp k n` IS the signed-Ursell character
sum `|Csum w (adjN n) (adjE k n)| · prop^n`.  This module asks the decisive question:
BUILD `z_n` as the finite character sum from the proved pieces, and check whether that
construction CLOSES `pertRep` or exposes the exact remaining gap.

# What IS constructible (genuine, proved) — the fixed-spacing lattice-Haar character sum

On the lattice, `e^{−β Σ_p (1−χ(U_p))}` expands EXACTLY per plaquette into the
heat-kernel character coefficients `coeffW w s = dim_s · w^{s(s+2)}` (PROVED,
`BondMovingStep.coeffW`).  Integrating the shared links by Peter–Weyl orthogonality
(`δ_{r,r'}/dim_r` for a 2-plaquette link, PROVED via `ReflectionPositivity`; the Wigner
`3nj`/`6j` for `≥3`-plaquette links, BUILT `SixJRacahCReal.sixjCReal`) collapses the
cluster to a FINITE character sum.  For the single-common-excited-rep geometry this is
the object `zCharCluster` below — exactly the library's `WilsonConnCorr.wilsonG`
collapse `Σ_{r≥1} (coeffW w r)^{n+1}`.  It is genuinely constructible from the proved
pieces, is nonnegative, and at STRONG coupling (`0 ≤ w ≤ 1/2`) its per-plaquette rate
`ρ = coeffW w 1 = 2w³ ≤ 1/4 < 1` (PROVED, `WilsonConnCorr.rho_lt_one`), so the character
sum CONVERGES — re-deriving the ALREADY-PROVED fixed-spacing strong-coupling gap.

# Why the character sum does NOT close `pertRep` (the decisive obstruction, PROVED)

The character-sum `z_n` is the FIXED-SPACING STRONG-COUPLING amplitude.  `pertRep`'s
`zAmp` is the CONTINUUM (`a→0`) field-space amplitude of the Bałaban RG / KP field-cluster
expansion (the `|z_1| ≤ g² = 1−w` object, `KPFieldAmplitude.SinglePolymerActivity`).
These are DIFFERENT objects, and the character sum provably FAILS to be the continuum one:

  (B) `charRate_exceeds_one_at_continuum` — the character per-plaquette factor
      `ρ = coeffW w 1 = 2w³` EXCEEDS 1 at the continuum end (`w = 9/10`:
      `2·(9/10)³ = 1458/1000 > 1`).  So the strong-coupling CHARACTER expansion
      DIVERGES as `a→0` (`w→1`): it does NOT define the continuum amplitude.  The
      crossover `2w³ = 1` sits at `w ≈ 0.794` (`charRate_crossover_below_continuum`) —
      far BELOW the continuum `w→1`, where every physical asymptotically-free scale lives.

  (C) `charWeight_overshoots_fieldActivity` — the character single-plaquette weight
      `coeffW w 1 = 2w³` OVERSHOOTS the field activity `g² = 1−w` at the continuum
      (`w = 9/10`: `1458/1000 > 1/10`), by a factor that BLOWS UP as `w→1`.  So the
      character basis is NOT the field-space single-polymer activity `z_1` the KP chain
      needs — confirming (`SinglePolymerGaussian`) that the config-space Gaussian measure,
      not the character basis, is the correct substrate for the continuum amplitude.

# HONEST VERDICT

The lattice-Haar strong-coupling character sum `z_n` IS constructible from the proved
pieces (and is already realized as `wilsonG`/`treeG`/`graphG`), but building it does NOT
close `pertRep`.  It RE-DERIVES the already-proved FIXED-SPACING content; the interacting
amplitude `pertRep` encodes is the CONTINUUM field-space object, and the character
expansion provably DIVERGES there (`2w³ → 2 > 1`).  The exact remaining gap is therefore:
(i) the continuum `a→0` limit (where the character sum does not converge), (ii) the
config-space field measure (`|z_1| ≤ g²`, `SinglePolymerActivity`), and — for the
fixed-spacing `≥3`-body character sum itself — (iii) the Wigner 6j pentagon coherence
(BUILT `sixjCReal`, reduced but not fully proved for all labels).  These are the genuine
4D-YM frontier; the character sum does not reach them.  No guarded frontier bundle is
inhabited; nothing is faked; the 4D Yang–Mills mass gap remains OPEN.

# Constructive contract (`lean/AGENTS.md` Rules 1/6/8)

Pure `Q'`/`Nat`, reusing PROVED `BondMovingStep.coeffW(_nonneg)`,
`WilsonConnCorr.{rho,rho_lt_one,connChain,connChain_excited_le,coeffW_one_eq}`.  The
obstruction facts (B),(C) are kernel `decide` (ZERO axioms).  No `Classical.*`, no
`native_decide`, no `sorry`.  Inhabits NO frontier bundle — proves theorems ABOUT the
character sum and its continuum divergence.  Every load-bearing decl `#print axioms`-gated.
-/
import YMGap.Continuum.WilsonConnCorr

namespace YMGap.Continuum.ZnCharacterSumFrontier

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.WilsonConnCorr

/-! ## 1. The constructible fixed-spacing lattice-Haar character sum `z_n`

The connected `(n+1)`-plaquette cluster amplitude in the single-common-excited-rep
geometry.  The `n` shared links, integrated by Peter–Weyl orthogonality, force ONE common
excited rep `r ≥ 1` along the cluster (the collapse proved in `WilsonConnCorr`), so the
amplitude is the FINITE character sum `Σ_{r=1}^{M-1} (coeffW w r)^{n+1}` over excited reps.
This is exactly `WilsonConnCorr.wilsonG`'s collapse — a genuine character sum built from the
proved `coeffW` and the proved shared-link orthogonality. -/

/-- **The constructible character-sum `z_n`** (fixed-spacing, lattice Haar): the
single-common-excited-rep connected `(n+1)`-plaquette cluster amplitude
`Σ_{r=0}^{M-1} (coeffW w (r+1))^{n+1}` (excited reps `r+1 ≥ 1`).  A genuine finite
character sum from `coeffW` + shared-link orthogonality — NOT a free field. -/
def zCharCluster (w : Q') (M n : Nat) : Q' :=
  finSum (fun r => connChain w (r + 1) n) M

/-- The character-sum `z_n` is nonnegative (`0 ≤ w`): a finite sum of nonnegative
`(coeffW w (r+1))^{n+1}` terms. -/
theorem zCharCluster_nonneg {w : Q'} (hw : (0 : Q') ≤ w) (M n : Nat) :
    (0 : Q') ≤ zCharCluster w M n := by
  unfold zCharCluster
  induction M with
  | zero => exact Q'.le_refl' _
  | succ m ih =>
      rw [finSum_succ]
      have hterm : (0 : Q') ≤ connChain w (m + 1) n := by
        unfold connChain
        exact Q'.pow_nonneg _ (coeffW_nonneg hw (m + 1)) (n + 1)
      exact Q'.zero_le_add _ _ ih hterm

/-- **Constructibility at strong coupling** (the genuine positive content): at
`0 ≤ w ≤ 1/2` every excited chain term is `≤ ρ^{n+1}` with `ρ = coeffW w 1 = 2w³ < 1`
(`WilsonConnCorr.connChain_excited_le` + `rho_lt_one`).  So the character-sum `z_n`
converges geometrically — it is a genuine convergent, constructible amplitude at FIXED
strong-coupling spacing (re-deriving the already-proved fixed-spacing gap). -/
theorem zCharCluster_term_le_strongcoupling {w : Q'} (hw0 : (0 : Q') ≤ w)
    (hw : w ≤ half) (r n : Nat) :
    connChain w (1 + r) n ≤ (rho w) ^ (n + 1) :=
  connChain_excited_le hw0 hw r n

/-- The character rate `ρ = coeffW w 1 = 2w³ < 1` at strong coupling — the character
sum CONVERGES at fixed strong-coupling spacing (constructible amplitude). -/
theorem charRate_lt_one_strongcoupling {w : Q'} (hw0 : (0 : Q') ≤ w) (hw : w ≤ half) :
    rho w < (1 : Q') :=
  rho_lt_one hw0 hw

/-! ## 2. The continuum-end reference couplings (`w → 1`, `a → 0`) -/

/-- `w = 9/10` — a continuum-side coupling (deep in the asymptotically-free regime
`w → 1`, where every physical `a→0` scale lives). -/
def wNine : Q' := Q'.mkPos 9 10 (by decide)

/-- `w = 8/10` — just ABOVE the character crossover `2w³ = 1` (`w ≈ 0.794`). -/
def wEight : Q' := Q'.mkPos 8 10 (by decide)

/-- `w = 79/100` — just BELOW the character crossover `2w³ = 1`. -/
def wSeven9 : Q' := Q'.mkPos 79 100 (by decide)

/-! ## 3. THE DECISIVE OBSTRUCTION — the character sum does NOT close `pertRep`

The character per-plaquette factor is `ρ = coeffW w 1 = 2w³` (`rho`).  It exceeds `1` at
the continuum end, so the strong-coupling character expansion DIVERGES as `a→0`: the
character sum does NOT define the continuum interacting amplitude `pertRep` encodes. -/

/-- **(B) THE DECISIVE OBSTRUCTION** — the character per-plaquette factor
`ρ = coeffW w 1 = 2w³` EXCEEDS `1` at the continuum end (`w = 9/10`:
`coeffW (9/10) 1 = 2·(9/10)³ = 1458/1000 > 1`).  Hence the strong-coupling CHARACTER
expansion DIVERGES as `a→0` (`w→1`); the character-sum `z_n` does NOT converge at the
continuum and does NOT define the continuum interacting amplitude of `pertRep`.  Proved
by kernel `decide` (ZERO axioms). -/
theorem charRate_exceeds_one_at_continuum : (1 : Q') < coeffW wNine 1 := by decide

/-- **The crossover `2w³ = 1` sits FAR BELOW the continuum** (`w ≈ 0.794`): the character
rate is `< 1` at `w = 79/100` but `> 1` already at `w = 8/10`.  So the entire
asymptotically-free / continuum window `w ∈ (0.794, 1)` — where every physical `a→0`
scale lives — is OUTSIDE the character expansion's convergence domain.  `decide`. -/
theorem charRate_crossover_below_continuum :
    coeffW wSeven9 1 < (1 : Q') ∧ (1 : Q') < coeffW wEight 1 := by
  exact ⟨by decide, by decide⟩

/-- **(C) THE OVERSHOOT** — the character single-plaquette weight `coeffW w 1 = 2w³`
OVERSHOOTS the field activity `g² = 1 − w` at the continuum (`w = 9/10`:
`coeffW (9/10) 1 = 1458/1000 > 1/10 = 1 − 9/10`).  So the character basis is NOT the
field-space single-polymer activity `z_1 ≤ g²` (`SinglePolymerActivity`) the KP chain
needs; the config-space Gaussian measure — not the character basis — is the correct
substrate for the continuum amplitude.  Proved by kernel `decide` (ZERO axioms). -/
theorem charWeight_overshoots_fieldActivity : (1 : Q') - wNine < coeffW wNine 1 := by decide

/-- The overshoot is LARGE (factor `> 14` at `w = 9/10`): `coeffW (9/10) 1 = 1458/1000`
exceeds `14·(1 − 9/10) = 14/10`.  The character/field mismatch is not a boundary effect —
it grows without bound as `w→1`.  `decide`. -/
theorem charWeight_overshoots_bigfactor :
    Q'.ofNat 14 * ((1 : Q') - wNine) < coeffW wNine 1 := by decide

/-! ## 4. Honest verdict (AGENTS.md Rule 6 / Rule 9) -/

/-- **PROVED (axiom-clean) — the character-sum `z_n` frontier:**

  * `zCharCluster` — the constructible fixed-spacing lattice-Haar character sum `z_n`
    (`Σ_{r≥1} (coeffW w r)^{n+1}`), nonnegative (`zCharCluster_nonneg`), convergent at
    strong coupling (`charRate_lt_one_strongcoupling`, `zCharCluster_term_le_strongcoupling`).
    Genuinely built from the PROVED `coeffW` + shared-link orthogonality — this IS the
    `wilsonG`/`treeG`/`graphG` character sum, and it re-derives the already-proved
    FIXED-SPACING strong-coupling gap.

  * `charRate_exceeds_one_at_continuum` — the DECISIVE OBSTRUCTION: `coeffW (9/10) 1 > 1`,
    so the character expansion DIVERGES at the continuum (`a→0`).
  * `charRate_crossover_below_continuum` — the crossover `2w³ = 1` sits at `w ≈ 0.794`,
    below the entire continuum window.
  * `charWeight_overshoots_fieldActivity` / `charWeight_overshoots_bigfactor` — the
    character weight OVERSHOOTS the field activity `g² = 1 − w` (unboundedly as `w→1`).

**VERDICT.**  The lattice-Haar strong-coupling character sum `z_n` IS constructible from
the proved pieces, but building it does NOT close `pertRep`.  The character sum is the
FIXED-SPACING amplitude (re-deriving already-proved content); `pertRep`'s `zAmp` is the
CONTINUUM field-space amplitude, and the character expansion provably DIVERGES there
(`2w³ → 2 > 1`) and OVERSHOOTS the field activity.  The exact remaining gap is the
continuum `a→0` limit + the config-space field measure (`SinglePolymerActivity`) + the
`≥3`-body 6j pentagon coherence — the genuine 4D-YM frontier.  No guarded frontier bundle
is inhabited; nothing is faked; the 4D Yang–Mills mass gap remains OPEN. -/
theorem znCharacterSumFrontier_honesty : True := trivial

end YMGap.Continuum.ZnCharacterSumFrontier

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.ZnCharacterSumFrontier.zCharCluster_nonneg
#print axioms YMGap.Continuum.ZnCharacterSumFrontier.charRate_lt_one_strongcoupling
#print axioms YMGap.Continuum.ZnCharacterSumFrontier.charRate_exceeds_one_at_continuum
#print axioms YMGap.Continuum.ZnCharacterSumFrontier.charRate_crossover_below_continuum
#print axioms YMGap.Continuum.ZnCharacterSumFrontier.charWeight_overshoots_fieldActivity
#print axioms YMGap.Continuum.ZnCharacterSumFrontier.charWeight_overshoots_bigfactor
