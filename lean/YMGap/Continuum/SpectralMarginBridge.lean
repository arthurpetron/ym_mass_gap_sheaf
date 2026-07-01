/-
Track B / R2 — **DISCHARGING the `hadd` feeding field of `SpectralMarginInput`
from the proved eigenvalue-location facts + pure `Q'` arithmetic.**

# What this module does (read first)

`AsymptoticSpectralLoc.SpectralMarginInput` had TWO open feeding fields:

  * `hadd` — the located-2nd-eigenvalue ↔ physical-margin dictionary
        `g_k − shift_k ≤ g_{k+1}`,   `g_k := divPos (floorRate_k) (a_k)`;
  * `hbridge` — the shift control `shift_k ≤ δ_k · g_k` (= `bulk_shift`, node ①).

This module PRODUCES `hadd` (in its exact field shape, fixed-spacing regime — the
live Stage-1 case) as a THEOREM, from:

  * the PROVED eigenvalue-location content read at the gap edge `s = 1`
    (`SpectralLocalization.pert`), plus
  * two honest model hookups — the next-scale-edge identification
    `hEdge : eigA (w (k+1)) 1 = (L k).eig' 1` and the floor-rate dictionary
    `hFR : (atSpacing k).floorRate = heatKernelMargin (w k)` — and
  * pure `Q'` order transport (`divPos` numerator-monotonicity + same-denominator
    `divPos` subtraction).

After this plumbing the ONLY surviving honest residual feeding the physical-gap
recursion is node ① (`SpectralLocalization.bulk_shift`, `shift s ≤ 1/12`): the
`weight-defect ⟹ eigenvalue-shift` bridge.  `hadd` is no longer independent.

# The reduction chain (as implemented)

  * **§1 same-denominator `divPos` algebra** — `sub_divPos_eqv` (N1) and
    `add_divPos_eqv` (its additive mirror), each a ~4-line `Q'` `eqv`.

  * **§2 the `a_k`-rescaling of a LATTICE margin drop to the physical `hadd`** —
    `hadd_of_hlat_fixed` (fixed spacing, via N1 + `divPos_le_divPos_of_le`) and
    `hadd_of_hlat_varying` (varying spacing, via cross-multiplication
    `divPos_le_divPos_of_cross` + the `sub_le_of_le_add` adjunction).

  * **§3 the LATTICE margin drop `hlat` from `pert` at `s = 1`** —
    `hlat_margin`: reading `pert` in `1 − (·)` margin units at the gap edge
    (using `heatKernelMargin w = 1 − eigA w 1`, since `eigA w 1 = w³ =
    heatKernelSep w`), so `margin_k − shift_k ≤ margin_{k+1}`.

  * **§4 the discharge** — `hadd_from_edge_residual` (and the bundling
    `EdgeLocalizationResidual` / `.hadd`) produces the field-shaped `hadd`
    for every `k`.

# Honest scope

Nothing here conjures the gap.  `EdgeLocalizationResidual` is NOT inhabited on ℝ⁴:
its `L k : SpectralLocalization (w k)` still carries the open `bulk_shift` field
(node ①), and `hEdge` / `hFR` are model hookups.  What is genuinely NEW is that
`hadd` becomes a THEOREM of those residuals rather than a parallel open field: the
`a_k`-rescaling and the `s = 1` margin reading are axiom-clean `Q'` facts.

The √-bridge is OFF the critical path: `floorRate_k = 1 − w_k³` is a rational
string-tension-unit margin, so the whole discharge is `Q'`-level order transport
and never invokes `√`.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat` arithmetic over the proved `SpectralLocalizationCrux` /
`HeatKernelGap` / `HeatKernelLinearBound` / `FusionMarginMono` lemmas.  Every
carrier is `Type`-level data.  Each load-bearing declaration is gated with
`#print axioms`; permitted output is `propext` / `Quot.sound` only.  No
`Classical.*`, no `native_decide`, no `sorry`, no custom `axiom`.
-/

import YMGap.Continuum.SpectralLocalizationCrux
import YMGap.Continuum.HeatKernelLinearBound
import YMGap.Continuum.FusionMarginMono
import YMGap.Continuum.RegularContinuumPipeline

namespace YMGap.Continuum.SpectralMarginBridge

open YMGap.Constructive
open YMGap.Continuum.HeatKernelGap
open YMGap.Continuum.HeatKernelLinearBound
open YMGap.Continuum.FusionMarginMono
open YMGap.Continuum.SpectralLocalizationCrux
open YMGap.Continuum.RegularContinuumPipeline

/-! ## 1. Same-denominator `divPos` algebra (N1 and its additive mirror) -/

/-- **(N1)** — same-denominator `divPos` SUBTRACTION:
`divPos p q − divPos p' q ≃ divPos (p − p') q` for `0 < q`.  The exact mirror of
`HeatKernelRGStep.one_sub_divPos_eqv` (the `p = 1` template).  PROOF:
`(p − p')·(1/q) ≃ p·(1/q) + (−p')·(1/q) ≃ p·(1/q) − p'·(1/q)`. -/
theorem sub_divPos_eqv (p p' q : Q') (hq : (0 : Q') < q) :
    (Q'.divPos p q hq - Q'.divPos p' q hq).eqv (Q'.divPos (p - p') q hq) := by
  have h1 : ((p - p') * Q'.recipPos q hq).eqv
      (p * Q'.recipPos q hq + (-p') * Q'.recipPos q hq) :=
    Q'.add_mul_eqv p (-p') (Q'.recipPos q hq)
  have h2 : (p * Q'.recipPos q hq + (-p') * Q'.recipPos q hq).eqv
      (p * Q'.recipPos q hq + -(p' * Q'.recipPos q hq)) :=
    Q'.add_eqv_congr_left (p * Q'.recipPos q hq) ((-p') * Q'.recipPos q hq)
      (-(p' * Q'.recipPos q hq)) (Q'.neg_mul_eqv p' (Q'.recipPos q hq))
  exact Q'.eqv_symm (Q'.eqv_trans _ _ _ h1 h2)

/-- Same-denominator `divPos` ADDITION: `divPos p q + divPos p' q ≃ divPos (p+p') q`.
(Used by the varying-spacing rescaling.)  PROOF: `(p+p')·(1/q) ≃ p·(1/q)+p'·(1/q)`. -/
theorem add_divPos_eqv (p p' q : Q') (hq : (0 : Q') < q) :
    (Q'.divPos p q hq + Q'.divPos p' q hq).eqv (Q'.divPos (p + p') q hq) :=
  Q'.eqv_symm (Q'.add_mul_eqv p p' (Q'.recipPos q hq))

/-! ## 2. `a_k`-rescaling of a lattice margin drop to the physical `hadd` -/

/-- **FIXED-SPACING rescaling (the live Stage-1 regime).**  From the lattice-level
margin drop `FR_k − shiftLat_k ≤ FR_{k+1}` (all at the SAME spacing `a`), divide
through by `a`:

    divPos FR_k a − divPos shiftLat_k a  ≤  divPos FR_{k+1} a,

which IS the physical `hadd` with `shift_k := divPos shiftLat_k a`.  PROOF: N1
turns the LHS into `divPos (FR_k − shiftLat_k) a`, then `divPos_le_divPos_of_le`
on the lattice drop. -/
theorem hadd_of_hlat_fixed (FRk FRk1 shiftLat a : Q') (ha : (0 : Q') < a)
    (hlat : FRk - shiftLat ≤ FRk1) :
    Q'.divPos FRk a ha - Q'.divPos shiftLat a ha ≤ Q'.divPos FRk1 a ha := by
  have he : (Q'.divPos FRk a ha - Q'.divPos shiftLat a ha).eqv
      (Q'.divPos (FRk - shiftLat) a ha) := sub_divPos_eqv FRk shiftLat a ha
  have hmono : Q'.divPos (FRk - shiftLat) a ha ≤ Q'.divPos FRk1 a ha :=
    divPos_le_divPos_of_le ha hlat
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv he) hmono

/-- **VARYING-SPACING rescaling.**  With `shift_k := divPos sNum a_{k+1}`, the
cross-multiplied polynomial inequality `FR_k · a_{k+1} ≤ (sNum + FR_{k+1}) · a_k`
yields the physical `hadd`

    divPos FR_k a_k − divPos sNum a_{k+1}  ≤  divPos FR_{k+1} a_{k+1}.

PROOF: cross-monotonicity gives `g_k ≤ divPos (sNum+FR_{k+1}) a_{k+1}`; the
same-denominator ADD splits that as `shift_k + g_{k+1}`; the `sub_le_of_le_add`
adjunction rewrites `g_k ≤ shift_k + g_{k+1}` into `g_k − shift_k ≤ g_{k+1}`. -/
theorem hadd_of_hlat_varying (FRk FRk1 sNum ak ak1 : Q')
    (hak : (0 : Q') < ak) (hak1 : (0 : Q') < ak1)
    (hcross : FRk * ak1 ≤ (sNum + FRk1) * ak) :
    Q'.divPos FRk ak hak - Q'.divPos sNum ak1 hak1 ≤ Q'.divPos FRk1 ak1 hak1 := by
  have hcr : Q'.divPos FRk ak hak ≤ Q'.divPos (sNum + FRk1) ak1 hak1 :=
    divPos_le_divPos_of_cross FRk ak (sNum + FRk1) ak1 hak hak1 hcross
  have hsplit : (Q'.divPos sNum ak1 hak1 + Q'.divPos FRk1 ak1 hak1).eqv
      (Q'.divPos (sNum + FRk1) ak1 hak1) := add_divPos_eqv sNum FRk1 ak1 hak1
  have hle : Q'.divPos FRk ak hak
      ≤ Q'.divPos sNum ak1 hak1 + Q'.divPos FRk1 ak1 hak1 :=
    Q'.le_trans' _ _ _ hcr (Q'.ge_of_eqv hsplit)
  exact Q'.sub_le_of_le_add hle

/-! ## 3. The lattice margin drop `hlat` from `pert` at the gap edge `s = 1` -/

/-- `heatKernelMargin w = 1 − eigA w 1` (the gap-edge eigenvalue reading of the
heat-kernel margin): `eigA w 1 = w^{c4 1} = w³ = heatKernelSep w` (`c4 1 = 3`),
so `1 − heatKernelSep w = 1 − eigA w 1`.  A definitional identity. -/
theorem heatKernelMargin_eq_oneSub_eigA (w : Q') :
    heatKernelMargin w = 1 - eigA w 1 := rfl

/-- **THE LATTICE MARGIN DROP `hlat` (the `s = 1` reading of `pert`).**  From a
spectral-localization certificate `L k : SpectralLocalization (w k)` at each scale
and the next-scale-edge identification `eigA (w (k+1)) 1 = (L k).eig' 1`, the gap
edge (`s = 1`) case of `pert` reads, in `1 − (·)` margin units, as the additive
margin drop

    heatKernelMargin (w k) − (L k).shift 1  ≤  heatKernelMargin (w (k+1)).

PROOF: `pert 1` gives `(L k).eig' 1 ≤ eigA (w k) 1 + (L k).shift 1`; the edge
identification rewrites the LHS to `eigA (w (k+1)) 1`; negating and adding `1`
(with `heatKernelMargin = 1 − eigA · 1`) yields the drop. -/
theorem hlat_margin (w : Nat → Q') (L : ∀ k, SpectralLocalization (w k))
    (hEdge : ∀ k, eigA (w (k + 1)) 1 = (L k).eig' 1) (k : Nat) :
    heatKernelMargin (w k) - (L k).shift 1 ≤ heatKernelMargin (w (k + 1)) := by
  -- abbreviations (as plain expressions; `heatKernelMargin w j ≡ 1 − eigA (w j) 1`)
  -- eigA (w (k+1)) 1 ≤ eigA (w k) 1 + shift 1
  have hp : (L k).eig' 1 ≤ eigA (w k) 1 + (L k).shift 1 := (L k).pert 1
  have hb : eigA (w (k + 1)) 1 ≤ eigA (w k) 1 + (L k).shift 1 := by
    rw [hEdge k]; exact hp
  -- negate and add 1:  (1 + −a) + −s ≤ 1 + −b
  have hneg : -(eigA (w k) 1 + (L k).shift 1) ≤ -(eigA (w (k + 1)) 1) :=
    Q'.neg_le_neg hb
  have hne : (-(eigA (w k) 1 + (L k).shift 1)).eqv
      (-(eigA (w k) 1) + -((L k).shift 1)) :=
    Q'.neg_add_eqv (eigA (w k) 1) ((L k).shift 1)
  have hneg' : -(eigA (w k) 1) + -((L k).shift 1) ≤ -(eigA (w (k + 1)) 1) :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv hne) hneg
  have hadd1 : (1 : Q') + (-(eigA (w k) 1) + -((L k).shift 1))
      ≤ (1 : Q') + -(eigA (w (k + 1)) 1) :=
    Q'.add_le_add_left 1 _ _ hneg'
  have hassoc : (((1 : Q') + -(eigA (w k) 1)) + -((L k).shift 1)).eqv
      ((1 : Q') + (-(eigA (w k) 1) + -((L k).shift 1))) :=
    Q'.add_assoc_eqv 1 (-(eigA (w k) 1)) (-((L k).shift 1))
  -- transport back through heatKernelMargin = 1 − eigA·1
  show ((1 : Q') - eigA (w k) 1) - (L k).shift 1 ≤ (1 : Q') - eigA (w (k + 1)) 1
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hassoc) hadd1

/-! ## 4. The discharge — the field-shaped `hadd` -/

/-- **THE EDGE-LOCALIZATION RESIDUAL (named open content).**  Bundles the honest
inputs from which `hadd` becomes a theorem in the fixed-spacing regime:

  * `w` — the RG weight trajectory `0 ≤ w k ≤ 1`;
  * `L` — the per-scale spectral-localization certificate (still carries the OPEN
    `bulk_shift` = node ①);
  * `hEdge` — the next-scale-edge identification (model hookup);
  * `atSpacing` / `spacing a` — the fixed physical spacing schedule;
  * `hFR` — the floor-rate dictionary `floorRate_k = heatKernelMargin (w k)`.

NOT inhabited on ℝ⁴ (its `L` still carries node ①). -/
structure EdgeLocalizationResidual : Type where
  /-- The RG weight trajectory. -/
  w : Nat → Q'
  /-- The per-scale spectral-localization certificate (open `bulk_shift`). -/
  L : ∀ k, SpectralLocalization (w k)
  /-- The next-scale gap-edge identification. -/
  hEdge : ∀ k, eigA (w (k + 1)) 1 = (L k).eig' 1
  /-- The fixed-spacing infinite-volume cluster bounds. -/
  atSpacing : Nat → RegUniformClusterBound
  /-- The (fixed) lattice spacing. -/
  spacing : Q'
  /-- The spacing is strictly positive. -/
  spacing_pos : (0 : Q') < spacing
  /-- The floor-rate dictionary `floorRate_k = 1 − w_k³`. -/
  hFR : ∀ k, (atSpacing k).floorRate = heatKernelMargin (w k)

/-- **THE DISCHARGE.**  From an `EdgeLocalizationResidual`, the physical `hadd`
inequality holds at every scale `k`, with `shift_k := divPos ((L k).shift 1) a`:

    divPos (floorRate_k) a − divPos ((L k).shift 1) a  ≤  divPos (floorRate_{k+1}) a.

This is exactly the fixed-spacing `SpectralMarginInput.hadd` field shape.  PROOF:
`hlat_margin` (edge reading of `pert`) rewritten through `hFR` gives the lattice
drop, then `hadd_of_hlat_fixed` rescales it by `a`. -/
theorem EdgeLocalizationResidual.hadd (R : EdgeLocalizationResidual) (k : Nat) :
    Q'.divPos ((R.atSpacing k).floorRate) R.spacing R.spacing_pos
        - Q'.divPos ((R.L k).shift 1) R.spacing R.spacing_pos
      ≤ Q'.divPos ((R.atSpacing (k + 1)).floorRate) R.spacing R.spacing_pos := by
  have hlat : (R.atSpacing k).floorRate - (R.L k).shift 1
      ≤ (R.atSpacing (k + 1)).floorRate := by
    rw [R.hFR k, R.hFR (k + 1)]
    exact hlat_margin R.w R.L R.hEdge k
  exact hadd_of_hlat_fixed _ _ _ R.spacing R.spacing_pos hlat

/-- The same discharge stated as a standalone theorem over loose data (no bundling),
matching the `SpectralMarginInput.hadd` field verbatim in the fixed-spacing case. -/
theorem hadd_from_edge_residual
    (atSpacing : Nat → RegUniformClusterBound)
    (a : Q') (ha : (0 : Q') < a)
    (w : Nat → Q')
    (L : ∀ k, SpectralLocalization (w k))
    (hEdge : ∀ k, eigA (w (k + 1)) 1 = (L k).eig' 1)
    (hFR : ∀ k, (atSpacing k).floorRate = heatKernelMargin (w k))
    (k : Nat) :
    Q'.divPos ((atSpacing k).floorRate) a ha - Q'.divPos ((L k).shift 1) a ha
      ≤ Q'.divPos ((atSpacing (k + 1)).floorRate) a ha := by
  have hlat : (atSpacing k).floorRate - (L k).shift 1
      ≤ (atSpacing (k + 1)).floorRate := by
    rw [hFR k, hFR (k + 1)]
    exact hlat_margin w L hEdge k
  exact hadd_of_hlat_fixed _ _ _ a ha hlat

end YMGap.Continuum.SpectralMarginBridge

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.SpectralMarginBridge.sub_divPos_eqv
#print axioms YMGap.Continuum.SpectralMarginBridge.add_divPos_eqv
#print axioms YMGap.Continuum.SpectralMarginBridge.hadd_of_hlat_fixed
#print axioms YMGap.Continuum.SpectralMarginBridge.hadd_of_hlat_varying
#print axioms YMGap.Continuum.SpectralMarginBridge.hlat_margin
#print axioms YMGap.Continuum.SpectralMarginBridge.EdgeLocalizationResidual.hadd
#print axioms YMGap.Continuum.SpectralMarginBridge.hadd_from_edge_residual
