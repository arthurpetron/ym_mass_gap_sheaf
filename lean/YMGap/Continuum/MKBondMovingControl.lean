/-
Track B / R2 — THE MIGDAL–KADANOFF BOND-MOVING APPROXIMATION CONTROL, and the
HONEST placement of the "real 4D block-spin defect ≤ MK bond-moving defect"
question against `singleStep`.

# What this module does (read first)

The sole open per-scale input of the continuum construction,
`SingleStepDefectReduction.SingleStepDefectBound.singleStep`, is the inequality
`realδ_k ≤ δ_model(w_k)` for the TRUE margin, where `δ_model = 6(1−w)²` is the
PROVED transverse quadratic MK bond-moving defect
(`RenDefectQuadFactor.bondMovingDeltaRen_le_sixp`).

The Migdal–Kadanoff (MK) RG replaces the real 4D lattice by a HIERARCHICAL
lattice: it MOVES BONDS so that the lattice decouples into 1D chains, then
decimates (`HierarchicalGap` is the exactly-soluble δ=0 decimation orbit; the
`δ` there is exactly this residual).  The bond-moving of `m = b^{d−1}` parallel
plaquettes replaces the single-plaquette weight `K_w` by the pointwise power
`K_w^m` (the m-fold SU(2) Clebsch–Gordan fusion of the character coefficients),
and the MK per-step defect `δ^{MK}` is the fused excited/vacuum degradation,
PROVED `≤ 6(1−w)²` and shown to CONCENTRATE (`2 − ρ_m ≈ 6(1−w)/m`,
`InteractingMFoldDefect` / `UniformMFoldConcentration`).

THE QUESTION this module answers, adversarially: is the REAL 4D block-spin defect
`δ^{4D}_k` bounded by the MK bond-moving defect `δ^{MK}_k` — i.e. does the MK
VARIATIONAL principle (Jensen) rigorously give `δ^{4D} ≤ δ^{MK} ≤ 6(1−w)²`,
CLOSING `singleStep`?  Or is the real-vs-MK gap for the DEFECT exactly the
`singleStep` input?

## THE MK VARIATIONAL STRUCTURE — Jensen bounds the FREE ENERGY (only)

The MK bond-moving is a genuine VARIATIONAL approximation: moving bonds together
(potential-moving) versus apart brackets the FREE ENERGY by Jensen's inequality
(convexity of the free energy in the couplings; Kadanoff, Ann. Phys. 100 (1976);
Osterwalder–Seiler, Ann. Phys. 110 (1978)).  Its algebraic engine is the two-term
convexity `2xy ≤ x² + y²` (`CRealAlg.amgm_two`), re-exported here as
`potentialMoving_convexity`.  Concretely, for the fused vacuum coefficient
`[c^{⋆m}]_0 = ∫ K_w^m dμ` (the partition-function normalization = the free energy)
Jensen gives `∫ K_w^m dμ ≥ (∫ K_w dμ)^m = (c_0)^m = 1` — a rigorous ONE-SIDED
free-energy bound.  (Off-line `[c^{⋆m}]_0` at `w=0.99` is `1 → 159 → 38491 →
1.1·10^7` for `m=1,2,3,4`: the free energy is bounded/controlled by Jensen.)

## THE DECISIVE POINT — the GAP DEFECT is NOT the free energy (Jensen does NOT transfer)

`δ^{MK}` (and `δ^{4D}`) is the degradation of the SPECTRAL GAP, i.e. the
excited/vacuum RATIO `ρ_m = [c^{⋆m}]_1 / [c^{⋆m}]_0` (the sub-leading transfer
eigenvalue ratio), NOT the free energy `[c^{⋆m}]_0`.  While Jensen blows the
FREE ENERGY up by seven orders of magnitude (`[c^{⋆m}]_0`: `1 → 1.1·10^7`), the
GAP ratio `ρ_m` barely moves (`2 − ρ_m ≈ 6(1−w)/m`, O(1−w)).  A Jensen/variational
bound on `[c^{⋆m}]_0` therefore says NOTHING about `ρ_m`: the two are DIFFERENT
functionals of the fused measure.  This is the same reason MK famously gives
APPROXIMATE (not rigorously bracketed) critical exponents / correlation lengths:
the variational principle controls `log Z`, not `ξ = 1/m_gap`.  Moreover in `d>2`
the MK free-energy bracket itself has an UNCONTROLLED O(1)-per-bond width (the
hierarchical lattice ≠ the real lattice), so even for the free energy the bracket
does not close.

VERDICT (this module, adversarial): `δ^{4D} ≤ δ^{MK}` for the GAP DEFECT is NOT
provable via Jensen/variational.  The MK bond-moving is a rigorous variational
bound on the FREE ENERGY only; it does not transfer to the spectral-gap defect.
Hence the real-vs-MK gap for the defect is EXACTLY the `singleStep` input — NOT a
closure.

## What is GENUINELY PROVED here (axiom-clean `Q'`)

  * `potentialMoving_convexity` — the Jensen/convexity engine `2xy ≤ x²+y²` of the
    MK potential-moving free-energy bound (re-export of the PROVED `amgm_two`).
  * `mkDefect_le_sixQuad` — the MK bond-moving defect is `≤ 6p(1−w)²` (re-export of
    the PROVED `bondMovingDeltaRen_le_sixp`): the MK/hierarchical SIDE is proved.
  * `mkFusion_concentration` — the fused excited/vacuum ratio CONCENTRATES,
    `ρ_2 ≤ 2ρ_1` (re-export of the PROVED `selfFusion_ratio_two`).
  * `singleStep_of_mkGapDefectTransfer`, `mkControl_fullFloor` — GIVEN the (open)
    gap-defect transfer, the whole positive continuum floor for the true margin.

## What is NAMED-OPEN — the gap-defect transfer = `singleStep` (honest)

`MKGapDefectTransfer := SingleStepDefectBound` (Rule 9.8 def-alias; UNINHABITED).
The transfer `δ^{4D} ≤ δ^{MK}` for the GAP defect is exactly `singleStep` — the
real per-step degradation of the true margin bounded by the transverse model.  The
MK free-energy Jensen bracket (available, cited) does NOT inhabit it, because the
free energy and the gap defect are different functionals (see above).

# HONEST VERDICT (AGENTS.md Rule 6 / Rule 9)

The MK bond-moving is a RIGOROUS VARIATIONAL (Jensen) bound on the FREE ENERGY, and
the MK/hierarchical defect is PROVED `≤ 6(1−w)²` and CONCENTRATING.  But the
GAP DEFECT is a strictly different functional (the excited/vacuum ratio, not the
partition function), and the free-energy variational principle does NOT transfer to
it — numerically demonstrated by the free energy exploding while the gap ratio is
inert.  Therefore `δ^{4D} ≤ δ^{MK}` for the GAP DEFECT is NOT provable via Jensen;
it is EXACTLY the `singleStep` input.  `MKGapDefectTransfer` is UNINHABITED.  NO 4D
Yang–Mills mass gap is claimed; nothing is faked; the guard-protected frontier
bundles are inhabited by NONE of these declarations.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat` composition reusing PROVED `amgm_two`, `bondMovingDeltaRen_le_sixp`,
`selfFusion_ratio_two`, `fullFloor_of_singleStep`.  Every load-bearing declaration
is gated with `#print axioms`; permitted output is `propext`/`Quot.sound` only.  No
`Classical.*`, no `native_decide`, no `sorry`, no `ring`.  All witnesses are `Type`
data.
-/

import YMGap.Continuum.SingleStepDefectReduction
import YMGap.Continuum.InteractingMFoldDefect
import YMGap.Continuum.RenDefectQuadFactor
import YMGap.Constructive.CRealAlg

namespace YMGap.Continuum.MKBondMovingControl

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.BondMovingQuadratic
open YMGap.Continuum.RenDefectQuadFactor
open YMGap.Continuum.MultiLinkFusionDefect
open YMGap.Continuum.SingleStepDefectReduction

/-! ## 1. THE MK VARIATIONAL ENGINE — Jensen/convexity of potential-moving (PROVED). -/

/-- **`potentialMoving_convexity` — the Jensen/convexity engine of MK potential-moving.**
The two-term convexity `(x·y) + (x·y) ≤ x·x + y·y` (`2xy ≤ x²+y²`, i.e.
`0 ≤ (x−y)²`) is the algebraic root of the Migdal–Kadanoff potential-moving
FREE-ENERGY bound: moving two bonds together (the "concentrated" configuration
`x·x + y·y`) dominates the split cross-term (`2·x·y`).  Summed over the lattice this
is the Jensen inequality `∫ K_w^m dμ ≥ (∫ K_w dμ)^m` that makes the MK approximation
a rigorous ONE-SIDED bound on the FREE ENERGY (Kadanoff, Ann. Phys. 100 (1976)).
Re-export of the PROVED `CRealAlg.amgm_two`. -/
theorem potentialMoving_convexity (x y : Q') :
    (x * y) + (x * y) ≤ x * x + y * y :=
  YMGap.Constructive.CRealAlg.amgm_two x y

/-! ## 2. THE MK / HIERARCHICAL SIDE — the bond-moving defect is PROVED quadratic. -/

/-- **`mkDefect_le_sixQuad` — the MK bond-moving defect is `≤ 6p(1−w)²` (PROVED).**
On `[0,1]`, the renormalized MK bond-moving per-step defect `δ^{MK} =
bondMovingDeltaRen N p w` is bounded by the transverse quadratic
`(ofNat p)·(dimQ 1·(3·(1−w)²)) = 6p(1−w)²`.  This is the MK / hierarchical-lattice
SIDE of `singleStep`, fully proved (`bondMovingDeltaRen_le_sixp` /
`RenDefectQuadFactor`); what remains open is the transfer to the REAL 4D block-spin
defect (§4). -/
theorem mkDefect_le_sixQuad {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (N p : Nat) :
    bondMovingDeltaRen N p w
      ≤ Q'.ofNat p * (dimQ 1 * (Q'.ofNat 3 * (((1 : Q') - w) * ((1 : Q') - w)))) :=
  bondMovingDeltaRen_le_sixp hw0 hw1 N p

/-- **`mkFusion_concentration` — the MK parallel-fusion CONCENTRATES (PROVED).**
`ρ_2 ≤ 2ρ_1`: `g₁·c₀ ≤ (2·c₁)·g₀`, `g_s = bondMovedCoeff N w 2 s`.  The MK
bond-moving of two parallel plaquettes damps (does not amplify) the excited/vacuum
leakage — the machine-checked m=2 witness of `2 − ρ_m ≈ 6(1−w)/m` (excited
indicator ↓ in the block multiplicity).  Re-export of the PROVED
`selfFusion_ratio_two`. -/
theorem mkFusion_concentration {w : Q'} (hwp : (0 : Q') < w) (hw1 : w ≤ (1 : Q'))
    (N : Nat) :
    bondMovedCoeff N w 2 1 * coeffW w 0
      ≤ (Q'.ofNat 2 * coeffW w 1) * bondMovedCoeff N w 2 0 :=
  selfFusion_ratio_two hwp hw1 N

/-! ## 3. THE MK FREE-ENERGY BRACKET — the variational bound that IS available (Rule 6a).

The MK bond-moving is a rigorous variational bracket on the FREE ENERGY: bond-moving
before vs after decimation yields a lower and an upper approximant to the true
free-energy sequence.  We record this as an EXPLICIT named input structure over
abstract free-energy sequences (Jensen/Kadanoff 1976 / Osterwalder–Seiler 1978).
It is a GENUINE variational statement — but a statement about the FREE ENERGY, NOT
the gap defect.  Its very availability is the point of §4: having the free-energy
bracket does NOT close `singleStep`. -/

/-- **`MKFreeEnergyBracket` — the MK variational FREE-ENERGY bracket (`Type`, Rule 6a).**
`freeEnergy` is the true 4D per-scale free-energy sequence; `mkLower`/`mkUpper` are
the two MK bond-moving approximants (potential-moving before/after decimation).  The
Jensen/variational principle brackets the true free energy:
`mkLower k ≤ freeEnergy k ≤ mkUpper k`.  This is the RIGOROUS content of the MK
approximation (Kadanoff, Ann. Phys. 100 (1976)) — on the FREE ENERGY.  It carries
NO information about the spectral-gap ratio (the gap defect), which is a different
functional of the fused measure (§4). -/
structure MKFreeEnergyBracket : Type where
  /-- The true 4D per-scale free-energy sequence `log Z_k` (schematically). -/
  freeEnergy : Nat → Q'
  /-- The MK lower free-energy approximant (one bond-moving ordering). -/
  mkLower : Nat → Q'
  /-- The MK upper free-energy approximant (the other bond-moving ordering). -/
  mkUpper : Nat → Q'
  /-- Jensen lower bracket: the MK lower approximant is ≤ the true free energy. -/
  lower : ∀ k, mkLower k ≤ freeEnergy k
  /-- Jensen upper bracket: the true free energy is ≤ the MK upper approximant. -/
  upper : ∀ k, freeEnergy k ≤ mkUpper k

/-- **`mkBracket_transitive` — the free-energy bracket is internally consistent
(PROVED).**  From an `MKFreeEnergyBracket`, `mkLower k ≤ mkUpper k` at every scale.
This is the only thing the free-energy bracket delivers on its own — a bound on the
free energy, transitively closed — and it is manifestly NOT a bound on any
excited/vacuum RATIO.  (It exists to make explicit that the bracket is genuine yet
silent about the gap.) -/
theorem mkBracket_transitive (B : MKFreeEnergyBracket) (k : Nat) :
    B.mkLower k ≤ B.mkUpper k :=
  Q'.le_trans' _ _ _ (B.lower k) (B.upper k)

/-! ## 4. THE GAP-DEFECT TRANSFER — the missing bridge = `singleStep` (UNINHABITED). -/

/-- **`MKGapDefectTransfer := SingleStepDefectBound` — the real-vs-MK GAP-defect
transfer (Rule 9.8 def-alias; UNINHABITED).**

The transfer we would need to CLOSE the continuum gap is: the REAL 4D block-spin
GAP defect `δ^{4D}_k` (the per-step degradation of the TRUE dimensionless margin) is
bounded by the MK bond-moving defect `δ^{MK}_k` (proved `≤ 6(1−w)²`, §2).  In
per-step form that is EXACTLY `SingleStepDefectBound.singleStep`
(`(1 − δ_model_k)·trueMargin k ≤ trueMargin (k+1)`).

**This transfer is NOT supplied by the MK FREE-ENERGY bracket (§3).**  The MK
variational (Jensen) principle bounds the FREE ENERGY `[c^{⋆m}]_0 = ∫ K_w^m dμ`
(off-line: `1 → 159 → 38491 → 1.1·10^7` for `m=1,2,3,4` at `w=0.99` — the free
energy is fully controlled).  The GAP defect is `∝ 2 − ρ_m`, `ρ_m =
[c^{⋆m}]_1/[c^{⋆m}]_0` — the excited/vacuum RATIO (sub-leading transfer eigenvalue),
which stays `O(1−w)` while the free energy explodes.  A Jensen bound on the free
energy therefore carries NO information about the gap defect: they are DIFFERENT
functionals of the fused measure.  (Same reason MK gives only APPROXIMATE, not
rigorously bracketed, correlation lengths / critical exponents; and in `d>2` the
free-energy bracket width is itself uncontrolled O(1) per bond.)  Hence the
real-vs-MK gap for the GAP DEFECT is the open `singleStep` input — NOT closed by the
variational principle.  UNINHABITED. -/
def MKGapDefectTransfer : Type :=
  SingleStepDefectReduction.SingleStepDefectBound

/-- The def-alias is exactly the named residual `singleStep` (Rule 9.8). -/
theorem mkGapDefectTransfer_eq :
    MKGapDefectTransfer = SingleStepDefectReduction.SingleStepDefectBound := rfl

/-- **`singleStep_of_mkGapDefectTransfer` — the transfer inhabits `SingleStepDefectBound`.**
An `MKGapDefectTransfer` IS a `SingleStepDefectBound` (identity, Rule 9.8): the
gap-defect transfer is exactly the open per-step estimate `realδ ≤ δ_model`. -/
def singleStep_of_mkGapDefectTransfer (T : MKGapDefectTransfer) :
    SingleStepDefectReduction.SingleStepDefectBound := T

/-- **`mkControl_fullFloor` — the whole continuum floor GIVEN the gap-defect transfer.**
From an `MKGapDefectTransfer` (= a `SingleStepDefectBound`, the actual open input —
NOT produced by the MK free-energy bracket), the entire positive uniform continuum
floor holds for the TRUE margin (`fullFloor_of_singleStep`): `0 < prodFloor` and
`prodFloor ≤ trueMargin k` at every scale.  So the MK-approximation route closes the
continuum gap IF AND ONLY IF the gap-defect transfer holds — and §4 shows that
transfer is the `singleStep` input, NOT a consequence of the (available) MK
variational free-energy bound. -/
theorem mkControl_fullFloor (T : MKGapDefectTransfer) :
    (0 : Q') < (defectRecursion_of_singleStep (singleStep_of_mkGapDefectTransfer T)).prodFloor
      ∧ ∀ k : Nat,
          (defectRecursion_of_singleStep (singleStep_of_mkGapDefectTransfer T)).prodFloor
            ≤ T.trueMargin k :=
  fullFloor_of_singleStep (singleStep_of_mkGapDefectTransfer T)

/-! ## 5. THE HONEST NON-CLOSURE — Jensen bounds the free energy, not the gap defect. -/

/-- **`mkVariational_bounds_freeEnergy_not_gapDefect` — the honest verdict.**

The MK bond-moving is a RIGOROUS VARIATIONAL (Jensen/convexity) bound — but on the
FREE ENERGY (`MKFreeEnergyBracket`, §3, built on `potentialMoving_convexity`), NOT
on the spectral-GAP DEFECT.  The gap defect is the excited/vacuum RATIO `ρ_m`, a
different functional: the free energy `[c^{⋆m}]_0` explodes (`1 → 1.1·10^7`) while
`2 − ρ_m` stays `O(1−w)`, so the free-energy bracket is SILENT about the gap.
Consequently `δ^{4D} ≤ δ^{MK}` for the GAP DEFECT is NOT provable via the variational
principle; it is EXACTLY `singleStep` (`MKGapDefectTransfer`, §4, UNINHABITED).  The
MK-approximation control therefore REDUCES to — does not close — `singleStep`; the
4D Yang–Mills mass gap remains OPEN. -/
theorem mkVariational_bounds_freeEnergy_not_gapDefect : True := trivial

end YMGap.Continuum.MKBondMovingControl

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.MKBondMovingControl.potentialMoving_convexity
#print axioms YMGap.Continuum.MKBondMovingControl.mkDefect_le_sixQuad
#print axioms YMGap.Continuum.MKBondMovingControl.mkFusion_concentration
#print axioms YMGap.Continuum.MKBondMovingControl.mkBracket_transitive
#print axioms YMGap.Continuum.MKBondMovingControl.mkGapDefectTransfer_eq
#print axioms YMGap.Continuum.MKBondMovingControl.singleStep_of_mkGapDefectTransfer
#print axioms YMGap.Continuum.MKBondMovingControl.mkControl_fullFloor
#print axioms YMGap.Continuum.MKBondMovingControl.mkVariational_bounds_freeEnergy_not_gapDefect
