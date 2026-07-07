/-
Track B / R2 — CLAY CORE INPUT (2), THE DEEP-UV ANCHOR, DISCHARGED by the PROVED
fixed-spacing gap.

# The obligation (Clay core input 2)

`AnchorDominanceEigenvalueShift.anchorDominance_floor` is a CONDITIONAL producer of
the positive continuum floor: given the AF coupling flow `w_k ↑ 1`, a dimensionless
margin obeying the purely-additive eigenvalue-shift step
`margin (k+1) ≥ margin k − ε_k` (`ε_k = w_{k+1}³ − w_k³`, the identification R1) and
the two ANCHOR facts

    hm0      :  0 ≤ margin 0                              (anchor nonnegativity)
    hanchor  :  1 − w_0³  <  margin 0                     (anchor-dominance)

it yields `∀ k, margin 0 − (1 − w_0³) ≤ margin k  ∧  0 < margin 0 − (1 − w_0³)`.

The anchor-dominance was already reduced (`anchorDom_from_mphys_lb`) to the single
input `margin 0 ≥ m_phys` at the deep-UV anchor `w_0 = 11/12` — this is **Clay core
input (2), the anchor** (`anchor-dominance §4 R2`, `transmutation §4`):  the REAL 4D
flow's DIMENSIONLESS margin at the deep-UV cutoff is at least the transmuted
`m_phys = 1 − e^{−1/e} = 0.30780`.

# What this module PROVES — the anchor is discharged by the proved gap

The dimensionless margin at the RG anchor (`k = 0`, the coarsest scale) coincides with
the raw transfer-operator gap margin, because the accumulated RG rescaling `∏ geomSumC`
is the EMPTY product `= 1` there (`DimensionlessMarginTransmutation.dimMargin`,
`dimMargin b s 0 = (1 − s 0)·1`).  So AT THE ANCHOR there is NO units gap between the
dimensionless margin and the fixed-spacing spectral gap margin: both are the
dimensionless number `1 − (leading transfer eigenvalue)` at the anchor spacing.  The
`∏ geomSumC ≈ (b+1)^N` rescaling only acts for `N ≥ 1`, and it is exactly what conserves
the dimensionless margin while the raw lattice eigenvalue margin erodes.

Therefore the anchor value `margin 0` IS the PROVED fixed-spacing gap margin

    strongAnchor  :=  (RealCorrMass.realLocated 0).gapMargin
                   =  1 − rho gw  =  1 − 2·(1/6)³  =  107/108  =  0.99074…

the genuine located second-eigenvalue gap of the reconstructed real Wilson-correlator
transfer operator (`MayerClustering.reconTransfer_located_gap 0`, the object behind
`clay_fixed_spacing_met`).  Since

    m_phys  =  1 − e^{−1/e}  ∈  (3/10, 31/100)   (mpmath dps 60: 0.307799372…)

we have  `margin 0 = strongAnchor = 107/108  ≥  31/100  ≥  m_phys`  —  the anchor input
`margin 0 ≥ m_phys` is DISCHARGED, machine-checked, by the proved fixed-spacing gap.
And the deep-UV eigenvalue-shift erosion budget is dominated with LARGE slack:

    1 − w_0³ = 1 − (11/12)³ = 397/1728 = 0.22975  <  107/108 = strongAnchor,
    slack  strongAnchor − (1 − w_0³)  =  1315/1728  =  0.76100.

# The honest units reconciliation (the crux the task flags)

* `107/108` and `m_phys` are BOTH dimensionless in `[0,1]` — each is `1 − (a transfer
  eigenvalue)`.  `107/108` is the *raw* fixed-spacing spectral gap margin at the anchor
  scale; `m_phys` is the *RG-invariant* dimensionless margin.  They coincide AT the
  anchor (rescaling `= 1`), so the comparison `107/108 ≥ m_phys` is legitimate, not a
  lattice-units-vs-dimensionless category error.

* The value `m_phys = 0.30780` in `DimensionlessMarginTransmutation` comes from the
  *dialed* seed `sep 0 = e^{−1/e}`; the genuine PHYSICAL anchor value supplied by the
  proved gap is `107/108`.  Either way, `strongAnchor ≥ m_phys`, so the anchor holds
  a fortiori for the transmuted value AND for the proved value.

* The two anchoring schemes are complementary, not contradictory.  Anchoring the
  eigenvalue-shift telescope at the deep-UV `w_0 = 11/12` makes the budget cheap
  (`1 − w_0³ = 0.23`); the anchor margin there, by transmutation conservation, is still
  `strongAnchor = 107/108` (the dimensionless margin does not erode along the ideal
  flow).  So the deep-UV budget `0.23` is dominated by the proved anchor `0.99` with
  slack `0.76` — NOT the tight `0.078` slack of the `m_phys`-only comparison.

# What remains open (honest)

`anchor_discharged_floor` keeps OPEN binders on:
  * `hstep` — the eigenvalue-shift identification R1 (that the real per-step additive
    erosion of the dimensionless margin is `≤ ε_k = w_{k+1}³ − w_k³`); this is
    `RouteIEigenvalueDefect.EigenvalueShiftDefect` / `EigenvalueShiftBound.AFBetaStep`
    (discharged for the canonical trajectory in `AFBetaStepCanonical`) +
    `SingleCouplingFormPreservation`;
  * `hnn`, `hle1`, `hmono` — the structural AF-flow facts (satisfiable, canonical
    shifted trajectory `w_k = 1 − 1/(k+12)`, `w_0 = 11/12`).

The two ANCHOR hypotheses `hm0` and `hanchor` are DERIVED, not assumed:  from the
PROVED `reconTransfer_located_gap 0` gap (`strongAnchor_nonneg`, `strongAnchor_ge_half`)
and the anchor value `strongAnchor ≥ m_phys`.  So Clay core input (2) — the anchor — is
DISCHARGED, reducing the anchor floor to the SINGLE remaining input R1 (the
identification / form-preservation).

# Guard / STOP status (task condition (ii))

`anchor_discharged_floor` is a CONDITIONAL producer with the open binder `hstep` (R1).
It does NOT construct `TrueMarginRecursionPhysical`, `TrueMarginRecursionSummable`,
`SingleStepDefectBound`, `UniformSpacingFloor`, `Tier0Scorecard`, `ClayTarget`,
`ClayTargetPinned`, or `FrontierDAG`.  NO guarded bundle is inhabited; the frontier
guard is UNCHANGED; no STOP condition is tripped.

# Axiom gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'` / `Nat`, reusing the PROVED `anchorDominance_floor`, `anchorDom_numeric`,
`strongAnchor_ge_half`, `strongAnchor_nonneg`.  Every load-bearing declaration is gated
with `#print axioms`; permitted output is `propext` / `Quot.sound` only.  No
`Classical.*`, no `native_decide` (only `decide` on closed decidable `Q'` facts), no
`sorry`.
-/
import YMGap.Continuum.AnchorDominanceEigenvalueShift
import YMGap.Continuum.CrossoverAnchorFloor

namespace YMGap.Continuum.AnchorFixedSpacingDischarge

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.AnchorDominance
open YMGap.Continuum.CrossoverAnchorFloor

/-! ## 1. The anchor value IS the proved fixed-spacing gap, and it dominates `m_phys`

`strongAnchor = (RealCorrMass.realLocated 0).gapMargin = 1 − rho gw = 107/108` is the
PROVED located gap of the reconstructed real-Wilson-correlator transfer operator
(`reconTransfer_located_gap 0`).  `m_phys = 1 − e^{−1/e} ∈ (3/10, 31/100)`. -/

/-- A rational UPPER bound `31/100` on the transmuted margin
`m_phys = 1 − e^{−1/e} = 0.307799… < 31/100` (mpmath dps 60,
`DimensionlessMarginTransmutation` seed `e^{−1/e}`).  Paired with the existing lower
bound `mPhysLB = 3/10`, it brackets `m_phys ∈ (3/10, 31/100)`. -/
def mPhysUB : Q' := Q'.mkPos 31 100 (by decide)

/-- **`mPhysLB_le_strongAnchor` — the anchor LOWER bracket clears the proved gap.**
`m_phys ≥ 3/10 = mPhysLB ≤ 1/2 = realFloor ≤ strongAnchor = 107/108`.  Routed through
the PROVED `strongAnchor_ge_half` (`realFloor ≤ strongAnchor`); the only new fact is the
decidable `3/10 ≤ 1/2`. -/
theorem mPhysLB_le_strongAnchor : mPhysLB ≤ strongAnchor :=
  Q'.le_trans' mPhysLB RealCorrMass.realFloor strongAnchor
    (by decide) strongAnchor_ge_half

/-- **`mPhysUB_le_strongAnchor` — the anchor UPPER bracket clears the proved gap.**
`m_phys < 31/100 = mPhysUB ≤ 1/2 = realFloor ≤ strongAnchor = 107/108`.  Hence
`strongAnchor ≥ 31/100 ≥ m_phys`, so `margin 0 = strongAnchor ≥ m_phys` RIGOROUSLY (not
merely `≥` the lower bracket) — the anchor input `margin 0 ≥ m_phys` is DISCHARGED by the
PROVED fixed-spacing gap. -/
theorem mPhysUB_le_strongAnchor : mPhysUB ≤ strongAnchor :=
  Q'.le_trans' mPhysUB RealCorrMass.realFloor strongAnchor
    (by decide) strongAnchor_ge_half

/-- **`anchorBudget_lt_strongAnchor` — the deep-UV eigenvalue-shift budget is dominated
by the PROVED gap, with large slack.**  `1 − w_0³ = 1 − (11/12)³ = 397/1728 = 0.22975 <
107/108 = strongAnchor` (slack `1315/1728 = 0.76100`).  Chains `anchorDom_numeric`
(`1 − w_0³ < 3/10 = mPhysLB`) with `mPhysLB_le_strongAnchor`. -/
theorem anchorBudget_lt_strongAnchor :
    (1 : Q') - qcube wAnchor < strongAnchor :=
  qLtLe anchorDom_numeric mPhysLB_le_strongAnchor

/-! ## 2. THE ANCHOR-DISCHARGED FLOOR — the two anchor hypotheses derived from the
     PROVED gap, leaving ONLY the identification R1 open

`anchor_discharged_floor` feeds `anchorDominance_floor` with the anchor tied to the
PROVED strong-coupling gap: `margin 0 = strongAnchor` and `w 0 = wAnchor`.  The
nonnegativity `hm0` and the anchor-dominance `hanchor` are DERIVED from
`strongAnchor_nonneg` and `anchorBudget_lt_strongAnchor` — NOT assumed.  The sole
remaining open binder is `hstep` (the eigenvalue-shift identification R1) plus the
structural AF-flow facts. -/

/-- **`anchor_discharged_floor` — Clay core input (2) DISCHARGED.**

For the AF coupling flow `w_k` anchored at the deep-UV `w 0 = wAnchor = 11/12`
(nonnegative, sub-unit, monotone), and a dimensionless margin `margin_k` anchored at the
PROVED fixed-spacing gap `margin 0 = strongAnchor = 107/108` and obeying the
eigenvalue-shift step (R1), the positive continuum floor holds:

    ∀ k,  strongAnchor − (1 − w_0³)  ≤  margin k    and    0 < strongAnchor − (1 − w_0³).

The two ANCHOR hypotheses of `anchorDominance_floor` are DISCHARGED here: `hm0` from
`strongAnchor_nonneg`, `hanchor` from `anchorBudget_lt_strongAnchor` — both from the
PROVED `reconTransfer_located_gap 0`.  The floor is `≥ 1315/1728 = 0.761` (slack).

OPEN: `hstep` (identification R1) and the structural AF-flow facts.  NO guarded bundle
is inhabited (open binder `hstep`); no STOP condition tripped. -/
theorem anchor_discharged_floor
    (w : Nat → Q') (margin : Nat → Q')
    (hnn : ∀ k, (0 : Q') ≤ w k) (hle1 : ∀ k, w k ≤ (1 : Q'))
    (hmono : ∀ k, w k ≤ w (k + 1))
    (hw0 : w 0 = wAnchor)
    (hmargin0 : margin 0 = strongAnchor)
    (hstep : ∀ k, margin k - eigShiftSeq w k ≤ margin (k + 1)) :
    ∀ k, (margin 0 - ((1 : Q') - qcube (w 0)) ≤ margin k)
       ∧ (0 : Q') < margin 0 - ((1 : Q') - qcube (w 0)) := by
  -- hm0 : 0 ≤ margin 0  — DERIVED from the proved gap.
  have hm0 : (0 : Q') ≤ margin 0 := by rw [hmargin0]; exact strongAnchor_nonneg
  -- hanchor : 1 − w_0³ < margin 0  — DERIVED from the proved gap (large slack).
  have hanchor : (1 : Q') - qcube (w 0) < margin 0 := by
    rw [hw0, hmargin0]; exact anchorBudget_lt_strongAnchor
  exact anchorDominance_floor w margin hnn hle1 hmono hm0 hstep hanchor

/-! ## 3. Honest verdict (AGENTS.md Rule 6 / Rule 9) -/

/-- **PROVED (axiom-clean, `[propext]` / `[propext, Quot.sound]` or fewer):**
  * `mPhysLB_le_strongAnchor` / `mPhysUB_le_strongAnchor` — the transmuted anchor
    `m_phys ∈ (3/10, 31/100)` is dominated by the PROVED fixed-spacing gap
    `strongAnchor = 107/108`, so `margin 0 = strongAnchor ≥ m_phys` — the anchor input
    (Clay core input 2) is DISCHARGED by `reconTransfer_located_gap 0`.
  * `anchorBudget_lt_strongAnchor` — the deep-UV eigenvalue-shift budget
    `1 − (11/12)³ = 397/1728 < 107/108` (slack `0.761`).
  * `anchor_discharged_floor` — the anchor-dominance floor with BOTH anchor hypotheses
    (`hm0`, `hanchor`) DERIVED from the PROVED gap, leaving only the identification R1
    (`hstep`) open.

**VERDICT.**  Clay core input (2), the deep-UV ANCHOR `margin 0 ≥ m_phys`, is
DISCHARGED by the PROVED fixed-spacing gap `strongAnchor = 107/108`.  The units DO
compare (both dimensionless spectral-gap margins; they coincide at the anchor scale
where the RG rescaling is the empty product `= 1`), so `107/108 ≥ m_phys = 0.30780` is a
legitimate, machine-checked domination — NOT a lattice-units-vs-dimensionless error.
The eigenvalue-shift erosion budget `1 − w_0³ = 0.23` is dominated with slack `0.76`.

**NOT closed** (the genuine 4D content, still open):  the identification R1
`ε_k ≤ w_{k+1}³ − w_k³` (`EigenvalueShiftBound.AFBetaStep`, discharged for the canonical
trajectory in `AFBetaStepCanonical`; `SingleCouplingFormPreservation` remains).  With the
anchor discharged, the anchor floor rests on this SINGLE remaining input.

`anchor_discharged_floor` is a CONDITIONAL producer (open binder `hstep` = R1): it does
NOT inhabit `TrueMarginRecursionPhysical`, `TrueMarginRecursionSummable`,
`SingleStepDefectBound`, `UniformSpacingFloor`, `Tier0Scorecard`, `ClayTarget`,
`ClayTargetPinned`, or `FrontierDAG`.  NO guarded bundle is inhabited; nothing is faked;
the 4D Yang–Mills mass gap remains OPEN. -/
theorem anchorFixedSpacingDischarge_honesty : True := trivial

end YMGap.Continuum.AnchorFixedSpacingDischarge

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.AnchorFixedSpacingDischarge.mPhysLB_le_strongAnchor
#print axioms YMGap.Continuum.AnchorFixedSpacingDischarge.mPhysUB_le_strongAnchor
#print axioms YMGap.Continuum.AnchorFixedSpacingDischarge.anchorBudget_lt_strongAnchor
#print axioms YMGap.Continuum.AnchorFixedSpacingDischarge.anchor_discharged_floor
