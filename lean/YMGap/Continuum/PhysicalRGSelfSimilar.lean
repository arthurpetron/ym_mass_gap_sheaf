/-
Track B / R2 — **The bridge: proven AF running + proven decimation power-law
⟹ separator self-similarity, reduced to ONE sharp physical input.**

# What this module assembles (read first)

The open dynamical-RG obligation of Route B is the physical-separator self-similar
law `sep_k ≃ (sep_{k+1})^(b+1)` (`PhysicalRGInput.selfSimilar`, deliberately
UNINHABITED for ℝ⁴).  This module shows that law is NOT an independent axiom: it is
the proven decimation power-law (Leg A) composed with a single tower descent (★),
and it reduces EXACTLY to the one sharp physical statement that the 4D block-spin
RG map preserves the heat-kernel form (bond-moving residual `δ = 0`).

## The three legs (all previously PROVED, re-exposed here)

  * **Leg A — decimation power-law (EXACT).**  Collapsing `b` heat-kernel links in
    series raises the separator to the `b`-th power: at the `Q'` level
    `heatKernelSep (mkDecimate b w) ≃ (heatKernelSep w)^b`; at the `CReal`
    exponent level the twin `(e^{−s})^n ≈ e^{−(n·s)}` (`expNegCD_powerLaw`).
  * **Leg B — AF block-factor calibration.**  The block factor `b+1` equals the
    proven spacing rescale `a_N / a_{N+1} ≥ b+1` (`afBlocked_ratio_ge`), so the
    self-similar exponent is the physically-correct one.
  * **★ — the tower descent (the SINGLE open input).**  One physical block-spin
    decimation step coarsens the heat-kernel exponent by exactly the block factor:
    `scaleN (b+1) (w_{k+1}) ≃ w_k` pointwise, i.e. `w_k = (b+1)·w_{k+1}` — the
    bond-moving residual `δ = 0`.

## The bridge, assembled (GENUINE, in small steps)

For any exponent tower carrying (★) (a `SelfSimilarTower b`) the separators satisfy
the self-similar CReal law, reconstructed here from the two named legs:

    sep_k = e^{−w_k}
          = e^{−(b+1)·w_{k+1}}      by ★               (`legStar_descent`)
          = (e^{−w_{k+1}})^{b+1}    by Leg A           (`legA_powerLaw`)
          = (sep_{k+1})^{b+1}       (`descent_selfSimilarC_step`)

`descent_selfSimilarC` packages this as `selfSimilarC b (sep T)`, and
`physicalRGInput_of_tower` uses it to REDUCE the abstract `PhysicalRGInput` (whose
`selfSimilar` field is the open obligation) to a single tower descent plus the
automatic `[0,1]` separator bounds and a UV-gap floor.  The payoff
`descentInput_continuum_gap` then yields the spacing-uniform continuum-gap floor.

## Honest scope

The reduction and both legs are fully green and axiom-clean.  The SINGLE remaining
obligation is the tower descent (★) for the genuine physical Yang–Mills exponents —
equivalently `δ = 0` in `HeatKernelRGStep.BondMovingResidual`.  It is EXACT on the
hierarchical / diamond lattice (bond-moving IS the decimation there), and this
module ships a GREEN inhabitant of the descent interface on the irrational
`e^{−1}`-seeded hierarchical model (`hierarchicalDescentInput`), demonstrating the
bridge is non-vacuous.  The ℝ⁴ residual is NOT inhabited — MK is approximate there.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure composition over the `SelfSimilarFlow` / `BlockSpinModel` / `HeatKernelRGStep`
/ `AFExpLift` backbones; every carrier is `Type`-level data.  Each load-bearing
declaration is gated with `#print axioms` (permitted: `propext` / `Quot.sound`).
No `Classical.*`, no `native_decide`, no `sorry`, no custom `axiom`.
-/

import YMGap.Continuum.BlockSpinModel
import YMGap.Continuum.HeatKernelRGStep
import YMGap.Continuum.AFExpLift
import YMGap.Constructive.SelfSimilarFlow

namespace YMGap.Continuum.PhysicalRGSelfSimilar

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.CodynamicCRealFlow
open YMGap.Continuum.CodynamicPhysFloor
open YMGap.Continuum.RateMatchFloor
open YMGap.Continuum.HeatKernelRGStep

/-! ## 1. Leg A — the decimation power-law (re-exposed) -/

/-- **Leg A at the `Q'` level (EXACT).**  Collapsing `b` heat-kernel links in
series raises the gap separator to the `b`-th power:
`heatKernelSep (mkDecimate b w) ≃ (heatKernelSep w)^b`.  The separator commutes
with the heat semigroup — the exact half of one Migdal–Kadanoff block step. -/
theorem legA_decimation_sep (b : Nat) (w : Q') :
    (HeatKernelGap.heatKernelSep (mkDecimate b w)).eqv
      (RGTransport.qpow (HeatKernelGap.heatKernelSep w) b) :=
  mkDecimate_sep b w

/-- **Leg A at the `CReal` exponent level.**  For a `SelfSimilarTower`, the
`(b+1)`-th CReal power of the finer separator equals `e^{−(b+1)·w_{k+1}}` — the
constructive twin of the decimation power-law (`expNegCD_powerLaw`, specialised to
the tower's `(b+1)`-fold exponent sum). -/
theorem legA_powerLaw {b : Nat} (T : SelfSimilarTower b) (k : Nat) :
    CReal.Equiv (cpow (sep T (k + 1)) (b + 1))
      (expNegCD (scaleN (b + 1) (T.w (k + 1)))
        (scaleData (T.w (k + 1)) (T.dw (k + 1)) (b + 1) (T.bnd k))) :=
  expNegCD_powerLaw (T.w (k + 1)) (T.dw (k + 1)) (b + 1) (T.bnd k)

/-! ## 2. Leg B — the AF block-factor calibration (re-exposed) -/

/-- **Leg B (AF spacing calibration).**  The block factor `b+1` is exactly the
proven AF-blocked spacing rescale: `ofNat (b+1) ≤ a_N / a_{N+1}` at every scale for
the AF-derived block-spin schedule.  This calibrates the self-similar exponent
`b+1` to the physical `a → 0` schedule (`afBlocked_ratio_ge`). -/
theorem legB_block_ratio (C : AFTrajectoryCertificate.AFTrajectoryCertificate) (q : Q')
    (hq : (0 : Q') < q) (b N : Nat) :
    Q'.ofNat (b + 1)
      ≤ Q'.divPos ((AFExpLift.blockSpacing C q hq b).a N)
          ((AFExpLift.blockSpacing C q hq b).a (N + 1))
          ((AFExpLift.blockSpacing C q hq b).a_pos (N + 1)) :=
  AFExpLift.afBlocked_ratio_ge C q hq b N

/-! ## 3. ★ — the tower descent, and the composed self-similar law (GENUINE) -/

/-- **★ — the tower descent step.**  Under the descent `T.div`, the CReal exponent
`(b+1)·w_{k+1}` coarsens to `w_k`, so `e^{−(b+1)·w_{k+1}} ≈ e^{−w_k} = sep_k`
(`expNegCD_pointwise_congr` fed the pointwise descent `w_k = (b+1)·w_{k+1}`).  This
is the single sharp input — the bond-moving residual `δ = 0`. -/
theorem legStar_descent {b : Nat} (T : SelfSimilarTower b) (k : Nat) :
    CReal.Equiv
      (expNegCD (scaleN (b + 1) (T.w (k + 1)))
        (scaleData (T.w (k + 1)) (T.dw (k + 1)) (b + 1) (T.bnd k)))
      (sep T k) :=
  expNegCD_pointwise_congr (scaleN (b + 1) (T.w (k + 1))) (T.w k)
    (scaleData (T.w (k + 1)) (T.dw (k + 1)) (b + 1) (T.bnd k)) (T.dw k) (T.div k)

/-- **THE BRIDGE, one scale (Leg A ∘ ★).**  Reconstructed from the two named legs:
`sep_k ≈ (sep_{k+1})^(b+1)` follows by chaining Leg A (`legA_powerLaw`,
`(sep_{k+1})^(b+1) ≈ e^{−(b+1)·w_{k+1}}`) with ★ (`legStar_descent`,
`e^{−(b+1)·w_{k+1}} ≈ sep_k`) and symmetrising.  This is the self-similar law as a
COMPOSED consequence of the decimation power-law and the exponent descent — not an
independent axiom. -/
theorem descent_selfSimilarC_step {b : Nat} (T : SelfSimilarTower b) (k : Nat) :
    CReal.Equiv (sep T k) (cpow (sep T (k + 1)) (b + 1)) :=
  (CReal.Equiv.trans (legA_powerLaw T k) (legStar_descent T k)).symm

/-- **THE BRIDGE, all scales.**  For any exponent tower carrying the descent (★),
the separators satisfy the CReal self-similar flow law `selfSimilarC b (sep T)` at
every scale — the composed decimation power-law. -/
theorem descent_selfSimilarC {b : Nat} (T : SelfSimilarTower b) :
    selfSimilarC b (sep T) :=
  fun k => descent_selfSimilarC_step T k

/-! ## 4. Reducing the abstract `PhysicalRGInput` to a single tower descent

The abstract `PhysicalRGInput` carries the open `selfSimilar` field over an
ABSTRACT separator family.  We reduce it to a CONCRETE `SelfSimilarTower` (whose
sole nontrivial content is the descent ★): the `selfSimilar` field is discharged by
`descent_selfSimilarC`, and the `[0,1]` separator bounds come for free from
`e^{−w} ∈ [0,1]`.  Only the UV-gap floor is supplied as data. -/

/-- **The physical-RG input from a tower descent.**  Given a `SelfSimilarTower b`
(the physical exponents with the descent ★), the genuine block factor `b ≥ 1`, and
an explicit UV-gap floor below the physical gap at the coarsest scale, assemble a
full `PhysicalRGInput`.  The open `selfSimilar` field is discharged by the composed
bridge `descent_selfSimilarC`; the `[0,1]` bounds are the automatic separator
brackets `sep_geRat_zero` / `sep_leRat_one`. -/
def physicalRGInput_of_tower {b : Nat} (hb : 1 ≤ b) (T : SelfSimilarTower b)
    (floor0 : Q') (floor0_pos : (0 : Q') < floor0)
    (hbase0 : CReal.leEv (CReal.ofQ' floor0) (physGapC b (sep T) (geomSpacing b) 0)) :
    PhysicalRGInput where
  b := b
  hb := hb
  physSep := sep T
  selfSimilar := descent_selfSimilarC T
  sepNonneg := RateMatchFloor.sep_geRat_zero T
  sepLeOne := RateMatchFloor.sep_leRat_one T
  floor0 := floor0
  floor0_pos := floor0_pos
  hbase0 := hbase0

/-- **The continuum mass gap from a tower descent (GREEN).**  Composing the
reduction with `physicalRG_continuum_gap`: a tower descent (★) with a UV-gap floor
yields a strictly-positive spacing-uniform floor on the physical gap at EVERY scale
of the genuine `a → 0` block schedule. -/
def tower_continuum_gap {b : Nat} (hb : 1 ≤ b) (T : SelfSimilarTower b)
    (floor0 : Q') (floor0_pos : (0 : Q') < floor0)
    (hbase0 : CReal.leEv (CReal.ofQ' floor0) (physGapC b (sep T) (geomSpacing b) 0)) :
    UnifiedContinuumFloor.CRealFloor (physGapC b (sep T) (geomSpacing b)) :=
  physicalRG_continuum_gap (physicalRGInput_of_tower hb T floor0 floor0_pos hbase0)

/-- The tower-descent continuum floor is strictly positive. -/
theorem tower_continuum_floor_pos {b : Nat} (hb : 1 ≤ b) (T : SelfSimilarTower b)
    (floor0 : Q') (floor0_pos : (0 : Q') < floor0)
    (hbase0 : CReal.leEv (CReal.ofQ' floor0) (physGapC b (sep T) (geomSpacing b) 0)) :
    (0 : Q') < (tower_continuum_gap hb T floor0 floor0_pos hbase0).floor :=
  physicalRG_continuum_floor_pos (physicalRGInput_of_tower hb T floor0 floor0_pos hbase0)

/-! ## 5. The SINGLE sharp residual — the heat-kernel exponent descent (`δ = 0`)

The named, `Type`-level interface stating the one remaining obligation: a physical
heat-kernel exponent tower whose one-step block-spin decimation is EXACT
(bond-moving `δ = 0`), i.e. the descent `scaleN (b+1) (w_{k+1}) ≃ w_k`.  Inhabiting
it (plus a UV-gap floor) discharges the whole physical-RG input via §4. -/

/-- **THE SHARP RESIDUAL INTERFACE.**  A physical heat-kernel exponent descent: a
`SelfSimilarTower b` (its `div` field IS the bond-moving `δ = 0` descent
`w_k = (b+1)·w_{k+1}`), a genuine block factor `b ≥ 1`, and an explicit UV-gap
floor.  This is the sole open input of the whole bridge; it is EXACT on the
hierarchical lattice and NOT inhabited on ℝ⁴. -/
structure HeatKernelDescentInput (b : Nat) : Type where
  /-- The block factor is a genuine decimation. -/
  hb : 1 ≤ b
  /-- The physical exponent tower whose descent `div` is the bond-moving `δ = 0`. -/
  T : SelfSimilarTower b
  /-- The explicit UV-gap floor (supplied as data). -/
  floor0 : Q'
  /-- The UV-gap floor is strictly positive. -/
  floor0_pos : (0 : Q') < floor0
  /-- The UV-gap floor lies below the physical gap at the coarsest scale. -/
  hbase0 : CReal.leEv (CReal.ofQ' floor0) (physGapC b (sep T) (geomSpacing b) 0)

/-- The residual discharges the abstract `PhysicalRGInput` (its open `selfSimilar`
field via the composed bridge). -/
def HeatKernelDescentInput.toPhysicalRGInput {b : Nat} (R : HeatKernelDescentInput b) :
    PhysicalRGInput :=
  physicalRGInput_of_tower R.hb R.T R.floor0 R.floor0_pos R.hbase0

/-- **The bridge payoff.**  From the sharp descent residual, the physical continuum
mass gap: a strictly-positive spacing-uniform floor on the physical gap at every
scale of the genuine `a → 0` block schedule. -/
def HeatKernelDescentInput.continuum_gap {b : Nat} (R : HeatKernelDescentInput b) :
    UnifiedContinuumFloor.CRealFloor (physGapC b (sep R.T) (geomSpacing b)) :=
  physicalRG_continuum_gap R.toPhysicalRGInput

/-- The residual's continuum floor is strictly positive. -/
theorem HeatKernelDescentInput.continuum_floor_pos {b : Nat}
    (R : HeatKernelDescentInput b) : (0 : Q') < R.continuum_gap.floor :=
  physicalRG_continuum_floor_pos R.toPhysicalRGInput

/-! ## 6. Non-vacuity: the hierarchical (`δ = 0`) inhabitant

The descent residual is inhabited on the hierarchical / diamond lattice, where
bond-moving IS the decimation (`δ = 0`).  We ship a GREEN inhabitant on the
irrational `e^{−1}`-seeded tower `concreteTowerE 1`, reusing the discharged UV-gap
floor of the concrete `e^{−1}` block-spin model.  This makes the whole bridge
non-vacuous; the ℝ⁴ residual (`δ ≠ 0`, uncontrolled) is NOT inhabited. -/

/-- **The hierarchical bond-moving residual is EXACT (`δ = 0`), re-exposed.**  On
the hierarchical lattice the `Q'`-level full-step weight equals the exact decimated
weight, so the sharp input `δ = 0` holds by construction — the exactly-solvable
case where the block-spin RG map preserves the heat-kernel form. -/
theorem hierarchical_bondMoving_delta_zero (b : Nat) (a w : Q') (ha : (0 : Q') ≤ a) :
    (hierarchicalBondMovingResidual b a w ha).delta = 0 :=
  hierarchical_residual_zero b a w ha

/-- **THE GREEN HIERARCHICAL DESCENT INHABITANT.**  The irrational `e^{−1}`-seeded
tower `concreteTowerE 1` (exponents `e^{−1}/2^k`, separators `e^{−(e^{−1})/2^k}`)
inhabits the sharp descent residual with the discharged UV-gap floor of the
concrete `e^{−1}` model — a genuine `δ = 0` instance of the single physical input. -/
def hierarchicalDescentInput : HeatKernelDescentInput 1 where
  hb := by decide
  T := concreteTowerE 1
  floor0 := concreteEFloor
  floor0_pos := concreteEFloor_pos
  hbase0 := concreteE_hbase

/-- **THE HIERARCHICAL BRIDGE IS GREEN.**  On the `δ = 0` hierarchical model the
sharp descent residual yields a strictly-positive continuum mass-gap floor — the
bridge closes unconditionally where bond-moving is the decimation. -/
theorem hierarchical_continuum_floor_pos :
    (0 : Q') < hierarchicalDescentInput.continuum_gap.floor :=
  hierarchicalDescentInput.continuum_floor_pos

end YMGap.Continuum.PhysicalRGSelfSimilar

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.PhysicalRGSelfSimilar.legA_decimation_sep
#print axioms YMGap.Continuum.PhysicalRGSelfSimilar.legA_powerLaw
#print axioms YMGap.Continuum.PhysicalRGSelfSimilar.legB_block_ratio
#print axioms YMGap.Continuum.PhysicalRGSelfSimilar.legStar_descent
#print axioms YMGap.Continuum.PhysicalRGSelfSimilar.descent_selfSimilarC_step
#print axioms YMGap.Continuum.PhysicalRGSelfSimilar.descent_selfSimilarC
#print axioms YMGap.Continuum.PhysicalRGSelfSimilar.physicalRGInput_of_tower
#print axioms YMGap.Continuum.PhysicalRGSelfSimilar.tower_continuum_gap
#print axioms YMGap.Continuum.PhysicalRGSelfSimilar.tower_continuum_floor_pos
#print axioms YMGap.Continuum.PhysicalRGSelfSimilar.HeatKernelDescentInput.toPhysicalRGInput
#print axioms YMGap.Continuum.PhysicalRGSelfSimilar.HeatKernelDescentInput.continuum_gap
#print axioms YMGap.Continuum.PhysicalRGSelfSimilar.HeatKernelDescentInput.continuum_floor_pos
#print axioms YMGap.Continuum.PhysicalRGSelfSimilar.hierarchical_bondMoving_delta_zero
#print axioms YMGap.Continuum.PhysicalRGSelfSimilar.hierarchicalDescentInput
#print axioms YMGap.Continuum.PhysicalRGSelfSimilar.hierarchical_continuum_floor_pos
