/-
**Track A2 — the real `Zreal` and the consumer discharge: inhabiting
`PhysicalRecouplingInterface` NON-VACUOUSLY (real `Zreal`, not `Zreal := Ξ`).**

`RecouplingInterface` extracted the genuine minimal A2 interface
`PhysicalRecouplingInterface` — a recoupling datum (the discharged elementary
½-recoupling) TOGETHER with the real partition function `Zreal` and the consumer
identity `Ξ ≃ Zreal` — and flagged the fake-close trap `under_cut_is_fake`
(`Zreal := Ξ`, no content).  This module inhabits that interface with a GENUINE
`Zreal`:

  * `Zreal := TreePartitionIdentity.ZrealTree` — the REAL partition function
    built by the iterated single-link Haar collapse (one `Z2_collapse` /
    2-fold-orthogonality per shared link = the elementary recoupling), defined by
    its OWN recursion WITHOUT any reference to `Ξ` (so it is NOT the `Zreal := Ξ`
    under-cut);
  * `identity := tree_partition_identity` — the PROVED abstract↔real identity
    `Ξ ≃ ZrealTree` (well-founded induction matching the two independent
    recursions), holding for EVERY polymer family `Γ`;
  * `recoupling := elementaryRecoupling` — the discharged, trace-faithful
    (`3 ≠ 1`) elementary Jones–Wenzl recoupling datum.

The 6j VALUE that the recoupling datum carries is now computed from the rep
category as an apolar norm ratio (`A2ApolarValue.apolar_dimweighted_6j_sq`,
`sixj_value_is_apolar_norm_ratio`).  So the interface is inhabited with: real
`Zreal`, proved `Ξ ≃ Zreal`, discharged elementary recoupling, and the apolar 6j
value — and it discharges the LITERAL A2 consumer
`Stage1Loopy.physical_identity` (which invokes only the `identity` field,
`RecouplingInterface.physical_identity_factors`).

# What this discharges vs. what remains (HONEST — AGENTS.md Rule 6)

DISCHARGED (genuine, axiom-clean, non-vacuous):
  * `PhysicalRecouplingInterface` INHABITED with a real (non-`Ξ`-alias) `Zreal`;
  * the consumer identity `Ξ ≃ ZrealTree` for every `Γ` (the exact obligation
    `physical_identity` factors through);
  * the elementary recoupling datum (trace-faithful `3 ≠ 1`);
  * the 6j value `1/4` as the apolar norm ratio (`A2ApolarValue`).

REMAINS (NOT faked, sharply named — the genuine loopy gap):
  `ZrealTree` is the real Haar partition function only on TREE geometry (≤ 2
  shared links: each add-one is a single 2-fold-orthogonality collapse).  On the
  loopy `z4` lattice, links are shared by ≥ 3 plaquettes, where the TRUE Wilson /
  Haar partition function needs the closed-fusion-loop 6j (the
  `PartitionBeyondTree.SixJRecoupling.biedenharn_elliott` Racah recoupling
  IDENTITY — the full sum rule for all `a,b,c,d,e`, strictly stronger than the
  single smallest-tetrahedron VALUE computed here).  So the residual is exactly:
  *build the loopy `Zreal` weaving the 6j recoupling identity into the partition
  function, and prove `Ξ ≃` that loopy `Zreal`.*  `SixJRecoupling` stays
  UNINHABITED; the Clay YM mass gap stays OPEN.

# Constructive contract (AGENTS.md Rules 1/6/8)

Mathlib-free; `Q'`/`Nat` core only.  No `Real`, `Classical.*`, `native_decide`,
`sorry`.  The interface inhabitant is `Type`-level data assembled from PROVED
components; the loopy 6j `Zreal` is a NAMED residual, never faked.  `#print
axioms` gated to `propext`/`Quot.sound`.
-/

import YMGap.Continuum.RecouplingInterface
import YMGap.Continuum.TreePartitionIdentity
import YMGap.Continuum.A2ApolarValue

namespace YMGap.Continuum.A2RecouplingDischarge

open YMGap.Constructive
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.AbstractPolymerXi
open YMGap.Continuum.PartitionBeyondTree
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Stage1LoopyReduction
open YMGap.Continuum.TreePartitionIdentity
open YMGap.Continuum.RecouplingInterface
open YMGap.Continuum.TemperleyLiebRecoupling
open YMGap.Continuum.PentagonRelation

/-! ## 1. The real `Zreal` inhabiting `PhysicalRecouplingInterface`. -/

/-- **`physRecouplingInterface` — the genuine minimal A2 interface, INHABITED
NON-VACUOUSLY.**  A recoupling datum (the discharged elementary ½-recoupling)
together with the REAL partition function `ZrealTree` (the iterated single-link
Haar collapse, defined WITHOUT reference to `Ξ`) and the PROVED identity
`Ξ ≃ ZrealTree`.  This is NOT the `Zreal := Ξ` under-cut
(`RecouplingInterface.under_cut_is_fake`): `ZrealTree` is a genuinely different
function (its own Haar-collapse recursion), proved value-equal to `Ξ` by
`tree_partition_identity`. -/
def physRecouplingInterface [DecidableEq z4Chain.toLattice.Plaquette]
    (w : Q') (label : z4Chain.toLattice.Plaquette → Rep) :
    PhysicalRecouplingInterface w label where
  recoupling := elementaryRecoupling
  Zreal := fun Γ => ZrealTree w label Γ
  identity := fun Γ => tree_partition_identity w label Γ

/-- **The interface discharges the A2 consumer identity.**  For the
strong-coupling weight `w4`, `physRecouplingInterface` supplies exactly
`(Xi w4 Γ label).eqv (Zreal Γ)` — the obligation
`Stage1Loopy.physical_identity` factors through
(`RecouplingInterface.physical_identity_factors`,
`physical_identity_of_interface`). -/
theorem physical_identity_discharged [DecidableEq z4Chain.toLattice.Plaquette]
    (label : z4Chain.toLattice.Plaquette → Rep)
    (Γ : List (Polymer z4Chain.toLattice)) :
    (Xi w4 Γ label).eqv ((physRecouplingInterface w4 label).Zreal Γ) :=
  physical_identity_of_interface (physRecouplingInterface w4 label) Γ

/-- **The discharged `Zreal` is the REAL single-link Haar collapse, not `Ξ`.**
`ZrealTree` satisfies its own add-one recursion (omit the new plaquette, or
integrate its single shared link via the 2-fold orthogonality `Z2_collapse`) —
`ZrealTree_cons` — which is defined independently of `Ξ`.  This exhibits the
`Zreal` here as a genuine recoupling-built object, distinguishing it from the
trivial `Zreal := Ξ` alias. -/
theorem physInterface_Zreal_is_real [DecidableEq z4Chain.toLattice.Plaquette]
    (w : Q') (label : z4Chain.toLattice.Plaquette → Rep)
    (γ : Polymer z4Chain.toLattice) (Λ : List (Polymer z4Chain.toLattice)) :
    (physRecouplingInterface w label).Zreal (γ :: Λ)
      = ZrealTree w label Λ
          + activity w γ label
              * ZrealTree w label (Λ.filter (fun X => compatibleB γ X)) :=
  ZrealTree_cons w label γ Λ

/-- **Non-vacuity of the recoupling datum** (a shape witness could not do this):
the interface's elementary recoupling separates the SU(2) channels — its two
Jones–Wenzl projectors have distinct traces `dim χ₂ = 3 ≠ 1 = dim χ₀`. -/
theorem physInterface_recoupling_nonvacuous
    [DecidableEq z4Chain.toLattice.Plaquette]
    (w : Q') (label : z4Chain.toLattice.Plaquette → Rep) :
    ¬ (mtr (physRecouplingInterface w label).recoupling.p_top).eqv
        (mtr (physRecouplingInterface w label).recoupling.p_bot) :=
  elementaryRecoupling_nonvacuous

/-! ## 2. The 6j value carried by the interface is the apolar norm ratio.

Re-export of `A2ApolarValue`: the recoupling datum's 6j VALUE at the smallest
tetrahedron is the ratio of apolar norms of the transvectant coupling trees,
`⟨A,B⟩²/(⟨A,A⟩⟨B,B⟩) = 1/4`, matching the physical factorial kernel. -/

/-- The 6j value the interface carries is the rep-category apolar norm ratio. -/
theorem interface_sixj_value_is_apolar :
    (A2ApolarValue.crossAB * A2ApolarValue.crossAB).eqv
      (oneQuarter * (A2ApolarValue.normAA * A2ApolarValue.normBB)) :=
  A2ApolarValue.apolar_dimweighted_6j_sq

/-! ## 3. Documentation: PROVED vs NAMED-open (AGENTS.md Rule 6)

PROVED (genuine, axiom-clean, non-vacuous):

  * `physRecouplingInterface` — `PhysicalRecouplingInterface` INHABITED with the
    real `Zreal := ZrealTree` (NOT the `Zreal := Ξ` under-cut), the discharged
    `elementaryRecoupling`, and the proved identity `Ξ ≃ ZrealTree`;
  * `physical_identity_discharged` — the A2 consumer identity `Ξ ≃ Zreal` is
    supplied at `w4` (what `Stage1Loopy.physical_identity` factors through);
  * `physInterface_Zreal_is_real` — the `Zreal` is the genuine single-link Haar
    collapse (its own recursion), not the `Ξ` alias;
  * `physInterface_recoupling_nonvacuous` — the recoupling datum separates the
    channels (`3 ≠ 1`);
  * `interface_sixj_value_is_apolar` — the 6j value is the apolar norm ratio.

NAMED-open (NOT faked, NO inhabitant — the genuine loopy gap):

  * the LOOPY real `Zreal`: on the `z4` lattice (links shared by ≥ 3 plaquettes)
    the TRUE Wilson/Haar partition function needs the closed-fusion-loop 6j
    Racah IDENTITY (`PartitionBeyondTree.SixJRecoupling.biedenharn_elliott`, the
    full sum rule for all `a,b,c,d,e` — strictly stronger than the single
    smallest-tetrahedron VALUE proved in `A2ApolarValue`), woven into the
    partition function, plus `Ξ ≃` that loopy `Zreal`.  `SixJRecoupling` stays
    UNINHABITED.

This module DISCHARGES the literal A2 consumer with a real recoupling-built
`Zreal` at TREE level (≤ 2 shared links) and computes the 6j value from the rep
category.  It is NOT the loopy `≥ 3`-shared-link 6j-network matching, NOT a
continuum limit, and NOT a 4D Yang–Mills mass gap.  The Clay problem stays
OPEN. -/

end YMGap.Continuum.A2RecouplingDischarge

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.A2RecouplingDischarge.physRecouplingInterface
#print axioms YMGap.Continuum.A2RecouplingDischarge.physical_identity_discharged
#print axioms YMGap.Continuum.A2RecouplingDischarge.physInterface_Zreal_is_real
#print axioms YMGap.Continuum.A2RecouplingDischarge.physInterface_recoupling_nonvacuous
#print axioms YMGap.Continuum.A2RecouplingDischarge.interface_sixj_value_is_apolar
