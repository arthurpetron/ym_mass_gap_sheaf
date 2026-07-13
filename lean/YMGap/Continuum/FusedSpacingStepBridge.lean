/-
`FusedSpacingStepBridge` — the exact spacing rescaling after the fused spectral
carrier, and a fence around the remaining physical identification.

`FusedSpectralCarrierBridge` proved the lattice-margin inequality for the
corrected Peter--Weyl eigenvalue, but its connection to
`TrueMarginRecursionPhysical` used two scalar equality hypotheses.  This file
removes those equalities from the mathematics: the incoming lattice mass,
outgoing lattice mass, and erosion are definitions of the constructed spectral
data, and the dimensionless step is proved directly.

There are two constructive results.

* At a common positive spacing, dividing the exact lattice inequality by that
  spacing preserves it.
* If the outgoing spacing contracts (`aOut <= aIn`), the same result holds with
  the genuine varying denominators.  The erosion is measured in outgoing units,
  which is the conservative orientation.  Positivity of the incoming lattice
  mass is not assumed: it is derived from the already-located retuned effective
  spectrum.

This is the strongest non-circular bridge available from the present spectral
carrier.  It constructs a spectral mass-over-spacing step, but it does not call
that mass the Yang--Mills Hamiltonian mass.  The first remaining physical
construction is therefore operator-level: prove that the actual finite-volume
YM transfer operator has these finite-character eigenvalues along the actual
contracting lattice-spacing schedule.  A scalar equality field would merely
re-assume that construction, so no new "physical pin" carrier is introduced.

Finally, a kernel-decided fence shows why spacing cannot be recovered from the
spectral mass alone: the same positive anchor mass divided by spacings `1` and
`2` gives different dimensionless margins.  A second fence records that the
unchanged canonical `FrontierDAG.trueMargin` field is type-independent of its
`G` and `L` parameters; it therefore cannot express the missing operator-level
identification.

Constructive contract: exact `Q'`/`Nat`; no `Classical`, `Real`,
`native_decide`, axioms, or holes.
-/

import YMGap.Continuum.FusedSpectralCarrierBridge
import YMGap.Continuum.SpectralMarginBridge
import YMGap.Rubric.FrontierDAG

namespace YMGap.Continuum.FusedSpacingStepBridge

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.ClusteringImpliesGap
open YMGap.Continuum.BondMovingRetuneFix
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.FusedPeterWeylNormalization
open YMGap.Continuum.FusedRatioCorridor
open YMGap.Continuum.FusedSpectralCarrierBridge
open YMGap.Continuum.HeatKernelGap
open YMGap.Continuum.MultiPlaquetteEffectiveTransfer
open YMGap.Continuum.SpectralMarginBridge
open YMGap.Continuum.VacNormEigShift
open YMGap.Continuum.GNSQuotient
open YMGap.Rubric

/-! ## 1. The constructed spectral mass data (definitions, not physical pins) -/

/-- The incoming lattice mass of the retuned effective transfer mode. -/
def incomingMass {w : Q'} (hw0 : (0 : Q') <= w) (k : Nat) : Q' :=
  (1 : Q') -
    (effTransfer (renormWFix 2 (by decide) w)
      (renormWFix_nonneg hw0 2 (by decide)) (k + 1)).lam k

/-- The outgoing lattice mass of the corrected fused Peter--Weyl mode. -/
def outgoingMass (w : Q') (N k : Nat) : Q' :=
  (1 : Q') - lamPW w N (k + 1)

/-- The exact vacuum-normalized additive erosion between the two spectral modes. -/
def spectralErosion {w : Q'} (hw0 : (0 : Q') <= w)
    (hw1 : w <= (1 : Q')) (N k : Nat) : Q' :=
  normEigShift N 2 (by decide) hw0 hw1 (k + 1)

/-- The incoming constructed lattice mass is nonnegative.  This is derived from
the located retuned effective spectrum: its mode lies below a separator `< 1`. -/
theorem incomingMass_nonneg {w : Q'} (hwpos : (0 : Q') < w)
    (hw1 : w <= (1 : Q')) (hwlt : w < (1 : Q')) (k : Nat) :
    (0 : Q') <= incomingMass (Q'.le_of_lt hwpos) k := by
  let G := retunedEffLocatedGap hwpos hw1 hwlt k
  have hsep :
      (effTransfer (renormWFix 2 (by decide) w)
        (renormWFix_nonneg (Q'.le_of_lt hwpos) 2 (by decide)) (k + 1)).lam k
        <= G.sep :=
    G.bound k
  have hle1 :
      (effTransfer (renormWFix 2 (by decide) w)
        (renormWFix_nonneg (Q'.le_of_lt hwpos) 2 (by decide)) (k + 1)).lam k
        <= (1 : Q') :=
    Q'.le_trans' _ _ _ hsep (Q'.le_of_lt G.sep_lt_one)
  exact Q'.sub_nonneg_of_le hle1

/-! ## 2. Direct mass-over-spacing bridges (no scalar pin hypotheses) -/

/-- At a common positive spacing, the constructed spectral masses satisfy the
dimensionless additive step directly. -/
theorem same_spacing_margin_step {w : Q'} (hw0 : (0 : Q') <= w)
    (hw1 : w <= (1 : Q')) (N k : Nat) (a : Q')
    (ha : (0 : Q') < a) :
    Q'.divPos (incomingMass hw0 k) a ha -
        Q'.divPos (spectralErosion hw0 hw1 N k) a ha <=
      Q'.divPos (outgoingMass w N k) a ha := by
  exact hadd_of_hlat_fixed _ _ _ _ ha
    (by
      simpa [incomingMass, outgoingMass, spectralErosion] using
        (fused_margin_after_retuned_erosion hw0 hw1 N k))

/-- If the lattice spacing contracts, the exact lattice spectral step upgrades
to the genuine varying-spacing dimensionless step.  No mass/spacing equality is
assumed: all three numerators are the definitions above. -/
theorem contracting_spacing_margin_step {w : Q'}
    (hwpos : (0 : Q') < w) (hw1 : w <= (1 : Q'))
    (hwlt : w < (1 : Q')) (N k : Nat)
    (aIn aOut : Q') (haIn : (0 : Q') < aIn)
    (haOut : (0 : Q') < aOut) (hcontract : aOut <= aIn) :
    Q'.divPos (incomingMass (Q'.le_of_lt hwpos) k) aIn haIn -
        Q'.divPos
          (spectralErosion (Q'.le_of_lt hwpos) hw1 N k) aOut haOut <=
      Q'.divPos (outgoingMass w N k) aOut haOut := by
  let mIn := incomingMass (Q'.le_of_lt hwpos) k
  let eps := spectralErosion (Q'.le_of_lt hwpos) hw1 N k
  let mOut := outgoingMass w N k
  have hlat : mIn - eps <= mOut :=
    by
      simpa [mIn, eps, mOut, incomingMass, outgoingMass, spectralErosion] using
        (fused_margin_after_retuned_erosion (Q'.le_of_lt hwpos) hw1 N k)
  have hadd0 : mIn <= mOut + eps :=
    EigenvalueShiftBridge.le_add_of_sub_le hlat
  have hadd : mIn <= eps + mOut :=
    Q'.le_trans' _ _ _ hadd0 (Q'.le_of_eqv (Q'.add_comm_eqv mOut eps))
  have hmIn0 : (0 : Q') <= mIn :=
    incomingMass_nonneg hwpos hw1 hwlt k
  have haIn0 : (0 : Q') <= aIn := Q'.le_of_lt haIn
  have hscale : mIn * aOut <= mIn * aIn :=
    Q'.mul_le_mul_of_nonneg_left aOut aIn mIn hcontract hmIn0
  have hmass : mIn * aIn <= (eps + mOut) * aIn :=
    Q'.mul_le_mul_of_nonneg_right mIn (eps + mOut) aIn hadd haIn0
  have hcross : mIn * aOut <= (eps + mOut) * aIn :=
    Q'.le_trans' _ _ _ hscale hmass
  exact hadd_of_hlat_varying mIn mOut eps aIn aOut haIn haOut hcross

/-! ## 3. Machine-checked fences around the remaining physical construction -/

/-- The exact positive anchor spectral mass does not determine a dimensionless
margin without a spacing: dividing the same mass by `1` and by `2` differs. -/
theorem anchor_spacing_ambiguity :
    not (
      (Q'.divPos (outgoingMass w0 3 0) (1 : Q') (by decide)).eqv
      (Q'.divPos (outgoingMass w0 3 0) (2 : Q') (by decide))) := by
  decide

/-- The unchanged canonical DAG's `trueMargin` atom can be projected after an
arbitrary change of the ambient physical `G`/`L` indices: its result type mentions
neither.  This is a statement fence, not a frontier inhabitant. -/
def frontierTrueMargin_ignores_spectral_indices
    {p : z4Chain.toLattice.Plaquette} {w : Q'}
    {D : GNSData} {G : SpectralGapData D.gnsComplete}
    {L : AdditiveTransferOperator D} {N pGamma : Nat}
    (F : FrontierDAG.FrontierDAG p w G L N pGamma)
    {D' : GNSData} (_G' : SpectralGapData D'.gnsComplete)
    (_L' : AdditiveTransferOperator D') :
    UniformCouplingFromAF.TrueMarginRecursion :=
  F.trueMargin

/-- The reindexed projection is definitionally the same legacy margin atom. -/
theorem frontierTrueMargin_ignores_spectral_indices_eq
    {p : z4Chain.toLattice.Plaquette} {w : Q'}
    {D : GNSData} {G : SpectralGapData D.gnsComplete}
    {L : AdditiveTransferOperator D} {N pGamma : Nat}
    (F : FrontierDAG.FrontierDAG p w G L N pGamma)
    {D' : GNSData} (G' : SpectralGapData D'.gnsComplete)
    (L' : AdditiveTransferOperator D') :
    frontierTrueMargin_ignores_spectral_indices F G' L' = F.trueMargin :=
  rfl

end YMGap.Continuum.FusedSpacingStepBridge

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.FusedSpacingStepBridge.incomingMass_nonneg
#print axioms YMGap.Continuum.FusedSpacingStepBridge.same_spacing_margin_step
#print axioms YMGap.Continuum.FusedSpacingStepBridge.contracting_spacing_margin_step
#print axioms YMGap.Continuum.FusedSpacingStepBridge.anchor_spacing_ambiguity
#print axioms YMGap.Continuum.FusedSpacingStepBridge.frontierTrueMargin_ignores_spectral_indices
#print axioms YMGap.Continuum.FusedSpacingStepBridge.frontierTrueMargin_ignores_spectral_indices_eq
