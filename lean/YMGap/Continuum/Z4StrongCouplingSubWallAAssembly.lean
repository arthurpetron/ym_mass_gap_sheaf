/-
# Exact assembly of the formal Z4 strong-coupling Sub-wall A bundle

Later constructive modules discharge every field of the older
`Tier0Scorecard.SubWallA` interface:

* the noncollapsed Z4 separation lattice;
* the hard-core tree-graph bound;
* the reconstructed Z4 Mayer--Ursell bridge decomposition;
* the guarded doubly-stochastic permutation witness at the coarse Racah layer;
* the exact rational dimension-weighted SU(2) 6j-squared kernel at the numeric
  layer.

The assembly below is therefore a real closure of that *formal* bundle.  It is
not closure of the physical Biedenharn--Elliott associator: the field
`SubWallA.a2Pentagon` has type `PentagonNumericCore`, which asks only for
nonnegativity and one pinned value.  To make that interface weakness permanent
and machine-visible, this file also assembles `SubWallA` with the constant
shape witness and proves that the resulting kernel fails even the naively
transcribed nonlinear pentagon equation at the all-zero labels.  This last
test is deliberately named `NaiveKernelPentagon`: a Racah probability kernel
is not being identified with the differently normalized tetrahedral amplitude.

Thus the proved result is exactly scoped: the historical `SubWallA` carrier is
inhabited, while a future physical scorecard must separately require the
correctly normalized nonlinear pentagon/coherence data.
-/

import YMGap.Continuum.Tier0Scorecard
import YMGap.Continuum.SepLatticeZ4Close
import YMGap.Continuum.UrsellPinComplete
import YMGap.Continuum.MayerUrsellZ4PhysicalClose
import YMGap.Continuum.RacahInhabit
import YMGap.Continuum.SixJKernel

namespace YMGap.Continuum.Z4StrongCouplingSubWallAAssembly

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.PinnedCluster
open YMGap.Continuum.PentagonRelation

/-- Assemble the historical `SubWallA` interface from the exact constructive
witnesses now available in the development.  The parameter `w` is retained
because it is part of the pinned interface, although the interface's fields use
the fixed coupling `w4`. -/
def strongCouplingSubWallAOfCore
    (p : ClusterCount4DProgress.z4Chain.toLattice.Plaquette) (w : Q')
    (core : PentagonNumericCore) : Tier0Scorecard.SubWallA p w where
  d2Sep := SepLatticeZ4Close.SepLatticeZ4_witness
  tTree := UrsellPinComplete.treeGraphBoundHardCore
    SepLatticeZ4Close.SepLatticeZ4_witness.val
    Stage1LoopyReduction.w4 GenuineKP.gr
  d1Mayer := MayerUrsellZ4PhysicalClose.bridgeDecomposition_z4_recon p
  a2Racah := RacahInhabit.racahRP
  a2Pentagon := core

/-- The strongest currently derived inhabitant uses the exact finite-sum,
dimension-weighted SU(2) 6j-squared kernel, rather than the constant shape
witness. -/
def strongCouplingSubWallA
    (p : ClusterCount4DProgress.z4Chain.toLattice.Plaquette) (w : Q') :
    Tier0Scorecard.SubWallA p w :=
  strongCouplingSubWallAOfCore p w SixJKernel.racahKernelCore

/-- Projection check: the assembled numeric layer is definitionally the exact
SU(2) Racah kernel computed in `SixJKernel`. -/
theorem strongCouplingSubWallA_kernel
    (p : ClusterCount4DProgress.z4Chain.toLattice.Plaquette) (w : Q')
    (j : Fin 6 -> Rep) :
    (strongCouplingSubWallA p w).a2Pentagon.racahKernel j =
      SixJKernel.racahKernelQ j :=
  rfl

/-- The assembled tree-graph component exposes its actual inequality; this is
not inhabitation through an empty premise. -/
theorem strongCouplingSubWallA_tree_graph
    (p : ClusterCount4DProgress.z4Chain.toLattice.Plaquette) (w : Q')
    (Y : Polymer SepLatticeZ4Close.SepLatticeZ4_witness.val.toLattice) :
    (strongCouplingSubWallA p w).tTree.phiT Y <=
      KPCriterion.eSurrogate ^ Polymer.size Y :=
  (strongCouplingSubWallA p w).tTree.tree_graph Y

/-! ## An exact under-specification fence

This diagnostic property copies the wiring of `PentagonRelation.pentagon` but
feeds a `PentagonNumericCore.racahKernel` into it.  It is intentionally *not* a
claim that the two normalizations should be identified.  Its role is narrower:
the historical numeric-core field does not entail nonlinear coherence even
under this most direct transcription.
-/

def NaiveKernelPentagon (core : PentagonNumericCore) : Prop :=
  forall (D a b c d e f : Rep), a + b + c + d + e + f < D ->
    (finSum (fun x => Q'.ofNat (x + 1) *
        (core.racahKernel (PartitionBeyondTree.mk6 a b c d e x) *
          core.racahKernel (PartitionBeyondTree.mk6 a x e f b c) *
          core.racahKernel (PartitionBeyondTree.mk6 x c d e f a))) D).eqv
      (core.racahKernel (PartitionBeyondTree.mk6 a b c d e f) *
        core.racahKernel (PartitionBeyondTree.mk6 b c d e f a))

/-- The constant `1/4` shape witness satisfies every field of
`PentagonNumericCore` but fails the directly transcribed nonlinear equation:
at `D = 1` and all external labels zero, the two sides are `1/64` and `1/16`.
-/
theorem numericShapeWitness_not_naiveKernelPentagon :
    ¬ NaiveKernelPentagon numericShapeWitness := by
  intro h
  have hbad := h 1 0 0 0 0 0 0 (by decide)
  have hne : ¬
      (finSum (fun x => Q'.ofNat (x + 1) *
          (numericShapeWitness.racahKernel
              (PartitionBeyondTree.mk6 0 0 0 0 0 x) *
            numericShapeWitness.racahKernel
              (PartitionBeyondTree.mk6 0 x 0 0 0 0) *
            numericShapeWitness.racahKernel
              (PartitionBeyondTree.mk6 x 0 0 0 0 0))) 1).eqv
        (numericShapeWitness.racahKernel
            (PartitionBeyondTree.mk6 0 0 0 0 0 0) *
          numericShapeWitness.racahKernel
            (PartitionBeyondTree.mk6 0 0 0 0 0 0)) := by
    decide
  exact hne hbad

/-- Consequently the full historical `SubWallA` bundle can be inhabited while
its numeric-core field fails `NaiveKernelPentagon`.  This is the checked fence
against treating formal bundle closure as physical pentagon closure. -/
theorem subWallA_does_not_encode_pentagon
    (p : ClusterCount4DProgress.z4Chain.toLattice.Plaquette) (w : Q') :
    ¬ NaiveKernelPentagon
      (strongCouplingSubWallAOfCore p w numericShapeWitness).a2Pentagon :=
  numericShapeWitness_not_naiveKernelPentagon

/-! ## Exact compression of the historical Tier-0 carrier

With its fixed-spacing and Sub-wall A fields now constructively available, the
historical `Tier0Scorecard` is equi-inhabited with its sole remaining field,
`SpectralMarginInput`.  The maps below are only frontier bookkeeping: they do
not inhabit that physical RG/spectral input.
-/

/-- Assemble the complete historical Tier-0 scorecard from precisely one
`SpectralMarginInput`; all other fields are now derived. -/
def tier0ScorecardOfSpectralMarginInput
    {b : Nat} {afr : AFRateCalibration.AFRateModulus} {N0 : Nat}
    (p : ClusterCount4DProgress.z4Chain.toLattice.Plaquette) (w : Q')
    (input : AsymptoticSpectralLoc.SpectralMarginInput b afr N0) :
    Tier0Scorecard.Tier0Scorecard p w b afr N0 where
  fixedSpacing := Tier0Scorecard.fixedSpacing_met
  subA := strongCouplingSubWallA p w
  subB := input

/-- The reverse map is the surviving field itself. -/
def spectralMarginInputOfTier0Scorecard
    {p : ClusterCount4DProgress.z4Chain.toLattice.Plaquette} {w : Q'}
    {b : Nat} {afr : AFRateCalibration.AFRateModulus} {N0 : Nat}
    (scorecard : Tier0Scorecard.Tier0Scorecard p w b afr N0) :
    AsymptoticSpectralLoc.SpectralMarginInput b afr N0 :=
  scorecard.subB

/-- The assembly is a right inverse of the projection, so no information about
the remaining `SpectralMarginInput` is hidden in the compression. -/
theorem spectralMarginInput_scorecard_retraction
    {b : Nat} {afr : AFRateCalibration.AFRateModulus} {N0 : Nat}
    (p : ClusterCount4DProgress.z4Chain.toLattice.Plaquette) (w : Q')
    (input : AsymptoticSpectralLoc.SpectralMarginInput b afr N0) :
    spectralMarginInputOfTier0Scorecard
      (tier0ScorecardOfSpectralMarginInput p w input) = input :=
  rfl

end YMGap.Continuum.Z4StrongCouplingSubWallAAssembly

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4StrongCouplingSubWallAAssembly.strongCouplingSubWallA
#print axioms YMGap.Continuum.Z4StrongCouplingSubWallAAssembly.strongCouplingSubWallA_kernel
#print axioms YMGap.Continuum.Z4StrongCouplingSubWallAAssembly.strongCouplingSubWallA_tree_graph
#print axioms YMGap.Continuum.Z4StrongCouplingSubWallAAssembly.numericShapeWitness_not_naiveKernelPentagon
#print axioms YMGap.Continuum.Z4StrongCouplingSubWallAAssembly.subWallA_does_not_encode_pentagon
#print axioms YMGap.Continuum.Z4StrongCouplingSubWallAAssembly.tier0ScorecardOfSpectralMarginInput
#print axioms YMGap.Continuum.Z4StrongCouplingSubWallAAssembly.spectralMarginInput_scorecard_retraction
