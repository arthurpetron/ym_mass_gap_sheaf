/-
M4d -- bind the OS functional and reconstruction data to one projective
continuum-measure thread.

The legacy `OSAxiomBundle mu` and `OSReconstruction mu` signatures remember
`mu` only as a type parameter.  Their content fields can otherwise select
unrelated functionals, spectral models, and gap bounds.  This module supplies
the stronger provenance layer needed by the physical-separator route.

There are two independent bindings.

* `ProjectiveOSFunctionalIdentification` requires the OS Schwinger functional
  to be the constructive limit of an externally fixed evaluator on the
  selected stage measures `mu.pick j`.
* `BundleLinkedOSReconstructionData` constructs the reconstruction through
  `os_reconstruct_su2` using exactly the observable bundle's spectral model
  and gap bound.  The OS4 model/rate and reconstruction model/rate are
  therefore definitionally the same data.

`MeasureLinkedOSGNSData` packages both.  It is still an open Type-level input:
no continuum measure theory, GNS completion, Stone theorem, or spectral
theorem is manufactured here.
-/

import YMGap.Constructive.CRealAbs
import YMGap.Continuum.FourDExistence

namespace YMGap.Continuum.MeasureLinkedOSReconstruction

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.ContinuumMeasure
open YMGap.Continuum.FourDExistence
open YMGap.Continuum.ObservableMeasure
open YMGap.Continuum.OSAxioms
open YMGap.Continuum.OSReconstruction
open YMGap.Continuum.SpectralGap

/-! ## 1. The OS functional as a limit of the selected measure thread -/

/-- External finite-stage expectation semantics for one fixed observable
algebra.  It is a parameter of the identification below, so the equality
witness cannot choose an evaluator that ignores the selected measures. -/
structure StageOSFunctionalSemantics
    (A : ObsAlg) (M : Nat -> Type) : Type 1 where
  expectationFromStage : (j : Nat) -> M j -> A.carrier -> CReal

/-- The Schwinger functional stored by a continuum Yang--Mills existence datum
is the cutoff limit of the externally fixed evaluator on the same projective
measure thread.

This is the missing measure-provenance assertion in the legacy OS bundle: the
functional `H.os_axioms.E` is no longer merely carried alongside `mu`. -/
structure ProjectiveOSFunctionalIdentification
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (H : ContinuumYMExistence mu)
    (stageFunctional :
      StageOSFunctionalSemantics H.os_axioms.A M) : Type 1 where
  stageExpectationConverges : forall a : H.os_axioms.A.carrier,
    CReal.ConvergesTo
      (fun j => stageFunctional.expectationFromStage j (mu.pick j) a)
      (CReal.ofQ' (H.os_axioms.E.E a))

/-! ## 2. Reconstruction from exactly the same OS spectral data -/

/-- Reconstruction inputs whose spectral model and separator are fixed to be
the model `H.os_axioms.S` and rate `H.os_axioms.mu` already used by OS4.

The analytic Hilbert/GNS laws remain honest supplied propositions because the
current constructive substrate does not yet implement the required Hilbert
completion, unbounded operators, or Stone functional calculus. -/
structure BundleLinkedOSReconstructionData
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (H : ContinuumYMExistence mu) : Type 1 where
  space : HilbertSpace
  vacuum : VectorIn space
  semigroup : ContractionSemigroup space
  hamiltonian : SelfAdjointOp space
  vacuum_normalized : VacuumNormalized vacuum
  hamiltonian_nonneg : HamiltonianNonneg hamiltonian
  vacuum_annihilated : VacuumAnnihilated hamiltonian vacuum
  semigroup_generated : SemigroupGenerated hamiltonian semigroup
  gapBound_nonneg : (0 : Q') <= H.os_axioms.μ
  gapBound_lt_one : H.os_axioms.μ < 1
  hasGap : SpectralGapBound H.os_axioms.S H.os_axioms.μ

namespace BundleLinkedOSReconstructionData

/-- Construct the OS reconstruction through the bundle-consuming smart
constructor, using exactly the OS4 spectral model and gap bound. -/
def reconstruction
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    (D : BundleLinkedOSReconstructionData H) : OSReconstruction mu :=
  os_reconstruct_su2 mu H.os_axioms
    D.space D.vacuum D.semigroup D.hamiltonian
    D.vacuum_normalized D.hamiltonian_nonneg D.vacuum_annihilated
    D.semigroup_generated H.os_axioms.S H.os_axioms.μ
    D.gapBound_nonneg D.gapBound_lt_one D.hasGap

@[simp] theorem reconstruction_spec
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    (D : BundleLinkedOSReconstructionData H) :
    D.reconstruction.spec = H.os_axioms.S := rfl

@[simp] theorem reconstruction_gapBound
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    (D : BundleLinkedOSReconstructionData H) :
    D.reconstruction.gapBound = H.os_axioms.μ := rfl

/-- The OS4 clustering statement and the reconstructed spectral statement are
about definitionally the same spectral model and separator. -/
def reconstructionCarriesOS4
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    (D : BundleLinkedOSReconstructionData H) :
    IsOS4ClusterProperty D.reconstruction.spec
      D.reconstruction.gapBound :=
  H.os_axioms.os4_cluster

end BundleLinkedOSReconstructionData

/-! ## 3. The combined measure-linked OS/GNS boundary -/

/-- The non-phantom OS/GNS provenance needed by the M4 continuum endpoint.

An inhabitant supplies both a functional limit on the selected projective
thread and a reconstruction made from exactly that functional bundle's OS4
spectral data. -/
structure MeasureLinkedOSGNSData
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (H : ContinuumYMExistence mu) : Type 2 where
  stageFunctional : StageOSFunctionalSemantics H.os_axioms.A M
  projectiveFunctional :
    ProjectiveOSFunctionalIdentification H stageFunctional
  reconstructionData : BundleLinkedOSReconstructionData H

namespace MeasureLinkedOSGNSData

/-- The reconstruction determined by the same measure-linked OS bundle. -/
def reconstruction
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    (D : MeasureLinkedOSGNSData H) : OSReconstruction mu :=
  D.reconstructionData.reconstruction

/-- Its OS4 statement is inherited from definitionally identical bundle data. -/
def reconstructionCarriesOS4
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    (D : MeasureLinkedOSGNSData H) :
    IsOS4ClusterProperty D.reconstruction.spec
      D.reconstruction.gapBound :=
  D.reconstructionData.reconstructionCarriesOS4

end MeasureLinkedOSGNSData

end YMGap.Continuum.MeasureLinkedOSReconstruction

#print axioms YMGap.Continuum.MeasureLinkedOSReconstruction.BundleLinkedOSReconstructionData.reconstruction
#print axioms YMGap.Continuum.MeasureLinkedOSReconstruction.BundleLinkedOSReconstructionData.reconstruction_spec
#print axioms YMGap.Continuum.MeasureLinkedOSReconstruction.BundleLinkedOSReconstructionData.reconstruction_gapBound
#print axioms YMGap.Continuum.MeasureLinkedOSReconstruction.BundleLinkedOSReconstructionData.reconstructionCarriesOS4
#print axioms YMGap.Continuum.MeasureLinkedOSReconstruction.MeasureLinkedOSGNSData.reconstructionCarriesOS4
