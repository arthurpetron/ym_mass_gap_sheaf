/-
# Reduce the cutoff-two physical table to 127 spatial-S3 representatives

The exact raw table has 499 nonzero upper-triangular entries.  Checked spatial
axis permutations and physical/raw kernel symmetry contract those entries to
the 127 literal representative codes certified by the generated coverage
rows.  This module packages precisely the remaining physical equalities and
compiles them into the existing nonzero-upper certificate, hence into the full
65 by 65 physical table certificate.

The representative certificate is deliberately not inhabited here.  This is
a finite cutoff-two reduction only; it supplies no uniform-cutoff, spectral,
thermodynamic-limit, or continuum claim.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorNonzeroUpperReduction
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSpatialS3PairCanonicalization
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSpatialS3RawCanonicalUpperRows
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSpatialS3NonzeroRepresentativeCoverageRows

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSpatialS3RepresentativeReduction

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportData
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSubsetEnumeration
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorNonzeroUpperReduction
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorPhysicalKernelBridge
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawKernelCertificate
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSpatialS3NonzeroRepresentativeCoverageRows
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSpatialS3NonzeroRepresentativeData
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSpatialS3PairCanonicalization
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSpatialS3PairCanonicalizationData
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSpatialS3RawCanonicalUpperRows
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

/-- The `Fin 65` state accessor used by spatial transport is the in-range
version of the `Nat`/`getD` accessor used by the raw-table bridge. -/
theorem cutoffTwoSectorStateAt_fin_eq_nat (index : Fin 65) :
    BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportData.cutoffTwoSectorStateAt
        index =
      BF4PhysicalBoundaryCutoffTwoSectorRawKernelCertificate.cutoffTwoSectorStateAt
        index.val := by
  unfold
    BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportData.cutoffTwoSectorStateAt
    BF4PhysicalBoundaryCutoffTwoSectorRawKernelCertificate.cutoffTwoSectorStateAt
  have hlength : index.val < cutoffTwoCubeSectorStates.length := by
    rw [cutoffTwoCubeSectorStates_length]
    exact index.isLt
  rw [← List.getElem_eq_getD (h := hlength) zeroEdgeLabelling]
  rfl

/-- The exact residual after zero removal, symmetry, and spatial-S3 orbit
reduction.  The Boolean premise recognizes exactly the explicit 127-code
carrier; a later certificate producer must prove the physical/raw equality
only on those representatives. -/
structure CutoffTwoSectorPhysicalSpatialS3RepresentativeCertificate : Type where
  representativeChecked : ∀ (pair : CutoffTwoSectorPair),
    cutoffTwoSpatialS3NonzeroRepresentativeCodeCheck
        (cutoffTwoSectorPairCode pair) = true →
    centralPhysicalReflectedKernel cutoffTwoHalfCoupling 2 0
        (BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportData.cutoffTwoSectorStateAt
          pair.row)
        (BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportData.cutoffTwoSectorStateAt
          pair.column) ≈
      cutoffTwoSectorRawKernel pair.row.val pair.column.val

/-- A checked representative certificate propagates to every nonzero upper
entry by physical transport to the canonical pair and checked raw transport
back to the source pair. -/
theorem centralPhysicalReflectedKernel_cutoffTwo_finStateAt_eqv_raw_of_spatialS3Representative
    (certificate : CutoffTwoSectorPhysicalSpatialS3RepresentativeCertificate)
    {row column : Fin 65}
    (hupper : row.val ≤ column.val)
    (hnonzero : ¬ cutoffTwoSectorRawKernel row.val column.val ≈ 0) :
    centralPhysicalReflectedKernel cutoffTwoHalfCoupling 2 0
        (BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportData.cutoffTwoSectorStateAt
          row)
        (BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportData.cutoffTwoSectorStateAt
          column) ≈
      cutoffTwoSectorRawKernel row.val column.val := by
  have hphysical :=
    centralPhysicalReflectedKernel_cutoffTwo_pairCanonical_eqv
      (⟨row, column⟩ : CutoffTwoSectorPair)
  have hcode :=
    cutoffTwoSectorPairCanonicalCodeCheck_nonzeroRepresentative
      (row := row) (column := column) hupper hnonzero
  have hrepresentative := certificate.representativeChecked
    (cutoffTwoSectorPairCanonical ⟨row, column⟩) hcode
  have hraw := cutoffTwoSectorRawKernel_pairCanonical_eqv_of_upper
    (row := row) (column := column) hupper
  exact Q'.eqv_trans _ _ _ hphysical
    (Q'.eqv_trans _ _ _ hrepresentative (Q'.eqv_symm hraw))

/-- Compile the 127-representative residual into the previously established
499-entry nonzero-upper certificate. -/
def CutoffTwoSectorPhysicalSpatialS3RepresentativeCertificate.toNonzeroUpperCertificate
    (certificate : CutoffTwoSectorPhysicalSpatialS3RepresentativeCertificate) :
    CutoffTwoSectorPhysicalNonzeroUpperCertificate where
  upperNonzeroChecked := by
    intro row column hrow hcolumn hupper hnonzero
    let rowFin : Fin 65 := ⟨row, hrow⟩
    let columnFin : Fin 65 := ⟨column, hcolumn⟩
    have hfinite :=
      centralPhysicalReflectedKernel_cutoffTwo_finStateAt_eqv_raw_of_spatialS3Representative
        certificate (row := rowFin) (column := columnFin) hupper hnonzero
    simpa only [cutoffTwoSectorStateAt_fin_eq_nat] using hfinite

/-- Consequently, the 127-representative residual is sufficient for the
original full 65-row production physical-table certificate. -/
def CutoffTwoSectorPhysicalSpatialS3RepresentativeCertificate.toPhysicalTableCertificate
    (certificate : CutoffTwoSectorPhysicalSpatialS3RepresentativeCertificate) :
    CutoffTwoSectorPhysicalTableCertificate :=
  certificate.toNonzeroUpperCertificate.toPhysicalTableCertificate

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSpatialS3RepresentativeReduction

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSpatialS3RepresentativeReduction.cutoffTwoSectorStateAt_fin_eq_nat
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSpatialS3RepresentativeReduction.centralPhysicalReflectedKernel_cutoffTwo_finStateAt_eqv_raw_of_spatialS3Representative
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSpatialS3RepresentativeReduction.CutoffTwoSectorPhysicalSpatialS3RepresentativeCertificate.toNonzeroUpperCertificate
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSpatialS3RepresentativeReduction.CutoffTwoSectorPhysicalSpatialS3RepresentativeCertificate.toPhysicalTableCertificate
