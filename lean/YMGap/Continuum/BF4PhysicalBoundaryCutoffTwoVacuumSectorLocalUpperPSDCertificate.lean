/-
# Generated sector-local upper PSD certificate at cutoff two

The verified cutoff-two canonical vacuum-sector gap is independent of state
enumeration, whereas the historical triangular LDL factors are not.  This
module uses the explicit coordinate right inverse to package that gap as
nonnegativity of the generated canonical head restriction's upper matrix at
the strict rate `49/50`.

Thus the exact restriction used by the cofinal same-object architecture is
inhabited at cutoff two without claiming that a permuted historical LDL table
remains triangular.  No all-cutoff or cofinal certificate, completed-space
gap, thermodynamic or continuum limit, or Clay conclusion is constructed.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalVacuumFiniteFormGap
import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorLocalCanonicalLDLBridge

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumSectorLocalUpperPSDCertificate

set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalVacuumFiniteFormGap
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalVacuumSector
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorUpperGap
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorLocalCanonicalLDLBridge
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteRationalLDLCertificate
open YMGap.Continuum.FiniteRationalReversibleSpectralCertificate

local infix:50 " ≈ " => Q'.eqv

private abbrev cutoffTwoStrictRate : Q' :=
  cutoffTwoSectorRate49Over50

/-- The generated canonical vacuum-sector restriction is upper positive
semidefinite at cutoff two and rate `49/50`. -/
opaque cutoffTwoCanonicalVacuumSectorUpperPSDCertificateAt49Over50 :
    CentralPhysicalFiniteVacuumSectorCanonicalHeadUpperPSDCertificate
      cutoffTwoHalfCoupling (by decide) 2 0 cutoffTwoStrictRate :=
  CentralPhysicalFiniteVacuumSectorCanonicalHeadUpperPSDCertificate.ofMeanZeroAbsGap
    cutoffTwoCanonicalVacuumFinite_abs_gap

/-- Concrete nonnegativity of every reduced vector for the exact generated
canonical upper matrix. -/
theorem cutoffTwoCanonicalVacuumSectorCanonicalHeadUpperMatrix_nonnegative
    (reduced : Nat → Q') :
    (0 : Q') ≤ finiteMatrixQuadratic
      (centralPhysicalFiniteVacuumSectorCanonicalHeadRestriction
        cutoffTwoHalfCoupling (by decide) 2 0
        cutoffTwoStrictRate).reducedSize
      (centralPhysicalFiniteVacuumSectorCanonicalHeadRestriction
        cutoffTwoHalfCoupling (by decide) 2 0
        cutoffTwoStrictRate).upperMatrix
      reduced :=
  cutoffTwoCanonicalVacuumSectorUpperPSDCertificateAt49Over50.upper_nonnegative
    reduced

/-- The generated sector-coordinate matrix obeys the strict upper form bound
at cutoff two. -/
theorem cutoffTwoCanonicalVacuumSectorCoordinate_meanZero_upper_gap
    (coordinate : Nat → Q')
    (hcenter : finiteWeightedMean
        (centralPhysicalFiniteVacuumSectorCoordinateSize
          cutoffTwoHalfCoupling (by decide) 2 0)
        (centralPhysicalFiniteVacuumSectorCoordinateWeight
          cutoffTwoHalfCoupling (by decide) 2 0)
        coordinate ≈ 0) :
    finiteMatrixQuadratic
        (centralPhysicalFiniteVacuumSectorCoordinateSize
          cutoffTwoHalfCoupling (by decide) 2 0)
        (centralPhysicalFiniteVacuumSectorCoordinateKernel
          cutoffTwoHalfCoupling (by decide) 2 0)
        coordinate ≤
      cutoffTwoStrictRate *
        finiteDiagonalQuadratic
          (centralPhysicalFiniteVacuumSectorCoordinateSize
            cutoffTwoHalfCoupling (by decide) 2 0)
          (centralPhysicalFiniteVacuumSectorCoordinateWeight
            cutoffTwoHalfCoupling (by decide) 2 0)
          coordinate :=
  cutoffTwoCanonicalVacuumSectorUpperPSDCertificateAt49Over50.upperContraction
    coordinate hcenter

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumSectorLocalUpperPSDCertificate

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumSectorLocalUpperPSDCertificate.cutoffTwoCanonicalVacuumSectorUpperPSDCertificateAt49Over50
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumSectorLocalUpperPSDCertificate.cutoffTwoCanonicalVacuumSectorCanonicalHeadUpperMatrix_nonnegative
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumSectorLocalUpperPSDCertificate.cutoffTwoCanonicalVacuumSectorCoordinate_meanZero_upper_gap
