/-
# Exact two-sided LDL compiler for the cofinal physical BF4 gap

At one physical cutoff, the absolute centered correlation bound requires two
positive-semidefinite matrices:

  (1/16) D - K + d d^T,     (1/16) D + K + d d^T.

This module connects literal Boolean LDL checks of those canonical matrices to
the exact physical carrier and then packages a constructively cofinal family
of successful checks as `FixedNomeCofinalCenteredSixteenth`.

The records below are certificate interfaces, not inhabitants.  In particular,
this module supplies no LDL tables and proves no unbounded fixed-nome family.
Thermodynamic, continuum, QFT-axiom, and Clay conclusions remain open.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalCutoffCofinalConnectedGap
import YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
import YMGap.Continuum.FiniteRationalPenalizedMatrix

namespace YMGap.Continuum.BF4PhysicalCutoffCofinalLDLGap

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffCofinalConnectedGap
open YMGap.Continuum.BF4PhysicalCutoffConnectedGap
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4WeightedJointPerronPerturbation
open YMGap.Continuum.FiniteRationalLDLCertificate
open YMGap.Continuum.FiniteRationalPenalizedMatrix
open YMGap.Continuum.FiniteRationalReversibleSpectralCertificate
open YMGap.Continuum.OSReconstructionProgress
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The exact per-cutoff PSD interface -/

/-- Nonnegativity of the two canonical penalized matrices at one genuine
physical cutoff.  The quantification over coefficient vectors is the direct
soundness target of either exact LDL checker below. -/
structure CentralPhysicalTwoSidedPSDCertificate
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat) (q : Q') : Type 1 where
  upperNonnegative :
    ∀ coefficient : Nat → Q',
      (0 : Q') ≤
        finiteMatrixQuadratic
          (centralPhysicalFiniteCarrierSize w hw cutoff half)
          (finiteUpperPenalizedMatrix q
            (centralPhysicalFiniteWeight w hw cutoff half)
            (centralPhysicalFiniteKernel w hw cutoff half))
          coefficient
  lowerNonnegative :
    ∀ coefficient : Nat → Q',
      (0 : Q') ≤
        finiteMatrixQuadratic
          (centralPhysicalFiniteCarrierSize w hw cutoff half)
          (finiteLowerPenalizedMatrix q
            (centralPhysicalFiniteWeight w hw cutoff half)
            (centralPhysicalFiniteKernel w hw cutoff half))
          coefficient

namespace CentralPhysicalTwoSidedPSDCertificate

/-- Two canonical physical PSD forms imply the exact absolute centered
correlation estimate at the same cutoff. -/
theorem meanZeroGap
    {w : Q'} {hw : (0 : Q') ≤ w} {cutoff half : Nat} {q : Q'}
    (certificate :
      CentralPhysicalTwoSidedPSDCertificate w hw cutoff half q)
    (observable : EdgeLabelling → Q')
    (hcenter :
      CentralPhysicalMeanZero w hw cutoff half observable) :
    Q'.abs
        (centralPhysicalJointQuadratic
          w hw cutoff half observable) ≤
      q * centralPhysicalWeightedInner
        w hw cutoff half observable observable := by
  let n := centralPhysicalFiniteCarrierSize w hw cutoff half
  let weight := centralPhysicalFiniteWeight w hw cutoff half
  let kernel := centralPhysicalFiniteKernel w hw cutoff half
  let coefficient :=
    centralPhysicalFiniteCoefficient w hw cutoff half observable
  have hindexed :
      Q'.abs (finiteMatrixQuadratic n kernel coefficient) ≤
        q * finiteDiagonalQuadratic n weight coefficient := by
    exact finiteReversibleAbsContraction_of_two_matrix_nonnegative
      (certificate.upperNonnegative coefficient)
      (finiteUpperPenalizedMatrix_identify
        n q weight kernel coefficient)
      (certificate.lowerNonnegative coefficient)
      (finiteLowerPenalizedMatrix_identify
        n q weight kernel coefficient)
      (centralPhysicalFiniteCoefficient_centered hcenter)
  have hleft :
      Q'.abs (finiteMatrixQuadratic n kernel coefficient) ≈
        Q'.abs
          (centralPhysicalJointQuadratic
            w hw cutoff half observable) :=
    Q'.abs_eqv_congr
      (centralPhysicalFiniteMatrixQuadratic_eqv_jointQuadratic
        w hw cutoff half observable)
  have hright :
      q * finiteDiagonalQuadratic n weight coefficient ≈
        q * centralPhysicalWeightedInner
          w hw cutoff half observable observable :=
    Q'.mul_eqv_congr_left q _ _
      (centralPhysicalFiniteDiagonalQuadratic_eqv_weightedInner
        w hw cutoff half observable)
  exact le_of_eqv_le (Q'.eqv_symm hleft)
    (le_of_le_eqv hindexed hright)

end CentralPhysicalTwoSidedPSDCertificate

/-! ## 2. Executable ordinary and cleared-denominator LDL interfaces -/

/-- Literal full rational LDL checks for both canonical matrices at one
physical cutoff. -/
structure CentralPhysicalTwoSidedLDLCertificate
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat) (q : Q') : Type 1 where
  upperLower : Nat → Nat → Q'
  upperDiagonal : Nat → Q'
  upperCheck :
    finiteLDLCheck
      (centralPhysicalFiniteCarrierSize w hw cutoff half)
      (finiteUpperPenalizedMatrix q
        (centralPhysicalFiniteWeight w hw cutoff half)
        (centralPhysicalFiniteKernel w hw cutoff half))
      upperLower upperDiagonal = true
  lowerLower : Nat → Nat → Q'
  lowerDiagonal : Nat → Q'
  lowerCheck :
    finiteLDLCheck
      (centralPhysicalFiniteCarrierSize w hw cutoff half)
      (finiteLowerPenalizedMatrix q
        (centralPhysicalFiniteWeight w hw cutoff half)
        (centralPhysicalFiniteKernel w hw cutoff half))
      lowerLower lowerDiagonal = true

namespace CentralPhysicalTwoSidedLDLCertificate

/-- Soundness of the two full Boolean LDL checks. -/
def toPSD
    {w : Q'} {hw : (0 : Q') ≤ w} {cutoff half : Nat} {q : Q'}
    (certificate :
      CentralPhysicalTwoSidedLDLCertificate w hw cutoff half q) :
    CentralPhysicalTwoSidedPSDCertificate w hw cutoff half q where
  upperNonnegative := fun coefficient =>
    finiteMatrixQuadratic_nonnegative_of_ldl_check
      certificate.upperCheck coefficient
  lowerNonnegative := fun coefficient =>
    finiteMatrixQuadratic_nonnegative_of_ldl_check
      certificate.lowerCheck coefficient

theorem meanZeroGap
    {w : Q'} {hw : (0 : Q') ≤ w} {cutoff half : Nat} {q : Q'}
    (certificate :
      CentralPhysicalTwoSidedLDLCertificate w hw cutoff half q)
    (observable : EdgeLabelling → Q')
    (hcenter : CentralPhysicalMeanZero w hw cutoff half observable) :
    Q'.abs
        (centralPhysicalJointQuadratic
          w hw cutoff half observable) ≤
      q * centralPhysicalWeightedInner
        w hw cutoff half observable observable :=
  certificate.toPSD.meanZeroGap observable hcenter

end CentralPhysicalTwoSidedLDLCertificate

/-- Cleared-denominator row checks, triangularity witnesses, and pivot checks
for both canonical matrices.  This separates large row computations so they
can be kernel-checked in independent shards. -/
structure CentralPhysicalTwoSidedClearedLDLCertificate
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat) (q : Q') : Type 1 where
  upperLower : Nat → Nat → Q'
  upperDiagonal : Nat → Q'
  upperCommon : Nat → Nat → Nat
  upperRowsCheck :
    finiteLDLClearedRowsCheck
      (centralPhysicalFiniteCarrierSize w hw cutoff half)
      (finiteUpperPenalizedMatrix q
        (centralPhysicalFiniteWeight w hw cutoff half)
        (centralPhysicalFiniteKernel w hw cutoff half))
      upperLower upperDiagonal upperCommon = true
  upperTriangular : ∀ i k, i < k → upperLower i k = 0
  upperDiagonalCheck :
    finiteLDLDiagonalCheck
      (centralPhysicalFiniteCarrierSize w hw cutoff half)
      upperDiagonal = true
  lowerLower : Nat → Nat → Q'
  lowerDiagonal : Nat → Q'
  lowerCommon : Nat → Nat → Nat
  lowerRowsCheck :
    finiteLDLClearedRowsCheck
      (centralPhysicalFiniteCarrierSize w hw cutoff half)
      (finiteLowerPenalizedMatrix q
        (centralPhysicalFiniteWeight w hw cutoff half)
        (centralPhysicalFiniteKernel w hw cutoff half))
      lowerLower lowerDiagonal lowerCommon = true
  lowerTriangular : ∀ i k, i < k → lowerLower i k = 0
  lowerDiagonalCheck :
    finiteLDLDiagonalCheck
      (centralPhysicalFiniteCarrierSize w hw cutoff half)
      lowerDiagonal = true

namespace CentralPhysicalTwoSidedClearedLDLCertificate

/-- Soundness of the two independently shardable cleared LDL checks. -/
def toPSD
    {w : Q'} {hw : (0 : Q') ≤ w} {cutoff half : Nat} {q : Q'}
    (certificate :
      CentralPhysicalTwoSidedClearedLDLCertificate
        w hw cutoff half q) :
    CentralPhysicalTwoSidedPSDCertificate w hw cutoff half q where
  upperNonnegative := fun coefficient =>
    finiteMatrixQuadratic_nonnegative_of_cleared_ldl_check
      certificate.upperRowsCheck certificate.upperTriangular
      certificate.upperDiagonalCheck coefficient
  lowerNonnegative := fun coefficient =>
    finiteMatrixQuadratic_nonnegative_of_cleared_ldl_check
      certificate.lowerRowsCheck certificate.lowerTriangular
      certificate.lowerDiagonalCheck coefficient

theorem meanZeroGap
    {w : Q'} {hw : (0 : Q') ≤ w} {cutoff half : Nat} {q : Q'}
    (certificate :
      CentralPhysicalTwoSidedClearedLDLCertificate
        w hw cutoff half q)
    (observable : EdgeLabelling → Q')
    (hcenter : CentralPhysicalMeanZero w hw cutoff half observable) :
    Q'.abs
        (centralPhysicalJointQuadratic
          w hw cutoff half observable) ≤
      q * centralPhysicalWeightedInner
        w hw cutoff half observable observable :=
  certificate.toPSD.meanZeroGap observable hcenter

end CentralPhysicalTwoSidedClearedLDLCertificate

/-! ## 3. Cofinal-family contraction -/

/-- A constructively cofinal family of canonical two-sided PSD certificates
at the fixed physical rate `1/16`. -/
structure FixedNomeCofinalTwoSidedPSD
    (w : Q') (hw : (0 : Q') ≤ w) (half : Nat) : Type 1 where
  anchor : Nat → Nat
  anchor_ge : ∀ base, base ≤ anchor base
  certificate :
    ∀ base,
      CentralPhysicalTwoSidedPSDCertificate
        w hw (anchor base) half physicalCutoffSixteenth

namespace FixedNomeCofinalTwoSidedPSD

/-- A cofinal family of canonical two-sided PSD forms supplies exactly the
finite input required by the completed fixed-nome gap route. -/
def toCenteredSixteenth
    {w : Q'} {hw : (0 : Q') ≤ w} {half : Nat}
    (certificate : FixedNomeCofinalTwoSidedPSD w hw half) :
    FixedNomeCofinalCenteredSixteenth w hw half where
  anchor := certificate.anchor
  anchor_ge := certificate.anchor_ge
  meanZeroGap := by
    intro base observable hcenter
    exact (certificate.certificate base).meanZeroGap observable hcenter

end FixedNomeCofinalTwoSidedPSD

/-- A cofinal family of full rational LDL checks for both canonical matrices. -/
structure FixedNomeCofinalTwoSidedLDL
    (w : Q') (hw : (0 : Q') ≤ w) (half : Nat) : Type 1 where
  anchor : Nat → Nat
  anchor_ge : ∀ base, base ≤ anchor base
  certificate :
    ∀ base,
      CentralPhysicalTwoSidedLDLCertificate
        w hw (anchor base) half physicalCutoffSixteenth

namespace FixedNomeCofinalTwoSidedLDL

def toPSD
    {w : Q'} {hw : (0 : Q') ≤ w} {half : Nat}
    (certificate : FixedNomeCofinalTwoSidedLDL w hw half) :
    FixedNomeCofinalTwoSidedPSD w hw half where
  anchor := certificate.anchor
  anchor_ge := certificate.anchor_ge
  certificate := fun base => (certificate.certificate base).toPSD

/-- Successful full LDL checks along a cofinal cutoff sequence compile to the
fixed-nome cofinal centered sixteenth. -/
def toCenteredSixteenth
    {w : Q'} {hw : (0 : Q') ≤ w} {half : Nat}
    (certificate : FixedNomeCofinalTwoSidedLDL w hw half) :
    FixedNomeCofinalCenteredSixteenth w hw half :=
  certificate.toPSD.toCenteredSixteenth

end FixedNomeCofinalTwoSidedLDL

/-- A cofinal family of shardable cleared-denominator LDL checks for both
canonical matrices. -/
structure FixedNomeCofinalTwoSidedClearedLDL
    (w : Q') (hw : (0 : Q') ≤ w) (half : Nat) : Type 1 where
  anchor : Nat → Nat
  anchor_ge : ∀ base, base ≤ anchor base
  certificate :
    ∀ base,
      CentralPhysicalTwoSidedClearedLDLCertificate
        w hw (anchor base) half physicalCutoffSixteenth

namespace FixedNomeCofinalTwoSidedClearedLDL

def toPSD
    {w : Q'} {hw : (0 : Q') ≤ w} {half : Nat}
    (certificate : FixedNomeCofinalTwoSidedClearedLDL w hw half) :
    FixedNomeCofinalTwoSidedPSD w hw half where
  anchor := certificate.anchor
  anchor_ge := certificate.anchor_ge
  certificate := fun base => (certificate.certificate base).toPSD

/-- Successful shardable cleared LDL checks along a cofinal cutoff sequence
compile to the fixed-nome cofinal centered sixteenth. -/
def toCenteredSixteenth
    {w : Q'} {hw : (0 : Q') ≤ w} {half : Nat}
    (certificate : FixedNomeCofinalTwoSidedClearedLDL w hw half) :
    FixedNomeCofinalCenteredSixteenth w hw half :=
  certificate.toPSD.toCenteredSixteenth

end FixedNomeCofinalTwoSidedClearedLDL

end YMGap.Continuum.BF4PhysicalCutoffCofinalLDLGap

#print axioms
  YMGap.Continuum.BF4PhysicalCutoffCofinalLDLGap.CentralPhysicalTwoSidedPSDCertificate.meanZeroGap
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffCofinalLDLGap.CentralPhysicalTwoSidedLDLCertificate.toPSD
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffCofinalLDLGap.CentralPhysicalTwoSidedClearedLDLCertificate.toPSD
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffCofinalLDLGap.FixedNomeCofinalTwoSidedLDL.toCenteredSixteenth
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffCofinalLDLGap.FixedNomeCofinalTwoSidedClearedLDL.toCenteredSixteenth
