/-
# Reduced-coordinate LDL compiler for the cofinal physical BF4 gap

Finite centered computations usually eliminate one stationary-mean
coordinate before factorization.  This module specializes the constructive
restriction interface to the genuine finite BF4 physical carrier.  It then
compiles ordinary or cleared-denominator LDL checks of the two reduced
penalized matrices into the exact physical mean-zero gap and, along a
constructively cofinal cutoff family, into
`FixedNomeCofinalCenteredSixteenth`.

The records below are certificate interfaces, not inhabitants.  No physical
restriction, LDL table, cofinal family, thermodynamic limit, continuum theory,
or Clay conclusion is constructed here.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalCutoffCofinalLDLGap
import YMGap.Continuum.FiniteRationalCenteredRestrictionCertificate

namespace YMGap.Continuum.BF4PhysicalCutoffCofinalRestrictedLDLGap

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffCofinalConnectedGap
open YMGap.Continuum.BF4PhysicalCutoffConnectedGap
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffCofinalLDLGap
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4WeightedJointPerronPerturbation
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteRationalCenteredRestrictionCertificate
open YMGap.Continuum.FiniteRationalLDLCertificate
open YMGap.Continuum.FiniteRationalReversibleSpectralCertificate
open YMGap.Continuum.OSReconstructionProgress
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The genuine physical centered restriction -/

/-- A reduced coordinate realization of every exactly centered vector on the
genuine indexed physical carrier at one cutoff. -/
abbrev CentralPhysicalCenteredTwoSidedRestriction
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat) (q : Q') : Type 1 :=
  FiniteCenteredTwoSidedRestriction
    (centralPhysicalFiniteCarrierSize w hw cutoff half)
    q
    (centralPhysicalFiniteWeight w hw cutoff half)
    (centralPhysicalFiniteKernel w hw cutoff half)

/-- Transport an exact absolute centered inequality on the indexed physical
carrier back to the genuine physical list sums. -/
theorem centralPhysicalMeanZeroGap_of_finiteCenteredGap
    {w : Q'} {hw : (0 : Q') ≤ w} {cutoff half : Nat} {q : Q'}
    (hfinite :
      ∀ coefficient : Nat → Q',
        finiteWeightedMean
            (centralPhysicalFiniteCarrierSize w hw cutoff half)
            (centralPhysicalFiniteWeight w hw cutoff half)
            coefficient ≈ 0 →
          Q'.abs
              (finiteMatrixQuadratic
                (centralPhysicalFiniteCarrierSize w hw cutoff half)
                (centralPhysicalFiniteKernel w hw cutoff half)
                coefficient) ≤
            q * finiteDiagonalQuadratic
              (centralPhysicalFiniteCarrierSize w hw cutoff half)
              (centralPhysicalFiniteWeight w hw cutoff half)
              coefficient)
    (observable : EdgeLabelling → Q')
    (hcenter : CentralPhysicalMeanZero w hw cutoff half observable) :
    Q'.abs
        (centralPhysicalJointQuadratic
          w hw cutoff half observable) ≤
      q * centralPhysicalWeightedInner
        w hw cutoff half observable observable := by
  let coefficient :=
    centralPhysicalFiniteCoefficient w hw cutoff half observable
  have hindexed := hfinite coefficient
    (centralPhysicalFiniteCoefficient_centered hcenter)
  have hleft :
      Q'.abs
          (finiteMatrixQuadratic
            (centralPhysicalFiniteCarrierSize w hw cutoff half)
            (centralPhysicalFiniteKernel w hw cutoff half)
            coefficient) ≈
        Q'.abs
          (centralPhysicalJointQuadratic
            w hw cutoff half observable) :=
    Q'.abs_eqv_congr
      (centralPhysicalFiniteMatrixQuadratic_eqv_jointQuadratic
        w hw cutoff half observable)
  have hright :
      q * finiteDiagonalQuadratic
          (centralPhysicalFiniteCarrierSize w hw cutoff half)
          (centralPhysicalFiniteWeight w hw cutoff half)
          coefficient ≈
        q * centralPhysicalWeightedInner
          w hw cutoff half observable observable :=
    Q'.mul_eqv_congr_left q _ _
      (centralPhysicalFiniteDiagonalQuadratic_eqv_weightedInner
        w hw cutoff half observable)
  exact le_of_eqv_le (Q'.eqv_symm hleft)
    (le_of_le_eqv hindexed hright)

/-! ## 2. Executable reduced LDL interfaces -/

/-- One physical restriction together with complete ordinary LDL checks of
both reduced penalized matrices. -/
abbrev CentralPhysicalRestrictedLDLCertificate
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat) (q : Q') : Type 1 :=
  FiniteCenteredRestrictionLDLPackage
    (centralPhysicalFiniteCarrierSize w hw cutoff half)
    q
    (centralPhysicalFiniteWeight w hw cutoff half)
    (centralPhysicalFiniteKernel w hw cutoff half)

namespace CentralPhysicalRestrictedLDLCertificate

/-- Soundness of the ordinary reduced LDL checks on the physical carrier. -/
theorem meanZeroGap
    {w : Q'} {hw : (0 : Q') ≤ w} {cutoff half : Nat} {q : Q'}
    (physical :
      CentralPhysicalRestrictedLDLCertificate w hw cutoff half q)
    (observable : EdgeLabelling → Q')
    (hcenter : CentralPhysicalMeanZero w hw cutoff half observable) :
    Q'.abs
        (centralPhysicalJointQuadratic
          w hw cutoff half observable) ≤
      q * centralPhysicalWeightedInner
        w hw cutoff half observable observable :=
  centralPhysicalMeanZeroGap_of_finiteCenteredGap
    (fun coefficient hcoefficient =>
      physical.certificate.absContraction coefficient hcoefficient)
    observable hcenter

end CentralPhysicalRestrictedLDLCertificate

/-- One physical restriction together with shardable cleared-denominator LDL
checks of both reduced penalized matrices. -/
abbrev CentralPhysicalRestrictedClearedLDLCertificate
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat) (q : Q') : Type 1 :=
  FiniteCenteredRestrictionClearedLDLPackage
    (centralPhysicalFiniteCarrierSize w hw cutoff half)
    q
    (centralPhysicalFiniteWeight w hw cutoff half)
    (centralPhysicalFiniteKernel w hw cutoff half)

namespace CentralPhysicalRestrictedClearedLDLCertificate

/-- Soundness of the cleared reduced LDL checks on the physical carrier. -/
theorem meanZeroGap
    {w : Q'} {hw : (0 : Q') ≤ w} {cutoff half : Nat} {q : Q'}
    (physical :
      CentralPhysicalRestrictedClearedLDLCertificate
        w hw cutoff half q)
    (observable : EdgeLabelling → Q')
    (hcenter : CentralPhysicalMeanZero w hw cutoff half observable) :
    Q'.abs
        (centralPhysicalJointQuadratic
          w hw cutoff half observable) ≤
      q * centralPhysicalWeightedInner
        w hw cutoff half observable observable :=
  centralPhysicalMeanZeroGap_of_finiteCenteredGap
    (fun coefficient hcoefficient =>
      physical.certificate.absContraction coefficient hcoefficient)
    observable hcenter

end CentralPhysicalRestrictedClearedLDLCertificate

/-! ## 3. Cofinal reduced-certificate families -/

/-- Ordinary reduced LDL certificates on a constructively cofinal sequence of
fixed-nome physical representation cutoffs. -/
abbrev FixedNomeCofinalRestrictedLDL
    (w : Q') (hw : (0 : Q') ≤ w) (half : Nat) : Type 1 :=
  CofinalFiniteCenteredRestrictionLDLPackage
    physicalCutoffSixteenth
    (fun cutoff => centralPhysicalFiniteCarrierSize w hw cutoff half)
    (fun cutoff => centralPhysicalFiniteWeight w hw cutoff half)
    (fun cutoff => centralPhysicalFiniteKernel w hw cutoff half)

namespace FixedNomeCofinalRestrictedLDL

/-- Cofinal ordinary reduced checks supply the exact finite input consumed by
the cutoff-removed completed-transfer gap route. -/
def toCenteredSixteenth
    {w : Q'} {hw : (0 : Q') ≤ w} {half : Nat}
    (physical : FixedNomeCofinalRestrictedLDL w hw half) :
    FixedNomeCofinalCenteredSixteenth w hw half where
  anchor := physical.anchor
  anchor_ge := physical.anchor_ge
  meanZeroGap := by
    intro base observable hcenter
    exact centralPhysicalMeanZeroGap_of_finiteCenteredGap
      (fun coefficient hcoefficient =>
        (physical.certificate base).absContraction
          coefficient hcoefficient)
      observable hcenter

end FixedNomeCofinalRestrictedLDL

/-- Cleared reduced LDL certificates on a constructively cofinal sequence of
fixed-nome physical representation cutoffs. -/
abbrev FixedNomeCofinalRestrictedClearedLDL
    (w : Q') (hw : (0 : Q') ≤ w) (half : Nat) : Type 1 :=
  CofinalFiniteCenteredRestrictionClearedLDLPackage
    physicalCutoffSixteenth
    (fun cutoff => centralPhysicalFiniteCarrierSize w hw cutoff half)
    (fun cutoff => centralPhysicalFiniteWeight w hw cutoff half)
    (fun cutoff => centralPhysicalFiniteKernel w hw cutoff half)

namespace FixedNomeCofinalRestrictedClearedLDL

/-- Cofinal shardable reduced checks supply the exact finite input consumed by
the cutoff-removed completed-transfer gap route. -/
def toCenteredSixteenth
    {w : Q'} {hw : (0 : Q') ≤ w} {half : Nat}
    (physical : FixedNomeCofinalRestrictedClearedLDL w hw half) :
    FixedNomeCofinalCenteredSixteenth w hw half where
  anchor := physical.anchor
  anchor_ge := physical.anchor_ge
  meanZeroGap := by
    intro base observable hcenter
    exact centralPhysicalMeanZeroGap_of_finiteCenteredGap
      (fun coefficient hcoefficient =>
        (physical.certificate base).absContraction
          coefficient hcoefficient)
      observable hcenter

end FixedNomeCofinalRestrictedClearedLDL

end YMGap.Continuum.BF4PhysicalCutoffCofinalRestrictedLDLGap

#print axioms
  YMGap.Continuum.BF4PhysicalCutoffCofinalRestrictedLDLGap.centralPhysicalMeanZeroGap_of_finiteCenteredGap
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffCofinalRestrictedLDLGap.CentralPhysicalRestrictedLDLCertificate.meanZeroGap
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffCofinalRestrictedLDLGap.CentralPhysicalRestrictedClearedLDLCertificate.meanZeroGap
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffCofinalRestrictedLDLGap.FixedNomeCofinalRestrictedLDL.toCenteredSixteenth
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffCofinalRestrictedLDLGap.FixedNomeCofinalRestrictedClearedLDL.toCenteredSixteenth
