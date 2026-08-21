/-
# Canonical head-reduced LDL compiler for the physical BF4 gap

The genuine finite BF4 carrier is the nonempty list of exactly those rows with
positive stationary marginal.  Hence its first indexed weight is strictly
positive.  This module uses that proved fact to instantiate the canonical
positive-head centered pullback at every physical cutoff.

Ordinary or cleared LDL checks are consequently pinned to literal generated
reduced matrices, not to an abstract restriction or externally asserted
matrix identity.  Cofinal families of those checks compile to the existing
fixed-nome centered-sixteenth interface.

No LDL table, cofinal family, thermodynamic limit, continuum theory, or Clay
conclusion is constructed here.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalCutoffCofinalRestrictedLDLGap
import YMGap.Continuum.FiniteRationalHeadCenteredPullback

namespace YMGap.Continuum.BF4PhysicalCutoffCanonicalHeadLDLGap

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffCofinalConnectedGap
open YMGap.Continuum.BF4PhysicalCutoffConnectedGap
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffCofinalRestrictedLDLGap
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4WeightedJointPerronPerturbation
open YMGap.Continuum.FiniteListIndexQuadraticBridge
open YMGap.Continuum.FiniteRationalCenteredRestrictionCertificate
open YMGap.Continuum.FiniteRationalHeadCenteredPullback
open YMGap.Continuum.FiniteRationalLDLCertificate
open YMGap.Continuum.FiniteRationalReversibleSpectralCertificate
open YMGap.Continuum.OSReconstructionProgress
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The physical positive head and canonical restriction -/

/-- Indexed weight zero is strictly positive because the carrier is nonempty
and every retained state is retained exactly by a positive-row filter. -/
theorem centralPhysicalFiniteWeight_zero_pos
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat) :
    (0 : Q') < centralPhysicalFiniteWeight w hw cutoff half 0 := by
  have hne := centralPositiveHalfStates_ne_nil w hw cutoff half
  unfold centralPhysicalFiniteWeight centralPhysicalFiniteStateAt
    finiteListStateAt
  generalize hstates :
      centralPositiveHalfStates w hw cutoff half = states at hne ⊢
  cases states with
  | nil => exact False.elim (hne rfl)
  | cons head tail =>
      simp only [List.getD_cons_zero]
      have hmem :
          head ∈ centralPositiveHalfStates w hw cutoff half := by
        rw [hstates]
        exact List.mem_cons_self
      exact (mem_centralPositiveHalfStates_iff.mp hmem).2

/-- The positive physical carrier size is its predecessor plus one. -/
theorem centralPhysicalFiniteCarrierSize_pred_succ
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat) :
    centralPhysicalFiniteCarrierSize w hw cutoff half - 1 + 1 =
      centralPhysicalFiniteCarrierSize w hw cutoff half := by
  apply Nat.sub_add_cancel
  exact Nat.succ_le_iff.mpr
    (centralPositiveHalfStates_length_pos w hw cutoff half)

/-- The genuine physical carrier equipped with its completely generated
positive-head centered restriction and canonical reduced upper/lower
penalized matrices. -/
def centralPhysicalCanonicalHeadRestriction
    (w : Q') (hw : (0 : Q') ≤ w)
    (cutoff half : Nat) (q : Q') :
    FiniteCenteredTwoSidedRestriction
      (centralPhysicalFiniteCarrierSize w hw cutoff half)
      q
      (centralPhysicalFiniteWeight w hw cutoff half)
      (centralPhysicalFiniteKernel w hw cutoff half) := by
  let n := centralPhysicalFiniteCarrierSize w hw cutoff half - 1
  have hsize :
      n + 1 = centralPhysicalFiniteCarrierSize w hw cutoff half :=
    centralPhysicalFiniteCarrierSize_pred_succ w hw cutoff half
  rw [← hsize]
  exact finiteCanonicalHeadCenteredRestriction
    n q
    (centralPhysicalFiniteWeight w hw cutoff half)
    (centralPhysicalFiniteKernel w hw cutoff half)
    (centralPhysicalFiniteWeight_zero_pos w hw cutoff half)

/-! ## 2. LDL checks pinned to the generated physical restriction -/

/-- Ordinary LDL checks of the two generated reduced physical matrices. -/
abbrev CentralPhysicalCanonicalHeadLDLCertificate
    (w : Q') (hw : (0 : Q') ≤ w)
    (cutoff half : Nat) (q : Q') : Type 1 :=
  FiniteCenteredRestrictionLDLCertificate
    (centralPhysicalCanonicalHeadRestriction w hw cutoff half q)

/-- Cleared-denominator LDL checks of the two generated reduced physical
matrices. -/
abbrev CentralPhysicalCanonicalHeadClearedLDLCertificate
    (w : Q') (hw : (0 : Q') ≤ w)
    (cutoff half : Nat) (q : Q') : Type 1 :=
  FiniteCenteredRestrictionClearedLDLCertificate
    (centralPhysicalCanonicalHeadRestriction w hw cutoff half q)

namespace CentralPhysicalCanonicalHeadLDLCertificate

/-- Soundness of ordinary LDL checks pinned to the canonical physical
head-reduced matrices. -/
theorem meanZeroGap
    {w : Q'} {hw : (0 : Q') ≤ w}
    {cutoff half : Nat} {q : Q'}
    (certificate :
      CentralPhysicalCanonicalHeadLDLCertificate
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
      certificate.absContraction coefficient hcoefficient)
    observable hcenter

end CentralPhysicalCanonicalHeadLDLCertificate

namespace CentralPhysicalCanonicalHeadClearedLDLCertificate

/-- Soundness of cleared LDL checks pinned to the canonical physical
head-reduced matrices. -/
theorem meanZeroGap
    {w : Q'} {hw : (0 : Q') ≤ w}
    {cutoff half : Nat} {q : Q'}
    (certificate :
      CentralPhysicalCanonicalHeadClearedLDLCertificate
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
      certificate.absContraction coefficient hcoefficient)
    observable hcenter

end CentralPhysicalCanonicalHeadClearedLDLCertificate

/-! ## 3. Cofinal canonical certificate families -/

/-- Ordinary LDL checks pinned to the canonical physical head restriction at
every anchor of a constructively cofinal cutoff schedule. -/
abbrev FixedNomeCofinalCanonicalHeadLDL
    (w : Q') (hw : (0 : Q') ≤ w) (half : Nat) : Type 1 :=
  CofinalFixedCenteredRestrictionLDLCertificate
    physicalCutoffSixteenth
    (fun cutoff => centralPhysicalFiniteCarrierSize w hw cutoff half)
    (fun cutoff => centralPhysicalFiniteWeight w hw cutoff half)
    (fun cutoff => centralPhysicalFiniteKernel w hw cutoff half)
    (fun cutoff => centralPhysicalCanonicalHeadRestriction
      w hw cutoff half physicalCutoffSixteenth)

namespace FixedNomeCofinalCanonicalHeadLDL

/-- A cofinal family of ordinary checks of the generated matrices supplies the
exact fixed-nome centered sixteenth. -/
def toCenteredSixteenth
    {w : Q'} {hw : (0 : Q') ≤ w} {half : Nat}
    (certificate : FixedNomeCofinalCanonicalHeadLDL w hw half) :
    FixedNomeCofinalCenteredSixteenth w hw half where
  anchor := certificate.anchor
  anchor_ge := certificate.anchor_ge
  meanZeroGap := by
    intro base observable hcenter
    exact centralPhysicalMeanZeroGap_of_finiteCenteredGap
      (fun coefficient hcoefficient =>
        (certificate.certificate base).absContraction
          coefficient hcoefficient)
      observable hcenter

end FixedNomeCofinalCanonicalHeadLDL

/-- Cleared LDL checks pinned to the canonical physical head restriction at
every anchor of a constructively cofinal cutoff schedule. -/
abbrev FixedNomeCofinalCanonicalHeadClearedLDL
    (w : Q') (hw : (0 : Q') ≤ w) (half : Nat) : Type 1 :=
  CofinalFixedCenteredRestrictionClearedLDLCertificate
    physicalCutoffSixteenth
    (fun cutoff => centralPhysicalFiniteCarrierSize w hw cutoff half)
    (fun cutoff => centralPhysicalFiniteWeight w hw cutoff half)
    (fun cutoff => centralPhysicalFiniteKernel w hw cutoff half)
    (fun cutoff => centralPhysicalCanonicalHeadRestriction
      w hw cutoff half physicalCutoffSixteenth)

namespace FixedNomeCofinalCanonicalHeadClearedLDL

/-- A cofinal family of cleared checks of the generated matrices supplies the
exact fixed-nome centered sixteenth. -/
def toCenteredSixteenth
    {w : Q'} {hw : (0 : Q') ≤ w} {half : Nat}
    (certificate :
      FixedNomeCofinalCanonicalHeadClearedLDL w hw half) :
    FixedNomeCofinalCenteredSixteenth w hw half where
  anchor := certificate.anchor
  anchor_ge := certificate.anchor_ge
  meanZeroGap := by
    intro base observable hcenter
    exact centralPhysicalMeanZeroGap_of_finiteCenteredGap
      (fun coefficient hcoefficient =>
        (certificate.certificate base).absContraction
          coefficient hcoefficient)
      observable hcenter

end FixedNomeCofinalCanonicalHeadClearedLDL

end YMGap.Continuum.BF4PhysicalCutoffCanonicalHeadLDLGap

#print axioms
  YMGap.Continuum.BF4PhysicalCutoffCanonicalHeadLDLGap.centralPhysicalFiniteWeight_zero_pos
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffCanonicalHeadLDLGap.centralPhysicalCanonicalHeadRestriction
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffCanonicalHeadLDLGap.CentralPhysicalCanonicalHeadLDLCertificate.meanZeroGap
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffCanonicalHeadLDLGap.CentralPhysicalCanonicalHeadClearedLDLCertificate.meanZeroGap
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffCanonicalHeadLDLGap.FixedNomeCofinalCanonicalHeadLDL.toCenteredSixteenth
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffCanonicalHeadLDLGap.FixedNomeCofinalCanonicalHeadClearedLDL.toCenteredSixteenth
