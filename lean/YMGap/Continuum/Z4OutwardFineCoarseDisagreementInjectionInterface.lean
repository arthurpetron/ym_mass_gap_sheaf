/-
# Injection interface for the outward query-disagreement residual

This module exposes the exact constructive data needed to dominate the
fine/coarse query-disagreement numerator by the fine pattern numerator.  A
certificate supplies a deterministic map on compatible surface families,
proves target-event membership, proves injectivity on the filtered source,
and pays a pointwise rational activity cost.  The finite weighted-injection
theorem then gives the required relative numerator estimate with no counting
multiplicity hidden in prose.

The six-face small-lift witness also gives a sharp fence on one tempting map:
an identity image of that positive-weight disagreement family necessarily has
cost at least one.  Thus any genuinely small bound must use aggregate slack or
a different, explicitly weight-improving surgery.
-/

import YMGap.Continuum.FiniteDeterministicKernelPushforward
import YMGap.Continuum.FiniteWeightedCartesianInjection
import YMGap.Continuum.BakryEmery
import YMGap.Continuum.Z4OutwardChildQueryDisagreementWitness

namespace YMGap.Continuum.Z4OutwardFineCoarseDisagreementInjectionInterface

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BakryEmery
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CanonicalPolymerRange
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CouplingParametricSpinSummedCoarseOccurrenceFloor
open YMGap.Continuum.Z4CouplingParametricSpinSummedEventBridge
open YMGap.Continuum.Z4CouplingParametricSpinSummedPinnedLayer
open YMGap.Continuum.Z4CouplingParametricSpinSummedSupportFactorization
open YMGap.Continuum.Z4OutwardChildQueryDisagreementWitness
open YMGap.Continuum.Z4OutwardChildQuerySmallLiftWitness
open YMGap.Continuum.Z4OutwardFineCoarseSupportGasCrossDifference
open YMGap.Continuum.Z4OutwardFineCoarseSupportGasErrorSplit
open YMGap.Continuum.Z4OutwardFineCoarseSupportGasEventDifference
open YMGap.Continuum.Z4OutwardThreeCubeFineSubsupportPatterns
open YMGap.Continuum.Z4OutwardThreeCubeFullRootQueries
open YMGap.Continuum.Z4OutwardThreeCubeSubsupportPatterns
open YMGap.Continuum.Z4ThreeBlockFiberConditionalKernel

local infix:50 " ≈ " => Q'.eqv

def outwardPatternDisagreementFamilies
    (pattern : ThreeBlockPattern) : List (List (List Nat)) :=
  (canonicalCompatibleAmbientFamilies 6).filter
    (supportEventDisagreement
      (outwardComponentSubsupportFamilyPatternEvent
        outwardCoarseQueries pattern)
      (outwardComponentSubsupportFamilyPatternEvent
        outwardFineQueries pattern))

def outwardFinePatternFamilies
    (pattern : ThreeBlockPattern) : List (List (List Nat)) :=
  (canonicalCompatibleAmbientFamilies 6).filter
    (outwardComponentSubsupportFamilyPatternEvent
      outwardFineQueries pattern)

def outwardFineFamilyWeight (fineCoupling : Q') :
    List (List Nat) → Q' :=
  couplingParametricKSupportFamilyActivity fineCoupling 1 6

theorem outwardPatternDisagreementFamilies_nodup
    (pattern : ThreeBlockPattern) :
    (outwardPatternDisagreementFamilies pattern).Nodup := by
  unfold outwardPatternDisagreementFamilies
  exact List.filter_sublist.nodup
    (canonicalCompatibleAmbientFamilies_nodup 6)

theorem outwardFinePatternFamilies_nodup
    (pattern : ThreeBlockPattern) :
    (outwardFinePatternFamilies pattern).Nodup := by
  unfold outwardFinePatternFamilies
  exact List.filter_sublist.nodup
    (canonicalCompatibleAmbientFamilies_nodup 6)

theorem outwardGeometryDisagreementNumerator_eq_listQSum
    (fineCoupling : Q') (pattern : ThreeBlockPattern) :
    outwardFineCoarseGeometryDisagreementNumerator fineCoupling pattern =
      listQSum (outwardFineFamilyWeight fineCoupling)
        (outwardPatternDisagreementFamilies pattern) := by
  unfold outwardFineCoarseGeometryDisagreementNumerator
    couplingParametricKCompatibleSupportEventNumerator
    outwardFineFamilyWeight outwardPatternDisagreementFamilies
  exact Eq.refl _

theorem outwardFinePatternNumerator_eq_listQSum
    (fineCoupling : Q') (pattern : ThreeBlockPattern) :
    outwardFineCompatibleSupportPatternNumerator fineCoupling pattern =
      listQSum (outwardFineFamilyWeight fineCoupling)
        (outwardFinePatternFamilies pattern) := by
  unfold outwardFineCompatibleSupportPatternNumerator
    outwardCompatibleSupportPatternNumerator
    couplingParametricKCompatibleSupportEventNumerator
    outwardFineFamilyWeight outwardFinePatternFamilies
  exact Eq.refl _

/-- Concrete data for a multiplicity-controlled disagreement-to-fine-event
map at one pattern.  `term_le` is the complete spin-summed family-weight cost,
not a surrogate face count. -/
structure OutwardPatternDisagreementInjectionCertificate
    (fineCoupling bound : Q') (pattern : ThreeBlockPattern) where
  encode : List (List Nat) → List (List Nat)
  map_mem : ∀ family,
    family ∈ outwardPatternDisagreementFamilies pattern →
      encode family ∈ outwardFinePatternFamilies pattern
  injective_on : ∀ left,
    left ∈ outwardPatternDisagreementFamilies pattern →
      ∀ right,
      right ∈ outwardPatternDisagreementFamilies pattern →
        encode left = encode right → left = right
  term_le : ∀ family,
    family ∈ outwardPatternDisagreementFamilies pattern →
      outwardFineFamilyWeight fineCoupling family ≤
        bound * outwardFineFamilyWeight fineCoupling (encode family)

/-- The certificate fields discharge exactly the finite weighted-injection
estimate, including source multiplicity and the explicit target cost. -/
theorem outwardGeometryDisagreementNumerator_le_of_injection
    {fineCoupling bound : Q'}
    (hfine : (0 : Q') ≤ fineCoupling)
    (hbound : (0 : Q') ≤ bound)
    (pattern : ThreeBlockPattern)
    (certificate : OutwardPatternDisagreementInjectionCertificate
      fineCoupling bound pattern) :
    outwardFineCoarseGeometryDisagreementNumerator
        fineCoupling pattern ≤
      bound * outwardFineCompatibleSupportPatternNumerator
        fineCoupling pattern := by
  rw [outwardGeometryDisagreementNumerator_eq_listQSum,
    outwardFinePatternNumerator_eq_listQSum]
  have hinjection := listQSum_le_of_injective
    (outwardPatternDisagreementFamilies pattern)
    (outwardFinePatternFamilies pattern)
    (outwardFineFamilyWeight fineCoupling)
    (fun family => bound * outwardFineFamilyWeight fineCoupling family)
    certificate.encode
    (outwardPatternDisagreementFamilies_nodup pattern)
    certificate.map_mem
    certificate.injective_on
    certificate.term_le
    (fun family _ =>
      Q'.mul_nonneg _ _ hbound
        (couplingParametricKSupportFamilyActivity_nonnegative
          hfine 1 6 family))
  exact Q'.le_trans' _ _ _ hinjection
    (Q'.le_of_eqv
      (listQSum_mul_left bound
        (outwardFineFamilyWeight fineCoupling)
        (outwardFinePatternFamilies pattern)))

def OutwardAllPatternDisagreementInjectionCertificates
    (fineCoupling bound : Q') : Type :=
  ∀ pattern : ThreeBlockPattern,
    OutwardPatternDisagreementInjectionCertificate
      fineCoupling bound pattern

theorem outwardFineCoarseGeometryDisagreementBound_of_injections
    {fineCoupling bound : Q'}
    (hfine : (0 : Q') ≤ fineCoupling)
    (hbound : (0 : Q') ≤ bound)
    (certificates : OutwardAllPatternDisagreementInjectionCertificates
      fineCoupling bound) :
    OutwardFineCoarseGeometryDisagreementBound
      fineCoupling bound := by
  intro pattern
  exact outwardGeometryDisagreementNumerator_le_of_injection
    hfine hbound pattern (certificates pattern)

theorem outwardFineCoarseSupportGeometryBound_of_injections
    {fineCoupling bound : Q'}
    (hfine : (0 : Q') ≤ fineCoupling)
    (hbound : (0 : Q') ≤ bound)
    (certificates : OutwardAllPatternDisagreementInjectionCertificates
      fineCoupling bound) :
    OutwardFineCoarseSupportGeometryCrossDifferenceBound
      fineCoupling bound :=
  outwardFineCoarseSupportGeometryBound_of_disagreement
    fineCoupling hfine bound
    (outwardFineCoarseGeometryDisagreementBound_of_injections
      hfine hbound certificates)

/-! ## Identity-image obstruction at the six-face witness -/

theorem outwardXFineSmallLift_spinSummedFamilyWeight_pos
    {fineCoupling : Q'} (hfine : (0 : Q') < fineCoupling) :
    (0 : Q') < outwardFineFamilyWeight fineCoupling
      [outwardXFineSmallLiftRoot] := by
  have hsupport := canonicalSurfacePolymer_mem_faceSupports
    outwardXFineSmallLiftRoot_mem_canonical
  have hrootSupport :=
    canonicalSurfaceActivity_le_couplingParametricKSupportActivity
      (Q'.le_of_lt hfine) (cutoff := 1) (n := 6)
      (by decide) hsupport
  have hsupportPos : (0 : Q') <
      couplingParametricKSupportActivity fineCoupling 1 6
        outwardXFineSmallLiftRoot :=
    Q'.pos_of_lt_of_le
      (outwardXFineSmallLiftRoot_activity_pos hfine)
      hrootSupport
  unfold outwardFineFamilyWeight
    couplingParametricKSupportFamilyActivity
  exact Q'.pos_of_lt_of_le hsupportPos
    (Q'.ge_of_eqv
      (Q'.mul_one_eqv
        (couplingParametricKSupportActivity fineCoupling 1 6
          outwardXFineSmallLiftRoot)))

/-- A termwise certificate that sends the positive six-face XOR witness to
itself cannot carry a coefficient below one.  This is the exact fence around
the naive identity branch of an XOR-to-fine injection. -/
theorem smallLift_identity_term_cost_forces_one_le
    {fineCoupling bound : Q'} (hfine : (0 : Q') < fineCoupling)
    (hcost : outwardFineFamilyWeight fineCoupling
        [outwardXFineSmallLiftRoot] ≤
      bound * outwardFineFamilyWeight fineCoupling
        [outwardXFineSmallLiftRoot]) :
    (1 : Q') ≤ bound := by
  let weight := outwardFineFamilyWeight fineCoupling
    [outwardXFineSmallLiftRoot]
  have hweight : (0 : Q') < weight :=
    outwardXFineSmallLift_spinSummedFamilyWeight_pos hfine
  have hone : (1 : Q') * weight ≤ weight :=
    Q'.le_of_eqv (Q'.one_mul_eqv weight)
  have hscaled : (1 : Q') * weight ≤ bound * weight :=
    Q'.le_trans' _ _ _ hone hcost
  exact le_of_mul_le_mul_right_pos hweight hscaled

#print axioms outwardGeometryDisagreementNumerator_eq_listQSum
#print axioms outwardFinePatternNumerator_eq_listQSum
#print axioms outwardGeometryDisagreementNumerator_le_of_injection
#print axioms outwardFineCoarseGeometryDisagreementBound_of_injections
#print axioms outwardFineCoarseSupportGeometryBound_of_injections
#print axioms outwardXFineSmallLift_spinSummedFamilyWeight_pos
#print axioms smallLift_identity_term_cost_forces_one_le

end YMGap.Continuum.Z4OutwardFineCoarseDisagreementInjectionInterface
