/-
# Arbitrary-rate cofinal fixed-nome physical BF4 gap

The finite rational matrix and LDL layers already accept an arbitrary rate
`q`.  The previous cofinal physical interface nevertheless fixed that rate to
`1/16`.  The exact cutoff-two obstruction shows that such hardcoding is too
strong for the displayed finite sector.

This module exposes the actual strictness datum needed by the completed route:
a constructive rational rate `q` with `0 <= q < 1`, together with exact
mean-zero bounds on a constructively cofinal cutoff schedule.  It also pins
ordinary and cleared LDL families to the canonical positive-head matrices at
that same supplied rate.

No LDL table, cofinal family, thermodynamic limit, continuum theory, or Clay
conclusion is constructed here.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalCutoffCanonicalHeadLDLGap
import YMGap.Continuum.BF4PhysicalCompletedMacroCorrelator

namespace YMGap.Continuum.BF4PhysicalCutoffCofinalStrictGap

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffCanonicalHeadLDLGap
open YMGap.Continuum.BF4PhysicalCutoffCofinalConnectedGap
open YMGap.Continuum.BF4PhysicalCutoffConnectedGap
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffCofinalRestrictedLDLGap
open YMGap.Continuum.BF4PhysicalCompletedMacroCorrelator
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4WeightedJointPerronPerturbation
open YMGap.Continuum.FiniteRationalCenteredRestrictionCertificate
open YMGap.Continuum.FiniteRationalLDLCertificate
open YMGap.Continuum.FiniteRationalReversibleSpectralCertificate
open YMGap.Continuum.OSReconstructionProgress
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The arbitrary strict cofinal datum -/

/-- Exact physical mean-zero contraction at a supplied strict rational rate
on a constructively selected unbounded subsequence of representation
cutoffs. -/
structure FixedNomeCofinalCenteredStrictGap
    (w : Q') (hw : (0 : Q') <= w) (half : Nat) (q : Q') : Type 1 where
  rate_nonnegative : (0 : Q') <= q
  rate_lt_one : q < (1 : Q')
  anchor : Nat -> Nat
  anchor_ge : forall base, base <= anchor base
  meanZeroGap :
    forall base (observable : EdgeLabelling -> Q'),
      CentralPhysicalMeanZero w hw (anchor base) half observable ->
        Q'.abs
            (centralPhysicalJointQuadratic
              w hw (anchor base) half observable) <=
          q * centralPhysicalWeightedInner
            w hw (anchor base) half observable observable

namespace FixedNomeCofinalCenteredStrictGap

/-- The historical cofinal sixteenth is the special case `q = 1/16`. -/
def ofCenteredSixteenth
    {w : Q'} {hw : (0 : Q') <= w} {half : Nat}
    (certificate : FixedNomeCofinalCenteredSixteenth w hw half) :
    FixedNomeCofinalCenteredStrictGap
      w hw half physicalCutoffSixteenth where
  rate_nonnegative := physicalCutoffSixteenth_nonnegative
  rate_lt_one := physicalCutoffSixteenth_lt_one
  anchor := certificate.anchor
  anchor_ge := certificate.anchor_ge
  meanZeroGap := certificate.meanZeroGap

end FixedNomeCofinalCenteredStrictGap

/-! ## 2. Canonical ordinary LDL families at a supplied rate -/

/-- Ordinary LDL checks of the canonical positive-head matrices at an
arbitrary supplied rate along a constructively cofinal cutoff schedule. -/
abbrev FixedNomeCofinalCanonicalHeadLDLAtRate
    (w : Q') (hw : (0 : Q') <= w) (half : Nat) (q : Q') : Type 1 :=
  CofinalFixedCenteredRestrictionLDLCertificate
    q
    (fun cutoff => centralPhysicalFiniteCarrierSize w hw cutoff half)
    (fun cutoff => centralPhysicalFiniteWeight w hw cutoff half)
    (fun cutoff => centralPhysicalFiniteKernel w hw cutoff half)
    (fun cutoff => centralPhysicalCanonicalHeadRestriction
      w hw cutoff half q)

namespace FixedNomeCofinalCanonicalHeadLDLAtRate

/-- Canonical ordinary LDL checks at `q` compile to the arbitrary strict
cofinal physical interface once the two strict-rate inequalities are
supplied. -/
def toCenteredStrictGap
    {w : Q'} {hw : (0 : Q') <= w} {half : Nat} {q : Q'}
    (hq0 : (0 : Q') <= q) (hq1 : q < (1 : Q'))
    (certificate : FixedNomeCofinalCanonicalHeadLDLAtRate
      w hw half q) :
    FixedNomeCofinalCenteredStrictGap w hw half q where
  rate_nonnegative := hq0
  rate_lt_one := hq1
  anchor := certificate.anchor
  anchor_ge := certificate.anchor_ge
  meanZeroGap := by
    intro base observable hcenter
    exact centralPhysicalMeanZeroGap_of_finiteCenteredGap
      (fun coefficient hcoefficient =>
        (certificate.certificate base).absContraction
          coefficient hcoefficient)
      observable hcenter

end FixedNomeCofinalCanonicalHeadLDLAtRate

/-! ## 3. Canonical cleared LDL families at a supplied rate -/

/-- Cleared-denominator LDL checks of the canonical positive-head matrices at
an arbitrary supplied rate along a constructively cofinal cutoff schedule. -/
abbrev FixedNomeCofinalCanonicalHeadClearedLDLAtRate
    (w : Q') (hw : (0 : Q') <= w) (half : Nat) (q : Q') : Type 1 :=
  CofinalFixedCenteredRestrictionClearedLDLCertificate
    q
    (fun cutoff => centralPhysicalFiniteCarrierSize w hw cutoff half)
    (fun cutoff => centralPhysicalFiniteWeight w hw cutoff half)
    (fun cutoff => centralPhysicalFiniteKernel w hw cutoff half)
    (fun cutoff => centralPhysicalCanonicalHeadRestriction
      w hw cutoff half q)

namespace FixedNomeCofinalCanonicalHeadClearedLDLAtRate

/-- Canonical cleared LDL checks at `q` compile to the arbitrary strict
cofinal physical interface once the two strict-rate inequalities are
supplied. -/
def toCenteredStrictGap
    {w : Q'} {hw : (0 : Q') <= w} {half : Nat} {q : Q'}
    (hq0 : (0 : Q') <= q) (hq1 : q < (1 : Q'))
    (certificate : FixedNomeCofinalCanonicalHeadClearedLDLAtRate
      w hw half q) :
    FixedNomeCofinalCenteredStrictGap w hw half q where
  rate_nonnegative := hq0
  rate_lt_one := hq1
  anchor := certificate.anchor
  anchor_ge := certificate.anchor_ge
  meanZeroGap := by
    intro base observable hcenter
    exact centralPhysicalMeanZeroGap_of_finiteCenteredGap
      (fun coefficient hcoefficient =>
        (certificate.certificate base).absContraction
          coefficient hcoefficient)
      observable hcenter

end FixedNomeCofinalCanonicalHeadClearedLDLAtRate

/-! ## 4. Reflection positivity removes the lower LDL obligation -/

/-- An ordinary LDL check only of the upper reduced matrix.  This suffices on
the physical carrier because reflection positivity separately proves that the
joint quadratic is nonnegative. -/
structure FiniteCenteredRestrictionUpperLDLCertificate
    {n : Nat} {q : Q'} {weight : Nat -> Q'}
    {kernel : Nat -> Nat -> Q'}
    (restriction :
      FiniteCenteredTwoSidedRestriction n q weight kernel) : Type 1 where
  upperLower : Nat -> Nat -> Q'
  upperDiagonal : Nat -> Q'
  upperCheck :
    finiteLDLCheck restriction.reducedSize
      restriction.upperMatrix upperLower upperDiagonal = true

namespace FiniteCenteredRestrictionUpperLDLCertificate

/-- The sole upper LDL check proves `K <= qD` for every exactly centered full
coefficient vector. -/
theorem upperContraction
    {n : Nat} {q : Q'} {weight : Nat -> Q'}
    {kernel : Nat -> Nat -> Q'}
    {restriction :
      FiniteCenteredTwoSidedRestriction n q weight kernel}
    (certificate :
      FiniteCenteredRestrictionUpperLDLCertificate restriction)
    (coefficient : Nat -> Q')
    (hcenter : finiteWeightedMean n weight coefficient ≈ 0) :
    finiteMatrixQuadratic n kernel coefficient <=
      q * finiteDiagonalQuadratic n weight coefficient := by
  let chosen := restriction.complete coefficient hcenter
  let reduced : Nat -> Q' := chosen.val
  have hagrees : forall i, i < n ->
      coefficient i ≈ restriction.lift reduced i :=
    chosen.property
  have hlift :
      finiteMatrixQuadratic n kernel (restriction.lift reduced) <=
        q * finiteDiagonalQuadratic n weight
          (restriction.lift reduced) := by
    apply finiteReversibleContraction_of_penalized
    · exact Q'.le_trans' _ _ _
        (finiteMatrixQuadratic_nonnegative_of_ldl_check
          certificate.upperCheck reduced)
        (Q'.le_of_eqv (restriction.upperIdentify reduced))
    · exact restriction.liftCentered reduced
  have hleft :
      finiteMatrixQuadratic n kernel coefficient ≈
        finiteMatrixQuadratic n kernel (restriction.lift reduced) :=
    finiteMatrixQuadratic_coefficient_congr hagrees
  have hright :
      q * finiteDiagonalQuadratic n weight
          (restriction.lift reduced) ≈
        q * finiteDiagonalQuadratic n weight coefficient :=
    Q'.mul_eqv_congr_left q _ _
      (Q'.eqv_symm
        (finiteDiagonalQuadratic_coefficient_congr hagrees))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
    (Q'.le_trans' _ _ _ hlift (Q'.le_of_eqv hright))

end FiniteCenteredRestrictionUpperLDLCertificate

/-- A shardable cleared-denominator LDL check only of the upper reduced
matrix. -/
structure FiniteCenteredRestrictionUpperClearedLDLCertificate
    {n : Nat} {q : Q'} {weight : Nat -> Q'}
    {kernel : Nat -> Nat -> Q'}
    (restriction :
      FiniteCenteredTwoSidedRestriction n q weight kernel) : Type 1 where
  upperLower : Nat -> Nat -> Q'
  upperDiagonal : Nat -> Q'
  upperCommon : Nat -> Nat -> Nat
  upperRowsCheck :
    finiteLDLClearedRowsCheck restriction.reducedSize
      restriction.upperMatrix upperLower upperDiagonal upperCommon = true
  upperTriangular : forall i k, i < k -> upperLower i k = 0
  upperDiagonalCheck :
    finiteLDLDiagonalCheck restriction.reducedSize upperDiagonal = true

namespace FiniteCenteredRestrictionUpperClearedLDLCertificate

/-- Soundness of the sole cleared upper LDL check. -/
theorem upperContraction
    {n : Nat} {q : Q'} {weight : Nat -> Q'}
    {kernel : Nat -> Nat -> Q'}
    {restriction :
      FiniteCenteredTwoSidedRestriction n q weight kernel}
    (certificate :
      FiniteCenteredRestrictionUpperClearedLDLCertificate restriction)
    (coefficient : Nat -> Q')
    (hcenter : finiteWeightedMean n weight coefficient ≈ 0) :
    finiteMatrixQuadratic n kernel coefficient <=
      q * finiteDiagonalQuadratic n weight coefficient := by
  let chosen := restriction.complete coefficient hcenter
  let reduced : Nat -> Q' := chosen.val
  have hagrees : forall i, i < n ->
      coefficient i ≈ restriction.lift reduced i :=
    chosen.property
  have hlift :
      finiteMatrixQuadratic n kernel (restriction.lift reduced) <=
        q * finiteDiagonalQuadratic n weight
          (restriction.lift reduced) := by
    apply finiteReversibleContraction_of_penalized
    · exact Q'.le_trans' _ _ _
        (finiteMatrixQuadratic_nonnegative_of_cleared_ldl_check
          certificate.upperRowsCheck certificate.upperTriangular
          certificate.upperDiagonalCheck reduced)
        (Q'.le_of_eqv (restriction.upperIdentify reduced))
    · exact restriction.liftCentered reduced
  have hleft :
      finiteMatrixQuadratic n kernel coefficient ≈
        finiteMatrixQuadratic n kernel (restriction.lift reduced) :=
    finiteMatrixQuadratic_coefficient_congr hagrees
  have hright :
      q * finiteDiagonalQuadratic n weight
          (restriction.lift reduced) ≈
        q * finiteDiagonalQuadratic n weight coefficient :=
    Q'.mul_eqv_congr_left q _ _
      (Q'.eqv_symm
        (finiteDiagonalQuadratic_coefficient_congr hagrees))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
    (Q'.le_trans' _ _ _ hlift (Q'.le_of_eqv hright))

end FiniteCenteredRestrictionUpperClearedLDLCertificate

/-- Transport a centered upper bound from the indexed carrier to the genuine
physical finite sums. -/
theorem centralPhysicalMeanZeroUpperGap_of_finiteCenteredUpperGap
    {w : Q'} {hw : (0 : Q') <= w} {cutoff half : Nat} {q : Q'}
    (hfinite :
      forall coefficient : Nat -> Q',
        finiteWeightedMean
            (centralPhysicalFiniteCarrierSize w hw cutoff half)
            (centralPhysicalFiniteWeight w hw cutoff half)
            coefficient ≈ 0 ->
          finiteMatrixQuadratic
              (centralPhysicalFiniteCarrierSize w hw cutoff half)
              (centralPhysicalFiniteKernel w hw cutoff half)
              coefficient <=
            q * finiteDiagonalQuadratic
              (centralPhysicalFiniteCarrierSize w hw cutoff half)
              (centralPhysicalFiniteWeight w hw cutoff half)
              coefficient)
    (observable : EdgeLabelling -> Q')
    (hcenter : CentralPhysicalMeanZero w hw cutoff half observable) :
    centralPhysicalJointQuadratic w hw cutoff half observable <=
      q * centralPhysicalWeightedInner
        w hw cutoff half observable observable := by
  let coefficient :=
    centralPhysicalFiniteCoefficient w hw cutoff half observable
  have hindexed := hfinite coefficient
    (centralPhysicalFiniteCoefficient_centered hcenter)
  have hleft :
      finiteMatrixQuadratic
          (centralPhysicalFiniteCarrierSize w hw cutoff half)
          (centralPhysicalFiniteKernel w hw cutoff half) coefficient ≈
        centralPhysicalJointQuadratic
          w hw cutoff half observable :=
    centralPhysicalFiniteMatrixQuadratic_eqv_jointQuadratic
      w hw cutoff half observable
  have hright :
      q * finiteDiagonalQuadratic
          (centralPhysicalFiniteCarrierSize w hw cutoff half)
          (centralPhysicalFiniteWeight w hw cutoff half) coefficient ≈
        q * centralPhysicalWeightedInner
          w hw cutoff half observable observable :=
    Q'.mul_eqv_congr_left q _ _
      (centralPhysicalFiniteDiagonalQuadratic_eqv_weightedInner
        w hw cutoff half observable)
  exact le_of_eqv_le (Q'.eqv_symm hleft)
    (le_of_le_eqv hindexed hright)

/-- Ordinary upper-only LDL checks pinned to prescribed centered restrictions
along a constructively cofinal sequence of changing finite carriers. -/
structure CofinalFixedCenteredRestrictionUpperLDLCertificate
    (q : Q') (size : Nat -> Nat)
    (weight : Nat -> Nat -> Q')
    (kernel : Nat -> Nat -> Nat -> Q')
    (restriction : forall cutoff,
      FiniteCenteredTwoSidedRestriction
        (size cutoff) q (weight cutoff) (kernel cutoff)) : Type 1 where
  anchor : Nat -> Nat
  anchor_ge : forall base, base <= anchor base
  certificate : forall base,
    FiniteCenteredRestrictionUpperLDLCertificate
      (restriction (anchor base))

/-- Cleared upper-only LDL checks pinned to prescribed centered restrictions
along a constructively cofinal sequence of changing finite carriers. -/
structure CofinalFixedCenteredRestrictionUpperClearedLDLCertificate
    (q : Q') (size : Nat -> Nat)
    (weight : Nat -> Nat -> Q')
    (kernel : Nat -> Nat -> Nat -> Q')
    (restriction : forall cutoff,
      FiniteCenteredTwoSidedRestriction
        (size cutoff) q (weight cutoff) (kernel cutoff)) : Type 1 where
  anchor : Nat -> Nat
  anchor_ge : forall base, base <= anchor base
  certificate : forall base,
    FiniteCenteredRestrictionUpperClearedLDLCertificate
      (restriction (anchor base))

/-- Ordinary upper-only checks specialized to the canonical physical
positive-head matrices at a supplied rate. -/
abbrev FixedNomeCofinalCanonicalHeadUpperLDLAtRate
    (w : Q') (hw : (0 : Q') <= w) (half : Nat) (q : Q') : Type 1 :=
  CofinalFixedCenteredRestrictionUpperLDLCertificate
    q
    (fun cutoff => centralPhysicalFiniteCarrierSize w hw cutoff half)
    (fun cutoff => centralPhysicalFiniteWeight w hw cutoff half)
    (fun cutoff => centralPhysicalFiniteKernel w hw cutoff half)
    (fun cutoff => centralPhysicalCanonicalHeadRestriction
      w hw cutoff half q)

namespace FixedNomeCofinalCanonicalHeadUpperLDLAtRate

/-- Reflection positivity turns each one-sided upper certificate into the
absolute mean-zero estimate consumed by the arbitrary strict cofinal route. -/
def toCenteredStrictGap
    {w : Q'} {hw : (0 : Q') <= w} {half : Nat} {q : Q'}
    (hq0 : (0 : Q') <= q) (hq1 : q < (1 : Q'))
    (certificate : FixedNomeCofinalCanonicalHeadUpperLDLAtRate
      w hw half q) :
    FixedNomeCofinalCenteredStrictGap w hw half q where
  rate_nonnegative := hq0
  rate_lt_one := hq1
  anchor := certificate.anchor
  anchor_ge := certificate.anchor_ge
  meanZeroGap := by
    intro base observable hcenter
    rw [YMGap.Constructive.ExpNeg.abs_of_nonneg
      (centralPhysicalJointQuadratic_nonnegative
        w hw (certificate.anchor base) half observable)]
    exact centralPhysicalMeanZeroUpperGap_of_finiteCenteredUpperGap
      (fun coefficient hcoefficient =>
        (certificate.certificate base).upperContraction
          coefficient hcoefficient)
      observable hcenter

end FixedNomeCofinalCanonicalHeadUpperLDLAtRate

/-- Cleared-denominator upper-only LDL checks pinned to the canonical
positive-head matrix at an arbitrary rate along a cofinal cutoff schedule. -/
abbrev FixedNomeCofinalCanonicalHeadUpperClearedLDLAtRate
    (w : Q') (hw : (0 : Q') <= w) (half : Nat) (q : Q') : Type 1 :=
  CofinalFixedCenteredRestrictionUpperClearedLDLCertificate
    q
    (fun cutoff => centralPhysicalFiniteCarrierSize w hw cutoff half)
    (fun cutoff => centralPhysicalFiniteWeight w hw cutoff half)
    (fun cutoff => centralPhysicalFiniteKernel w hw cutoff half)
    (fun cutoff => centralPhysicalCanonicalHeadRestriction
      w hw cutoff half q)

namespace FixedNomeCofinalCanonicalHeadUpperClearedLDLAtRate

/-- Cleared one-sided checks compile to the same arbitrary strict physical
cofinal interface. -/
def toCenteredStrictGap
    {w : Q'} {hw : (0 : Q') <= w} {half : Nat} {q : Q'}
    (hq0 : (0 : Q') <= q) (hq1 : q < (1 : Q'))
    (certificate : FixedNomeCofinalCanonicalHeadUpperClearedLDLAtRate
      w hw half q) :
    FixedNomeCofinalCenteredStrictGap w hw half q where
  rate_nonnegative := hq0
  rate_lt_one := hq1
  anchor := certificate.anchor
  anchor_ge := certificate.anchor_ge
  meanZeroGap := by
    intro base observable hcenter
    rw [YMGap.Constructive.ExpNeg.abs_of_nonneg
      (centralPhysicalJointQuadratic_nonnegative
        w hw (certificate.anchor base) half observable)]
    exact centralPhysicalMeanZeroUpperGap_of_finiteCenteredUpperGap
      (fun coefficient hcoefficient =>
        (certificate.certificate base).upperContraction
          coefficient hcoefficient)
      observable hcenter

end FixedNomeCofinalCanonicalHeadUpperClearedLDLAtRate

end YMGap.Continuum.BF4PhysicalCutoffCofinalStrictGap

#print axioms
  YMGap.Continuum.BF4PhysicalCutoffCofinalStrictGap.FixedNomeCofinalCenteredStrictGap.ofCenteredSixteenth
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffCofinalStrictGap.FixedNomeCofinalCanonicalHeadLDLAtRate.toCenteredStrictGap
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffCofinalStrictGap.FixedNomeCofinalCanonicalHeadClearedLDLAtRate.toCenteredStrictGap
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffCofinalStrictGap.FiniteCenteredRestrictionUpperLDLCertificate.upperContraction
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffCofinalStrictGap.FiniteCenteredRestrictionUpperClearedLDLCertificate.upperContraction
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffCofinalStrictGap.FixedNomeCofinalCanonicalHeadUpperLDLAtRate.toCenteredStrictGap
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffCofinalStrictGap.FixedNomeCofinalCanonicalHeadUpperClearedLDLAtRate.toCenteredStrictGap
