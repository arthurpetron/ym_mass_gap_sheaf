/-
# Canonical LDL checks restricted to the physical vacuum component

The same-object coefficient is supported on the canonical vacuum component,
whereas the earlier canonical LDL bridge asked for a certificate on the whole
positive physical carrier.  This module reindexes only the duplicate-free
vacuum-sector list, constructs its canonical positive-head restriction, and
compiles upper-only ordinary or cleared LDL checks on that smaller matrix to
the same-object centered cutoff-limit interface.

Reflection positivity supplies the lower form bound.  No cofinal LDL family,
uniform strict rate, completed-space theorem, thermodynamic or continuum
limit, or Clay conclusion is constructed here.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCanonicalLDLBridge
import YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity

namespace YMGap.Continuum.BF4PhysicalCutoffVacuumSectorLocalCanonicalLDLBridge

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffCofinalStrictGap
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorBlockDecomposition
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCanonicalLDLBridge
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCenteredDiagonalCauchy
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCenteredLimitGap
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCenteredMatrixCauchy
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFormCauchy
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFormPushforward
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFullCarrierContraction
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorHeadCentering
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledUniformPoincareGap
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorZeroExtensionContraction
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorGramPositivity
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
open YMGap.Continuum.FiniteListIndexQuadraticBridge
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteRationalCenteredRestrictionCertificate
open YMGap.Continuum.FiniteRationalHeadCenteredPullback
open YMGap.Continuum.FiniteRationalLDLCertificate
open YMGap.Continuum.FiniteRationalReversibleSpectralCertificate
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Exact finite coordinates on the vacuum-sector list -/

def centralPhysicalFiniteVacuumSectorCoordinateSize
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat) : Nat :=
  (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half).length

def centralPhysicalFiniteVacuumSectorCoordinateAt
    (w : Q') (hw : (0 : Q') ≤ w)
    (cutoff half coordinate : Nat) : Nat :=
  finiteListStateAt
    (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
    0 coordinate

def centralPhysicalFiniteVacuumSectorCoordinateWeight
    (w : Q') (hw : (0 : Q') ≤ w)
    (cutoff half coordinate : Nat) : Q' :=
  centralPhysicalFiniteWeight w hw cutoff half
    (centralPhysicalFiniteVacuumSectorCoordinateAt
      w hw cutoff half coordinate)

def centralPhysicalFiniteVacuumSectorCoordinateKernel
    (w : Q') (hw : (0 : Q') ≤ w)
    (cutoff half left right : Nat) : Q' :=
  centralPhysicalFiniteKernel w hw cutoff half
    (centralPhysicalFiniteVacuumSectorCoordinateAt
      w hw cutoff half left)
    (centralPhysicalFiniteVacuumSectorCoordinateAt
      w hw cutoff half right)

def centralPhysicalFiniteVacuumSectorCoordinateCoefficient
    (w : Q') (hw : (0 : Q') ≤ w)
    (cutoff half : Nat) (coefficient : Nat → Q')
    (coordinate : Nat) : Q' :=
  coefficient
    (centralPhysicalFiniteVacuumSectorCoordinateAt
      w hw cutoff half coordinate)

theorem centralPhysicalFiniteVacuumSectorCoordinateMean_eqv
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat)
    (coefficient : Nat → Q') :
    finiteWeightedMean
        (centralPhysicalFiniteVacuumSectorCoordinateSize
          w hw cutoff half)
        (centralPhysicalFiniteVacuumSectorCoordinateWeight
          w hw cutoff half)
        (centralPhysicalFiniteVacuumSectorCoordinateCoefficient
          w hw cutoff half coefficient) ≈
      centralPhysicalFiniteVacuumSectorWeightedMean
        w hw cutoff half coefficient := by
  unfold finiteWeightedMean
    centralPhysicalFiniteVacuumSectorCoordinateSize
    centralPhysicalFiniteVacuumSectorCoordinateWeight
    centralPhysicalFiniteVacuumSectorCoordinateCoefficient
    centralPhysicalFiniteVacuumSectorCoordinateAt
    centralPhysicalFiniteVacuumSectorWeightedMean
  exact Q'.eqv_of_eq
    (finiteIndexSum_eq_listQSum
      (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half) 0
      (fun index => coefficient index *
        centralPhysicalFiniteWeight w hw cutoff half index))

theorem centralPhysicalFiniteVacuumSectorCoordinateDiagonal_eqv
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat)
    (coefficient : Nat → Q') :
    finiteDiagonalQuadratic
        (centralPhysicalFiniteVacuumSectorCoordinateSize
          w hw cutoff half)
        (centralPhysicalFiniteVacuumSectorCoordinateWeight
          w hw cutoff half)
        (centralPhysicalFiniteVacuumSectorCoordinateCoefficient
          w hw cutoff half coefficient) ≈
      centralPhysicalFiniteVacuumSectorDiagonalQuadratic
        w hw cutoff half coefficient := by
  unfold finiteDiagonalQuadratic
    centralPhysicalFiniteVacuumSectorCoordinateSize
    centralPhysicalFiniteVacuumSectorCoordinateWeight
    centralPhysicalFiniteVacuumSectorCoordinateCoefficient
    centralPhysicalFiniteVacuumSectorCoordinateAt
    centralPhysicalFiniteVacuumSectorDiagonalQuadratic
  exact Q'.eqv_of_eq
    (finiteIndexSum_eq_listQSum
      (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half) 0
      (fun index =>
        (coefficient index * coefficient index) *
          centralPhysicalFiniteWeight w hw cutoff half index))

theorem centralPhysicalFiniteVacuumSectorCoordinateMatrix_eqv
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat)
    (coefficient : Nat → Q') :
    finiteMatrixQuadratic
        (centralPhysicalFiniteVacuumSectorCoordinateSize
          w hw cutoff half)
        (centralPhysicalFiniteVacuumSectorCoordinateKernel
          w hw cutoff half)
        (centralPhysicalFiniteVacuumSectorCoordinateCoefficient
          w hw cutoff half coefficient) ≈
      centralPhysicalFiniteVacuumSectorMatrixQuadratic
        w hw cutoff half coefficient := by
  unfold finiteMatrixQuadratic
    centralPhysicalFiniteVacuumSectorCoordinateSize
    centralPhysicalFiniteVacuumSectorCoordinateKernel
    centralPhysicalFiniteVacuumSectorCoordinateCoefficient
    centralPhysicalFiniteVacuumSectorCoordinateAt
    centralPhysicalFiniteVacuumSectorMatrixQuadratic
    finiteJointQuadratic
  exact finiteIndexDoubleSum_eqv_listQSum
    (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half) 0
    (fun left right =>
      (coefficient left * coefficient right) *
        centralPhysicalFiniteKernel w hw cutoff half left right)

private theorem finiteListStateAt_zero_mem_of_ne_nil
    {A : Type} (items : List A) (fallback : A)
    (hne : items ≠ []) :
    finiteListStateAt items fallback 0 ∈ items := by
  cases items with
  | nil => exact False.elim (hne rfl)
  | cons head tail =>
      simp only [finiteListStateAt, List.getD_cons_zero,
        List.mem_cons, true_or]

theorem centralPhysicalFiniteVacuumSectorCoordinateAt_zero_mem
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat) :
    centralPhysicalFiniteVacuumSectorCoordinateAt w hw cutoff half 0 ∈
      centralPhysicalFiniteVacuumSectorIndices w hw cutoff half := by
  apply finiteListStateAt_zero_mem_of_ne_nil
  intro hempty
  have hzero := zero_mem_centralPhysicalFiniteVacuumSectorIndices
    w hw cutoff half
  rw [hempty] at hzero
  exact List.not_mem_nil hzero

theorem centralPhysicalFiniteVacuumSectorCoordinateWeight_zero_pos
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat) :
    (0 : Q') <
      centralPhysicalFiniteVacuumSectorCoordinateWeight
        w hw cutoff half 0 := by
  unfold centralPhysicalFiniteVacuumSectorCoordinateWeight
  exact centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex
    (centralPhysicalFiniteVacuumSectorCoordinateAt_zero_mem
      w hw cutoff half)

theorem centralPhysicalFiniteVacuumSectorCoordinateSize_pred_succ
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat) :
    centralPhysicalFiniteVacuumSectorCoordinateSize w hw cutoff half - 1 + 1 =
      centralPhysicalFiniteVacuumSectorCoordinateSize w hw cutoff half := by
  apply Nat.sub_add_cancel
  exact Nat.succ_le_iff.mpr
    (List.length_pos_of_mem
      (zero_mem_centralPhysicalFiniteVacuumSectorIndices
        w hw cutoff half))

/-! ## 2. Canonical sector-local upper LDL certificates -/

def centralPhysicalFiniteVacuumSectorCanonicalHeadRestriction
    (w : Q') (hw : (0 : Q') ≤ w)
    (cutoff half : Nat) (q : Q') :
    FiniteCenteredTwoSidedRestriction
      (centralPhysicalFiniteVacuumSectorCoordinateSize w hw cutoff half)
      q
      (centralPhysicalFiniteVacuumSectorCoordinateWeight w hw cutoff half)
      (centralPhysicalFiniteVacuumSectorCoordinateKernel
        w hw cutoff half) := by
  let n :=
    centralPhysicalFiniteVacuumSectorCoordinateSize w hw cutoff half - 1
  have hsize : n + 1 =
      centralPhysicalFiniteVacuumSectorCoordinateSize w hw cutoff half :=
    centralPhysicalFiniteVacuumSectorCoordinateSize_pred_succ
      w hw cutoff half
  rw [← hsize]
  exact finiteCanonicalHeadCenteredRestriction n q
    (centralPhysicalFiniteVacuumSectorCoordinateWeight w hw cutoff half)
    (centralPhysicalFiniteVacuumSectorCoordinateKernel w hw cutoff half)
    (centralPhysicalFiniteVacuumSectorCoordinateWeight_zero_pos
      w hw cutoff half)

abbrev CentralPhysicalFiniteVacuumSectorCanonicalHeadUpperLDLCertificate
    (w : Q') (hw : (0 : Q') ≤ w)
    (cutoff half : Nat) (q : Q') : Type 1 :=
  FiniteCenteredRestrictionUpperLDLCertificate
    (centralPhysicalFiniteVacuumSectorCanonicalHeadRestriction
      w hw cutoff half q)

abbrev CentralPhysicalFiniteVacuumSectorCanonicalHeadUpperClearedLDLCertificate
    (w : Q') (hw : (0 : Q') ≤ w)
    (cutoff half : Nat) (q : Q') : Type 1 :=
  FiniteCenteredRestrictionUpperClearedLDLCertificate
    (centralPhysicalFiniteVacuumSectorCanonicalHeadRestriction
      w hw cutoff half q)

private theorem centralPhysicalFiniteVacuumSectorMeanZeroUpperGap_of_coordinate
    {w : Q'} {hw : (0 : Q') ≤ w}
    {cutoff half : Nat} {q : Q'}
    (hupper : ∀ coordinate : Nat → Q',
      finiteWeightedMean
          (centralPhysicalFiniteVacuumSectorCoordinateSize
            w hw cutoff half)
          (centralPhysicalFiniteVacuumSectorCoordinateWeight
            w hw cutoff half)
          coordinate ≈ 0 →
        finiteMatrixQuadratic
            (centralPhysicalFiniteVacuumSectorCoordinateSize
              w hw cutoff half)
            (centralPhysicalFiniteVacuumSectorCoordinateKernel
              w hw cutoff half)
            coordinate ≤
          q * finiteDiagonalQuadratic
            (centralPhysicalFiniteVacuumSectorCoordinateSize
              w hw cutoff half)
            (centralPhysicalFiniteVacuumSectorCoordinateWeight
              w hw cutoff half)
            coordinate)
    (coefficient : Nat → Q')
    (hcenter : centralPhysicalFiniteVacuumSectorWeightedMean
      w hw cutoff half coefficient ≈ 0) :
    centralPhysicalFiniteVacuumSectorMatrixQuadratic
        w hw cutoff half coefficient ≤
      q * centralPhysicalFiniteVacuumSectorDiagonalQuadratic
        w hw cutoff half coefficient := by
  let coordinate :=
    centralPhysicalFiniteVacuumSectorCoordinateCoefficient
      w hw cutoff half coefficient
  have hcoordinateCenter :
      finiteWeightedMean
          (centralPhysicalFiniteVacuumSectorCoordinateSize
            w hw cutoff half)
          (centralPhysicalFiniteVacuumSectorCoordinateWeight
            w hw cutoff half)
          coordinate ≈ 0 :=
    Q'.eqv_trans _ _ _
      (centralPhysicalFiniteVacuumSectorCoordinateMean_eqv
        w hw cutoff half coefficient)
      hcenter
  have hcoordinate := hupper coordinate hcoordinateCenter
  have hmatrix :=
    centralPhysicalFiniteVacuumSectorCoordinateMatrix_eqv
      w hw cutoff half coefficient
  have hdiagonal :=
    centralPhysicalFiniteVacuumSectorCoordinateDiagonal_eqv
      w hw cutoff half coefficient
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm hmatrix))
    (Q'.le_trans' _ _ _ hcoordinate
      (Q'.le_of_eqv (Q'.mul_eqv_congr_left q _ _ hdiagonal)))

namespace CentralPhysicalFiniteVacuumSectorCanonicalHeadUpperLDLCertificate

theorem meanZeroAbsGap
    {w : Q'} {hw : (0 : Q') ≤ w}
    {cutoff half : Nat} {q : Q'}
    (certificate :
      CentralPhysicalFiniteVacuumSectorCanonicalHeadUpperLDLCertificate
        w hw cutoff half q)
    (coefficient : Nat → Q')
    (hcenter : centralPhysicalFiniteVacuumSectorWeightedMean
      w hw cutoff half coefficient ≈ 0) :
    Q'.abs
        (centralPhysicalFiniteVacuumSectorMatrixQuadratic
          w hw cutoff half coefficient) ≤
      q * centralPhysicalFiniteVacuumSectorDiagonalQuadratic
        w hw cutoff half coefficient := by
  rw [YMGap.Constructive.ExpNeg.abs_of_nonneg
    (centralPhysicalFiniteVacuumSectorMatrixQuadratic_nonnegative
      w hw cutoff half coefficient)]
  exact centralPhysicalFiniteVacuumSectorMeanZeroUpperGap_of_coordinate
    (fun coordinate hcoordinate =>
      certificate.upperContraction coordinate hcoordinate)
    coefficient hcenter

end CentralPhysicalFiniteVacuumSectorCanonicalHeadUpperLDLCertificate

namespace CentralPhysicalFiniteVacuumSectorCanonicalHeadUpperClearedLDLCertificate

theorem meanZeroAbsGap
    {w : Q'} {hw : (0 : Q') ≤ w}
    {cutoff half : Nat} {q : Q'}
    (certificate :
      CentralPhysicalFiniteVacuumSectorCanonicalHeadUpperClearedLDLCertificate
        w hw cutoff half q)
    (coefficient : Nat → Q')
    (hcenter : centralPhysicalFiniteVacuumSectorWeightedMean
      w hw cutoff half coefficient ≈ 0) :
    Q'.abs
        (centralPhysicalFiniteVacuumSectorMatrixQuadratic
          w hw cutoff half coefficient) ≤
      q * centralPhysicalFiniteVacuumSectorDiagonalQuadratic
        w hw cutoff half coefficient := by
  rw [YMGap.Constructive.ExpNeg.abs_of_nonneg
    (centralPhysicalFiniteVacuumSectorMatrixQuadratic_nonnegative
      w hw cutoff half coefficient)]
  exact centralPhysicalFiniteVacuumSectorMeanZeroUpperGap_of_coordinate
    (fun coordinate hcoordinate =>
      certificate.upperContraction coordinate hcoordinate)
    coefficient hcenter

end CentralPhysicalFiniteVacuumSectorCanonicalHeadUpperClearedLDLCertificate

/-! ## 3. Cofinal sector-local certificates and the same-object limit -/

abbrev FixedNomeCofinalVacuumSectorCanonicalHeadUpperLDLAtRate
    (w : Q') (hw : (0 : Q') ≤ w) (half : Nat) (q : Q') : Type 1 :=
  CofinalFixedCenteredRestrictionUpperLDLCertificate
    q
    (fun cutoff =>
      centralPhysicalFiniteVacuumSectorCoordinateSize w hw cutoff half)
    (fun cutoff =>
      centralPhysicalFiniteVacuumSectorCoordinateWeight w hw cutoff half)
    (fun cutoff =>
      centralPhysicalFiniteVacuumSectorCoordinateKernel w hw cutoff half)
    (fun cutoff =>
      centralPhysicalFiniteVacuumSectorCanonicalHeadRestriction
        w hw cutoff half q)

abbrev FixedNomeCofinalVacuumSectorCanonicalHeadUpperClearedLDLAtRate
    (w : Q') (hw : (0 : Q') ≤ w) (half : Nat) (q : Q') : Type 1 :=
  CofinalFixedCenteredRestrictionUpperClearedLDLCertificate
    q
    (fun cutoff =>
      centralPhysicalFiniteVacuumSectorCoordinateSize w hw cutoff half)
    (fun cutoff =>
      centralPhysicalFiniteVacuumSectorCoordinateWeight w hw cutoff half)
    (fun cutoff =>
      centralPhysicalFiniteVacuumSectorCoordinateKernel w hw cutoff half)
    (fun cutoff =>
      centralPhysicalFiniteVacuumSectorCanonicalHeadRestriction
        w hw cutoff half q)

private def toVacuumSectorCenteredStrictGap_of_coordinateUpper
    {w : Q'} {hw : (0 : Q') ≤ w} {half : Nat} {q : Q'}
    (hq0 : (0 : Q') ≤ q) (hq1 : q < (1 : Q'))
    (anchor : Nat → Nat)
    (anchor_ge : ∀ request, request ≤ anchor request)
    (hupper : ∀ request (coordinate : Nat → Q'),
      finiteWeightedMean
          (centralPhysicalFiniteVacuumSectorCoordinateSize
            w hw (anchor request) half)
          (centralPhysicalFiniteVacuumSectorCoordinateWeight
            w hw (anchor request) half)
          coordinate ≈ 0 →
        finiteMatrixQuadratic
            (centralPhysicalFiniteVacuumSectorCoordinateSize
              w hw (anchor request) half)
            (centralPhysicalFiniteVacuumSectorCoordinateKernel
              w hw (anchor request) half)
            coordinate ≤
          q * finiteDiagonalQuadratic
            (centralPhysicalFiniteVacuumSectorCoordinateSize
              w hw (anchor request) half)
            (centralPhysicalFiniteVacuumSectorCoordinateWeight
              w hw (anchor request) half)
            coordinate) :
    FixedNomeCofinalVacuumSectorCenteredStrictGap w hw half q where
  rate_nonnegative := hq0
  rate_lt_one := hq1
  anchor := fun base threshold => anchor (max base threshold)
  anchor_ge := by
    intro base threshold
    exact anchor_ge (max base threshold)
  centeredGap := by
    intro base threshold coefficient
    let request := max base threshold
    let later := anchor request
    let moving :=
      centralPhysicalFinitePulledVacuumSectorHeadCenteredCoefficient
        w hw base later half coefficient
    let extended :=
      centralPhysicalFiniteVacuumSectorCoefficientExtension
        w hw base later half moving
    let coordinate :=
      centralPhysicalFiniteVacuumSectorCoordinateCoefficient
        w hw later half extended
    have hrequestLater : request ≤ later := anchor_ge request
    have hbaseLater : base ≤ later :=
      Nat.le_trans (Nat.le_max_left base threshold) hrequestLater
    have hsectorCenter :
        centralPhysicalFiniteVacuumSectorWeightedMean
          w hw later half extended ≈ 0 :=
      centralPhysicalFiniteVacuumSectorHeadCenteredExtension_meanZero
        hbaseLater coefficient
    have hcoordinateCenter :
        finiteWeightedMean
            (centralPhysicalFiniteVacuumSectorCoordinateSize
              w hw later half)
            (centralPhysicalFiniteVacuumSectorCoordinateWeight
              w hw later half)
            coordinate ≈ 0 :=
      Q'.eqv_trans _ _ _
        (centralPhysicalFiniteVacuumSectorCoordinateMean_eqv
          w hw later half extended)
        hsectorCenter
    have hcoordinateUpper :
        finiteMatrixQuadratic
              (centralPhysicalFiniteVacuumSectorCoordinateSize
                w hw later half)
              (centralPhysicalFiniteVacuumSectorCoordinateKernel
                w hw later half)
              coordinate ≤
          q * finiteDiagonalQuadratic
            (centralPhysicalFiniteVacuumSectorCoordinateSize
              w hw later half)
            (centralPhysicalFiniteVacuumSectorCoordinateWeight
              w hw later half)
            coordinate :=
      hupper request coordinate hcoordinateCenter
    have hmatrix :
        finiteMatrixQuadratic
            (centralPhysicalFiniteVacuumSectorCoordinateSize
              w hw later half)
            (centralPhysicalFiniteVacuumSectorCoordinateKernel
              w hw later half)
            coordinate ≈
          centralPhysicalFinitePulledVacuumSectorMatrixQuadratic
            w hw base later half moving :=
      Q'.eqv_trans _ _ _
        (centralPhysicalFiniteVacuumSectorCoordinateMatrix_eqv
          w hw later half extended)
        (centralPhysicalFiniteVacuumSectorHeadCenteredExtensionMatrix_eqv_pulled
          hbaseLater coefficient)
    have hdiagonal :
        finiteDiagonalQuadratic
            (centralPhysicalFiniteVacuumSectorCoordinateSize
              w hw later half)
            (centralPhysicalFiniteVacuumSectorCoordinateWeight
              w hw later half)
            coordinate ≈
          centralPhysicalFinitePulledVacuumSectorDiagonalQuadratic
            w hw base later half moving :=
      Q'.eqv_trans _ _ _
        (centralPhysicalFiniteVacuumSectorCoordinateDiagonal_eqv
          w hw later half extended)
        (centralPhysicalFiniteVacuumSectorHeadCenteredExtensionDiagonal_eqv_pulled
          hbaseLater coefficient)
    have hpulledNonnegative :
        (0 : Q') ≤
          centralPhysicalFinitePulledVacuumSectorMatrixQuadratic
            w hw base later half moving :=
      fixedBasePulledMovingMatrix_nonnegative
        base later half hbaseLater coefficient
    rw [YMGap.Constructive.ExpNeg.abs_of_nonneg hpulledNonnegative]
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.eqv_symm hmatrix))
      (Q'.le_trans' _ _ _ hcoordinateUpper
        (Q'.le_of_eqv
          (Q'.mul_eqv_congr_left q _ _ hdiagonal)))

namespace FixedNomeCofinalVacuumSectorCanonicalHeadUpperLDLAtRate

def toVacuumSectorCenteredStrictGap
    {w : Q'} {hw : (0 : Q') ≤ w} {half : Nat} {q : Q'}
    (hq0 : (0 : Q') ≤ q) (hq1 : q < (1 : Q'))
    (certificate :
      FixedNomeCofinalVacuumSectorCanonicalHeadUpperLDLAtRate
        w hw half q) :
    FixedNomeCofinalVacuumSectorCenteredStrictGap w hw half q :=
  toVacuumSectorCenteredStrictGap_of_coordinateUpper
    hq0 hq1 certificate.anchor certificate.anchor_ge
    (fun request coordinate hcenter =>
      (certificate.certificate request).upperContraction
        coordinate hcenter)

theorem centeredMatrixCutoffLimit_leEv_rate_mul_diagonal
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) {q : Q'}
    (hq0 : (0 : Q') ≤ q) (hq1 : q < (1 : Q'))
    (certificate :
      FixedNomeCofinalVacuumSectorCanonicalHeadUpperLDLAtRate
        w (Q'.le_of_lt hw0) half q)
    (base : Nat) (coefficient : Nat → Q') :
    CReal.leEv
      (centralPhysicalFinitePulledVacuumSectorHeadCenteredMatrixCutoffLimit
        hw0 hw1 base half coefficient)
      (CReal.mul
        (CReal.ofQ' q)
        (centralPhysicalFinitePulledVacuumSectorHeadCenteredDiagonalCutoffLimit
          hw0 hw1 base half coefficient)) :=
  FixedNomeCofinalVacuumSectorCenteredStrictGap.centeredMatrixCutoffLimit_leEv_rate_mul_diagonal
      hw0 hw1 half
      (toVacuumSectorCenteredStrictGap hq0 hq1 certificate)
      base coefficient

end FixedNomeCofinalVacuumSectorCanonicalHeadUpperLDLAtRate

namespace FixedNomeCofinalVacuumSectorCanonicalHeadUpperClearedLDLAtRate

def toVacuumSectorCenteredStrictGap
    {w : Q'} {hw : (0 : Q') ≤ w} {half : Nat} {q : Q'}
    (hq0 : (0 : Q') ≤ q) (hq1 : q < (1 : Q'))
    (certificate :
      FixedNomeCofinalVacuumSectorCanonicalHeadUpperClearedLDLAtRate
        w hw half q) :
    FixedNomeCofinalVacuumSectorCenteredStrictGap w hw half q :=
  toVacuumSectorCenteredStrictGap_of_coordinateUpper
    hq0 hq1 certificate.anchor certificate.anchor_ge
    (fun request coordinate hcenter =>
      (certificate.certificate request).upperContraction
        coordinate hcenter)

theorem centeredMatrixCutoffLimit_leEv_rate_mul_diagonal
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) {q : Q'}
    (hq0 : (0 : Q') ≤ q) (hq1 : q < (1 : Q'))
    (certificate :
      FixedNomeCofinalVacuumSectorCanonicalHeadUpperClearedLDLAtRate
        w (Q'.le_of_lt hw0) half q)
    (base : Nat) (coefficient : Nat → Q') :
    CReal.leEv
      (centralPhysicalFinitePulledVacuumSectorHeadCenteredMatrixCutoffLimit
        hw0 hw1 base half coefficient)
      (CReal.mul
        (CReal.ofQ' q)
        (centralPhysicalFinitePulledVacuumSectorHeadCenteredDiagonalCutoffLimit
          hw0 hw1 base half coefficient)) :=
  FixedNomeCofinalVacuumSectorCenteredStrictGap.centeredMatrixCutoffLimit_leEv_rate_mul_diagonal
      hw0 hw1 half
      (toVacuumSectorCenteredStrictGap hq0 hq1 certificate)
      base coefficient

end FixedNomeCofinalVacuumSectorCanonicalHeadUpperClearedLDLAtRate

end YMGap.Continuum.BF4PhysicalCutoffVacuumSectorLocalCanonicalLDLBridge

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorLocalCanonicalLDLBridge.centralPhysicalFiniteVacuumSectorCoordinateMean_eqv
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorLocalCanonicalLDLBridge.centralPhysicalFiniteVacuumSectorCoordinateDiagonal_eqv
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorLocalCanonicalLDLBridge.centralPhysicalFiniteVacuumSectorCoordinateMatrix_eqv
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorLocalCanonicalLDLBridge.centralPhysicalFiniteVacuumSectorCanonicalHeadRestriction
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorLocalCanonicalLDLBridge.CentralPhysicalFiniteVacuumSectorCanonicalHeadUpperLDLCertificate.meanZeroAbsGap
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorLocalCanonicalLDLBridge.CentralPhysicalFiniteVacuumSectorCanonicalHeadUpperClearedLDLCertificate.meanZeroAbsGap
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorLocalCanonicalLDLBridge.FixedNomeCofinalVacuumSectorCanonicalHeadUpperLDLAtRate.toVacuumSectorCenteredStrictGap
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorLocalCanonicalLDLBridge.FixedNomeCofinalVacuumSectorCanonicalHeadUpperLDLAtRate.centeredMatrixCutoffLimit_leEv_rate_mul_diagonal
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorLocalCanonicalLDLBridge.FixedNomeCofinalVacuumSectorCanonicalHeadUpperClearedLDLAtRate.toVacuumSectorCenteredStrictGap
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorLocalCanonicalLDLBridge.FixedNomeCofinalVacuumSectorCanonicalHeadUpperClearedLDLAtRate.centeredMatrixCutoffLimit_leEv_rate_mul_diagonal
