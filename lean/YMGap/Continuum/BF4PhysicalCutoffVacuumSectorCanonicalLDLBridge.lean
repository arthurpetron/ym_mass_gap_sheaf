/-
# Canonical full-carrier LDL bridge to centered vacuum-sector limits

An ordinary, cleared, or upper-only canonical head-reduced LDL family acts on
the full finite positive carrier at a constructively cofinal sequence of
cutoffs.  The full-carrier contraction theorem shows that the zero extension
of each moving head-centered vacuum-sector coefficient is a valid centered
input and that its full forms are exactly the pulled same-object forms.

This module composes those facts.  Reindexing a one-parameter cofinal LDL
schedule by `max base threshold` constructs the two-parameter same-object
certificate, which then contracts to the centered Bishop-real form limits.

No cofinal LDL family or strict rate is constructed here.  No completed-space,
thermodynamic, continuum, or Clay conclusion is claimed.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalCutoffCofinalStrictGap
import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCenteredLimitGap
import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFullCarrierContraction
import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledUniformPoincareGap

namespace YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCanonicalLDLBridge

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffCanonicalHeadLDLGap
open YMGap.Continuum.BF4PhysicalCutoffCofinalStrictGap
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCenteredDiagonalCauchy
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCenteredLimitGap
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCenteredMatrixCauchy
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFormCauchy
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFormPushforward
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFullCarrierContraction
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorHeadCentering
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledUniformPoincareGap
open YMGap.Continuum.FiniteRationalCenteredRestrictionCertificate
open YMGap.Continuum.FiniteRationalLDLCertificate
open YMGap.Continuum.FiniteRationalReversibleSpectralCertificate

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Ordinary canonical LDL family -/

namespace FixedNomeCofinalCanonicalHeadLDLAtRate

/-- A cofinal family of ordinary canonical full-carrier LDL checks at one
strict rate constructs the exact same-object centered vacuum-sector
certificate consumed by the cutoff-limit theorem. -/
def toVacuumSectorCenteredStrictGap
    {w : Q'} {hw : (0 : Q') ≤ w} {half : Nat} {q : Q'}
    (hq0 : (0 : Q') ≤ q) (hq1 : q < (1 : Q'))
    (certificate : FixedNomeCofinalCanonicalHeadLDLAtRate
      w hw half q) :
    FixedNomeCofinalVacuumSectorCenteredStrictGap
      w hw half q where
  rate_nonnegative := hq0
  rate_lt_one := hq1
  anchor := fun base threshold =>
    certificate.anchor (max base threshold)
  anchor_ge := by
    intro base threshold
    exact certificate.anchor_ge (max base threshold)
  centeredGap := by
    intro base threshold coefficient
    let request := max base threshold
    let later := certificate.anchor request
    let moving :=
      centralPhysicalFinitePulledVacuumSectorHeadCenteredCoefficient
        w hw base later half coefficient
    let extended :=
      centralPhysicalFiniteVacuumSectorCoefficientExtension
        w hw base later half moving
    have hrequestLater : request ≤ later :=
      certificate.anchor_ge request
    have hbaseLater : base ≤ later :=
      Nat.le_trans (Nat.le_max_left base threshold) hrequestLater
    have hcenter :
        finiteWeightedMean
            (centralPhysicalFiniteCarrierSize w hw later half)
            (centralPhysicalFiniteWeight w hw later half)
            extended ≈ 0 :=
      centralPhysicalFiniteFullCarrierHeadCenteredExtension_meanZero
        hbaseLater coefficient
    have hldl :
        Q'.abs
            (finiteMatrixQuadratic
              (centralPhysicalFiniteCarrierSize w hw later half)
              (centralPhysicalFiniteKernel w hw later half)
              extended) ≤
          q * finiteDiagonalQuadratic
            (centralPhysicalFiniteCarrierSize w hw later half)
            (centralPhysicalFiniteWeight w hw later half)
            extended :=
      (certificate.certificate request).absContraction extended hcenter
    have hmatrix :
        finiteMatrixQuadratic
            (centralPhysicalFiniteCarrierSize w hw later half)
            (centralPhysicalFiniteKernel w hw later half)
            extended ≈
          centralPhysicalFinitePulledVacuumSectorMatrixQuadratic
            w hw base later half moving :=
      centralPhysicalFiniteFullCarrierCoefficientExtensionMatrix_eqv_pulled
        hbaseLater moving
    have hdiagonal :
        finiteDiagonalQuadratic
            (centralPhysicalFiniteCarrierSize w hw later half)
            (centralPhysicalFiniteWeight w hw later half)
            extended ≈
          centralPhysicalFinitePulledVacuumSectorDiagonalQuadratic
            w hw base later half moving :=
      centralPhysicalFiniteFullCarrierCoefficientExtensionDiagonal_eqv_pulled
        hbaseLater moving
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (Q'.abs_eqv_congr (Q'.eqv_symm hmatrix)))
      (Q'.le_trans' _ _ _ hldl
        (Q'.le_of_eqv
          (Q'.mul_eqv_congr_left q _ _ hdiagonal)))

/-- The ordinary cofinal canonical LDL family therefore proves the strict
comparison between the literal centered reflected-form and diagonal-form
cutoff limits for every fixed base-sector coefficient. -/
theorem centeredMatrixCutoffLimit_leEv_rate_mul_diagonal
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) {q : Q'}
    (hq0 : (0 : Q') ≤ q) (hq1 : q < (1 : Q'))
    (certificate : FixedNomeCofinalCanonicalHeadLDLAtRate
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

end FixedNomeCofinalCanonicalHeadLDLAtRate

/-! ## 2. Cleared-denominator canonical LDL family -/

namespace FixedNomeCofinalCanonicalHeadClearedLDLAtRate

/-- The shardable cleared-denominator canonical LDL family constructs the
same same-object centered vacuum-sector certificate. -/
def toVacuumSectorCenteredStrictGap
    {w : Q'} {hw : (0 : Q') ≤ w} {half : Nat} {q : Q'}
    (hq0 : (0 : Q') ≤ q) (hq1 : q < (1 : Q'))
    (certificate : FixedNomeCofinalCanonicalHeadClearedLDLAtRate
      w hw half q) :
    FixedNomeCofinalVacuumSectorCenteredStrictGap
      w hw half q where
  rate_nonnegative := hq0
  rate_lt_one := hq1
  anchor := fun base threshold =>
    certificate.anchor (max base threshold)
  anchor_ge := by
    intro base threshold
    exact certificate.anchor_ge (max base threshold)
  centeredGap := by
    intro base threshold coefficient
    let request := max base threshold
    let later := certificate.anchor request
    let moving :=
      centralPhysicalFinitePulledVacuumSectorHeadCenteredCoefficient
        w hw base later half coefficient
    let extended :=
      centralPhysicalFiniteVacuumSectorCoefficientExtension
        w hw base later half moving
    have hrequestLater : request ≤ later :=
      certificate.anchor_ge request
    have hbaseLater : base ≤ later :=
      Nat.le_trans (Nat.le_max_left base threshold) hrequestLater
    have hcenter :
        finiteWeightedMean
            (centralPhysicalFiniteCarrierSize w hw later half)
            (centralPhysicalFiniteWeight w hw later half)
            extended ≈ 0 :=
      centralPhysicalFiniteFullCarrierHeadCenteredExtension_meanZero
        hbaseLater coefficient
    have hldl :
        Q'.abs
            (finiteMatrixQuadratic
              (centralPhysicalFiniteCarrierSize w hw later half)
              (centralPhysicalFiniteKernel w hw later half)
              extended) ≤
          q * finiteDiagonalQuadratic
            (centralPhysicalFiniteCarrierSize w hw later half)
            (centralPhysicalFiniteWeight w hw later half)
            extended :=
      (certificate.certificate request).absContraction extended hcenter
    have hmatrix :
        finiteMatrixQuadratic
            (centralPhysicalFiniteCarrierSize w hw later half)
            (centralPhysicalFiniteKernel w hw later half)
            extended ≈
          centralPhysicalFinitePulledVacuumSectorMatrixQuadratic
            w hw base later half moving :=
      centralPhysicalFiniteFullCarrierCoefficientExtensionMatrix_eqv_pulled
        hbaseLater moving
    have hdiagonal :
        finiteDiagonalQuadratic
            (centralPhysicalFiniteCarrierSize w hw later half)
            (centralPhysicalFiniteWeight w hw later half)
            extended ≈
          centralPhysicalFinitePulledVacuumSectorDiagonalQuadratic
            w hw base later half moving :=
      centralPhysicalFiniteFullCarrierCoefficientExtensionDiagonal_eqv_pulled
        hbaseLater moving
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (Q'.abs_eqv_congr (Q'.eqv_symm hmatrix)))
      (Q'.le_trans' _ _ _ hldl
        (Q'.le_of_eqv
          (Q'.mul_eqv_congr_left q _ _ hdiagonal)))

/-- The cleared cofinal canonical LDL family proves the same strict
comparison between the centered form limits. -/
theorem centeredMatrixCutoffLimit_leEv_rate_mul_diagonal
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) {q : Q'}
    (hq0 : (0 : Q') ≤ q) (hq1 : q < (1 : Q'))
    (certificate : FixedNomeCofinalCanonicalHeadClearedLDLAtRate
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

end FixedNomeCofinalCanonicalHeadClearedLDLAtRate

/-! ## 3. Reflection-positive upper-only canonical LDL family -/

namespace FixedNomeCofinalCanonicalHeadUpperLDLAtRate

/-- A cofinal family of ordinary upper-only canonical checks supplies the
same-object absolute contraction: reflection positivity supplies the omitted
lower reduced-matrix obligation. -/
def toVacuumSectorCenteredStrictGap
    {w : Q'} {hw : (0 : Q') ≤ w} {half : Nat} {q : Q'}
    (hq0 : (0 : Q') ≤ q) (hq1 : q < (1 : Q'))
    (certificate : FixedNomeCofinalCanonicalHeadUpperLDLAtRate
      w hw half q) :
    FixedNomeCofinalVacuumSectorCenteredStrictGap
      w hw half q where
  rate_nonnegative := hq0
  rate_lt_one := hq1
  anchor := fun base threshold =>
    certificate.anchor (max base threshold)
  anchor_ge := by
    intro base threshold
    exact certificate.anchor_ge (max base threshold)
  centeredGap := by
    intro base threshold coefficient
    let request := max base threshold
    let later := certificate.anchor request
    let moving :=
      centralPhysicalFinitePulledVacuumSectorHeadCenteredCoefficient
        w hw base later half coefficient
    let extended :=
      centralPhysicalFiniteVacuumSectorCoefficientExtension
        w hw base later half moving
    have hrequestLater : request ≤ later :=
      certificate.anchor_ge request
    have hbaseLater : base ≤ later :=
      Nat.le_trans (Nat.le_max_left base threshold) hrequestLater
    have hcenter :
        finiteWeightedMean
            (centralPhysicalFiniteCarrierSize w hw later half)
            (centralPhysicalFiniteWeight w hw later half)
            extended ≈ 0 :=
      centralPhysicalFiniteFullCarrierHeadCenteredExtension_meanZero
        hbaseLater coefficient
    have hupper :
        finiteMatrixQuadratic
              (centralPhysicalFiniteCarrierSize w hw later half)
              (centralPhysicalFiniteKernel w hw later half)
              extended ≤
          q * finiteDiagonalQuadratic
            (centralPhysicalFiniteCarrierSize w hw later half)
            (centralPhysicalFiniteWeight w hw later half)
            extended :=
      (certificate.certificate request).upperContraction extended hcenter
    have hmatrix :
        finiteMatrixQuadratic
            (centralPhysicalFiniteCarrierSize w hw later half)
            (centralPhysicalFiniteKernel w hw later half)
            extended ≈
          centralPhysicalFinitePulledVacuumSectorMatrixQuadratic
            w hw base later half moving :=
      centralPhysicalFiniteFullCarrierCoefficientExtensionMatrix_eqv_pulled
        hbaseLater moving
    have hdiagonal :
        finiteDiagonalQuadratic
            (centralPhysicalFiniteCarrierSize w hw later half)
            (centralPhysicalFiniteWeight w hw later half)
            extended ≈
          centralPhysicalFinitePulledVacuumSectorDiagonalQuadratic
            w hw base later half moving :=
      centralPhysicalFiniteFullCarrierCoefficientExtensionDiagonal_eqv_pulled
        hbaseLater moving
    have hpulledNonnegative :
        (0 : Q') ≤
          centralPhysicalFinitePulledVacuumSectorMatrixQuadratic
            w hw base later half moving :=
      fixedBasePulledMovingMatrix_nonnegative
        base later half hbaseLater coefficient
    rw [YMGap.Constructive.ExpNeg.abs_of_nonneg hpulledNonnegative]
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.eqv_symm hmatrix))
      (Q'.le_trans' _ _ _ hupper
        (Q'.le_of_eqv
          (Q'.mul_eqv_congr_left q _ _ hdiagonal)))

/-- Ordinary upper-only canonical checks therefore prove the strict
same-object comparison between the reflected-form and diagonal-form cutoff
limits. -/
theorem centeredMatrixCutoffLimit_leEv_rate_mul_diagonal
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) {q : Q'}
    (hq0 : (0 : Q') ≤ q) (hq1 : q < (1 : Q'))
    (certificate : FixedNomeCofinalCanonicalHeadUpperLDLAtRate
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

end FixedNomeCofinalCanonicalHeadUpperLDLAtRate

/-! ## 4. Reflection-positive cleared upper-only canonical LDL family -/

namespace FixedNomeCofinalCanonicalHeadUpperClearedLDLAtRate

/-- Shardable cleared upper-only checks compile to the same same-object
absolute contraction, with the lower side again supplied by reflection
positivity. -/
def toVacuumSectorCenteredStrictGap
    {w : Q'} {hw : (0 : Q') ≤ w} {half : Nat} {q : Q'}
    (hq0 : (0 : Q') ≤ q) (hq1 : q < (1 : Q'))
    (certificate : FixedNomeCofinalCanonicalHeadUpperClearedLDLAtRate
      w hw half q) :
    FixedNomeCofinalVacuumSectorCenteredStrictGap
      w hw half q where
  rate_nonnegative := hq0
  rate_lt_one := hq1
  anchor := fun base threshold =>
    certificate.anchor (max base threshold)
  anchor_ge := by
    intro base threshold
    exact certificate.anchor_ge (max base threshold)
  centeredGap := by
    intro base threshold coefficient
    let request := max base threshold
    let later := certificate.anchor request
    let moving :=
      centralPhysicalFinitePulledVacuumSectorHeadCenteredCoefficient
        w hw base later half coefficient
    let extended :=
      centralPhysicalFiniteVacuumSectorCoefficientExtension
        w hw base later half moving
    have hrequestLater : request ≤ later :=
      certificate.anchor_ge request
    have hbaseLater : base ≤ later :=
      Nat.le_trans (Nat.le_max_left base threshold) hrequestLater
    have hcenter :
        finiteWeightedMean
            (centralPhysicalFiniteCarrierSize w hw later half)
            (centralPhysicalFiniteWeight w hw later half)
            extended ≈ 0 :=
      centralPhysicalFiniteFullCarrierHeadCenteredExtension_meanZero
        hbaseLater coefficient
    have hupper :
        finiteMatrixQuadratic
              (centralPhysicalFiniteCarrierSize w hw later half)
              (centralPhysicalFiniteKernel w hw later half)
              extended ≤
          q * finiteDiagonalQuadratic
            (centralPhysicalFiniteCarrierSize w hw later half)
            (centralPhysicalFiniteWeight w hw later half)
            extended :=
      (certificate.certificate request).upperContraction extended hcenter
    have hmatrix :
        finiteMatrixQuadratic
            (centralPhysicalFiniteCarrierSize w hw later half)
            (centralPhysicalFiniteKernel w hw later half)
            extended ≈
          centralPhysicalFinitePulledVacuumSectorMatrixQuadratic
            w hw base later half moving :=
      centralPhysicalFiniteFullCarrierCoefficientExtensionMatrix_eqv_pulled
        hbaseLater moving
    have hdiagonal :
        finiteDiagonalQuadratic
            (centralPhysicalFiniteCarrierSize w hw later half)
            (centralPhysicalFiniteWeight w hw later half)
            extended ≈
          centralPhysicalFinitePulledVacuumSectorDiagonalQuadratic
            w hw base later half moving :=
      centralPhysicalFiniteFullCarrierCoefficientExtensionDiagonal_eqv_pulled
        hbaseLater moving
    have hpulledNonnegative :
        (0 : Q') ≤
          centralPhysicalFinitePulledVacuumSectorMatrixQuadratic
            w hw base later half moving :=
      fixedBasePulledMovingMatrix_nonnegative
        base later half hbaseLater coefficient
    rw [YMGap.Constructive.ExpNeg.abs_of_nonneg hpulledNonnegative]
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.eqv_symm hmatrix))
      (Q'.le_trans' _ _ _ hupper
        (Q'.le_of_eqv
          (Q'.mul_eqv_congr_left q _ _ hdiagonal)))

/-- Cleared upper-only canonical checks prove the same strict comparison of
the centered same-object form limits. -/
theorem centeredMatrixCutoffLimit_leEv_rate_mul_diagonal
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) {q : Q'}
    (hq0 : (0 : Q') ≤ q) (hq1 : q < (1 : Q'))
    (certificate : FixedNomeCofinalCanonicalHeadUpperClearedLDLAtRate
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

end FixedNomeCofinalCanonicalHeadUpperClearedLDLAtRate

end YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCanonicalLDLBridge

#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCanonicalLDLBridge.FixedNomeCofinalCanonicalHeadLDLAtRate.toVacuumSectorCenteredStrictGap
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCanonicalLDLBridge.FixedNomeCofinalCanonicalHeadLDLAtRate.centeredMatrixCutoffLimit_leEv_rate_mul_diagonal
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCanonicalLDLBridge.FixedNomeCofinalCanonicalHeadClearedLDLAtRate.toVacuumSectorCenteredStrictGap
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCanonicalLDLBridge.FixedNomeCofinalCanonicalHeadClearedLDLAtRate.centeredMatrixCutoffLimit_leEv_rate_mul_diagonal
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCanonicalLDLBridge.FixedNomeCofinalCanonicalHeadUpperLDLAtRate.toVacuumSectorCenteredStrictGap
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCanonicalLDLBridge.FixedNomeCofinalCanonicalHeadUpperLDLAtRate.centeredMatrixCutoffLimit_leEv_rate_mul_diagonal
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCanonicalLDLBridge.FixedNomeCofinalCanonicalHeadUpperClearedLDLAtRate.toVacuumSectorCenteredStrictGap
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCanonicalLDLBridge.FixedNomeCofinalCanonicalHeadUpperClearedLDLAtRate.centeredMatrixCutoffLimit_leEv_rate_mul_diagonal
