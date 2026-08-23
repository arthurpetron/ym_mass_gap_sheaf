/-
# Cofinal sector-local upper PSD certificates reach completion

An upper PSD witness for the generated sector-local centered restriction is
order-invariant and strictly weaker than exhibiting a triangular LDL table.
This module isolates the exact unbounded input still needed after the
cutoff-two witness: one strict rate and physical mean-zero signed-form gaps on
a constructively cofinal schedule.  It packages those gaps as generated upper
PSD certificates and contracts them through the same-object CReal limit to
the actual completed vacuum-sector transfer contraction.

No such cofinal finite-gap family is constructed here.  In particular this
module supplies no volume- or spacing-uniform estimate, thermodynamic or
continuum limit, QFT reconstruction, or Clay conclusion.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalCutoffLinearMarkovJointAdaptiveCauchySchwarz
import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorLocalCanonicalLDLBridge

namespace YMGap.Continuum.BF4PhysicalCutoffVacuumSectorLocalUpperPSDCofinalBridge

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovJointAdaptiveCauchySchwarz
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorBlockDecomposition
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCenteredDiagonalCauchy
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCenteredLimitGap
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedGap
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorLocalCanonicalLDLBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector

local infix:50 " ≈ " => Q'.eqv

/-- The direct finite signed-form frontier: a single strict rate and exact
physical vacuum-sector gaps along a constructively cofinal cutoff schedule. -/
structure FixedNomeCofinalVacuumSectorFiniteStrictGap
    (w : Q') (hw : (0 : Q') ≤ w) (half : Nat) (q : Q') : Type 1 where
  rate_nonnegative : (0 : Q') ≤ q
  rate_lt_one : q < (1 : Q')
  anchor : Nat → Nat
  anchor_ge : ∀ request, request ≤ anchor request
  sectorGap : ∀ request (coefficient : Nat → Q'),
    centralPhysicalFiniteVacuumSectorWeightedMean
        w hw (anchor request) half coefficient ≈ 0 →
      Q'.abs
          (centralPhysicalFiniteVacuumSectorMatrixQuadratic
            w hw (anchor request) half coefficient) ≤
        q * centralPhysicalFiniteVacuumSectorDiagonalQuadratic
          w hw (anchor request) half coefficient

namespace FixedNomeCofinalVacuumSectorFiniteStrictGap

/-- Recode every physical signed-form estimate into upper PSD of the exact
generated canonical restriction at the same cofinal cutoff. -/
def toCanonicalHeadUpperPSDAtRate
    {w : Q'} {hw : (0 : Q') ≤ w} {half : Nat} {q : Q'}
    (family : FixedNomeCofinalVacuumSectorFiniteStrictGap
      w hw half q) :
    FixedNomeCofinalVacuumSectorCanonicalHeadUpperPSDAtRate
      w hw half q where
  anchor := family.anchor
  anchor_ge := family.anchor_ge
  certificate := by
    intro request
    exact
      CentralPhysicalFiniteVacuumSectorCanonicalHeadUpperPSDCertificate.ofMeanZeroAbsGap
        (family.sectorGap request)

/-- The cofinal finite sector gaps imply the existing same-object moving
centered strict-gap interface. -/
def toVacuumSectorCenteredStrictGap
    {w : Q'} {hw : (0 : Q') ≤ w} {half : Nat} {q : Q'}
    (family : FixedNomeCofinalVacuumSectorFiniteStrictGap
      w hw half q) :
    FixedNomeCofinalVacuumSectorCenteredStrictGap w hw half q :=
  family.toCanonicalHeadUpperPSDAtRate.toVacuumSectorCenteredStrictGap
    family.rate_nonnegative family.rate_lt_one

/-- The finite cofinal signed-form frontier reaches the actual completed
vacuum-sector transfer contraction; completed positive-form Cauchy--Schwarz
is already constructed independently. -/
def toCompletedStrictContractionData
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) {q : Q'}
    (family : FixedNomeCofinalVacuumSectorFiniteStrictGap
      w (Q'.le_of_lt hw0) half q) :
    CentralPhysicalVacuumSectorCylinderCompletedStrictContractionData
      hw0 hw1 half :=
  centralPhysicalVacuumSectorCylinderCompletedStrictContractionDataAtSectorRate
    hw0 hw1 half family.toVacuumSectorCenteredStrictGap

end FixedNomeCofinalVacuumSectorFiniteStrictGap

namespace FixedNomeCofinalVacuumSectorCanonicalHeadUpperPSDAtRate

/-- Equivalently, a cofinal generated upper-PSD family plus the two strict
rate inequalities reaches the completed transfer contraction directly. -/
def toCompletedStrictContractionData
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) {q : Q'}
    (hq0 : (0 : Q') ≤ q) (hq1 : q < (1 : Q'))
    (certificate :
      FixedNomeCofinalVacuumSectorCanonicalHeadUpperPSDAtRate
        w (Q'.le_of_lt hw0) half q) :
    CentralPhysicalVacuumSectorCylinderCompletedStrictContractionData
      hw0 hw1 half :=
  centralPhysicalVacuumSectorCylinderCompletedStrictContractionDataAtSectorRate
    hw0 hw1 half
    (certificate.toVacuumSectorCenteredStrictGap hq0 hq1)

end FixedNomeCofinalVacuumSectorCanonicalHeadUpperPSDAtRate

end YMGap.Continuum.BF4PhysicalCutoffVacuumSectorLocalUpperPSDCofinalBridge

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorLocalUpperPSDCofinalBridge.FixedNomeCofinalVacuumSectorFiniteStrictGap.toCanonicalHeadUpperPSDAtRate
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorLocalUpperPSDCofinalBridge.FixedNomeCofinalVacuumSectorFiniteStrictGap.toVacuumSectorCenteredStrictGap
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorLocalUpperPSDCofinalBridge.FixedNomeCofinalVacuumSectorFiniteStrictGap.toCompletedStrictContractionData
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorLocalUpperPSDCofinalBridge.FixedNomeCofinalVacuumSectorCanonicalHeadUpperPSDAtRate.toCompletedStrictContractionData
