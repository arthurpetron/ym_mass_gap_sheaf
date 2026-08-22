/-
# Cofinal genuine local slices imply the fixed-nome physical BF4 gap

The preceding adapter reduces the fixed-nome gap to cofinal bounds on the
literal physical centered row mass.  The local-contraction layer already
proves each such row bound at rate `1/16` from one genuine stationary slice:
exact row and column normalization, exact all-label density gluing, and a
one-step centered rate at most `1/4`.

This file packages a constructively cofinal family of those genuine local
slice witnesses and compiles it to the global centered gap and the moving
same-object vacuum-sector cutoff-limit inequality.

No local slice family is constructed here.  The gluing identity and local
quarter bound remain the analytic producer obligation.  Hence this file does
not claim a physical gap, thermodynamic limit, continuum theory, or Clay
conclusion.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalLocalGluingAFCertificate
import YMGap.Continuum.BF4PhysicalCutoffCofinalCenteredRowGap

namespace YMGap.Continuum.BF4PhysicalCutoffCofinalLocalSliceGap

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum.BF4CommonRankOneRowTriangle
open YMGap.Continuum.BF4LocalContractionGluing
open YMGap.Continuum.BF4PhysicalCutoffCofinalCenteredRowGap
open YMGap.Continuum.BF4PhysicalCutoffCofinalConnectedGap
open YMGap.Continuum.BF4PhysicalCutoffConnectedGap
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCenteredDiagonalCauchy
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCenteredLimitGap
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCenteredMatrixCauchy
open YMGap.Continuum.BF4PhysicalLocalGluingAFCertificate
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiveHolonomyPerronCutoff
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph

/-! ## 1. Cofinal genuine local-slice data -/

/-- A generic constructively cofinal family of witnesses. -/
structure CofinalWitnessFamily (Witness : Nat → Type 1) : Type 1 where
  anchor : Nat → Nat
  anchor_ge : ∀ base, base ≤ anchor base
  witness : ∀ base, Witness (anchor base)

/-- One genuine physical local slice at a fixed representation cutoff,
together with the numerical quarter estimate consumed by tensorization. -/
structure FixedNomePhysicalLocalSliceWitness
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat) : Type 1 where
  depth : Nat
  oneStep : EdgeLabelling → EdgeLabelling → Q'
  qS : Q'
  qS_le_quarter : qS ≤ quarter
  slice : PhysicalBF4LocalSliceGluing
    hw cutoff half depth oneStep qS

/-- A constructively cofinal family of genuine local slice witnesses for one
fixed nome and spatial half-extent. -/
abbrev FixedNomeCofinalPhysicalLocalSliceGluing
    (w : Q') (hw : (0 : Q') ≤ w) (half : Nat) : Type 1 :=
  CofinalWitnessFamily
    (fun cutoff =>
      FixedNomePhysicalLocalSliceWitness w hw cutoff half)

namespace FixedNomeCofinalPhysicalLocalSliceGluing

/-! ## 2. Contraction to the physical row and gap interfaces -/

/-- Genuine local slices on a cofinal cutoff schedule produce the literal
physical centered-row family at the uniform rate `1/16`. -/
def toCenteredRowDistance
    {w : Q'} {hw : (0 : Q') ≤ w} {half : Nat}
    (family : FixedNomeCofinalPhysicalLocalSliceGluing w hw half) :
    FixedNomeCofinalPhysicalCenteredRowDistance
      w hw half physicalCutoffSixteenth where
  rate_nonnegative := physicalCutoffSixteenth_nonnegative
  rate_lt_one := physicalCutoffSixteenth_lt_one
  anchor := family.anchor
  anchor_ge := family.anchor_ge
  rowDistance := by
    intro base source hsource
    let witness := family.witness base
    change physicalCenteredPhysicalRowMass
        w hw (family.anchor base) half source ≤
      Q'.mkPos 1 16 (by decide) *
        centralPhysicalRowMarginal
          w hw (family.anchor base) half source
    exact (witness.slice.toRow source hsource)
      |>.physical_centered_row_le_sixteenth witness.qS_le_quarter

/-- The cofinal genuine local slices supply the global fixed-nome centered
strict-gap interface. -/
def toCenteredStrictGap
    {w : Q'} {hw : (0 : Q') ≤ w} {half : Nat}
    (family : FixedNomeCofinalPhysicalLocalSliceGluing w hw half) :=
  family.toCenteredRowDistance.toCenteredStrictGap

/-- The cofinal genuine local slices also supply the moving same-object
vacuum-sector certificate. -/
def toVacuumSectorCenteredStrictGap
    {w : Q'} {hw : (0 : Q') ≤ w} {half : Nat}
    (family : FixedNomeCofinalPhysicalLocalSliceGluing w hw half) :=
  family.toCenteredRowDistance.toVacuumSectorCenteredStrictGap

/-- Cofinal genuine local slice gluing therefore proves the strict
`1/16` comparison between the moving centered form limits. -/
theorem centeredMatrixCutoffLimit_leEv_sixteenth_mul_diagonal
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (family : FixedNomeCofinalPhysicalLocalSliceGluing
      w (Q'.le_of_lt hw0) half)
    (base : Nat) (coefficient : Nat → Q') :
    CReal.leEv
      (centralPhysicalFinitePulledVacuumSectorHeadCenteredMatrixCutoffLimit
        hw0 hw1 base half coefficient)
      (CReal.mul
        (CReal.ofQ' physicalCutoffSixteenth)
        (centralPhysicalFinitePulledVacuumSectorHeadCenteredDiagonalCutoffLimit
          hw0 hw1 base half coefficient)) :=
  FixedNomeCofinalPhysicalCenteredRowDistance.centeredMatrixCutoffLimit_leEv_rate_mul_diagonal
    hw0 hw1 half family.toCenteredRowDistance base coefficient

end FixedNomeCofinalPhysicalLocalSliceGluing

/-! ## 3. Adapter from the established cofinal local-gluing certificate -/

namespace FixedNomeCofinalLocalGluing

/-- The repository's established cofinal local-gluing package is exactly a
cofinal family of the genuine local-slice witnesses used above. -/
def toPhysicalLocalSliceGluing
    {w : Q'} {hw : (0 : Q') ≤ w} {half : Nat}
    (certificate : FixedNomeCofinalLocalGluing w hw half) :
    FixedNomeCofinalPhysicalLocalSliceGluing w hw half where
  anchor := certificate.anchor
  anchor_ge := certificate.anchor_ge
  witness := fun base =>
    { depth := certificate.depth base
      oneStep := certificate.oneStep base
      qS := certificate.localRate base
      qS_le_quarter := certificate.localRate_le_quarter base
      slice := certificate.localSlice base }

/-- Existing cofinal local-gluing data therefore proves the moving
same-object `1/16` cutoff-limit inequality directly. -/
theorem centeredMatrixCutoffLimit_leEv_sixteenth_mul_diagonal
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (certificate : FixedNomeCofinalLocalGluing
      w (Q'.le_of_lt hw0) half)
    (base : Nat) (coefficient : Nat → Q') :
    CReal.leEv
      (centralPhysicalFinitePulledVacuumSectorHeadCenteredMatrixCutoffLimit
        hw0 hw1 base half coefficient)
      (CReal.mul
        (CReal.ofQ' physicalCutoffSixteenth)
        (centralPhysicalFinitePulledVacuumSectorHeadCenteredDiagonalCutoffLimit
          hw0 hw1 base half coefficient)) :=
  FixedNomeCofinalPhysicalLocalSliceGluing.centeredMatrixCutoffLimit_leEv_sixteenth_mul_diagonal
    hw0 hw1 half (toPhysicalLocalSliceGluing certificate) base coefficient

end FixedNomeCofinalLocalGluing

/-! ## Axiom audit -/

#print axioms FixedNomeCofinalPhysicalLocalSliceGluing.toCenteredRowDistance
#print axioms FixedNomeCofinalPhysicalLocalSliceGluing.toCenteredStrictGap
#print axioms FixedNomeCofinalPhysicalLocalSliceGluing.toVacuumSectorCenteredStrictGap
#print axioms FixedNomeCofinalPhysicalLocalSliceGluing.centeredMatrixCutoffLimit_leEv_sixteenth_mul_diagonal
#print axioms FixedNomeCofinalLocalGluing.toPhysicalLocalSliceGluing
#print axioms FixedNomeCofinalLocalGluing.centeredMatrixCutoffLimit_leEv_sixteenth_mul_diagonal

end YMGap.Continuum.BF4PhysicalCutoffCofinalLocalSliceGap
