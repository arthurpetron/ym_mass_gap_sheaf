/-
# Exact inverse-fiber threshold after the complete component-code audit

The retained fine-intertwiner disintegration assigns unit counting weight to
every accepted auxiliary witness.  Hence the failed `4^12` factor cannot be
removed by appealing to a hidden auxiliary Boltzmann weight.  What remains is
an inverse-fiber counting problem.

The already-faithful structural words have base

  625 * 4 * 16 = 40000.

Against the proved face payment `1 / 32000000`, this leaves an exact auxiliary
branching budget of 800 per peeled copy.  Equality at 800 is critical; a fixed
base of 799 gives the explicit strict ratio `799 / 800`.

This module records that numerical contract in kernel-checked rational
arithmetic.  It does not assert the still-open inverse-fiber bound.

Constructive contract: definitions and decidable rational arithmetic only.
No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom,
noncomputable declaration, or enlarged heartbeat budget.
-/

import YMGap.Continuum.CompactDualSlabFaceStrandComponentEntropyCarrier
import YMGap.Continuum.BF4SU2FineIntertwinerPhysicalDisintegration

namespace YMGap.Continuum.CompactDualSlabFaceStrandComponentEntropyThreshold

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.CompactDualSlabFaceStrandComponentEntropyCarrier
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

/-- The code base already consumed by shape, physical multiplicity, and row
presence, before storing auxiliary row values. -/
def componentStructuralEntropyBase : Nat := 625 * 4 * 16

theorem componentStructuralEntropyBase_eq :
    componentStructuralEntropyBase = 40000 := by
  rfl

/-- Structural entropy times the one-copy heat payment. -/
def componentStructuralAnchorRatio : Q' :=
  Q'.ofNat componentStructuralEntropyBase * anchorFaceCoefficient

/-- Exactly one eight-hundredth of the available mass remains after paying
the three structural carriers. -/
theorem componentStructuralAnchorRatio_eqv_one_800 :
    componentStructuralAnchorRatio ≈ Q'.mkPos 1 800 (by decide) := by
  decide

theorem componentStructuralAnchorRatio_lt_one :
    componentStructuralAnchorRatio < (1 : Q') := by
  decide

/-- The largest convenient integral auxiliary branching base with a strict
reserve against the current heat payment. -/
def strictAuxiliaryBranchingBase : Nat := 799

/-- The total candidate ratio if the remaining inverse auxiliary fiber is
bounded by `799^peelSize`. -/
def strictComponentEntropyAnchorRatio : Q' :=
  Q'.ofNat strictAuxiliaryBranchingBase * componentStructuralAnchorRatio

theorem strictComponentEntropyAnchorRatio_eqv_799_800 :
    strictComponentEntropyAnchorRatio ≈
      Q'.mkPos 799 800 (by decide) := by
  decide

theorem strictComponentEntropyAnchorRatio_lt_one :
    strictComponentEntropyAnchorRatio < (1 : Q') := by
  decide

/-- Base 800 exhausts the reserve exactly and therefore cannot yield a strict
component contraction. -/
def criticalComponentEntropyAnchorRatio : Q' :=
  Q'.ofNat 800 * componentStructuralAnchorRatio

theorem criticalComponentEntropyAnchorRatio_eqv_one :
    criticalComponentEntropyAnchorRatio ≈ (1 : Q') := by
  decide

/-- The raw auxiliary weak-composition base lies far beyond the strict
inverse-fiber budget. -/
theorem strictAuxiliaryBranchingBase_lt_rawAuxiliaryBase :
    strictAuxiliaryBranchingBase < 4 ^ 12 := by
  decide

#print axioms componentStructuralEntropyBase
#print axioms componentStructuralEntropyBase_eq
#print axioms componentStructuralAnchorRatio
#print axioms componentStructuralAnchorRatio_eqv_one_800
#print axioms componentStructuralAnchorRatio_lt_one
#print axioms strictAuxiliaryBranchingBase
#print axioms strictComponentEntropyAnchorRatio
#print axioms strictComponentEntropyAnchorRatio_eqv_799_800
#print axioms strictComponentEntropyAnchorRatio_lt_one
#print axioms criticalComponentEntropyAnchorRatio
#print axioms criticalComponentEntropyAnchorRatio_eqv_one
#print axioms strictAuxiliaryBranchingBase_lt_rawAuxiliaryBase

end YMGap.Continuum.CompactDualSlabFaceStrandComponentEntropyThreshold
