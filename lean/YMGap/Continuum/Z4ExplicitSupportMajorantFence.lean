/-
# Kernel fence for the cutoff-cardinality support majorant

The support-sized estimate is volume independent, but its link factor uses the
largest possible number of auxiliary fusion channels.  At the first nonzero
physical cutoff this file evaluates that envelope exactly.  The resulting
one-plaquette base is already much larger than one, so no counting or polymer
argument downstream can turn this particular worst-case envelope into a
contractive activity.  Any successful continuation must retain spin-dependent
heat-kernel decay before maximizing the fusion multiplicities.
-/

import YMGap.Continuum.Z4ExplicitSupportMultiplicityBound

namespace YMGap.Continuum.Z4ExplicitSupportMajorantFence

open YMGap.Constructive
open YMGap.Continuum.SU2PeterWeylWilsonBlock
open YMGap.Continuum.Z4ExplicitSupportMultiplicityBound
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff

local infix:50 " ≈ " => Q'.eqv

/-- The per-excited-plaquette base furnished by the crude support majorant. -/
def crudeSupportBase (K : Nat) : Q' :=
  quarter * linkMultiplicityBound K ^ 4

theorem linkAuxiliaryCutoff_one : linkAuxiliaryCutoff 1 = 6 := by
  decide

theorem localMultiplicityNatBound_six :
    localMultiplicityNatBound 6 = 343 := by
  decide

theorem linkMultiplicityBound_one_eqv :
    linkMultiplicityBound 1 ≈ Q'.ofNat 343 := by
  decide

/-- Exact value of the crude one-plaquette activity envelope at cutoff one. -/
theorem crudeSupportBase_one_exact :
    crudeSupportBase 1 ≈ Q'.mkPos 13841287201 4 (by decide) := by
  decide

/-- The literal cutoff-cardinality envelope is not contractive even at `K=1`. -/
theorem crudeSupportBase_one_gt_one :
    (1 : Q') < crudeSupportBase 1 := by
  decide

theorem crudeSupportBase_one_not_le_one :
    ¬ crudeSupportBase 1 ≤ (1 : Q') := by
  decide

end YMGap.Continuum.Z4ExplicitSupportMajorantFence

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4ExplicitSupportMajorantFence.crudeSupportBase_one_exact
#print axioms YMGap.Continuum.Z4ExplicitSupportMajorantFence.crudeSupportBase_one_gt_one
#print axioms YMGap.Continuum.Z4ExplicitSupportMajorantFence.crudeSupportBase_one_not_le_one
