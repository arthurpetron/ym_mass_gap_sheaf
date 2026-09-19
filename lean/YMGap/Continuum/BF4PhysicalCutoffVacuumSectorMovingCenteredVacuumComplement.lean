/-
# A concrete nonzero vector in the completed physical vacuum complement

The moving-centered cutoff-one cube observable has already been constructed in
the actual cutoff-removed physical completion.  Separate preceding modules
prove its vacuum orthogonality and prove that it is not the completed zero
vector.  This module contracts those two facts into the subtype that is
consumed by the completed vacuum-complement transfer machinery.

The result is a fixed-nome, fixed-half-extent SU(2) witness.  It is not a
thermodynamic or continuum construction, and it does not identify a transfer
moment or a spectral gap.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
`noncomputable` declaration is used.
-/

import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorMovingCenteredNonzero

namespace YMGap.Continuum.BF4PhysicalCutoffVacuumSectorMovingCenteredVacuumComplement

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedAlgebra
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedVacuumComplement
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorMovingCenteredCompletion
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorMovingCenteredNonzero
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorMovingCenteredVacuumOrthogonal

/-! ## The explicit completed complement witness -/

/-- The moving-centered cutoff-one cube vector, packaged with its proved
vacuum-orthogonality, as an inhabitant of the actual completed complement. -/
def centralPhysicalCutoffOneCubeMovingCenteredVacuumComplement
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    CentralPhysicalCutoffCompletedVacuumComplement hw0 hw1 0 :=
  ⟨centralPhysicalVacuumSectorMovingCenteredGlobalVector
      hw0 hw1 1 0
      (centralPhysicalCutoffOneCubeIndicatorCoefficient w hw0),
    centralPhysicalVacuumSectorMovingCenteredGlobalVector_vacuumOrthogonal
      hw0 hw1 1 0
      (centralPhysicalCutoffOneCubeIndicatorCoefficient w hw0)⟩

/-- The explicit completed-complement witness is nonzero in the ambient
physical completion. -/
theorem centralPhysicalCutoffOneCubeMovingCenteredVacuumComplement_ne_zero
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    (centralPhysicalCutoffOneCubeMovingCenteredVacuumComplement
      hw0 hw1).1 ≠ completedPhysicalLinearZero hw0 hw1 0 := by
  intro hzero
  exact centralPhysicalCutoffOneCubeMovingCenteredGlobalVector_ne_zero
    hw0 hw1 hzero

end YMGap.Continuum.BF4PhysicalCutoffVacuumSectorMovingCenteredVacuumComplement

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorMovingCenteredVacuumComplement.centralPhysicalCutoffOneCubeMovingCenteredVacuumComplement
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorMovingCenteredVacuumComplement.centralPhysicalCutoffOneCubeMovingCenteredVacuumComplement_ne_zero
