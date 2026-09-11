/-
# BF4 inward-mate label maps

The physical BF4 inward mate changes an even label by `0 -> 1` at the vacuum
and by predecessor lowering away from the vacuum.  An odd label is positive,
so its mate is simply its predecessor.

This tiny module deliberately isolates the combinatorial label maps from both
the heat-weight estimates and the SU(2) fusion analysis.  Those two compilers
can therefore depend on the same definitions without importing one another.

No `Classical`, choice, `native_decide`, `sorry`, custom axiom, noncomputable
declaration, or trusted external computation is used.
-/

namespace YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateHeatBound

/-- The parity-changing inward mate of an even label: `0 -> 1`, while every
positive label loses one unit. -/
def evenInwardMateLabel (spin : Nat) : Nat :=
  if spin = 0 then 1 else spin - 1

/-- The inward mate of a positive odd label is its predecessor. -/
def oddInwardMateLabel (spin : Nat) : Nat := spin - 1

end YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateHeatBound

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateHeatBound.evenInwardMateLabel
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateHeatBound.oddInwardMateLabel
