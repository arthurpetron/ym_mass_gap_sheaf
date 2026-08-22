/-
# Axiom audit for the canonical cutoff-two vacuum-sector gap

The implementation modules omit repeated recursive axiom reports so their
large certified dependency graph can be compiled through compact opaque
interfaces.  This leaf module performs the single audit that matters: the
fully contracted finite theorem.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalVacuumGap

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalVacuumGap.cutoffTwoCanonicalVacuumSector_exact_and_strict_abs_gap
