/-
# Exact corrected-slab normalization at the fundamental cutoff

At cutoff one, every nonzero fixed-interface label is the odd fundamental
SU(2) character.  The selected exposed-link Haar theorem therefore kills the
entire non-vacuum vacuum--vacuum tail.  Combining this with the literal slab
reflection theorem gives an unconditional exact normalization certificate at
`K = 1`, uniformly in the rational coupling.

The all-spin even-label continuation remains separate; this module does not
promote the cutoff-one result to arbitrary cutoff.
-/

import YMGap.Continuum.BF4ExactSlabVacuumSelectedHaar
import YMGap.Continuum.BF4ExactSlabGroupedAFComparison

namespace YMGap.Continuum.BF4ExactSlabVacuumCutoffOneNormalization

open YMGap.Constructive
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactSlabGroupedAFComparison
open YMGap.Continuum.BF4ExactSlabVacuumFixedFaceGeometry
open YMGap.Continuum.BF4ExactSlabVacuumReflection
open YMGap.Continuum.BF4ExactSlabVacuumSelectedHaar

local infix:50 " ≈ " => Q'.eqv

/-- The literal vacuum partition is exactly one at the fundamental cutoff,
for every rational heat-kernel parameter. -/
theorem exactSlabVacuumPartition_cutoff_one_eqv_one (w : Q') :
    exactSlabVacuumPartition w 1 ≈ 1 := by
  exact exactSlabVacuumPartition_eqv_one_of_nontrivial_terms_vanish
    (exactSlabVacuumNontrivialTermsVanish_of_haar
      exactVacuumNontrivialHaarTermsVanish_cutoff_one w)

/-- Exact strict vacuum positivity at `K = 1`. -/
theorem exactSlabVacuumPartition_cutoff_one_pos (w : Q') :
    (0 : Q') < exactSlabVacuumPartition w 1 := by
  exact exactSlabVacuumPartition_pos_of_nontrivial_terms_vanish
    (exactSlabVacuumNontrivialTermsVanish_of_haar
      exactVacuumNontrivialHaarTermsVanish_cutoff_one w)

/-- Literal source/target reflection symmetry at the same fundamental
cutoff.  The underlying reflection theorem is in fact valid at every
cutoff; this specialization records the second field of the exact
cutoff-one normalization gate explicitly. -/
theorem exactSlabRawKernel_cutoff_one_symmetric
    (w : Q')
    (left right :
      YMGap.Continuum.SU2FundamentalPentagonFiniteGraph.EdgeLabelling) :
    exactSlabRawKernel w 1 left right ≈
      exactSlabRawKernel w 1 right left := by
  exact exactCorrectedSlabReflectedKernel_symmetric w 1 left right

/-- Exact vacuum positivity plus literal all-row reflection symmetry at the
fundamental cutoff. -/
def exactSlabNormalizationData_cutoff_one (w : Q') :
    ExactSlabNormalizationData w 1 :=
  ExactSlabNormalizationData.ofHaarNontrivialTermsVanish
    exactVacuumNontrivialHaarTermsVanish_cutoff_one

end YMGap.Continuum.BF4ExactSlabVacuumCutoffOneNormalization

#print axioms YMGap.Continuum.BF4ExactSlabVacuumSelectedHaar.exactVacuumNontrivialHaarTermsVanish_cutoff_one
#print axioms YMGap.Continuum.BF4ExactSlabVacuumCutoffOneNormalization.exactSlabVacuumPartition_cutoff_one_eqv_one
#print axioms YMGap.Continuum.BF4ExactSlabVacuumCutoffOneNormalization.exactSlabVacuumPartition_cutoff_one_pos
#print axioms YMGap.Continuum.BF4ExactSlabVacuumCutoffOneNormalization.exactSlabRawKernel_cutoff_one_symmetric
#print axioms YMGap.Continuum.BF4ExactSlabVacuumCutoffOneNormalization.exactSlabNormalizationData_cutoff_one
