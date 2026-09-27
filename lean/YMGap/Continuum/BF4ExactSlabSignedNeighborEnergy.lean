/-
# Only neighboring signed pairs can reduce the original residual-sum square

The finite residual sum uses the ACTUAL full-action completed conditional
projections. Its norm square equals the original conditional Dirichlet energy
plus the ordered distinct-neighbor cross pairings plus nonnegative remote
squares. No original action factor, mean, or inner product is replaced.

Every retained row has at most 25 links, independent of volume and nome.
This does not bound the negative neighboring terms: a useful signed lower
estimate remains open. These operators are conditional-link dynamics, not
the physical OS time transfer or Hamiltonian.
-/

import YMGap.Continuum.GNSProjectionSignedEnergy
import YMGap.Continuum.BF4ExactSlabConditionalSweepEnergy

namespace YMGap.Continuum.BF4ExactSlabSignedNeighborEnergy

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.GNSProjectionSweep
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactSlabConditionalSweep
open YMGap.Continuum.BF4ExactSlabConditionalSweepEnergy
open YMGap.Continuum.BF4ExactSlabEightLayerCone
open YMGap.Continuum.BF4ExactSlabWardStarGeometry
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabStarFullActionProbe
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

private instance (extent : Nat) : DecidableEq (PhysicalLink extent) :=
  inferInstanceAs (DecidableEq {link : Z4Link // link ∈ boundaryCompleteSlabLinks extent})

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K extent : Nat) (hK : headCutoff w ≤ K)

local notation "F" => fullData hw0 hw1 K extent hK
local notation "P" => projections hw0 hw1 K extent hK

/-- All original physical links, each occurring exactly once. -/
def conditionalGenerator (x : GNSCompletionSpace F) : GNSCompletionSpace F :=
  (P).residualSum (schedule extent) x

/-- Signed and ordered distinct-neighbor pairs, at the SAME completed state. -/
def signedNeighborEnergy (x : GNSCompletionSpace F) : RC :=
  (P).neighboringCross adjacent (schedule extent) x

/-- Exact remote remainder; each entry is an actual composed-residual square. -/
def remoteEnergy (x : GNSCompletionSpace F) : RC :=
  (P).remoteSquares adjacent (schedule extent) x

private theorem adjacent_refl (i : PhysicalLink extent) : adjacent i i = true :=
  decide_eq_true (List.mem_cons_self : Near extent i.val i.val)

/-- The generator's quadratic form is the existing original conditional energy. -/
theorem conditionalGenerator_energy (x : GNSCompletionSpace F) :
    (F).cinnerCompl (conditionalGenerator hw0 hw1 K extent hK x) x =
      (P).finalEnergy (schedule extent) x :=
  (P).residualSum_self_pairing (schedule extent) x

/-- No analytic hypothesis: exact decomposition of the original H-squared
quadratic form into its diagonal, signed neighboring, and positive remote parts. -/
theorem conditionalGenerator_square (x : GNSCompletionSpace F) :
    normSq (conditionalGenerator hw0 hw1 K extent hK x) =
      RCadd (RCadd ((P).finalEnergy (schedule extent) x)
        (signedNeighborEnergy hw0 hw1 K extent hK x))
        (remoteEnergy hw0 hw1 K extent hK x) := by
  rw [conditionalGenerator, (P).residualSum_square_decomposition adjacent
    (nonadjacent_commute hw0 hw1 K extent hK)]
  rw [(P).neighborhoodGram_diagonal adjacent (adjacent_refl extent)
    (schedule extent) (schedule_nodup extent)]
  rfl

theorem remoteEnergy_nonnegative (x : GNSCompletionSpace F) :
    RCnonneg (remoteEnergy hw0 hw1 K extent hK x) :=
  (P).remoteSquares_nonnegative adjacent (schedule extent) x

/-- All possible negative contributions now lie in the explicit signed
neighbor sum. This is not yet a positive coercivity estimate. -/
theorem signed_energy_le_generator_square (x : GNSCompletionSpace F) :
    RCle (RCadd ((P).finalEnergy (schedule extent) x)
      (signedNeighborEnergy hw0 hw1 K extent hK x))
      (normSq (conditionalGenerator hw0 hw1 K extent hK x)) := by
  have h := (P).neighborhoodGram_le_residualSum_square adjacent
    (nonadjacent_commute hw0 hw1 K extent hK) (schedule extent) x
  rw [(P).neighborhoodGram_diagonal adjacent (adjacent_refl extent)
    (schedule extent) (schedule_nodup extent)] at h
  exact h

/-- Uniform geometric row count, including its own diagonal entry. It is
not a uniform analytic lower bound on the signed row. -/
theorem neighborhood_row_count (i : PhysicalLink extent) :
    ((schedule extent).filter (adjacent i)).length ≤ 25 :=
  BF4ExactSlabConditionalSweep.neighbor_count extent i (schedule extent)
    (schedule_nodup extent)

#print axioms conditionalGenerator
#print axioms signedNeighborEnergy
#print axioms remoteEnergy
#print axioms conditionalGenerator_energy
#print axioms conditionalGenerator_square
#print axioms remoteEnergy_nonnegative
#print axioms signed_energy_le_generator_square
#print axioms neighborhood_row_count

end YMGap.Continuum.BF4ExactSlabSignedNeighborEnergy
