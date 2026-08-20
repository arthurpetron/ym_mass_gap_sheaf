/-
# The explicit cutoff-two physical Krylov seed

The first abstract leakage witness is now supplemented by the concrete
doubled-spin cube found by the exact production computation.  Faithful BF4
state codes give the explicit three-state list

  vacuum, fundamental cube, doubled cube.

Every literally row-closed physical code sector containing the vacuum must
contain the doubled-cube code, because the corresponding genuine physical
Gram entry is strictly positive.  In particular, every proof-carrying
cutoff-two closure certificate contains this explicit code.

This is a forced seed, not a claim that the three displayed states are
row-closed or form an invariant spectral block.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoDoubleCubeLeakage

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoExplicitKrylovSeed

set_option maxRecDepth 300000
set_option maxHeartbeats 300000

open YMGap.Constructive
open YMGap.Continuum.BF4CanonicalFiniteNumeratorPartitionBudget
open YMGap.Continuum.BF4CentralLowerCubePositiveRow
open YMGap.Continuum.BF4FiveHolonomyNormalizedKernel
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubePhysicalIntegrand
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoDoubleCubeLeakage
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoKrylovClosureCertificate
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoKrylovSeed
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumCubeLeakage
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumRefreshSpectrum
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph

/-! ## 1. A noduplicated explicit state-code seed -/

theorem cutoffTwoDoubleCube_code_ne_vacuum :
    bf4StateCode 2 0 centralLowerDoubleCubeState ≠
      bf4StateCode 2 0 zeroEdgeLabelling := by
  intro hcode
  exact centralLowerDoubleCubeState_ne_zero
    (bf4StateCode_injective_on_positive
      centralLowerDoubleCubeState_mem_carrier
      (zeroEdgeLabelling_mem_centralPositiveHalfStates
        (by decide : (0 : Q') ≤ cutoffTwoHalfCoupling) 2 0)
      hcode)

theorem cutoffTwoDoubleCube_code_ne_cube :
    bf4StateCode 2 0 centralLowerDoubleCubeState ≠
      bf4StateCode 2 0 centralLowerCubeState := by
  intro hcode
  exact centralLowerDoubleCubeState_ne_cube
    (bf4StateCode_injective_on_positive
      centralLowerDoubleCubeState_mem_carrier
      (centralLowerCubeState_mem_centralPositiveHalfStates
        (w := cutoffTwoHalfCoupling) (by decide) (K := 2) (by decide))
      hcode)

def cutoffTwoExplicitKrylovSeedStates : List EdgeLabelling :=
  [zeroEdgeLabelling, centralLowerCubeState, centralLowerDoubleCubeState]

def cutoffTwoExplicitKrylovSeedCodes : List Nat :=
  cutoffTwoExplicitKrylovSeedStates.map (bf4StateCode 2 0)

theorem cutoffTwoExplicitKrylovSeedStates_nodup :
    cutoffTwoExplicitKrylovSeedStates.Nodup := by
  unfold cutoffTwoExplicitKrylovSeedStates
  apply List.nodup_cons.mpr
  constructor
  · intro hmem
    rcases List.mem_cons.mp hmem with hcube | htail
    · exact (Ne.symm centralLowerCubeState_ne_zero) hcube
    rcases List.mem_cons.mp htail with hdouble | hempty
    · exact (Ne.symm centralLowerDoubleCubeState_ne_zero) hdouble
    · exact List.not_mem_nil hempty
  · apply List.nodup_cons.mpr
    constructor
    · intro hmem
      rcases List.mem_cons.mp hmem with hdouble | hempty
      · exact (Ne.symm centralLowerDoubleCubeState_ne_cube) hdouble
      · exact List.not_mem_nil hempty
    · exact List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩

theorem cutoffTwoExplicitKrylovSeedCodes_nodup :
    cutoffTwoExplicitKrylovSeedCodes.Nodup := by
  unfold cutoffTwoExplicitKrylovSeedCodes cutoffTwoExplicitKrylovSeedStates
  apply List.nodup_cons.mpr
  constructor
  · intro hmem
    rcases List.mem_cons.mp hmem with hcube | htail
    · exact cutoffTwo_vacuum_cube_code_ne hcube
    rcases List.mem_cons.mp htail with hdouble | hempty
    · exact (Ne.symm cutoffTwoDoubleCube_code_ne_vacuum) hdouble
    · exact List.not_mem_nil hempty
  · apply List.nodup_cons.mpr
    constructor
    · intro hmem
      rcases List.mem_cons.mp hmem with hdouble | hempty
      · exact (Ne.symm cutoffTwoDoubleCube_code_ne_cube) hdouble
      · exact List.not_mem_nil hempty
    · exact List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩

theorem cutoffTwoExplicitKrylovSeedStates_subset_carrier
    (state : EdgeLabelling)
    (hstate : state ∈ cutoffTwoExplicitKrylovSeedStates) :
    state ∈ cutoffTwoVacuumColumnCarrier := by
  unfold cutoffTwoExplicitKrylovSeedStates at hstate
  rcases List.mem_cons.mp hstate with hstate | htail
  · subst state
    exact zeroEdgeLabelling_mem_centralPositiveHalfStates
      (by decide : (0 : Q') ≤ cutoffTwoHalfCoupling) 2 0
  rcases List.mem_cons.mp htail with hstate | htail
  · subst state
    exact centralLowerCubeState_mem_centralPositiveHalfStates
      (w := cutoffTwoHalfCoupling) (by decide) (K := 2) (by decide)
  rcases List.mem_cons.mp htail with hstate | hempty
  · subst state
    exact centralLowerDoubleCubeState_mem_carrier
  · exact False.elim (List.not_mem_nil hempty)

/-! ## 2. The explicit doubled cube is forced by row closure -/

theorem doubleCube_code_mem_of_vacuum_code_mem_and_rowClosed
    (sectorCodes : List Nat)
    (hclosed : cutoffTwoPhysicalCodeSectorRowClosed sectorCodes)
    (hvacuum : bf4StateCode 2 0 zeroEdgeLabelling ∈ sectorCodes) :
    bf4StateCode 2 0 centralLowerDoubleCubeState ∈ sectorCodes := by
  exact code_mem_of_positive_physical_edge sectorCodes hclosed
    zeroEdgeLabelling centralLowerDoubleCubeState
    (zeroEdgeLabelling_mem_centralPositiveHalfStates
      (by decide : (0 : Q') ≤ cutoffTwoHalfCoupling) 2 0)
    centralLowerDoubleCubeState_mem_carrier hvacuum
    centralPhysicalReflectedKernel_cutoffTwo_vacuum_doubleCube_pos

theorem closureCertificate_contains_doubleCube
    (certificate : CutoffTwoPhysicalKrylovClosureCertificate) :
    bf4StateCode 2 0 centralLowerDoubleCubeState ∈
      certificate.sectorCodes := by
  apply doubleCube_code_mem_of_vacuum_code_mem_and_rowClosed
    certificate.sectorCodes certificate.rowClosed
  exact certificate.forcedSeedIncluded
    (bf4StateCode 2 0 zeroEdgeLabelling)
    (by simp [cutoffTwoFirstKrylovSeedCodes])

/-- The original vacuum/fundamental-cube code list is also refuted directly
by the explicit doubled-cube edge, independently of the selected abstract
leakage witness. -/
theorem not_cutoffTwoVacuumCubeCodes_rowClosed_explicit :
    ¬ cutoffTwoPhysicalCodeSectorRowClosed cutoffTwoVacuumCubeCodes := by
  intro hclosed
  have hdouble := doubleCube_code_mem_of_vacuum_code_mem_and_rowClosed
    cutoffTwoVacuumCubeCodes hclosed
    (by simp [cutoffTwoVacuumCubeCodes])
  unfold cutoffTwoVacuumCubeCodes at hdouble
  rcases List.mem_cons.mp hdouble with hvacuum | htail
  · exact cutoffTwoDoubleCube_code_ne_vacuum hvacuum
  rcases List.mem_cons.mp htail with hcube | hempty
  · exact cutoffTwoDoubleCube_code_ne_cube hcube
  · exact False.elim (List.not_mem_nil hempty)

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoExplicitKrylovSeed

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoExplicitKrylovSeed.cutoffTwoExplicitKrylovSeedCodes_nodup
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoExplicitKrylovSeed.cutoffTwoExplicitKrylovSeedStates_subset_carrier
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoExplicitKrylovSeed.doubleCube_code_mem_of_vacuum_code_mem_and_rowClosed
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoExplicitKrylovSeed.closureCertificate_contains_doubleCube
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoExplicitKrylovSeed.not_cutoffTwoVacuumCubeCodes_rowClosed_explicit
