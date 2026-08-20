/-
# The first forced cutoff-two physical Krylov seed

Finite sectors are represented by faithful natural-number BF4 state codes,
so membership is decidable without equality on function-valued labellings.
For any code sector satisfying the literal raw-Gram row-closure condition, a
strictly positive entry from an included source forces the target code into
the sector.  The previously selected leakage state is therefore required in
every row-closed sector containing the vacuum.

This constructs only the first forced closure layer.  It neither proves that
the three-state seed is closed nor supplies a finite or uniform spectral gap.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumCubeLeakage

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoKrylovSeed

set_option maxRecDepth 300000
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Continuum.BF4CanonicalFiniteNumeratorPartitionBudget
open YMGap.Continuum.BF4CentralLowerCubePositiveRow
open YMGap.Continuum.BF4FiveHolonomyNormalizedKernel
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubePhysicalIntegrand
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumCubeLeakage
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumRefreshSpectrum
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Faithful codes of the forced three-state seed -/

theorem cutoffTwoLeakage_code_ne_vacuum :
    bf4StateCode 2 0 cutoffTwoVacuumCubeLeakageState ≠
      bf4StateCode 2 0 zeroEdgeLabelling := by
  intro hcode
  exact cutoffTwoVacuumCubeLeakageState_spec.2.1
    (bf4StateCode_injective_on_positive
      cutoffTwoVacuumCubeLeakageState_spec.1
      (zeroEdgeLabelling_mem_centralPositiveHalfStates
        (by decide : (0 : Q') ≤ cutoffTwoHalfCoupling) 2 0)
      hcode)

theorem cutoffTwoLeakage_code_ne_cube :
    bf4StateCode 2 0 cutoffTwoVacuumCubeLeakageState ≠
      bf4StateCode 2 0 centralLowerCubeState := by
  intro hcode
  exact cutoffTwoVacuumCubeLeakageState_spec.2.2.1
    (bf4StateCode_injective_on_positive
      cutoffTwoVacuumCubeLeakageState_spec.1
      (centralLowerCubeState_mem_centralPositiveHalfStates
        (w := cutoffTwoHalfCoupling) (by decide) (K := 2) (by decide))
      hcode)

def cutoffTwoVacuumCubeCodes : List Nat :=
  [bf4StateCode 2 0 zeroEdgeLabelling,
    bf4StateCode 2 0 centralLowerCubeState]

def cutoffTwoFirstKrylovSeedCodes : List Nat :=
  [bf4StateCode 2 0 zeroEdgeLabelling,
    bf4StateCode 2 0 centralLowerCubeState,
    bf4StateCode 2 0 cutoffTwoVacuumCubeLeakageState]

def cutoffTwoFirstKrylovSeedStates : List EdgeLabelling :=
  [zeroEdgeLabelling, centralLowerCubeState,
    cutoffTwoVacuumCubeLeakageState]

theorem cutoffTwoFirstKrylovSeedCodes_nodup :
    cutoffTwoFirstKrylovSeedCodes.Nodup := by
  unfold cutoffTwoFirstKrylovSeedCodes
  apply List.nodup_cons.mpr
  constructor
  · intro hmem
    rcases List.mem_cons.mp hmem with hcube | htail
    · exact cutoffTwo_vacuum_cube_code_ne hcube
    rcases List.mem_cons.mp htail with hleak | hempty
    · exact (Ne.symm cutoffTwoLeakage_code_ne_vacuum) hleak
    · exact List.not_mem_nil hempty
  · apply List.nodup_cons.mpr
    constructor
    · intro hmem
      rcases List.mem_cons.mp hmem with hleak | hempty
      · exact (Ne.symm cutoffTwoLeakage_code_ne_cube) hleak
      · exact List.not_mem_nil hempty
    · exact List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩

theorem cutoffTwoFirstKrylovSeedStates_nodup :
    cutoffTwoFirstKrylovSeedStates.Nodup := by
  unfold cutoffTwoFirstKrylovSeedStates
  apply List.nodup_cons.mpr
  constructor
  · intro hmem
    rcases List.mem_cons.mp hmem with hcube | htail
    · exact (Ne.symm centralLowerCubeState_ne_zero) hcube
    rcases List.mem_cons.mp htail with hleak | hempty
    · exact (Ne.symm cutoffTwoVacuumCubeLeakageState_spec.2.1) hleak
    · exact List.not_mem_nil hempty
  · apply List.nodup_cons.mpr
    constructor
    · intro hmem
      rcases List.mem_cons.mp hmem with hleak | hempty
      · exact (Ne.symm cutoffTwoVacuumCubeLeakageState_spec.2.2.1) hleak
      · exact List.not_mem_nil hempty
    · exact List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩

theorem cutoffTwoFirstKrylovSeedStates_subset_carrier
    (state : EdgeLabelling)
    (hstate : state ∈ cutoffTwoFirstKrylovSeedStates) :
    state ∈ cutoffTwoVacuumColumnCarrier := by
  unfold cutoffTwoFirstKrylovSeedStates at hstate
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
    exact cutoffTwoVacuumCubeLeakageState_spec.1
  · exact False.elim (List.not_mem_nil hempty)

/-! ## 2. Constructive code-sector row closure -/

/-- Literal coordinate row closure for a finite list of faithful BF4 state
codes.  Every kernel entry from an included retained source to an excluded
retained target must vanish. -/
def cutoffTwoPhysicalCodeSectorRowClosed
    (sectorCodes : List Nat) : Prop :=
  ∀ source target : EdgeLabelling,
    source ∈ cutoffTwoVacuumColumnCarrier →
    target ∈ cutoffTwoVacuumColumnCarrier →
    bf4StateCode 2 0 source ∈ sectorCodes →
    bf4StateCode 2 0 target ∉ sectorCodes →
    centralPhysicalReflectedKernel cutoffTwoHalfCoupling 2 0
      source target ≈ 0

/-- The constructive one-step closure rule: a positive raw physical Gram
edge from a code already in a row-closed sector forces the target code into
that sector. -/
theorem code_mem_of_positive_physical_edge
    (sectorCodes : List Nat)
    (hclosed : cutoffTwoPhysicalCodeSectorRowClosed sectorCodes)
    (source target : EdgeLabelling)
    (hsource : source ∈ cutoffTwoVacuumColumnCarrier)
    (htarget : target ∈ cutoffTwoVacuumColumnCarrier)
    (hsourceCode : bf4StateCode 2 0 source ∈ sectorCodes)
    (hpositive : (0 : Q') <
      centralPhysicalReflectedKernel cutoffTwoHalfCoupling 2 0
        source target) :
    bf4StateCode 2 0 target ∈ sectorCodes := by
  by_cases htargetCode : bf4StateCode 2 0 target ∈ sectorCodes
  · exact htargetCode
  · have hzero := hclosed source target hsource htarget
      hsourceCode htargetCode
    exact False.elim
      ((Int.not_lt_of_ge (Q'.le_of_eqv hzero)) hpositive)

theorem leakage_code_mem_of_vacuum_code_mem_and_rowClosed
    (sectorCodes : List Nat)
    (hclosed : cutoffTwoPhysicalCodeSectorRowClosed sectorCodes)
    (hvacuum : bf4StateCode 2 0 zeroEdgeLabelling ∈ sectorCodes) :
    bf4StateCode 2 0 cutoffTwoVacuumCubeLeakageState ∈ sectorCodes := by
  exact code_mem_of_positive_physical_edge sectorCodes hclosed
    zeroEdgeLabelling cutoffTwoVacuumCubeLeakageState
    (zeroEdgeLabelling_mem_centralPositiveHalfStates
      (by decide : (0 : Q') ≤ cutoffTwoHalfCoupling) 2 0)
    cutoffTwoVacuumCubeLeakageState_spec.1 hvacuum
    centralPhysicalReflectedKernel_cutoffTwo_vacuum_leakage_pos

theorem not_cutoffTwoVacuumCubeCodes_rowClosed :
    ¬ cutoffTwoPhysicalCodeSectorRowClosed cutoffTwoVacuumCubeCodes := by
  intro hclosed
  have hleak := leakage_code_mem_of_vacuum_code_mem_and_rowClosed
    cutoffTwoVacuumCubeCodes hclosed
    (by simp [cutoffTwoVacuumCubeCodes])
  unfold cutoffTwoVacuumCubeCodes at hleak
  rcases List.mem_cons.mp hleak with hleak | htail
  · exact cutoffTwoLeakage_code_ne_vacuum hleak
  rcases List.mem_cons.mp htail with hleak | hempty
  · exact cutoffTwoLeakage_code_ne_cube hleak
  · exact False.elim (List.not_mem_nil hempty)

/-- The selected leakage code is present in the first enlarged seed by
construction.  Closure of this three-code seed is deliberately not claimed. -/
theorem cutoffTwoLeakage_code_mem_firstKrylovSeed :
    bf4StateCode 2 0 cutoffTwoVacuumCubeLeakageState ∈
      cutoffTwoFirstKrylovSeedCodes := by
  simp [cutoffTwoFirstKrylovSeedCodes]

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoKrylovSeed

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoKrylovSeed.cutoffTwoFirstKrylovSeedCodes_nodup
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoKrylovSeed.cutoffTwoFirstKrylovSeedStates_subset_carrier
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoKrylovSeed.code_mem_of_positive_physical_edge
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoKrylovSeed.leakage_code_mem_of_vacuum_code_mem_and_rowClosed
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoKrylovSeed.not_cutoffTwoVacuumCubeCodes_rowClosed
