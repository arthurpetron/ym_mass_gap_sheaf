/-
# Cauchy limits of physical entries pulled back to an old cutoff carrier

The explicit cutoff index map identifies every old positive-row state with
the same literal state in each later carrier.  Pulling the later stationary
weights and normalized reflected kernel back along that map produces entries
on one fixed finite index set.  The existing corrected-slab cutoff moduli then
give executable two-sided Cauchy bounds for every pulled weight and kernel
entry, and hence actual Bishop-real limits.

These are entry limits on a fixed finite carrier, including its canonical
vacuum component.  They do not say that the cutoff-two `49/50` form bound
persists, because both the stationary weights and normalized kernel genuinely
change before reaching their limits.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorEmbedding
import YMGap.Continuum.BF4PhysicalCutoffUniformRowFloor

namespace YMGap.Continuum.BF4PhysicalCutoffEmbeddedEntryCauchy

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffPositiveRowPersistence
open YMGap.Continuum.BF4PhysicalCutoffUniformRowFloor
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorEmbedding
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4SU2CorrectedSlabBoundedObservableTail
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4SU2FixedMagneticPositiveKernelConvergence
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Pulled-back finite entries -/

/-- The later stationary weight read at the explicit image of one old
positive-carrier index. -/
def centralPhysicalFinitePulledWeight
    (w : Q') (hw : (0 : Q') ≤ w)
    (base later half index : Nat) : Q' :=
  centralPhysicalFiniteWeight w hw later half
    (centralPhysicalFiniteCutoffIndexMap
      w hw base later half index)

/-- The later normalized reflected entry read at the explicit images of two
old positive-carrier indices. -/
def centralPhysicalFinitePulledKernel
    (w : Q') (hw : (0 : Q') ≤ w)
    (base later half row column : Nat) : Q' :=
  centralPhysicalFiniteKernel w hw later half
    (centralPhysicalFiniteCutoffIndexMap
      w hw base later half row)
    (centralPhysicalFiniteCutoffIndexMap
      w hw base later half column)

/-- Pulled weights are exactly later row marginals of the same old literal
state. -/
theorem centralPhysicalFinitePulledWeight_eq_rowMarginal
    {w : Q'} {hw : (0 : Q') ≤ w}
    {base later half index : Nat}
    (hcutoff : base ≤ later)
    (hindex : index < centralPhysicalFiniteCarrierSize w hw base half) :
    centralPhysicalFinitePulledWeight w hw base later half index =
      centralPhysicalRowMarginal w hw later half
        (centralPhysicalFiniteStateAt w hw base half index) := by
  unfold centralPhysicalFinitePulledWeight centralPhysicalFiniteWeight
  rw [centralPhysicalFiniteStateAt_cutoffIndexMap_eq hcutoff hindex]

/-- Pulled kernel values are exactly later normalized entries between the
same two old literal states. -/
theorem centralPhysicalFinitePulledKernel_eq_normalizedKernel
    {w : Q'} {hw : (0 : Q') ≤ w}
    {base later half row column : Nat}
    (hcutoff : base ≤ later)
    (hrow : row < centralPhysicalFiniteCarrierSize w hw base half)
    (hcolumn : column < centralPhysicalFiniteCarrierSize w hw base half) :
    centralPhysicalFinitePulledKernel
        w hw base later half row column =
      centralNormalizedPhysicalReflectedKernel w hw later half
        (centralPhysicalFiniteStateAt w hw base half row)
        (centralPhysicalFiniteStateAt w hw base half column) := by
  unfold centralPhysicalFinitePulledKernel centralPhysicalFiniteKernel
  rw [centralPhysicalFiniteStateAt_cutoffIndexMap_eq hcutoff hrow,
    centralPhysicalFiniteStateAt_cutoffIndexMap_eq hcutoff hcolumn]

private theorem centralPhysicalFiniteStateAt_mem_half_of_le
    {w : Q'} {hw : (0 : Q') ≤ w}
    {base later half index : Nat}
    (hcutoff : base ≤ later)
    (hindex : index < centralPhysicalFiniteCarrierSize w hw base half) :
    centralPhysicalFiniteStateAt w hw base half index ∈
      centralHalfStates later half :=
  (mem_centralPositiveHalfStates_iff.mp
    (mem_centralPositiveHalfStates_of_le hw hcutoff
      (centralPhysicalFiniteStateAt_mem_positive
        w hw base half hindex))).1

/-! ## 2. Executable entrywise Cauchy bounds -/

/-- Two pulled normalized kernel entries are epsilon-close once both cutoffs
contain the old carrier and lie beyond the corrected-slab modulus. -/
theorem centralPhysicalFinitePulledKernel_twoSided_of_modulus
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {base first second half row column : Nat}
    {epsilon : Q'} (hepsilon : (0 : Q') < epsilon)
    (hbaseFirst : base ≤ first)
    (hbaseSecond : base ≤ second)
    (hfirst : slabNomeBoundedObservableModulus
      w (centralExtent half) epsilon ≤ first)
    (hsecond : slabNomeBoundedObservableModulus
      w (centralExtent half) epsilon ≤ second)
    (hrow : row < centralPhysicalFiniteCarrierSize
      w (Q'.le_of_lt hw0) base half)
    (hcolumn : column < centralPhysicalFiniteCarrierSize
      w (Q'.le_of_lt hw0) base half) :
    centralPhysicalFinitePulledKernel
          w (Q'.le_of_lt hw0) base first half row column ≤
        centralPhysicalFinitePulledKernel
            w (Q'.le_of_lt hw0) base second half row column + epsilon ∧
      centralPhysicalFinitePulledKernel
          w (Q'.le_of_lt hw0) base second half row column ≤
        centralPhysicalFinitePulledKernel
            w (Q'.le_of_lt hw0) base first half row column + epsilon := by
  have htwo := centralNormalizedPhysicalReflectedKernel_twoSided_of_modulus
    hw0 hw1 half
    (centralPhysicalFiniteStateAt
      w (Q'.le_of_lt hw0) base half row)
    (centralPhysicalFiniteStateAt
      w (Q'.le_of_lt hw0) base half column)
    hepsilon hfirst hsecond
    (centralPhysicalFiniteStateAt_mem_half_of_le hbaseFirst hrow)
    (centralPhysicalFiniteStateAt_mem_half_of_le hbaseFirst hcolumn)
    (centralPhysicalFiniteStateAt_mem_half_of_le hbaseSecond hrow)
    (centralPhysicalFiniteStateAt_mem_half_of_le hbaseSecond hcolumn)
  rw [centralPhysicalFinitePulledKernel_eq_normalizedKernel
      hbaseFirst hrow hcolumn,
    centralPhysicalFinitePulledKernel_eq_normalizedKernel
      hbaseSecond hrow hcolumn]
  exact htwo

/-- Two pulled stationary weights are epsilon-close on the same executable
schedule.  The proof uses the fixed source-cylinder observable. -/
theorem centralPhysicalFinitePulledWeight_twoSided_of_modulus
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {base first second half index : Nat}
    {epsilon : Q'} (hepsilon : (0 : Q') < epsilon)
    (hbaseFirst : base ≤ first)
    (hbaseSecond : base ≤ second)
    (hfirst : slabNomeBoundedObservableModulus
      w (centralExtent half) epsilon ≤ first)
    (hsecond : slabNomeBoundedObservableModulus
      w (centralExtent half) epsilon ≤ second)
    (hindex : index < centralPhysicalFiniteCarrierSize
      w (Q'.le_of_lt hw0) base half) :
    centralPhysicalFinitePulledWeight
          w (Q'.le_of_lt hw0) base first half index ≤
        centralPhysicalFinitePulledWeight
            w (Q'.le_of_lt hw0) base second half index + epsilon ∧
      centralPhysicalFinitePulledWeight
          w (Q'.le_of_lt hw0) base second half index ≤
        centralPhysicalFinitePulledWeight
            w (Q'.le_of_lt hw0) base first half index + epsilon := by
  let source := centralPhysicalFiniteStateAt
    w (Q'.le_of_lt hw0) base half index
  let observable := centralSourceCylinderObservable half source
  have hsourceFirst : source ∈ centralHalfStates first half :=
    centralPhysicalFiniteStateAt_mem_half_of_le hbaseFirst hindex
  have hsourceSecond : source ∈ centralHalfStates second half :=
    centralPhysicalFiniteStateAt_mem_half_of_le hbaseSecond hindex
  have hslab :=
    slabNomeCutoffBoundedObservableExpectation_twoSided_of_modulus
      hw0 hw1 (centralExtent half) observable
      hepsilon hfirst hsecond
  have hfirstEq := centralPhysicalRowMarginal_eq_sourceExpectation
    (w := w) (K := first) (half := half)
    (source := source) (Q'.le_of_lt hw0) hsourceFirst
  have hsecondEq := centralPhysicalRowMarginal_eq_sourceExpectation
    (w := w) (K := second) (half := half)
    (source := source) (Q'.le_of_lt hw0) hsourceSecond
  rw [centralPhysicalFinitePulledWeight_eq_rowMarginal
      hbaseFirst hindex,
    centralPhysicalFinitePulledWeight_eq_rowMarginal
      hbaseSecond hindex]
  constructor
  · exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hfirstEq)
      (Q'.le_trans' _ _ _ hslab.1
        (Q'.add_le_add_right _ _ epsilon
          (Q'.le_of_eqv (Q'.eqv_symm hsecondEq))))
  · exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hsecondEq)
      (Q'.le_trans' _ _ _ hslab.2
        (Q'.add_le_add_right _ _ epsilon
          (Q'.le_of_eqv (Q'.eqv_symm hfirstEq))))

/-! ## 3. Actual Bishop-real entry limits -/

/-- Cutoff-removed stationary weight of one fixed old carrier state. -/
def centralPhysicalFinitePulledWeightCutoffLimit
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (base half index : Nat)
    (hindex : index < centralPhysicalFiniteCarrierSize
      w (Q'.le_of_lt hw0) base half) : CReal where
  approx later := centralPhysicalFinitePulledWeight
    w (Q'.le_of_lt hw0) base later half index
  cauchy := by
    intro epsilon hepsilon
    refine ⟨max base
      (slabNomeBoundedObservableModulus
        w (centralExtent half) epsilon), ?_⟩
    intro first second hfirst hsecond
    exact centralPhysicalFinitePulledWeight_twoSided_of_modulus
      hw0 hw1 hepsilon
      (Nat.le_trans (Nat.le_max_left _ _) hfirst)
      (Nat.le_trans (Nat.le_max_left _ _) hsecond)
      (Nat.le_trans (Nat.le_max_right _ _) hfirst)
      (Nat.le_trans (Nat.le_max_right _ _) hsecond)
      hindex

/-- Cutoff-removed normalized kernel entry between two fixed old carrier
states. -/
def centralPhysicalFinitePulledKernelCutoffLimit
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (base half row column : Nat)
    (hrow : row < centralPhysicalFiniteCarrierSize
      w (Q'.le_of_lt hw0) base half)
    (hcolumn : column < centralPhysicalFiniteCarrierSize
      w (Q'.le_of_lt hw0) base half) : CReal where
  approx later := centralPhysicalFinitePulledKernel
    w (Q'.le_of_lt hw0) base later half row column
  cauchy := by
    intro epsilon hepsilon
    refine ⟨max base
      (slabNomeBoundedObservableModulus
        w (centralExtent half) epsilon), ?_⟩
    intro first second hfirst hsecond
    exact centralPhysicalFinitePulledKernel_twoSided_of_modulus
      hw0 hw1 hepsilon
      (Nat.le_trans (Nat.le_max_left _ _) hfirst)
      (Nat.le_trans (Nat.le_max_left _ _) hsecond)
      (Nat.le_trans (Nat.le_max_right _ _) hfirst)
      (Nat.le_trans (Nat.le_max_right _ _) hsecond)
      hrow hcolumn

end YMGap.Continuum.BF4PhysicalCutoffEmbeddedEntryCauchy

#print axioms
  YMGap.Continuum.BF4PhysicalCutoffEmbeddedEntryCauchy.centralPhysicalFinitePulledKernel_twoSided_of_modulus
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffEmbeddedEntryCauchy.centralPhysicalFinitePulledWeight_twoSided_of_modulus
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffEmbeddedEntryCauchy.centralPhysicalFinitePulledWeightCutoffLimit
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffEmbeddedEntryCauchy.centralPhysicalFinitePulledKernelCutoffLimit
