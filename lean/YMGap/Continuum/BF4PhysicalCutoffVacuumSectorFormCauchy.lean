/-
# Cauchy limits of the embedded canonical-vacuum-sector forms

The old canonical vacuum component embeds into every later representation
cutoff.  This file restricts the pulled weight and normalized reflected
quadratic constructions to exactly that old root component and lifts their
entrywise cutoff moduli to Bishop-real limits.

The coefficient is still extended by zero outside the embedded old component.
Consequently these limits describe the old block inside the later canonical
component, not the whole later component.  Newly entering states, their
stationary mass, and the old/new cross block remain explicit open terms before
any cutoff-uniform strict contraction can be claimed.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalCutoffEmbeddedFormCauchy

namespace YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFormCauchy

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffEmbeddedEntryCauchy
open YMGap.Continuum.BF4PhysicalCutoffEmbeddedFormCauchy
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4SU2CorrectedSlabBoundedObservableTail
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Pulled forms on the old canonical vacuum component -/

/-- The later stationary mean restricted to the embedded old canonical
vacuum component. -/
def centralPhysicalFinitePulledVacuumSectorWeightedMean
    (w : Q') (hw : (0 : Q') ≤ w)
    (base later half : Nat) (coefficient : Nat → Q') : Q' :=
  listQSum
    (fun index => coefficient index *
      centralPhysicalFinitePulledWeight w hw base later half index)
    (centralPhysicalFiniteVacuumSectorIndices w hw base half)

/-- The later stationary diagonal quadratic restricted to the embedded old
canonical vacuum component. -/
def centralPhysicalFinitePulledVacuumSectorDiagonalQuadratic
    (w : Q') (hw : (0 : Q') ≤ w)
    (base later half : Nat) (coefficient : Nat → Q') : Q' :=
  listQSum
    (fun index =>
      (coefficient index * coefficient index) *
        centralPhysicalFinitePulledWeight w hw base later half index)
    (centralPhysicalFiniteVacuumSectorIndices w hw base half)

/-- The later normalized reflected quadratic restricted to the embedded old
canonical vacuum component. -/
def centralPhysicalFinitePulledVacuumSectorMatrixQuadratic
    (w : Q') (hw : (0 : Q') ≤ w)
    (base later half : Nat) (coefficient : Nat → Q') : Q' :=
  finiteJointQuadratic
    (centralPhysicalFiniteVacuumSectorIndices w hw base half)
    coefficient
    (centralPhysicalFinitePulledKernel w hw base later half)

/-! ## 2. Constructive cutoff limits of the three sector forms -/

/-- Executable cutoff rate for the pulled weighted mean on one fixed old
canonical vacuum component.  This exposes the witness already used by the
legacy `CReal.cauchy` proof so later Type-level completion data need not
extract a cutoff from `Prop`. -/
def centralPhysicalFinitePulledVacuumSectorWeightedMeanCutoffRate
    {w : Q'} (hw0 : (0 : Q') < w)
    (base half : Nat) (coefficient : Nat → Q')
    (epsilon : Q') : Nat :=
  let states := centralPhysicalFiniteVacuumSectorIndices
    w (Q'.le_of_lt hw0) base half
  let baseScale := coefficientL1 states coefficient
  let tolerance := Q'.divPos epsilon (baseScale + 1)
    (positive_scale (coefficientL1_nonnegative_local states coefficient))
  max base
    (slabNomeBoundedObservableModulus
      w (centralExtent half) tolerance)

/-- The explicit weighted-mean cutoff rate controls every pair of later
pulled means. -/
theorem centralPhysicalFinitePulledVacuumSectorWeightedMeanCutoff_regular
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (base half : Nat) (coefficient : Nat → Q')
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (first second : Nat)
    (hfirst :
      centralPhysicalFinitePulledVacuumSectorWeightedMeanCutoffRate
        hw0 base half coefficient epsilon ≤ first)
    (hsecond :
      centralPhysicalFinitePulledVacuumSectorWeightedMeanCutoffRate
        hw0 base half coefficient epsilon ≤ second) :
    centralPhysicalFinitePulledVacuumSectorWeightedMean
        w (Q'.le_of_lt hw0) base first half coefficient ≤
      centralPhysicalFinitePulledVacuumSectorWeightedMean
          w (Q'.le_of_lt hw0) base second half coefficient + epsilon ∧
    centralPhysicalFinitePulledVacuumSectorWeightedMean
        w (Q'.le_of_lt hw0) base second half coefficient ≤
      centralPhysicalFinitePulledVacuumSectorWeightedMean
          w (Q'.le_of_lt hw0) base first half coefficient + epsilon := by
    let states := centralPhysicalFiniteVacuumSectorIndices
      w (Q'.le_of_lt hw0) base half
    let baseScale := coefficientL1 states coefficient
    have hbaseScale : (0 : Q') ≤ baseScale :=
      coefficientL1_nonnegative_local _ _
    let tolerance := Q'.divPos epsilon (baseScale + 1)
      (positive_scale hbaseScale)
    have htolerance : (0 : Q') < tolerance :=
      Q'.divPos_pos epsilon (baseScale + 1)
        (positive_scale hbaseScale) hepsilon
    have hrate :
        centralPhysicalFinitePulledVacuumSectorWeightedMeanCutoffRate
            hw0 base half coefficient epsilon =
          max base
            (slabNomeBoundedObservableModulus
              w (centralExtent half) tolerance) := by
      rfl
    have hbaseFirst := Nat.le_trans (Nat.le_max_left _ _) (hrate ▸ hfirst)
    have hbaseSecond := Nat.le_trans (Nat.le_max_left _ _) (hrate ▸ hsecond)
    have hmodFirst := Nat.le_trans (Nat.le_max_right _ _) (hrate ▸ hfirst)
    have hmodSecond := Nat.le_trans (Nat.le_max_right _ _) (hrate ▸ hsecond)
    have hbaseFirst := Nat.le_trans (Nat.le_max_left _ _) hfirst
    have hbaseSecond := Nat.le_trans (Nat.le_max_left _ _) hsecond
    have hmodFirst := Nat.le_trans (Nat.le_max_right _ _) hfirst
    have hmodSecond := Nat.le_trans (Nat.le_max_right _ _) hsecond
    have hentry : ∀ index, index ∈ states →
        Q'.abs
          (centralPhysicalFinitePulledWeight
              w (Q'.le_of_lt hw0) base first half index +
            (-centralPhysicalFinitePulledWeight
              w (Q'.le_of_lt hw0) base second half index)) ≤
          tolerance := by
      intro index hindex
      have hindexLt : index < centralPhysicalFiniteCarrierSize
          w (Q'.le_of_lt hw0) base half :=
        centralPhysicalFiniteVacuumSectorIndex_lt
          w (Q'.le_of_lt hw0) base half hindex
      exact CReal.abs_sub_le_of_bounds
        (centralPhysicalFinitePulledWeight_twoSided_of_modulus
          hw0 hw1 htolerance hbaseFirst hbaseSecond
          hmodFirst hmodSecond hindexLt).1
        (centralPhysicalFinitePulledWeight_twoSided_of_modulus
          hw0 hw1 htolerance hbaseFirst hbaseSecond
          hmodFirst hmodSecond hindexLt).2
    have habs :
        Q'.abs
          (centralPhysicalFinitePulledVacuumSectorWeightedMean
              w (Q'.le_of_lt hw0) base first half coefficient +
            (-centralPhysicalFinitePulledVacuumSectorWeightedMean
              w (Q'.le_of_lt hw0) base second half coefficient)) ≤
          baseScale * tolerance := by
      unfold centralPhysicalFinitePulledVacuumSectorWeightedMean
      exact finiteLinearForm_abs_sub_le_l1_on
        states coefficient
        (centralPhysicalFinitePulledWeight
          w (Q'.le_of_lt hw0) base first half)
        (centralPhysicalFinitePulledWeight
          w (Q'.le_of_lt hw0) base second half)
        tolerance hentry
    exact two_sided_add_of_abs_sub_le_local
      (Q'.le_trans' _ _ _ habs
        (scaled_divPos_le_epsilon hbaseScale hepsilon))

/-- The pulled weighted mean on the embedded old canonical vacuum component
is a constructive cutoff-Cauchy sequence. -/
def centralPhysicalFinitePulledVacuumSectorWeightedMeanCutoffLimit
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (base half : Nat) (coefficient : Nat → Q') : CReal where
  approx later := centralPhysicalFinitePulledVacuumSectorWeightedMean
    w (Q'.le_of_lt hw0) base later half coefficient
  cauchy := by
    intro epsilon hepsilon
    exact
      ⟨centralPhysicalFinitePulledVacuumSectorWeightedMeanCutoffRate
          hw0 base half coefficient epsilon,
        fun first second hfirst hsecond =>
          centralPhysicalFinitePulledVacuumSectorWeightedMeanCutoff_regular
            hw0 hw1 base half coefficient epsilon hepsilon
            first second hfirst hsecond⟩

/-- The pulled diagonal quadratic on the embedded old canonical vacuum
component is a constructive cutoff-Cauchy sequence. -/
def centralPhysicalFinitePulledVacuumSectorDiagonalQuadraticCutoffLimit
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (base half : Nat) (coefficient : Nat → Q') : CReal where
  approx later := centralPhysicalFinitePulledVacuumSectorDiagonalQuadratic
    w (Q'.le_of_lt hw0) base later half coefficient
  cauchy := by
    intro epsilon hepsilon
    let states := centralPhysicalFiniteVacuumSectorIndices
      w (Q'.le_of_lt hw0) base half
    let squaredCoefficient := fun index =>
      coefficient index * coefficient index
    let baseScale := coefficientL1 states squaredCoefficient
    have hbaseScale : (0 : Q') ≤ baseScale :=
      coefficientL1_nonnegative_local _ _
    let tolerance := Q'.divPos epsilon (baseScale + 1)
      (positive_scale hbaseScale)
    have htolerance : (0 : Q') < tolerance :=
      Q'.divPos_pos epsilon (baseScale + 1)
        (positive_scale hbaseScale) hepsilon
    refine ⟨max base
      (slabNomeBoundedObservableModulus
        w (centralExtent half) tolerance), ?_⟩
    intro first second hfirst hsecond
    have hbaseFirst := Nat.le_trans (Nat.le_max_left _ _) hfirst
    have hbaseSecond := Nat.le_trans (Nat.le_max_left _ _) hsecond
    have hmodFirst := Nat.le_trans (Nat.le_max_right _ _) hfirst
    have hmodSecond := Nat.le_trans (Nat.le_max_right _ _) hsecond
    have hentry : ∀ index, index ∈ states →
        Q'.abs
          (centralPhysicalFinitePulledWeight
              w (Q'.le_of_lt hw0) base first half index +
            (-centralPhysicalFinitePulledWeight
              w (Q'.le_of_lt hw0) base second half index)) ≤
          tolerance := by
      intro index hindex
      have hindexLt : index < centralPhysicalFiniteCarrierSize
          w (Q'.le_of_lt hw0) base half :=
        centralPhysicalFiniteVacuumSectorIndex_lt
          w (Q'.le_of_lt hw0) base half hindex
      exact CReal.abs_sub_le_of_bounds
        (centralPhysicalFinitePulledWeight_twoSided_of_modulus
          hw0 hw1 htolerance hbaseFirst hbaseSecond
          hmodFirst hmodSecond hindexLt).1
        (centralPhysicalFinitePulledWeight_twoSided_of_modulus
          hw0 hw1 htolerance hbaseFirst hbaseSecond
          hmodFirst hmodSecond hindexLt).2
    have habs :
        Q'.abs
          (centralPhysicalFinitePulledVacuumSectorDiagonalQuadratic
              w (Q'.le_of_lt hw0) base first half coefficient +
            (-centralPhysicalFinitePulledVacuumSectorDiagonalQuadratic
              w (Q'.le_of_lt hw0) base second half coefficient)) ≤
          baseScale * tolerance := by
      unfold centralPhysicalFinitePulledVacuumSectorDiagonalQuadratic
      exact finiteLinearForm_abs_sub_le_l1_on
        states squaredCoefficient
        (centralPhysicalFinitePulledWeight
          w (Q'.le_of_lt hw0) base first half)
        (centralPhysicalFinitePulledWeight
          w (Q'.le_of_lt hw0) base second half)
        tolerance hentry
    exact two_sided_add_of_abs_sub_le_local
      (Q'.le_trans' _ _ _ habs
        (scaled_divPos_le_epsilon hbaseScale hepsilon))

/-- Explicit cutoff rate for the pulled reflected quadratic on one fixed old
canonical vacuum component.  Exposing this rate separately from the legacy
`CReal.cauchy` field lets later moving-presentation diagonals pay it without
extracting a witness from `Prop`. -/
def centralPhysicalFinitePulledVacuumSectorMatrixQuadraticCutoffRate
    {w : Q'} (hw0 : (0 : Q') < w)
    (base half : Nat) (coefficient : Nat → Q')
    (epsilon : Q') : Nat :=
  let states := centralPhysicalFiniteVacuumSectorIndices
    w (Q'.le_of_lt hw0) base half
  let l1 := coefficientL1 states coefficient
  let baseScale := l1 * l1
  let tolerance := Q'.divPos epsilon (baseScale + 1)
    (positive_scale
      (Q'.mul_nonneg _ _
        (coefficientL1_nonnegative_local states coefficient)
        (coefficientL1_nonnegative_local states coefficient)))
  max base
    (slabNomeBoundedObservableModulus
      w (centralExtent half) tolerance)

/-- The explicit rate above controls every pair of later pulled reflected
quadratics. -/
theorem centralPhysicalFinitePulledVacuumSectorMatrixQuadraticCutoff_regular
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (base half : Nat) (coefficient : Nat → Q')
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (first second : Nat)
    (hfirst :
      centralPhysicalFinitePulledVacuumSectorMatrixQuadraticCutoffRate
        hw0 base half coefficient epsilon ≤ first)
    (hsecond :
      centralPhysicalFinitePulledVacuumSectorMatrixQuadraticCutoffRate
        hw0 base half coefficient epsilon ≤ second) :
    centralPhysicalFinitePulledVacuumSectorMatrixQuadratic
        w (Q'.le_of_lt hw0) base first half coefficient ≤
      centralPhysicalFinitePulledVacuumSectorMatrixQuadratic
          w (Q'.le_of_lt hw0) base second half coefficient + epsilon ∧
    centralPhysicalFinitePulledVacuumSectorMatrixQuadratic
        w (Q'.le_of_lt hw0) base second half coefficient ≤
      centralPhysicalFinitePulledVacuumSectorMatrixQuadratic
          w (Q'.le_of_lt hw0) base first half coefficient + epsilon := by
  let states := centralPhysicalFiniteVacuumSectorIndices
    w (Q'.le_of_lt hw0) base half
  let l1 := coefficientL1 states coefficient
  let baseScale := l1 * l1
  have hl1 : (0 : Q') ≤ l1 :=
    coefficientL1_nonnegative_local _ _
  have hbaseScale : (0 : Q') ≤ baseScale :=
    Q'.mul_nonneg _ _ hl1 hl1
  let tolerance := Q'.divPos epsilon (baseScale + 1)
    (positive_scale hbaseScale)
  have htolerance : (0 : Q') < tolerance :=
    Q'.divPos_pos epsilon (baseScale + 1)
      (positive_scale hbaseScale) hepsilon
  have hrate :
      centralPhysicalFinitePulledVacuumSectorMatrixQuadraticCutoffRate
          hw0 base half coefficient epsilon =
        max base
          (slabNomeBoundedObservableModulus
            w (centralExtent half) tolerance) := by
    rfl
  have hbaseFirst := Nat.le_trans
    (Nat.le_max_left base
      (slabNomeBoundedObservableModulus
        w (centralExtent half) tolerance))
    (hrate ▸ hfirst)
  have hbaseSecond := Nat.le_trans
    (Nat.le_max_left base
      (slabNomeBoundedObservableModulus
        w (centralExtent half) tolerance))
    (hrate ▸ hsecond)
  have hmodFirst := Nat.le_trans
    (Nat.le_max_right base
      (slabNomeBoundedObservableModulus
        w (centralExtent half) tolerance))
    (hrate ▸ hfirst)
  have hmodSecond := Nat.le_trans
    (Nat.le_max_right base
      (slabNomeBoundedObservableModulus
        w (centralExtent half) tolerance))
    (hrate ▸ hsecond)
  have hentry : ∀ row column,
      row ∈ states → column ∈ states →
      Q'.abs
        (centralPhysicalFinitePulledKernel
            w (Q'.le_of_lt hw0) base first half row column +
          (-centralPhysicalFinitePulledKernel
            w (Q'.le_of_lt hw0) base second half row column)) ≤
        tolerance := by
    intro row column hrow hcolumn
    have hrowLt : row < centralPhysicalFiniteCarrierSize
        w (Q'.le_of_lt hw0) base half :=
      centralPhysicalFiniteVacuumSectorIndex_lt
        w (Q'.le_of_lt hw0) base half hrow
    have hcolumnLt : column < centralPhysicalFiniteCarrierSize
        w (Q'.le_of_lt hw0) base half :=
      centralPhysicalFiniteVacuumSectorIndex_lt
        w (Q'.le_of_lt hw0) base half hcolumn
    have htwo := centralPhysicalFinitePulledKernel_twoSided_of_modulus
      hw0 hw1 htolerance hbaseFirst hbaseSecond
      hmodFirst hmodSecond hrowLt hcolumnLt
    exact CReal.abs_sub_le_of_bounds htwo.1 htwo.2
  have habs :
      Q'.abs
        (centralPhysicalFinitePulledVacuumSectorMatrixQuadratic
            w (Q'.le_of_lt hw0) base first half coefficient +
          (-centralPhysicalFinitePulledVacuumSectorMatrixQuadratic
            w (Q'.le_of_lt hw0) base second half coefficient)) ≤
        baseScale * tolerance := by
    unfold centralPhysicalFinitePulledVacuumSectorMatrixQuadratic
    exact finiteJointQuadratic_abs_sub_le_square
      states coefficient
      (centralPhysicalFinitePulledKernel
        w (Q'.le_of_lt hw0) base first half)
      (centralPhysicalFinitePulledKernel
        w (Q'.le_of_lt hw0) base second half)
      tolerance (Q'.le_of_lt htolerance) hentry
  exact two_sided_add_of_abs_sub_le_local
    (Q'.le_trans' _ _ _ habs
      (scaled_divPos_le_epsilon hbaseScale hepsilon))

/-- The pulled reflected quadratic on the embedded old canonical vacuum
component is a constructive cutoff-Cauchy sequence. -/
def centralPhysicalFinitePulledVacuumSectorMatrixQuadraticCutoffLimit
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (base half : Nat) (coefficient : Nat → Q') : CReal where
  approx later := centralPhysicalFinitePulledVacuumSectorMatrixQuadratic
    w (Q'.le_of_lt hw0) base later half coefficient
  cauchy := by
    intro epsilon hepsilon
    exact
      ⟨centralPhysicalFinitePulledVacuumSectorMatrixQuadraticCutoffRate
          hw0 base half coefficient epsilon,
        fun first second hfirst hsecond =>
          centralPhysicalFinitePulledVacuumSectorMatrixQuadraticCutoff_regular
            hw0 hw1 base half coefficient epsilon hepsilon
            first second hfirst hsecond⟩

set_option maxHeartbeats 3000000 in
/-- Type-level inner regularity of the fixed-presentation pulled matrix
cutoff limit. -/
def centralPhysicalFinitePulledVacuumSectorMatrixQuadraticInnerRegularity
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (base half : Nat) (coefficient : Nat → Q') :
    CReal.InnerRegularity
      (centralPhysicalFinitePulledVacuumSectorMatrixQuadraticCutoffLimit
        hw0 hw1 base half coefficient) where
  rate :=
    centralPhysicalFinitePulledVacuumSectorMatrixQuadraticCutoffRate
      hw0 base half coefficient
  regular := by
    intro epsilon hepsilon first second hfirst hsecond
    exact
      centralPhysicalFinitePulledVacuumSectorMatrixQuadraticCutoff_regular
        hw0 hw1 base half coefficient epsilon hepsilon
        first second hfirst hsecond

end YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFormCauchy

#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFormCauchy.centralPhysicalFinitePulledVacuumSectorWeightedMeanCutoffRate
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFormCauchy.centralPhysicalFinitePulledVacuumSectorWeightedMeanCutoff_regular
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFormCauchy.centralPhysicalFinitePulledVacuumSectorWeightedMeanCutoffLimit
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFormCauchy.centralPhysicalFinitePulledVacuumSectorDiagonalQuadraticCutoffLimit
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFormCauchy.centralPhysicalFinitePulledVacuumSectorMatrixQuadraticCutoff_regular
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFormCauchy.centralPhysicalFinitePulledVacuumSectorMatrixQuadraticCutoffLimit
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFormCauchy.centralPhysicalFinitePulledVacuumSectorMatrixQuadraticInnerRegularity
