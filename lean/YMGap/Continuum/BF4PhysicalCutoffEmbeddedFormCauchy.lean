/-
# Cauchy limits of pulled physical means and quadratic forms

Entrywise cutoff convergence on a fixed old carrier is lifted here to the
complete finite weighted mean, diagonal quadratic, and reflected matrix
quadratic for every fixed rational coefficient vector.  The moduli explicitly
pay the coefficient `l1` envelope (or its square) before invoking the physical
source/pair cylinder modulus.

The resulting Bishop reals describe the old finite coordinate subspace
embedded in every later cutoff, equivalently extending its coefficient vector
by zero on all new states.  This is not yet a strict limiting gap: exact
centering changes with the stationary weights, and no estimate here identifies
the cutoff-two `49/50` form with its cutoff-removed limit.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalCutoffEmbeddedEntryCauchy
import YMGap.Continuum.Z4FiniteCylinderQuadraticStability

namespace YMGap.Continuum.BF4PhysicalCutoffEmbeddedFormCauchy

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Constructive.ExpNeg
open YMGap.Continuum.BF4PhysicalCutoffEmbeddedEntryCauchy
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4SU2CorrectedSlabBoundedObservableTail
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteRationalLDLCertificate
open YMGap.Continuum.FiniteRationalReversibleSpectralCertificate
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Finite form values on the embedded old carrier -/

/-- Pulled stationary mean on the entire fixed old positive carrier. -/
def centralPhysicalFinitePulledWeightedMean
    (w : Q') (hw : (0 : Q') ≤ w)
    (base later half : Nat) (coefficient : Nat → Q') : Q' :=
  finiteWeightedMean
    (centralPhysicalFiniteCarrierSize w hw base half)
    (centralPhysicalFinitePulledWeight w hw base later half)
    coefficient

/-- Pulled stationary diagonal quadratic on the fixed old carrier. -/
def centralPhysicalFinitePulledDiagonalQuadratic
    (w : Q') (hw : (0 : Q') ≤ w)
    (base later half : Nat) (coefficient : Nat → Q') : Q' :=
  finiteDiagonalQuadratic
    (centralPhysicalFiniteCarrierSize w hw base half)
    (centralPhysicalFinitePulledWeight w hw base later half)
    coefficient

/-- Pulled normalized reflected quadratic on the fixed old carrier. -/
def centralPhysicalFinitePulledMatrixQuadratic
    (w : Q') (hw : (0 : Q') ≤ w)
    (base later half : Nat) (coefficient : Nat → Q') : Q' :=
  finiteMatrixQuadratic
    (centralPhysicalFiniteCarrierSize w hw base half)
    (centralPhysicalFinitePulledKernel w hw base later half)
    coefficient

/-! ## 2. Generic finite-sum stability -/

theorem finiteLinearForm_abs_sub_le_l1_on
    {State : Type} (states : List State)
    (coefficient left right : State → Q')
    (epsilon : Q')
    (herror : ∀ state, state ∈ states →
      Q'.abs (left state + (-right state)) ≤ epsilon) :
    Q'.abs
        (listQSum (fun state => coefficient state * left state) states +
          (-listQSum (fun state => coefficient state * right state) states)) ≤
      coefficientL1 states coefficient * epsilon := by
  have hsum := abs_listQSum_sub_le
    (fun state => coefficient state * left state)
    (fun state => coefficient state * right state)
    states
  refine Q'.le_trans' _ _ _ hsum ?_
  have hterms :
      listQSum
          (fun state => Q'.abs
            (coefficient state * left state +
              (-(coefficient state * right state))))
          states ≤
        listQSum
          (fun state => Q'.abs (coefficient state) * epsilon)
          states := by
    apply listQSum_mono
    intro state hstate
    exact abs_common_mul_sub_le
      (coefficient state) (left state) (right state) epsilon
      (herror state hstate)
  refine Q'.le_trans' _ _ _ hterms ?_
  unfold coefficientL1
  exact Q'.le_of_eqv
    (listQSum_mul_right
      (fun state => Q'.abs (coefficient state)) epsilon states)

private theorem finiteLinearForm_abs_sub_le_l1
    (n : Nat) (coefficient left right : Nat → Q')
    (epsilon : Q')
    (herror : ∀ index, index < n →
      Q'.abs (left index + (-right index)) ≤ epsilon) :
    Q'.abs
        (listQSum (fun index => coefficient index * left index)
            (List.range n) +
          (-listQSum (fun index => coefficient index * right index)
            (List.range n))) ≤
      coefficientL1 (List.range n) coefficient * epsilon := by
  exact finiteLinearForm_abs_sub_le_l1_on
    (List.range n) coefficient left right epsilon
    (fun index hindex => herror index (List.mem_range.mp hindex))

theorem coefficientL1_nonnegative_local
    {State : Type} (states : List State) (coefficient : State → Q') :
    (0 : Q') ≤ coefficientL1 states coefficient := by
  unfold coefficientL1
  apply listQSum_nonnegative_on
  intro state _
  exact Q'.abs_nonneg (coefficient state)

theorem positive_scale
    {baseScale : Q'} (hbase : (0 : Q') ≤ baseScale) :
    (0 : Q') < baseScale + 1 := by
  have hone : (0 : Q') < (1 : Q') := by decide
  have hle : (1 : Q') ≤ baseScale + 1 := by
    have hadd := Q'.add_le_add_right
      (0 : Q') baseScale 1 hbase
    simpa only [Q'.zero_add'] using hadd
  exact Q'.pos_of_lt_of_le hone hle

theorem scaled_divPos_le_epsilon
    {baseScale epsilon : Q'}
    (hbase : (0 : Q') ≤ baseScale)
    (hepsilon : (0 : Q') < epsilon) :
    baseScale *
        Q'.divPos epsilon (baseScale + 1)
          (positive_scale hbase) ≤
      epsilon := by
  let scale := baseScale + 1
  let tolerance := Q'.divPos epsilon scale (positive_scale hbase)
  have htolerance0 : (0 : Q') ≤ tolerance :=
    Q'.le_of_lt
      (Q'.divPos_pos epsilon scale (positive_scale hbase) hepsilon)
  have hbaseScale : baseScale ≤ scale :=
    Q'.add_le_self_of_nonneg baseScale 1 Q'.zero_le_one
  have hscaled : baseScale * tolerance ≤ scale * tolerance :=
    Q'.mul_le_mul_of_nonneg_right _ _ tolerance
      hbaseScale htolerance0
  have hcollapse : scale * tolerance ≈ epsilon :=
    Q'.eqv_trans _ (tolerance * scale) _
      (Q'.mul_comm_eqv scale tolerance)
      (Q'.divPos_mul_eqv epsilon scale (positive_scale hbase))
  exact Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv hcollapse)

theorem two_sided_add_of_abs_sub_le_local
    {left right epsilon : Q'}
    (habs : Q'.abs (left + (-right)) ≤ epsilon) :
    left ≤ right + epsilon ∧ right ≤ left + epsilon := by
  constructor
  · exact ExpNeg.le_add_of_abs_sub_le habs
  · apply ExpNeg.le_add_of_abs_sub_le
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (YMGap.Continuum.TsumDeriv.Q'.abs_sub_comm right left))
      habs

/-! ## 3. Whole-form cutoff Cauchy estimates -/

/-- The pulled weighted mean is a constructive Cauchy sequence for every
fixed rational coefficient vector. -/
def centralPhysicalFinitePulledWeightedMeanCutoffLimit
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (base half : Nat) (coefficient : Nat → Q') : CReal where
  approx later := centralPhysicalFinitePulledWeightedMean
    w (Q'.le_of_lt hw0) base later half coefficient
  cauchy := by
    intro epsilon hepsilon
    let n := centralPhysicalFiniteCarrierSize
      w (Q'.le_of_lt hw0) base half
    let baseScale := coefficientL1 (List.range n) coefficient
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
    have hentry : ∀ index, index < n →
        Q'.abs
          (centralPhysicalFinitePulledWeight
              w (Q'.le_of_lt hw0) base first half index +
            (-centralPhysicalFinitePulledWeight
              w (Q'.le_of_lt hw0) base second half index)) ≤
          tolerance := by
      intro index hindex
      exact CReal.abs_sub_le_of_bounds
        (centralPhysicalFinitePulledWeight_twoSided_of_modulus
          hw0 hw1 htolerance hbaseFirst hbaseSecond
          hmodFirst hmodSecond hindex).1
        (centralPhysicalFinitePulledWeight_twoSided_of_modulus
          hw0 hw1 htolerance hbaseFirst hbaseSecond
          hmodFirst hmodSecond hindex).2
    have habs :
        Q'.abs
          (centralPhysicalFinitePulledWeightedMean
              w (Q'.le_of_lt hw0) base first half coefficient +
            (-centralPhysicalFinitePulledWeightedMean
              w (Q'.le_of_lt hw0) base second half coefficient)) ≤
          baseScale * tolerance := by
      unfold centralPhysicalFinitePulledWeightedMean finiteWeightedMean
      exact finiteLinearForm_abs_sub_le_l1
        n coefficient
        (centralPhysicalFinitePulledWeight
          w (Q'.le_of_lt hw0) base first half)
        (centralPhysicalFinitePulledWeight
          w (Q'.le_of_lt hw0) base second half)
        tolerance hentry
    exact two_sided_add_of_abs_sub_le_local
      (Q'.le_trans' _ _ _ habs
        (scaled_divPos_le_epsilon hbaseScale hepsilon))

/-- The pulled diagonal quadratic is a constructive Cauchy sequence for every
fixed rational coefficient vector. -/
def centralPhysicalFinitePulledDiagonalQuadraticCutoffLimit
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (base half : Nat) (coefficient : Nat → Q') : CReal where
  approx later := centralPhysicalFinitePulledDiagonalQuadratic
    w (Q'.le_of_lt hw0) base later half coefficient
  cauchy := by
    intro epsilon hepsilon
    let n := centralPhysicalFiniteCarrierSize
      w (Q'.le_of_lt hw0) base half
    let squaredCoefficient := fun index =>
      coefficient index * coefficient index
    let baseScale := coefficientL1
      (List.range n) squaredCoefficient
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
    have hentry : ∀ index, index < n →
        Q'.abs
          (centralPhysicalFinitePulledWeight
              w (Q'.le_of_lt hw0) base first half index +
            (-centralPhysicalFinitePulledWeight
              w (Q'.le_of_lt hw0) base second half index)) ≤
          tolerance := by
      intro index hindex
      exact CReal.abs_sub_le_of_bounds
        (centralPhysicalFinitePulledWeight_twoSided_of_modulus
          hw0 hw1 htolerance hbaseFirst hbaseSecond
          hmodFirst hmodSecond hindex).1
        (centralPhysicalFinitePulledWeight_twoSided_of_modulus
          hw0 hw1 htolerance hbaseFirst hbaseSecond
          hmodFirst hmodSecond hindex).2
    have habs :
        Q'.abs
          (centralPhysicalFinitePulledDiagonalQuadratic
              w (Q'.le_of_lt hw0) base first half coefficient +
            (-centralPhysicalFinitePulledDiagonalQuadratic
              w (Q'.le_of_lt hw0) base second half coefficient)) ≤
          baseScale * tolerance := by
      unfold centralPhysicalFinitePulledDiagonalQuadratic
        finiteDiagonalQuadratic
      exact finiteLinearForm_abs_sub_le_l1
        n squaredCoefficient
        (centralPhysicalFinitePulledWeight
          w (Q'.le_of_lt hw0) base first half)
        (centralPhysicalFinitePulledWeight
          w (Q'.le_of_lt hw0) base second half)
        tolerance hentry
    exact two_sided_add_of_abs_sub_le_local
      (Q'.le_trans' _ _ _ habs
        (scaled_divPos_le_epsilon hbaseScale hepsilon))

/-- The pulled reflected matrix quadratic is a constructive Cauchy sequence
for every fixed rational coefficient vector. -/
def centralPhysicalFinitePulledMatrixQuadraticCutoffLimit
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (base half : Nat) (coefficient : Nat → Q') : CReal where
  approx later := centralPhysicalFinitePulledMatrixQuadratic
    w (Q'.le_of_lt hw0) base later half coefficient
  cauchy := by
    intro epsilon hepsilon
    let n := centralPhysicalFiniteCarrierSize
      w (Q'.le_of_lt hw0) base half
    let l1 := coefficientL1 (List.range n) coefficient
    let baseScale := l1 * l1
    have hl1 : (0 : Q') ≤ l1 := coefficientL1_nonnegative_local _ _
    have hbaseScale : (0 : Q') ≤ baseScale :=
      Q'.mul_nonneg _ _ hl1 hl1
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
    have hentry : ∀ row column,
        row ∈ List.range n → column ∈ List.range n →
        Q'.abs
          (centralPhysicalFinitePulledKernel
              w (Q'.le_of_lt hw0) base first half row column +
            (-centralPhysicalFinitePulledKernel
              w (Q'.le_of_lt hw0) base second half row column)) ≤
          tolerance := by
      intro row column hrow hcolumn
      have htwo := centralPhysicalFinitePulledKernel_twoSided_of_modulus
        hw0 hw1 htolerance hbaseFirst hbaseSecond
        hmodFirst hmodSecond
        (List.mem_range.mp hrow) (List.mem_range.mp hcolumn)
      exact CReal.abs_sub_le_of_bounds htwo.1 htwo.2
    have habs :
        Q'.abs
          (centralPhysicalFinitePulledMatrixQuadratic
              w (Q'.le_of_lt hw0) base first half coefficient +
            (-centralPhysicalFinitePulledMatrixQuadratic
              w (Q'.le_of_lt hw0) base second half coefficient)) ≤
          baseScale * tolerance := by
      unfold centralPhysicalFinitePulledMatrixQuadratic
        finiteMatrixQuadratic
      change Q'.abs
          (finiteJointQuadratic (List.range n) coefficient
              (centralPhysicalFinitePulledKernel
                w (Q'.le_of_lt hw0) base first half) +
            (-finiteJointQuadratic (List.range n) coefficient
              (centralPhysicalFinitePulledKernel
                w (Q'.le_of_lt hw0) base second half))) ≤
        baseScale * tolerance
      exact finiteJointQuadratic_abs_sub_le_square
        (List.range n) coefficient
        (centralPhysicalFinitePulledKernel
          w (Q'.le_of_lt hw0) base first half)
        (centralPhysicalFinitePulledKernel
          w (Q'.le_of_lt hw0) base second half)
        tolerance (Q'.le_of_lt htolerance) hentry
    exact two_sided_add_of_abs_sub_le_local
      (Q'.le_trans' _ _ _ habs
        (scaled_divPos_le_epsilon hbaseScale hepsilon))

end YMGap.Continuum.BF4PhysicalCutoffEmbeddedFormCauchy

#print axioms
  YMGap.Continuum.BF4PhysicalCutoffEmbeddedFormCauchy.centralPhysicalFinitePulledWeightedMeanCutoffLimit
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffEmbeddedFormCauchy.centralPhysicalFinitePulledDiagonalQuadraticCutoffLimit
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffEmbeddedFormCauchy.centralPhysicalFinitePulledMatrixQuadraticCutoffLimit
