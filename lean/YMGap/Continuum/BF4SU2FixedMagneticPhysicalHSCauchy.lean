/-
# Dimension-compensated BF4 physical Hilbert--Schmidt cutoff Cauchy bound

Every old grouped BF4 joint-kernel entry has the executable degree-thirteen
cutoff modulus.  This module pays the complete square-carrier growth.

For a retained cutoff `base`, let `N` be the exact number of lower-half
states.  Ask the entrywise theorem for tolerance `epsilon / N`.  Then

    N * (N * (epsilon / N)^2) = epsilon^2

exactly in `Q'`.  The resulting explicit cutoff is also at least `base`, so
all rows and columns of the old carrier occur in both later cutoffs.
Consequently the genuine normalized BF4 joint kernels at any two later
cutoffs are Hilbert--Schmidt close on the entire retained square carrier.

Honest scope: this is nonlinear physical cutoff Cauchy convergence on a
moving finite carrier.  It does not define a distinct Gaussian Mehler
operator or bound the physical-minus-Mehler entries.

## Axiom gate

Finite list recursion and exact `Q'` order only.  No `Classical.*`, `sorry`,
`native_decide`, custom axiom, choice, or noncomputable declaration.
-/

import YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
import YMGap.Continuum.BF4EntrywiseSameCarrierHSConvergence

namespace YMGap.Continuum.BF4SU2FixedMagneticPhysicalHSCauchy

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum.BF4EntrywiseSameCarrierHSConvergence
open YMGap.Continuum.BF4SU2CorrectedSlabBoundedObservableTail
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4SU2FixedMagneticPositiveKernelConvergence
open YMGap.Continuum.FiniteCarrierHSPerronPerturbation
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The exact old square carrier -/

private theorem zeroEdgeLabelling_mem_halfStates
    (K half : Nat) :
    zeroEdgeLabelling ∈ centralHalfStates K half := by
  unfold centralHalfStates
  apply boundedEdgeLabellings_complete
  · intro _ _
    change 0 < K + 1
    omega
  · intro _ _
    rfl

theorem centralHalfStates_length_pos
    (K half : Nat) :
    0 < (centralHalfStates K half).length :=
  List.length_pos_of_mem
    (zeroEdgeLabelling_mem_halfStates K half)

private theorem qOfNat_pos_of_nat_pos
    (N : Nat) (hN : 0 < N) :
    (0 : Q') < Q'.ofNat N := by
  cases N with
  | zero => omega
  | succ predecessor =>
      exact Q'.ofNat_succ_pos predecessor

/-- In-range totalized lookup in the old lower-half carrier. -/
def centralOldStateAt
    (base half index : Nat) : EdgeLabelling :=
  (centralHalfStates base half).getD
    index zeroEdgeLabelling

theorem centralOldStateAt_mem
    {base half index : Nat}
    (hindex :
      index < (centralHalfStates base half).length) :
    centralOldStateAt base half index ∈
      centralHalfStates base half := by
  unfold centralOldStateAt
  rw [← List.getElem_eq_getD
    (l := centralHalfStates base half)
    (i := index)
    (h := hindex)
    zeroEdgeLabelling]
  exact List.getElem_mem hindex

private theorem centralHalfStates_mem_of_le
    {base later half : Nat}
    (hcutoff : base ≤ later)
    {state : EdgeLabelling}
    (hstate : state ∈ centralHalfStates base half) :
    state ∈ centralHalfStates later half := by
  unfold centralHalfStates at hstate ⊢
  have hsound :=
    boundedEdgeLabellings_sound
      base (centralLowerFaceIds half)
      state hstate
  apply boundedEdgeLabellings_complete
  · intro id hid
    have hbound := hsound.1 id hid
    omega
  · exact hsound.2

/-! ## 2. Dimension-scaled executable modulus -/

/-- Entry tolerance which exactly pays one factor of the old carrier
dimension in each Hilbert--Schmidt index. -/
def centralOldCarrierEntryTolerance
    (base half : Nat) (epsilon : Q') : Q' :=
  Q'.divPos epsilon
    (Q'.ofNat (centralHalfStates base half).length)
    (qOfNat_pos_of_nat_pos _
      (centralHalfStates_length_pos base half))

theorem centralOldCarrierEntryTolerance_pos
    (base half : Nat) {epsilon : Q'}
    (hepsilon : (0 : Q') < epsilon) :
    (0 : Q') <
      centralOldCarrierEntryTolerance
        base half epsilon := by
  unfold centralOldCarrierEntryTolerance
  exact Q'.divPos_pos _ _ _
    hepsilon

/-- The physical HS cutoff is both beyond the retained carrier and beyond
the degree-thirteen entry modulus at tolerance `epsilon / N`. -/
def centralOldCarrierHSCutoff
    (w : Q') (base half : Nat)
    (epsilon : Q') : Nat :=
  max base
    (slabNomeBoundedObservableModulus
      w (centralExtent half)
      (centralOldCarrierEntryTolerance
        base half epsilon))

/-! ## 3. The physical cutoff-difference matrix -/

/-- Difference of two genuine normalized BF4 joint kernels, restricted to
the same old square carrier. -/
def centralOldCarrierCutoffDifferenceMatrix
    (w : Q') (hw : (0 : Q') ≤ w)
    (base first second half : Nat) :
    RationalMatrix :=
  fun row column =>
    let left := centralOldStateAt base half row
    let right := centralOldStateAt base half column
    centralNormalizedPhysicalReflectedKernel
        w hw first half left right +
      -centralNormalizedPhysicalReflectedKernel
        w hw second half left right

/-- The degree-thirteen cutoff theorem, with cutoff nesting, gives the
dimension-scaled entry bound on every old row and column. -/
theorem centralOldCarrierCutoffDifferenceMatrix_entry_abs_le
    {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q'))
    (base half : Nat)
    {epsilon : Q'} (hepsilon : (0 : Q') < epsilon)
    {first second row column : Nat}
    (hfirst :
      centralOldCarrierHSCutoff
          w base half epsilon ≤ first)
    (hsecond :
      centralOldCarrierHSCutoff
          w base half epsilon ≤ second)
    (hrow :
      row < (centralHalfStates base half).length)
    (hcolumn :
      column < (centralHalfStates base half).length) :
    Q'.abs
        (centralOldCarrierCutoffDifferenceMatrix
          w (Q'.le_of_lt hw0)
          base first second half row column) ≤
      centralOldCarrierEntryTolerance
        base half epsilon := by
  let left := centralOldStateAt base half row
  let right := centralOldStateAt base half column
  have hbaseFirst : base ≤ first :=
    Nat.le_trans
      (Nat.le_max_left _ _) hfirst
  have hbaseSecond : base ≤ second :=
    Nat.le_trans
      (Nat.le_max_left _ _) hsecond
  have hmodulusFirst :
      slabNomeBoundedObservableModulus
          w (centralExtent half)
          (centralOldCarrierEntryTolerance
            base half epsilon) ≤
        first :=
    Nat.le_trans
      (Nat.le_max_right _ _) hfirst
  have hmodulusSecond :
      slabNomeBoundedObservableModulus
          w (centralExtent half)
          (centralOldCarrierEntryTolerance
            base half epsilon) ≤
        second :=
    Nat.le_trans
      (Nat.le_max_right _ _) hsecond
  have hleftBase :
      left ∈ centralHalfStates base half := by
    dsimp only [left]
    exact centralOldStateAt_mem hrow
  have hrightBase :
      right ∈ centralHalfStates base half := by
    dsimp only [right]
    exact centralOldStateAt_mem hcolumn
  have htwo :=
    centralNormalizedPhysicalReflectedKernel_twoSided_of_modulus
      hw0 hw1 half left right
      (centralOldCarrierEntryTolerance_pos
        base half hepsilon)
      hmodulusFirst hmodulusSecond
      (centralHalfStates_mem_of_le
        hbaseFirst hleftBase)
      (centralHalfStates_mem_of_le
        hbaseFirst hrightBase)
      (centralHalfStates_mem_of_le
        hbaseSecond hleftBase)
      (centralHalfStates_mem_of_le
        hbaseSecond hrightBase)
  unfold centralOldCarrierCutoffDifferenceMatrix
  dsimp only [left, right] at htwo ⊢
  exact CReal.abs_sub_le_of_bounds
    htwo.1 htwo.2

private theorem q_mul_congr
    {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') :
    a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

private theorem nested_square_rearrange
    (dimension tolerance : Q') :
    dimension *
        (dimension *
          (tolerance * tolerance)) ≈
      (tolerance * dimension) *
        (tolerance * dimension) := by
  show
    (dimension *
      (dimension *
        (tolerance * tolerance))).num *
        (((tolerance * dimension) *
          (tolerance * dimension)).den : Int) =
      ((tolerance * dimension) *
        (tolerance * dimension)).num *
        ((dimension *
          (dimension *
            (tolerance * tolerance))).den : Int)
  simp only [Q'.mul_num_cast, Q'.mul_den_cast]
  ac_rfl

/-- The dimension-scaled tolerance cancels the complete square-carrier
growth exactly. -/
theorem centralOldCarrier_dimension_tolerance_collapse
    (base half : Nat) (epsilon : Q') :
    let dimension :=
      Q'.ofNat (centralHalfStates base half).length
    let tolerance :=
      centralOldCarrierEntryTolerance
        base half epsilon
    dimension *
        (dimension *
          (tolerance * tolerance)) ≈
      epsilon * epsilon := by
  dsimp only
  refine Q'.eqv_trans _
    ((centralOldCarrierEntryTolerance
          base half epsilon *
        Q'.ofNat
          (centralHalfStates base half).length) *
      (centralOldCarrierEntryTolerance
          base half epsilon *
        Q'.ofNat
          (centralHalfStates base half).length)) _
    (nested_square_rearrange _ _) ?_
  apply q_mul_congr
  · unfold centralOldCarrierEntryTolerance
    exact Q'.divPos_mul_eqv _ _ _
  · unfold centralOldCarrierEntryTolerance
    exact Q'.divPos_mul_eqv _ _ _

/-! ## 4. Quantitative nonlinear physical HS convergence -/

/-- **Dimension-compensated nonlinear Hilbert--Schmidt Cauchy theorem.**

At every two cutoffs beyond the executable schedule, the genuine normalized
BF4 joint kernels are `epsilon`-close in HS norm on the entire old moving
carrier.  The theorem pays all `N^2` entries exactly. -/
theorem centralOldCarrierCutoffDifferenceHSSq_le
    {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q'))
    (base half : Nat)
    {epsilon : Q'} (hepsilon : (0 : Q') < epsilon)
    {first second : Nat}
    (hfirst :
      centralOldCarrierHSCutoff
          w base half epsilon ≤ first)
    (hsecond :
      centralOldCarrierHSCutoff
          w base half epsilon ≤ second) :
    matrixHSSq
        (centralOldCarrierCutoffDifferenceMatrix
          w (Q'.le_of_lt hw0)
          base first second half)
        (centralHalfStates base half).length ≤
      epsilon * epsilon := by
  let tolerance :=
    centralOldCarrierEntryTolerance
      base half epsilon
  have htolerance0 : (0 : Q') ≤ tolerance :=
    Q'.le_of_lt
      (centralOldCarrierEntryTolerance_pos
        base half hepsilon)
  refine Q'.le_trans' _ _ _
    (matrixHSSq_le_of_entrywise_abs
      (centralOldCarrierCutoffDifferenceMatrix
        w (Q'.le_of_lt hw0)
        base first second half)
      (centralHalfStates base half).length
      tolerance htolerance0
      (fun row hrow column hcolumn =>
        centralOldCarrierCutoffDifferenceMatrix_entry_abs_le
          hw0 hw1 base half hepsilon
          hfirst hsecond hrow hcolumn)) ?_
  exact Q'.le_of_eqv
    (centralOldCarrier_dimension_tolerance_collapse
      base half epsilon)

#print axioms centralHalfStates_length_pos
#print axioms centralOldStateAt_mem
#print axioms centralOldCarrierEntryTolerance_pos
#print axioms
  centralOldCarrierCutoffDifferenceMatrix_entry_abs_le
#print axioms centralOldCarrier_dimension_tolerance_collapse
#print axioms centralOldCarrierCutoffDifferenceHSSq_le

end YMGap.Continuum.BF4SU2FixedMagneticPhysicalHSCauchy
