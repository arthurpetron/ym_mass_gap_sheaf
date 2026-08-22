/-
# Cauchy limit of the root-centered vacuum-sector reflected form

Root centering changes a fixed base-sector coefficient by a moving scalar
multiple of the root indicator.  Bilinearity expands the reflected quadratic
into the raw fixed-coefficient form, two root cross forms, and one root-root
form.  This file first proves that every fixed-coefficient pulled bilinear
form is cutoff-Cauchy, then combines those limits with the already constructed
head-correction Bishop real.

The final Bishop real has as its literal approximants the physical reflected
quadratic of the moving exactly centered coefficient.  This closes form-limit
existence for each fixed base coefficient; it does not provide the strict
rate uniform in the base cutoff needed for a spectral gap.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4ExactPhysicalCenteredVacuumMomentExpansion
import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCenteredDiagonalCauchy

namespace YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCenteredMatrixCauchy

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Constructive.ExpNeg
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumMomentExpansion
open YMGap.Continuum.BF4PhysicalCutoffEmbeddedEntryCauchy
open YMGap.Continuum.BF4PhysicalCutoffEmbeddedFormCauchy
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCenteredDiagonalCauchy
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFormCauchy
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorHeadCentering
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorHeadCorrectionCauchy
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4SU2CorrectedSlabBoundedObservableTail
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast_local (a : Q') : (-a).num = -(a.num) := rfl

local macro "q_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast_local,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one,
               Int.zero_mul, Int.mul_zero, Int.add_zero, Int.zero_add];
             try ac_rfl))

/-! ## 1. Fixed-coefficient finite bilinear stability -/

/-- Literal pair `l1` envelope for two different coefficient vectors. -/
def coefficientBilinearPairL1 {State : Type}
    (states : List State)
    (leftCoefficient rightCoefficient : State → Q') : Q' :=
  listQSum
    (fun left => listQSum
      (fun right =>
        Q'.abs (leftCoefficient left * rightCoefficient right))
      states)
    states

theorem coefficientBilinearPairL1_le_product {State : Type}
    (states : List State)
    (leftCoefficient rightCoefficient : State → Q') :
    coefficientBilinearPairL1 states leftCoefficient rightCoefficient ≤
      coefficientL1 states leftCoefficient *
        coefficientL1 states rightCoefficient := by
  have hpointwise :
      coefficientBilinearPairL1 states leftCoefficient rightCoefficient ≤
        listQSum
          (fun left => listQSum
            (fun right =>
              Q'.abs (leftCoefficient left) *
                Q'.abs (rightCoefficient right))
            states)
          states := by
    unfold coefficientBilinearPairL1
    apply listQSum_mono
    intro left _hleft
    apply listQSum_mono
    intro right _hright
    exact YMGap.Continuum.TsumDeriv.Q'.abs_mul_le _ _
  refine Q'.le_trans' _ _ _ hpointwise ?_
  exact Q'.le_of_eqv
    (listQSum_product
      (fun state => Q'.abs (leftCoefficient state))
      (fun state => Q'.abs (rightCoefficient state))
      states states)

/-- A uniform entrywise kernel error controls a finite bilinear form by the
literal cross-coefficient pair envelope. -/
theorem finiteJointBilinear_abs_sub_le_pairL1
    {State : Type}
    (states : List State)
    (leftCoefficient rightCoefficient : State → Q')
    (leftLaw rightLaw : State → State → Q')
    (epsilon : Q')
    (herror : ∀ left right, left ∈ states → right ∈ states →
      Q'.abs (leftLaw left right + (-rightLaw left right)) ≤ epsilon) :
    Q'.abs
        (finiteJointBilinear states leftCoefficient rightCoefficient leftLaw +
          (-finiteJointBilinear
            states leftCoefficient rightCoefficient rightLaw)) ≤
      coefficientBilinearPairL1
        states leftCoefficient rightCoefficient * epsilon := by
  let leftRow : State → Q' := fun left =>
    listQSum
      (fun right =>
        (leftCoefficient left * rightCoefficient right) *
          leftLaw left right)
      states
  let rightRow : State → Q' := fun left =>
    listQSum
      (fun right =>
        (leftCoefficient left * rightCoefficient right) *
          rightLaw left right)
      states
  have houter := abs_listQSum_sub_le leftRow rightRow states
  have hrows :
      listQSum
          (fun left => Q'.abs (leftRow left + (-rightRow left)))
          states ≤
        listQSum
          (fun left => listQSum
            (fun right =>
              Q'.abs (leftCoefficient left * rightCoefficient right))
            states * epsilon)
          states := by
    apply listQSum_mono
    intro left hleft
    have hinner := abs_listQSum_sub_le
      (fun right =>
        (leftCoefficient left * rightCoefficient right) *
          leftLaw left right)
      (fun right =>
        (leftCoefficient left * rightCoefficient right) *
          rightLaw left right)
      states
    refine Q'.le_trans' _ _ _ hinner ?_
    have hterms :
        listQSum
            (fun right => Q'.abs
              ((leftCoefficient left * rightCoefficient right) *
                  leftLaw left right +
                (-((leftCoefficient left * rightCoefficient right) *
                  rightLaw left right))))
            states ≤
          listQSum
            (fun right =>
              Q'.abs (leftCoefficient left * rightCoefficient right) *
                epsilon)
            states := by
      apply listQSum_mono
      intro right hright
      exact abs_common_mul_sub_le
        (leftCoefficient left * rightCoefficient right)
        (leftLaw left right) (rightLaw left right) epsilon
        (herror left right hleft hright)
    refine Q'.le_trans' _ _ _ hterms ?_
    exact Q'.le_of_eqv
      (listQSum_mul_right
        (fun right =>
          Q'.abs (leftCoefficient left * rightCoefficient right))
        epsilon states)
  unfold finiteJointBilinear
  change Q'.abs
    (listQSum leftRow states + (-listQSum rightRow states)) ≤ _
  refine Q'.le_trans' _ _ _ houter
    (Q'.le_trans' _ _ _ hrows ?_)
  exact Q'.le_of_eqv
    (listQSum_mul_right
      (fun left => listQSum
        (fun right =>
          Q'.abs (leftCoefficient left * rightCoefficient right))
        states)
      epsilon states)

theorem finiteJointBilinear_abs_sub_le_productL1
    {State : Type}
    (states : List State)
    (leftCoefficient rightCoefficient : State → Q')
    (leftLaw rightLaw : State → State → Q')
    (epsilon : Q') (hepsilon : (0 : Q') ≤ epsilon)
    (herror : ∀ left right, left ∈ states → right ∈ states →
      Q'.abs (leftLaw left right + (-rightLaw left right)) ≤ epsilon) :
    Q'.abs
        (finiteJointBilinear states leftCoefficient rightCoefficient leftLaw +
          (-finiteJointBilinear
            states leftCoefficient rightCoefficient rightLaw)) ≤
      (coefficientL1 states leftCoefficient *
        coefficientL1 states rightCoefficient) * epsilon := by
  refine Q'.le_trans' _ _ _
    (finiteJointBilinear_abs_sub_le_pairL1
      states leftCoefficient rightCoefficient
      leftLaw rightLaw epsilon herror) ?_
  exact Q'.mul_le_mul_of_nonneg_right _ _ _
    (coefficientBilinearPairL1_le_product
      states leftCoefficient rightCoefficient) hepsilon

/-! ## 2. Pulled vacuum-sector bilinear Bishop reals -/

def centralPhysicalFinitePulledVacuumSectorMatrixBilinear
    (w : Q') (hw : (0 : Q') ≤ w)
    (base later half : Nat)
    (leftCoefficient rightCoefficient : Nat → Q') : Q' :=
  finiteJointBilinear
    (centralPhysicalFiniteVacuumSectorIndices w hw base half)
    leftCoefficient rightCoefficient
    (centralPhysicalFinitePulledKernel w hw base later half)

/-- Every pair of fixed base-sector coefficient vectors has a constructive
pulled reflected bilinear cutoff limit. -/
def centralPhysicalFinitePulledVacuumSectorMatrixBilinearCutoffLimit
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (base half : Nat)
    (leftCoefficient rightCoefficient : Nat → Q') : CReal where
  approx later := centralPhysicalFinitePulledVacuumSectorMatrixBilinear
    w (Q'.le_of_lt hw0) base later half
    leftCoefficient rightCoefficient
  cauchy := by
    intro epsilon hepsilon
    let states := centralPhysicalFiniteVacuumSectorIndices
      w (Q'.le_of_lt hw0) base half
    let leftL1 := coefficientL1 states leftCoefficient
    let rightL1 := coefficientL1 states rightCoefficient
    let baseScale := leftL1 * rightL1
    have hleftL1 : (0 : Q') ≤ leftL1 :=
      coefficientL1_nonnegative_local _ _
    have hrightL1 : (0 : Q') ≤ rightL1 :=
      coefficientL1_nonnegative_local _ _
    have hbaseScale : (0 : Q') ≤ baseScale :=
      Q'.mul_nonneg _ _ hleftL1 hrightL1
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
          (centralPhysicalFinitePulledVacuumSectorMatrixBilinear
              w (Q'.le_of_lt hw0) base first half
              leftCoefficient rightCoefficient +
            (-centralPhysicalFinitePulledVacuumSectorMatrixBilinear
              w (Q'.le_of_lt hw0) base second half
              leftCoefficient rightCoefficient)) ≤
          baseScale * tolerance := by
      unfold centralPhysicalFinitePulledVacuumSectorMatrixBilinear
      exact finiteJointBilinear_abs_sub_le_productL1
        states leftCoefficient rightCoefficient
        (centralPhysicalFinitePulledKernel
          w (Q'.le_of_lt hw0) base first half)
        (centralPhysicalFinitePulledKernel
          w (Q'.le_of_lt hw0) base second half)
        tolerance (Q'.le_of_lt htolerance) hentry
    exact two_sided_add_of_abs_sub_le_local
      (Q'.le_trans' _ _ _ habs
        (scaled_divPos_le_epsilon hbaseScale hepsilon))

/-! ## 3. Exact moving root expansion -/

/-- The distinguished root basis vector on a finite index carrier. -/
def finiteRootIndicator (index : Nat) : Q' :=
  if index = 0 then 1 else 0

theorem finiteJointBilinear_coefficient_eqv_on
    {State : Type} (states : List State)
    (left₁ left₂ right₁ right₂ : State → Q')
    (joint : State → State → Q')
    (hleft : ∀ state, state ∈ states → left₁ state ≈ left₂ state)
    (hright : ∀ state, state ∈ states → right₁ state ≈ right₂ state) :
    finiteJointBilinear states left₁ right₁ joint ≈
      finiteJointBilinear states left₂ right₂ joint := by
  unfold finiteJointBilinear
  apply listQSum_congr_on
  intro left hleftMem
  apply listQSum_congr_on
  intro right hrightMem
  have hpair : left₁ left * right₁ right ≈
      left₂ left * right₂ right :=
    Q'.eqv_trans _ (left₂ left * right₁ right) _
      (Q'.mul_eqv_congr_right _ _ _ (hleft left hleftMem))
      (Q'.mul_eqv_congr_left _ _ _ (hright right hrightMem))
  exact Q'.mul_eqv_congr_right _ _ _ hpair

theorem finiteJointBilinear_scale_left
    {State : Type} (states : List State)
    (scalar : Q') (left right : State → Q')
    (joint : State → State → Q') :
    finiteJointBilinear states
        (fun state => scalar * left state) right joint ≈
      scalar * finiteJointBilinear states left right joint := by
  unfold finiteJointBilinear
  refine Q'.eqv_trans _
    (listQSum
      (fun leftState => scalar *
        listQSum
          (fun rightState =>
            (left leftState * right rightState) *
              joint leftState rightState)
          states)
      states) _ ?_ ?_
  · apply listQSum_congr_on
    intro leftState _hleft
    refine Q'.eqv_trans _
      (listQSum
        (fun rightState => scalar *
          ((left leftState * right rightState) *
            joint leftState rightState))
        states) _ ?_ ?_
    · apply listQSum_congr_on
      intro rightState _hright
      q_ring
    · exact listQSum_mul_left scalar _ states
  · exact listQSum_mul_left scalar _ states

theorem finiteJointBilinear_scale_right
    {State : Type} (states : List State)
    (scalar : Q') (left right : State → Q')
    (joint : State → State → Q') :
    finiteJointBilinear states left
        (fun state => scalar * right state) joint ≈
      scalar * finiteJointBilinear states left right joint := by
  unfold finiteJointBilinear
  refine Q'.eqv_trans _
    (listQSum
      (fun leftState => scalar *
        listQSum
          (fun rightState =>
            (left leftState * right rightState) *
              joint leftState rightState)
          states)
      states) _ ?_ ?_
  · apply listQSum_congr_on
    intro leftState _hleft
    refine Q'.eqv_trans _
      (listQSum
        (fun rightState => scalar *
          ((left leftState * right rightState) *
            joint leftState rightState))
        states) _ ?_ ?_
    · apply listQSum_congr_on
      intro rightState _hright
      q_ring
    · exact listQSum_mul_left scalar _ states
  · exact listQSum_mul_left scalar _ states

/-- Quadratic expansion along a scalar multiple of an arbitrary fixed basis
vector. -/
theorem finiteJointBilinear_add_scaled_self
    {State : Type} (states : List State)
    (coefficient basis : State → Q') (scalar : Q')
    (joint : State → State → Q') :
    finiteJointBilinear states
        (fun state => coefficient state + scalar * basis state)
        (fun state => coefficient state + scalar * basis state) joint ≈
      finiteJointBilinear states coefficient coefficient joint +
        (scalar * finiteJointBilinear states coefficient basis joint +
          (scalar * finiteJointBilinear states basis coefficient joint +
            (scalar * scalar) *
              finiteJointBilinear states basis basis joint)) := by
  let scaled := fun state => scalar * basis state
  refine Q'.eqv_trans _
    (finiteJointBilinear states coefficient
        (fun state => coefficient state + scaled state) joint +
      finiteJointBilinear states scaled
        (fun state => coefficient state + scaled state) joint) _
    (finiteJointBilinear_add_left states coefficient scaled
      (fun state => coefficient state + scaled state) joint) ?_
  refine Q'.eqv_trans _
    ((finiteJointBilinear states coefficient coefficient joint +
        finiteJointBilinear states coefficient scaled joint) +
      (finiteJointBilinear states scaled coefficient joint +
        finiteJointBilinear states scaled scaled joint)) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (finiteJointBilinear_add_right
        states coefficient coefficient scaled joint)
      (finiteJointBilinear_add_right
        states scaled coefficient scaled joint)
  have hright := finiteJointBilinear_scale_right
    states scalar coefficient basis joint
  have hleft := finiteJointBilinear_scale_left
    states scalar basis coefficient joint
  have hscaledLeft := finiteJointBilinear_scale_left
    states scalar basis scaled joint
  have hscaledRight := finiteJointBilinear_scale_right
    states scalar basis basis joint
  have hdouble :
      finiteJointBilinear states scaled scaled joint ≈
        (scalar * scalar) *
          finiteJointBilinear states basis basis joint := by
    exact Q'.eqv_trans _
      (scalar * finiteJointBilinear states basis scaled joint) _
      hscaledLeft
      (Q'.eqv_trans _
        (scalar *
          (scalar * finiteJointBilinear states basis basis joint)) _
        (Q'.mul_eqv_congr_left _ _ _ hscaledRight)
        (Q'.eqv_symm
          (Q'.mul_assoc_eqv scalar scalar
            (finiteJointBilinear states basis basis joint))))
  exact Q'.eqv_trans _
    ((finiteJointBilinear states coefficient coefficient joint +
        scalar * finiteJointBilinear states coefficient basis joint) +
      (scalar * finiteJointBilinear states basis coefficient joint +
        (scalar * scalar) *
          finiteJointBilinear states basis basis joint)) _
    (Q'.add_eqv_congr'
      (Q'.add_eqv_congr' (Q'.eqv_refl _) hright)
      (Q'.add_eqv_congr' hleft hdouble))
    (Q'.add_assoc_eqv _ _ _)

theorem centralPhysicalFinitePulledVacuumSectorHeadCenteredCoefficient_eqv_rootShift
    {w : Q'} (hw0 : (0 : Q') < w)
    (base later half index : Nat) (coefficient : Nat → Q') :
    centralPhysicalFinitePulledVacuumSectorHeadCenteredCoefficient
        w (Q'.le_of_lt hw0) base later half coefficient index ≈
      coefficient index +
        (-centralPhysicalFinitePulledVacuumSectorHeadCorrectionApprox
          hw0 base half coefficient later) * finiteRootIndicator index := by
  unfold centralPhysicalFinitePulledVacuumSectorHeadCenteredCoefficient
    finiteListRootCenteredCoefficient
    centralPhysicalFinitePulledVacuumSectorHeadCorrectionApprox
    centralPhysicalFinitePulledVacuumSectorWeightedMean
    finiteRootIndicator
  by_cases hzero : index = 0
  · subst index
    simp only [ite_true]
    exact Q'.add_eqv_congr_left _ _ _
      (Q'.eqv_symm
        (Q'.mul_one_eqv
          (-Q'.divPos
            (listQSum
              (fun item => coefficient item *
                centralPhysicalFinitePulledWeight
                  w (Q'.le_of_lt hw0) base later half item)
              (centralPhysicalFiniteVacuumSectorIndices
                w (Q'.le_of_lt hw0) base half))
            (centralPhysicalFinitePulledWeight
              w (Q'.le_of_lt hw0) base later half 0)
            (centralPhysicalFinitePulledWeight_zero_pos
              w (Q'.le_of_lt hw0) base later half))))
  · simp only [if_neg hzero]
    exact Q'.add_eqv_congr_left _ _ _
      (Q'.eqv_symm (Q'.mul_zero_eqv _))

/-- Exact four-term expansion of the moving root-centered pulled reflected
quadratic at every cutoff. -/
theorem centralPhysicalFinitePulledVacuumSectorHeadCenteredMatrix_expansion
    {w : Q'} (hw0 : (0 : Q') < w)
    (base later half : Nat) (coefficient : Nat → Q') :
    centralPhysicalFinitePulledVacuumSectorMatrixQuadratic
        w (Q'.le_of_lt hw0) base later half
        (centralPhysicalFinitePulledVacuumSectorHeadCenteredCoefficient
          w (Q'.le_of_lt hw0) base later half coefficient) ≈
      centralPhysicalFinitePulledVacuumSectorMatrixQuadratic
          w (Q'.le_of_lt hw0) base later half coefficient +
        ((-centralPhysicalFinitePulledVacuumSectorHeadCorrectionApprox
            hw0 base half coefficient later) *
            centralPhysicalFinitePulledVacuumSectorMatrixBilinear
              w (Q'.le_of_lt hw0) base later half
              coefficient finiteRootIndicator +
          ((-centralPhysicalFinitePulledVacuumSectorHeadCorrectionApprox
              hw0 base half coefficient later) *
              centralPhysicalFinitePulledVacuumSectorMatrixBilinear
                w (Q'.le_of_lt hw0) base later half
                finiteRootIndicator coefficient +
            ((-centralPhysicalFinitePulledVacuumSectorHeadCorrectionApprox
                hw0 base half coefficient later) *
              (-centralPhysicalFinitePulledVacuumSectorHeadCorrectionApprox
                hw0 base half coefficient later)) *
              centralPhysicalFinitePulledVacuumSectorMatrixBilinear
                w (Q'.le_of_lt hw0) base later half
                finiteRootIndicator finiteRootIndicator)) := by
  let states := centralPhysicalFiniteVacuumSectorIndices
    w (Q'.le_of_lt hw0) base half
  let joint := centralPhysicalFinitePulledKernel
    w (Q'.le_of_lt hw0) base later half
  let centered :=
    centralPhysicalFinitePulledVacuumSectorHeadCenteredCoefficient
      w (Q'.le_of_lt hw0) base later half coefficient
  let shift :=
    -centralPhysicalFinitePulledVacuumSectorHeadCorrectionApprox
      hw0 base half coefficient later
  have hcoefficient : ∀ index, index ∈ states →
      centered index ≈ coefficient index + shift * finiteRootIndicator index := by
    intro index _hindex
    exact
      centralPhysicalFinitePulledVacuumSectorHeadCenteredCoefficient_eqv_rootShift
        hw0 base later half index coefficient
  unfold centralPhysicalFinitePulledVacuumSectorMatrixQuadratic
    centralPhysicalFinitePulledVacuumSectorMatrixBilinear
  change finiteJointBilinear states centered centered joint ≈ _
  refine Q'.eqv_trans _
    (finiteJointBilinear states
      (fun index => coefficient index + shift * finiteRootIndicator index)
      (fun index => coefficient index + shift * finiteRootIndicator index)
      joint) _ ?_ ?_
  · exact finiteJointBilinear_coefficient_eqv_on
      states centered
      (fun index => coefficient index + shift * finiteRootIndicator index)
      centered
      (fun index => coefficient index + shift * finiteRootIndicator index)
      joint hcoefficient hcoefficient
  · exact finiteJointBilinear_add_scaled_self
      states coefficient finiteRootIndicator shift joint

/-! ## 4. The actual centered reflected-form Bishop real -/

def centralPhysicalFinitePulledVacuumSectorHeadCenteredMatrixExpansionCutoffLimit
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (base half : Nat) (coefficient : Nat → Q') : CReal :=
  let raw :=
    centralPhysicalFinitePulledVacuumSectorMatrixQuadraticCutoffLimit
      hw0 hw1 base half coefficient
  let shift := CReal.neg
    (centralPhysicalFinitePulledVacuumSectorHeadCorrectionCutoffLimit
      hw0 hw1 base half coefficient)
  let rightCross :=
    centralPhysicalFinitePulledVacuumSectorMatrixBilinearCutoffLimit
      hw0 hw1 base half coefficient finiteRootIndicator
  let leftCross :=
    centralPhysicalFinitePulledVacuumSectorMatrixBilinearCutoffLimit
      hw0 hw1 base half finiteRootIndicator coefficient
  let rootRoot :=
    centralPhysicalFinitePulledVacuumSectorMatrixBilinearCutoffLimit
      hw0 hw1 base half finiteRootIndicator finiteRootIndicator
  CReal.add raw
    (CReal.add
      (CReal.mul shift rightCross)
      (CReal.add
        (CReal.mul shift leftCross)
        (CReal.mul (CReal.mul shift shift) rootRoot)))

theorem centralPhysicalFinitePulledVacuumSectorHeadCenteredMatrix_eqv_expansionApprox
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (base half : Nat) (coefficient : Nat → Q') (later : Nat) :
    centralPhysicalFinitePulledVacuumSectorMatrixQuadratic
        w (Q'.le_of_lt hw0) base later half
        (centralPhysicalFinitePulledVacuumSectorHeadCenteredCoefficient
          w (Q'.le_of_lt hw0) base later half coefficient) ≈
      (centralPhysicalFinitePulledVacuumSectorHeadCenteredMatrixExpansionCutoffLimit
        hw0 hw1 base half coefficient).approx later := by
  change
    centralPhysicalFinitePulledVacuumSectorMatrixQuadratic
        w (Q'.le_of_lt hw0) base later half
        (centralPhysicalFinitePulledVacuumSectorHeadCenteredCoefficient
          w (Q'.le_of_lt hw0) base later half coefficient) ≈
      centralPhysicalFinitePulledVacuumSectorMatrixQuadratic
          w (Q'.le_of_lt hw0) base later half coefficient +
        ((-centralPhysicalFinitePulledVacuumSectorHeadCorrectionApprox
            hw0 base half coefficient later) *
            centralPhysicalFinitePulledVacuumSectorMatrixBilinear
              w (Q'.le_of_lt hw0) base later half
              coefficient finiteRootIndicator +
          ((-centralPhysicalFinitePulledVacuumSectorHeadCorrectionApprox
              hw0 base half coefficient later) *
              centralPhysicalFinitePulledVacuumSectorMatrixBilinear
                w (Q'.le_of_lt hw0) base later half
                finiteRootIndicator coefficient +
            ((-centralPhysicalFinitePulledVacuumSectorHeadCorrectionApprox
                hw0 base half coefficient later) *
              (-centralPhysicalFinitePulledVacuumSectorHeadCorrectionApprox
                hw0 base half coefficient later)) *
              centralPhysicalFinitePulledVacuumSectorMatrixBilinear
                w (Q'.le_of_lt hw0) base later half
                finiteRootIndicator finiteRootIndicator))
  exact centralPhysicalFinitePulledVacuumSectorHeadCenteredMatrix_expansion
    hw0 base later half coefficient

/-- The literal moving exactly centered reflected quadratic is a Bishop real. -/
def centralPhysicalFinitePulledVacuumSectorHeadCenteredMatrixCutoffLimit
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (base half : Nat) (coefficient : Nat → Q') : CReal :=
  cRealRecodePointwiseEqv
    (centralPhysicalFinitePulledVacuumSectorHeadCenteredMatrixExpansionCutoffLimit
      hw0 hw1 base half coefficient)
    (fun later =>
      centralPhysicalFinitePulledVacuumSectorMatrixQuadratic
        w (Q'.le_of_lt hw0) base later half
        (centralPhysicalFinitePulledVacuumSectorHeadCenteredCoefficient
          w (Q'.le_of_lt hw0) base later half coefficient))
    (centralPhysicalFinitePulledVacuumSectorHeadCenteredMatrix_eqv_expansionApprox
      hw0 hw1 base half coefficient)

/-- The physical recoding exposes the literal moving reflected form as each
approximant.  Naming this definitional projection prevents downstream proofs
from unfolding the whole Cauchy construction merely to cross the seam. -/
theorem centralPhysicalFinitePulledVacuumSectorHeadCenteredMatrixCutoffLimit_approx
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (base half : Nat) (coefficient : Nat → Q') (later : Nat) :
    (centralPhysicalFinitePulledVacuumSectorHeadCenteredMatrixCutoffLimit
        hw0 hw1 base half coefficient).approx later =
      centralPhysicalFinitePulledVacuumSectorMatrixQuadratic
        w (Q'.le_of_lt hw0) base later half
        (centralPhysicalFinitePulledVacuumSectorHeadCenteredCoefficient
          w (Q'.le_of_lt hw0) base later half coefficient) :=
  rfl

end YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCenteredMatrixCauchy

#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCenteredMatrixCauchy.finiteJointBilinear_abs_sub_le_productL1
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCenteredMatrixCauchy.centralPhysicalFinitePulledVacuumSectorMatrixBilinearCutoffLimit
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCenteredMatrixCauchy.centralPhysicalFinitePulledVacuumSectorHeadCenteredMatrix_expansion
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCenteredMatrixCauchy.centralPhysicalFinitePulledVacuumSectorHeadCenteredMatrixCutoffLimit
