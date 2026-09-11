/-
# Head--tail Gram gluing on the physical BF4 vacuum sector

The growing canonical SU(2) vacuum sector already has an exact old/new split.
This module turns that split into two literal coefficient functions on the
later carrier and packages the actual finite reflected kernel as a positive
`GNSData` form.  The generic scaled-positivity theorem then proves

    head rate q + tail rate tau  ==>  full rate q + tau.

In particular, mixed old/new matrix entries require no separate absolute-row
or congestion estimate: Gram positivity absorbs the entire cross block.

This is a structural physical theorem.  It does not supply the still-open
uniform low-spin comparison or high-spin trace bound, and asserts no
thermodynamic, continuum, or Clay conclusion.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorCenteredGram
import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorBlockDecomposition
import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCenteredMatrixCauchy
import YMGap.Continuum.FinitePositiveFormHeadTailGluing

namespace YMGap.Continuum.BF4PhysicalVacuumSectorHeadTailGramGap

open YMGap.Constructive
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumMomentExpansion
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorBlockDecomposition
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCenteredMatrixCauchy
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorGramPositivity
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4PhysicalVacuumSectorCenteredGram
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FinitePositiveFormHeadTailGluing
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.OSReconstructionProgress
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast_local (a : Q') : (-a).num = -(a.num) := rfl
private theorem zero_num_cast_local : (0 : Q').num = 0 := rfl
private theorem zero_den_cast_local : ((0 : Q').den : Int) = 1 := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast_local,
               Q'.mkPos_num, Q'.mkPos_den,
               Q'.ofNat_num_cast, Q'.ofNat_den_cast,
               zero_num_cast_local, zero_den_cast_local,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one,
               Int.zero_mul, Int.mul_zero, Int.zero_add, Int.add_zero]; ac_rfl))

private theorem symmetric_cross_regroup (A C D : Q') :
    (A + C) + (C + D) ≈ (A + 2 * C) + D := by
  refine Q'.eqv_trans _ (((A + C) + C) + D) _
    (Q'.eqv_symm (Q'.add_assoc_eqv (A + C) C D)) ?_
  have hinner : (A + C) + C ≈ A + 2 * C :=
    Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv A C C)
      (Q'.add_eqv_congr_left A _ _
        (OSReconstructionProgress.q_two_mul C))
  exact QPoly.q_add_congr hinner (Q'.eqv_refl D)

/-! ## 1. The actual finite physical Gram as a positive form -/

/-- Bilinearization of the genuine finite physical vacuum-sector matrix. -/
def centralPhysicalFiniteVacuumSectorMatrixBilinear
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat)
    (left right : Nat → Q') : Q' :=
  finiteJointBilinear
    (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
    left right
    (centralPhysicalFiniteKernel w hw cutoff half)

/-- A pointwise rational module with the zero form.  The actual physical form
below reuses this compact algebraic scaffold, so projecting its named
bilinear field never unfolds all pointwise module proofs. -/
private def pointwiseQCoefficientZeroGNSData : GNSData where
  V := Nat → Q'
  veq := fun left right => ∀ index, left index ≈ right index
  veq_refl := fun coefficient index => Q'.eqv_refl (coefficient index)
  veq_symm := fun h index => Q'.eqv_symm (h index)
  veq_trans := fun hleft hright index =>
    Q'.eqv_trans _ _ _ (hleft index) (hright index)
  zero := fun _ => 0
  add := fun left right index => left index + right index
  neg := fun coefficient index => -coefficient index
  smul := fun scalar coefficient index => scalar * coefficient index
  add_congr := by
    intro left left' right right' hleft hright index
    exact QPoly.q_add_congr (hleft index) (hright index)
  neg_congr := by
    intro left right h index
    exact Q'.neg_eqv_congr _ _ (h index)
  smul_congr := by
    intro scalar left right h index
    exact Q'.mul_eqv_congr_left scalar _ _ (h index)
  add_assoc := fun left middle right index =>
    Q'.add_assoc_eqv (left index) (middle index) (right index)
  add_comm := fun left right index =>
    Q'.add_comm_eqv (left index) (right index)
  zero_add := fun coefficient index =>
    Q'.eqv_of_eq (Q'.zero_add' (coefficient index))
  neg_add := fun coefficient index =>
    Q'.neg_add_self_eqv (coefficient index)
  B := fun _ _ => 0
  B_congr_left := fun _ _ => Q'.eqv_refl 0
  B_add_left := fun _ _ _ => Q'.eqv_symm (QPoly.q_add_zero_eqv 0)
  B_smul_left := fun scalar _ _ => Q'.eqv_symm (Q'.mul_zero_eqv scalar)
  B_symm := fun _ _ => Q'.eqv_refl 0
  self_nonneg := fun _ => Q'.le_refl' 0

theorem centralPhysicalFiniteVacuumSectorMatrixBilinear_congr_left
    {w : Q'} (hw0 : (0 : Q') < w) (cutoff half : Nat)
    {left left' : Nat → Q'} (right : Nat → Q')
    (hleft : ∀ index, left index ≈ left' index) :
    centralPhysicalFiniteVacuumSectorMatrixBilinear
        w (Q'.le_of_lt hw0) cutoff half left right ≈
      centralPhysicalFiniteVacuumSectorMatrixBilinear
        w (Q'.le_of_lt hw0) cutoff half left' right := by
  unfold centralPhysicalFiniteVacuumSectorMatrixBilinear
  exact finiteJointBilinear_coefficient_eqv_on
    (centralPhysicalFiniteVacuumSectorIndices
      w (Q'.le_of_lt hw0) cutoff half)
    left left' right right
    (centralPhysicalFiniteKernel
      w (Q'.le_of_lt hw0) cutoff half)
    (fun index _ => hleft index)
    (fun index _ => Q'.eqv_refl (right index))

theorem centralPhysicalFiniteVacuumSectorMatrixBilinear_add_left
    {w : Q'} (hw0 : (0 : Q') < w) (cutoff half : Nat)
    (left right test : Nat → Q') :
    centralPhysicalFiniteVacuumSectorMatrixBilinear
        w (Q'.le_of_lt hw0) cutoff half
        (fun index => left index + right index) test ≈
      centralPhysicalFiniteVacuumSectorMatrixBilinear
          w (Q'.le_of_lt hw0) cutoff half left test +
        centralPhysicalFiniteVacuumSectorMatrixBilinear
          w (Q'.le_of_lt hw0) cutoff half right test := by
  unfold centralPhysicalFiniteVacuumSectorMatrixBilinear
  exact finiteJointBilinear_add_left
    (centralPhysicalFiniteVacuumSectorIndices
      w (Q'.le_of_lt hw0) cutoff half)
    left right test
    (centralPhysicalFiniteKernel
      w (Q'.le_of_lt hw0) cutoff half)

theorem centralPhysicalFiniteVacuumSectorMatrixBilinear_scale_left
    {w : Q'} (hw0 : (0 : Q') < w) (cutoff half : Nat)
    (scalar : Q') (left right : Nat → Q') :
    centralPhysicalFiniteVacuumSectorMatrixBilinear
        w (Q'.le_of_lt hw0) cutoff half
        (fun index => scalar * left index) right ≈
      scalar * centralPhysicalFiniteVacuumSectorMatrixBilinear
        w (Q'.le_of_lt hw0) cutoff half left right := by
  unfold centralPhysicalFiniteVacuumSectorMatrixBilinear
  exact finiteJointBilinear_scale_left
    (centralPhysicalFiniteVacuumSectorIndices
      w (Q'.le_of_lt hw0) cutoff half)
    scalar left right
    (centralPhysicalFiniteKernel
      w (Q'.le_of_lt hw0) cutoff half)

theorem centralPhysicalFiniteVacuumSectorMatrixBilinear_add_right
    {w : Q'} (hw0 : (0 : Q') < w) (cutoff half : Nat)
    (left right first : Nat → Q') :
    centralPhysicalFiniteVacuumSectorMatrixBilinear
        w (Q'.le_of_lt hw0) cutoff half left
        (fun index => right index + first index) ≈
      centralPhysicalFiniteVacuumSectorMatrixBilinear
          w (Q'.le_of_lt hw0) cutoff half left right +
        centralPhysicalFiniteVacuumSectorMatrixBilinear
          w (Q'.le_of_lt hw0) cutoff half left first := by
  unfold centralPhysicalFiniteVacuumSectorMatrixBilinear
  exact finiteJointBilinear_add_right
    (centralPhysicalFiniteVacuumSectorIndices
      w (Q'.le_of_lt hw0) cutoff half)
    left right first
    (centralPhysicalFiniteKernel
      w (Q'.le_of_lt hw0) cutoff half)

theorem centralPhysicalFiniteVacuumSectorMatrixBilinear_scale_right
    {w : Q'} (hw0 : (0 : Q') < w) (cutoff half : Nat)
    (scalar : Q') (left right : Nat → Q') :
    centralPhysicalFiniteVacuumSectorMatrixBilinear
        w (Q'.le_of_lt hw0) cutoff half left
        (fun index => scalar * right index) ≈
      scalar * centralPhysicalFiniteVacuumSectorMatrixBilinear
        w (Q'.le_of_lt hw0) cutoff half left right := by
  unfold centralPhysicalFiniteVacuumSectorMatrixBilinear
  exact finiteJointBilinear_scale_right
    (centralPhysicalFiniteVacuumSectorIndices
      w (Q'.le_of_lt hw0) cutoff half)
    scalar left right
    (centralPhysicalFiniteKernel
      w (Q'.le_of_lt hw0) cutoff half)

theorem centralPhysicalFiniteVacuumSectorMatrixBilinear_symm
    {w : Q'} (hw0 : (0 : Q') < w) (cutoff half : Nat)
    (left right : Nat → Q') :
    centralPhysicalFiniteVacuumSectorMatrixBilinear
        w (Q'.le_of_lt hw0) cutoff half left right ≈
      centralPhysicalFiniteVacuumSectorMatrixBilinear
        w (Q'.le_of_lt hw0) cutoff half right left := by
  unfold centralPhysicalFiniteVacuumSectorMatrixBilinear
  apply finiteJointBilinear_swap_of_symmetric
  intro row column hrow hcolumn
  exact centralNormalizedPhysicalReflectedKernel_symm
    ((mem_centralPositiveHalfStates_iff.mp
      (centralPhysicalFiniteStateAt_mem_positive
        w (Q'.le_of_lt hw0) cutoff half
        (centralPhysicalFiniteVacuumSectorIndex_lt
          w (Q'.le_of_lt hw0) cutoff half hrow))).1)
    ((mem_centralPositiveHalfStates_iff.mp
      (centralPhysicalFiniteStateAt_mem_positive
        w (Q'.le_of_lt hw0) cutoff half
        (centralPhysicalFiniteVacuumSectorIndex_lt
          w (Q'.le_of_lt hw0) cutoff half hcolumn))).1)

/-- The bilinear form on equal arguments is the previously defined physical
matrix quadratic. -/
theorem centralPhysicalFiniteVacuumSectorMatrixBilinear_self
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat)
    (coefficient : Nat → Q') :
    centralPhysicalFiniteVacuumSectorMatrixBilinear
        w hw cutoff half coefficient coefficient =
      centralPhysicalFiniteVacuumSectorMatrixQuadratic
        w hw cutoff half coefficient := by
  rfl

theorem centralPhysicalFiniteVacuumSectorMatrixBilinear_self_nonnegative
    {w : Q'} (hw0 : (0 : Q') < w) (cutoff half : Nat)
    (coefficient : Nat → Q') :
    (0 : Q') ≤ centralPhysicalFiniteVacuumSectorMatrixBilinear
      w (Q'.le_of_lt hw0) cutoff half coefficient coefficient := by
  exact centralPhysicalFiniteVacuumSectorMatrixQuadratic_nonnegative
    w (Q'.le_of_lt hw0) cutoff half coefficient

/-- Diagonalized positivity of the physical bilinear form, proved directly
from its boundary-channel Gram factorization. -/
theorem centralPhysicalFiniteVacuumSectorMatrixBilinear_nonnegQuad
    {w : Q'} (hw0 : (0 : Q') < w) (cutoff half : Nat)
    (s r : Q') (left right : Nat → Q') :
    let B := centralPhysicalFiniteVacuumSectorMatrixBilinear
      w (Q'.le_of_lt hw0) cutoff half
    (0 : Q') ≤ s * s * B left left +
      2 * (s * r) * B left right + r * r * B right right := by
    dsimp only
    let combination : Nat → Q' := fun index =>
      s * left index + r * right index
    let B := centralPhysicalFiniteVacuumSectorMatrixBilinear
      w (Q'.le_of_lt hw0) cutoff half
    have hleftRight :
        B left combination ≈
          s * B left left + r * B left right := by
      have hadd := centralPhysicalFiniteVacuumSectorMatrixBilinear_add_right
        hw0 cutoff half left
        (fun index => s * left index)
        (fun index => r * right index)
      have hs := centralPhysicalFiniteVacuumSectorMatrixBilinear_scale_right
        hw0 cutoff half s left left
      have hr := centralPhysicalFiniteVacuumSectorMatrixBilinear_scale_right
        hw0 cutoff half r left right
      exact Q'.eqv_trans _ _ _ hadd (Q'.add_eqv_congr' hs hr)
    have hrightRight :
        B right combination ≈
          s * B left right + r * B right right := by
      have hadd := centralPhysicalFiniteVacuumSectorMatrixBilinear_add_right
        hw0 cutoff half right
        (fun index => s * left index)
        (fun index => r * right index)
      have hs0 := centralPhysicalFiniteVacuumSectorMatrixBilinear_scale_right
        hw0 cutoff half s right left
      have hsymm := centralPhysicalFiniteVacuumSectorMatrixBilinear_symm
        hw0 cutoff half right left
      have hs : B right (fun index => s * left index) ≈
          s * B left right :=
        Q'.eqv_trans _ _ _ hs0
          (Q'.mul_eqv_congr_left s _ _ hsymm)
      have hr := centralPhysicalFiniteVacuumSectorMatrixBilinear_scale_right
        hw0 cutoff half r right right
      exact Q'.eqv_trans _ _ _ hadd (Q'.add_eqv_congr' hs hr)
    have hscaledLeft :
        B (fun index => s * left index) combination ≈
          s * (s * B left left + r * B left right) :=
      Q'.eqv_trans _ _ _
        (centralPhysicalFiniteVacuumSectorMatrixBilinear_scale_left
          hw0 cutoff half s left combination)
        (Q'.mul_eqv_congr_left s _ _ hleftRight)
    have hscaledRight :
        B (fun index => r * right index) combination ≈
          r * (s * B left right + r * B right right) :=
      Q'.eqv_trans _ _ _
        (centralPhysicalFiniteVacuumSectorMatrixBilinear_scale_left
          hw0 cutoff half r right combination)
        (Q'.mul_eqv_congr_left r _ _ hrightRight)
    have hexpand :
        B combination combination ≈
          s * (s * B left left + r * B left right) +
            r * (s * B left right + r * B right right) :=
      Q'.eqv_trans _ _ _
        (centralPhysicalFiniteVacuumSectorMatrixBilinear_add_left
          hw0 cutoff half
          (fun index => s * left index)
          (fun index => r * right index) combination)
        (Q'.add_eqv_congr' hscaledLeft hscaledRight)
    have hring :
        s * (s * B left left + r * B left right) +
            r * (s * B left right + r * B right right) ≈
          s * s * B left left +
            2 * (s * r) * B left right +
              r * r * B right right := by
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr'
          (Q'.mul_add_eqv s (s * B left left) (r * B left right))
          (Q'.mul_add_eqv r (s * B left right) (r * B right right))) ?_
      exact GNSData.quad_regroup
        s r (B left left) (B left right) (B right right)
    have hself := centralPhysicalFiniteVacuumSectorMatrixBilinear_self
      w (Q'.le_of_lt hw0) cutoff half combination
    have hpoly :
        s * s * B left left +
            2 * (s * r) * B left right +
              r * r * B right right ≈
          centralPhysicalFiniteVacuumSectorMatrixQuadratic
            w (Q'.le_of_lt hw0) cutoff half combination :=
      Q'.eqv_trans _ _ _ (Q'.eqv_symm hring)
        (Q'.eqv_trans _ _ _ (Q'.eqv_symm hexpand)
          (Q'.eqv_of_eq hself))
    exact Q'.le_trans' _ _ _
      (centralPhysicalFiniteVacuumSectorMatrixQuadratic_nonnegative
        w (Q'.le_of_lt hw0) cutoff half combination)
      (Q'.ge_of_eqv hpoly)

/-- The physical vacuum-sector matrix as a pre-inner form. -/
def centralPhysicalFiniteVacuumSectorMatrixPreInnerForm
    {w : Q'} (hw0 : (0 : Q') < w) (cutoff half : Nat) :
    PreInnerForm (Nat → Q') where
  B := centralPhysicalFiniteVacuumSectorMatrixBilinear
    w (Q'.le_of_lt hw0) cutoff half
  nonnegQuad :=
    centralPhysicalFiniteVacuumSectorMatrixBilinear_nonnegQuad
      hw0 cutoff half

/-- The genuine finite physical vacuum-sector matrix, as a constructive GNS
form on total coefficient functions.  Only indices in the actual canonical
sector list are read. -/
def centralPhysicalFiniteVacuumSectorMatrixGNSData
    {w : Q'} (hw0 : (0 : Q') < w) (cutoff half : Nat) : GNSData where
  V := Nat → Q'
  veq := fun left right => ∀ index, left index ≈ right index
  veq_refl := fun coefficient index => Q'.eqv_refl (coefficient index)
  veq_symm := fun h index => Q'.eqv_symm (h index)
  veq_trans := fun hleft hright index =>
    Q'.eqv_trans _ _ _ (hleft index) (hright index)
  zero := fun _ => 0
  add := fun left right index => left index + right index
  neg := fun coefficient index => -coefficient index
  smul := fun scalar coefficient index => scalar * coefficient index
  add_congr := pointwiseQCoefficientZeroGNSData.add_congr
  neg_congr := pointwiseQCoefficientZeroGNSData.neg_congr
  smul_congr := pointwiseQCoefficientZeroGNSData.smul_congr
  add_assoc := pointwiseQCoefficientZeroGNSData.add_assoc
  add_comm := pointwiseQCoefficientZeroGNSData.add_comm
  zero_add := pointwiseQCoefficientZeroGNSData.zero_add
  neg_add := pointwiseQCoefficientZeroGNSData.neg_add
  B := centralPhysicalFiniteVacuumSectorMatrixBilinear
    w (Q'.le_of_lt hw0) cutoff half
  B_congr_left := centralPhysicalFiniteVacuumSectorMatrixBilinear_congr_left
    hw0 cutoff half
  B_add_left := centralPhysicalFiniteVacuumSectorMatrixBilinear_add_left
    hw0 cutoff half
  B_smul_left := centralPhysicalFiniteVacuumSectorMatrixBilinear_scale_left
    hw0 cutoff half
  B_symm := centralPhysicalFiniteVacuumSectorMatrixBilinear_symm
    hw0 cutoff half
  self_nonneg := centralPhysicalFiniteVacuumSectorMatrixBilinear_self_nonnegative
    hw0 cutoff half

/-! ## 2. Literal embedded-head and new-tail coefficient functions -/

/-- Restrict a later coefficient to the explicitly embedded base sector. -/
def centralPhysicalFiniteVacuumSectorEmbeddedHeadCoefficient
    (w : Q') (hw : (0 : Q') ≤ w)
    (base later half : Nat) (coefficient : Nat → Q')
    (index : Nat) : Q' :=
  if centralPhysicalFiniteEmbeddedVacuumSectorB
      w hw base later half index
  then coefficient index
  else 0

/-- Restrict a later coefficient to the genuinely new complement. -/
def centralPhysicalFiniteVacuumSectorNewTailCoefficient
    (w : Q') (hw : (0 : Q') ≤ w)
    (base later half : Nat) (coefficient : Nat → Q')
    (index : Nat) : Q' :=
  if centralPhysicalFiniteEmbeddedVacuumSectorB
      w hw base later half index
  then 0
  else coefficient index

/-- The embedded head and new tail reassemble the original coefficient at
every index, independently of carrier membership. -/
theorem embeddedHead_add_newTail_eqv
    (w : Q') (hw : (0 : Q') ≤ w)
    (base later half : Nat) (coefficient : Nat → Q')
    (index : Nat) :
    centralPhysicalFiniteVacuumSectorEmbeddedHeadCoefficient
          w hw base later half coefficient index +
        centralPhysicalFiniteVacuumSectorNewTailCoefficient
          w hw base later half coefficient index ≈
      coefficient index := by
  unfold centralPhysicalFiniteVacuumSectorEmbeddedHeadCoefficient
    centralPhysicalFiniteVacuumSectorNewTailCoefficient
  cases htest : centralPhysicalFiniteEmbeddedVacuumSectorB
      w hw base later half index
  · simp only [Bool.false_eq_true, if_false]
    exact Q'.eqv_of_eq (Q'.zero_add' (coefficient index))
  · simp only [if_true]
    exact Q'.eqv_of_eq (Q'.add_zero' (coefficient index))

/-! ## 3. Exact diagonal split -/

/-- The stationary diagonal norm is exactly the sum of the diagonal norms of
the disjoint embedded head and new tail. -/
theorem centralPhysicalFiniteVacuumSectorDiagonal_eqv_head_add_tail
    (w : Q') (hw : (0 : Q') ≤ w)
    (base later half : Nat) (coefficient : Nat → Q') :
    centralPhysicalFiniteVacuumSectorDiagonalQuadratic
        w hw later half coefficient ≈
      centralPhysicalFiniteVacuumSectorDiagonalQuadratic
          w hw later half
          (centralPhysicalFiniteVacuumSectorEmbeddedHeadCoefficient
            w hw base later half coefficient) +
        centralPhysicalFiniteVacuumSectorDiagonalQuadratic
          w hw later half
          (centralPhysicalFiniteVacuumSectorNewTailCoefficient
            w hw base later half coefficient) := by
  let states :=
    centralPhysicalFiniteVacuumSectorIndices w hw later half
  let weight := centralPhysicalFiniteWeight w hw later half
  let head := centralPhysicalFiniteVacuumSectorEmbeddedHeadCoefficient
    w hw base later half coefficient
  let tail := centralPhysicalFiniteVacuumSectorNewTailCoefficient
    w hw base later half coefficient
  let headTerm := fun index => (head index * head index) * weight index
  let tailTerm := fun index => (tail index * tail index) * weight index
  refine Q'.eqv_trans _
    (listQSum (fun index => headTerm index + tailTerm index) states) _ ?_ ?_
  · unfold centralPhysicalFiniteVacuumSectorDiagonalQuadratic
    apply listQSum_congr_on
    intro index _hindex
    unfold headTerm tailTerm head tail weight
      centralPhysicalFiniteVacuumSectorEmbeddedHeadCoefficient
      centralPhysicalFiniteVacuumSectorNewTailCoefficient
    cases htest : centralPhysicalFiniteEmbeddedVacuumSectorB
        w hw base later half index
    · simp only [Bool.false_eq_true, if_false]
      ring_qeqv
    · simp only [if_true]
      ring_qeqv
  · refine Q'.eqv_trans _
      (listQSum headTerm states + listQSum tailTerm states) _
      (listQSum_add headTerm tailTerm states) ?_
    exact Q'.eqv_refl _

/-! ## 4. The physical head--tail contraction -/

/-- Exact three-term expansion of the physical quadratic after the literal
embedded-head/new-tail split. -/
theorem centralPhysicalFiniteVacuumSectorMatrixQuadratic_eqv_head_cross_tail
    {w : Q'} (hw0 : (0 : Q') < w)
    (base later half : Nat) (coefficient : Nat → Q') :
    let head := centralPhysicalFiniteVacuumSectorEmbeddedHeadCoefficient
      w (Q'.le_of_lt hw0) base later half coefficient
    let tail := centralPhysicalFiniteVacuumSectorNewTailCoefficient
      w (Q'.le_of_lt hw0) base later half coefficient
    let B := centralPhysicalFiniteVacuumSectorMatrixBilinear
      w (Q'.le_of_lt hw0) later half
    centralPhysicalFiniteVacuumSectorMatrixQuadratic
        w (Q'.le_of_lt hw0) later half coefficient ≈
      (B head head + 2 * B head tail) + B tail tail := by
  dsimp only
  let head := centralPhysicalFiniteVacuumSectorEmbeddedHeadCoefficient
    w (Q'.le_of_lt hw0) base later half coefficient
  let tail := centralPhysicalFiniteVacuumSectorNewTailCoefficient
    w (Q'.le_of_lt hw0) base later half coefficient
  let combination : Nat → Q' := fun index => head index + tail index
  let B := centralPhysicalFiniteVacuumSectorMatrixBilinear
    w (Q'.le_of_lt hw0) later half
  have hcoefficient : ∀ index, coefficient index ≈ combination index := by
    intro index
    exact Q'.eqv_symm (embeddedHead_add_newTail_eqv
      w (Q'.le_of_lt hw0) base later half coefficient index)
  have hrecode : B coefficient coefficient ≈
      B combination combination := by
    unfold B centralPhysicalFiniteVacuumSectorMatrixBilinear
    exact finiteJointBilinear_coefficient_eqv_on
      (centralPhysicalFiniteVacuumSectorIndices
        w (Q'.le_of_lt hw0) later half)
      coefficient combination coefficient combination
      (centralPhysicalFiniteKernel
        w (Q'.le_of_lt hw0) later half)
      (fun index _ => hcoefficient index)
      (fun index _ => hcoefficient index)
  have hadd : B combination combination ≈
      B head combination + B tail combination :=
    centralPhysicalFiniteVacuumSectorMatrixBilinear_add_left
      hw0 later half head tail combination
  have hheadAdd : B head combination ≈
      B head head + B head tail :=
    centralPhysicalFiniteVacuumSectorMatrixBilinear_add_right
      hw0 later half head head tail
  have htailAdd : B tail combination ≈
      B tail head + B tail tail :=
    centralPhysicalFiniteVacuumSectorMatrixBilinear_add_right
      hw0 later half tail head tail
  have hsymm : B tail head ≈ B head tail :=
    centralPhysicalFiniteVacuumSectorMatrixBilinear_symm
      hw0 later half tail head
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_of_eq
      (Eq.symm (centralPhysicalFiniteVacuumSectorMatrixBilinear_self
        w (Q'.le_of_lt hw0) later half coefficient))) ?_
  refine Q'.eqv_trans _ _ _ hrecode ?_
  refine Q'.eqv_trans _ _ _ hadd ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' hheadAdd htailAdd) ?_
  refine Q'.eqv_trans _
    ((B head head + B head tail) +
      (B head tail + B tail tail)) _ ?_ ?_
  · exact Q'.add_eqv_congr' (Q'.eqv_refl _)
      (Q'.add_eqv_congr' hsymm (Q'.eqv_refl _))
  · exact symmetric_cross_regroup
      (B head head) (B head tail) (B tail tail)

/-- Scaled positivity turns separate physical diagonal estimates into the
mixed-block estimate needed for head--tail gluing. -/
theorem centralPhysicalFiniteVacuumSectorMatrix_two_cross_le
    {w : Q'} (hw0 : (0 : Q') < w) (later half : Nat)
    (head tail : Nat → Q') (q tau X Y : Q')
    (hq : (0 : Q') < q) (htau : (0 : Q') < tau)
    (hhead :
      centralPhysicalFiniteVacuumSectorMatrixQuadratic
          w (Q'.le_of_lt hw0) later half head ≤ q * X)
    (htail :
      centralPhysicalFiniteVacuumSectorMatrixQuadratic
          w (Q'.le_of_lt hw0) later half tail ≤ tau * Y) :
    2 * centralPhysicalFiniteVacuumSectorMatrixBilinear
          w (Q'.le_of_lt hw0) later half head tail ≤
      tau * X + q * Y := by
  let B := centralPhysicalFiniteVacuumSectorMatrixBilinear
    w (Q'.le_of_lt hw0) later half
  have hhead' : B head head ≤ q * X := by
    unfold B
    rw [centralPhysicalFiniteVacuumSectorMatrixBilinear_self]
    exact hhead
  have htail' : B tail tail ≤ tau * Y := by
    unfold B
    rw [centralPhysicalFiniteVacuumSectorMatrixBilinear_self]
    exact htail
  exact two_cross_le_tail_head_budget_of_nonnegQuad
    B
    (centralPhysicalFiniteVacuumSectorMatrixBilinear_nonnegQuad
      hw0 later half)
    head tail q tau X Y hq htau hhead' htail'

/-- Positivity of the physical boundary Gram absorbs the complete mixed block
between any two coefficient vectors with separate diagonal budgets. -/
theorem centralPhysicalFiniteVacuumSectorMatrix_head_tail_bilinear_le
    {w : Q'} (hw0 : (0 : Q') < w) (later half : Nat)
    (head tail : Nat → Q') (q tau X Y : Q')
    (hq : (0 : Q') < q) (htau : (0 : Q') < tau)
    (hhead :
      centralPhysicalFiniteVacuumSectorMatrixQuadratic
          w (Q'.le_of_lt hw0) later half head ≤ q * X)
    (htail :
      centralPhysicalFiniteVacuumSectorMatrixQuadratic
          w (Q'.le_of_lt hw0) later half tail ≤ tau * Y) :
    let B := centralPhysicalFiniteVacuumSectorMatrixBilinear
      w (Q'.le_of_lt hw0) later half
    (B head head + 2 * B head tail) + B tail tail ≤
      (q + tau) * (X + Y) := by
  dsimp only
  let B := centralPhysicalFiniteVacuumSectorMatrixBilinear
    w (Q'.le_of_lt hw0) later half
  have hhead' : B head head ≤ q * X := by
    unfold B
    rw [centralPhysicalFiniteVacuumSectorMatrixBilinear_self]
    exact hhead
  have htail' : B tail tail ≤ tau * Y := by
    unfold B
    rw [centralPhysicalFiniteVacuumSectorMatrixBilinear_self]
    exact htail
  have hcross : 2 * B head tail ≤ tau * X + q * Y :=
    centralPhysicalFiniteVacuumSectorMatrix_two_cross_le
      hw0 later half head tail q tau X Y hq htau hhead htail
  have hthree :
      (B head head + 2 * B head tail) + B tail tail ≤
        (q * X + (tau * X + q * Y)) + tau * Y :=
    Q'.add_le_add (Q'.add_le_add hhead' hcross) htail'
  exact Q'.le_trans' _ _ _ hthree
    (Q'.le_of_eqv (by ring_qeqv))

/-- Separate strict form estimates on the embedded head and the new tail
control the entire actual finite physical vacuum-sector form.  Positivity of
the genuine BF4 boundary Gram absorbs both cross blocks at no extra analytic
hypothesis. -/
theorem centralPhysicalFiniteVacuumSectorMatrix_le_of_head_tail
    {w : Q'} (hw0 : (0 : Q') < w)
    (base later half : Nat) (coefficient : Nat → Q')
    (q tau : Q') (hq : (0 : Q') < q) (htau : (0 : Q') < tau)
    (hhead :
      centralPhysicalFiniteVacuumSectorMatrixQuadratic
          w (Q'.le_of_lt hw0) later half
          (centralPhysicalFiniteVacuumSectorEmbeddedHeadCoefficient
            w (Q'.le_of_lt hw0) base later half coefficient) ≤
        q * centralPhysicalFiniteVacuumSectorDiagonalQuadratic
          w (Q'.le_of_lt hw0) later half
          (centralPhysicalFiniteVacuumSectorEmbeddedHeadCoefficient
            w (Q'.le_of_lt hw0) base later half coefficient))
    (htail :
      centralPhysicalFiniteVacuumSectorMatrixQuadratic
          w (Q'.le_of_lt hw0) later half
          (centralPhysicalFiniteVacuumSectorNewTailCoefficient
            w (Q'.le_of_lt hw0) base later half coefficient) ≤
        tau * centralPhysicalFiniteVacuumSectorDiagonalQuadratic
          w (Q'.le_of_lt hw0) later half
          (centralPhysicalFiniteVacuumSectorNewTailCoefficient
            w (Q'.le_of_lt hw0) base later half coefficient)) :
    centralPhysicalFiniteVacuumSectorMatrixQuadratic
        w (Q'.le_of_lt hw0) later half coefficient ≤
      (q + tau) *
        centralPhysicalFiniteVacuumSectorDiagonalQuadratic
          w (Q'.le_of_lt hw0) later half coefficient := by
  let head := centralPhysicalFiniteVacuumSectorEmbeddedHeadCoefficient
    w (Q'.le_of_lt hw0) base later half coefficient
  let tail := centralPhysicalFiniteVacuumSectorNewTailCoefficient
    w (Q'.le_of_lt hw0) base later half coefficient
  let headDiagonal := centralPhysicalFiniteVacuumSectorDiagonalQuadratic
    w (Q'.le_of_lt hw0) later half head
  let tailDiagonal := centralPhysicalFiniteVacuumSectorDiagonalQuadratic
    w (Q'.le_of_lt hw0) later half tail
  have hmatrix :=
    centralPhysicalFiniteVacuumSectorMatrixQuadratic_eqv_head_cross_tail
      hw0 base later half coefficient
  have hform :=
    centralPhysicalFiniteVacuumSectorMatrix_head_tail_bilinear_le
      hw0 later half head tail q tau headDiagonal tailDiagonal
      hq htau hhead htail
  have hglued :
      centralPhysicalFiniteVacuumSectorMatrixQuadratic
          w (Q'.le_of_lt hw0) later half coefficient ≤
        (q + tau) * (headDiagonal + tailDiagonal) :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv hmatrix)
      hform
  have hdiagonal :=
    centralPhysicalFiniteVacuumSectorDiagonal_eqv_head_add_tail
      w (Q'.le_of_lt hw0) base later half coefficient
  exact Q'.le_trans' _ _ _
    hglued
    (Q'.le_of_eqv
      (Q'.mul_eqv_congr_left (q + tau) _ _
        (Q'.eqv_symm hdiagonal)))

end YMGap.Continuum.BF4PhysicalVacuumSectorHeadTailGramGap

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorHeadTailGramGap.centralPhysicalFiniteVacuumSectorMatrixGNSData
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorHeadTailGramGap.embeddedHead_add_newTail_eqv
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorHeadTailGramGap.centralPhysicalFiniteVacuumSectorDiagonal_eqv_head_add_tail
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorHeadTailGramGap.centralPhysicalFiniteVacuumSectorMatrix_le_of_head_tail
