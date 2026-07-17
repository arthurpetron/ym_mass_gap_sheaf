/-
# Explicit Gram carrier for the adjacent-even fixed-interface link

The arbitrary-cutoff anchor positivity theorem for the resummed fixed-face
channel kernel is a quadratic statement.  Interface gluing needs stronger
data: an explicit finite Gram carrier whose entries are the literal
production link kernel.  This file polarizes the diagonal-dominance SOS at
the level of exact rational finite sums and packages its residual-channel and
ordered-edge features as a `SchurHadamardTransfer.GramRep`.

Every weight is derived in substrate.  The diagonal feature at channel `i`
has weight `1 - rowMass i`; the ordered-edge feature `(i,j)` has weight
`half * E i j`, where `E` is the excited-face channel kernel.  The uniform
anchor row bound makes the former nonnegative and character-coefficient
positivity makes the latter nonnegative.
-/

import YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenFixedFaceResummedKernel
import YMGap.Continuum.SchurHadamardTransfer

namespace YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenInterfaceLinkGram

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Constructive.RationalTail
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.CubeRatioBounds
open YMGap.Continuum.FusedFreeSplit
open YMGap.Continuum.SchurHadamardTransfer
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4FusionPathZeroInsertion
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenFixedFaceResummedKernel
open YMGap.Continuum.Z4StrongCouplingParametricAnchor
open YMGap.Continuum.Z4ValenceFusionCutoffIndependence

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Polarized finite diagonal-dominance algebra -/

def gramDoubleSum (term : Nat → Nat → Q') (count : Nat) : Q' :=
  finSum (fun first => finSum (term first) count) count

private theorem gramDoubleSum_congr
    (left right : Nat → Nat → Q')
    (h : ∀ first second, left first second ≈ right first second)
    (count : Nat) :
    gramDoubleSum left count ≈ gramDoubleSum right count := by
  unfold gramDoubleSum
  apply finSum_eqv_congr
  intro first
  apply finSum_eqv_congr
  intro second
  exact h first second

private theorem gramDoubleSum_add
    (left right : Nat → Nat → Q') (count : Nat) :
    gramDoubleSum (fun first second =>
      left first second + right first second) count ≈
      gramDoubleSum left count + gramDoubleSum right count := by
  unfold gramDoubleSum
  refine Q'.eqv_trans _ _ _
    (finSum_eqv_congr _ _ (fun first =>
      finSum_add (left first) (right first) count) count) ?_
  exact finSum_add
    (fun first => finSum (left first) count)
    (fun first => finSum (right first) count) count

def gramDiagonalPair
    (left right : Nat → Q') (count : Nat) : Q' :=
  finSum (fun row => left row * right row) count

def gramRowWeightedPair (matrix : Nat → Nat → Q')
    (left right : Nat → Q') (count : Nat) : Q' :=
  finSum (fun row =>
    finiteRowSum matrix count row * (left row * right row)) count

def gramMatrixBilinear (matrix : Nat → Nat → Q')
    (left right : Nat → Q') (count : Nat) : Q' :=
  gramDoubleSum (fun row column =>
    matrix row column * (left row * right column)) count

def gramDominantResidualPair (matrix : Nat → Nat → Q')
    (left right : Nat → Q') (count : Nat) : Q' :=
  finSum (fun row =>
    ((1 : Q') + -finiteRowSum matrix count row) *
      (left row * right row)) count

def gramSymmetricEdgePair (matrix : Nat → Nat → Q')
    (left right : Nat → Q') (count : Nat) : Q' :=
  YMGap.Constructive.HalfPow.half *
    gramDoubleSum (fun row column =>
      matrix row column *
        ((left row + left column) *
          (right row + right column))) count

def gramDominantFeaturePair (matrix : Nat → Nat → Q')
    (left right : Nat → Q') (count : Nat) : Q' :=
  gramDominantResidualPair matrix left right count +
    gramSymmetricEdgePair matrix left right count

def gramIdentityPlusBilinear (matrix : Nat → Nat → Q')
    (left right : Nat → Q') (count : Nat) : Q' :=
  gramDiagonalPair left right count +
    gramMatrixBilinear matrix left right count

private theorem bilinear_add_expand
    (leftRow leftColumn rightRow rightColumn : Q') :
    (leftRow + leftColumn) * (rightRow + rightColumn) ≈
      (leftRow * rightRow + leftRow * rightColumn) +
        (leftColumn * rightRow + leftColumn * rightColumn) := by
  refine Q'.eqv_trans _ _ _
    (Q'.add_mul_eqv leftRow leftColumn
      (rightRow + rightColumn)) ?_
  exact Q'.add_eqv_congr'
    (Q'.mul_add_eqv leftRow rightRow rightColumn)
    (Q'.mul_add_eqv leftColumn rightRow rightColumn)

private theorem weighted_bilinear_add_expand
    (weight leftRow leftColumn rightRow rightColumn : Q') :
    weight * ((leftRow + leftColumn) *
      (rightRow + rightColumn)) ≈
      (weight * (leftRow * rightRow) +
        weight * (leftRow * rightColumn)) +
      (weight * (leftColumn * rightRow) +
        weight * (leftColumn * rightColumn)) := by
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left weight _ _
      (bilinear_add_expand leftRow leftColumn
        rightRow rightColumn)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_add_eqv weight
      (leftRow * rightRow + leftRow * rightColumn)
      (leftColumn * rightRow + leftColumn * rightColumn)) ?_
  exact Q'.add_eqv_congr'
    (Q'.mul_add_eqv weight
      (leftRow * rightRow) (leftRow * rightColumn))
    (Q'.mul_add_eqv weight
      (leftColumn * rightRow) (leftColumn * rightColumn))

private theorem gramEdgeFirst_eqv_rowWeighted
    (matrix : Nat → Nat → Q')
    (left right : Nat → Q') (count : Nat) :
    gramDoubleSum (fun row column =>
        matrix row column * (left row * right row)) count ≈
      gramRowWeightedPair matrix left right count := by
  unfold gramDoubleSum gramRowWeightedPair finiteRowSum
  apply finSum_eqv_congr
  intro row
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (finSum_mul_const (matrix row)
      (left row * right row) count)) ?_
  exact Q'.mul_eqv_congr_right _ _ _
    (Q'.eqv_symm (Q'.eqv_of_eq
      (YMGap.Continuum.MovingCutoff.fsum_eq_finSum
        (matrix row) count)))

private theorem gramEdgeLast_eqv_rowWeighted
    (matrix : Nat → Nat → Q')
    (left right : Nat → Q') (count : Nat)
    (hsymmetric : ∀ row column,
      matrix row column ≈ matrix column row) :
    gramDoubleSum (fun row column =>
        matrix row column * (left column * right column)) count ≈
      gramRowWeightedPair matrix left right count := by
  refine Q'.eqv_trans _ _ _
    (finSum_swap (fun row column =>
      matrix row column * (left column * right column)) count count) ?_
  unfold gramRowWeightedPair finiteRowSum
  apply finSum_eqv_congr
  intro column
  refine Q'.eqv_trans _ _ _
    (finSum_eqv_congr _ _ (fun row =>
      Q'.mul_eqv_congr_right (matrix row column)
        (matrix column row) (left column * right column)
        (hsymmetric row column)) count) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (finSum_mul_const (matrix column)
      (left column * right column) count)) ?_
  exact Q'.mul_eqv_congr_right _ _ _
    (Q'.eqv_symm (Q'.eqv_of_eq
      (YMGap.Continuum.MovingCutoff.fsum_eq_finSum
        (matrix column) count)))

private theorem gramReverseCross_eqv_cross
    (matrix : Nat → Nat → Q')
    (left right : Nat → Q') (count : Nat)
    (hsymmetric : ∀ row column,
      matrix row column ≈ matrix column row) :
    gramDoubleSum (fun row column =>
        matrix row column * (left column * right row)) count ≈
      gramMatrixBilinear matrix left right count := by
  refine Q'.eqv_trans _ _ _
    (finSum_swap (fun row column =>
      matrix row column * (left column * right row)) count count) ?_
  unfold gramMatrixBilinear gramDoubleSum
  apply finSum_eqv_congr
  intro column
  apply finSum_eqv_congr
  intro row
  exact Q'.mul_eqv_congr_right _ _ _
    (hsymmetric row column)

private theorem half_duplicate_pair_collapse (row cross : Q') :
    YMGap.Constructive.HalfPow.half *
        ((row + cross) + (cross + row)) ≈
      row + cross := by
  have hinside : ((row + cross) + (cross + row)) ≈
      (row + row) + (cross + cross) := by
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left (row + cross) _ _
        (Q'.add_comm_eqv cross row)) ?_
    exact Q'.add_swap_inner row cross row cross
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left YMGap.Constructive.HalfPow.half _ _
      hinside) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_add_eqv YMGap.Constructive.HalfPow.half
      (row + row) (cross + cross)) ?_
  exact Q'.add_eqv_congr'
    (Q'.eqv_trans _ _ _
      (Q'.mul_add_eqv YMGap.Constructive.HalfPow.half row row)
      (YMGap.Constructive.ExpNeg.two_halves row))
    (Q'.eqv_trans _ _ _
      (Q'.mul_add_eqv YMGap.Constructive.HalfPow.half cross cross)
      (YMGap.Constructive.ExpNeg.two_halves cross))

theorem gramSymmetricEdgePair_eqv_row_add_cross
    (matrix : Nat → Nat → Q')
    (left right : Nat → Q') (count : Nat)
    (hsymmetric : ∀ row column,
      matrix row column ≈ matrix column row) :
    gramSymmetricEdgePair matrix left right count ≈
      gramRowWeightedPair matrix left right count +
        gramMatrixBilinear matrix left right count := by
  let edgeFirst : Nat → Nat → Q' := fun row column =>
    matrix row column * (left row * right row)
  let edgeCross : Nat → Nat → Q' := fun row column =>
    matrix row column * (left row * right column)
  let edgeReverse : Nat → Nat → Q' := fun row column =>
    matrix row column * (left column * right row)
  let edgeLast : Nat → Nat → Q' := fun row column =>
    matrix row column * (left column * right column)
  have hexpand :
      gramDoubleSum (fun row column =>
          matrix row column *
            ((left row + left column) *
              (right row + right column))) count ≈
        gramDoubleSum (fun row column =>
          (edgeFirst row column + edgeCross row column) +
            (edgeReverse row column + edgeLast row column)) count := by
    apply gramDoubleSum_congr
    intro row column
    exact weighted_bilinear_add_expand (matrix row column)
      (left row) (left column) (right row) (right column)
  have hsplit :
      gramDoubleSum (fun row column =>
          (edgeFirst row column + edgeCross row column) +
            (edgeReverse row column + edgeLast row column)) count ≈
        (gramDoubleSum edgeFirst count +
          gramDoubleSum edgeCross count) +
          (gramDoubleSum edgeReverse count +
            gramDoubleSum edgeLast count) := by
    refine Q'.eqv_trans _ _ _
      (gramDoubleSum_add
        (fun row column => edgeFirst row column + edgeCross row column)
        (fun row column => edgeReverse row column + edgeLast row column)
        count) ?_
    exact Q'.add_eqv_congr'
      (gramDoubleSum_add edgeFirst edgeCross count)
      (gramDoubleSum_add edgeReverse edgeLast count)
  have hcomponents :
      (gramDoubleSum edgeFirst count +
          gramDoubleSum edgeCross count) +
          (gramDoubleSum edgeReverse count +
            gramDoubleSum edgeLast count) ≈
        (gramRowWeightedPair matrix left right count +
          gramMatrixBilinear matrix left right count) +
          (gramMatrixBilinear matrix left right count +
            gramRowWeightedPair matrix left right count) :=
    Q'.add_eqv_congr'
      (Q'.add_eqv_congr'
        (gramEdgeFirst_eqv_rowWeighted matrix left right count)
        (Q'.eqv_refl _))
      (Q'.add_eqv_congr'
        (gramReverseCross_eqv_cross
          matrix left right count hsymmetric)
        (gramEdgeLast_eqv_rowWeighted
          matrix left right count hsymmetric))
  unfold gramSymmetricEdgePair
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left YMGap.Constructive.HalfPow.half _ _
      (Q'.eqv_trans _ _ _ hexpand
        (Q'.eqv_trans _ _ _ hsplit hcomponents))) ?_
  exact half_duplicate_pair_collapse
    (gramRowWeightedPair matrix left right count)
    (gramMatrixBilinear matrix left right count)

theorem gramDominantResidualPair_eqv_diag_sub_row
    (matrix : Nat → Nat → Q')
    (left right : Nat → Q') (count : Nat) :
    gramDominantResidualPair matrix left right count ≈
      gramDiagonalPair left right count +
        -gramRowWeightedPair matrix left right count := by
  have gramFinSum_neg : ∀ (value : Nat → Q') (n : Nat),
      finSum (fun index => -(value index)) n ≈
        -(finSum value n) := by
    intro value n
    induction n with
    | zero =>
        change (0 : Q') ≈ -(0 : Q')
        decide
    | succ m ih =>
        change finSum (fun index => -(value index)) m + -(value m) ≈
          -(finSum value m + value m)
        refine Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr_right _ _ _ ih) ?_
        exact Q'.eqv_symm (Q'.neg_add_eqv _ _)
  have hterm : ∀ row,
      (((1 : Q') + -finiteRowSum matrix count row) *
          (left row * right row)) ≈
        (left row * right row) +
          -(finiteRowSum matrix count row *
            (left row * right row)) := by
    intro row
    refine Q'.eqv_trans _ _ _
      (Q'.add_mul_eqv 1 (-finiteRowSum matrix count row)
        (left row * right row)) ?_
    exact Q'.add_eqv_congr'
      (Q'.one_mul_eqv (left row * right row))
      (Q'.neg_mul_eqv (finiteRowSum matrix count row)
        (left row * right row))
  unfold gramDominantResidualPair gramDiagonalPair
    gramRowWeightedPair
  refine Q'.eqv_trans _ _ _
    (finSum_eqv_congr _ _ hterm count) ?_
  refine Q'.eqv_trans _ _ _
    (finSum_add
      (fun row => left row * right row)
      (fun row => -(finiteRowSum matrix count row *
        (left row * right row))) count) ?_
  exact Q'.add_eqv_congr_left _ _ _
    (gramFinSum_neg
      (fun row => finiteRowSum matrix count row *
        (left row * right row)) count)

private theorem cancel_polarized_row_pair
    (diagonal row cross : Q') :
    (diagonal + -row) + (row + cross) ≈
      diagonal + cross := by
  refine Q'.eqv_trans _ _ _
    (Q'.add_assoc_eqv diagonal (-row) (row + cross)) ?_
  refine Q'.add_eqv_congr_left diagonal _ _ ?_
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.add_assoc_eqv (-row) row cross)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right ((-row) + row) 0 cross
      (Q'.neg_add_self_eqv row)) ?_
  exact q_zero_add_eqv cross

/-- Polarized exact form of the diagonal-dominance SOS.  This is stronger
than quadratic nonnegativity: it gives the entrywise Gram identity used by
the interface tensor product. -/
theorem gramDominantFeaturePair_eqv_identityPlusBilinear
    (matrix : Nat → Nat → Q')
    (left right : Nat → Q') (count : Nat)
    (hsymmetric : ∀ row column,
      matrix row column ≈ matrix column row) :
    gramDominantFeaturePair matrix left right count ≈
      gramIdentityPlusBilinear matrix left right count := by
  unfold gramDominantFeaturePair gramIdentityPlusBilinear
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr'
      (gramDominantResidualPair_eqv_diag_sub_row
        matrix left right count)
      (gramSymmetricEdgePair_eqv_row_add_cross
        matrix left right count hsymmetric)) ?_
  exact cancel_polarized_row_pair
    (gramDiagonalPair left right count)
    (gramRowWeightedPair matrix left right count)
    (gramMatrixBilinear matrix left right count)

/-! ## 2. Exact production-channel bilinear identification -/

private theorem localListQSum_append {A : Type}
    (value : A → Q') : ∀ left right : List A,
    listQSum value (left ++ right) ≈
      listQSum value left + listQSum value right
  | [], right => Q'.eqv_symm (q_zero_add_eqv _)
  | head :: tail, right => by
      simp only [List.cons_append, listQSum]
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left (value head) _ _
          (localListQSum_append value tail right)) ?_
      exact Q'.eqv_symm (Q'.add_assoc_eqv
        (value head) (listQSum value tail) (listQSum value right))

private theorem localListQSum_range_eqv_finSum
    (value : Nat → Q') : ∀ count,
    listQSum value (List.range count) ≈ finSum value count
  | 0 => Q'.eqv_refl 0
  | count + 1 => by
      rw [List.range_succ]
      refine Q'.eqv_trans _ _ _
        (localListQSum_append value (List.range count) [count]) ?_
      simp only [listQSum]
      change listQSum value (List.range count) + (value count + 0) ≈
        finSum value count + value count
      exact Q'.add_eqv_congr'
        (localListQSum_range_eqv_finSum value count)
        (q_add_zero_eqv (value count))

private theorem triple_weight_rearrange
    (left weight right : Q') :
    (left * weight) * right ≈ weight * (left * right) := by
  refine Q'.eqv_trans _ _ _
    (Q'.mul_assoc_eqv left weight right) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left left _ _
      (Q'.mul_comm_eqv weight right)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.mul_assoc_eqv left right weight)) ?_
  exact Q'.mul_comm_eqv (left * right) weight

private theorem triple_mul_add
    (left first second right : Q') :
    (left * (first + second)) * right ≈
      (left * first) * right + (left * second) * right := by
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ right
      (Q'.mul_add_eqv left first second)) ?_
  exact Q'.add_mul_eqv (left * first) (left * second) right

private theorem delta_finSum
    (value : Nat → Q') (source count : Nat)
    (hsource : source < count) :
    finSum (fun target => delta source target * value target) count ≈
      value source := by
  have h := delta_fsum value source count hsource
  rw [YMGap.Continuum.MovingCutoff.fsum_eq_finSum] at h
  exact h

private theorem channelBilinear_eqv_gramDoubleSum
    (cutoff : Nat) (left right : List Nat) :
    adjacentEvenResummedFaceChannelBilinear
        cutoff anchorCoupling left right ≈
      gramDoubleSum (fun source target =>
        (adjacentEvenResummedFaceChannelAmplitude cutoff left source *
          adjacentEvenResummedFaceChannelKernel
            cutoff anchorCoupling source target) *
          adjacentEvenResummedFaceChannelAmplitude cutoff right target)
        (cutoff + 1) := by
  unfold adjacentEvenResummedFaceChannelBilinear gramDoubleSum
  refine Q'.eqv_trans _ _ _
    (localListQSum_range_eqv_finSum
      (fun source =>
        listQSum (fun target =>
          (adjacentEvenResummedFaceChannelAmplitude cutoff left source *
            adjacentEvenResummedFaceChannelKernel
              cutoff anchorCoupling source target) *
            adjacentEvenResummedFaceChannelAmplitude cutoff right target)
          (List.range (cutoff + 1)))
      (cutoff + 1)) ?_
  apply finSum_eqv_congr
  intro source
  exact localListQSum_range_eqv_finSum
    (fun target =>
      (adjacentEvenResummedFaceChannelAmplitude cutoff left source *
        adjacentEvenResummedFaceChannelKernel
          cutoff anchorCoupling source target) *
        adjacentEvenResummedFaceChannelAmplitude cutoff right target)
    (cutoff + 1)

private theorem deltaChannelPair_eqv_diagonalPair
    (left right : Nat → Q') (count : Nat) :
    gramDoubleSum (fun source target =>
        (left source * delta source target) * right target) count ≈
      gramDiagonalPair left right count := by
  unfold gramDoubleSum gramDiagonalPair
  apply finSum_congr_lt
  intro source hsource
  refine Q'.eqv_trans _ _ _
    (finSum_eqv_congr _ _ (fun target =>
      triple_weight_rearrange
        (left source) (delta source target) (right target)) count) ?_
  exact delta_finSum
    (fun target => left source * right target)
    source count hsource

/-- The exact anchor channel bilinear equals the identity-plus-excited
polarized form on all finite cutoffs. -/
theorem anchorResummedFaceChannelBilinear_eqv_identityPlus
    (cutoff : Nat) (left right : List Nat) :
    adjacentEvenResummedFaceChannelBilinear
        cutoff anchorCoupling left right ≈
      gramIdentityPlusBilinear
        (anchorExcitedFaceChannelKernel cutoff)
        (adjacentEvenResummedFaceChannelAmplitude cutoff left)
        (adjacentEvenResummedFaceChannelAmplitude cutoff right)
        (cutoff + 1) := by
  let leftAmplitude : Nat → Q' :=
    adjacentEvenResummedFaceChannelAmplitude cutoff left
  let rightAmplitude : Nat → Q' :=
    adjacentEvenResummedFaceChannelAmplitude cutoff right
  have hfinite := channelBilinear_eqv_gramDoubleSum cutoff left right
  have hkernel :
      gramDoubleSum (fun source target =>
        (leftAmplitude source *
          adjacentEvenResummedFaceChannelKernel
            cutoff anchorCoupling source target) *
          rightAmplitude target) (cutoff + 1) ≈
      gramDoubleSum (fun source target =>
        (leftAmplitude source *
          (delta source target +
            anchorExcitedFaceChannelKernel cutoff source target)) *
          rightAmplitude target) (cutoff + 1) := by
    apply gramDoubleSum_congr
    intro source target
    exact Q'.mul_eqv_congr_right _ _ (rightAmplitude target)
      (Q'.mul_eqv_congr_left (leftAmplitude source) _ _
        (adjacentEvenResummedFaceChannelKernel_anchor_eqv_identity_add_excited
          cutoff source target))
  have hdistribute :
      gramDoubleSum (fun source target =>
        (leftAmplitude source *
          (delta source target +
            anchorExcitedFaceChannelKernel cutoff source target)) *
          rightAmplitude target) (cutoff + 1) ≈
      gramDoubleSum (fun source target =>
        (leftAmplitude source * delta source target) *
          rightAmplitude target) (cutoff + 1) +
      gramDoubleSum (fun source target =>
        (leftAmplitude source *
          anchorExcitedFaceChannelKernel cutoff source target) *
          rightAmplitude target) (cutoff + 1) := by
    refine Q'.eqv_trans _ _ _
      (gramDoubleSum_congr _ _ (fun source target =>
        triple_mul_add (leftAmplitude source)
          (delta source target)
          (anchorExcitedFaceChannelKernel cutoff source target)
          (rightAmplitude target)) (cutoff + 1)) ?_
    exact gramDoubleSum_add _ _ (cutoff + 1)
  have hexcited :
      gramDoubleSum (fun source target =>
        (leftAmplitude source *
          anchorExcitedFaceChannelKernel cutoff source target) *
          rightAmplitude target) (cutoff + 1) ≈
      gramMatrixBilinear
        (anchorExcitedFaceChannelKernel cutoff)
        leftAmplitude rightAmplitude (cutoff + 1) := by
    unfold gramMatrixBilinear
    apply gramDoubleSum_congr
    intro source target
    exact triple_weight_rearrange
      (leftAmplitude source)
      (anchorExcitedFaceChannelKernel cutoff source target)
      (rightAmplitude target)
  unfold gramIdentityPlusBilinear
  exact Q'.eqv_trans _ _ _ hfinite
    (Q'.eqv_trans _ _ _ hkernel
      (Q'.eqv_trans _ _ _ hdistribute
        (Q'.add_eqv_congr'
          (deltaChannelPair_eqv_diagonalPair
            leftAmplitude rightAmplitude (cutoff + 1))
          hexcited)))

/-- The literal production link kernel is exactly the explicit polarized
diagonal-dominance feature pairing. -/
theorem adjacentEvenAnchorResummedFixedFaceLinkKernel_eqv_features
    {cutoff : Nat} {left right : List Nat}
    (hleft : SpinsBounded cutoff left)
    (hright : SpinsBounded cutoff right) :
    adjacentEvenResummedFixedFaceLinkKernel
        cutoff anchorCoupling left right ≈
      gramDominantFeaturePair
        (anchorExcitedFaceChannelKernel cutoff)
        (adjacentEvenResummedFaceChannelAmplitude cutoff left)
        (adjacentEvenResummedFaceChannelAmplitude cutoff right)
        (cutoff + 1) := by
  refine Q'.eqv_trans _ _ _
    (adjacentEvenResummedFixedFaceLinkKernel_eqv_channelBilinear
      hleft hright) ?_
  refine Q'.eqv_trans _ _ _
    (anchorResummedFaceChannelBilinear_eqv_identityPlus
      cutoff left right) ?_
  exact Q'.eqv_symm
    (gramDominantFeaturePair_eqv_identityPlusBilinear
      (anchorExcitedFaceChannelKernel cutoff)
      (adjacentEvenResummedFaceChannelAmplitude cutoff left)
      (adjacentEvenResummedFaceChannelAmplitude cutoff right)
      (cutoff + 1)
      (anchorExcitedFaceChannelKernel_symmetric cutoff))

/-! ## 3. Explicit local Gram carrier -/

def adjacentEvenAnchorResidualFeatureMatrix
    (cutoff : Nat) (state : Nat → List Nat)
    (left right : Nat) : Q' :=
  gramDominantResidualPair
    (anchorExcitedFaceChannelKernel cutoff)
    (adjacentEvenResummedFaceChannelAmplitude cutoff (state left))
    (adjacentEvenResummedFaceChannelAmplitude cutoff (state right))
    (cutoff + 1)

def adjacentEvenAnchorEdgeFeatureMatrix
    (cutoff : Nat) (state : Nat → List Nat)
    (left right : Nat) : Q' :=
  gramSymmetricEdgePair
    (anchorExcitedFaceChannelKernel cutoff)
    (adjacentEvenResummedFaceChannelAmplitude cutoff (state left))
    (adjacentEvenResummedFaceChannelAmplitude cutoff (state right))
    (cutoff + 1)

def adjacentEvenAnchorDominantFeatureMatrix
    (cutoff : Nat) (state : Nat → List Nat)
    (left right : Nat) : Q' :=
  adjacentEvenAnchorResidualFeatureMatrix cutoff state left right +
    adjacentEvenAnchorEdgeFeatureMatrix cutoff state left right

/-- Residual-channel features.  Their exact derived weights are
`1 - rowMass`; the uniform anchor estimate makes every weight nonnegative. -/
def adjacentEvenAnchorResidualFeatureGramRep
    (cutoff : Nat) (state : Nat → List Nat) :
    GramRep (adjacentEvenAnchorResidualFeatureMatrix cutoff state) where
  r := cutoff + 1
  d := fun channel =>
    (1 : Q') + -finiteRowSum
      (anchorExcitedFaceChannelKernel cutoff) (cutoff + 1) channel
  hd := fun channel =>
    Q'.sub_nonneg_of_le
      (anchorExcitedFaceChannelRowSum_le_one cutoff channel)
  v := fun channel configuration =>
    adjacentEvenResummedFaceChannelAmplitude
      cutoff (state configuration) channel
  hM := by
    intro left right
    exact Q'.eqv_refl _

private theorem half_nested_finSum_eqv_flattened
    (term : Nat → Nat → Q') (count : Nat) :
    YMGap.Constructive.HalfPow.half *
        finSum (fun row => finSum (term row) count) count ≈
      finSum (fun packed =>
        YMGap.Constructive.HalfPow.half *
          term (packed / count) (packed % count))
        (count * count) := by
  have hpushOuter :
      YMGap.Constructive.HalfPow.half *
          finSum (fun row => finSum (term row) count) count ≈
        finSum (fun row =>
          YMGap.Constructive.HalfPow.half *
            finSum (term row) count) count :=
    const_mul_finSum
      (fun row => finSum (term row) count)
      YMGap.Constructive.HalfPow.half count
  have hpushInner :
      finSum (fun row =>
          YMGap.Constructive.HalfPow.half *
            finSum (term row) count) count ≈
        finSum (fun row => finSum (fun column =>
          YMGap.Constructive.HalfPow.half *
            term row column) count) count := by
    apply finSum_eqv_congr
    intro row
    exact const_mul_finSum (term row)
      YMGap.Constructive.HalfPow.half count
  exact Q'.eqv_trans _ _ _ hpushOuter
    (Q'.eqv_trans _ _ _ hpushInner
      (Q'.eqv_symm
        (finSum_flatten
          (fun row column =>
            YMGap.Constructive.HalfPow.half * term row column)
          count count)))

/-- Ordered symmetric-edge features.  Packing `(source,target)` by quotient
and remainder gives a finite rank `(cutoff+1)^2` Gram carrier. -/
def adjacentEvenAnchorEdgeFeatureGramRep
    (cutoff : Nat) (state : Nat → List Nat) :
    GramRep (adjacentEvenAnchorEdgeFeatureMatrix cutoff state) where
  r := (cutoff + 1) * (cutoff + 1)
  d := fun packed =>
    YMGap.Constructive.HalfPow.half *
      anchorExcitedFaceChannelKernel cutoff
        (packed / (cutoff + 1)) (packed % (cutoff + 1))
  hd := fun packed =>
    Q'.mul_nonneg _ _ (by decide)
      (anchorExcitedFaceChannelKernel_nonnegative cutoff
        (packed / (cutoff + 1)) (packed % (cutoff + 1)))
  v := fun packed configuration =>
    adjacentEvenResummedFaceChannelAmplitude cutoff
        (state configuration) (packed / (cutoff + 1)) +
      adjacentEvenResummedFaceChannelAmplitude cutoff
        (state configuration) (packed % (cutoff + 1))
  hM := by
    intro left right
    unfold adjacentEvenAnchorEdgeFeatureMatrix
      gramSymmetricEdgePair gramDoubleSum
    let term : Nat → Nat → Q' := fun source target =>
      anchorExcitedFaceChannelKernel cutoff source target *
        ((adjacentEvenResummedFaceChannelAmplitude cutoff
            (state left) source +
          adjacentEvenResummedFaceChannelAmplitude cutoff
            (state left) target) *
        (adjacentEvenResummedFaceChannelAmplitude cutoff
            (state right) source +
          adjacentEvenResummedFaceChannelAmplitude cutoff
            (state right) target))
    have hflatten := half_nested_finSum_eqv_flattened
      term (cutoff + 1)
    refine Q'.eqv_trans _ _ _ hflatten ?_
    apply finSum_eqv_congr
    intro packed
    exact Q'.eqv_symm
      (Q'.mul_assoc_eqv
        YMGap.Constructive.HalfPow.half
        (anchorExcitedFaceChannelKernel cutoff
          (packed / (cutoff + 1)) (packed % (cutoff + 1)))
        ((adjacentEvenResummedFaceChannelAmplitude cutoff
              (state left) (packed / (cutoff + 1)) +
            adjacentEvenResummedFaceChannelAmplitude cutoff
              (state left) (packed % (cutoff + 1))) *
          (adjacentEvenResummedFaceChannelAmplitude cutoff
              (state right) (packed / (cutoff + 1)) +
            adjacentEvenResummedFaceChannelAmplitude cutoff
              (state right) (packed % (cutoff + 1)))))

/-- The complete residual-plus-edge feature carrier. -/
def adjacentEvenAnchorDominantFeatureGramRep
    (cutoff : Nat) (state : Nat → List Nat) :
    GramRep (adjacentEvenAnchorDominantFeatureMatrix cutoff state) :=
  gramRep_add
    (adjacentEvenAnchorResidualFeatureGramRep cutoff state)
    (adjacentEvenAnchorEdgeFeatureGramRep cutoff state)

def adjacentEvenAnchorResummedPhysicalLinkMatrix
    (cutoff : Nat) (state : Nat → List Nat)
    (left right : Nat) : Q' :=
  adjacentEvenResummedFixedFaceLinkKernel cutoff anchorCoupling
    (state left) (state right)

/-- Explicit Gram carrier for the literal production fixed-interface link
kernel, for any enumerated family of cutoff-bounded half-state words. -/
def adjacentEvenAnchorResummedPhysicalLinkGramRep
    (cutoff : Nat) (state : Nat → List Nat)
    (hstate : ∀ configuration, SpinsBounded cutoff (state configuration)) :
    GramRep (adjacentEvenAnchorResummedPhysicalLinkMatrix cutoff state) := by
  let rep := adjacentEvenAnchorDominantFeatureGramRep cutoff state
  exact {
    r := rep.r
    d := rep.d
    hd := rep.hd
    v := rep.v
    hM := fun left right =>
      Q'.eqv_trans _ _ _
        (adjacentEvenAnchorResummedFixedFaceLinkKernel_eqv_features
          (hstate left) (hstate right))
        (rep.hM left right)
  }

/-! ## 4. Finite interface-network tensor gluing -/

/-- Entrywise product of the first `linkCount` literal interface-link
kernels.  A global configuration may induce a different incident-spin word
at every link; no product-state assumption is made. -/
def adjacentEvenAnchorInterfaceNetworkKernel
    (cutoff : Nat) (localState : Nat → Nat → List Nat) :
    Nat → Nat → Nat → Q'
  | 0, _, _ => 1
  | linkCount + 1, left, right =>
      adjacentEvenAnchorInterfaceNetworkKernel
          cutoff localState linkCount left right *
        adjacentEvenAnchorResummedPhysicalLinkMatrix cutoff
          (localState linkCount) left right

/-- Constructive finite-interface gluing: repeated Schur products turn the
local production Gram carriers into an explicit Gram carrier for their full
network product. -/
def adjacentEvenAnchorInterfaceNetworkGramRep
    (cutoff : Nat) (localState : Nat → Nat → List Nat)
    (hstate : ∀ link configuration,
      SpinsBounded cutoff (localState link configuration)) :
    ∀ linkCount,
      GramRep (adjacentEvenAnchorInterfaceNetworkKernel
        cutoff localState linkCount)
  | 0 => onesGramRep
  | linkCount + 1 =>
      schur_product
        (adjacentEvenAnchorInterfaceNetworkGramRep
          cutoff localState hstate linkCount)
        (adjacentEvenAnchorResummedPhysicalLinkGramRep
          cutoff (localState linkCount) (hstate linkCount))

/-- Every finite interface-network quadratic form is nonnegative, uniformly
in the number of links and without a volume-dependent estimate. -/
theorem adjacentEvenAnchorInterfaceNetworkQuadratic_nonnegative
    (cutoff : Nat) (localState : Nat → Nat → List Nat)
    (hstate : ∀ link configuration,
      SpinsBounded cutoff (localState link configuration))
    (linkCount : Nat) (coefficient : Nat → Q')
    (configurationCount : Nat) :
    (0 : Q') ≤
      gramQuadForm
        (adjacentEvenAnchorInterfaceNetworkKernel
          cutoff localState linkCount)
        coefficient configurationCount :=
  gramPSD_quadForm_nonneg
    (adjacentEvenAnchorInterfaceNetworkGramRep
      cutoff localState hstate linkCount)
    coefficient configurationCount

#print axioms gramSymmetricEdgePair_eqv_row_add_cross
#print axioms gramDominantResidualPair_eqv_diag_sub_row
#print axioms gramDominantFeaturePair_eqv_identityPlusBilinear
#print axioms anchorResummedFaceChannelBilinear_eqv_identityPlus
#print axioms adjacentEvenAnchorResummedFixedFaceLinkKernel_eqv_features
#print axioms adjacentEvenAnchorResidualFeatureGramRep
#print axioms adjacentEvenAnchorEdgeFeatureGramRep
#print axioms adjacentEvenAnchorDominantFeatureGramRep
#print axioms adjacentEvenAnchorResummedPhysicalLinkGramRep
#print axioms adjacentEvenAnchorInterfaceNetworkGramRep
#print axioms adjacentEvenAnchorInterfaceNetworkQuadratic_nonnegative

end YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenInterfaceLinkGram
