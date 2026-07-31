/-
# Constructive physical negative-action limit for the compact BF4 carrier

This file passes from the coefficientwise identity

  exp(-133/4) H(P² exp(D)) = H(P² exp(-A))

to a sound statement about located constructive limits.  The finite product
rectangle is split into its Cauchy triangle and corner.  The triangle is the
genuine negative-action Taylor partial, while the corner is dominated by the
ordinary exponential Mertens corner at the coefficient-L1 majorants already
proved for the compact BF4 action.

No equality of integrated polynomials is multiplied by an extra factor.  The
carrier identification used here is the arbitrary-suffix Haar theorem from
`BF4CompactActionExponentialShift`.

## Axiom gate

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4CompactActionExponentialShift
import YMGap.Constructive.CornerBoundAdd
import YMGap.Constructive.CRealAbs
import YMGap.Constructive.CRealMulMono

namespace YMGap.Continuum.BF4CompactActionPhysicalLimit

set_option maxRecDepth 100000
set_option maxHeartbeats 24000000

open YMGap.Constructive
open YMGap.Constructive.ExpNeg
open YMGap.Constructive.HalfPow
open YMGap.Constructive.RationalTail
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.BF4CompactActionShiftedExponential
open YMGap.Continuum.BF4CompactActionShiftedLimit
open YMGap.Continuum.BF4CompactActionExponentialShift
open YMGap.Continuum.BF4CompactCoupledActionBounds
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The finite Cauchy triangle and corner -/

/-- The coefficient product occurring at total degree `total`. -/
def compactShiftedConvolutionTerm
    (polynomial : RatPoly) (total index : Nat) : Q' :=
  ExpNeg.term compactCoupledBF4ActionCeiling index *
    compactActionShiftedTaylorQuadraticTerm
      polynomial (total - index)

/-- The total-degree coefficient of the scalar exponential times the located
shifted BF4 series. -/
def compactShiftedConvolution
    (polynomial : RatPoly) (total : Nat) : Q' :=
  finSum
    (compactShiftedConvolutionTerm polynomial total)
    (total + 1)

/-- One row of the lower Cauchy triangle. -/
def compactShiftedTriangleTerm
    (polynomial : RatPoly) (terms : Nat) : Nat → Q' :=
  fun index =>
    ExpNeg.term compactCoupledBF4ActionCeiling index *
      compactActionShiftedTaylorQuadraticPartial
        polynomial (terms - index)

/-- The lower Cauchy triangle inside the `terms × terms` product rectangle. -/
def compactShiftedTriangle
    (polynomial : RatPoly) (terms : Nat) : Q' :=
  finSum (compactShiftedTriangleTerm polynomial terms) terms

/-- One row of the upper-right Mertens corner. -/
def compactShiftedCornerTerm
    (polynomial : RatPoly) (terms : Nat) : Nat → Q' :=
  fun index =>
    ExpNeg.term compactCoupledBF4ActionCeiling index *
      (compactActionShiftedTaylorQuadraticPartial polynomial terms +
        -(compactActionShiftedTaylorQuadraticPartial
          polynomial (terms - index)))

/-- The part of the product rectangle above the total-degree diagonal. -/
def compactShiftedCorner
    (polynomial : RatPoly) (terms : Nat) : Q' :=
  finSum (compactShiftedCornerTerm polynomial terms) terms

private theorem compactActionShiftedTaylorQuadraticPartial_eq_finSum
    (polynomial : RatPoly) :
    ∀ terms : Nat,
      compactActionShiftedTaylorQuadraticPartial
          polynomial terms =
        finSum
          (compactActionShiftedTaylorQuadraticTerm polynomial)
          terms
  | 0 => rfl
  | terms + 1 => by
      rw [
        compactActionShiftedTaylorQuadraticPartial,
        finSum_succ,
        compactActionShiftedTaylorQuadraticPartial_eq_finSum
          polynomial terms]

theorem compactShiftedTriangle_succ
    (polynomial : RatPoly) (terms : Nat) :
    compactShiftedTriangle polynomial (terms + 1) ≈
      compactShiftedTriangle polynomial terms +
        compactShiftedConvolution polynomial terms := by
  have hlast :
      compactShiftedTriangleTerm
          polynomial (terms + 1) terms ≈
        compactShiftedConvolutionTerm
          polynomial terms terms := by
    have hsub : (terms + 1) - terms = 1 := by
      omega
    have hzero : terms - terms = 0 := by
      omega
    unfold compactShiftedTriangleTerm
      compactShiftedConvolutionTerm
    rw [hsub, hzero]
    change
      ExpNeg.term compactCoupledBF4ActionCeiling terms *
          (0 +
            compactActionShiftedTaylorQuadraticTerm
              polynomial 0) ≈
        ExpNeg.term compactCoupledBF4ActionCeiling terms *
          compactActionShiftedTaylorQuadraticTerm
            polynomial 0
    exact Q'.mul_eqv_congr_left _ _ _
      (Q'.eqv_of_eq
        (Q'.zero_add'
          (compactActionShiftedTaylorQuadraticTerm
            polynomial 0)))
  have hrow :
      ∀ index, index < terms →
        compactShiftedTriangleTerm
            polynomial (terms + 1) index ≈
          compactShiftedTriangleTerm polynomial terms index +
            compactShiftedConvolutionTerm
              polynomial terms index := by
    intro index hindex
    have hsub :
        (terms + 1) - index =
          (terms - index) + 1 := by
      omega
    unfold compactShiftedTriangleTerm
      compactShiftedConvolutionTerm
    rw [hsub]
    change
      ExpNeg.term compactCoupledBF4ActionCeiling index *
          (compactActionShiftedTaylorQuadraticPartial
              polynomial (terms - index) +
            compactActionShiftedTaylorQuadraticTerm
              polynomial (terms - index)) ≈
        ExpNeg.term compactCoupledBF4ActionCeiling index *
              compactActionShiftedTaylorQuadraticPartial
                polynomial (terms - index) +
          ExpNeg.term compactCoupledBF4ActionCeiling index *
              compactActionShiftedTaylorQuadraticTerm
                polynomial (terms - index)
    exact Q'.mul_add_eqv _ _ _
  have hinner :
      finSum
          (compactShiftedTriangleTerm
            polynomial (terms + 1))
          terms ≈
        compactShiftedTriangle polynomial terms +
          finSum
            (compactShiftedConvolutionTerm
              polynomial terms)
            terms := by
    exact Q'.eqv_trans _ _ _
      (finSum_eqv_congr_lt
        (compactShiftedTriangleTerm
          polynomial (terms + 1))
        (fun index =>
          compactShiftedTriangleTerm polynomial terms index +
            compactShiftedConvolutionTerm
              polynomial terms index)
        terms hrow)
      (finSum_add
        (compactShiftedTriangleTerm polynomial terms)
        (compactShiftedConvolutionTerm polynomial terms)
        terms)
  change
    finSum
          (compactShiftedTriangleTerm
            polynomial (terms + 1))
          terms +
        compactShiftedTriangleTerm
          polynomial (terms + 1) terms ≈
      compactShiftedTriangle polynomial terms +
        (finSum
            (compactShiftedConvolutionTerm
              polynomial terms)
            terms +
          compactShiftedConvolutionTerm
            polynomial terms terms)
  refine Q'.eqv_trans _
    ((compactShiftedTriangle polynomial terms +
        finSum
          (compactShiftedConvolutionTerm polynomial terms)
          terms) +
      compactShiftedConvolutionTerm
        polynomial terms terms) _
    (Q'.add_eqv_congr'
      hinner hlast) ?_
  exact Q'.add_assoc_eqv _ _ _

theorem compactShiftedTriangle_eq_convolutionSum
    (polynomial : RatPoly) :
    ∀ terms : Nat,
      compactShiftedTriangle polynomial terms ≈
        finSum (compactShiftedConvolution polynomial) terms
  | 0 => Q'.eqv_refl 0
  | terms + 1 => by
      refine Q'.eqv_trans _ _ _
        (compactShiftedTriangle_succ polynomial terms) ?_
      exact Q'.add_eqv_congr_right _ _
        (compactShiftedConvolution polynomial terms)
        (compactShiftedTriangle_eq_convolutionSum
          polynomial terms)

theorem compactShiftedProduct_eq_triangle_add_corner
    (polynomial : RatPoly) (terms : Nat) :
    ExpNeg.partialSum
          compactCoupledBF4ActionCeiling terms *
        compactActionShiftedTaylorQuadraticPartial
          polynomial terms ≈
      compactShiftedTriangle polynomial terms +
        compactShiftedCorner polynomial terms := by
  rw [partialSum_eq_finSum]
  refine Q'.eqv_trans _
    (finSum
      (fun index =>
        ExpNeg.term
            compactCoupledBF4ActionCeiling index *
          compactActionShiftedTaylorQuadraticPartial
            polynomial terms)
      terms) _
    (finSum_mul_const
      (ExpNeg.term compactCoupledBF4ActionCeiling)
      (compactActionShiftedTaylorQuadraticPartial
        polynomial terms)
      terms) ?_
  have hterm :
      ∀ index,
        ExpNeg.term compactCoupledBF4ActionCeiling index *
            compactActionShiftedTaylorQuadraticPartial
              polynomial terms ≈
          compactShiftedTriangleTerm
                polynomial terms index +
            compactShiftedCornerTerm
                polynomial terms index := by
    intro index
    unfold compactShiftedTriangleTerm
      compactShiftedCornerTerm
    refine Q'.eqv_trans _
      (ExpNeg.term compactCoupledBF4ActionCeiling index *
        (compactActionShiftedTaylorQuadraticPartial
              polynomial (terms - index) +
          (compactActionShiftedTaylorQuadraticPartial
                polynomial terms +
            -(compactActionShiftedTaylorQuadraticPartial
              polynomial (terms - index))))) _
      (Q'.mul_eqv_congr_left _ _ _
        (Q'.add_sub_cancel_eqv
          (compactActionShiftedTaylorQuadraticPartial
            polynomial terms)
          (compactActionShiftedTaylorQuadraticPartial
            polynomial (terms - index)))) ?_
    exact Q'.mul_add_eqv _ _ _
  refine Q'.eqv_trans _
    (finSum
      (fun index =>
        compactShiftedTriangleTerm polynomial terms index +
          compactShiftedCornerTerm polynomial terms index)
      terms) _
    (finSum_eqv_congr _ _ hterm terms) ?_
  exact finSum_add
    (compactShiftedTriangleTerm polynomial terms)
    (compactShiftedCornerTerm polynomial terms)
    terms

/-! ## 2. The triangle is the genuine negative-action Taylor partial -/

/-- The first `terms` genuine physical `H(P² exp(-A))` coefficients. -/
def compactPhysicalNegativeTaylorQuadraticPartial
    (polynomial : RatPoly) (terms : Nat) : Q' :=
  finSum
    (compactPhysicalNegativeTaylorHaarTerm
      (polyMul polynomial polynomial))
    terms

theorem compactShiftedConvolution_eq_physicalShift
    (polynomial : RatPoly) (total : Nat) :
    compactShiftedConvolution polynomial total ≈
      compactPhysicalShiftConvolution
        (polyMul polynomial polynomial) total := by
  unfold compactShiftedConvolution
    compactPhysicalShiftConvolution
  exact finSum_eqv_congr _ _
    (fun index =>
      Q'.mul_eqv_congr_left
        (ExpNeg.term
          compactCoupledBF4ActionCeiling index)
        _ _
        (compactActionShiftedTaylorQuadraticTerm_eq_complement
          polynomial (total - index)))
    (total + 1)

theorem compactShiftedConvolution_eq_negative
    (polynomial : RatPoly) (total : Nat) :
    compactShiftedConvolution polynomial total ≈
      compactPhysicalNegativeTaylorHaarTerm
        (polyMul polynomial polynomial) total := by
  exact Q'.eqv_trans _ _ _
    (compactShiftedConvolution_eq_physicalShift
      polynomial total)
    (compactPhysicalShiftConvolution_eq_negative
      total (polyMul polynomial polynomial))

theorem compactShiftedTriangle_eq_negativePartial
    (polynomial : RatPoly) (terms : Nat) :
    compactShiftedTriangle polynomial terms ≈
      compactPhysicalNegativeTaylorQuadraticPartial
        polynomial terms := by
  exact Q'.eqv_trans _ _ _
    (compactShiftedTriangle_eq_convolutionSum
      polynomial terms)
    (finSum_eqv_congr _ _
      (compactShiftedConvolution_eq_negative polynomial)
      terms)

/-- Exact finite rectangle/physical-triangle/corner decomposition. -/
theorem compactShiftedProduct_eq_negativePartial_add_corner
    (polynomial : RatPoly) (terms : Nat) :
    ExpNeg.partialSum
          compactCoupledBF4ActionCeiling terms *
        compactActionShiftedTaylorQuadraticPartial
          polynomial terms ≈
      compactPhysicalNegativeTaylorQuadraticPartial
          polynomial terms +
        compactShiftedCorner polynomial terms := by
  exact Q'.eqv_trans _ _ _
    (compactShiftedProduct_eq_triangle_add_corner
      polynomial terms)
    (Q'.add_eqv_congr_right _ _
      (compactShiftedCorner polynomial terms)
      (compactShiftedTriangle_eq_negativePartial
        polynomial terms))

/-! ## 3. A quantitative BF4 Mertens-corner bound -/

theorem compactShiftedPartial_block_upper
    (polynomial : RatPoly) (start : Nat) :
    ∀ distance : Nat,
      compactActionShiftedTaylorQuadraticPartial
          polynomial (start + distance) ≤
        compactActionShiftedTaylorQuadraticPartial
            polynomial start +
          scaledTaylorBlockAbs
            (compactActionShiftedInsertionL1 polynomial)
            compactActionComplementL1 start distance
  | 0 =>
      Q'.add_le_self_of_nonneg _ _
        (Q'.le_refl' 0)
  | distance + 1 => by
      have hinduction :=
        compactShiftedPartial_block_upper
          polynomial start distance
      have hterm :=
        compactActionShiftedTaylorQuadraticTerm_le_majorant
          polynomial (start + distance)
      exact Q'.le_trans' _ _ _
        (ExpNeg.add_le_add2 hinduction hterm)
        (Q'.le_of_eqv
          (Q'.add_assoc_eqv
            (compactActionShiftedTaylorQuadraticPartial
              polynomial start)
            (scaledTaylorBlockAbs
              (compactActionShiftedInsertionL1 polynomial)
              compactActionComplementL1 start distance)
            (compactActionShiftedInsertionL1 polynomial *
              ExpNeg.termAbs compactActionComplementL1
                (start + distance))))

theorem compactShiftedPartial_difference_upper
    (polynomial : RatPoly) (start distance : Nat) :
    compactActionShiftedTaylorQuadraticPartial
          polynomial (start + distance) +
        -(compactActionShiftedTaylorQuadraticPartial
          polynomial start) ≤
      compactActionShiftedInsertionL1 polynomial *
        ExpNeg.blockAbs
          compactActionComplementL1 start distance := by
  exact Q'.le_trans' _ _ _
    (Q'.sub_le_of_le_add
      (compactShiftedPartial_block_upper
        polynomial start distance))
    (Q'.le_of_eqv
      (scaledTaylorBlockAbs_eq
        (compactActionShiftedInsertionL1 polynomial)
        compactActionComplementL1 start distance))

private theorem compactShiftedCornerTerm_two_sided
    (polynomial : RatPoly)
    (hsupport :
      SupportedQuaternionBlocks 10 polynomial)
    (terms index : Nat) (hindex : index < terms) :
    compactShiftedCornerTerm polynomial terms index ≤
          compactActionShiftedInsertionL1 polynomial *
            cornerAbsTermAdd
              compactCoupledBF4ActionCeiling
              compactActionComplementL1
              terms index ∧
      -(compactShiftedCornerTerm polynomial terms index) ≤
          compactActionShiftedInsertionL1 polynomial *
            cornerAbsTermAdd
              compactCoupledBF4ActionCeiling
              compactActionComplementL1
              terms index := by
  let scale :=
    compactActionShiftedInsertionL1 polynomial
  let actionL1 := compactActionComplementL1
  let scalarTerm :=
    ExpNeg.term compactCoupledBF4ActionCeiling index
  let scalarAbs :=
    ExpNeg.termAbs compactCoupledBF4ActionCeiling index
  let difference :=
    compactActionShiftedTaylorQuadraticPartial
          polynomial terms +
      -(compactActionShiftedTaylorQuadraticPartial
        polynomial (terms - index))
  let block :=
    ExpNeg.blockAbs actionL1 (terms - index) index
  have hsum : (terms - index) + index = terms := by
    omega
  have hscale0 : (0 : Q') ≤ scale :=
    compactActionShiftedInsertionL1_nonnegative polynomial
  have haction0 : (0 : Q') ≤ actionL1 :=
    compactActionComplementL1_nonnegative
  have hscalarAbs0 : (0 : Q') ≤ scalarAbs :=
    ExpNeg.termAbs_nonneg
      compactCoupledBF4ActionCeiling (by decide) index
  have hblock0 : (0 : Q') ≤ block := by
    unfold block
    rw [ExpNeg.blockAbs_eq_finSum]
    exact finSum_monotone_of_nonneg
      (fun offset =>
        ExpNeg.termAbs actionL1
          ((terms - index) + offset))
      (fun offset =>
        ExpNeg.termAbs_nonneg actionL1 haction0
          ((terms - index) + offset))
      0 index (Nat.zero_le index)
  have hscaledBlock0 :
      (0 : Q') ≤ scale * block :=
    Q'.mul_nonneg scale block hscale0 hblock0
  have hdifference0 : (0 : Q') ≤ difference := by
    apply Q'.sub_nonneg_of_le
    have hmono :=
      compactActionShiftedTaylorQuadraticPartial_add_mono
        polynomial hsupport (terms - index) index
    rw [hsum] at hmono
    exact hmono
  have hdifferenceUpper :
      difference ≤ scale * block := by
    have hraw :=
      compactShiftedPartial_difference_upper
        polynomial (terms - index) index
    rw [hsum] at hraw
    exact hraw
  have hdifferenceLower :
      -(scale * block) ≤ difference := by
    exact Q'.le_trans' _ (0 : Q') _
      (Q'.neg_le_neg hscaledBlock0)
      hdifference0
  obtain ⟨hscalarUpper, hnegScalarUpper⟩ :=
    ExpNeg.term_two_sided
      compactCoupledBF4ActionCeiling
      (by decide) index
  have hscalarLower : -scalarAbs ≤ scalarTerm := by
    exact Q'.le_trans' _ _ _
      (Q'.neg_le_neg hnegScalarUpper)
      (Q'.le_of_eqv
        (Q'.neg_neg_eqv scalarTerm))
  have hbound :
      scalarAbs * (scale * block) ≈
        scale * (scalarAbs * block) := by
    refine Q'.eqv_trans _
      ((scalarAbs * scale) * block) _
      (Q'.eqv_symm
        (Q'.mul_assoc_eqv scalarAbs scale block)) ?_
    refine Q'.eqv_trans _
      ((scale * scalarAbs) * block) _
      (Q'.mul_eqv_congr_right _ _ block
        (Q'.mul_comm_eqv scalarAbs scale)) ?_
    exact Q'.mul_assoc_eqv scale scalarAbs block
  have hupperRaw :
      scalarTerm * difference ≤
        scalarAbs * (scale * block) :=
    Q'.mul_le_of_bounds
      hscalarAbs0 hscaledBlock0
      hscalarLower hscalarUpper
      hdifferenceLower hdifferenceUpper
  have hnegScalarLower :
      -scalarAbs ≤ -scalarTerm := by
    exact Q'.neg_le_neg hscalarUpper
  have hnegRaw :
      (-scalarTerm) * difference ≤
        scalarAbs * (scale * block) :=
    Q'.mul_le_of_bounds
      hscalarAbs0 hscaledBlock0
      hnegScalarLower hnegScalarUpper
      hdifferenceLower hdifferenceUpper
  unfold compactShiftedCornerTerm
    cornerAbsTermAdd
  change
    scalarTerm * difference ≤
          scale * (scalarAbs * block) ∧
      -(scalarTerm * difference) ≤
          scale * (scalarAbs * block)
  refine ⟨Q'.le_trans' _ _ _
      hupperRaw (Q'.le_of_eqv hbound), ?_⟩
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (Q'.eqv_symm
        (Q'.neg_mul_eqv scalarTerm difference)))
    (Q'.le_trans' _ _ _
      hnegRaw (Q'.le_of_eqv hbound))

/-- The signed BF4 corner is bounded on both sides by the coefficient-L1
scale times the ordinary exponential Mertens corner. -/
theorem compactShiftedCorner_two_sided
    (polynomial : RatPoly)
    (hsupport :
      SupportedQuaternionBlocks 10 polynomial)
    (terms : Nat) :
    compactShiftedCorner polynomial terms ≤
          compactActionShiftedInsertionL1 polynomial *
            cornerAbsAdd
              compactCoupledBF4ActionCeiling
              compactActionComplementL1 terms ∧
      -(compactShiftedCorner polynomial terms) ≤
          compactActionShiftedInsertionL1 polynomial *
            cornerAbsAdd
              compactCoupledBF4ActionCeiling
              compactActionComplementL1 terms := by
  let majorant :=
    fun index =>
      compactActionShiftedInsertionL1 polynomial *
        cornerAbsTermAdd
          compactCoupledBF4ActionCeiling
          compactActionComplementL1 terms index
  have hpositive :
      compactShiftedCorner polynomial terms ≤
        finSum majorant terms :=
    finSum_le_lt
      (compactShiftedCornerTerm polynomial terms)
      majorant terms
      (fun index hindex =>
        (compactShiftedCornerTerm_two_sided
          polynomial hsupport terms index hindex).1)
  have hnegative :
      -(compactShiftedCorner polynomial terms) ≤
        finSum majorant terms := by
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (neg_finSum
          (compactShiftedCornerTerm polynomial terms)
          terms))
      (finSum_le_lt
        (fun index =>
          -(compactShiftedCornerTerm
            polynomial terms index))
        majorant terms
        (fun index hindex =>
          (compactShiftedCornerTerm_two_sided
            polynomial hsupport terms index hindex).2))
  have hmajorant :
      finSum majorant terms ≈
        compactActionShiftedInsertionL1 polynomial *
          cornerAbsAdd
            compactCoupledBF4ActionCeiling
            compactActionComplementL1 terms := by
    exact Q'.eqv_symm
      (const_mul_finSum
        (cornerAbsTermAdd
          compactCoupledBF4ActionCeiling
          compactActionComplementL1 terms)
        (compactActionShiftedInsertionL1 polynomial)
        terms)
  exact
    ⟨Q'.le_trans' _ _ _
      hpositive (Q'.le_of_eqv hmajorant),
     Q'.le_trans' _ _ _
      hnegative (Q'.le_of_eqv hmajorant)⟩

/-- Explicit vanishing of the physical BF4 Mertens corner. -/
theorem compactShiftedCorner_eventually_small
    (polynomial : RatPoly)
    (hsupport :
      SupportedQuaternionBlocks 10 polynomial)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon) :
    ∃ cutoff : Nat, ∀ terms : Nat, cutoff ≤ terms →
      compactShiftedCorner polynomial terms ≤ epsilon ∧
        -(compactShiftedCorner polynomial terms) ≤ epsilon := by
  let scale :=
    compactActionShiftedInsertionL1 polynomial
  let delta :=
    epsilon * Q'.invSucc scale.num.toNat
  have hscale0 : (0 : Q') ≤ scale :=
    compactActionShiftedInsertionL1_nonnegative polynomial
  have hepsilon0 : (0 : Q') ≤ epsilon :=
    Q'.le_of_lt hepsilon
  have hdeltaPos : (0 : Q') < delta :=
    Q'.mul_pos hepsilon
      (Q'.invSucc_pos scale.num.toNat)
  have hdelta0 : (0 : Q') ≤ delta :=
    Q'.le_of_lt hdeltaPos
  obtain ⟨cutoff, hcutoff⟩ :=
    cornerAbsAdd_le
      compactCoupledBF4ActionCeiling
      compactActionComplementL1
      (by decide)
      compactActionComplementL1_nonnegative
      delta hdeltaPos
  refine ⟨cutoff, fun terms hterms => ?_⟩
  have hcorner :=
    compactShiftedCorner_two_sided
      polynomial hsupport terms
  have hscaled :
      scale *
          cornerAbsAdd
            compactCoupledBF4ActionCeiling
            compactActionComplementL1 terms ≤
        epsilon := by
    exact Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ scale
        (hcutoff terms hterms) hscale0)
      (ExpNeg.mul_le_of_mul_invSucc_toNat
        scale epsilon hscale0 hepsilon0)
  exact
    ⟨Q'.le_trans' _ _ _ hcorner.1 hscaled,
     Q'.le_trans' _ _ _ hcorner.2 hscaled⟩

/-! ## 4. Located physical limit and convergence of the genuine series -/

/-- The located physical compact BF4 quadratic.  It is constructed as the
product of the scalar sphere shift and the located positive complement
series; the convergence theorem below proves that the genuine
`H(P² exp(-A))` Taylor partials have exactly this limit. -/
def compactPhysicalNegativeTaylorQuadraticLimit
    (polynomial : RatPoly)
    (hsupport :
      SupportedQuaternionBlocks 10 polynomial) :
    CReal :=
  CReal.mul
    (ExpNeg.expNeg
      compactCoupledBF4ActionCeiling (by decide))
    (compactActionShiftedTaylorQuadraticLimit
      polynomial hsupport)

/-- **Haar--`L²` positivity of the located physical endpoint.**

For every supported rational polynomial `P`, the genuine compact BF4
functional

`H₁₀(P² exp(-A))`

is nonnegative in the sound constructive-real order.  This is derived from
the exact sphere shift: the scalar factor `exp(-133/4)` is nonnegative and
the shifted complement series is a located limit of nonnegative Haar
quadratics.  No positivity certificate is passed as an argument.

This is positivity of the full ten-holonomy square functional.  Reflected
source/target positivity is a distinct statement and requires the
cross-plane Gram factorization. -/
theorem compactPhysicalNegativeTaylorQuadraticLimit_nonnegative
    (polynomial : RatPoly)
    (hsupport :
      SupportedQuaternionBlocks 10 polynomial) :
    ExpPos.geRat
      (compactPhysicalNegativeTaylorQuadraticLimit
        polynomial hsupport)
      0 := by
  exact CReal.mul_nonneg
    (expNeg_geRat_zero
      compactCoupledBF4ActionCeiling (by decide))
    (compactActionShiftedTaylorQuadraticLimit_nonnegative
      polynomial hsupport)

@[simp] theorem compactPhysicalNegativeTaylorQuadraticLimit_approx
    (polynomial : RatPoly)
    (hsupport :
      SupportedQuaternionBlocks 10 polynomial)
    (terms : Nat) :
    (compactPhysicalNegativeTaylorQuadraticLimit
      polynomial hsupport).approx terms =
        ExpNeg.partialSum
            compactCoupledBF4ActionCeiling terms *
          compactActionShiftedTaylorQuadraticPartial
            polynomial terms := rfl

/-- The genuine physical partial and the same-cutoff located product
approximation differ by an explicitly vanishing corner. -/
theorem compactPhysicalNegativeTaylorPartial_product_close
    (polynomial : RatPoly)
    (hsupport :
      SupportedQuaternionBlocks 10 polynomial)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon) :
    ∃ cutoff : Nat, ∀ terms : Nat, cutoff ≤ terms →
      compactPhysicalNegativeTaylorQuadraticPartial
            polynomial terms ≤
          (compactPhysicalNegativeTaylorQuadraticLimit
            polynomial hsupport).approx terms +
            epsilon ∧
        (compactPhysicalNegativeTaylorQuadraticLimit
            polynomial hsupport).approx terms ≤
          compactPhysicalNegativeTaylorQuadraticPartial
              polynomial terms +
            epsilon := by
  obtain ⟨cutoff, hcutoff⟩ :=
    compactShiftedCorner_eventually_small
      polynomial hsupport epsilon hepsilon
  refine ⟨cutoff, fun terms hterms => ?_⟩
  let product :=
    (compactPhysicalNegativeTaylorQuadraticLimit
      polynomial hsupport).approx terms
  let physical :=
    compactPhysicalNegativeTaylorQuadraticPartial
      polynomial terms
  let corner :=
    compactShiftedCorner polynomial terms
  have hdecomposition : product ≈ physical + corner := by
    exact compactShiftedProduct_eq_negativePartial_add_corner
      polynomial terms
  obtain ⟨hcornerUpper, hnegCornerUpper⟩ :=
    hcutoff terms hterms
  have hphysical :
      physical ≈ product + (-corner) := by
    have hforward :
        product + (-corner) ≈
          (physical + corner) + (-corner) :=
      Q'.add_eqv_congr_right _ _ _
        hdecomposition
    have hcancel :
        (physical + corner) + (-corner) ≈
          physical := by
      refine Q'.eqv_trans _
        (physical + (corner + (-corner))) _
        (Q'.add_assoc_eqv physical corner (-corner)) ?_
      refine Q'.eqv_trans _
        (physical + 0) _
        (Q'.add_eqv_congr_left physical _ _
          (Q'.add_neg_self_eqv corner)) ?_
      exact Q'.eqv_of_eq
        (Q'.add_zero' physical)
    exact Q'.eqv_symm
      (Q'.eqv_trans _ _ _
        hforward hcancel)
  change
    physical ≤ product + epsilon ∧
      product ≤ physical + epsilon
  refine ⟨?_, ?_⟩
  · exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv hphysical)
      (Q'.add_le_add_left product
        (-corner) epsilon hnegCornerUpper)
  · exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv hdecomposition)
      (Q'.add_le_add_left physical
        corner epsilon hcornerUpper)

/-- **Located negative-action exponential identity.**

The lifted genuine Taylor partials `H(P² exp(-A))` converge to the located
product `exp(-133/4) H(P² exp(D))`.  This is the constructive limit-level
version of the coefficientwise sphere shift. -/
theorem compactPhysicalNegativeTaylorQuadraticPartial_converges
    (polynomial : RatPoly)
    (hsupport :
      SupportedQuaternionBlocks 10 polynomial) :
    CReal.ConvergesTo
      (fun terms =>
        CReal.ofQ'
          (compactPhysicalNegativeTaylorQuadraticPartial
            polynomial terms))
      (compactPhysicalNegativeTaylorQuadraticLimit
        polynomial hsupport) := by
  intro epsilon hepsilon
  let halfEpsilon := HalfPow.half * epsilon
  have hhalfEpsilon :
      (0 : Q') < halfEpsilon :=
    ExpNeg.half_mul_pos epsilon hepsilon
  obtain ⟨cornerCutoff, hcorner⟩ :=
    compactPhysicalNegativeTaylorPartial_product_close
      polynomial hsupport halfEpsilon hhalfEpsilon
  obtain ⟨limitCutoff, hlimit⟩ :=
    (compactPhysicalNegativeTaylorQuadraticLimit
      polynomial hsupport).cauchy
        halfEpsilon hhalfEpsilon
  refine
    ⟨max cornerCutoff limitCutoff,
      fun terms hterms =>
        ⟨limitCutoff, fun approximation happ => ?_⟩⟩
  have hcornerStage : cornerCutoff ≤ terms :=
    Nat.le_trans (Nat.le_max_left _ _) hterms
  have hlimitStage : limitCutoff ≤ terms :=
    Nat.le_trans (Nat.le_max_right _ _) hterms
  obtain ⟨hphysicalToSame, hsameToPhysical⟩ :=
    hcorner terms hcornerStage
  obtain ⟨hsameToLimit, hlimitToSame⟩ :=
    hlimit terms approximation hlimitStage happ
  change
    compactPhysicalNegativeTaylorQuadraticPartial
          polynomial terms ≤
        (compactPhysicalNegativeTaylorQuadraticLimit
            polynomial hsupport).approx approximation +
          epsilon ∧
      (compactPhysicalNegativeTaylorQuadraticLimit
            polynomial hsupport).approx approximation ≤
        compactPhysicalNegativeTaylorQuadraticPartial
            polynomial terms +
          epsilon
  refine ⟨?_, ?_⟩
  · refine Q'.le_trans' _ _ _
      hphysicalToSame
      (Q'.le_trans' _ _ _
        (Q'.add_le_add_right _ _
          halfEpsilon hsameToLimit)
        (Q'.le_of_eqv ?_))
    refine Q'.eqv_trans _
      ((compactPhysicalNegativeTaylorQuadraticLimit
          polynomial hsupport).approx approximation +
        (halfEpsilon + halfEpsilon)) _
      (Q'.add_assoc_eqv _ halfEpsilon halfEpsilon) ?_
    exact Q'.add_eqv_congr_left _ _ _
      (ExpNeg.two_halves epsilon)
  · refine Q'.le_trans' _ _ _
      hlimitToSame
      (Q'.le_trans' _ _ _
        (Q'.add_le_add_right _ _
          halfEpsilon hsameToPhysical)
        (Q'.le_of_eqv ?_))
    refine Q'.eqv_trans _
      (compactPhysicalNegativeTaylorQuadraticPartial
          polynomial terms +
        (halfEpsilon + halfEpsilon)) _
      (Q'.add_assoc_eqv _ halfEpsilon halfEpsilon) ?_
    exact Q'.add_eqv_congr_left _ _ _
      (ExpNeg.two_halves epsilon)

end YMGap.Continuum.BF4CompactActionPhysicalLimit

#print axioms YMGap.Continuum.BF4CompactActionPhysicalLimit.compactShiftedTriangle_succ
#print axioms YMGap.Continuum.BF4CompactActionPhysicalLimit.compactShiftedProduct_eq_negativePartial_add_corner
#print axioms YMGap.Continuum.BF4CompactActionPhysicalLimit.compactShiftedCorner_eventually_small
#print axioms YMGap.Continuum.BF4CompactActionPhysicalLimit.compactPhysicalNegativeTaylorQuadraticLimit
#print axioms YMGap.Continuum.BF4CompactActionPhysicalLimit.compactPhysicalNegativeTaylorQuadraticLimit_nonnegative
#print axioms YMGap.Continuum.BF4CompactActionPhysicalLimit.compactPhysicalNegativeTaylorQuadraticPartial_converges
