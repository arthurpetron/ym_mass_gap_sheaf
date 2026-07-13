/-
The harmonic fused separator can be compared honestly with the established
reflection-positive character transfer operator, but it cannot be identified
with that operator's fundamental eigenvalue by an exact rank-one intertwiner.

The fundamental character line of `charTransfer` is invariant with eigenvalue
`heatKernelSep w = w^3`.  The one-channel fused operator instead has eigenvalue
`lamPW w N 1`, whose complementary margin is exactly `harmonicMass`.  At the
first harmonic scale these eigenvalues are distinct, so positivity plus exact
rank-one intertwining is machine-refuted.

The remaining compatible input is only the scalar comparison

  heatKernelSep (harmW k) <= lamPW (harmW k) (Ncut k) 1.

It is packaged pointwise and globally below.  The pointwise datum is inhabited
at the first two scales.  From the global datum, this module constructs a
located gap and an operator-form gap for the existing `charTransfer`, using the
fused eigenvalue as a (weaker) separator.  Its gap margin is definitionally the
actual harmonic fused mass.
-/

import YMGap.Continuum.FusedOperatorIntertwinerFence
import YMGap.Continuum.HarmonicWeightDriftFence
import YMGap.Continuum.PhysicalCharCoordinateMap

namespace YMGap.Continuum.HarmonicTransferOperatorIdentification

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.CompactTransferGNS
open YMGap.Continuum.CorrectedCarrierOperatorBridge
open YMGap.Continuum.FusedOperatorIntertwinerFence
open YMGap.Continuum.FusedPeterWeylNormalization
open YMGap.Continuum.HamiltonianScalar
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicFusedSchurObstruction
open YMGap.Continuum.HarmonicWeightDriftFence
open YMGap.Continuum.HeatKernelGap
open YMGap.Continuum.PhysicalCharCoordinateMap
open YMGap.Continuum.QuadraticCutoffSchedule
open YMGap.Continuum.RCScaleClose
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SpectralGap
open YMGap.Continuum.WilsonSchurIdentities
open YMGap.Continuum.WilsonSpectralBridge

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The actual invariant fundamental line -/

/-- The spin-one character coordinate in the excited-only indexing. -/
def fundamentalChar : Nat -> Q' := fun s => if s = 0 then (1 : Q') else 0

/-- The fundamental character line is invariant under the established
reflection-positive character transfer operator, with exact eigenvalue `w^3`.
The statement is pointwise on the completed character carrier. -/
theorem fundamentalChar_invariant
    (w : Q') (hw0 : (0 : Q') <= w) (hw1 : w < (1 : Q'))
    (t : Q') (ht : (0 : Q') <= t) (N s : Nat) :
    ((charTransfer w hw0 hw1 t ht N).T fundamentalChar s) ≈
      heatKernelSep w * fundamentalChar s := by
  by_cases hs : s = 0
  · subst s
    unfold fundamentalChar charTransfer
    rw [if_pos rfl]
    exact Q'.eqv_trans _ _ _ (Q'.mul_one_eqv _)
      (Q'.eqv_symm (Q'.mul_one_eqv _))
  · have hT : ((charTransfer w hw0 hw1 t ht N).T fundamentalChar s) =
        qpow w (c4 (s + 1)) * fundamentalChar s := rfl
    rw [hT]
    unfold fundamentalChar
    rw [if_neg hs]
    exact Q'.eqv_trans _ _ _ (Q'.mul_zero_eqv _)
      (Q'.eqv_symm (Q'.mul_zero_eqv _))

/-! ## 2. Exact fused eigenvalue and the rank-one fence -/

/-- The one-channel fused operator's coordinate eigenvalue is exactly the
Peter--Weyl-normalized fused rate. -/
theorem harmonicFused_operator_eigen (k : Nat) :
    ((fusedChannelOp (harmW k) (Ncut k) 1).apply (basis 0) 0) ≈
      lamPW (harmW k) (Ncut k) 1 := by
  simpa [fusedChannelOp, fusedChannelLam] using
    (diagOp_eigen (fusedChannelLam (harmW k) (Ncut k) 1) 1 0 (by decide))

/-- The harmonic mass is precisely the complement of the constructed fused
operator eigenvalue. -/
theorem harmonicMass_eq_fused_operator_gap (k : Nat) :
    harmonicMass k ≈
      (1 : Q') - ((fusedChannelOp (harmW k) (Ncut k) 1).apply (basis 0) 0) := by
  unfold harmonicMass
  exact Q'.add_eqv_congr_left 1 _ _
    (Q'.neg_eqv_congr _ _ (Q'.eqv_symm (harmonicFused_operator_eigen k)))

/-- At the first harmonic scale the GNS fundamental eigenvalue and the fused
harmonic eigenvalue are not equal. -/
theorem harmonicFundamental_fused_ne_zero :
    ¬ (heatKernelSep (harmW 0) ≈ lamPW (harmW 0) (Ncut 0) 1) := by
  decide

/-- The mismatch written directly between the invariant line of the existing
character transfer operator and the constructed fused operator. -/
theorem harmonicChar_fundamental_not_fused_zero :
    ¬ (((charTransfer (harmW 0) (harmW_nonneg 0)
        (BakryEmery.one_sub_lt_one (harmU_pos 0))
        (0 : Q') (by decide) (Ncut 0)).T fundamentalChar 0) ≈
      ((fusedChannelOp (harmW 0) (Ncut 0) 1).apply (basis 0) 0)) := by
  intro h
  apply harmonicFundamental_fused_ne_zero
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_symm
      (fundamentalChar_invariant (harmW 0) (harmW_nonneg 0)
        (BakryEmery.one_sub_lt_one (harmU_pos 0))
        0 (by decide) (Ncut 0) 0))
    (Q'.eqv_trans _ _ _ h (harmonicFused_operator_eigen 0))

/-- Hence no positive rank-one map can exactly intertwine the fundamental GNS
character line with the first harmonic fused line. -/
theorem no_harmonic_zero_positive_rankOne_intertwiner :
    PositiveRankOneIntertwiner
      (heatKernelSep (harmW 0))
      (lamPW (harmW 0) (Ncut 0) 1) -> False := by
  intro I
  exact harmonicFundamental_fused_ne_zero
    (positive_rankOne_intertwiner_forces_eigen_eq I)

/-! ## 3. The minimal compatible scalar residual -/

/-- Pointwise comparison needed to use the fused eigenvalue as a separator for
the heat-kernel character spectrum. -/
structure HarmonicSectorComparison (k : Nat) : Type where
  heat_le_fused :
    heatKernelSep (harmW k) <= lamPW (harmW k) (Ncut k) 1

/-- The all-scale residual is only the family of explicit rational separator
comparisons; it contains no operator, RG map, or margin recursion fields. -/
def HarmonicTransferSectorDomination : Type :=
  forall k, HarmonicSectorComparison k

/-- Exact anchor comparison at the first harmonic scale. -/
def harmonicSectorComparison_zero : HarmonicSectorComparison 0 :=
  ⟨by decide⟩

/-- Exact comparison at the second harmonic scale. -/
def harmonicSectorComparison_one : HarmonicSectorComparison 1 :=
  ⟨by decide⟩

private theorem lt_one_of_one_sub_pos {x : Q'}
    (h : (0 : Q') < (1 : Q') - x) : x < (1 : Q') := by
  have hnum : (0 : Int) < ((1 : Q') - x).num := by
    change (0 : Int) * ((((1 : Q') - x).den : Nat) : Int) <
      ((1 : Q') - x).num * (((0 : Q').den : Nat) : Int) at h
    have h0d : (((0 : Q').den : Nat) : Int) = 1 := rfl
    rw [Int.zero_mul, h0d, Int.mul_one] at h
    exact h
  have hxnegnum : (-x).num = -x.num := rfl
  have hxnegden : (((-x).den : Nat) : Int) = (x.den : Int) := rfl
  change (0 : Int) <
    (1 : Q').num * (((-x).den : Nat) : Int) +
      (-x).num * (((1 : Q').den : Nat) : Int) at hnum
  rw [hxnegnum, hxnegden] at hnum
  have h1n : (1 : Q').num = 1 := rfl
  have h1d : (((1 : Q').den : Nat) : Int) = 1 := rfl
  rw [h1n, h1d, Int.one_mul, Int.mul_one] at hnum
  show x.num * (((1 : Q').den : Nat) : Int) <
    (1 : Q').num * (x.den : Int)
  rw [h1n, h1d, Int.mul_one, Int.one_mul]
  omega

/-- Every harmonic weight lies strictly below one. -/
theorem harmonicW_lt_one (k : Nat) : harmW k < (1 : Q') :=
  BakryEmery.one_sub_lt_one (harmU_pos k)

/-! ## 4. Conditional identification as an actual GNS operator gap -/

/-- Under only the scalar sector comparison, the fused harmonic eigenvalue is
a located separator for the complete excited character spectrum. -/
def harmonicCharLocatedGap (C : HarmonicTransferSectorDomination) (k : Nat) :
    LocatedSpectralGap
      (excitedCharModel (harmW k) (harmW_nonneg k) (Ncut k)) where
  sep := lamPW (harmW k) (Ncut k) 1
  sep_lt_one := lt_one_of_one_sub_pos (by
    change (0 : Q') < harmonicMass k
    exact harmonicMass_pos_all k)
  bound := fun i => Q'.le_trans' _ _ _
    (casimir_qpow_le (harmW_nonneg k) (harmW_le_one k) i)
    (C k).heat_le_fused

/-- The located separator's positive margin is exactly `harmonicMass`. -/
theorem harmonicChar_gapMargin_eq
    (C : HarmonicTransferSectorDomination) (k : Nat) :
    (harmonicCharLocatedGap C k).gapMargin = harmonicMass k := rfl

/-- The located harmonic separator attached to the existing
reflection-positive `charTransfer` on its completed GNS carrier. -/
def harmonicCharSpectralGapData
    (C : HarmonicTransferSectorDomination)
    (k : Nat) (t : Q') (ht : (0 : Q') <= t) :
    SpectralGapData (charComplete t ht (Ncut k)) where
  op := charTransfer (harmW k) (harmW_nonneg k)
    (harmonicW_lt_one k) t ht (Ncut k)
  model := excitedCharModel (harmW k) (harmW_nonneg k) (Ncut k)
  gap := harmonicCharLocatedGap C k

/-- The character Schur resolution, with eigenvalue bounds weakened from
`w^3` to the fused harmonic separator. -/
def harmonicCharSpectralBridge
    (C : HarmonicTransferSectorDomination)
    (k : Nat) (t : Q') (ht : (0 : Q') <= t) :
    TransferSpectralBridge
      (harmonicCharSpectralGapData C k t ht) rcScaleResidualPlus := by
  let hw1 : harmW k < (1 : Q') := harmonicW_lt_one k
  let P := physicalCharCoordDiagResolution
    (harmW k) (harmW_nonneg k) hw1 t ht (Ncut k)
  refine {
    coeffSq := P.coeffSq
    coeffSq_nonneg := P.coeffSq_nonneg
    innerT_diag := by
      intro x
      simpa [harmonicCharSpectralGapData] using P.parseval_T x
    innerSelf_diag := by
      intro x
      simpa [harmonicCharSpectralGapData] using P.parseval_self x
    eigen_le_sep := ?_
  }
  intro x _hx i
  change CReal.RCle
    (rcScaleResidualPlus.RCscale
      (qpow (harmW k) (c4 (i.val + 1))) (P.coeffSq x i))
    (rcScaleResidualPlus.RCscale
      (lamPW (harmW k) (Ncut k) 1) (P.coeffSq x i))
  apply rscale_mono
  · exact Q'.le_trans' _ _ _
      (casimir_qpow_le (harmW_nonneg k) (harmW_le_one k) i.val)
      (C k).heat_le_fused
  · exact P.coeffSq_nonneg x i

/-- Consequently the existing reflection-positive GNS operator satisfies its
operator-form gap with separator `lamPW` and margin `harmonicMass`. -/
def harmonicCharFormGap
    (C : HarmonicTransferSectorDomination)
    (k : Nat) (t : Q') (ht : (0 : Q') <= t) :
    TransferFormGapResidual (harmonicCharSpectralGapData C k t ht) :=
  (harmonicCharSpectralBridge C k t ht).toFormGapResidual

end YMGap.Continuum.HarmonicTransferOperatorIdentification

#print axioms YMGap.Continuum.HarmonicTransferOperatorIdentification.fundamentalChar_invariant
#print axioms YMGap.Continuum.HarmonicTransferOperatorIdentification.harmonicFused_operator_eigen
#print axioms YMGap.Continuum.HarmonicTransferOperatorIdentification.harmonicMass_eq_fused_operator_gap
#print axioms YMGap.Continuum.HarmonicTransferOperatorIdentification.harmonicFundamental_fused_ne_zero
#print axioms YMGap.Continuum.HarmonicTransferOperatorIdentification.harmonicChar_fundamental_not_fused_zero
#print axioms YMGap.Continuum.HarmonicTransferOperatorIdentification.no_harmonic_zero_positive_rankOne_intertwiner
#print axioms YMGap.Continuum.HarmonicTransferOperatorIdentification.harmonicSectorComparison_zero
#print axioms YMGap.Continuum.HarmonicTransferOperatorIdentification.harmonicSectorComparison_one
#print axioms YMGap.Continuum.HarmonicTransferOperatorIdentification.harmonicW_lt_one
#print axioms YMGap.Continuum.HarmonicTransferOperatorIdentification.harmonicCharLocatedGap
#print axioms YMGap.Continuum.HarmonicTransferOperatorIdentification.harmonicChar_gapMargin_eq
#print axioms YMGap.Continuum.HarmonicTransferOperatorIdentification.harmonicCharSpectralGapData
#print axioms YMGap.Continuum.HarmonicTransferOperatorIdentification.harmonicCharSpectralBridge
#print axioms YMGap.Continuum.HarmonicTransferOperatorIdentification.harmonicCharFormGap
