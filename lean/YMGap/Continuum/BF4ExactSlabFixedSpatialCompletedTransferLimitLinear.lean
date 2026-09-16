/-
# Rational linearity of the actual cutoff-limit Haar transfer

At one explicitly common late cutoff, the original polynomial transfer is
additive and rational homogeneous. The represented cutoff family converges
to its constructed limit on each of the supplied inputs. Three quadratic
comparison hops therefore prove the two linearity laws on the SAME existing
completion and the SAME cutoff-limit map.

Only the already constructed family, its explicit rates and finite-transfer
identities are used. No representatives are chosen from quotient points and
no linearity, stationary law, OS interpretation or spectral hypothesis is
assumed for the limit.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedTransferLimit

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedTransferLimitLinear

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.HamiltonianScalar
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBound
open YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedHaarTransfer
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferLimitFamily
open YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedTransferLimit
open YMGap.Continuum.SU2QuaternionHaarBoundedCompletion

local infix:50 " ≈ " => Q'.eqv

private theorem tiny_budget (epsilon : Q') (he : (0 : Q') < epsilon) :
    treeval (Q'.invSucc (gMod epsilon)) ≤ epsilon :=
  Q'.le_trans' _ _ _ (treeval_le_ten _)
    (gMod_spec epsilon he (gMod epsilon) (Nat.le_refl _))

private theorem four_quarters (epsilon : Q') :
    ((HalfPow.half * (HalfPow.half * epsilon) + HalfPow.half * (HalfPow.half * epsilon)) +
      (HalfPow.half * (HalfPow.half * epsilon) + HalfPow.half * (HalfPow.half * epsilon))) ≈
        epsilon :=
  Q'.eqv_trans _ _ _ (Q'.add_eqv_congr'
    (ExpNeg.two_halves (HalfPow.half * epsilon))
    (ExpNeg.two_halves (HalfPow.half * epsilon))) (ExpNeg.two_halves epsilon)

/-- The constructed representatives respect addition up to the existing null
relation. The common cutoff is computed from the three supplied family rates. -/
theorem limitRep_add_null {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width : Nat) (X Y : CauchyGNS (sliceData width).toGNSData) :
    CauchyNull (sliceData width).toGNSData
      (limitRep hw0 hw1 width ((sliceData width).toGNSData.cAddCauchy X Y))
      ((sliceData width).toGNSData.cAddCauchy
        (limitRep hw0 hw1 width X) (limitRep hw0 hw1 width Y)) := by
  let D := (sliceData width).toGNSData
  let Z := D.cAddCauchy X Y
  intro epsilon he
  let tiny := Q'.invSucc (gMod epsilon)
  have htiny : (0 : Q') < tiny := Q'.invSucc_pos _
  let quarter := HalfPow.half * (HalfPow.half * tiny)
  have hquarter : (0 : Q') < quarter :=
    ExpNeg.half_mul_pos _ (ExpNeg.half_mul_pos tiny htiny)
  let p := max (familyRate hw0 hw1 width Z tiny)
    (max (familyRate hw0 hw1 width X quarter) (familyRate hw0 hw1 width Y quarter))
  obtain ⟨NZ, hNZ⟩ := family_close_at hw0 hw1 width Z tiny htiny p (Nat.le_max_left _ _)
  obtain ⟨NX, hNX⟩ := family_close_at hw0 hw1 width X quarter hquarter p
    (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _))
  obtain ⟨NY, hNY⟩ := family_close_at hw0 hw1 width Y quarter hquarter p
    (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))
  refine ⟨max NZ (max NX NY), fun n hn => ?_⟩
  have hz := hNZ n (Nat.le_trans (Nat.le_max_left _ _) hn)
  have hx := hNX n (Nat.le_trans
    (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) hn)
  have hy := hNY n (Nat.le_trans
    (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) hn)
  let a := ((cutoffFamily hw0 hw1 width Z).pt p).seq n
  let b := D.add (((cutoffFamily hw0 hw1 width X).pt p).seq n)
    (((cutoffFamily hw0 hw1 width Y).pt p).seq n)
  have hmiddle : D.rad a b :=
    rad_of_veq D (transferStep_add w (lateCutoff w p) width (X.seq n).val (Y.seq n).val)
  have hlast : D.distSqQ b
      (D.add ((limitRep hw0 hw1 width X).seq n) ((limitRep hw0 hw1 width Y).seq n)) ≤ tiny :=
    Q'.le_trans' _ _ _
      (D.distSqQ_add_le (((cutoffFamily hw0 hw1 width X).pt p).seq n)
        (((cutoffFamily hw0 hw1 width Y).pt p).seq n)
        ((limitRep hw0 hw1 width X).seq n) ((limitRep hw0 hw1 width Y).seq n))
      (Q'.le_trans' _ _ _
        (Q'.add_le_add (Q'.add_le_add hx hx) (Q'.add_le_add hy hy))
        (Q'.le_of_eqv (four_quarters tiny)))
  exact Q'.le_trans' _ _ _
    (D.quad3 ((limitRep hw0 hw1 width Z).seq n) a b
      (D.add ((limitRep hw0 hw1 width X).seq n) ((limitRep hw0 hw1 width Y).seq n)) tiny
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv (D.distSqQ_comm _ _)) hz)
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv hmiddle) (Q'.le_of_lt htiny)) hlast)
    (tiny_budget epsilon he)

/-- Rational scaling uses a concrete positive tolerance even when the scalar
is zero or negative; no reciprocal of the scalar is needed. -/
theorem limitRep_smul_null {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width : Nat) (c : Q') (X : CauchyGNS (sliceData width).toGNSData) :
    CauchyNull (sliceData width).toGNSData
      (limitRep hw0 hw1 width ((sliceData width).cSmulCauchy c X))
      ((sliceData width).cSmulCauchy c (limitRep hw0 hw1 width X)) := by
  let D := (sliceData width).toGNSData
  let Z := (sliceData width).cSmulCauchy c X
  intro epsilon he
  let tiny := Q'.invSucc (gMod epsilon)
  have htiny : (0 : Q') < tiny := Q'.invSucc_pos _
  let delta := tolerance c tiny
  have hdelta : (0 : Q') < delta := tolerance_positive c tiny htiny
  let p := max (familyRate hw0 hw1 width Z tiny) (familyRate hw0 hw1 width X delta)
  obtain ⟨NZ, hNZ⟩ := family_close_at hw0 hw1 width Z tiny htiny p (Nat.le_max_left _ _)
  obtain ⟨NX, hNX⟩ := family_close_at hw0 hw1 width X delta hdelta p (Nat.le_max_right _ _)
  refine ⟨max NZ NX, fun n hn => ?_⟩
  have hz := hNZ n (Nat.le_trans (Nat.le_max_left _ _) hn)
  have hx := hNX n (Nat.le_trans (Nat.le_max_right _ _) hn)
  let a := ((cutoffFamily hw0 hw1 width Z).pt p).seq n
  let b := D.smul c (((cutoffFamily hw0 hw1 width X).pt p).seq n)
  have hmiddle : D.rad a b :=
    rad_of_veq D (transferStep_smul w (lateCutoff w p) width c (X.seq n).val)
  have hc : (0 : Q') ≤ c*c := SumOfSquares.q_mul_self_nonneg c
  have hlast : D.distSqQ b (D.smul c ((limitRep hw0 hw1 width X).seq n)) ≤ tiny :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv ((sliceData width).distSqQ_smul c
        (((cutoffFamily hw0 hw1 width X).pt p).seq n) ((limitRep hw0 hw1 width X).seq n)))
      (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ (c*c) hx hc)
        (ExpNeg.mul_le_of_mul_invSucc_toNat (c*c) tiny hc (Q'.le_of_lt htiny)))
  exact Q'.le_trans' _ _ _
    (D.quad3 ((limitRep hw0 hw1 width Z).seq n) a b
      (D.smul c ((limitRep hw0 hw1 width X).seq n)) tiny
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv (D.distSqQ_comm _ _)) hz)
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv hmiddle) (Q'.le_of_lt htiny)) hlast)
    (tiny_budget epsilon he)

/-- The actual cutoff-limit operator is additive on all completion points. -/
theorem completedLimit_add {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width : Nat) (x y : GNSCompletionSpace (sliceData width).toGNSData) :
    completedLimit hw0 hw1 width ((sliceData width).toGNSData.cAdd x y) =
      (sliceData width).toGNSData.cAdd
        (completedLimit hw0 hw1 width x) (completedLimit hw0 hw1 width y) := by
  refine Quotient.inductionOn₂ x y ?_
  intro X Y
  exact Quotient.sound (limitRep_add_null hw0 hw1 width X Y)

/-- The same actual cutoff limit is homogeneous for every rational scalar. -/
theorem completedLimit_smul {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width : Nat) (c : Q') (x : GNSCompletionSpace (sliceData width).toGNSData) :
    completedLimit hw0 hw1 width ((sliceData width).cSmul c x) =
      (sliceData width).cSmul c (completedLimit hw0 hw1 width x) := by
  refine Quotient.inductionOn x ?_
  intro X
  exact Quotient.sound (limitRep_smul_null hw0 hw1 width c X)

end YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedTransferLimitLinear

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedTransferLimitLinear.limitRep_add_null
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedTransferLimitLinear.limitRep_smul_null
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedTransferLimitLinear.completedLimit_add
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedTransferLimitLinear.completedLimit_smul
