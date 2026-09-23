/-
# Iterated completed contraction for the finite ordinary-Haar SU(2) carrier

The centered ordinary-Haar completion already has a descended product-map
transfer and a finite squared-distance estimate.  This module passes that
estimate through the genuine `CReal` completion, then iterates it.  The
resulting decay is a fixed-(n,w,K,ids) statement; it is not a beta/spacing
uniform OS gap or a continuum theorem.
-/

import YMGap.Continuum.SU2QuaternionFiniteHaarMidpointFormRate

namespace YMGap.Continuum.SU2QuaternionFiniteHaarCompletedTransferContraction

set_option autoImplicit false
set_option maxHeartbeats 8000000

open YMGap.Constructive
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionFiniteHaarGNSCarrier
open YMGap.Continuum.SU2QuaternionFiniteHaarProductMapQuotient
open YMGap.Continuum.SU2QuaternionFiniteHaarMidpointFormRate
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.SU2HeatCutoffCasimirBound
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionProductHeatDualForm
open YMGap.Continuum.SU2QuaternionRelativeHeatContraction

local infix:50 " ≈ " => Q'.eqv

/-! ## One completed norm step -/

/-- The finite centered squared-distance estimate survives as a completed
`CReal.RC` squared-norm estimate for the descended centered transfer. -/
theorem centeredCompletionTransfer_norm_sq_le
    (n : Nat) {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K : Nat) (hK : headCutoff w ≤ K)
    (ids : List Nat) (hnodup : ids.Nodup)
    (hids : ∀ i, i ∈ ids → i < n)
    (x : CenteredCompletionSpace n) :
    CReal.RCle
      (centeredCompletionInner n
        (centeredCompletionTransfer n hw0 hw1 K hK ids hnodup hids x)
        (centeredCompletionTransfer n hw0 hw1 K hK ids hnodup hids x))
      (CReal.RCscale (squaredHeatRate w)
        (centeredCompletionInner n x x)) := by
  refine Quotient.inductionOn x ?_
  intro X
  let D := finiteHaarGNSData n
  let Y : CauchyGNS D :=
    productMap_centeredCauchy n hw0 hw1 K hK ids hnodup hids X
  have hleft : CReal.ConvergesTo
      (fun k => CReal.ofQ' (D.cInnerSeq Y Y k))
      (D.cinnerRep Y Y) :=
    CReal.convergesTo_ofQ'CauchySeq _ _
  have hright : CReal.ConvergesTo
      (fun k => CReal.mul (CReal.ofQ' (squaredHeatRate w))
        (CReal.ofQ' (D.cInnerSeq X.seq X.seq k)))
      (CReal.mul (CReal.ofQ' (squaredHeatRate w))
        (D.cinnerRep X.seq X.seq)) := by
    have hconst : CReal.ConvergesTo
        (fun _ : Nat => CReal.ofQ' (squaredHeatRate w))
        (CReal.ofQ' (squaredHeatRate w)) := by
      simpa using
        (CReal.convergesTo_self
          (CReal.ofQ' (squaredHeatRate w)))
    have hnorm : CReal.ConvergesTo
        (fun k => CReal.ofQ' (D.cInnerSeq X.seq X.seq k))
        (D.cinnerRep X.seq X.seq) :=
      CReal.convergesTo_ofQ'CauchySeq _ _
    exact CReal.convergesTo_mul_general hconst hnorm
  apply CReal.leEv_of_convergesTo_le hleft hright
  intro k
  apply CReal.leEv_ofQ'_of_approx_ge
  intro j
  have hfinite := productMapQuotient_centered_square_bound
    n hw0 hw1 K hK ids hnodup hids (X.seq.seq k)
    (X.centered k)
  change D.cInnerSeq Y Y k ≤
    squaredHeatRate w * D.cInnerSeq X.seq X.seq k
  exact hfinite

/-! ## Completed transfer powers -/

/-- The literal iterated completed centered transfer. -/
def centeredCompletionTransferPower
    (n : Nat) {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K : Nat) (hK : headCutoff w ≤ K)
    (ids : List Nat) (hnodup : ids.Nodup)
    (hids : ∀ i, i ∈ ids → i < n) :
    Nat → CenteredCompletionSpace n → CenteredCompletionSpace n
  | 0, x => x
  | k + 1, x => centeredCompletionTransfer n hw0 hw1 K hK ids hnodup hids
      (centeredCompletionTransferPower n hw0 hw1 K hK ids hnodup hids k x)

theorem centeredCompletionTransferPower_zero
    (n : Nat) {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K : Nat) (hK : headCutoff w ≤ K)
    (ids : List Nat) (hnodup : ids.Nodup)
    (hids : ∀ i, i ∈ ids → i < n)
    (x : CenteredCompletionSpace n) :
    centeredCompletionTransferPower n hw0 hw1 K hK ids hnodup hids 0 x = x := rfl

theorem centeredCompletionTransferPower_succ
    (n : Nat) {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K : Nat) (hK : headCutoff w ≤ K)
    (ids : List Nat) (hnodup : ids.Nodup)
    (hids : ∀ i, i ∈ ids → i < n)
    (k : Nat) (x : CenteredCompletionSpace n) :
    centeredCompletionTransferPower n hw0 hw1 K hK ids hnodup hids (k + 1) x =
      centeredCompletionTransfer n hw0 hw1 K hK ids hnodup hids
        (centeredCompletionTransferPower n hw0 hw1 K hK ids hnodup hids k x) := rfl

/-- Nonnegativity of the squared norm in the centered completion. -/
private theorem centeredCompletionInner_self_nonneg
    (n : Nat) (x : CenteredCompletionSpace n) :
    CReal.RCnonneg (centeredCompletionInner n x x) := by
  refine Quotient.inductionOn x ?_
  intro X
  unfold centeredCompletionInner
  change CReal.leEv CReal.czero
    ((finiteHaarGNSData n).cinnerRep X.seq X.seq)
  apply CReal.leEv_ofQ'_of_approx_ge
  intro k
  let m : Nat := CReal.QMhat
    ((finiteHaarGNSData n).cInnerSeq X.seq X.seq)
    ((finiteHaarGNSData n).cInnerQCauchy X.seq X.seq) k
  change (0 : Q') ≤
    (finiteHaarGNSData n).cInnerSeq X.seq X.seq m
  change (0 : Q') ≤ finiteHaarPair n
    (X.seq.seq m).val (X.seq.seq m).val
  exact finiteHaarPair_nonnegative n (X.seq.seq m).val (X.seq.seq m).property

/-- Iterated completed squared-norm decay at the explicit finite rate. -/
theorem centeredCompletionTransferPower_norm_sq_decay
    (n : Nat) {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K : Nat) (hK : headCutoff w ≤ K)
    (ids : List Nat) (hnodup : ids.Nodup)
    (hids : ∀ i, i ∈ ids → i < n)
    (k : Nat) (x : CenteredCompletionSpace n) :
    CReal.RCle
      (centeredCompletionInner n
        (centeredCompletionTransferPower n hw0 hw1 K hK ids hnodup hids k x)
        (centeredCompletionTransferPower n hw0 hw1 K hK ids hnodup hids k x))
      (CReal.RCscale ((squaredHeatRate w) ^ k)
        (centeredCompletionInner n x x)) := by
  induction k with
  | zero =>
      rw [centeredCompletionTransferPower_zero, Q'.pow_zero,
        CReal.RCscale_one]
      exact CReal.RCle_refl _
  | succ k ih =>
      rw [centeredCompletionTransferPower_succ]
      have hstep := centeredCompletionTransfer_norm_sq_le
        n hw0 hw1 K hK ids hnodup hids
        (centeredCompletionTransferPower n hw0 hw1 K hK ids hnodup hids k x)
      refine CReal.RCle_trans hstep ?_
      have hrateNonnegative : (0 : Q') ≤ squaredHeatRate w :=
        squaredHeatRate_nonnegative hw0 hw1
      have hscaled := CReal.RCscale_mono hrateNonnegative ih
      refine CReal.RCle_trans hscaled ?_
      rw [CReal.RCscale_RCscale]
      exact CReal.RCle_refl _

/-! ## Same-object consequence -/

private theorem cReal_const_product_le
    {a b c d : Q'} (h : a * b ≤ c * d) :
    CReal.leEv
      (CReal.mul (CReal.ofQ' a) (CReal.ofQ' b))
      (CReal.mul (CReal.ofQ' c) (CReal.ofQ' d)) := by
  intro ε hε
  refine ⟨0, fun n _ => ?_⟩
  change a * b ≤ c * d + ε
  exact Q'.le_trans' _ _ _ h
    (Q'.add_le_self_of_nonneg (c * d) ε (Q'.le_of_lt hε))

private theorem centeredCompletionInner_cauchy_schwarz
    (n : Nat) (x y : CenteredCompletionSpace n) :
    CReal.RCle
      (CReal.RCmul (centeredCompletionInner n x y)
        (centeredCompletionInner n x y))
      (CReal.RCmul (centeredCompletionInner n x x)
        (centeredCompletionInner n y y)) := by
  refine Quotient.inductionOn₂ x y ?_
  intro X Y
  let D := finiteHaarGNSData n
  apply CReal.leEv_of_convergesTo_le
    (CReal.convergesTo_mul_general
      (CReal.convergesTo_ofQ'CauchySeq
        (D.cInnerSeq X.seq Y.seq) (D.cInnerQCauchy X.seq Y.seq))
      (CReal.convergesTo_ofQ'CauchySeq
        (D.cInnerSeq X.seq Y.seq) (D.cInnerQCauchy X.seq Y.seq)))
    (CReal.convergesTo_mul_general
      (CReal.convergesTo_ofQ'CauchySeq
        (D.cInnerSeq X.seq X.seq) (D.cInnerQCauchy X.seq X.seq))
      (CReal.convergesTo_ofQ'CauchySeq
        (D.cInnerSeq Y.seq Y.seq) (D.cInnerQCauchy Y.seq Y.seq)))
  intro k
  apply cReal_const_product_le
  change D.cInnerSeq X.seq Y.seq
      k * D.cInnerSeq X.seq Y.seq k ≤
    D.cInnerSeq X.seq X.seq k * D.cInnerSeq Y.seq Y.seq k
  exact finiteHaar_cauchySchwarz n
    (X.seq.seq k).val (Y.seq.seq k).val
    (X.seq.seq k).property (Y.seq.seq k).property

private theorem RCmul_mono_nonnegative_right
    {left right factor : CReal.RC}
    (hle : CReal.RCle left right)
    (hfactor : CReal.RCnonneg factor) :
    CReal.RCle
      (CReal.RCmul left factor)
      (CReal.RCmul right factor) := by
  rw [CReal.RCmul_comm left factor, CReal.RCmul_comm right factor]
  revert hfactor hle
  refine Quotient.inductionOn₃ factor left right ?_
  intro F L R hle' hfactor'
  change CReal.leEv CReal.czero F at hfactor'
  rw [CReal.RCle_mk] at hle'
  exact CReal.leEv_mul_nonneg_left hfactor' hle'

/-- The completed same-object moment decays at the squared finite rate. -/
theorem centeredCompletionTransferPower_autocorrelation_sq_decay
    (n : Nat) {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K : Nat) (hK : headCutoff w ≤ K)
    (ids : List Nat) (hnodup : ids.Nodup)
    (hids : ∀ i, i ∈ ids → i < n)
    (k : Nat) (x : CenteredCompletionSpace n) :
    CReal.RCle
      (CReal.RCmul
        (centeredCompletionInner n x
          (centeredCompletionTransferPower n hw0 hw1 K hK ids hnodup hids k x))
        (centeredCompletionInner n x
          (centeredCompletionTransferPower n hw0 hw1 K hK ids hnodup hids k x)))
      (CReal.RCmul
        (CReal.RCscale ((squaredHeatRate w) ^ k)
          (centeredCompletionInner n x x))
        (centeredCompletionInner n x x)) := by
  have hcs := centeredCompletionInner_cauchy_schwarz n x
    (centeredCompletionTransferPower n hw0 hw1 K hK ids hnodup hids k x)
  have hnorm := centeredCompletionTransferPower_norm_sq_decay
    n hw0 hw1 K hK ids hnodup hids k x
  have hscaled := RCmul_mono_nonnegative_right hnorm
    (centeredCompletionInner_self_nonneg n x)
  rw [CReal.RCmul_comm
    (centeredCompletionInner n x x)
    (centeredCompletionInner n
      (centeredCompletionTransferPower n hw0 hw1 K hK ids hnodup hids k x)
      (centeredCompletionTransferPower n hw0 hw1 K hK ids hnodup hids k x))] at hcs
  exact CReal.RCle_trans hcs hscaled

#print axioms YMGap.Continuum.SU2QuaternionFiniteHaarCompletedTransferContraction.centeredCompletionTransfer_norm_sq_le
#print axioms YMGap.Continuum.SU2QuaternionFiniteHaarCompletedTransferContraction.centeredCompletionTransferPower
#print axioms YMGap.Continuum.SU2QuaternionFiniteHaarCompletedTransferContraction.centeredCompletionTransferPower_norm_sq_decay
#print axioms YMGap.Continuum.SU2QuaternionFiniteHaarCompletedTransferContraction.centeredCompletionTransferPower_autocorrelation_sq_decay

end YMGap.Continuum.SU2QuaternionFiniteHaarCompletedTransferContraction
