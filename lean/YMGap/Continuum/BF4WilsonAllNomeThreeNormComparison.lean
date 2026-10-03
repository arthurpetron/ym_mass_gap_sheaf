/-
# Three homogeneous costs on the ORIGINAL all-nome Wilson completion

Polarization of the actual norms of x, x+T(j)x and x-T(j)x reduces
normalized cross-scale comparison to three relative quadratic estimates.
The two theories retain their own completed carriers, action, time and
centering; no width inclusion is used. A common nonnegative real scale is
allowed, and no uniform positive raw norm floor is assumed.

The relative estimates are explicit analytic inputs, NOT constructed here.
This supplies neither a physical family nor a continuum limit or mass gap.
-/

import YMGap.Continuum.RCThreeNormProjectiveComparison
import YMGap.Continuum.BF4WilsonAllNomeCompletedPairingContinuity
import YMGap.Continuum.BF4WilsonAllNomeDyadicNormalizedBondAnchor

namespace YMGap.Continuum.BF4WilsonAllNomeThreeNormComparison

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser (PolyExpr poly_identity_of_normal_eq)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4WilsonAllNomeLinear
open YMGap.Continuum.BF4WilsonAllNomeBilinearTime
open YMGap.Continuum.BF4WilsonAllNomeCompletedPairingContinuity
  (completedInner_sub_left completedInner_sub_right)
open YMGap.Continuum.RCSignedPairBudget (scale_congr)
open YMGap.Continuum.RCThreeNormProjectiveComparison
open YMGap.Continuum.BF4DyadicWilsonSquare (side)
open YMGap.Continuum.BF4WilsonAllNomeDyadicUnitExcitation
open YMGap.Continuum.BF4WilsonAllNomeDyadicNormalizedBondAnchor

local notation "Rq" q:arg => Quotient.mk crealSetoid (ofQ' q)

private theorem rc_mul_assoc (a b c : RC) :
    RCmul (RCmul a b) c = RCmul a (RCmul b c) := by
  refine Quotient.inductionOn₃ a b c ?_
  exact fun A B C => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.mul_assoc_eqv (A.approx n) (B.approx n) (C.approx n)))

private theorem rc_mul_one (a : RC) : RCmul a (Rq 1) = a := by
  refine Quotient.inductionOn a ?_
  exact fun A => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.mul_one_eqv (A.approx n)))

private theorem rc_mul_scale (q : Q') (a b : RC) :
    RCmul (RCscale q a) b = RCscale q (RCmul a b) := by
  refine Quotient.inductionOn₂ a b ?_
  exact fun A B => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.mul_assoc_eqv q (A.approx n) (B.approx n)))

private theorem rc_scale_rational_one (q : Q') : RCscale q (Rq 1) = Rq q :=
  Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.mul_one_eqv q))

private theorem rc_product_shuffle (a b c d : RC) :
    RCmul (RCmul a b) (RCmul c d) = RCmul (RCmul c a) (RCmul d b) := by
  refine Quotient.inductionOn₃ a b c ?_
  intro A B C
  refine Quotient.inductionOn d ?_
  intro D
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
      (.mul (.mul (.var 2) (.var 0)) (.mul (.var 3) (.var 1)))
      (by decide) (fun
        | 0 => A.approx n
        | 1 => B.approx n
        | 2 => C.approx n
        | _ => D.approx n)))

private theorem rc_add_zero (a : RC) : RCadd a RCzero = a := by
  refine Quotient.inductionOn a ?_
  exact fun A => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.eqv_of_eq (Q'.add_zero' (A.approx n))))

private theorem rc_scale_one (a : RC) : RCscale 1 a = a := by
  refine Quotient.inductionOn a ?_
  exact fun A => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.one_mul_eqv (A.approx n)))

private theorem rc_twice (a : RC) : RCadd a a = RCscale 2 a := by
  refine Quotient.inductionOn a ?_
  exact fun A => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => poly_identity_of_normal_eq (.add (.var 0) (.var 0))
      (.mul (.const 2) (.var 0)) (by decide) (fun _ => A.approx n)))

private theorem scalar_diagonals (a c m : RC) :
    let p := RCadd (RCadd a c) (RCadd c m)
    let q := RCsub (RCsub a c) (RCsub c m)
    RCscale 4 c = RCsub p q ∧
    RCadd p q = RCscale 2 (RCadd a m) ∧
    RCadd (RCscale 2 c) q = RCadd a m ∧
    RCadd (RCscale 2 (RCneg c)) p = RCadd a m := by
  refine Quotient.inductionOn₃ a c m ?_
  intro A C M
  let plus : PolyExpr := .add (.add (.var 0) (.var 1)) (.add (.var 1) (.var 2))
  let minus : PolyExpr := .add (.add (.var 0) (.neg (.var 1)))
    (.neg (.add (.var 1) (.neg (.var 2))))
  let env := fun (n i : Nat) => match i with
    | 0 => A.approx n
    | 1 => C.approx n
    | _ => M.approx n
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
      poly_identity_of_normal_eq (.mul (.const 4) (.var 1))
        (.add plus (.neg minus)) (by decide) (env n)))
  · exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
      poly_identity_of_normal_eq (.add plus minus)
        (.mul (.const 2) (.add (.var 0) (.var 2))) (by decide) (env n)))
  · exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
      poly_identity_of_normal_eq (.add (.mul (.const 2) (.var 1)) minus)
        (.add (.var 0) (.var 2)) (by decide) (env n)))
  · exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
      poly_identity_of_normal_eq (.add (.mul (.const 2) (.neg (.var 1))) plus)
        (.add (.var 0) (.var 2)) (by decide) (env n)))

section OneTheory

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "T" => completedTime hw0 hw1

def normSq (x : V) : RC := B x x

def response (j : Nat) (x : V) : RC := B x (T j x)

def plusSq (j : Nat) (x : V) : RC :=
  let p := completedAdd hw0 hw1 x (T j x)
  B p p

def minusSq (j : Nat) (x : V) : RC :=
  let q := completedSub hw0 hw1 x (T j x)
  B q q

private theorem actual_diagonals (j : Nat) (x : V) :
    RCscale 4 (response hw0 hw1 j x) =
      RCsub (plusSq hw0 hw1 j x) (minusSq hw0 hw1 j x) ∧
    RCadd (plusSq hw0 hw1 j x) (minusSq hw0 hw1 j x) =
      RCscale 2 (RCadd (normSq hw0 hw1 x) (normSq hw0 hw1 (T j x))) ∧
    RCadd (RCscale 2 (response hw0 hw1 j x)) (minusSq hw0 hw1 j x) =
      RCadd (normSq hw0 hw1 x) (normSq hw0 hw1 (T j x)) ∧
    RCadd (RCscale 2 (RCneg (response hw0 hw1 j x))) (plusSq hw0 hw1 j x) =
      RCadd (normSq hw0 hw1 x) (normSq hw0 hw1 (T j x)) := by
  unfold response plusSq minusSq normSq
  simp only [completedInner_add_left, completedInner_add_right,
    completedInner_sub_left, completedInner_sub_right,
    completedInner_symm hw0 hw1 (T j x) x]
  exact scalar_diagonals (B x x) (B x (T j x)) (B (T j x) (T j x))

/-- Exact polarization on this theory's OWN actual completed form. -/
theorem response_polarization (j : Nat) (x : V) :
    RCscale 4 (response hw0 hw1 j x) =
      RCsub (plusSq hw0 hw1 j x) (minusSq hw0 hw1 j x) :=
  (actual_diagonals hw0 hw1 j x).1

/-- The sum of both actual diagonals costs at most four anchor norms. -/
theorem plus_minus_sum_bound (j : Nat) (x : V) :
    RCle (RCadd (plusSq hw0 hw1 j x) (minusSq hw0 hw1 j x))
      (RCscale 4 (normSq hw0 hw1 x)) := by
  rw [(actual_diagonals hw0 hw1 j x).2.1]
  have h := RCscale_mono (by decide : (0 : Q') ≤ 2)
    (RCadd_le_add (RCle_refl (B x x)) (completedInner_time_contraction hw0 hw1 j x))
  rw [rc_twice, RCscale_RCscale,
    scale_congr (by decide : Q'.eqv ((2 : Q')*2) 4)] at h
  exact h

/-- Both signs, including a zero anchor: no real square root or division. -/
theorem response_signed_bound (j : Nat) (x : V) :
    RCle (response hw0 hw1 j x) (normSq hw0 hw1 x) ∧
    RCle (RCneg (response hw0 hw1 j x)) (normSq hw0 hw1 x) := by
  have hnm := RCadd_le_add (RCle_refl (B x x))
    (completedInner_time_contraction hw0 hw1 j x)
  rw [rc_twice] at hnm
  constructor
  · have h := RCadd_le_add (RCle_refl (RCscale 2 (response hw0 hw1 j x)))
      (completedInner_nonnegative hw0 hw1 (completedSub hw0 hw1 x (T j x)))
    rw [rc_add_zero] at h
    change RCle (RCscale 2 (response hw0 hw1 j x))
      (RCadd (RCscale 2 (response hw0 hw1 j x)) (minusSq hw0 hw1 j x)) at h
    rw [(actual_diagonals hw0 hw1 j x).2.2.1] at h
    have hh := RCscale_mono HalfPow.half_nonneg (RCle_trans h hnm)
    simpa only [RCscale_RCscale,
      scale_congr (by decide : Q'.eqv (HalfPow.half*2) 1), rc_scale_one] using hh
  · have h := RCadd_le_add
      (RCle_refl (RCscale 2 (RCneg (response hw0 hw1 j x))))
      (completedInner_nonnegative hw0 hw1 (completedAdd hw0 hw1 x (T j x)))
    rw [rc_add_zero] at h
    change RCle (RCscale 2 (RCneg (response hw0 hw1 j x)))
      (RCadd (RCscale 2 (RCneg (response hw0 hw1 j x))) (plusSq hw0 hw1 j x)) at h
    rw [(actual_diagonals hw0 hw1 j x).2.2.2] at h
    have hh := RCscale_mono HalfPow.half_nonneg (RCle_trans h hnm)
    simpa only [RCscale_RCscale,
      scale_congr (by decide : Q'.eqv (HalfPow.half*2) 1), rc_scale_one] using hh

/-- The EXISTING original positive-time unit excitation, not a new state. -/
def dyadicAnchor (scale : Nat) (hwidth : side scale < width) : V :=
  T (side scale) (dyadicUnitExcitation hw0 hw1 scale width hwidth).val

theorem dyadicAnchor_vacuum (scale : Nat) (hwidth : side scale < width) :
    B (unitState hw0 hw1 width) (dyadicAnchor hw0 hw1 scale hwidth) = RCzero :=
  completedTime_preserves_vacuumComplement hw0 hw1 _ _
    (dyadicUnitExcitation hw0 hw1 scale width hwidth).property

theorem dyadicAnchor_norm_pin (scale : Nat) (hwidth : side scale < width) :
    normSq hw0 hw1 (dyadicAnchor hw0 hw1 scale hwidth) =
      Quotient.mk crealSetoid (anchorNorm hw0 hw1 scale width hwidth) := by
  unfold normSq dyadicAnchor anchorNorm
  rw [completedInner_time_sum, show side scale+side scale=2*side scale by omega]
  exact dyadicUnitResponse_pin hw0 hw1 scale width hwidth _

theorem dyadicAnchor_response_pin (scale : Nat) (hwidth : side scale < width)
    (j : Nat) : response hw0 hw1 j (dyadicAnchor hw0 hw1 scale hwidth) =
      Quotient.mk crealSetoid (dyadicUnitResponse hw0 hw1 scale width hwidth (2*side scale+j)) := by
  unfold response dyadicAnchor
  rw [← completedTime_add, completedInner_time_sum,
    show side scale+(j+side scale)=2*side scale+j by omega]
  exact dyadicUnitResponse_pin hw0 hw1 scale width hwidth _

/-- Squared EXISTING computed inverse-root scalar, with no new inverse. -/
def normalizerSquare (scale : Nat) (hwidth : side scale < width) : RC :=
  let a := Quotient.mk crealSetoid (anchorNormalizer hw0 hw1 scale width hwidth)
  RCmul a a

theorem normalizerSquare_nonnegative (scale : Nat) (hwidth : side scale < width) :
    RCnonneg (normalizerSquare hw0 hw1 scale hwidth) := by
  unfold normalizerSquare
  exact ScaledGNSCompletionEstimates.square_nonnegative
    (Quotient.mk crealSetoid (anchorNormalizer hw0 hw1 scale width hwidth))

theorem normalizerSquare_norm (scale : Nat) (hwidth : side scale < width) :
    RCmul (normalizerSquare hw0 hw1 scale hwidth)
      (normSq hw0 hw1 (dyadicAnchor hw0 hw1 scale hwidth)) = Rq 1 := by
  unfold normalizerSquare
  rw [rc_mul_assoc, dyadicAnchor_norm_pin]
  exact Quotient.sound (anchorNormalizer_normalizes hw0 hw1 scale width hwidth)

theorem normalizerSquare_response_pin (scale : Nat) (hwidth : side scale < width)
    (j : Nat) : RCmul (normalizerSquare hw0 hw1 scale hwidth)
      (response hw0 hw1 j (dyadicAnchor hw0 hw1 scale hwidth)) =
      Quotient.mk crealSetoid (normalizedAnchorResponse hw0 hw1 scale width hwidth j) := by
  unfold normalizerSquare
  rw [rc_mul_assoc, dyadicAnchor_response_pin]
  rfl

end OneTheory

private theorem normalize_cleared (delta : Q') (Nk Nl Ck Cl bk bl : RC)
    (hbk : RCnonneg bk) (hbl : RCnonneg bl)
    (hkn : RCmul bk Nk = Rq 1) (hln : RCmul bl Nl = Rq 1)
    (h : twoSided (RCscale (4*delta) (RCmul Nk Nl))
      (RCmul Ck Nl) (RCmul Cl Nk)) :
    twoSided (Rq (4*delta)) (RCmul bk Ck) (RCmul bl Cl) := by
  have hf : RCnonneg (RCmul bk bl) := by
    refine Quotient.inductionOn₂ bk bl ?_ hbk hbl
    exact fun A B hA hB => CReal.mul_nonneg hA hB
  have hs : twoSided
      (RCmul (RCscale (4*delta) (RCmul Nk Nl)) (RCmul bk bl))
      (RCmul (RCmul Ck Nl) (RCmul bk bl))
      (RCmul (RCmul Cl Nk) (RCmul bk bl)) := by
    constructor
    · simpa only [RCBilinearDifference.mul_sub] using
        ScaledGNSCompletionEstimates.mul_mono_right hf h.1
    · simpa only [RCBilinearDifference.mul_sub] using
        ScaledGNSCompletionEstimates.mul_mono_right hf h.2
  have hb : RCmul (RCscale (4*delta) (RCmul Nk Nl)) (RCmul bk bl) = Rq (4*delta) := by
    rw [rc_mul_scale, rc_product_shuffle, hkn, hln, rc_mul_one, rc_scale_rational_one]
  have hk : RCmul (RCmul Ck Nl) (RCmul bk bl) = RCmul bk Ck := by
    rw [rc_product_shuffle, hln, rc_mul_one]
  have hl : RCmul (RCmul Cl Nk) (RCmul bk bl) = RCmul bl Cl := by
    rw [RCmul_comm bk bl, rc_product_shuffle, hkn, rc_mul_one]
  simpa only [hb, hk, hl] using hs

section TwoTheories

variable {wk wl : Q'} (hk0 : (0 : Q') < wk) (hk1 : wk < (1 : Q'))
  (hl0 : (0 : Q') < wl) (hl1 : wl < (1 : Q')) {widthk widthl : Nat}

/-- THREE supplied relative costs, with original carriers kept separate,
give BOTH cleared normalized response errors. No raw norm floor is used. -/
theorem three_norm_response_compare
    (xk : Completion hk0 hk1 widthk) (xl : Completion hl0 hl1 widthl)
    (jk jl : Nat) (delta : Q') (lambda : RC)
    (hd0 : (0 : Q') ≤ delta) (hdhalf : delta ≤ HalfPow.half)
    (hlambda : RCnonneg lambda)
    (hN : twoSided (RCscale delta (RCmul lambda (normSq hl0 hl1 xl)))
      (normSq hk0 hk1 xk) (RCmul lambda (normSq hl0 hl1 xl)))
    (hplus : twoSided (RCscale delta (RCmul lambda (plusSq hl0 hl1 jl xl)))
      (plusSq hk0 hk1 jk xk) (RCmul lambda (plusSq hl0 hl1 jl xl)))
    (hminus : twoSided (RCscale delta (RCmul lambda (minusSq hl0 hl1 jl xl)))
      (minusSq hk0 hk1 jk xk) (RCmul lambda (minusSq hl0 hl1 jl xl))) :
    twoSided (RCscale (4*delta) (RCmul (normSq hk0 hk1 xk) (normSq hl0 hl1 xl)))
      (RCmul (response hk0 hk1 jk xk) (normSq hl0 hl1 xl))
      (RCmul (response hl0 hl1 jl xl) (normSq hk0 hk1 xk)) := by
  exact three_norm_projective_compare delta lambda
    (normSq hk0 hk1 xk) (normSq hl0 hl1 xl)
    (response hk0 hk1 jk xk) (response hl0 hl1 jl xl)
    (plusSq hk0 hk1 jk xk) (minusSq hk0 hk1 jk xk)
    (plusSq hl0 hl1 jl xl) (minusSq hl0 hl1 jl xl)
    hd0 hdhalf hlambda (completedInner_nonnegative hl0 hl1 xl)
    hN hplus hminus (response_polarization hk0 hk1 jk xk)
    (response_polarization hl0 hl1 jl xl) (plus_minus_sum_bound hl0 hl1 jl xl)
    (response_signed_bound hl0 hl1 jl xl).1 (response_signed_bound hl0 hl1 jl xl).2

/-- On the ACTUAL constructed dyadic anchors, the three relative costs
give BOTH absolute normalized-response errors. Existing parameter-dependent
normalizers cancel; no uniform inverse or raw norm floor is assumed. -/
theorem dyadic_normalized_response_compare
    (scalek scalel : Nat) (hwidthk : side scalek < widthk) (hwidthl : side scalel < widthl)
    (jk jl : Nat) (delta : Q') (lambda : RC)
    (hd0 : (0 : Q') ≤ delta) (hdhalf : delta ≤ HalfPow.half)
    (hlambda : RCnonneg lambda)
    (hN : twoSided
      (RCscale delta (RCmul lambda (normSq hl0 hl1 (dyadicAnchor hl0 hl1 scalel hwidthl))))
      (normSq hk0 hk1 (dyadicAnchor hk0 hk1 scalek hwidthk))
      (RCmul lambda (normSq hl0 hl1 (dyadicAnchor hl0 hl1 scalel hwidthl))))
    (hplus : twoSided
      (RCscale delta (RCmul lambda (plusSq hl0 hl1 jl (dyadicAnchor hl0 hl1 scalel hwidthl))))
      (plusSq hk0 hk1 jk (dyadicAnchor hk0 hk1 scalek hwidthk))
      (RCmul lambda (plusSq hl0 hl1 jl (dyadicAnchor hl0 hl1 scalel hwidthl))))
    (hminus : twoSided
      (RCscale delta (RCmul lambda (minusSq hl0 hl1 jl (dyadicAnchor hl0 hl1 scalel hwidthl))))
      (minusSq hk0 hk1 jk (dyadicAnchor hk0 hk1 scalek hwidthk))
      (RCmul lambda (minusSq hl0 hl1 jl (dyadicAnchor hl0 hl1 scalel hwidthl)))) :
    twoSided (Rq (4*delta))
      (Quotient.mk crealSetoid (normalizedAnchorResponse hk0 hk1 scalek widthk hwidthk jk))
      (Quotient.mk crealSetoid (normalizedAnchorResponse hl0 hl1 scalel widthl hwidthl jl)) := by
  have hclear := three_norm_response_compare hk0 hk1 hl0 hl1
    (dyadicAnchor hk0 hk1 scalek hwidthk) (dyadicAnchor hl0 hl1 scalel hwidthl)
    jk jl delta lambda hd0 hdhalf hlambda hN hplus hminus
  have hnormalized := normalize_cleared delta _ _ _ _
    (normalizerSquare hk0 hk1 scalek hwidthk) (normalizerSquare hl0 hl1 scalel hwidthl)
    (normalizerSquare_nonnegative hk0 hk1 scalek hwidthk)
    (normalizerSquare_nonnegative hl0 hl1 scalel hwidthl)
    (normalizerSquare_norm hk0 hk1 scalek hwidthk)
    (normalizerSquare_norm hl0 hl1 scalel hwidthl) hclear
  simpa only [normalizerSquare_response_pin] using hnormalized

end TwoTheories

end YMGap.Continuum.BF4WilsonAllNomeThreeNormComparison

#print axioms YMGap.Continuum.BF4WilsonAllNomeThreeNormComparison.normSq
#print axioms YMGap.Continuum.BF4WilsonAllNomeThreeNormComparison.response
#print axioms YMGap.Continuum.BF4WilsonAllNomeThreeNormComparison.plusSq
#print axioms YMGap.Continuum.BF4WilsonAllNomeThreeNormComparison.minusSq
#print axioms YMGap.Continuum.BF4WilsonAllNomeThreeNormComparison.dyadicAnchor
#print axioms YMGap.Continuum.BF4WilsonAllNomeThreeNormComparison.normalizerSquare
#print axioms YMGap.Continuum.BF4WilsonAllNomeThreeNormComparison.response_polarization
#print axioms YMGap.Continuum.BF4WilsonAllNomeThreeNormComparison.plus_minus_sum_bound
#print axioms YMGap.Continuum.BF4WilsonAllNomeThreeNormComparison.response_signed_bound
#print axioms YMGap.Continuum.BF4WilsonAllNomeThreeNormComparison.three_norm_response_compare
#print axioms YMGap.Continuum.BF4WilsonAllNomeThreeNormComparison.dyadicAnchor_vacuum
#print axioms YMGap.Continuum.BF4WilsonAllNomeThreeNormComparison.dyadicAnchor_norm_pin
#print axioms YMGap.Continuum.BF4WilsonAllNomeThreeNormComparison.dyadicAnchor_response_pin
#print axioms YMGap.Continuum.BF4WilsonAllNomeThreeNormComparison.normalizerSquare_nonnegative
#print axioms YMGap.Continuum.BF4WilsonAllNomeThreeNormComparison.normalizerSquare_norm
#print axioms YMGap.Continuum.BF4WilsonAllNomeThreeNormComparison.normalizerSquare_response_pin
#print axioms YMGap.Continuum.BF4WilsonAllNomeThreeNormComparison.dyadic_normalized_response_compare
