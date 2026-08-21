/-
# Outer Cauchy limit for the completed physical BF4 cutoff pairing

For explicit-modulus Cauchy representatives `X` and `Y`, this module proves
that the dense physical pairings `B(X_n,Y_n)` form a constructive outer
Cauchy sequence and constructs its `CReal` limit.  A computable uniform
diagonal bound is obtained from one anchor term, the squared-distance triangle
law, and the inner regularity proved in the preceding kernel.

This file constructs the representative-level pairing limit.  Independence
of the chosen completion representatives and descent to an `RC`-valued form
are the next frontier.  Nome, half-extent, and physical volume remain fixed;
no continuum or mass-gap claim is made.

## Axiom gate

All rates and approximation moduli are Type-level data.  No classical choice,
noncomputable declaration, custom axiom, or unproved placeholder is used.
-/

import YMGap.Constructive.CRealCompleteRate
import YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInnerKernel

namespace YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInnerOuter

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffLinearGNSForm.CentralPhysicalLinearObservable
open YMGap.Continuum.BF4PhysicalCutoffLinearRadicalDescent
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletion
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInnerKernel
open YMGap.Continuum.CRealSeminormCompletion

private theorem leEv_of_leRat {x : CReal} {bound : Q'}
    (h : CReal.leRat x bound) : CReal.leEv x (CReal.ofQ' bound) := by
  intro epsilon hepsilon
  obtain ⟨N, hN⟩ := h epsilon hepsilon
  exact ⟨N, fun n hn => hN n hn⟩

/-! ## 1. A computable uniform diagonal bound -/

/-- The representative index used as a fixed norm anchor. -/
def physicalCauchyNormBase
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (X : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy) : Nat :=
  X.modulus 1

/-- Squared distance from the anchor term to the dense zero. -/
def physicalCauchyAnchorDist
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (X : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy) : CReal :=
  physicalLinearDistSq hw0 hw1 half
    (X.seq (physicalCauchyNormBase hw0 hw1 half X)) .zero

/-- A rational anchor bound read at an explicitly regular approximation. -/
def physicalCauchyAnchorBoundQ
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (X : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy) : Q' :=
  let inner := physicalLinearDistSqInnerRegularity hw0 hw1 half
    (X.seq (physicalCauchyNormBase hw0 hw1 half X)) .zero
  Q'.abs ((physicalCauchyAnchorDist hw0 hw1 half X).approx
    (inner.rate 1)) + 1

/-- Triangle-derived uniform rational squared-norm bound. -/
def physicalCauchyNormBoundQ
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (X : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy) : Q' :=
  (1 + 1) +
    (physicalCauchyAnchorBoundQ hw0 hw1 half X +
      physicalCauchyAnchorBoundQ hw0 hw1 half X)

/-- Natural ceiling for the uniform diagonal bound. -/
def physicalCauchyNormCeil
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (X : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy) : Nat :=
  (physicalCauchyNormBoundQ hw0 hw1 half X).num.toNat + 1

theorem one_le_physicalCauchyNormCeil
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (X : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy) :
    1 <= physicalCauchyNormCeil hw0 hw1 half X :=
  Nat.le_add_left 1 _

/-- The anchor distance is eventually below its computable rational bound. -/
theorem physicalCauchyAnchorDist_leEv_bound
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (X : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy) :
    CReal.leEv (physicalCauchyAnchorDist hw0 hw1 half X)
      (CReal.ofQ' (physicalCauchyAnchorBoundQ hw0 hw1 half X)) := by
  let inner := physicalLinearDistSqInnerRegularity hw0 hw1 half
    (X.seq (physicalCauchyNormBase hw0 hw1 half X)) .zero
  have hone : (0 : Q') < 1 := by decide
  have hbound : CReal.leRat (physicalCauchyAnchorDist hw0 hw1 half X)
      (physicalCauchyAnchorBoundQ hw0 hw1 half X) := by
    apply CReal.leRat_of_eventually
    refine ⟨inner.rate 1, fun n hn => ?_⟩
    have hreg := inner.regular 1 hone n (inner.rate 1)
      hn (Nat.le_refl _)
    have hcenter :
        (physicalCauchyAnchorDist hw0 hw1 half X).approx (inner.rate 1) <=
          Q'.abs ((physicalCauchyAnchorDist hw0 hw1 half X).approx
            (inner.rate 1)) :=
      Q'.le_abs_self _
    exact Q'.le_trans' _ _ _ hreg.1
      (Q'.add_le_add_right _ _ 1 hcenter)
  exact leEv_of_leRat hbound

/-- Every representative term after the anchor has uniformly bounded
diagonal pairing. -/
theorem physicalCauchyStageDiagonal_leEv_normBound
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (X : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy)
    (n : Nat) (hn : physicalCauchyNormBase hw0 hw1 half X <= n) :
    CReal.leEv
      (innerLimit hw0 hw1 half (X.seq n) (X.seq n))
      (CReal.ofQ' (physicalCauchyNormBoundQ hw0 hw1 half X)) := by
  let anchor := X.seq (physicalCauchyNormBase hw0 hw1 half X)
  have hone : (0 : Q') < 1 := by decide
  have hnear : CReal.leEv
      (physicalLinearDistSq hw0 hw1 half (X.seq n) anchor)
      (CReal.ofQ' 1) :=
    X.isCauchy 1 hone n (physicalCauchyNormBase hw0 hw1 half X)
      hn (Nat.le_refl _)
  have hanchor : CReal.leEv
      (physicalLinearDistSq hw0 hw1 half anchor .zero)
      (CReal.ofQ' (physicalCauchyAnchorBoundQ hw0 hw1 half X)) :=
    physicalCauchyAnchorDist_leEv_bound hw0 hw1 half X
  have htriangle := physicalLinearDistSq_triangle
    hw0 hw1 half (X.seq n) anchor .zero
  have hsum := CReal.leEv_add
    (CReal.leEv_add hnear hnear) (CReal.leEv_add hanchor hanchor)
  have hdist : CReal.leEv
      (physicalLinearDistSq hw0 hw1 half (X.seq n) .zero)
      (CReal.ofQ' (physicalCauchyNormBoundQ hw0 hw1 half X)) := by
    apply CReal.leEv_trans htriangle
    simpa [physicalCauchyNormBoundQ] using hsum
  exact CReal.leEv_trans
    (CReal.leEv_of_equiv
      (innerLimit_self_equiv_distSq_zero
        hw0 hw1 half (X.seq n))) hdist

/-- Natural-ceiling version of the uniform diagonal bound. -/
theorem physicalCauchyStageDiagonal_leEv_normCeil
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (X : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy)
    (n : Nat) (hn : physicalCauchyNormBase hw0 hw1 half X <= n) :
    CReal.leEv
      (innerLimit hw0 hw1 half (X.seq n) (X.seq n))
      (CReal.ofQ' (Q'.ofNat
        (physicalCauchyNormCeil hw0 hw1 half X))) := by
  apply CReal.leEv_trans
    (physicalCauchyStageDiagonal_leEv_normBound hw0 hw1 half X n hn)
  exact CReal.leEv_of_le
    (CReal.ofQ'_le_ofQ'
      (Q'.le_ofNat_ceil (physicalCauchyNormBoundQ hw0 hw1 half X)))

/-! ## 2. Outer pairing rate and directed estimate -/

/-- Dense pairing sequence attached to two completion representatives. -/
def physicalCauchyPairingSeq
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (X Y : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy) (n : Nat) : CReal :=
  innerLimit hw0 hw1 half (X.seq n) (Y.seq n)

/-- Shared natural diagonal ceiling. -/
def physicalCauchyPairNormCeil
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (X Y : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy) : Nat :=
  max (physicalCauchyNormCeil hw0 hw1 half X)
    (physicalCauchyNormCeil hw0 hw1 half Y)

/-- One larger than the common diagonal ceiling, for the product budget. -/
def physicalCauchyPairBudgetCount
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (X Y : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy) : Nat :=
  physicalCauchyPairNormCeil hw0 hw1 half X Y + 1

theorem one_le_physicalCauchyPairBudgetCount
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (X Y : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy) :
    1 <= physicalCauchyPairBudgetCount hw0 hw1 half X Y :=
  Nat.le_add_left 1 _

/-- Small squared-distance tolerance allocated to each Cauchy--Schwarz term. -/
def physicalCauchyPairTolerance
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (X Y : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy) (epsilon : Q') : Q' :=
  HalfPow.half *
    (((HalfPow.half * epsilon) * (HalfPow.half * epsilon)) *
      Q'.invSucc
        (physicalCauchyPairBudgetCount hw0 hw1 half X Y - 1))

theorem physicalCauchyPairTolerance_pos
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (X Y : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon) :
    (0 : Q') < physicalCauchyPairTolerance
      hw0 hw1 half X Y epsilon := by
  apply ExpNeg.half_mul_pos
  exact Q'.mul_pos
    (Q'.mul_pos (ExpNeg.half_mul_pos epsilon hepsilon)
      (ExpNeg.half_mul_pos epsilon hepsilon))
    (Q'.invSucc_pos _)

/-- The tolerance consumes at most the half-epsilon square budget. -/
theorem physicalCauchyPairTolerance_budget
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (X Y : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon) :
    (physicalCauchyPairTolerance hw0 hw1 half X Y epsilon +
        physicalCauchyPairTolerance hw0 hw1 half X Y epsilon) *
      (Q'.ofNat (physicalCauchyPairNormCeil hw0 hw1 half X Y) + 1) <=
      (HalfPow.half * epsilon) * (HalfPow.half * epsilon) := by
  let target := HalfPow.half * epsilon
  let count := physicalCauchyPairBudgetCount hw0 hw1 half X Y
  let delta := (target * target) * Q'.invSucc (count - 1)
  have htarget : (0 : Q') < target :=
    ExpNeg.half_mul_pos epsilon hepsilon
  have htargetSq : (0 : Q') <= target * target :=
    Q'.le_of_lt (Q'.mul_pos htarget htarget)
  have hbase : delta * Q'.ofNat count <= target * target :=
    Q'.budget_le target count
      (one_le_physicalCauchyPairBudgetCount hw0 hw1 half X Y) htargetSq
  have htolerance :
      (physicalCauchyPairTolerance hw0 hw1 half X Y epsilon +
        physicalCauchyPairTolerance hw0 hw1 half X Y epsilon).eqv delta :=
    ExpNeg.two_halves delta
  have hcount :
      (Q'.ofNat (physicalCauchyPairNormCeil hw0 hw1 half X Y) + 1).eqv
        (Q'.ofNat count) :=
    Q'.eqv_symm
      (Q'.ofNat_add_eqv
        (physicalCauchyPairNormCeil hw0 hw1 half X Y) 1)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ htolerance)
      (Q'.mul_eqv_congr_left _ _ _ hcount))) hbase

/-- Raw outer rate for one requested pairing tolerance. -/
def physicalCauchyPairOuterRate
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (X Y : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy) (epsilon : Q') : Nat :=
  max (max (physicalCauchyNormBase hw0 hw1 half X)
      (physicalCauchyNormBase hw0 hw1 half Y))
    (max (X.modulus
        (physicalCauchyPairTolerance hw0 hw1 half X Y epsilon))
      (Y.modulus
        (physicalCauchyPairTolerance hw0 hw1 half X Y epsilon)))

/-- Directed outer pairing estimate at the raw rate. -/
theorem physicalCauchyPairingSeq_diff_leRat
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (X Y : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (m n : Nat)
    (hm : physicalCauchyPairOuterRate hw0 hw1 half X Y epsilon <= m)
    (hn : physicalCauchyPairOuterRate hw0 hw1 half X Y epsilon <= n) :
    CReal.leRat
      (CReal.add (physicalCauchyPairingSeq hw0 hw1 half X Y m)
        (CReal.neg
          (physicalCauchyPairingSeq hw0 hw1 half X Y n))) epsilon := by
  let u := physicalCauchyPairTolerance hw0 hw1 half X Y epsilon
  let ceiling := physicalCauchyPairNormCeil hw0 hw1 half X Y
  have hu : (0 : Q') < u :=
    physicalCauchyPairTolerance_pos hw0 hw1 half X Y epsilon hepsilon
  have hehalf : (0 : Q') < HalfPow.half * epsilon :=
    ExpNeg.half_mul_pos epsilon hepsilon
  have hbaseM : max (physicalCauchyNormBase hw0 hw1 half X)
      (physicalCauchyNormBase hw0 hw1 half Y) <= m :=
    Nat.le_trans (Nat.le_max_left _ _) hm
  have hbaseN : max (physicalCauchyNormBase hw0 hw1 half X)
      (physicalCauchyNormBase hw0 hw1 half Y) <= n :=
    Nat.le_trans (Nat.le_max_left _ _) hn
  have hmodM : max (X.modulus u) (Y.modulus u) <= m :=
    Nat.le_trans (Nat.le_max_right _ _) hm
  have hmodN : max (X.modulus u) (Y.modulus u) <= n :=
    Nat.le_trans (Nat.le_max_right _ _) hn
  have hXm : physicalCauchyNormBase hw0 hw1 half X <= m :=
    Nat.le_trans (Nat.le_max_left _ _) hbaseM
  have hXn : physicalCauchyNormBase hw0 hw1 half X <= n :=
    Nat.le_trans (Nat.le_max_left _ _) hbaseN
  have hYm : physicalCauchyNormBase hw0 hw1 half Y <= m :=
    Nat.le_trans (Nat.le_max_right _ _) hbaseM
  have hXmodM : X.modulus u <= m :=
    Nat.le_trans (Nat.le_max_left _ _) hmodM
  have hXmodN : X.modulus u <= n :=
    Nat.le_trans (Nat.le_max_left _ _) hmodN
  have hYmodM : Y.modulus u <= m :=
    Nat.le_trans (Nat.le_max_right _ _) hmodM
  have hYmodN : Y.modulus u <= n :=
    Nat.le_trans (Nat.le_max_right _ _) hmodN
  have hdistX : CReal.leEv
      (physicalLinearDistSq hw0 hw1 half (X.seq m) (X.seq n))
      (CReal.ofQ' u) :=
    X.isCauchy u hu m n hXmodM hXmodN
  have hdistY : CReal.leEv
      (physicalLinearDistSq hw0 hw1 half (Y.seq m) (Y.seq n))
      (CReal.ofQ' u) :=
    Y.isCauchy u hu m n hYmodM hYmodN
  have hsubX : CReal.leEv
      (innerLimit hw0 hw1 half
        (sub (X.seq m) (X.seq n)) (sub (X.seq m) (X.seq n)))
      (CReal.ofQ' u) := hdistX
  have hsubY : CReal.leEv
      (innerLimit hw0 hw1 half
        (sub (Y.seq m) (Y.seq n)) (sub (Y.seq m) (Y.seq n)))
      (CReal.ofQ' u) := hdistY
  have hnormYm : CReal.leEv
      (innerLimit hw0 hw1 half (Y.seq m) (Y.seq m))
      (CReal.ofQ' (Q'.ofNat ceiling)) := by
    apply CReal.leEv_trans
      (physicalCauchyStageDiagonal_leEv_normCeil
        hw0 hw1 half Y m hYm)
    exact CReal.leEv_of_le (CReal.ofQ'_le_ofQ'
      (Q'.ofNat_le_ofNat (Nat.le_max_right _ _)))
  have hnormXn : CReal.leEv
      (innerLimit hw0 hw1 half (X.seq n) (X.seq n))
      (CReal.ofQ' (Q'.ofNat ceiling)) := by
    apply CReal.leEv_trans
      (physicalCauchyStageDiagonal_leEv_normCeil
        hw0 hw1 half X n hXn)
    exact CReal.leEv_of_le (CReal.ofQ'_le_ofQ'
      (Q'.ofNat_le_ofNat (Nat.le_max_left _ _)))
  have hbudget := physicalCauchyPairTolerance_budget
    hw0 hw1 half X Y epsilon hepsilon
  have htermX := innerLimit_twoSided_leRat hw0 hw1 half
    (sub (X.seq m) (X.seq n)) (Y.seq m)
    u (Q'.ofNat ceiling) (HalfPow.half * epsilon)
    hu hehalf hsubX hnormYm hbudget
  have htermY := innerLimit_twoSided_leRat hw0 hw1 half
    (sub (Y.seq m) (Y.seq n)) (X.seq n)
    u (Q'.ofNat ceiling) (HalfPow.half * epsilon)
    hu hehalf hsubY hnormXn hbudget
  have hsum := CReal.leRat_add htermX.1 htermY.1
  have hsplit := innerLimit_diff_split hw0 hw1 half
    (X.seq m) (X.seq n) (Y.seq m) (Y.seq n)
  apply CReal.leRat_of_equiv hsplit
  exact CReal.leRat_mono hsum
    (Q'.le_of_eqv (ExpNeg.two_halves epsilon))

/-- Running maximum of raw rates along the cofinal `invSucc` scale. -/
def physicalCauchyPairRateNat
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (X Y : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy) : Nat -> Nat
  | 0 => physicalCauchyPairOuterRate hw0 hw1 half X Y (Q'.invSucc 0)
  | k + 1 => max (physicalCauchyPairRateNat hw0 hw1 half X Y k)
      (physicalCauchyPairOuterRate hw0 hw1 half X Y (Q'.invSucc (k + 1)))

theorem physicalCauchyPairRateNat_mono
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (X Y : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy)
    {a b : Nat} (hab : a <= b) :
    physicalCauchyPairRateNat hw0 hw1 half X Y a <=
      physicalCauchyPairRateNat hw0 hw1 half X Y b := by
  induction b with
  | zero => exact Nat.le_of_eq (by cases Nat.le_zero.mp hab; rfl)
  | succ b ih =>
      rcases Nat.lt_or_ge a (b + 1) with hlt | hge
      · exact Nat.le_trans (ih (Nat.lt_succ_iff.mp hlt))
          (Nat.le_max_left _ _)
      · exact Nat.le_of_eq (by cases Nat.le_antisymm hab hge; rfl)

theorem physicalCauchyPairOuterRate_invSucc_le_rateNat
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (X Y : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy) (k : Nat) :
    physicalCauchyPairOuterRate hw0 hw1 half X Y (Q'.invSucc k) <=
      physicalCauchyPairRateNat hw0 hw1 half X Y k := by
  cases k with
  | zero => exact Nat.le_refl _
  | succ k => exact Nat.le_max_right _ _

/-- Denominator-rate outer `leRat` Cauchy predicate. -/
theorem physicalCauchyPairingSeq_LeRatBound
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (X Y : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy) :
    CReal.LeRatBound (physicalCauchyPairingSeq hw0 hw1 half X Y)
      (fun epsilon =>
        physicalCauchyPairRateNat hw0 hw1 half X Y epsilon.den) := by
  intro epsilon hepsilon m n hm hn
  let q := Q'.invSucc epsilon.den
  have hqpos : (0 : Q') < q := Q'.invSucc_pos _
  have hqle : q <= epsilon :=
    Q'.le_trans' _ _ _
      (ExpNeg.invSucc_le_of_le (Nat.le_refl _))
      (HalfPow.invSucc_den_le epsilon hepsilon)
  have hraw :
      physicalCauchyPairOuterRate hw0 hw1 half X Y q <=
        physicalCauchyPairRateNat hw0 hw1 half X Y epsilon.den :=
    physicalCauchyPairOuterRate_invSucc_le_rateNat
      hw0 hw1 half X Y epsilon.den
  have hmraw := Nat.le_trans hraw hm
  have hnraw := Nat.le_trans hraw hn
  refine ⟨?_, ?_⟩
  · exact CReal.leRat_mono
      (physicalCauchyPairingSeq_diff_leRat
        hw0 hw1 half X Y q hqpos m n hmraw hnraw) hqle
  · exact CReal.leRat_mono
      (physicalCauchyPairingSeq_diff_leRat
        hw0 hw1 half X Y q hqpos n m hnraw hmraw) hqle

/-! ## 3. Choice-free representative pairing limit -/

/-- Type-level inner approximation rate for each outer pairing term. -/
def physicalCauchyPairingInnerRate
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (X Y : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy) (n : Nat) (epsilon : Q') : Nat :=
  (innerLimitInnerRegularity hw0 hw1 half (X.seq n) (Y.seq n)).rate epsilon

theorem physicalCauchyPairingSeq_RegPred
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (X Y : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy) :
    CReal.RegPred (physicalCauchyPairingSeq hw0 hw1 half X Y)
      (physicalCauchyPairingInnerRate hw0 hw1 half X Y) := by
  intro n epsilon hepsilon p q hp hq
  exact (innerLimitInnerRegularity hw0 hw1 half (X.seq n) (Y.seq n)).regular
    epsilon hepsilon p q hp hq

/-- Constructed outer limit of the representative pairing sequence. -/
def physicalCauchyPairingLimit
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (X Y : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy) : CReal :=
  CReal.completeLimitFromRate
    (physicalCauchyPairingSeq hw0 hw1 half X Y)
    (fun epsilon =>
      physicalCauchyPairRateNat hw0 hw1 half X Y epsilon.den)
    (physicalCauchyPairingInnerRate hw0 hw1 half X Y)
    (physicalCauchyPairingSeq_RegPred hw0 hw1 half X Y)
    (physicalCauchyPairingSeq_LeRatBound hw0 hw1 half X Y)

/-- The dense representative pairings converge to the constructed limit. -/
theorem physicalCauchyPairingSeq_converges
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (X Y : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy) :
    CReal.ConvergesTo (physicalCauchyPairingSeq hw0 hw1 half X Y)
      (physicalCauchyPairingLimit hw0 hw1 half X Y) :=
  CReal.convergesTo_completeLimitFromDenRate
    (physicalCauchyPairingSeq hw0 hw1 half X Y)
    (physicalCauchyPairRateNat hw0 hw1 half X Y)
    (physicalCauchyPairingInnerRate hw0 hw1 half X Y)
    (physicalCauchyPairingSeq_RegPred hw0 hw1 half X Y)
    (physicalCauchyPairingSeq_LeRatBound hw0 hw1 half X Y)
    (fun hab => physicalCauchyPairRateNat_mono
      hw0 hw1 half X Y hab)

/-! ## Axiom audit -/

#print axioms physicalCauchyAnchorDist_leEv_bound
#print axioms physicalCauchyStageDiagonal_leEv_normBound
#print axioms physicalCauchyStageDiagonal_leEv_normCeil
#print axioms physicalCauchyPairTolerance_budget
#print axioms physicalCauchyPairingSeq_diff_leRat
#print axioms physicalCauchyPairRateNat_mono
#print axioms physicalCauchyPairingSeq_LeRatBound
#print axioms physicalCauchyPairingSeq_RegPred
#print axioms physicalCauchyPairingLimit
#print axioms physicalCauchyPairingSeq_converges

end YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInnerOuter
