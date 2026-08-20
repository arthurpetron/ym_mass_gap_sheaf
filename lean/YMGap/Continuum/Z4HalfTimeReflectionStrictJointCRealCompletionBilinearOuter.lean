/-
# Outer Cauchy control for the completed strict-cylinder OS pairing

This file constructs the representative-level estimates needed to take the
choice-free limit of `n |-> B(X_n,Y_n)`.  It first derives an explicit uniform
diagonal bound for every explicit-modulus Cauchy representative, using one
anchor term and the Type-level inner regularity of the staged squared distance.
-/

import YMGap.Constructive.CRealCompleteRate
import YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealStageBilinearBounds

namespace YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletionBilinearOuter

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum.CRealSeminormCompletion
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealBilinearInnerRegularity
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletionAdd
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletionZeroNeg
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealDirectLimitSeminorm
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealStageBilinearBounds
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealStageBilinearGeometry
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderDirectLimit
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDirectLimitBilinear
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

private theorem leEv_of_leRat {x : CReal} {bound : Q'}
    (h : CReal.leRat x bound) : CReal.leEv x (CReal.ofQ' bound) := by
  intro epsilon hepsilon
  obtain ⟨N, hN⟩ := h epsilon hepsilon
  exact ⟨N, fun n hn => hN n hn⟩

/-! ## 1. A computable uniform diagonal bound for one representative -/

/-- The representative index used as the fixed norm anchor. -/
def cauchyNormBase
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (X : (strictJointCylinderStageSquaredSeminorm hcoupling hle).Cauchy) : Nat :=
  X.modulus 1

/-- Squared distance from the anchor term to the staged zero. -/
def cauchyAnchorDist
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (X : (strictJointCylinderStageSquaredSeminorm hcoupling hle).Cauchy) : CReal :=
  strictJointCylinderStageReflectionDistSq hcoupling hle
    (X.seq (cauchyNormBase hcoupling hle X)) strictJointCylinderStageZero

/-- A rational upper bound obtained from one explicitly regular approximation
of the anchor distance. -/
def cauchyAnchorBoundQ
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (X : (strictJointCylinderStageSquaredSeminorm hcoupling hle).Cauchy) : Q' :=
  let inner := strictJointCylinderStageReflectionDistSqInnerRegularity
    hcoupling hle (X.seq (cauchyNormBase hcoupling hle X))
      strictJointCylinderStageZero
  Q'.abs ((cauchyAnchorDist hcoupling hle X).approx (inner.rate 1)) + 1

/-- The triangle-derived uniform rational squared-norm bound. -/
def cauchyNormBoundQ
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (X : (strictJointCylinderStageSquaredSeminorm hcoupling hle).Cauchy) : Q' :=
  (1 + 1) +
    (cauchyAnchorBoundQ hcoupling hle X + cauchyAnchorBoundQ hcoupling hle X)

/-- A natural ceiling for the uniform diagonal bound. -/
def cauchyNormCeil
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (X : (strictJointCylinderStageSquaredSeminorm hcoupling hle).Cauchy) : Nat :=
  (cauchyNormBoundQ hcoupling hle X).num.toNat + 1

theorem one_le_cauchyNormCeil
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (X : (strictJointCylinderStageSquaredSeminorm hcoupling hle).Cauchy) :
    1 <= cauchyNormCeil hcoupling hle X :=
  Nat.le_add_left 1 _

/-- The anchor distance is eventually bounded by the computable rational
`abs(anchor approximation)+1`. -/
theorem cauchyAnchorDist_leEv_bound
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (X : (strictJointCylinderStageSquaredSeminorm hcoupling hle).Cauchy) :
    CReal.leEv (cauchyAnchorDist hcoupling hle X)
      (CReal.ofQ' (cauchyAnchorBoundQ hcoupling hle X)) := by
  let inner := strictJointCylinderStageReflectionDistSqInnerRegularity
    hcoupling hle (X.seq (cauchyNormBase hcoupling hle X))
      strictJointCylinderStageZero
  have hone : (0 : Q') < 1 := by decide
  have hbound : CReal.leRat (cauchyAnchorDist hcoupling hle X)
      (cauchyAnchorBoundQ hcoupling hle X) := by
    apply CReal.leRat_of_eventually
    refine ⟨inner.rate 1, fun n hn => ?_⟩
    have hreg := inner.regular 1 hone n (inner.rate 1) hn (Nat.le_refl _)
    have hcenter :
        (cauchyAnchorDist hcoupling hle X).approx (inner.rate 1) <=
          Q'.abs ((cauchyAnchorDist hcoupling hle X).approx (inner.rate 1)) :=
      Q'.le_abs_self _
    exact Q'.le_trans' _ _ _ hreg.1
      (Q'.add_le_add_right _ _ 1 hcenter)
  exact leEv_of_leRat hbound

/-- Every term after the anchor index has diagonal pairing bounded by the
explicit rational `cauchyNormBoundQ`. -/
theorem cauchyStageDiagonal_leEv_normBound
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (X : (strictJointCylinderStageSquaredSeminorm hcoupling hle).Cauchy)
    (n : Nat) (hn : cauchyNormBase hcoupling hle X <= n) :
    CReal.leEv
      (strictJointCylinderStageReflectionBilinear hcoupling hle
        (X.seq n) (X.seq n))
      (CReal.ofQ' (cauchyNormBoundQ hcoupling hle X)) := by
  let anchor := X.seq (cauchyNormBase hcoupling hle X)
  have hone : (0 : Q') < 1 := by decide
  have hnear : CReal.leEv
      (strictJointCylinderStageReflectionDistSq hcoupling hle (X.seq n) anchor)
      (CReal.ofQ' 1) :=
    X.isCauchy 1 hone n (cauchyNormBase hcoupling hle X)
      hn (Nat.le_refl _)
  have hanchor : CReal.leEv
      (strictJointCylinderStageReflectionDistSq hcoupling hle
        anchor strictJointCylinderStageZero)
      (CReal.ofQ' (cauchyAnchorBoundQ hcoupling hle X)) :=
    cauchyAnchorDist_leEv_bound hcoupling hle X
  have htriangle := strictJointCylinderStageReflectionDistSq_triangle
    hcoupling hle (X.seq n) anchor strictJointCylinderStageZero
  have hsum := CReal.leEv_add
    (CReal.leEv_add hnear hnear) (CReal.leEv_add hanchor hanchor)
  have hdist : CReal.leEv
      (strictJointCylinderStageReflectionDistSq hcoupling hle
        (X.seq n) strictJointCylinderStageZero)
      (CReal.ofQ' (cauchyNormBoundQ hcoupling hle X)) := by
    apply CReal.leEv_trans htriangle
    simpa [cauchyNormBoundQ] using hsum
  exact CReal.leEv_trans
    (CReal.leEv_of_equiv
      (strictJointCylinderStageReflectionBilinear_self_equiv_distSq_zero
        hcoupling hle (X.seq n))) hdist

/-- Natural-ceiling version of the uniform diagonal bound. -/
theorem cauchyStageDiagonal_leEv_normCeil
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (X : (strictJointCylinderStageSquaredSeminorm hcoupling hle).Cauchy)
    (n : Nat) (hn : cauchyNormBase hcoupling hle X <= n) :
    CReal.leEv
      (strictJointCylinderStageReflectionBilinear hcoupling hle
        (X.seq n) (X.seq n))
      (CReal.ofQ' (Q'.ofNat (cauchyNormCeil hcoupling hle X))) := by
  apply CReal.leEv_trans (cauchyStageDiagonal_leEv_normBound hcoupling hle X n hn)
  exact CReal.leEv_of_le
    (CReal.ofQ'_le_ofQ'
      (Q'.le_ofNat_ceil (cauchyNormBoundQ hcoupling hle X)))

/-! ## 2. The outer pairing rate and its Cauchy estimate -/

/-- Representative-level staged pairing sequence. -/
def cauchyPairingSeq
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (X Y : (strictJointCylinderStageSquaredSeminorm hcoupling hle).Cauchy)
    (n : Nat) : CReal :=
  strictJointCylinderStageReflectionBilinear hcoupling hle (X.seq n) (Y.seq n)

/-- One natural ceiling shared by both representatives. -/
def cauchyPairNormCeil
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (X Y : (strictJointCylinderStageSquaredSeminorm hcoupling hle).Cauchy) : Nat :=
  max (cauchyNormCeil hcoupling hle X) (cauchyNormCeil hcoupling hle Y)

/-- The factor used by the division-free product budget.  It is one larger
than the shared diagonal ceiling because the quantitative staged CS lemma
uses one unit of eventual-order slack. -/
def cauchyPairBudgetCount
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (X Y : (strictJointCylinderStageSquaredSeminorm hcoupling hle).Cauchy) : Nat :=
  cauchyPairNormCeil hcoupling hle X Y + 1

theorem one_le_cauchyPairBudgetCount
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (X Y : (strictJointCylinderStageSquaredSeminorm hcoupling hle).Cauchy) :
    1 <= cauchyPairBudgetCount hcoupling hle X Y :=
  Nat.le_add_left 1 _

/-- The small squared-distance tolerance used for each CS term. -/
def cauchyPairTolerance
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (X Y : (strictJointCylinderStageSquaredSeminorm hcoupling hle).Cauchy)
    (epsilon : Q') : Q' :=
  HalfPow.half *
    (((HalfPow.half * epsilon) * (HalfPow.half * epsilon)) *
      Q'.invSucc (cauchyPairBudgetCount hcoupling hle X Y - 1))

theorem cauchyPairTolerance_pos
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (X Y : (strictJointCylinderStageSquaredSeminorm hcoupling hle).Cauchy)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon) :
    (0 : Q') < cauchyPairTolerance hcoupling hle X Y epsilon := by
  apply ExpNeg.half_mul_pos
  exact Q'.mul_pos
    (Q'.mul_pos (ExpNeg.half_mul_pos epsilon hepsilon)
      (ExpNeg.half_mul_pos epsilon hepsilon))
    (Q'.invSucc_pos _)

/-- The rational product budget consumed by the staged CS lemma. -/
theorem cauchyPairTolerance_budget
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (X Y : (strictJointCylinderStageSquaredSeminorm hcoupling hle).Cauchy)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon) :
    (cauchyPairTolerance hcoupling hle X Y epsilon +
        cauchyPairTolerance hcoupling hle X Y epsilon) *
      (Q'.ofNat (cauchyPairNormCeil hcoupling hle X Y) + 1) <=
      (HalfPow.half * epsilon) * (HalfPow.half * epsilon) := by
  let target := HalfPow.half * epsilon
  let count := cauchyPairBudgetCount hcoupling hle X Y
  let delta := (target * target) * Q'.invSucc (count - 1)
  have htarget : (0 : Q') < target := ExpNeg.half_mul_pos epsilon hepsilon
  have htargetSq : (0 : Q') <= target * target :=
    Q'.le_of_lt (Q'.mul_pos htarget htarget)
  have hbase : delta * Q'.ofNat count <= target * target :=
    Q'.budget_le target count
      (one_le_cauchyPairBudgetCount hcoupling hle X Y) htargetSq
  have htolerance :
      (cauchyPairTolerance hcoupling hle X Y epsilon +
        cauchyPairTolerance hcoupling hle X Y epsilon).eqv delta := by
    exact ExpNeg.two_halves delta
  have hcount :
      (Q'.ofNat (cauchyPairNormCeil hcoupling hle X Y) + 1).eqv
        (Q'.ofNat count) := by
    exact Q'.eqv_symm
      (Q'.ofNat_add_eqv (cauchyPairNormCeil hcoupling hle X Y) 1)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ htolerance)
      (Q'.mul_eqv_congr_left _ _ _ hcount))) hbase

/-- Raw outer rate at one requested pairing tolerance. -/
def cauchyPairOuterRate
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (X Y : (strictJointCylinderStageSquaredSeminorm hcoupling hle).Cauchy)
    (epsilon : Q') : Nat :=
  max (max (cauchyNormBase hcoupling hle X)
      (cauchyNormBase hcoupling hle Y))
    (max (X.modulus (cauchyPairTolerance hcoupling hle X Y epsilon))
      (Y.modulus (cauchyPairTolerance hcoupling hle X Y epsilon)))

/-- One directed outer pairing estimate at the raw rate. -/
theorem cauchyPairingSeq_diff_leRat
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (X Y : (strictJointCylinderStageSquaredSeminorm hcoupling hle).Cauchy)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (m n : Nat)
    (hm : cauchyPairOuterRate hcoupling hle X Y epsilon <= m)
    (hn : cauchyPairOuterRate hcoupling hle X Y epsilon <= n) :
    CReal.leRat
      (CReal.add (cauchyPairingSeq hcoupling hle X Y m)
        (CReal.neg (cauchyPairingSeq hcoupling hle X Y n))) epsilon := by
  let u := cauchyPairTolerance hcoupling hle X Y epsilon
  let ceiling := cauchyPairNormCeil hcoupling hle X Y
  have hu : (0 : Q') < u :=
    cauchyPairTolerance_pos hcoupling hle X Y epsilon hepsilon
  have hehalf : (0 : Q') < HalfPow.half * epsilon :=
    ExpNeg.half_mul_pos epsilon hepsilon
  have hbaseM : max (cauchyNormBase hcoupling hle X)
      (cauchyNormBase hcoupling hle Y) <= m :=
    Nat.le_trans (Nat.le_max_left _ _) hm
  have hbaseN : max (cauchyNormBase hcoupling hle X)
      (cauchyNormBase hcoupling hle Y) <= n :=
    Nat.le_trans (Nat.le_max_left _ _) hn
  have hmodM : max (X.modulus u) (Y.modulus u) <= m :=
    Nat.le_trans (Nat.le_max_right _ _) hm
  have hmodN : max (X.modulus u) (Y.modulus u) <= n :=
    Nat.le_trans (Nat.le_max_right _ _) hn
  have hXm : cauchyNormBase hcoupling hle X <= m :=
    Nat.le_trans (Nat.le_max_left _ _) hbaseM
  have hXn : cauchyNormBase hcoupling hle X <= n :=
    Nat.le_trans (Nat.le_max_left _ _) hbaseN
  have hYm : cauchyNormBase hcoupling hle Y <= m :=
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
      (strictJointCylinderStageReflectionDistSq hcoupling hle (X.seq m) (X.seq n))
      (CReal.ofQ' u) :=
    X.isCauchy u hu m n hXmodM hXmodN
  have hdistY : CReal.leEv
      (strictJointCylinderStageReflectionDistSq hcoupling hle (Y.seq m) (Y.seq n))
      (CReal.ofQ' u) :=
    Y.isCauchy u hu m n hYmodM hYmodN
  have hsubX : CReal.leEv
      (strictJointCylinderStageReflectionBilinear hcoupling hle
        (strictJointCylinderStageSub (X.seq m) (X.seq n))
        (strictJointCylinderStageSub (X.seq m) (X.seq n)))
      (CReal.ofQ' u) :=
    CReal.leEv_trans
      (CReal.leEv_of_equiv
        (strictJointCylinderStageReflectionBilinear_sub_self_equiv_distSq
          hcoupling hle (X.seq m) (X.seq n))) hdistX
  have hsubY : CReal.leEv
      (strictJointCylinderStageReflectionBilinear hcoupling hle
        (strictJointCylinderStageSub (Y.seq m) (Y.seq n))
        (strictJointCylinderStageSub (Y.seq m) (Y.seq n)))
      (CReal.ofQ' u) :=
    CReal.leEv_trans
      (CReal.leEv_of_equiv
        (strictJointCylinderStageReflectionBilinear_sub_self_equiv_distSq
          hcoupling hle (Y.seq m) (Y.seq n))) hdistY
  have hnormYm : CReal.leEv
      (strictJointCylinderStageReflectionBilinear hcoupling hle
        (Y.seq m) (Y.seq m)) (CReal.ofQ' (Q'.ofNat ceiling)) := by
    apply CReal.leEv_trans
      (cauchyStageDiagonal_leEv_normCeil hcoupling hle Y m hYm)
    exact CReal.leEv_of_le (CReal.ofQ'_le_ofQ'
      (Q'.ofNat_le_ofNat (Nat.le_max_right _ _)))
  have hnormXn : CReal.leEv
      (strictJointCylinderStageReflectionBilinear hcoupling hle
        (X.seq n) (X.seq n)) (CReal.ofQ' (Q'.ofNat ceiling)) := by
    apply CReal.leEv_trans
      (cauchyStageDiagonal_leEv_normCeil hcoupling hle X n hXn)
    exact CReal.leEv_of_le (CReal.ofQ'_le_ofQ'
      (Q'.ofNat_le_ofNat (Nat.le_max_left _ _)))
  have hbudget := cauchyPairTolerance_budget
    hcoupling hle X Y epsilon hepsilon
  have htermX :=
    strictJointCylinderStageReflectionBilinear_twoSided_leRat
      hcoupling hle
      (strictJointCylinderStageSub (X.seq m) (X.seq n)) (Y.seq m)
      u (Q'.ofNat ceiling) (HalfPow.half * epsilon)
      hu hehalf hsubX hnormYm hbudget
  have htermY :=
    strictJointCylinderStageReflectionBilinear_twoSided_leRat
      hcoupling hle
      (strictJointCylinderStageSub (Y.seq m) (Y.seq n)) (X.seq n)
      u (Q'.ofNat ceiling) (HalfPow.half * epsilon)
      hu hehalf hsubY hnormXn hbudget
  have hsum := CReal.leRat_add htermX.1 htermY.1
  have hsplit := strictJointCylinderStageReflectionBilinear_diff_split
    hcoupling hle (X.seq m) (X.seq n) (Y.seq m) (Y.seq n)
  apply CReal.leRat_of_equiv hsplit
  exact CReal.leRat_mono hsum
    (Q'.le_of_eqv (ExpNeg.two_halves epsilon))

/-- Running maximum of raw rates along the cofinal `invSucc` scale. -/
def cauchyPairRateNat
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (X Y : (strictJointCylinderStageSquaredSeminorm hcoupling hle).Cauchy) :
    Nat -> Nat
  | 0 => cauchyPairOuterRate hcoupling hle X Y (Q'.invSucc 0)
  | k + 1 => max (cauchyPairRateNat hcoupling hle X Y k)
      (cauchyPairOuterRate hcoupling hle X Y (Q'.invSucc (k + 1)))

theorem cauchyPairRateNat_mono
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (X Y : (strictJointCylinderStageSquaredSeminorm hcoupling hle).Cauchy)
    {a b : Nat} (hab : a <= b) :
    cauchyPairRateNat hcoupling hle X Y a <=
      cauchyPairRateNat hcoupling hle X Y b := by
  induction b with
  | zero => exact Nat.le_of_eq (by cases Nat.le_zero.mp hab; rfl)
  | succ b ih =>
      rcases Nat.lt_or_ge a (b + 1) with hlt | hge
      · exact Nat.le_trans (ih (Nat.lt_succ_iff.mp hlt)) (Nat.le_max_left _ _)
      · exact Nat.le_of_eq (by cases Nat.le_antisymm hab hge; rfl)

theorem cauchyPairOuterRate_invSucc_le_rateNat
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (X Y : (strictJointCylinderStageSquaredSeminorm hcoupling hle).Cauchy)
    (k : Nat) :
    cauchyPairOuterRate hcoupling hle X Y (Q'.invSucc k) <=
      cauchyPairRateNat hcoupling hle X Y k := by
  cases k with
  | zero => exact Nat.le_refl _
  | succ k => exact Nat.le_max_right _ _

/-- The denominator-rate outer `leRat` Cauchy predicate consumed by
`CReal.completeLimitFromRate`. -/
theorem cauchyPairingSeq_LeRatBound
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (X Y : (strictJointCylinderStageSquaredSeminorm hcoupling hle).Cauchy) :
    CReal.LeRatBound (cauchyPairingSeq hcoupling hle X Y)
      (fun epsilon => cauchyPairRateNat hcoupling hle X Y epsilon.den) := by
  intro epsilon hepsilon m n hm hn
  let q := Q'.invSucc epsilon.den
  have hqpos : (0 : Q') < q := Q'.invSucc_pos _
  have hqle : q <= epsilon :=
    Q'.le_trans' _ _ _ (ExpNeg.invSucc_le_of_le (Nat.le_refl _))
      (HalfPow.invSucc_den_le epsilon hepsilon)
  have hraw : cauchyPairOuterRate hcoupling hle X Y q <=
      cauchyPairRateNat hcoupling hle X Y epsilon.den :=
    cauchyPairOuterRate_invSucc_le_rateNat
      hcoupling hle X Y epsilon.den
  have hmraw : cauchyPairOuterRate hcoupling hle X Y q <= m :=
    Nat.le_trans hraw hm
  have hnraw : cauchyPairOuterRate hcoupling hle X Y q <= n :=
    Nat.le_trans hraw hn
  refine ⟨?_, ?_⟩
  · exact CReal.leRat_mono
      (cauchyPairingSeq_diff_leRat hcoupling hle X Y q hqpos m n hmraw hnraw)
      hqle
  · exact CReal.leRat_mono
      (cauchyPairingSeq_diff_leRat hcoupling hle X Y q hqpos n m hnraw hmraw)
      hqle

/-! ## 3. The choice-free representative pairing limit -/

/-- Type-level inner approximation rate for every term of the outer pairing
sequence. -/
def cauchyPairingInnerRate
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (X Y : (strictJointCylinderStageSquaredSeminorm hcoupling hle).Cauchy)
    (n : Nat) (epsilon : Q') : Nat :=
  (strictJointCylinderStageReflectionBilinearInnerRegularity
    hcoupling hle (X.seq n) (Y.seq n)).rate epsilon

theorem cauchyPairingSeq_RegPred
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (X Y : (strictJointCylinderStageSquaredSeminorm hcoupling hle).Cauchy) :
    CReal.RegPred (cauchyPairingSeq hcoupling hle X Y)
      (cauchyPairingInnerRate hcoupling hle X Y) := by
  intro n epsilon hepsilon p q hp hq
  exact (strictJointCylinderStageReflectionBilinearInnerRegularity
    hcoupling hle (X.seq n) (Y.seq n)).regular
      epsilon hepsilon p q hp hq

/-- The choice-free outer limit of the staged pairing sequence. -/
def cauchyPairingLimit
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (X Y : (strictJointCylinderStageSquaredSeminorm hcoupling hle).Cauchy) : CReal :=
  CReal.completeLimitFromRate
    (cauchyPairingSeq hcoupling hle X Y)
    (fun epsilon => cauchyPairRateNat hcoupling hle X Y epsilon.den)
    (cauchyPairingInnerRate hcoupling hle X Y)
    (cauchyPairingSeq_RegPred hcoupling hle X Y)
    (cauchyPairingSeq_LeRatBound hcoupling hle X Y)

/-- The representative pairing sequence converges to its constructed outer
limit. -/
theorem cauchyPairingSeq_converges
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (X Y : (strictJointCylinderStageSquaredSeminorm hcoupling hle).Cauchy) :
    CReal.ConvergesTo (cauchyPairingSeq hcoupling hle X Y)
      (cauchyPairingLimit hcoupling hle X Y) :=
  CReal.convergesTo_completeLimitFromDenRate
    (cauchyPairingSeq hcoupling hle X Y)
    (cauchyPairRateNat hcoupling hle X Y)
    (cauchyPairingInnerRate hcoupling hle X Y)
    (cauchyPairingSeq_RegPred hcoupling hle X Y)
    (cauchyPairingSeq_LeRatBound hcoupling hle X Y)
    (fun hab => cauchyPairRateNat_mono hcoupling hle X Y hab)

/-! ## 4. Invariance under asymptotically close representatives -/

/-- Two convergent `CReal` sequences with an eventual two-sided `leRat`
distance tending to zero have equivalent limits. -/
theorem CReal.Equiv_of_convergesTo_leRat_close
    {s t : Nat -> CReal} {A B : CReal}
    (hA : CReal.ConvergesTo s A) (hB : CReal.ConvergesTo t B)
    (hclose : forall epsilon : Q', (0 : Q') < epsilon ->
      exists N : Nat, forall n : Nat, N <= n ->
        CReal.leRat (CReal.add (s n) (CReal.neg (t n))) epsilon ∧
        CReal.leRat (CReal.add (t n) (CReal.neg (s n))) epsilon) :
    CReal.Equiv A B := by
  intro epsilon hepsilon
  let q := HalfPow.half * (HalfPow.half * epsilon)
  have hqpos : (0 : Q') < q :=
    ExpNeg.half_mul_pos _ (ExpNeg.half_mul_pos epsilon hepsilon)
  obtain ⟨NA, hNA⟩ := hA q hqpos
  obtain ⟨NB, hNB⟩ := hB q hqpos
  obtain ⟨NC, hNC⟩ := hclose q hqpos
  let N := max (max NA NB) NC
  have hN_A : NA <= N :=
    Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)
  have hN_B : NB <= N :=
    Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)
  have hN_C : NC <= N := Nat.le_max_right _ _
  obtain ⟨KA, hKA⟩ := hNA N hN_A
  obtain ⟨KB, hKB⟩ := hNB N hN_B
  obtain ⟨hst, hts⟩ := hNC N hN_C
  obtain ⟨Kst, hKst⟩ := hst q hqpos
  obtain ⟨Kts, hKts⟩ := hts q hqpos
  refine ⟨max (max KA KB) (max Kst Kts), fun k hk => ?_⟩
  have hkA : KA <= k :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)) hk
  have hkB : KB <= k :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)) hk
  have hkst : Kst <= k :=
    Nat.le_trans (Nat.le_max_left _ _) (Nat.le_trans (Nat.le_max_right _ _) hk)
  have hkts : Kts <= k :=
    Nat.le_trans (Nat.le_max_right _ _) (Nat.le_trans (Nat.le_max_right _ _) hk)
  obtain ⟨hsA, hAs⟩ := hKA k hkA
  obtain ⟨htB, hBt⟩ := hKB k hkB
  have hstRaw := hKst k hkst
  have htsRaw := hKts k hkts
  have hst' : (s N).approx k <= (t N).approx k + (q + q) :=
    CReal.leAddOfSubLe hstRaw
  have hts' : (t N).approx k <= (s N).approx k + (q + q) :=
    CReal.leAddOfSubLe htsRaw
  have hcollapse : forall w : Q', ((((w + q) + q) + q) + q) <= w + epsilon :=
    fun w => CReal.collapse4 w q epsilon (CReal.fourQ_le epsilon hepsilon)
  refine ⟨?_, ?_⟩
  · have h1 : A.approx k <= ((t N).approx k + (q + q)) + q :=
      Q'.le_trans' _ _ _ hAs (Q'.add_le_add_right _ _ q hst')
    have h2 : A.approx k <= (((B.approx k + q) + q) + q) + q := by
      refine Q'.le_trans' _ _ _ h1 ?_
      have hpush : (t N).approx k + (q + q) <=
          (B.approx k + q) + (q + q) :=
        Q'.add_le_add_right _ _ (q + q) htB
      refine Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ q hpush) ?_
      exact Q'.le_of_eqv (Q'.add_eqv_congr_right _ _ q
        (Q'.eqv_symm (Q'.add_assoc_eqv (B.approx k + q) q q)))
    exact Q'.le_trans' _ _ _ h2 (hcollapse (B.approx k))
  · have h1 : B.approx k <= ((s N).approx k + (q + q)) + q :=
      Q'.le_trans' _ _ _ hBt (Q'.add_le_add_right _ _ q hts')
    have h2 : B.approx k <= (((A.approx k + q) + q) + q) + q := by
      refine Q'.le_trans' _ _ _ h1 ?_
      have hpush : (s N).approx k + (q + q) <=
          (A.approx k + q) + (q + q) :=
        Q'.add_le_add_right _ _ (q + q) hsA
      refine Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ q hpush) ?_
      exact Q'.le_of_eqv (Q'.add_eqv_congr_right _ _ q
        (Q'.eqv_symm (Q'.add_assoc_eqv (A.approx k + q) q q)))
    exact Q'.le_trans' _ _ _ h2 (hcollapse (A.approx k))

/-- Raw same-index rate for comparing pairings of close representatives. -/
def cauchyPairCloseRate
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    {X X' Y Y' : (strictJointCylinderStageSquaredSeminorm hcoupling hle).Cauchy}
    (hX : (strictJointCylinderStageSquaredSeminorm hcoupling hle).Close X X')
    (hY : (strictJointCylinderStageSquaredSeminorm hcoupling hle).Close Y Y')
    (epsilon : Q') : Nat :=
  let u := cauchyPairTolerance hcoupling hle Y X' epsilon
  max (max (cauchyNormBase hcoupling hle Y)
      (cauchyNormBase hcoupling hle X'))
    (max (hX.modulus u) (hY.modulus u))

/-- One directed same-index pairing comparison for close representatives. -/
theorem cauchyPairingSeq_close_diff_leRat
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    {X X' Y Y' : (strictJointCylinderStageSquaredSeminorm hcoupling hle).Cauchy}
    (hX : (strictJointCylinderStageSquaredSeminorm hcoupling hle).Close X X')
    (hY : (strictJointCylinderStageSquaredSeminorm hcoupling hle).Close Y Y')
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (n : Nat) (hn : cauchyPairCloseRate hcoupling hle hX hY epsilon <= n) :
    CReal.leRat
      (CReal.add (cauchyPairingSeq hcoupling hle X Y n)
        (CReal.neg (cauchyPairingSeq hcoupling hle X' Y' n))) epsilon := by
  let u := cauchyPairTolerance hcoupling hle Y X' epsilon
  let ceiling := cauchyPairNormCeil hcoupling hle Y X'
  have hu : (0 : Q') < u :=
    cauchyPairTolerance_pos hcoupling hle Y X' epsilon hepsilon
  have hehalf : (0 : Q') < HalfPow.half * epsilon :=
    ExpNeg.half_mul_pos epsilon hepsilon
  have hbase : max (cauchyNormBase hcoupling hle Y)
      (cauchyNormBase hcoupling hle X') <= n :=
    Nat.le_trans (Nat.le_max_left _ _) hn
  have hmods : max (hX.modulus u) (hY.modulus u) <= n :=
    Nat.le_trans (Nat.le_max_right _ _) hn
  have hYn : cauchyNormBase hcoupling hle Y <= n :=
    Nat.le_trans (Nat.le_max_left _ _) hbase
  have hX'n : cauchyNormBase hcoupling hle X' <= n :=
    Nat.le_trans (Nat.le_max_right _ _) hbase
  have hXmod : hX.modulus u <= n :=
    Nat.le_trans (Nat.le_max_left _ _) hmods
  have hYmod : hY.modulus u <= n :=
    Nat.le_trans (Nat.le_max_right _ _) hmods
  have hdistX := hX.close u hu n hXmod
  have hdistY := hY.close u hu n hYmod
  have hsubX : CReal.leEv
      (strictJointCylinderStageReflectionBilinear hcoupling hle
        (strictJointCylinderStageSub (X.seq n) (X'.seq n))
        (strictJointCylinderStageSub (X.seq n) (X'.seq n)))
      (CReal.ofQ' u) :=
    CReal.leEv_trans
      (CReal.leEv_of_equiv
        (strictJointCylinderStageReflectionBilinear_sub_self_equiv_distSq
          hcoupling hle (X.seq n) (X'.seq n))) hdistX
  have hsubY : CReal.leEv
      (strictJointCylinderStageReflectionBilinear hcoupling hle
        (strictJointCylinderStageSub (Y.seq n) (Y'.seq n))
        (strictJointCylinderStageSub (Y.seq n) (Y'.seq n)))
      (CReal.ofQ' u) :=
    CReal.leEv_trans
      (CReal.leEv_of_equiv
        (strictJointCylinderStageReflectionBilinear_sub_self_equiv_distSq
          hcoupling hle (Y.seq n) (Y'.seq n))) hdistY
  have hnormY : CReal.leEv
      (strictJointCylinderStageReflectionBilinear hcoupling hle
        (Y.seq n) (Y.seq n)) (CReal.ofQ' (Q'.ofNat ceiling)) := by
    apply CReal.leEv_trans
      (cauchyStageDiagonal_leEv_normCeil hcoupling hle Y n hYn)
    exact CReal.leEv_of_le (CReal.ofQ'_le_ofQ'
      (Q'.ofNat_le_ofNat (Nat.le_max_left _ _)))
  have hnormX' : CReal.leEv
      (strictJointCylinderStageReflectionBilinear hcoupling hle
        (X'.seq n) (X'.seq n)) (CReal.ofQ' (Q'.ofNat ceiling)) := by
    apply CReal.leEv_trans
      (cauchyStageDiagonal_leEv_normCeil hcoupling hle X' n hX'n)
    exact CReal.leEv_of_le (CReal.ofQ'_le_ofQ'
      (Q'.ofNat_le_ofNat (Nat.le_max_right _ _)))
  have hbudget := cauchyPairTolerance_budget
    hcoupling hle Y X' epsilon hepsilon
  have htermX :=
    strictJointCylinderStageReflectionBilinear_twoSided_leRat
      hcoupling hle
      (strictJointCylinderStageSub (X.seq n) (X'.seq n)) (Y.seq n)
      u (Q'.ofNat ceiling) (HalfPow.half * epsilon)
      hu hehalf hsubX hnormY hbudget
  have htermY :=
    strictJointCylinderStageReflectionBilinear_twoSided_leRat
      hcoupling hle
      (strictJointCylinderStageSub (Y.seq n) (Y'.seq n)) (X'.seq n)
      u (Q'.ofNat ceiling) (HalfPow.half * epsilon)
      hu hehalf hsubY hnormX' hbudget
  have hsum := CReal.leRat_add htermX.1 htermY.1
  have hsplit := strictJointCylinderStageReflectionBilinear_diff_split
    hcoupling hle (X.seq n) (X'.seq n) (Y.seq n) (Y'.seq n)
  apply CReal.leRat_of_equiv hsplit
  exact CReal.leRat_mono hsum
    (Q'.le_of_eqv (ExpNeg.two_halves epsilon))

/-- Pairing limits do not depend on the chosen explicit-modulus completion
representatives. -/
theorem cauchyPairingLimit_welldef
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    {X X' Y Y' : (strictJointCylinderStageSquaredSeminorm hcoupling hle).Cauchy}
    (hX : (strictJointCylinderStageSquaredSeminorm hcoupling hle).Close X X')
    (hY : (strictJointCylinderStageSquaredSeminorm hcoupling hle).Close Y Y') :
    CReal.Equiv (cauchyPairingLimit hcoupling hle X Y)
      (cauchyPairingLimit hcoupling hle X' Y') := by
  apply CReal.Equiv_of_convergesTo_leRat_close
    (cauchyPairingSeq_converges hcoupling hle X Y)
    (cauchyPairingSeq_converges hcoupling hle X' Y')
  intro epsilon hepsilon
  let hXsymm :=
    (strictJointCylinderStageSquaredSeminorm hcoupling hle).closeSymm hX
  let hYsymm :=
    (strictJointCylinderStageSquaredSeminorm hcoupling hle).closeSymm hY
  let Nforward := cauchyPairCloseRate hcoupling hle hX hY epsilon
  let Nbackward := cauchyPairCloseRate hcoupling hle hXsymm hYsymm epsilon
  refine ⟨max Nforward Nbackward, fun n hn => ?_⟩
  have hnForward : Nforward <= n := Nat.le_trans (Nat.le_max_left _ _) hn
  have hnBackward : Nbackward <= n := Nat.le_trans (Nat.le_max_right _ _) hn
  exact ⟨
    cauchyPairingSeq_close_diff_leRat
      hcoupling hle hX hY epsilon hepsilon n hnForward,
    cauchyPairingSeq_close_diff_leRat
      hcoupling hle hXsymm hYsymm epsilon hepsilon n hnBackward⟩

#print axioms cauchyAnchorDist_leEv_bound
#print axioms cauchyStageDiagonal_leEv_normBound
#print axioms cauchyStageDiagonal_leEv_normCeil
#print axioms cauchyPairTolerance_budget
#print axioms cauchyPairingSeq_diff_leRat
#print axioms cauchyPairRateNat_mono
#print axioms cauchyPairingSeq_LeRatBound
#print axioms cauchyPairingSeq_RegPred
#print axioms cauchyPairingLimit
#print axioms cauchyPairingSeq_converges
#print axioms CReal.Equiv_of_convergesTo_leRat_close
#print axioms cauchyPairingSeq_close_diff_leRat
#print axioms cauchyPairingLimit_welldef

end YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletionBilinearOuter
